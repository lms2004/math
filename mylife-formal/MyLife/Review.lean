import MyLife.Provenance

/-!
# 过目：稿子的生命周期（吸收链路 4、6，分析链路 3–5）

稿子不是真源，但设计对它有几条硬规则，这里证明它们：

* 一个节点同时只有一份待定稿子：新的候选必须并进已有的那份（`replaces` 指向它），不能另起一份；
* 我拒绝过的内容（我不要的稿子、确认时我删掉的句子）不再被提出；
* 确认写进版本的稿子，确认时还在过目里，并且基于节点当时的最新版本（节点之后有了新版本，就只能重新起草或不要）；
* 重新分析不改动出处是我的话的句子，除非我在逐句确认里单独决定；
* 稿子离开过目只有三种方式：被并进新稿子、我不要、我确认。不会悄悄消失。

“拒绝过的内容”按句子文本判断：程序只能拦住原样重复，换了说法的重复要靠 Agent 读过目记录。
-/

namespace MyLife

theorem draftAt_cons_of_lt {l : Log} {d : Time} (e : Entry) (h : d < l.length) :
    draftAt (e :: l) d = draftAt l d := by
  simp [draftAt, Nat.ne_of_lt h]

theorem mem_pendingFor {l : Log} {d : Time} {n : NodeId} : d ∈ pendingFor l n ↔ Pending l d n := by
  unfold pendingFor
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨hd, _⟩ := h
    cases hda : draftAt l d with
    | none => simp [hda] at hd
    | some di => exact draftAt_lt hda

/-- 不是稿子的写入，不会让任何稿子进入过目 -/
theorem pending_of_cons_nondraft {l : Log} {e : Entry} {d : Time} {n : NodeId}
    (he : ∀ n' p v r, e.op ≠ .draft n' p v r) (h : Pending (e :: l) d n) : Pending l d n := by
  obtain ⟨hd, hr, hm, hc⟩ := h
  simp only [rejectedTimes, mergedTimes, confirmedTimes, List.mem_append, not_or] at hr hm hc
  refine ⟨?_, hr.2, hm.2, hc.2⟩
  by_cases hdl : d = l.length
  · exfalso
    subst hdl
    rcases e with ⟨op, actor⟩
    cases op <;> first
      | exact he _ _ _ _ rfl
      | simp [draftAt] at hd
  · simpa [draftAt, hdl] using hd

/-- **定理（一个节点同时只有一份待定稿子）** -/
theorem pending_unique {L : Log} (hR : Reachable check L) :
    ∀ n d₁ d₂, Pending L d₁ n → Pending L d₂ n → d₁ = d₂ := by
  induction hR with
  | nil => intro n d₁ _ h; simp [Pending, draftAt] at h
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    intro n d₁ d₂ h₁ h₂
    rcases e with ⟨op, actor⟩
    cases op
    case draft n' p v r =>
      simp only [CheckP] at hcP
      obtain ⟨_, _, hpend, _⟩ := hcP
      have key : ∀ d, Pending (⟨.draft n' p v r, actor⟩ :: l) d n →
          (d = l.length ∧ n' = n) ∨ (Pending l d n ∧ d ∉ r.toList) := by
        intro d hd
        obtain ⟨hda, hr, hm, hcf⟩ := hd
        simp only [rejectedTimes, mergedTimes, confirmedTimes, List.mem_append, not_or,
          List.nil_append] at hr hm hcf
        by_cases hdl : d = l.length
        · left
          subst hdl
          simp [draftAt] at hda
          exact ⟨rfl, hda⟩
        · right
          have hda' : (draftAt l d).map (fun di => di.node) = some n := by
            simpa [draftAt, hdl] using hda
          exact ⟨⟨hda', hr, hm.2, hcf⟩, hm.1⟩
      rcases key d₁ h₁ with ⟨rfl, hn⟩ | ⟨hp₁, hr₁⟩ <;>
        rcases key d₂ h₂ with ⟨rfl, hn'⟩ | ⟨hp₂, hr₂⟩
      · rfl
      · exfalso
        rw [← hn] at hp₂
        have hm := mem_pendingFor.mpr hp₂
        rw [hpend] at hm
        exact hr₂ hm
      · exfalso
        rw [← hn'] at hp₁
        have hm := mem_pendingFor.mpr hp₁
        rw [hpend] at hm
        exact hr₁ hm
      · exact ih n d₁ d₂ hp₁ hp₂
    all_goals
      exact ih n d₁ d₂ (pending_of_cons_nondraft (by intros; simp) h₁)
        (pending_of_cons_nondraft (by intros; simp) h₂)

theorem rejectedTexts_append {l : Log} {n : NodeId} {x : Text} :
    ∀ ext : Log, x ∈ rejectedTexts l n → x ∈ rejectedTexts (ext ++ l) n
  | [], h => h
  | e :: ext, h => by
    simp only [List.cons_append, rejectedTexts, List.mem_append]
    exact Or.inr (rejectedTexts_append ext h)

/-- **定理（不再提出我拒绝过的内容）**：一段内容在某个时刻已经被我拒绝过（不要的稿子，或确认时删掉的句子），
    那么此后针对同一个节点的任何稿子都不包含它 -/
theorem rejected_never_reproposed {L l₁ mid l₀ : Log} {e : Entry} {n : NodeId} {p : FragId}
    {v : Version} {r : Option Time} {x : Text} (hR : Reachable check L)
    (hL : L = l₁ ++ e :: (mid ++ l₀)) (hop : e.op = .draft n p v r) (hx : x ∈ rejectedTexts l₀ n) :
    ∀ s ∈ v.body, s.text ≠ x := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  intro s hs heq
  apply hc.2.2.2 s hs
  rw [heq]
  exact rejectedTexts_append mid hx

/-- **定理（确认的稿子不过时）**：写进版本的稿子，确认时还在过目里，并且基于节点当时的最新版本 -/
theorem confirmed_draft_fresh {L l₁ l : Log} {e : Entry} {n : NodeId} {b : Time} {v : Version}
    {ex : List Sentence} {d : Time} (hR : Reachable check L) (hL : L = l₁ ++ e :: l)
    (hop : e.op = .writeVersion n b v ex) (hd : v.fromDraft = some d) :
    Pending l d n ∧ OptAll (draftAt l d) (fun di => di.base = (latest l n).map (fun x => x.1)) := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  have hconf := hc.2.2.2.2.2
  simp only [ConfirmOK, hd, OptAll] at hconf
  exact ⟨hconf.1, hconf.2.1⟩

/-- **定理（重新分析不改我的话）**：确认一份稿子写入新版本时，上一版本里出处是我的话的句子原样保留，
    除非我在逐句确认里单独决定 -/
theorem my_sentences_kept {L l₁ l : Log} {e : Entry} {n : NodeId} {b : Time} {v : Version}
    {ex : List Sentence} {d : Time} (hR : Reachable check L) (hL : L = l₁ ++ e :: l)
    (hop : e.op = .writeVersion n b v ex) (hd : v.fromDraft = some d) :
    OptAll (latest l n) (fun x => ∀ s ∈ x.2.body, fragAuthor l s.origin = some .me →
      s ∈ v.body ∨ s ∈ ex) := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  have hconf := hc.2.2.2.2.2
  simp only [ConfirmOK, hd, OptAll] at hconf
  exact hconf.2.2

/-- **定理（稿子不会悄悄消失）**：一份待定稿子离开过目，只有三种方式：被并进新稿子、我不要、我确认 -/
theorem draft_leaves_review_only_by {l : Log} {e : Entry} {d : Time} {n : NodeId}
    (hR : Reachable check (e :: l)) (hp : Pending l d n) (hq : ¬ Pending (e :: l) d n) :
    (e.op = .rejectDraft d ∧ e.actor = .me) ∨
    (∃ n' p v, e.op = .draft n' p v (some d)) ∨
    (e.actor = .me ∧ ∃ v, v.fromDraft = some d ∧
      ((∃ m ly q src ends ex, e.op = .newNode m ly q src ends v ex) ∨
       (∃ m b ex, e.op = .writeVersion m b v ex))) := by
  obtain ⟨_, hc⟩ := hR.of_cons
  have hcP := checkP_of_check hc
  obtain ⟨hda, hr, hm, hcf⟩ := hp
  have hlt : d < l.length := by
    cases h : draftAt l d with
    | none => simp [h] at hda
    | some di => exact draftAt_lt h
  have hda' : (draftAt (e :: l) d).map (fun di => di.node) = some n := by
    rw [draftAt_cons_of_lt e hlt]; exact hda
  unfold Pending at hq
  rcases e with ⟨op, actor⟩
  cases op
  case rejectDraft d' =>
    simp only [CheckP] at hcP
    simp [rejectedTimes, mergedTimes, confirmedTimes, hda', hr, hm, hcf] at hq
    subst hq
    exact Or.inl ⟨rfl, hcP.1⟩
  case draft n' p v r =>
    simp [rejectedTimes, mergedTimes, confirmedTimes, hda', hr, hm, hcf] at hq
    subst hq
    exact Or.inr (Or.inl ⟨n', p, v, rfl⟩)
  case newNode m ly q src ends v ex =>
    simp only [CheckP] at hcP
    simp [rejectedTimes, mergedTimes, confirmedTimes, hda', hr, hm, hcf] at hq
    exact Or.inr (Or.inr ⟨hcP.1, v, hq, Or.inl ⟨m, ly, q, src, ends, ex, rfl⟩⟩)
  case writeVersion m b v ex =>
    simp only [CheckP] at hcP
    simp [rejectedTimes, mergedTimes, confirmedTimes, hda', hr, hm, hcf] at hq
    exact Or.inr (Or.inr ⟨hcP.1, v, hq, Or.inr ⟨m, b, ex, rfl⟩⟩)
  all_goals simp [rejectedTimes, mergedTimes, confirmedTimes, hda', hr, hm, hcf] at hq

end MyLife
