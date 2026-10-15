import MyLife.History

/-!
# 可追溯、看得出谁起草、只有我能拍板（核心思想 4、核心原则 2、Agent 的边界）

这些性质大多是“逐条写入”的：每条写入在它写入那一刻通过了检查，再加上“查到的东西永远查得到”
（只追加带来的单调性），就对整个日志成立。

片段的作者可以由我更正（追加一条作者更正记录，原件不动），所以和作者有关的性质分两层说：
写入那一刻一定成立（`snap L t` 是写入那一刻的状态）；之后作者被更正过的句子和事实，
一定出现在由日志推出的过目事项里，不会悄悄失效。
-/

namespace MyLife

/-! ## 把存储里的条目对回日志里的写入 -/

theorem records_entry : ∀ {L : Log} {t : Time} {r : FactRec}, (t, r) ∈ records L →
    ∃ l₁ e l, L = l₁ ++ e :: l ∧ e.op = .addFact r ∧ l.length = t
  | [], _, _, h => by simp [records] at h
  | e :: l, t, r, h => by
    simp only [records, List.mem_append] at h
    rcases h with h | h
    · split at h
      · next r' hop =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], e, l, rfl, hop, rfl⟩
      · simp at h
    · obtain ⟨l₁, e', l', hL, hop, ht⟩ := records_entry h
      exact ⟨e :: l₁, e', l', by simp [hL], hop, ht⟩

theorem versions_entry : ∀ {L : Log} {n : NodeId} {t : Time} {v : Version}, (n, t, v) ∈ versions L →
    ∃ l₁ e l, L = l₁ ++ e :: l ∧ l.length = t ∧
      ((∃ ly q src ends ex, e.op = .newNode n ly q src ends v ex) ∨
       (∃ b ex, e.op = .writeVersion n b v ex))
  | [], _, _, _, h => by simp [versions] at h
  | e :: l, n, t, v, h => by
    simp only [versions, List.mem_append] at h
    rcases h with h | h
    · split at h
      · next n' ly q src ends v' ex hop =>
        simp at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], e, l, rfl, rfl, Or.inl ⟨ly, q, src, ends, ex, hop⟩⟩
      · next n' b v' ex hop =>
        simp at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], e, l, rfl, rfl, Or.inr ⟨b, ex, hop⟩⟩
      · simp at h
    · obtain ⟨l₁, e', l', hL, ht, hop⟩ := versions_entry h
      exact ⟨e :: l₁, e', l', by simp [hL], ht, hop⟩

theorem split_append (l₁ : Log) (e : Entry) (l : Log) : l₁ ++ e :: l = (l₁ ++ [e]) ++ l := by
  simp

/-- 每个版本（含历史版本）都是我写入的，并且在写入那一刻通过了正文检查 -/
theorem version_checked {L : Log} {n : NodeId} {t : Time} {v : Version}
    (hR : Reachable check L) (h : (n, t, v) ∈ versions L) :
    ∃ l₁ e l ly ex, L = l₁ ++ e :: l ∧ l.length = t ∧ e.actor = .me ∧ VersionOK l ly ex v := by
  obtain ⟨l₁, e, l, hL, ht, hop⟩ := versions_entry h
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  rcases hop with ⟨ly, q, src, ends, ex, hop⟩ | ⟨b, ex, hop⟩
  · simp only [CheckP, hop] at hc
    exact ⟨l₁, e, l, some ly, ex, rfl, ht, hc.1, hc.2.2.2.2.2.2⟩
  · simp only [CheckP, hop] at hc
    exact ⟨l₁, e, l, layerOf l n, ex, rfl, ht, hc.1, hc.2.2.2.2⟩

/-! ## 只有我能拍板 -/

/-- 只能由我做的写入：正文的新建、新版本、结束和移层，引用跟上，冲突裁决，定权威作者，删除，作者更正 -/
def meOnly : Op → Bool
  | .adopt _ _ => true
  | .setAuthority _ _ => true
  | .newNode _ _ _ _ _ _ _ => true
  | .writeVersion _ _ _ _ => true
  | .endNode _ _ => true
  | .move _ _ => true
  | .ack _ _ => true
  | .deleteRecord _ => true
  | .correctAuthor _ _ => true
  | _ => false

/-- **定理（只有我能拍板）**：日志里每一条“拍板”类写入的发起者都是我。
    换句话说，Agent 和程序能做的只有：存原件、保存记录、吸收记录、抽取 / 作废事实、追加来源、挂关联、起草稿子。 -/
theorem only_me_decides {L l₁ l : Log} {e : Entry} (hR : Reachable check L)
    (hL : L = l₁ ++ e :: l) (h : meOnly e.op = true) : e.actor = .me := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  rcases e with ⟨op, actor⟩
  cases op <;> simp only [meOnly] at h <;> simp only [CheckP] at hc
  all_goals first
    | exact hc
    | exact hc.1
    | simp at h

/-! ## AI 的话不能成为事实 -/

theorem isMeOrExt_some {o : Option Author} (h : isMeOrExt o = true) :
    o = some .me ∨ ∃ p, o = some (.ext p) := by
  rcases o with _ | ⟨_ | _ | p | _⟩ <;> simp [isMeOrExt] at h ⊢

/-- **定理**：每条事实的出处片段都在事实之前就存在；写入那一刻，出处的作者是我或外部发布者，
    不是 AI，也不是作者不明 -/
theorem facts_traceable_not_ai {L : Log} {t : Time} {r : FactRec}
    (hR : Reachable check L) (h : (t, r) ∈ records L) :
    (∃ t' f, fragAt L r.origin = some (t', f) ∧ t' < t) ∧
    isMeOrExt (fragAuthor (snap L t) r.origin) = true := by
  obtain ⟨l₁, e, l, hL, hop, ht⟩ := records_entry h
  subst hL; subst ht
  rw [snap_split]
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  have ha := hc.1
  refine ⟨?_, ha⟩
  cases hf : fragAt l r.origin with
  | none => simp [fragAuthor, hf, isMeOrExt] at ha
  | some x =>
    obtain ⟨t', f⟩ := x
    exact ⟨t', f, by rw [split_append]; exact fragAt_append_of_some _ hf, fragAt_lt hf⟩

/-- 追加的来源同样不能是 AI 的话（写入那一刻） -/
theorem added_sources_not_ai {L l₁ l : Log} {e : Entry} {k : FactKey} {v : Value} {p : FragId}
    (hR : Reachable check L) (hL : L = l₁ ++ e :: l) (hop : e.op = .addSource k v p) :
    isMeOrExt (fragAuthor l p) = true := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  exact hc.1

/-! ## 每句正文都追得到出处，并且看得出是谁起草的 -/

/-- 句子的三种来源，由出处现在的作者和文字改动推出（不另存） -/
inductive Drafter where
  | verbatim    -- 原话
  | tidied      -- 整理
  | aiDrafted   -- AI 起草（经我确认）
  deriving DecidableEq, Repr

def drafter (L : Log) (s : Sentence) : Option Drafter :=
  match fragAt L s.origin with
  | some (_, f) =>
    match fragAuthor L s.origin with
    | some .me => some (if f.fp = s.text then .verbatim else .tidied)
    | some .ai => some .aiDrafted
    | _ => none
  | none => none

/-- 这段日志里没有对片段 p 的作者更正 -/
def NoCorrection (ext : Log) (p : FragId) : Prop := ∀ e ∈ ext, ∀ a, e.op ≠ .correctAuthor p a

theorem attributionOf_append {L : Log} {p : FragId} :
    ∀ (ext : Log), NoCorrection ext p → attributionOf (ext ++ L) p = attributionOf L p
  | [], _ => rfl
  | e :: ext, h => by
    have ih := attributionOf_append (L := L) ext (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e (List.mem_cons_self _ _)
    rcases e with ⟨op, actor⟩
    cases op
    case correctAuthor q a =>
      have hq : q ≠ p := fun hq => he a (by rw [hq])
      simp [attributionOf, hq, ih]
    all_goals simpa [attributionOf] using ih

/-- 没有作者更正，片段的作者就不变 -/
theorem fragAuthor_append_of_no_correction {L : Log} {p : FragId} {a : Author} (ext : Log)
    (hn : NoCorrection ext p) (h : fragAuthor L p = some a) : fragAuthor (ext ++ L) p = some a := by
  unfold fragAuthor at *
  cases hf : fragAt L p with
  | none => simp [hf] at h
  | some r =>
    obtain ⟨t, f⟩ := r
    rw [fragAt_append_of_some ext hf, attributionOf_append ext hn]
    simpa [hf] using h

/-- **定理**：句子的来源类别（原话 / 整理 / AI 起草）只会因为作者更正而改变 -/
theorem drafter_changes_only_by_correction {L : Log} {s : Sentence} {d : Drafter} (ext : Log)
    (hn : NoCorrection ext s.origin) (h : drafter L s = some d) : drafter (ext ++ L) s = some d := by
  unfold drafter at *
  cases hf : fragAt L s.origin with
  | none => simp [hf] at h
  | some r =>
    obtain ⟨t, f⟩ := r
    rw [fragAt_append_of_some ext hf]
    simp only [hf] at h
    cases ha : fragAuthor L s.origin with
    | none => simp [ha] at h
    | some a =>
      rw [fragAuthor_append_of_no_correction ext hn ha]
      simpa [ha] using h

theorem targetOK_append {l : Log} {c : Target} (ext : Log) (h : TargetOK l c) :
    TargetOK (ext ++ l) c := by
  cases c with
  | node m => exact created_isSome_append ext h
  | fact k => exact keyRecorded_append ext h
  | frag p => exact fragAt_isSome_append ext h

/-- **定理（可追溯 + 看得出谁起草）**：任何版本（含历史版本）里的每一句，
    出处片段都在这个版本之前存在；写入那一刻它的来源类别（原话 / 整理 / AI 起草）有定义；
    引用的东西都存在。 -/
theorem sentence_traceable {L : Log} {n : NodeId} {t : Time} {v : Version} {s : Sentence}
    (hR : Reachable check L) (hv : (n, t, v) ∈ versions L) (hs : s ∈ v.body) :
    (∃ t' f, fragAt L s.origin = some (t', f) ∧ t' < t) ∧
    (∃ d, drafter (snap L t) s = some d) ∧
    (∀ c ∈ s.cites, TargetOK L c) := by
  obtain ⟨l₁, e, l, ly, ex, hL, ht, _, hok⟩ := version_checked hR hv
  subst hL; subst ht
  rw [snap_split]
  obtain ⟨hauth, -, -, -, hcites, -, -⟩ := hok s hs
  cases hf : fragAt l s.origin with
  | none => simp [fragAuthor, hf] at hauth
  | some x =>
    obtain ⟨t', f⟩ := x
    refine ⟨⟨t', f, by rw [split_append]; exact fragAt_append_of_some _ hf, fragAt_lt hf⟩, ?_, ?_⟩
    · unfold drafter
      rw [hf]
      rcases hauth with h | h <;> simp [h]
    · intro c hc
      rw [split_append]
      exact targetOK_append _ (hcites c hc)

/-- **定理（程度标记）**：写入那一刻，AI 起草的句子都标了程度；标“确定”的至少引用一处直接依据
    （事实或我的话）；我的原话和整理不标程度。 -/
theorem degree_rules {L : Log} {n : NodeId} {t : Time} {v : Version} {s : Sentence}
    (hR : Reachable check L) (hv : (n, t, v) ∈ versions L) (hs : s ∈ v.body) :
    (drafter (snap L t) s = some .aiDrafted →
        s.degree ≠ none ∧ (s.degree = some .certain → ∃ c ∈ s.cites, Direct (snap L t) c)) ∧
    (drafter (snap L t) s = some .verbatim ∨ drafter (snap L t) s = some .tidied →
        s.degree = none) := by
  obtain ⟨l₁, e, l, ly, ex, hL, ht, _, hok⟩ := version_checked hR hv
  subst hL; subst ht
  rw [snap_split]
  obtain ⟨hauth, hai, hme, hcert, -, -, -⟩ := hok s hs
  cases hf : fragAt l s.origin with
  | none => simp [fragAuthor, hf] at hauth
  | some x =>
    obtain ⟨t', f⟩ := x
    unfold drafter
    rw [hf]
    constructor
    · intro hd
      rcases hauth with h | h
      · rw [h] at hd
        exfalso; revert hd; simp only; split <;> simp
      · exact ⟨hai h, hcert⟩
    · intro hd
      rcases hauth with h | h
      · exact hme h
      · rw [h] at hd; simp at hd

/-! ## 作者更正之后：受影响的句子和事实进过目 -/

/-- 作者更正带来的过目事项（推出，不存）：句子的出处、或它引用的片段，作者在句子写入之后被更正过 -/
def AuthorFlag (L : Log) (t : Time) (s : Sentence) : Prop :=
  ∃ p, (p = s.origin ∨ Target.frag p ∈ s.cites) ∧ fragAuthor (snap L t) p ≠ fragAuthor L p

/-- **定理（作者更正后不漏）**：任何版本里的任何一句，要么按现在的作者看仍然满足全部正文规则
    （作者是我或 AI；AI 起草标程度，我的话不标；“确定”有直接依据），要么进过目 -/
theorem sentence_ok_now_or_flagged {L : Log} {n : NodeId} {t : Time} {v : Version} {s : Sentence}
    (hR : Reachable check L) (hv : (n, t, v) ∈ versions L) (hs : s ∈ v.body) :
    AuthorFlag L t s ∨
    ((fragAuthor L s.origin = some .me ∨ fragAuthor L s.origin = some .ai) ∧
     (fragAuthor L s.origin = some .ai → s.degree ≠ none) ∧
     (fragAuthor L s.origin = some .me → s.degree = none) ∧
     (s.degree = some .certain → ∃ c ∈ s.cites, Direct L c)) := by
  rcases Classical.em (AuthorFlag L t s) with hf | hf
  · exact Or.inl hf
  · right
    have heq : ∀ p, (p = s.origin ∨ Target.frag p ∈ s.cites) →
        fragAuthor (snap L t) p = fragAuthor L p :=
      fun p hp => Classical.byContradiction fun h => hf ⟨p, hp, h⟩
    obtain ⟨l₁, e, l, ly, ex, hL, ht, _, hok⟩ := version_checked hR hv
    subst hL; subst ht
    rw [snap_split] at heq
    obtain ⟨hauth, hai, hme, hcert, -, -, -⟩ := hok s hs
    rw [← heq s.origin (Or.inl rfl)]
    refine ⟨hauth, hai, hme, fun hc => ?_⟩
    obtain ⟨c, hc, hd⟩ := hcert hc
    refine ⟨c, hc, ?_⟩
    cases c with
    | node _ => exact hd.elim
    | fact k => rw [split_append]; exact keyRecorded_append _ hd
    | frag p =>
      show fragAuthor _ p = some .me
      rw [← heq p (Or.inr hc)]; exact hd

/-- **定理（事实：作者更正后不漏）**：任何事实，出处现在的作者要么仍是我或外部发布者，
    要么在事实写入之后被更正过（进过目，由我决定作废） -/
theorem fact_ok_now_or_flagged {L : Log} {t : Time} {r : FactRec}
    (hR : Reachable check L) (h : (t, r) ∈ records L) :
    isMeOrExt (fragAuthor L r.origin) = true ∨
    fragAuthor (snap L t) r.origin ≠ fragAuthor L r.origin := by
  rcases Classical.em (fragAuthor (snap L t) r.origin = fragAuthor L r.origin) with he | he
  · left; rw [← he]; exact (facts_traceable_not_ai hR h).2
  · exact Or.inr he

/-- **定理（认知版本必有理由）**：每个认知版本（新建节点的第一个版本除外）都有理由，
    理由是写入那一刻已经存在的我的一句话（我的确认也存成我的话） -/
theorem cognitive_has_reason {L l₁ l : Log} {e : Entry} {n : NodeId} {b : Time} {v : Version}
    {ex : List Sentence} (hR : Reachable check L) (hL : L = l₁ ++ e :: l)
    (hop : e.op = .writeVersion n b v ex) (hk : v.kind = .cognitive) :
    ∃ p t' f, v.reason = some p ∧ fragAt L p = some (t', f) ∧ t' < l.length ∧
      fragAuthor l p = some .me := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  obtain ⟨hsome, hall⟩ := hc.2.2.2.1 hk
  cases hr : v.reason with
  | none => simp [hr] at hsome
  | some p =>
    simp only [hr, OptAll] at hall
    obtain ⟨⟨t', f⟩, hf⟩ := fragAuthor_isSome hall
    refine ⟨p, t', f, rfl, ?_, fragAt_lt hf, hall⟩
    rw [split_append]; exact fragAt_append_of_some _ hf

/-- **定理（结论和承诺逐句确认）**：任何版本里标为决定的结论或承诺的句子，都在那次写入的逐句确认清单里 -/
theorem decisions_confirmed {L l₁ l : Log} {e : Entry} (hR : Reachable check L)
    (hL : L = l₁ ++ e :: l) :
    (∀ n ly q src ends v ex, e.op = .newNode n ly q src ends v ex →
      ∀ s ∈ v.body, s.decision = true → s ∈ ex) ∧
    (∀ n b v ex, e.op = .writeVersion n b v ex →
      ∀ s ∈ v.body, s.decision = true → s ∈ ex) := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  constructor
  · intro n ly q src ends v ex hop s hs hd
    simp only [CheckP, hop] at hc
    exact (hc.2.2.2.2.2.2 s hs).2.2.2.2.2.2 hd
  · intro n b v ex hop s hs hd
    simp only [CheckP, hop] at hc
    exact (hc.2.2.2.2 s hs).2.2.2.2.2.2 hd

end MyLife
