import MyLife.History

/-!
# 可追溯、看得出谁起草、只有我能拍板（核心思想 4、核心原则 2、Agent 的边界）

这些性质都是“逐条写入”的：只要每条写入在它写入那一刻通过了检查，再加上“查到的东西永远查得到”
（只追加带来的单调性），就对整个日志成立。
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

/-- 只能由我做的写入：正文的新建、新版本、结束和移层，引用跟上，冲突裁决，定权威作者，删除 -/
def meOnly : Op → Bool
  | .adopt _ _ => true
  | .setAuthority _ _ => true
  | .newNode _ _ _ _ _ _ _ => true
  | .writeVersion _ _ _ _ => true
  | .endNode _ _ => true
  | .move _ _ => true
  | .ack _ _ => true
  | .deleteRecord _ => true
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

/-- **定理**：每条事实的出处片段都在事实之前就存在，作者是我或外部发布者，不是 AI，也不是作者不明 -/
theorem facts_traceable_not_ai {L : Log} {t : Time} {r : FactRec}
    (hR : Reachable check L) (h : (t, r) ∈ records L) :
    (∃ t' f, fragAt L r.origin = some (t', f) ∧ t' < t) ∧ isMeOrExt (fragAuthor L r.origin) = true := by
  obtain ⟨l₁, e, l, hL, hop, ht⟩ := records_entry h
  subst hL; subst ht
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  have ha := hc.1
  cases hf : fragAt l r.origin with
  | none => simp [fragAuthor, hf, isMeOrExt] at ha
  | some x =>
    have hlt := fragAt_lt (f := x.2) (by simpa using hf)
    have hL' : fragAt (l₁ ++ e :: l) r.origin = some x := by
      rw [split_append]; exact fragAt_append_of_some _ hf
    refine ⟨⟨x.1, x.2, by simpa using hL', hlt⟩, ?_⟩
    have : fragAuthor (l₁ ++ e :: l) r.origin = fragAuthor l r.origin := by
      simp [fragAuthor, hL', hf]
    rw [this]; exact ha

/-- 追加的来源同样不能是 AI 的话 -/
theorem added_sources_not_ai {L l₁ l : Log} {e : Entry} {k : FactKey} {v : Value} {p : FragId}
    (hR : Reachable check L) (hL : L = l₁ ++ e :: l) (hop : e.op = .addSource k v p) :
    isMeOrExt (fragAuthor L p) = true := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  rcases isMeOrExt_some hc.1 with h | ⟨q, h⟩
  · rw [split_append, fragAuthor_append_of_some _ h]; rfl
  · rw [split_append, fragAuthor_append_of_some _ h]; rfl

/-! ## 每句正文都追得到出处，并且永远看得出是谁起草的 -/

/-- 句子的三种来源，由出处的作者和文字改动推出（不另存） -/
inductive Drafter where
  | verbatim    -- 原话
  | tidied      -- 整理
  | aiDrafted   -- AI 起草（经我确认）
  deriving DecidableEq, Repr

def drafter (L : Log) (s : Sentence) : Option Drafter :=
  match fragAt L s.origin with
  | some (_, f) =>
    match f.author with
    | .me => some (if f.fp = s.text then .verbatim else .tidied)
    | .ai => some .aiDrafted
    | _ => none
  | none => none

theorem drafter_append {L : Log} {s : Sentence} {d : Drafter} (ext : Log)
    (h : drafter L s = some d) : drafter (ext ++ L) s = some d := by
  unfold drafter at *
  cases hf : fragAt L s.origin with
  | none => simp [hf] at h
  | some x => rw [fragAt_append_of_some ext hf]; simpa [hf] using h

theorem direct_append {l : Log} {c : Target} (ext : Log) (h : Direct l c) : Direct (ext ++ l) c := by
  cases c with
  | node _ => exact h
  | fact k => exact keyRecorded_append ext h
  | frag p => exact fragAuthor_append_of_some ext h

theorem targetOK_append {l : Log} {c : Target} (ext : Log) (h : TargetOK l c) :
    TargetOK (ext ++ l) c := by
  cases c with
  | node m => exact created_isSome_append ext h
  | fact k => exact keyRecorded_append ext h
  | frag p => exact fragAt_isSome_append ext h

/-- **定理（可追溯 + 看得出谁起草）**：任何版本（含历史版本）里的每一句，
    出处片段都在这个版本之前存在；它的来源类别（原话 / 整理 / AI 起草）有定义，并且以后永远不变；
    引用的东西都存在。 -/
theorem sentence_traceable {L : Log} {n : NodeId} {t : Time} {v : Version} {s : Sentence}
    (hR : Reachable check L) (hv : (n, t, v) ∈ versions L) (hs : s ∈ v.body) :
    (∃ t' f, fragAt L s.origin = some (t', f) ∧ t' < t) ∧
    (∃ d, drafter L s = some d ∧ ∀ ext, drafter (ext ++ L) s = some d) ∧
    (∀ c ∈ s.cites, TargetOK L c) := by
  obtain ⟨l₁, e, l, ly, ex, hL, ht, _, hok⟩ := version_checked hR hv
  subst hL; subst ht
  have hso := hok s hs
  obtain ⟨hauth, -, -, -, hcites, -, -⟩ := hso
  have hlift : ∀ {x}, fragAt l s.origin = some x → fragAt (l₁ ++ e :: l) s.origin = some x := by
    intro x hx; rw [split_append]; exact fragAt_append_of_some _ hx
  cases hf : fragAt l s.origin with
  | none => simp [fragAuthor, hf] at hauth
  | some x =>
    obtain ⟨t', f⟩ := x
    have hlt := fragAt_lt hf
    refine ⟨⟨t', f, hlift hf, hlt⟩, ?_, ?_⟩
    · have hd : ∃ d, drafter (l₁ ++ e :: l) s = some d := by
        unfold drafter
        rw [hlift hf]
        simp only [fragAuthor, hf, Option.map_some', Option.some.injEq] at hauth
        rcases hauth with h | h <;> simp [h]
      obtain ⟨d, hd⟩ := hd
      exact ⟨d, hd, fun ext => drafter_append ext hd⟩
    · intro c hc
      rw [split_append]
      exact targetOK_append _ (hcites c hc)

/-- **定理（程度标记）**：AI 起草的句子都标了程度；标“确定”的至少引用一处直接依据（事实或我的话）；
    我的原话和整理不标程度。 -/
theorem degree_rules {L : Log} {n : NodeId} {t : Time} {v : Version} {s : Sentence}
    (hR : Reachable check L) (hv : (n, t, v) ∈ versions L) (hs : s ∈ v.body) :
    (drafter L s = some .aiDrafted →
        s.degree ≠ none ∧ (s.degree = some .certain → ∃ c ∈ s.cites, Direct L c)) ∧
    (drafter L s = some .verbatim ∨ drafter L s = some .tidied → s.degree = none) := by
  obtain ⟨l₁, e, l, ly, ex, hL, ht, _, hok⟩ := version_checked hR hv
  subst hL; subst ht
  obtain ⟨hauth, hai, hme, hcert, -, -, -⟩ := hok s hs
  have hlift : ∀ {x}, fragAt l s.origin = some x → fragAt (l₁ ++ e :: l) s.origin = some x := by
    intro x hx; rw [split_append]; exact fragAt_append_of_some _ hx
  cases hf : fragAt l s.origin with
  | none => simp [fragAuthor, hf] at hauth
  | some x =>
    obtain ⟨t', f⟩ := x
    have hdr : drafter (l₁ ++ e :: l) s =
        (match f.author with
         | .me => some (if f.fp = s.text then .verbatim else .tidied)
         | .ai => some .aiDrafted
         | _ => none) := by
      unfold drafter; rw [hlift hf]
    have hfa : fragAuthor l s.origin = some f.author := by simp [fragAuthor, hf]
    rw [hdr]
    constructor
    · intro hd
      cases ha : f.author with
      | ai =>
        have hai' := hai (by rw [hfa, ha])
        refine ⟨hai', fun hc => ?_⟩
        obtain ⟨c, hc, hd⟩ := hcert hc
        exact ⟨c, hc, by rw [split_append]; exact direct_append _ hd⟩
      | me => rw [ha] at hd; simp at hd; split at hd <;> cases hd
      | ext _ => rw [ha] at hd; cases hd
      | unknown => rw [ha] at hd; cases hd
    · intro hd
      cases ha : f.author with
      | me => exact hme (by rw [hfa, ha])
      | ai => rw [ha] at hd; simp at hd
      | ext _ => rw [ha] at hd; simp at hd
      | unknown => rw [ha] at hd; simp at hd

/-- **定理（认知版本必有理由）**：每个认知版本（新建节点的第一个版本除外）都有理由，
    理由是我的一句话（我的确认也存成我的话），在这个版本之前就存在 -/
theorem cognitive_has_reason {L l₁ l : Log} {e : Entry} {n : NodeId} {b : Time} {v : Version}
    {ex : List Sentence} (hR : Reachable check L) (hL : L = l₁ ++ e :: l)
    (hop : e.op = .writeVersion n b v ex) (hk : v.kind = .cognitive) :
    ∃ p t' f, v.reason = some p ∧ fragAt L p = some (t', f) ∧ f.author = .me ∧ t' < l.length := by
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  obtain ⟨hsome, hall⟩ := hc.2.2.2.1 hk
  cases hr : v.reason with
  | none => simp [hr] at hsome
  | some p =>
    simp only [hr, OptAll] at hall
    cases hf : fragAt l p with
    | none => simp [fragAuthor, hf] at hall
    | some x =>
      obtain ⟨t', f⟩ := x
      simp [fragAuthor, hf] at hall
      refine ⟨p, t', f, rfl, ?_, hall, fragAt_lt hf⟩
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
