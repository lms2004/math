import MyLife.Provenance

/-!
# 事实的当前值（原始依据层 · 事实）

当前值由事实记录推出：同一作者的新值接替旧值；定了权威作者的，权威作者的新值接替；
其余不同作者的不同值标为冲突，当前值不变，交给我裁决。

本文件证明：
* 冲突不会悄悄改掉当前值；
* 当前值永远不是 AI 的话；
* 冲突只能由我解决——前提是检查里有 `void` 守卫：有待裁决的冲突时，Agent 不能作废这项属性的事实。
  没有这个守卫时，Agent 一次“撤销抽取”就能悄悄替我裁决冲突，反例见 `MyLife.Counterexamples`；
* 认识层的写入不改变任何依据（信息只从依据流向认识）。
-/

namespace MyLife

theorem voided_lt {L : Log} (hR : Reachable check L) : ∀ t ∈ voidedTimes L, t < L.length := by
  induction hR with
  | nil => intro t ht; simp [voidedTimes] at ht
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    intro t ht
    rcases e with ⟨op, actor⟩
    cases op
    case voidFact t₀ =>
      simp only [voidedTimes, List.singleton_append, List.mem_cons] at ht
      simp only [CheckP] at hcP
      rcases ht with rfl | ht
      · cases hr : recordAt l t with
        | none => simp [hr] at hcP
        | some r => have := recordAt_lt hr; simp; nomega
      · have := ih t ht; simp; nomega
    all_goals
      simp only [voidedTimes, List.nil_append] at ht
      have := ih t ht; simp; nomega

theorem fstate_cons_of_not_void {l : Log} {e : Entry} (k : FactKey)
    (h : ∀ t, e.op ≠ .voidFact t) :
    fstate (e :: l) k = fstep (voidedTimes l) l e k (fstate l k) := by
  have hv : voidedTimes (e :: l) = voidedTimes l := by
    simp only [voidedTimes]
    first
      | rfl
      | (split
         · next t hop => exact absurd hop (h t)
         · rfl)
  simp only [fstate, fstateAux, hv]

/-! ## 当前值怎么变 -/

/-- 第一个值直接成为当前值 -/
theorem first_value {l : Log} {e : Entry} {r : FactRec} {k : FactKey}
    (hl : Reachable check l) (hop : e.op = .addFact r) (hk : r.key = k)
    (hnone : (fstate l k).cur = none) :
    (fstate (e :: l) k).cur = some ⟨l.length, r, fragAuthor l r.origin⟩ := by
  have hnv : l.length ∉ voidedTimes l := fun h => Nat.lt_irrefl _ (voided_lt hl _ h)
  rw [fstate_cons_of_not_void k (by simp [hop])]
  simp [fstep, hop, hk, hnv, hnone]

/-- 同一作者的新值接替旧值 -/
theorem same_author_supersedes {l : Log} {e : Entry} {r : FactRec} {k : FactKey} {old : Cur}
    (hl : Reachable check l) (hop : e.op = .addFact r) (hk : r.key = k)
    (hcur : (fstate l k).cur = some old) (hsame : old.author = fragAuthor l r.origin) :
    (fstate (e :: l) k).cur = some ⟨l.length, r, fragAuthor l r.origin⟩ := by
  have hnv : l.length ∉ voidedTimes l := fun h => Nat.lt_irrefl _ (voided_lt hl _ h)
  rw [fstate_cons_of_not_void k (by simp [hop])]
  simp [fstep, hop, hk, hnv, hcur, hsame]

/-- **定理（冲突不悄悄改值）**：没定权威作者时，另一个作者给出的不同值标为冲突，当前值保持不变 -/
theorem conflict_keeps_current {l : Log} {e : Entry} {r : FactRec} {k : FactKey} {old : Cur}
    (hl : Reachable check l) (hop : e.op = .addFact r) (hk : r.key = k)
    (hcur : (fstate l k).cur = some old) (hdiff : old.author ≠ fragAuthor l r.origin)
    (hauth : authority l k = none) :
    (fstate (e :: l) k).cur = some old ∧ l.length ∈ (fstate (e :: l) k).conflicts := by
  have hnv : l.length ∉ voidedTimes l := fun h => Nat.lt_irrefl _ (voided_lt hl _ h)
  rw [fstate_cons_of_not_void k (by simp [hop])]
  simp [fstep, hop, hk, hnv, hcur, hdiff, hauth]

/-- 定了以哪个作者为准的属性，这个作者的新值直接接替 -/
theorem authority_supersedes {l : Log} {e : Entry} {r : FactRec} {k : FactKey} {old : Cur} {b : Author}
    (hl : Reachable check l) (hop : e.op = .addFact r) (hk : r.key = k)
    (hcur : (fstate l k).cur = some old) (hauth : authority l k = some b)
    (hb : fragAuthor l r.origin = some b) :
    (fstate (e :: l) k).cur = some ⟨l.length, r, fragAuthor l r.origin⟩ := by
  have hnv : l.length ∉ voidedTimes l := fun h => Nat.lt_irrefl _ (voided_lt hl _ h)
  rw [fstate_cons_of_not_void k (by simp [hop])]
  by_cases hs : old.author = fragAuthor l r.origin
  · simp [fstep, hop, hk, hnv, hcur, hs]
  · simp [fstep, hop, hk, hnv, hcur, hs, hauth, hb]

/-- 设计的直接后果（值得确认是不是想要的）：定了权威作者以后，其他作者的不同值既不改当前值，
    也不再作为冲突提出，状态完全不变 -/
theorem authority_silences_others {l : Log} {e : Entry} {r : FactRec} {k : FactKey} {old : Cur}
    {b : Author} (hl : Reachable check l) (hop : e.op = .addFact r) (hk : r.key = k)
    (hcur : (fstate l k).cur = some old) (hdiff : old.author ≠ fragAuthor l r.origin)
    (hauth : authority l k = some b) (hb : fragAuthor l r.origin ≠ some b) :
    fstate (e :: l) k = fstate l k := by
  have hnv : l.length ∉ voidedTimes l := fun h => Nat.lt_irrefl _ (voided_lt hl _ h)
  rw [fstate_cons_of_not_void k (by simp [hop])]
  have hb' : ¬ (some b = fragAuthor l r.origin) := fun h => hb h.symm
  simp [fstep, hop, hk, hnv, hcur, hdiff, hauth, hb']

/-! ## 当前值永远不是 AI 的话 -/

theorem fstep_cur (V : List Time) (l : Log) (e : Entry) (k : FactKey) (s : FState) :
    (fstep V l e k s).cur = s.cur ∨
    (∃ r, e.op = .addFact r ∧ (fstep V l e k s).cur = some ⟨l.length, r, fragAuthor l r.origin⟩) ∨
    (∃ k' t r, e.op = .adopt k' t ∧ recordAt l t = some r ∧
      (fstep V l e k s).cur = some ⟨t, r, fragAuthor l r.origin⟩) := by
  unfold fstep
  split
  · next r hop =>
    split
    · split
      · exact Or.inr (Or.inl ⟨r, hop, rfl⟩)
      · split
        · exact Or.inr (Or.inl ⟨r, hop, rfl⟩)
        · split
          · split
            · exact Or.inr (Or.inl ⟨r, hop, rfl⟩)
            · exact Or.inl rfl
          · exact Or.inl rfl
    · exact Or.inl rfl
  · next k' t hop =>
    split
    · split
      · next r hr => exact Or.inr (Or.inr ⟨k', t, r, hop, hr, rfl⟩)
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **定理**：任何时候，事实的当前值都出自我或外部发布者，不是 AI 的话 -/
theorem current_not_ai {L : Log} (hR : Reachable check L) (k : FactKey) :
    OptAll (fstate L k).cur (fun c => isMeOrExt c.author = true) := by
  suffices h : ∀ V, OptAll (fstateAux V L k).cur (fun c => isMeOrExt c.author = true) from h _
  intro V
  induction hR with
  | nil => simp [fstateAux, OptAll]
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    simp only [fstateAux]
    rcases fstep_cur V l e k (fstateAux V l k) with h | ⟨r, hop, h⟩ | ⟨k', t, r, hop, hr, h⟩
    · rw [h]; exact ih
    · rw [h]
      simp only [CheckP, hop] at hcP
      exact hcP.1
    · rw [h]
      exact (facts_traceable_not_ai hl (recordAt_mem hr)).2

/-! ## 冲突只能由我解决 -/

theorem records_time_unique : ∀ {l : Log} {t : Time} {r r' : FactRec},
    (t, r) ∈ records l → (t, r') ∈ records l → r = r'
  | [], _, _, _, h, _ => by simp [records] at h
  | e :: l, t, r, r', h, h' => by
    have lt : ∀ {x}, x ∈ records l → x.1 < l.length := records_lt
    rcases e with ⟨op, actor⟩
    cases op
    case addFact r₀ =>
      simp only [records, List.mem_append, List.mem_singleton] at h h'
      rcases h with h | h <;> rcases h' with h' | h'
      · simp at h h'; rw [h.2, h'.2]
      · simp at h; have := lt h'; simp [h.1] at this
      · simp at h'; have := lt h; simp [h'.1] at this
      · exact records_time_unique h h'
    all_goals
      simp only [records, List.nil_append] at h h'
      exact records_time_unique h h'

theorem fstateAux_congr {V V' : List Time} {k : FactKey} : ∀ {l : Log}, Reachable check l →
    (∀ t r, (t, r) ∈ records l → r.key = k → (t ∈ V ↔ t ∈ V')) →
    fstateAux V l k = fstateAux V' l k
  | [], _, _ => rfl
  | e :: l, hR, h => by
    obtain ⟨hl, hc⟩ := hR.of_cons
    have ih := fstateAux_congr hl (fun t r hr hk => h t r (records_cons_sub e hr) hk)
    simp only [fstateAux, ih]
    have hcP := checkP_of_check hc
    rcases e with ⟨op, actor⟩
    cases op
    case addFact r =>
      by_cases hk : r.key = k
      · have hm := h l.length r (by simp [records]) hk
        simp [fstep, hk, hm]
      · simp [fstep, hk]
    case adopt k' t =>
      simp only [CheckP] at hcP
      obtain ⟨_, _, hkey, _⟩ := hcP
      by_cases hk : k' = k
      · cases hr : recordAt l t with
        | none => simp [fstep, hk, hr]
        | some r =>
          simp only [hr, OptAll] at hkey
          have hm := h t r (records_cons_sub _ (recordAt_mem hr)) (hkey.trans hk)
          simp [fstep, hk, hm, hr]
      · simp [fstep, hk]
    all_goals rfl

theorem fstep_conflicts_mono {V : List Time} {l : Log} {e : Entry} {k : FactKey} {s : FState} {t : Time}
    (hop : ∀ k' t', e.op ≠ .adopt k' t') (ht : t ∈ s.conflicts) : t ∈ (fstep V l e k s).conflicts := by
  unfold fstep
  split
  · split
    · split
      · exact ht
      · split
        · exact ht
        · split
          · split
            · exact ht
            · exact ht
          · exact List.mem_cons_of_mem _ ht
    · exact ht
  · next k' t' h => exact absurd h (hop k' t')
  · exact ht

/-- **定理（冲突只能由我裁决）**：一项属性有待裁决的冲突时，任何不是我发起的写入都不会让它消失 -/
theorem conflicts_only_me {l : Log} {e : Entry} {k : FactKey} {t : Time}
    (hR : Reachable check (e :: l)) (hme : e.actor ≠ .me) (ht : t ∈ (fstate l k).conflicts) :
    t ∈ (fstate (e :: l) k).conflicts := by
  obtain ⟨hl, hc⟩ := hR.of_cons
  have hcP := checkP_of_check hc
  rcases e with ⟨op, actor⟩
  cases op
  case voidFact t₀ =>
    simp only [CheckP] at hcP
    obtain ⟨hs, hg⟩ := hcP
    cases hr : recordAt l t₀ with
    | none => simp [hr] at hs
    | some r =>
      simp only [hr, OptAll] at hg
      have hg := hg hme trivial
      have hkr : r.key ≠ k := by
        intro h; rw [h] at hg; rw [hg] at ht; simp at ht
      have heq : fstate ({ op := .voidFact t₀, actor := actor } :: l) k = fstate l k := by
        simp only [fstate, fstateAux, voidedTimes, List.singleton_append]
        simp only [fstep]
        apply fstateAux_congr hl
        intro t' r' hr' hk'
        simp only [List.mem_cons]
        constructor
        · rintro (rfl | h)
          · exfalso
            have := records_time_unique hr' (recordAt_mem hr)
            subst this; exact hkr hk'
          · exact h
        · exact Or.inr
      rw [heq]; exact ht
  case adopt k' t' =>
    simp only [CheckP] at hcP
    exact absurd hcP.1 hme
  all_goals
    rw [fstate_cons_of_not_void k (by intros; simp)]
    exact fstep_conflicts_mono (by intros; simp) ht

/-! ## 信息只从依据流向认识 -/

/-- 认识层和维护层的写入 -/
def cognitionOp : Op → Bool
  | .newNode _ _ _ _ _ _ _ => true
  | .writeVersion _ _ _ _ => true
  | .endNode _ _ => true
  | .move _ _ => true
  | .ack _ _ => true
  | .link _ _ => true
  | .draft _ _ _ => true
  | _ => false

/-- **定理（认识变了不回头改依据）**：认识层的写入不改变片段、事实记录、作废记录和任何事实的当前值 -/
theorem evidence_unaffected_by_cognition {l : Log} {e : Entry} (h : cognitionOp e.op = true) :
    frags (e :: l) = frags l ∧ records (e :: l) = records l ∧
    voidedTimes (e :: l) = voidedTimes l ∧ ∀ k, fstate (e :: l) k = fstate l k := by
  rcases e with ⟨op, actor⟩
  cases op <;> simp [cognitionOp] at h <;>
    simp [frags, newFrags, records, voidedTimes, fstate, fstateAux, fstep]

end MyLife
