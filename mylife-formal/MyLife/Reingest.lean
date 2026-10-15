import MyLife.Ingest
import MyLife.Facts

/-!
# 重新吸收（发现 AI 之前理解错了）

对同一份原件：先作废它之前产生的事实，再逐个片段重新抽取（不按“已处理”跳过），正文不动，
出处在这份原件里的节点列出来给我。

和“冲突只能由我裁决”（`void` 守卫）的交互：某项属性有待裁决的冲突时，Agent 不能作废它的事实，
所以重新吸收作废不了这些事实；本文件证明，这时冲突一直留在过目里，不会被重新吸收悄悄解决。
-/

namespace MyLife

/-- 这份原件里的片段产生的、还没作废的事实（写入时间） -/
def oldFacts (l : Log) (h : Hash) : List Time :=
  (records l).filterMap (fun x =>
    if x.1 ∉ voidedTimes l ∧ x.2.origin ∈ (fragsOf l h).map (fun f => f.id) then some x.1 else none)

def voidStep (acc : Log) (t : Time) : Log := tryStep acc ⟨.voidFact t, .agent⟩

/-- 重新抽取一个片段：不看它以前有没有处理过 -/
def processFragFresh (ex : Extractor) (l : Log) (p : Frag) : Log :=
  match ex p with
  | none => tryStep l ⟨.outcome p.id .unprocessed, .agent⟩
  | some cs =>
    tryStep (cs.foldl (absorb p) l) ⟨.outcome p.id (if cs.isEmpty then .noInfo else .produced), .agent⟩

def reingest (ex : Extractor) (h : Hash) (l : Log) : Log :=
  (fragsOf l h).foldl (processFragFresh ex) ((oldFacts l h).foldl voidStep l)

/-- 改变正文的写入 -/
def bodyOp : Op → Bool
  | .newNode _ _ _ _ _ _ _ => true
  | .writeVersion _ _ _ _ => true
  | .endNode _ _ => true
  | .move _ _ => true
  | _ => false

/-- Agent 的写入：不是我发起的，也不改正文 -/
def AgentWrite (e : Entry) : Prop := e.actor ≠ .me ∧ bodyOp e.op = false

theorem AddedOnly.mono {S S' : Entry → Prop} {l l' : Log} (h : ∀ e, S e → S' e)
    (ha : AddedOnly S l l') : AddedOnly S' l l' := by
  obtain ⟨ext, hl, hs⟩ := ha
  exact ⟨ext, hl, fun e he => h e (hs e he)⟩

theorem candEntry_agent (p : Frag) (l : Log) (c : Cand) : AgentWrite (candEntry p l c) := by
  cases c with
  | fact k v => unfold AgentWrite; by_cases hl : LiveSame l k v <;> simp [candEntry, hl, bodyOp]
  | link n => exact ⟨by simp [candEntry], rfl⟩
  | draft n v => exact ⟨by simp [candEntry], rfl⟩

theorem processFragFresh_agent (ex : Extractor) (l : Log) (p : Frag) :
    AddedOnly AgentWrite l (processFragFresh ex l p) := by
  unfold processFragFresh
  split
  · exact AddedOnly.tryStep _ ⟨by simp, rfl⟩
  · next cs _ =>
    apply AddedOnly.trans _ (AddedOnly.tryStep _ ⟨by simp, rfl⟩)
    exact foldl_inv (absorb p) (AddedOnly AgentWrite l) cs l (AddedOnly.refl _ _)
      (fun acc c _ h => h.trans (AddedOnly.tryStep _ (candEntry_agent p acc c)))

theorem voidStep_agent (acc : Log) (t : Time) : AddedOnly AgentWrite acc (voidStep acc t) :=
  AddedOnly.tryStep _ ⟨by simp, rfl⟩

theorem voidFold_agent (ts : List Time) (l : Log) : AddedOnly AgentWrite l (ts.foldl voidStep l) :=
  foldl_inv voidStep (AddedOnly AgentWrite l) ts l (AddedOnly.refl _ _)
    (fun acc t _ h => h.trans (voidStep_agent acc t))

/-- 重新吸收只做 Agent 能做的写入：不是我发起的，也不改正文 -/
theorem reingest_agent (ex : Extractor) (h : Hash) (l : Log) :
    AddedOnly AgentWrite l (reingest ex h l) :=
  (voidFold_agent _ l).trans
    (foldl_inv (processFragFresh ex) (AddedOnly AgentWrite _) _ _ (AddedOnly.refl _ _)
      (fun acc p _ h => h.trans (processFragFresh_agent ex acc p)))

theorem reingest_reachable (ex : Extractor) (h : Hash) {l : Log} (hR : Reachable check l) :
    Reachable check (reingest ex h l) := by
  unfold reingest
  apply foldl_inv (processFragFresh ex) (Reachable check)
  · exact foldl_inv voidStep (Reachable check) _ l hR (fun _ _ _ ha => tryStep_reachable _ ha)
  · intro acc p _ ha
    unfold processFragFresh
    split
    · exact tryStep_reachable _ ha
    · exact tryStep_reachable _
        (foldl_inv (absorb p) (Reachable check) _ acc ha (fun _ _ _ hb => tryStep_reachable _ hb))

/-! ## 正文不动 -/

theorem views_of_nonbody {l : Log} {e : Entry} (h : bodyOp e.op = false) :
    versions (e :: l) = versions l ∧ (∀ n, latest (e :: l) n = latest l n) ∧
    (∀ n, active (e :: l) n = active l n) ∧ (∀ n, layerOf (e :: l) n = layerOf l n) := by
  rcases e with ⟨op, actor⟩
  cases op <;> simp [bodyOp] at h <;> simp [versions, latest, active, layerOf]

theorem views_of_agentWrites {l L : Log} (h : AddedOnly AgentWrite l L) :
    versions L = versions l ∧ (∀ n, latest L n = latest l n) ∧
    (∀ n, active L n = active l n) ∧ (∀ n, layerOf L n = layerOf l n) := by
  obtain ⟨ext, rfl, hs⟩ := h
  induction ext with
  | nil => exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | cons e ext ih =>
    have ih := ih (fun e' he' => hs e' (List.mem_cons_of_mem _ he'))
    have he := views_of_nonbody (l := ext ++ l) (hs e (List.mem_cons_self _ _)).2
    exact ⟨he.1.trans ih.1, fun n => (he.2.1 n).trans (ih.2.1 n),
      fun n => (he.2.2.1 n).trans (ih.2.2.1 n), fun n => (he.2.2.2 n).trans (ih.2.2.2 n)⟩

/-- **定理（重新吸收不动正文）**：所有版本、每个节点的当前版本、有效 / 结束和所在的层都不变 -/
theorem reingest_body_untouched (ex : Extractor) (h : Hash) (l : Log) :
    versions (reingest ex h l) = versions l ∧ (∀ n, latest (reingest ex h l) n = latest l n) ∧
    (∀ n, active (reingest ex h l) n = active l n) ∧
    (∀ n, layerOf (reingest ex h l) n = layerOf l n) :=
  views_of_agentWrites (reingest_agent ex h l)

/-! ## 旧事实先作废；作废不了的，冲突留在过目里 -/

theorem recordAt_of_mem {l : Log} {t : Time} {r : FactRec} (h : (t, r) ∈ records l) :
    recordAt l t = some r := by
  unfold recordAt
  cases hf : (records l).find? (fun x => x.1 == t) with
  | none =>
    have := List.find?_eq_none.mp hf (t, r) h
    simp at this
  | some x =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp at hp
    obtain ⟨t', r'⟩ := x
    simp at hp; subst hp
    simp [records_time_unique hm h]

theorem recordAt_append_of_some {l : Log} {t : Time} {r : FactRec} :
    ∀ (ext : Log), recordAt l t = some r → recordAt (ext ++ l) t = some r
  | [], h => h
  | e :: ext, h => by
    have ih := recordAt_append_of_some ext h
    have hlt := recordAt_lt ih
    exact recordAt_of_mem (records_cons_sub e (recordAt_mem ih))

theorem voidedTimes_append {l : Log} {t : Time} :
    ∀ (ext : Log), t ∈ voidedTimes l → t ∈ voidedTimes (ext ++ l)
  | [], h => h
  | e :: ext, h => by
    simp only [List.cons_append, voidedTimes, List.mem_append]
    exact Or.inr (voidedTimes_append ext h)

/-- 冲突一旦待裁决，之后只要都不是我发起的写入，它就一直在 -/
theorem conflicts_persist {mid L : Log} {k : FactKey} {c : Time} (hR : Reachable check L)
    (h : AddedOnly (fun e => e.actor ≠ .me) mid L) (hc : c ∈ (fstate mid k).conflicts) :
    c ∈ (fstate L k).conflicts := by
  obtain ⟨ext, rfl, hs⟩ := h
  induction ext with
  | nil => exact hc
  | cons e ext ih =>
    have hR' := hR
    exact conflicts_only_me hR' (hs e (List.mem_cons_self _ _))
      (ih (fun e' he' => hs e' (List.mem_cons_of_mem _ he')) (Reachable.of_cons hR).1)

theorem foldl_witness {α : Type} (f : Log → α → Log) (S : Entry → Prop) (Q : Log → α → Prop)
    (base : Log) (hf : ∀ acc a, AddedOnly S acc (f acc a))
    (hq : ∀ acc a, Extends base acc → Q (f acc a) a) :
    ∀ (as : List α) (acc : Log), Extends base acc → ∀ a ∈ as,
      ∃ mid, Q mid a ∧ AddedOnly S mid (as.foldl f acc)
  | [], _, _, a, ha => by simp at ha
  | b :: bs, acc, hb, a, ha => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨f acc a, hq acc a hb,
        foldl_inv f (AddedOnly S (f acc a)) bs _ (AddedOnly.refl _ _)
          (fun acc' c _ h => h.trans (hf acc' c))⟩
    · exact foldl_witness f S Q base hf hq bs (f acc b) (hb.trans (hf acc b).extends) a ha

/-- 作废一步：要么作废成了，要么这项属性有待裁决的冲突（Agent 不能作废） -/
theorem voidStep_effect {l acc : Log} {t : Time} (he : Extends l acc) :
    recordAt l t = none ∨ t ∈ voidedTimes (voidStep acc t) ∨
      ∃ r, recordAt l t = some r ∧ (fstate (voidStep acc t) r.key).conflicts ≠ [] := by
  cases hr : recordAt l t with
  | none => exact Or.inl rfl
  | some r =>
    right
    obtain ⟨ext, rfl⟩ := he
    have hra := recordAt_append_of_some ext hr
    unfold voidStep tryStep
    split
    · left; simp [voidedTimes]
    · next hc =>
      right
      refine ⟨r, rfl, ?_⟩
      have hn : ¬ CheckP {} (ext ++ l) ⟨.voidFact t, .agent⟩ := by
        intro h; exact hc (decide_eq_true h)
      simp only [CheckP, hra, OptAll, Option.isSome_some, true_and] at hn
      intro hnil
      exact hn (fun _ _ => hnil)

/-- **定理（重新吸收先作废旧事实）**：这份原件之前产生的每条事实，重新吸收后要么已经作废，
    要么它那项属性有待我裁决的冲突（作废被挡下，冲突留在过目里，不会被悄悄解决） -/
theorem reingest_voids_old (ex : Extractor) (h : Hash) {l : Log} (hR : Reachable check l) :
    ∀ t ∈ oldFacts l h, t ∈ voidedTimes (reingest ex h l) ∨
      ∃ r, recordAt l t = some r ∧ (fstate (reingest ex h l) r.key).conflicts ≠ [] := by
  intro t ht
  have hrec : ∃ r, recordAt l t = some r := by
    unfold oldFacts at ht
    rw [List.mem_filterMap] at ht
    obtain ⟨x, hx, hxt⟩ := ht
    split at hxt
    · cases hxt; exact ⟨x.2, recordAt_of_mem hx⟩
    · cases hxt
  obtain ⟨r, hr⟩ := hrec
  have hRfin := reingest_reachable ex h hR
  obtain ⟨mid, hq, hmid⟩ := foldl_witness voidStep AgentWrite
    (fun acc t => recordAt l t = none ∨ t ∈ voidedTimes acc ∨
      ∃ r, recordAt l t = some r ∧ (fstate acc r.key).conflicts ≠ [])
    l voidStep_agent (fun acc t he => voidStep_effect he) (oldFacts l h) l (Extends.refl l) t ht
  have hall : AddedOnly AgentWrite mid (reingest ex h l) :=
    hmid.trans (foldl_inv (processFragFresh ex) (AddedOnly AgentWrite _) _ _ (AddedOnly.refl _ _)
      (fun acc p _ h => h.trans (processFragFresh_agent ex acc p)))
  rcases hq with hnone | hv | ⟨r', hr', hc⟩
  · rw [hr] at hnone; cases hnone
  · obtain ⟨ext, heq, _⟩ := hall
    left; rw [heq]; exact voidedTimes_append ext hv
  · right
    rw [hr] at hr'; cases hr'
    refine ⟨r, hr, ?_⟩
    obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc
    have := conflicts_persist hRfin (hall.mono (fun e he => he.1)) hcm
    intro hnil; rw [hnil] at this; simp at this

/-! ## 列出受影响的节点 -/

/-- 重新吸收后列给我的节点：当前版本里有句子出处在这份原件里的有效节点 -/
def reingestAffected (l : Log) (h : Hash) : List NodeId :=
  (nodeIds l).filter (fun n => decide (active l n = true ∧
    OptAll (latest l n) (fun x => ∃ s ∈ x.2.body, s.origin ∈ (fragsOf l h).map (fun f => f.id))))

/-- **定理**：出处在这份原件里的有效节点都会列出来；而且重新吸收不改正文，列表前后一样 -/
theorem reingestAffected_complete {l : Log} {h : Hash} {n : NodeId} {x : Time × Version} {s : Sentence}
    (hact : active l n = true) (hx : latest l n = some x) (hs : s ∈ x.2.body)
    (ho : s.origin ∈ (fragsOf l h).map (fun f => f.id)) : n ∈ reingestAffected l h := by
  unfold reingestAffected
  rw [List.mem_filter]
  refine ⟨active_mem_nodeIds hact, ?_⟩
  simp only [decide_eq_true_eq, hx, OptAll]
  exact ⟨hact, s, hs, ho⟩

end MyLife
