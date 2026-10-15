import MyLife.History

/-!
# 不重复：同一身份只存一份（核心原则 3、核心原则 1）

* 原件按哈希只存一份，再存只追加保存记录。
* 片段 id 唯一：按 id 查到的就是那一个片段。
* 同一个问题只有一个有效节点。“任何时刻只保持一个有效的阶段节点”是它的特例：
  阶段节点都回答同一个问题“我现在处于哪个阶段”。
  分裂、合并、换阶段必须在同一次写入里新建并结束旧节点（`newNode` 的 `ends`），
  否则中间会出现同一问题两个有效节点；反例见 `MyLife.Counterexamples`。
* 事实：同一身份、同样的值，没作废的记录只有一条（别的来源只是追加来源）。
-/

namespace MyLife

/-! ## 原件 -/

def sourceHashes : Log → List Hash
  | [] => []
  | e :: l =>
    (match e.op with
     | .saveSource h _ => [h]
     | _ => []) ++ sourceHashes l

theorem hashSaved_of_mem : ∀ {l : Log} {h : Hash}, h ∈ sourceHashes l → hashSaved l h = true
  | [], _, hm => by simp [sourceHashes] at hm
  | e :: l, h, hm => by
    simp only [sourceHashes, List.mem_append] at hm
    simp only [hashSaved, Bool.or_eq_true]
    rcases hm with hm | hm
    · split at hm
      · next h' fs hop => simp at hm; subst hm; simp [hop]
      · simp at hm
    · exact Or.inr (hashSaved_of_mem hm)

/-- **定理**：每份原件（按内容哈希）只存一份 -/
theorem sources_unique {L : Log} (hR : Reachable check L) : (sourceHashes L).Nodup := by
  induction hR with
  | nil => simp [sourceHashes]
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    rcases e with ⟨op, actor⟩
    cases op
    case saveSource h fs =>
      simp only [CheckP] at hcP
      simp only [sourceHashes, List.singleton_append, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      rw [hashSaved_of_mem hm] at hcP
      simp at hcP
    all_goals simpa [sourceHashes] using ih

/-! ## 片段 -/

theorem find_id_of_nodup : ∀ {fs : List Frag} {f : Frag}, (fs.map (fun g => g.id)).Nodup → f ∈ fs →
    fs.find? (fun g => g.id == f.id) = some f
  | [], _, _, h => by simp at h
  | g :: gs, f, hnd, hf => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hf'
    · simp
    · have hne : g.id ≠ f.id := by
        intro h; apply hnd.1; rw [h]; exact List.mem_map.mpr ⟨f, hf', rfl⟩
      simp [List.find?_cons, hne, find_id_of_nodup hnd.2 hf']

/-- 片段一致：每个片段按它的 id 查回来就是它自己 -/
def FragInv (L : Log) : Prop := ∀ f ∈ frags L, ∃ t, fragAt L f.id = some (t, f)

/-- **定理**：片段 id 唯一 -/
theorem fragInv {L : Log} (hR : Reachable check L) : FragInv L := by
  induction hR with
  | nil => intro f hf; simp [frags] at hf
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    intro f hf
    simp only [frags, List.mem_append] at hf
    rcases hf with hf | hf
    · rcases e with ⟨op, actor⟩
      cases op
      case saveSource h fs =>
        simp only [newFrags] at hf
        simp only [CheckP] at hcP
        obtain ⟨_, hnd, hfresh⟩ := hcP
        refine ⟨l.length, ?_⟩
        simp [fragAt, hfresh f hf, newFrags, find_id_of_nodup hnd hf]
      all_goals simp [newFrags] at hf
    · obtain ⟨t, ht⟩ := ih f hf
      exact ⟨t, fragAt_cons_of_some e ht⟩

/-! ## 节点：同一个问题只有一个有效节点 -/

def UniqueInv (L : Log) : Prop :=
  ∀ a b, active L a = true → active L b = true → question L a = question L b → a = b

theorem question_newNode {l : Log} {e : Entry} {n : NodeId} {ly : Layer} {q : Question}
    {src ends : List NodeId} {v : Version} {ex : List Sentence}
    (hop : e.op = .newNode n ly q src ends v ex) (hnew : created l n = none) (x : NodeId) :
    question (e :: l) x = if x = n then some q else question l x := by
  unfold question
  by_cases hx : x = n
  · subst hx; simp [created, hnew, hop]
  · simp only [created, hx, if_false]
    cases hc : created l x with
    | some r => simp
    | none => simp [hop, Ne.symm hx]

theorem question_cons_of_not_new {l : Log} {e : Entry}
    (h : ∀ n ly q src ends v ex, e.op ≠ .newNode n ly q src ends v ex) (x : NodeId) :
    question (e :: l) x = question l x := by
  unfold question
  simp only [created]
  cases hc : created l x with
  | some r => simp
  | none =>
    first
      | rfl
      | (simp only
         split
         · next n ly q src ends v ex hop => exact absurd hop (h n ly q src ends v ex)
         · rfl)

/-- **定理（同一个问题只有一个有效节点）** -/
theorem uniqueInv {L : Log} (hR : Reachable check L) : UniqueInv L := by
  induction hR with
  | nil => intro a b ha; simp [active] at ha
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    intro a b ha hb hq
    rcases e with ⟨op, actor⟩
    cases op
    case newNode n ly q src ends v ex =>
      simp only [CheckP] at hcP
      obtain ⟨_, hnew, _, _, _, huniq, _⟩ := hcP
      have huniq := huniq trivial
      have hqa := question_newNode (e := ⟨.newNode n ly q src ends v ex, actor⟩) rfl hnew a
      have hqb := question_newNode (e := ⟨.newNode n ly q src ends v ex, actor⟩) rfl hnew b
      rw [hqa, hqb] at hq
      simp only [active] at ha hb
      have old : ∀ c, n ≠ c → (if n = c then true else if c ∈ ends then false else active l c) = true →
          c ∉ ends ∧ active l c = true := by
        intro c hc h
        by_cases he : c ∈ ends
        · simp [hc, he] at h
        · simp [hc, he] at h; exact ⟨he, h⟩
      by_cases han : a = n <;> by_cases hbn : b = n
      · rw [han, hbn]
      · exfalso
        obtain ⟨hbe, hb'⟩ := old b (fun h => hbn h.symm) hb
        simp [han, hbn] at hq
        exact huniq b (active_mem_nodeIds hb') hb' hbe hq.symm
      · exfalso
        obtain ⟨hae, ha'⟩ := old a (fun h => han h.symm) ha
        simp [han, hbn] at hq
        exact huniq a (active_mem_nodeIds ha') ha' hae hq
      · obtain ⟨_, ha'⟩ := old a (fun h => han h.symm) ha
        obtain ⟨_, hb'⟩ := old b (fun h => hbn h.symm) hb
        simp [han, hbn] at hq
        exact ih a b ha' hb' hq
    case endNode n why =>
      rw [question_cons_of_not_new (by intros; simp) a,
          question_cons_of_not_new (by intros; simp) b] at hq
      simp only [active] at ha hb
      by_cases han : n = a
      · simp [han] at ha
      · by_cases hbn : n = b
        · simp [hbn] at hb
        · simp [han] at ha; simp [hbn] at hb
          exact ih a b ha hb hq
    all_goals
      rw [question_cons_of_not_new (by intros; simp) a,
          question_cons_of_not_new (by intros; simp) b] at hq
      simp only [active] at ha hb
      exact ih a b ha hb hq

/-! ## 事实：同一身份、同样的值只有一条有效记录 -/

def FactUnique (L : Log) : Prop :=
  ∀ x ∈ records L, ∀ y ∈ records L, x.1 ∉ voidedTimes L → y.1 ∉ voidedTimes L →
    x.2.key = y.2.key → x.2.value = y.2.value → x = y

/-- **定理（事实不重复）**：同一身份、同样的值，没作废的事实记录只有一条；
    同一个说法来自别的作者，只追加来源（`addSource`），不新增记录 -/
theorem factUnique {L : Log} (hR : Reachable check L) : FactUnique L := by
  induction hR with
  | nil => intro x hx; simp [records] at hx
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    intro x hx y hy hxv hyv hk hv
    rcases e with ⟨op, actor⟩
    cases op
    case addFact r =>
      simp only [CheckP] at hcP
      obtain ⟨_, hnl⟩ := hcP
      simp only [records, List.singleton_append, List.mem_cons] at hx hy
      simp only [voidedTimes, List.nil_append] at hxv hyv
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exact absurd ⟨y, hy, hk.symm, hv.symm, hyv⟩ hnl
      · exact absurd ⟨x, hx, hk, hv, hxv⟩ hnl
      · exact ih x hx y hy hxv hyv hk hv
    case voidFact t =>
      simp only [records, List.nil_append] at hx hy
      simp only [voidedTimes, List.singleton_append, List.mem_cons, not_or] at hxv hyv
      exact ih x hx y hy hxv.2 hyv.2 hk hv
    all_goals
      simp only [records, voidedTimes, List.nil_append] at hx hy hxv hyv
      exact ih x hx y hy hxv hyv hk hv

end MyLife
