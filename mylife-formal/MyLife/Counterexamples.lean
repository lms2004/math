import MyLife.Layering
import MyLife.Identity
import MyLife.Facts
import MyLife.Dag
import MyLife.Review
import MyLife.Deletion

/-!
# 反例和示例

`checkG g` 可以单独关掉某个守卫。第 1–4 节每个反例都是一条具体的日志：
关掉守卫时它是合规状态，却违反了对应的不变量；守卫打开时，那一步写入会被拒绝。
第 5 节说明活视图不是 DAG；第 6、7 节是按我的决定（作者更正、权威作者）给的示例；
第 8 节是过目稿子的规则，第 9 节是删除清单。
所有结论都由 Lean 用 `decide` 直接算出。
-/

namespace MyLife.Counterexamples

open MyLife

def reachableB (chk : Log → Entry → Bool) : Log → Bool
  | [] => true
  | e :: l => reachableB chk l && chk l e

theorem reachableB_sound {chk : Log → Entry → Bool} : ∀ {l : Log}, reachableB chk l = true → Reachable chk l
  | [], _ => Reachable.nil
  | e :: l, h => by
    simp only [reachableB, Bool.and_eq_true] at h
    exact Reachable.step (reachableB_sound h.1) h.2

/-! 公共素材：片段 10 是我的一句话，片段 20 是外部发布者 7 的一段话 -/

def saveMine : Entry := ⟨.saveSource 1 [⟨10, .me, 100⟩], .program⟩
def saveExt : Entry := ⟨.saveSource 2 [⟨20, .ext 7, 200⟩], .program⟩
def sent (cites : List Target) : Sentence := ⟨100, 10, none, cites, false⟩
def ver (cites : List Target) : Version := ⟨.cognitive, true, some 10, [sent cites], none⟩
def mkNode (n : NodeId) (ly : Layer) (q : Question) (cites : List Target) : Entry :=
  ⟨.newNode n ly q [] [] (ver cites) [], .me⟩

/-! ## 1. 移层守卫：没有它，“世界模型不引用个人认知模型”会被一次移动打破 -/

/-- 节点 1、2 都在世界模型，2 引用 1；然后把 1 单独移到个人模型 -/
def moveLog : Log :=
  [⟨.move [1] .personal, .me⟩, mkNode 2 .world 2 [.node 1], mkNode 1 .world 1 [], saveMine]

theorem move_guard_needed :
    Reachable (checkG { move := false }) moveLog ∧ ¬ LayerInv moveLog := by
  refine ⟨reachableB_sound (by decide), fun h => ?_⟩
  have := h 2 (2, ver [.node 1]) 1 (by decide) (by decide) (by decide) (by decide)
  exact absurd this (by decide)

theorem move_guard_rejects : check moveLog.tail ⟨.move [1] .personal, .me⟩ = false := by decide

/-- 被拒时，程序列出挡住它的引用者：节点 2 -/
theorem move_blockers_listed : moveBlockers moveLog.tail [1] = [2] := by decide

/-- 我的决定：在同一次写入里把节点 1 和引用它的节点 2 一起移过去，是允许的 -/
def groupMoveLog : Log :=
  [⟨.move [1, 2] .personal, .me⟩, mkNode 2 .world 2 [.node 1], mkNode 1 .world 1 [], saveMine]

theorem group_move_ok : Reachable check groupMoveLog := reachableB_sound (by decide)

/-! ## 2. 原子结束：没有它，合并 / 换阶段时同一个问题会有两个有效节点 -/

/-- 节点 2 由节点 1 合并而来、回答同一个问题，但没在同一次写入里结束节点 1 -/
def mergeLog : Log :=
  [⟨.newNode 2 .personal 5 [1] [] (ver []) [], .me⟩, mkNode 1 .personal 5 [], saveMine]

theorem atomic_end_needed :
    Reachable (checkG { unique := false }) mergeLog ∧ ¬ UniqueInv mergeLog := by
  refine ⟨reachableB_sound (by decide), fun h => ?_⟩
  have := h 1 2 (by decide) (by decide) (by decide)
  exact absurd this (by decide)

theorem atomic_end_rejects : check mergeLog.tail ⟨.newNode 2 .personal 5 [1] [] (ver []) [], .me⟩ = false := by
  decide

/-- 正确的做法：新建节点 2 的同一次写入里结束节点 1（换阶段同理） -/
def mergeLogOk : Log :=
  [⟨.newNode 2 .personal 5 [1] [1] (ver []) [], .me⟩, mkNode 1 .personal 5 [], saveMine]

theorem atomic_merge_ok : Reachable check mergeLogOk := reachableB_sound (by decide)

/-! ## 3. 基于版本写入：没有它，确认一份过时的稿子会悄悄覆盖中间的新版本 -/

/-- 稿子基于时刻 2 的版本起草；这期间节点已经有了时刻 3 的版本；再确认这份稿子 -/
def casLog : Log :=
  [⟨.writeVersion 1 2 (ver [.frag 10]) [], .me⟩,
   ⟨.writeVersion 1 2 (ver [.frag 20]) [], .me⟩,
   mkNode 1 .world 1 [], saveExt, saveMine]

theorem cas_needed :
    Reachable (checkG { cas := false }) casLog ∧ latest casLog.tail 1 = some (3, ver [.frag 20]) := by
  refine ⟨reachableB_sound (by decide), by decide⟩

theorem cas_rejects : check casLog.tail ⟨.writeVersion 1 2 (ver [.frag 10]) [], .me⟩ = false := by decide

/-! ## 4. 作废守卫：没有它，Agent 一次“撤销抽取”就能悄悄替我裁决冲突 -/

def key : FactKey := ⟨1, 1⟩

/-- 我说值是 10，外部发布者说是 12：冲突，当前值保持 10。然后 Agent 作废了我那条 -/
def voidLog : Log :=
  [⟨.voidFact 2, .agent⟩,
   ⟨.addFact ⟨key, 12, 20⟩, .agent⟩,
   ⟨.addFact ⟨key, 10, 10⟩, .agent⟩,
   saveExt, saveMine]

theorem void_guard_needed :
    Reachable (checkG { void := false }) voidLog ∧
    (fstate voidLog.tail key).conflicts = [3] ∧
    (fstate voidLog.tail key).cur.map (fun c => c.record.value) = some 10 ∧
    (fstate voidLog key).conflicts = [] ∧
    (fstate voidLog key).cur.map (fun c => c.record.value) = some 12 := by
  refine ⟨reachableB_sound (by decide), by decide, by decide, by decide, by decide⟩

theorem void_guard_rejects : check voidLog.tail ⟨.voidFact 2, .agent⟩ = false := by decide

/-- 同一步由我来做（我裁决：作废我那条）是允许的 -/
theorem void_by_me_ok : check voidLog.tail ⟨.voidFact 2, .me⟩ = true := by decide

/-! ## 5. 活视图的节点引用图不是 DAG -/

/-- 节点 2 引用节点 1；之后节点 1 的新版本引用节点 2。两步都合规 -/
def cycleLog : Log :=
  [⟨.writeVersion 1 1 (ver [.node 2]) [], .me⟩,
   mkNode 2 .world 2 [.node 1], mkNode 1 .world 1 [], saveMine]

theorem live_graph_may_cycle :
    Reachable check cycleLog ∧
    latest cycleLog 1 = some (3, ver [.node 2]) ∧ Cites (ver [.node 2]) (.node 2) ∧
    latest cycleLog 2 = some (2, ver [.node 1]) ∧ Cites (ver [.node 1]) (.node 1) := by
  refine ⟨reachableB_sound (by decide), by decide, by decide, by decide, by decide⟩

/-- 但存储层仍然无环：节点 1 的新版本（时刻 3）固定引用写入那一刻节点 2 的版本（时刻 2），后者固定引用节点 1 的旧版本（时刻 1） -/
example : ¬ Relation.TransGen (Edge cycleLog) 3 3 := storage_acyclic cycleLog 3

/-! ## 6. 作者更正：原来算原话的句子，更正后进过目 -/

/-- 节点 1 的一句话出处是片段 10（存入时标为我的话）；之后我把片段 10 的作者更正为 AI -/
def correctLog : Log :=
  [⟨.correctAuthor 10 .ai, .me⟩, mkNode 1 .personal 1 [], saveMine]

theorem correction_flags_sentence :
    Reachable check correctLog ∧
    drafter (snap correctLog 1) (sent []) = some .verbatim ∧
    drafter correctLog (sent []) = some .aiDrafted ∧
    AuthorFlag correctLog 1 (sent []) :=
  ⟨reachableB_sound (by decide), by decide, by decide, ⟨10, Or.inl rfl, by decide⟩⟩

/-! ## 7. 权威作者：其他作者的不同值不提醒，但查得到 -/

/-- 这项属性定了以外部发布者 7 为准；它说 12，之后我说 10 -/
def authLog : Log :=
  [⟨.addFact ⟨key, 10, 10⟩, .agent⟩,
   ⟨.addFact ⟨key, 12, 20⟩, .agent⟩,
   ⟨.setAuthority key (.ext 7), .me⟩,
   saveExt, saveMine]

theorem overridden_listed_example :
    Reachable check authLog ∧
    (fstate authLog key).cur.map (fun c => c.record.value) = some 12 ∧
    (fstate authLog key).conflicts = [] ∧
    (fstate authLog key).overridden = [4] :=
  ⟨reachableB_sound (by decide), by decide, by decide, by decide⟩

/-! ## 8. 过目里的稿子 -/

/-- 片段 30 是 AI 的话（一份分析稿） -/
def saveAI : Entry := ⟨.saveSource 3 [⟨30, .ai, 300⟩], .program⟩
def aiSent : Sentence := ⟨300, 30, some .guess, [], false⟩
def draftVer : Version := ⟨.cognitive, true, none, [aiSent], none⟩

/-- 节点 1 当前版本是我的一句原话；Agent 起草了一份稿子（时刻 3） -/
def reviewLog : Log :=
  [⟨.draft 1 30 draftVer none, .agent⟩, mkNode 1 .personal 1 [], saveAI, saveMine]

theorem review_log_ok : Reachable check reviewLog := reachableB_sound (by decide)

/-- 已有待定稿子时另起一份：拒绝；并进去重新起草（指向旧稿子）：允许 -/
theorem one_pending_draft :
    check reviewLog ⟨.draft 1 30 draftVer none, .agent⟩ = false ∧
    check reviewLog ⟨.draft 1 30 draftVer (some 3), .agent⟩ = true := ⟨by decide, by decide⟩

/-- 我不要这份稿子以后，Agent 再提出同样的句子：拒绝 -/
theorem rejected_not_reproposed :
    check (⟨.rejectDraft 3, .me⟩ :: reviewLog) ⟨.draft 1 30 draftVer none, .agent⟩ = false := by
  decide

/-- 确认稿子时删掉我的原话：拒绝；我在逐句确认里单独决定改它：允许；保留它：允许 -/
def confirmVer (body : List Sentence) : Version := ⟨.cognitive, true, some 10, body, some 3⟩

theorem my_sentence_needs_my_decision :
    check reviewLog ⟨.writeVersion 1 2 (confirmVer [aiSent]) [], .me⟩ = false ∧
    check reviewLog ⟨.writeVersion 1 2 (confirmVer [aiSent]) [sent []], .me⟩ = true ∧
    check reviewLog ⟨.writeVersion 1 2 (confirmVer [sent [], aiSent]) [], .me⟩ = true :=
  ⟨by decide, by decide, by decide⟩

/-- 稿子起草之后节点有了新版本（时刻 4），再确认这份稿子：拒绝（只能重新起草或不要） -/
theorem stale_draft_rejected :
    check (⟨.writeVersion 1 2 (ver [.frag 10]) [], .me⟩ :: reviewLog)
      ⟨.writeVersion 1 4 (confirmVer [sent [], aiSent]) [], .me⟩ = false := by
  decide

/-! ## 9. 删除清单 -/

/-- 外部资料（原件 2，时刻 1）抽出一条事实（时刻 2）；节点 1 的一句话（出处是我的话，原件 1）引用了这条事实（时刻 3） -/
def deleteLog : Log :=
  [mkNode 1 .world 1 [.fact key], ⟨.addFact ⟨key, 12, 20⟩, .agent⟩, saveExt, saveMine]

/-- 删原件 2：列出它本身、从它抽的事实、引用这条事实的版本；删原件 1：列出它本身和出处在它里面的版本 -/
theorem deletion_lists :
    deletionList deleteLog 2 = [1, 3, 2] ∧ deletionList deleteLog 1 = [0, 3] :=
  ⟨by decide, by decide⟩

end MyLife.Counterexamples
