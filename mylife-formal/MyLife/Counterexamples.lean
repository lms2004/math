import MyLife.Layering
import MyLife.Identity
import MyLife.Facts
import MyLife.Dag

/-!
# 反例：每个守卫都是必要的，以及活视图不是 DAG

`checkG g` 可以单独关掉某个守卫。下面每个反例都是一条具体的日志：
关掉守卫时它是合规状态，却违反了对应的不变量；守卫打开时，那一步写入会被拒绝。
这些守卫在原设计里没有写明，是形式化时发现的。
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
def ver (cites : List Target) : Version := ⟨.cognitive, true, some 10, [sent cites]⟩
def mkNode (n : NodeId) (ly : Layer) (q : Question) (cites : List Target) : Entry :=
  ⟨.newNode n ly q [] [] (ver cites) [], .me⟩

/-! ## 1. 移层守卫：没有它，“世界模型不引用个人认知模型”会被一次移动打破 -/

/-- 节点 1、2 都在世界模型，2 引用 1；然后把 1 移到个人模型 -/
def moveLog : Log :=
  [⟨.move 1 .personal, .me⟩, mkNode 2 .world 2 [.node 1], mkNode 1 .world 1 [], saveMine]

theorem move_guard_needed :
    Reachable (checkG { move := false }) moveLog ∧ ¬ LayerInv moveLog := by
  refine ⟨reachableB_sound (by decide), fun h => ?_⟩
  have := h 2 (2, ver [.node 1]) 1 (by decide) (by decide) (by decide) (by decide)
  exact absurd this (by decide)

theorem move_guard_rejects : check moveLog.tail ⟨.move 1 .personal, .me⟩ = false := by decide

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

end MyLife.Counterexamples
