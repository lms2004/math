import MyLife.Log

/-!
# 只追加与历史还原（核心原则 1）

* 每一步写入只在日志头上追加一条，旧的日志原样是新日志的后缀；各个存储也都只追加。
* 时刻 t 的状态 = 日志里写入时间早于 t 的部分（`snap L t`）。之后再写多少，都不改变它。
* 过去任何时刻的状态本身也是一个合规状态：所有对“能走到的状态”证明的不变量，在每个历史时刻都成立。
-/

namespace MyLife

/-- 一步合规写入 -/
def Step (chk : Log → Entry → Bool) (l l' : Log) : Prop :=
  ∃ e, chk l e = true ∧ l' = e :: l

/-- **只追加**：合规写入后，旧日志原样是新日志的后缀 -/
theorem step_suffix {chk : Log → Entry → Bool} {l l' : Log} (h : Step chk l l') : l <:+ l' := by
  obtain ⟨e, _, rfl⟩ := h
  exact ⟨[e], rfl⟩

/-- 所有版本（含历史版本）：节点、写入时间、内容 -/
def versions : Log → List (NodeId × Time × Version)
  | [] => []
  | e :: l =>
    (match e.op with
     | .newNode n _ _ _ _ v _ => [(n, l.length, v)]
     | .writeVersion n _ v _ => [(n, l.length, v)]
     | _ => []) ++ versions l

theorem frags_suffix (e : Entry) (l : Log) : frags l <:+ frags (e :: l) :=
  ⟨newFrags e, rfl⟩

theorem records_suffix (e : Entry) (l : Log) : records l <:+ records (e :: l) :=
  ⟨_, rfl⟩

theorem versions_suffix (e : Entry) (l : Log) : versions l <:+ versions (e :: l) :=
  ⟨_, rfl⟩

/-- 时刻 t 的快照：写入时间小于 t 的那些写入 -/
def snap (L : Log) (t : Time) : Log := L.drop (L.length - t)

theorem snap_length {L : Log} {t : Time} (h : t ≤ L.length) : (snap L t).length = t := by
  simp [snap, List.length_drop]; nomega

theorem snap_self (L : Log) : snap L L.length = L := by
  simp [snap]

theorem snap_suffix (L : Log) (t : Time) : snap L t <:+ L :=
  List.drop_suffix _ _

/-- **历史不变**：之后再写多少，时刻 t 的快照都不变 -/
theorem snap_append (new : Log) {L : Log} {t : Time} (h : t ≤ L.length) :
    snap (new ++ L) t = snap L t := by
  unfold snap
  have : (new ++ L).length - t = new.length + (L.length - t) := by
    simp [List.length_append]; nomega
  rw [this, List.drop_append]

/-- 由日志推出的任何视图（Current Model、事实当前值、引用索引、界面投影……）在时刻 t 的值都不会被后来的写入改变 -/
theorem view_stable {α : Type} (f : Log → α) (new : Log) {L : Log} {t : Time} (h : t ≤ L.length) :
    f (snap (new ++ L) t) = f (snap L t) := by
  rw [snap_append new h]

/-- 写入 e 那一刻的快照，就是 e 之前的日志 -/
theorem snap_split (l₁ : Log) (e : Entry) (l : Log) : snap (l₁ ++ e :: l) l.length = l := by
  have : l₁ ++ e :: l = (l₁ ++ [e]) ++ l := by simp
  rw [this, snap_append _ (Nat.le_refl _), snap_self]

theorem Reachable.of_suffix {chk : Log → Entry → Bool} {l L : Log}
    (hR : Reachable chk L) (h : l <:+ L) : Reachable chk l := by
  obtain ⟨pre, rfl⟩ := h
  exact Reachable.suffix pre hR

/-- 过去任何时刻的快照都是合规状态 -/
theorem reachable_snap {chk : Log → Entry → Bool} {L : Log} (hR : Reachable chk L) (t : Time) :
    Reachable chk (snap L t) :=
  hR.of_suffix (snap_suffix L t)

/-- **还原**：凡是对所有合规状态成立的不变量，在每一个历史时刻也成立 -/
theorem invariant_at_every_time {chk : Log → Entry → Bool} (I : Log → Prop)
    (hI : ∀ L, Reachable chk L → I L) {L : Log} (hR : Reachable chk L) (t : Time) :
    I (snap L t) :=
  hI _ (reachable_snap hR t)

/-- Current Model 的节点部分：所有有效节点的最新版本（事实的当前值见 `MyLife.Facts`） -/
def currentNode (L : Log) (n : NodeId) : Option (Time × Version) :=
  if active L n then latest L n else none

theorem currentNode_at_time_stable (new : Log) {L : Log} {t : Time} (h : t ≤ L.length) :
    currentNode (snap (new ++ L) t) = currentNode (snap L t) :=
  view_stable currentNode new h

end MyLife
