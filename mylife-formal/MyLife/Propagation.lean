import MyLife.Layering
import MyLife.Facts

/-!
# 更新的传播（引用的东西变了，引用者进过目）

“哪些引用没跟上”不存，由日志推出（`Stale`）：有效节点 n 的当前版本引用了 t，
而 t 在 n 跟上之后又变了。“跟上”的时刻是 n 最新版本的写入时间和我最后一次“确认不用改”的时间里晚的那个。

“变了”只有两种：被引用的节点有了新的认知版本或结束；被引用的事实当前值变了。
整理版本、追加来源、挂关联都不算。
-/

namespace MyLife

def changedAt (l : Log) (e : Entry) : Target → Bool
  | .node m =>
    match e.op with
    | .writeVersion n _ v _ => n == m && v.kind == .cognitive
    | .endNode n _ => n == m
    | _ => false
  | .fact k => decide ((fstate (e :: l) k).cur ≠ (fstate l k).cur)
  | .frag _ => false

/-- 目标 t 变过的时刻 -/
def changeTimes : Log → Target → List Time
  | [], _ => []
  | e :: l, t => (if changedAt l e t then [l.length] else []) ++ changeTimes l t

def lastAck : Log → NodeId → Target → Option Time
  | [], _, _ => none
  | e :: l, n, t =>
    match e.op with
    | .ack n' t' => if n' = n ∧ t' = t then some l.length else lastAck l n t
    | _ => lastAck l n t

/-- 过目里应有的“引用的东西变了”事项（推出） -/
def Stale (l : Log) (n : NodeId) (t : Target) : Prop :=
  active l n = true ∧ ∃ x, latest l n = some x ∧ Cites x.2 t ∧
    ∃ c ∈ changeTimes l t, max x.1 ((lastAck l n t).getD 0) < c

theorem changeTimes_lt : ∀ {l : Log} {t : Target} {c : Time}, c ∈ changeTimes l t → c < l.length
  | [], _, _, h => by simp [changeTimes] at h
  | e :: l, t, c, h => by
    simp only [changeTimes, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h; subst h; simp
      · simp at h
    · have := changeTimes_lt h; simp; nomega

theorem lastAck_lt : ∀ {l : Log} {n : NodeId} {t : Target} {a : Time},
    lastAck l n t = some a → a < l.length
  | [], _, _, _, h => by simp [lastAck] at h
  | e :: l, n, t, a, h => by
    simp only [lastAck] at h
    split at h
    · split at h
      · cases h; simp
      · have := lastAck_lt h; simp; nomega
    · have := lastAck_lt h; simp; nomega

/-- 不改变任何“变了”判断的写入 -/
theorem changeTimes_cons_of_quiet {l : Log} {e : Entry} {t : Target}
    (h : changedAt l e t = false) : changeTimes (e :: l) t = changeTimes l t := by
  simp [changeTimes, h]

/-! ## 不漏：变了就进过目 -/

/-- **定理（不漏提醒，节点）**：节点 m 有了新的认知版本，所有直接引用它的有效节点都进过目 -/
theorem cognitive_version_flags_citers {l : Log} {e : Entry} {m n : NodeId} {b : Time} {v : Version}
    {ex : List Sentence} {x : Time × Version}
    (hop : e.op = .writeVersion m b v ex) (hk : v.kind = .cognitive) (hnm : n ≠ m)
    (hact : active l n = true) (hx : latest l n = some x) (hc : Cites x.2 (.node m)) :
    Stale (e :: l) n (.node m) := by
  have hact' : active (e :: l) n = true := by simp [active, hop, Ne.symm hnm, hact]
  have hx' : latest (e :: l) n = some x := by simp [latest, hop, Ne.symm hnm, hx]
  have hack : lastAck (e :: l) n (.node m) = lastAck l n (.node m) := by simp [lastAck, hop]
  refine ⟨hact', x, hx', hc, l.length, ?_, ?_⟩
  · simp [changeTimes, changedAt, hop, hk]
  · rw [hack]
    have h1 := latest_lt hx
    have h2 : (lastAck l n (.node m)).getD 0 < l.length ∨ l = [] := by
      cases ha : lastAck l n (.node m) with
      | none => cases l with
        | nil => exact Or.inr rfl
        | cons _ _ => left; simp
      | some a => left; simpa using lastAck_lt ha
    rcases h2 with h2 | h2
    · exact Nat.max_lt.mpr ⟨h1, h2⟩
    · subst h2; simp at h1

/-- **定理（不漏提醒，事实）**：事实 k 的当前值变了，所有直接引用它的有效节点都进过目 -/
theorem fact_change_flags_citers {l : Log} {e : Entry} {k : FactKey} {n : NodeId} {x : Time × Version}
    (hchg : (fstate (e :: l) k).cur ≠ (fstate l k).cur)
    (hact : active l n = true) (hx : latest l n = some x) (hc : Cites x.2 (.fact k)) :
    Stale (e :: l) n (.fact k) := by
  have hcog : cognitionOp e.op = false := by
    cases h : cognitionOp e.op
    · rfl
    · exact absurd ((evidence_unaffected_by_cognition (l := l) h).2.2.2 k ▸ rfl) hchg
  have hsame : active (e :: l) n = active l n ∧ latest (e :: l) n = latest l n ∧
      lastAck (e :: l) n (.fact k) = lastAck l n (.fact k) := by
    rcases e with ⟨op, actor⟩
    cases op <;> simp [cognitionOp] at hcog <;> simp [active, latest, lastAck]
  obtain ⟨ha, hl, hack⟩ := hsame
  refine ⟨ha ▸ hact, x, hl ▸ hx, hc, l.length, ?_, ?_⟩
  · simp [changeTimes, changedAt, hchg]
  · rw [hack]
    have h1 := latest_lt hx
    cases ha : lastAck l n (.fact k) with
    | none => simpa using h1
    | some a => exact Nat.max_lt.mpr ⟨h1, by simpa using lastAck_lt ha⟩

/-! ## 不多：只有真正的变化才提醒，确认过就不再提醒 -/

/-- **定理**：我确认“不用改”之后，这条引用就跟上了 -/
theorem ack_clears {l : Log} {e : Entry} {n : NodeId} {t : Target} (hop : e.op = .ack n t) :
    ¬ Stale (e :: l) n t := by
  rintro ⟨_, x, hx, _, c, hc, hlt⟩
  have hq : changedAt l e t = false := by
    cases t with
    | node m => simp [changedAt, hop]
    | fact k =>
      have := (evidence_unaffected_by_cognition (l := l) (e := e) (by simp [cognitionOp, hop])).2.2.2 k
      simp [changedAt, this]
    | frag p => simp [changedAt]
  rw [changeTimes_cons_of_quiet hq] at hc
  have hc' := changeTimes_lt hc
  have hack : lastAck (e :: l) n t = some l.length := by simp [lastAck, hop]
  rw [hack] at hlt
  simp at hlt
  nomega

/-- 不触发提醒的写入：整理版本、挂关联、追加来源、稿子、吸收记录、存原件 -/
def quietOp : Op → Bool
  | .writeVersion _ _ v _ => v.kind == .tidy
  | .link _ _ => true
  | .addSource _ _ _ => true
  | .draft _ _ _ => true
  | .outcome _ _ => true
  | .saveSource _ _ => true
  | .saveRecord _ => true
  | _ => false

theorem quiet_no_change {l : Log} {e : Entry} (hq : quietOp e.op = true) (t : Target) :
    changedAt l e t = false := by
  rcases e with ⟨op, actor⟩
  cases t with
  | node m =>
    cases op <;> simp [quietOp] at hq <;> simp [changedAt]
    next n b v ex => intro _; simp [hq]
  | fact k =>
    cases op <;> simp [quietOp] at hq <;>
      simp [changedAt, fstate, fstateAux, fstep, voidedTimes]
  | frag p => simp [changedAt]

/-- **定理（整理版本、追加来源、挂关联不触发）**：这些写入不会让任何别的节点进过目 -/
theorem quiet_no_new_stale {l : Log} {e : Entry} (hq : quietOp e.op = true)
    {n : NodeId} (hn : ∀ b v ex, e.op ≠ .writeVersion n b v ex) (t : Target) :
    Stale (e :: l) n t → Stale l n t := by
  rintro ⟨hact, x, hx, hc, c, hcm, hlt⟩
  rw [changeTimes_cons_of_quiet (quiet_no_change hq t)] at hcm
  rcases e with ⟨op, actor⟩
  cases op <;> simp [quietOp] at hq
  case writeVersion m b v ex =>
    have hmn : m ≠ n := fun h => hn b v ex (by rw [h])
    simp [active] at hact
    simp [latest, hmn] at hx
    simp [lastAck] at hlt
    exact ⟨hact, x, hx, hc, c, hcm, hlt⟩
  all_goals
    simp [active] at hact
    simp [latest] at hx
    simp [lastAck] at hlt
    exact ⟨hact, x, hx, hc, c, hcm, hlt⟩

/-! ## 方向：个人认知模型的变化不牵动世界模型 -/

/-- **定理**：有效的世界节点只会因为世界节点（或事实）的变化进过目，个人节点的变化牵动不到它 -/
theorem world_not_stale_by_personal {L : Log} {n m : NodeId} (hR : Reachable check L)
    (hly : layerOf L n = some .world) (hs : Stale L n (.node m)) :
    layerOf L m = some .world := by
  obtain ⟨hact, x, hx, hc, _⟩ := hs
  exact layerInv hR n x m hact hly hx hc

/-- **定理（认识之间只提醒，不自动改写）**：节点“变了”只能来自我写入的认知版本或结束，
    传播每走一层都要经过我 -/
theorem node_change_by_me {l : Log} {e : Entry} {m : NodeId} (hR : Reachable check (e :: l))
    (h : changedAt l e (.node m) = true) : e.actor = .me := by
  apply only_me_decides (l₁ := []) (l := l) hR rfl
  rcases e with ⟨op, actor⟩
  cases op <;> simp [changedAt] at h <;> rfl

end MyLife
