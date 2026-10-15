import MyLife.Log

/-!
# 存储层是 DAG（由构造保证）

每条写入在写入那一刻，把它引用的东西（出处片段、事实、节点、理由……）解析成
“已经写入的那一条”的写入时间。解析只在更早的日志里进行，所以每条引用边都指向更早的时间，
写入顺序本身就是拓扑序，引用图不可能有环。

这条性质对任意日志都成立（连检查都不需要）：DAG 不是要去验证的东西，而是
“只追加 + 引用在写入时解析”这一设计的直接结果。检查保证的是另一件事：引用都能解析到（不悬空），
见 `MyLife.Provenance`。

注意：引用节点时，存储层固定到“写入那一刻该节点的最新版本”（核心原则 1：回看时取那一时刻的版本）。
活视图里按节点 id 取最新版本，节点之间可以互相引用，所以活视图的节点引用图不一定是 DAG，
反例见 `MyLife.Counterexamples`。
-/

namespace MyLife

def fragT (l : Log) (p : FragId) : List Time := ((fragAt l p).map (fun r => r.1)).toList
def nodeT (l : Log) (n : NodeId) : List Time := ((latest l n).map (fun r => r.1)).toList
def recT (l : Log) (t : Time) : List Time := if (recordAt l t).isSome then [t] else []
def keyT (l : Log) (k : FactKey) : List Time :=
  (records l).filterMap (fun x => if x.2.key = k then some x.1 else none)
def hashT (l : Log) (h : Hash) : List Time := (hashTime l h).toList

def targetT (l : Log) : Target → List Time
  | .node m => nodeT l m
  | .fact k => keyT l k
  | .frag p => fragT l p

def sentenceT (l : Log) (s : Sentence) : List Time :=
  fragT l s.origin ++ s.cites.flatMap (targetT l)

def versionT (l : Log) (v : Version) : List Time :=
  v.body.flatMap (sentenceT l) ++
    (match v.reason with
     | some p => fragT l p
     | none => [])

/-- 写入 e（写在日志 l 之上）引用的更早写入的时间 -/
def refs (l : Log) (e : Entry) : List Time :=
  match e.op with
  | .saveSource _ _ => []
  | .saveRecord h => hashT l h
  | .outcome p _ => fragT l p
  | .addFact r => fragT l r.origin
  | .addSource k _ p => keyT l k ++ fragT l p
  | .voidFact t => recT l t
  | .adopt _ t => recT l t
  | .setAuthority k _ => keyT l k
  | .link p n => fragT l p ++ nodeT l n
  | .draft n p v => fragT l p ++ nodeT l n ++ versionT l v
  | .newNode _ _ _ src ends v _ => src.flatMap (nodeT l) ++ ends.flatMap (nodeT l) ++ versionT l v
  | .writeVersion n _ v _ => nodeT l n ++ versionT l v
  | .endNode n why => nodeT l n ++ fragT l why
  | .move n _ => nodeT l n
  | .ack n t => nodeT l n ++ targetT l t
  | .deleteRecord h => hashT l h

theorem hashTime_lt : ∀ {l : Log} {h : Hash} {t : Time}, hashTime l h = some t → t < l.length
  | [], _, _, hh => by simp [hashTime] at hh
  | e :: l, h, t, hh => by
    simp only [hashTime] at hh
    split at hh
    · next t' ht => cases hh; have := hashTime_lt ht; simp; nomega
    · split at hh
      · split at hh
        · cases hh; simp
        · cases hh
      · cases hh

theorem fragT_lt {l : Log} {p : FragId} {j : Time} (h : j ∈ fragT l p) : j < l.length := by
  unfold fragT at h
  cases hf : fragAt l p with
  | none => simp [hf] at h
  | some r => simp [hf] at h; subst h; exact fragAt_lt (p := p) (f := r.2) (by simp [hf])

theorem nodeT_lt {l : Log} {n : NodeId} {j : Time} (h : j ∈ nodeT l n) : j < l.length := by
  unfold nodeT at h
  cases hf : latest l n with
  | none => simp [hf] at h
  | some r => simp [hf] at h; subst h; exact latest_lt hf

theorem recT_lt {l : Log} {t j : Time} (h : j ∈ recT l t) : j < l.length := by
  unfold recT at h
  split at h
  · next hs =>
    simp at h; subst h
    cases hr : recordAt l j with
    | none => simp [hr] at hs
    | some r => exact recordAt_lt hr
  · simp at h

theorem keyT_lt {l : Log} {k : FactKey} {j : Time} (h : j ∈ keyT l k) : j < l.length := by
  unfold keyT at h
  rw [List.mem_filterMap] at h
  obtain ⟨x, hx, hj⟩ := h
  split at hj
  · cases hj; exact records_lt hx
  · cases hj

theorem hashT_lt {l : Log} {h : Hash} {j : Time} (hj : j ∈ hashT l h) : j < l.length := by
  unfold hashT at hj
  cases hf : hashTime l h with
  | none => simp [hf] at hj
  | some r => simp [hf] at hj; subst hj; exact hashTime_lt hf

theorem targetT_lt {l : Log} {t : Target} {j : Time} (h : j ∈ targetT l t) : j < l.length := by
  cases t with
  | node m => exact nodeT_lt h
  | fact k => exact keyT_lt h
  | frag p => exact fragT_lt h

theorem sentenceT_lt {l : Log} {s : Sentence} {j : Time} (h : j ∈ sentenceT l s) : j < l.length := by
  unfold sentenceT at h
  rw [List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨t, _, ht⟩
  · exact fragT_lt h
  · exact targetT_lt ht

theorem versionT_lt {l : Log} {v : Version} {j : Time} (h : j ∈ versionT l v) : j < l.length := by
  unfold versionT at h
  rw [List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨s, _, hs⟩ | h
  · exact sentenceT_lt hs
  · split at h
    · exact fragT_lt h
    · simp at h

/-- 每条引用都指向更早的写入 -/
theorem refs_lt {l : Log} {e : Entry} {j : Time} (h : j ∈ refs l e) : j < l.length := by
  rcases e with ⟨op, actor⟩
  have hfm : ∀ {ns : List NodeId}, j ∈ ns.flatMap (nodeT l) → j < l.length := by
    intro ns hm
    rw [List.mem_flatMap] at hm
    obtain ⟨_, _, hm⟩ := hm
    exact nodeT_lt hm
  cases op <;> simp only [refs, List.mem_append] at h
  case saveSource => simp at h
  case saveRecord => exact hashT_lt h
  case outcome => exact fragT_lt h
  case addFact => exact fragT_lt h
  case addSource => rcases h with h | h; exact keyT_lt h; exact fragT_lt h
  case voidFact => exact recT_lt h
  case adopt => exact recT_lt h
  case setAuthority => exact keyT_lt h
  case link => rcases h with h | h; exact fragT_lt h; exact nodeT_lt h
  case draft =>
    rcases h with (h | h) | h
    · exact fragT_lt h
    · exact nodeT_lt h
    · exact versionT_lt h
  case newNode =>
    rcases h with (h | h) | h
    · exact hfm h
    · exact hfm h
    · exact versionT_lt h
  case writeVersion => rcases h with h | h; exact nodeT_lt h; exact versionT_lt h
  case endNode => rcases h with h | h; exact nodeT_lt h; exact fragT_lt h
  case move => exact nodeT_lt h
  case ack => rcases h with h | h; exact nodeT_lt h; exact targetT_lt h
  case deleteRecord => exact hashT_lt h

/-- 存储层的引用图：写入时间为 i 的那条写入引用了写入时间为 j 的那条 -/
def Edge (L : Log) (i j : Time) : Prop :=
  ∃ l₁ e l, L = l₁ ++ e :: l ∧ l.length = i ∧ j ∈ refs l e

theorem edge_lt {L : Log} {i j : Time} (h : Edge L i j) : j < i := by
  obtain ⟨_, _, l, _, hi, hj⟩ := h
  subst hi
  exact refs_lt hj

/-- 沿引用走任意多步，时间严格变小 -/
theorem path_lt {L : Log} {i j : Time} (h : Relation.TransGen (Edge L) i j) : j < i := by
  induction h with
  | single h => exact edge_lt h
  | tail _ h ih => exact Nat.lt_trans (edge_lt h) ih

/-- **定理（存储层是 DAG）**：对任意日志，引用图没有环 -/
theorem storage_acyclic (L : Log) (i : Time) : ¬ Relation.TransGen (Edge L) i i :=
  fun h => Nat.lt_irrefl _ (path_lt h)

/-! ## 节点的来源（分裂、合并、换阶段）也是 DAG -/

/-- 节点 n 由节点 m 分裂 / 合并 / 接续而来 -/
def DerivedFrom (L : Log) (n m : NodeId) : Prop :=
  ∃ l₁ e l ly q src ends v ex, L = l₁ ++ e :: l ∧ e.op = .newNode n ly q src ends v ex ∧ m ∈ src

def ctime (L : Log) (n : NodeId) : Option Time := (created L n).map (fun r => r.1)

theorem ctime_append {l : Log} {n : NodeId} {t : Time} (ext : Log)
    (h : ctime l n = some t) : ctime (ext ++ l) n = some t := by
  unfold ctime at *
  cases hc : created l n with
  | none => simp [hc] at h
  | some r => rw [created_append_of_some ext hc]; simpa [hc] using h

theorem derived_ctime_lt {L : Log} {n m : NodeId} (hR : Reachable check L) (h : DerivedFrom L n m) :
    ∃ tn tm, ctime L n = some tn ∧ ctime L m = some tm ∧ tm < tn := by
  obtain ⟨l₁, e, l, ly, q, src, ends, v, ex, hL, hop, hm⟩ := h
  subst hL
  have hc := checkP_of_check (Reachable.entry hR)
  simp only [CheckP, hop] at hc
  obtain ⟨_, hnew, hsrc, _⟩ := hc
  have hmc := hsrc m hm
  cases hcm : created l m with
  | none => simp [hcm] at hmc
  | some r =>
    have hlt := created_lt hcm
    refine ⟨l.length, r.1, ?_, ?_, hlt⟩
    · have : ctime (e :: l) n = some l.length := by
        simp [ctime, created, hnew, hop]
      simpa using ctime_append l₁ this
    · have : ctime l m = some r.1 := by simp [ctime, hcm]
      simpa using ctime_append (l₁ ++ [e]) this

/-- **定理**：节点的来源关系没有环（不会出现“A 来自 B、B 又来自 A”） -/
theorem lineage_acyclic {L : Log} (hR : Reachable check L) (n : NodeId) :
    ¬ Relation.TransGen (DerivedFrom L) n n := by
  have key : ∀ a b, Relation.TransGen (DerivedFrom L) a b →
      ∃ ta tb, ctime L a = some ta ∧ ctime L b = some tb ∧ tb < ta := by
    intro a b h
    induction h with
    | single h => exact derived_ctime_lt hR h
    | tail _ h ih =>
      obtain ⟨ta, tb, ha, hb, hlt⟩ := ih
      obtain ⟨tb', tc, hb', hc, hlt'⟩ := derived_ctime_lt hR h
      rw [hb] at hb'; cases hb'
      exact ⟨ta, tc, ha, hc, Nat.lt_trans hlt' hlt⟩
  intro h
  obtain ⟨ta, tb, ha, hb, hlt⟩ := key n n h
  rw [ha] at hb; cases hb
  exact Nat.lt_irrefl _ hlt

end MyLife
