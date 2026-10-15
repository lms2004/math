import MyLife.Basic

/-!
# 日志、推出的视图、写入检查

一切视图（片段、节点、版本、事实当前值……）都由日志算出（“推出”），不另存。
程序在写入前做检查 `check`，不合规就拒绝；能走到的状态 `Reachable` 就是从空日志开始、
每一步都通过检查得到的日志。
-/

namespace MyLife

/-! ## 原始依据层的视图 -/

/-- 这一条写入新切出的片段 -/
def newFrags (e : Entry) : List Frag :=
  match e.op with
  | .saveSource _ fs => fs
  | _ => []

/-- 所有片段（新的在前） -/
def frags : Log → List Frag
  | [] => []
  | e :: l => newFrags e ++ frags l

/-- 按 id 找片段，返回最早写入它的时间和片段本身。先在更早的日志里找，所以一旦找到就永远不变。 -/
def fragAt : Log → FragId → Option (Time × Frag)
  | [], _ => none
  | e :: l, p =>
    match fragAt l p with
    | some r => some r
    | none =>
      match (newFrags e).find? (fun f => f.id == p) with
      | some f => some (l.length, f)
      | none => none

/-- 最近一次作者更正 -/
def attributionOf : Log → FragId → Option Author
  | [], _ => none
  | e :: l, p =>
    match e.op with
    | .correctAuthor q a => if q = p then some a else attributionOf l p
    | _ => attributionOf l p

/-- 片段现在的作者：有作者更正就用最近一次更正，否则是存入时标的作者 -/
def fragAuthor (l : Log) (p : FragId) : Option Author :=
  match fragAt l p with
  | none => none
  | some (_, f) => some ((attributionOf l p).getD f.author)

def hashSaved : Log → Hash → Bool
  | [], _ => false
  | e :: l, h =>
    (match e.op with
     | .saveSource h' _ => h' == h
     | _ => false) || hashSaved l h

/-- 某份原件（按哈希）切出的片段 -/
def fragsOf : Log → Hash → List Frag
  | [], _ => []
  | e :: l, h =>
    if hashSaved l h then fragsOf l h
    else
      match e.op with
      | .saveSource h' fs => if h' = h then fs else []
      | _ => []

/-- 原件第一次存入的时间 -/
def hashTime : Log → Hash → Option Time
  | [], _ => none
  | e :: l, h =>
    match hashTime l h with
    | some t => some t
    | none =>
      match e.op with
      | .saveSource h' _ => if h' = h then some l.length else none
      | _ => none

/-- 事实记录（带写入时间，新的在前） -/
def records : Log → List (Time × FactRec)
  | [] => []
  | e :: l =>
    (match e.op with
     | .addFact r => [(l.length, r)]
     | _ => []) ++ records l

def voidedTimes : Log → List Time
  | [] => []
  | e :: l =>
    (match e.op with
     | .voidFact t => [t]
     | _ => []) ++ voidedTimes l

def recordAt (l : Log) (t : Time) : Option FactRec :=
  ((records l).find? (fun x => x.1 == t)).map (fun x => x.2)

/-- 已有同一身份、同样的值、还没作废的事实 -/
def LiveSame (l : Log) (k : FactKey) (v : Value) : Prop :=
  ∃ x ∈ records l, x.2.key = k ∧ x.2.value = v ∧ x.1 ∉ voidedTimes l

instance (l : Log) (k : FactKey) (v : Value) : Decidable (LiveSame l k v) := by
  unfold LiveSame; infer_instance

def KeyRecorded (l : Log) (k : FactKey) : Prop :=
  ∃ x ∈ records l, x.2.key = k

instance (l : Log) (k : FactKey) : Decidable (KeyRecorded l k) := by
  unfold KeyRecorded; infer_instance

def authority : Log → FactKey → Option Author
  | [], _ => none
  | e :: l, k =>
    match e.op with
    | .setAuthority k' a => if k' = k then some a else authority l k
    | _ => authority l k

/-! ## 事实的当前值（推出，不另存） -/

/-- 当前值：哪条记录（写入时间）、它的作者 -/
structure Cur where
  time : Time
  record : FactRec
  author : Option Author
  deriving DecidableEq, Repr

/-- 一项属性的状态：当前值 + 等我裁决的冲突 + 被权威作者盖过的不同说法（都是记录的写入时间） -/
structure FState where
  cur : Option Cur
  conflicts : List Time
  overridden : List Time
  deriving DecidableEq, Repr

/-- 一条写入对事实 k 的状态的影响（V 是已作废的写入时间）：
    * 第一个值直接成为当前值；
    * 同一作者的新值接替旧值；
    * 定了以哪个作者为准的，这个作者的新值直接接替；其他作者的不同值不提醒，但列进“被盖过的说法”，查得到；
    * 其余不同作者给出不同的值：标为冲突，当前值保持不变，交给我；
    * 我裁决（采用某条）后，冲突清空。 -/
def fstep (V : List Time) (l : Log) (e : Entry) (k : FactKey) (s : FState) : FState :=
  match e.op with
  | .addFact r =>
    if r.key = k ∧ l.length ∉ V then
      match s.cur with
      | none => { s with cur := some ⟨l.length, r, fragAuthor l r.origin⟩ }
      | some old =>
        if old.author = fragAuthor l r.origin then
          { s with cur := some ⟨l.length, r, fragAuthor l r.origin⟩ }
        else
          match authority l k with
          | some b =>
            if some b = fragAuthor l r.origin then
              { s with cur := some ⟨l.length, r, fragAuthor l r.origin⟩ }
            else { s with overridden := l.length :: s.overridden }
          | none => { s with conflicts := l.length :: s.conflicts }
    else s
  | .adopt k' t =>
    if k' = k ∧ t ∉ V then
      match recordAt l t with
      | some r => { s with cur := some ⟨t, r, fragAuthor l r.origin⟩, conflicts := [] }
      | none => s
    else s
  | _ => s

def fstateAux (V : List Time) : Log → FactKey → FState
  | [], _ => ⟨none, [], []⟩
  | e :: l, k => fstep V l e k (fstateAux V l k)

/-- 事实 k 的状态：作废的记录整条跳过，其余按写入顺序走一遍 -/
def fstate (L : Log) (k : FactKey) : FState := fstateAux (voidedTimes L) L k

/-! ## 认识层的视图 -/

/-- 节点的创建：时间、初始层、回答的问题 -/
def created : Log → NodeId → Option (Time × Layer × Question)
  | [], _ => none
  | e :: l, n =>
    match created l n with
    | some r => some r
    | none =>
      match e.op with
      | .newNode m ly q _ _ _ _ => if m = n then some (l.length, ly, q) else none
      | _ => none

def nodeIds : Log → List NodeId
  | [] => []
  | e :: l =>
    (match e.op with
     | .newNode m _ _ _ _ _ _ => [m]
     | _ => []) ++ nodeIds l

def question (l : Log) (n : NodeId) : Option Question :=
  (created l n).map (fun r => r.2.2)

def layerOf : Log → NodeId → Option Layer
  | [], _ => none
  | e :: l, n =>
    match e.op with
    | .newNode m ly _ _ _ _ _ => if m = n then some ly else layerOf l n
    | .move ns ly => if n ∈ ns then some ly else layerOf l n
    | _ => layerOf l n

/-- 有效 / 结束 -/
def active : Log → NodeId → Bool
  | [], _ => false
  | e :: l, n =>
    match e.op with
    | .newNode m _ _ _ ends _ _ => if m = n then true else if n ∈ ends then false else active l n
    | .endNode m _ => if m = n then false else active l n
    | _ => active l n

/-- 节点的最新版本（写入时间和内容） -/
def latest : Log → NodeId → Option (Time × Version)
  | [], _ => none
  | e :: l, n =>
    match e.op with
    | .newNode m _ _ _ _ v _ => if m = n then some (l.length, v) else latest l n
    | .writeVersion m _ v _ => if m = n then some (l.length, v) else latest l n
    | _ => latest l n

/-- 版本正文引用了目标 t -/
def Cites (v : Version) (t : Target) : Prop :=
  ∃ s ∈ v.body, t ∈ s.cites

instance (v : Version) (t : Target) : Decidable (Cites v t) := by
  unfold Cites; infer_instance

/-! ## 过目里的稿子（推出） -/

/-- 一份稿子：针对的节点、内容、基于的节点版本（写入时节点的最新版本，推出） -/
structure DraftInfo where
  node : NodeId
  body : Version
  base : Option Time
  deriving DecidableEq, Repr

/-- 写入时间为 d 的稿子 -/
def draftAt : Log → Time → Option DraftInfo
  | [], _ => none
  | e :: l, d =>
    if d = l.length then
      match e.op with
      | .draft n _ v _ => some ⟨n, v, (latest l n).map (fun x => x.1)⟩
      | _ => none
    else draftAt l d

/-- 我不要的稿子 -/
def rejectedTimes : Log → List Time
  | [] => []
  | e :: l =>
    (match e.op with
     | .rejectDraft d => [d]
     | _ => []) ++ rejectedTimes l

/-- 被并进新稿子的旧稿子 -/
def mergedTimes : Log → List Time
  | [] => []
  | e :: l =>
    (match e.op with
     | .draft _ _ _ r => r.toList
     | _ => []) ++ mergedTimes l

/-- 被我确认写进版本的稿子 -/
def confirmedTimes : Log → List Time
  | [] => []
  | e :: l =>
    (match e.op with
     | .newNode _ _ _ _ _ v _ => v.fromDraft.toList
     | .writeVersion _ _ v _ => v.fromDraft.toList
     | _ => []) ++ confirmedTimes l

/-- 稿子 d 还在过目里，针对节点 n：没被拒绝、没被并进新稿子、没被确认 -/
def Pending (l : Log) (d : Time) (n : NodeId) : Prop :=
  (draftAt l d).map (fun di => di.node) = some n ∧ d ∉ rejectedTimes l ∧ d ∉ mergedTimes l ∧
    d ∉ confirmedTimes l

instance (l : Log) (d : Time) (n : NodeId) : Decidable (Pending l d n) := by
  unfold Pending; infer_instance

/-- 节点 n 在过目里的待定稿子 -/
def pendingFor (l : Log) (n : NodeId) : List Time :=
  (List.range l.length).filter (fun d => decide (Pending l d n))

/-- 确认稿子时我删掉的句子（稿子里有、写进去的版本里没有的文本） -/
def deletedTexts (l : Log) (v : Version) : List Text :=
  match v.fromDraft with
  | some d =>
    match draftAt l d with
    | some di => (di.body.body.map (fun s => s.text)).filter (fun x => x ∉ v.body.map (fun s => s.text))
    | none => []
  | none => []

/-- 节点 n 上我拒绝过的内容：我不要的稿子里的句子，以及确认稿子时我删掉的句子 -/
def rejectedTexts : Log → NodeId → List Text
  | [], _ => []
  | e :: l, n =>
    (match e.op with
     | .rejectDraft d =>
       match draftAt l d with
       | some di => if di.node = n then di.body.body.map (fun s => s.text) else []
       | none => []
     | .newNode m _ _ _ _ v _ => if m = n then deletedTexts l v else []
     | .writeVersion m _ v _ => if m = n then deletedTexts l v else []
     | _ => []) ++ rejectedTexts l n

/-! ## 写入检查 -/

def OptAll {α : Type} (o : Option α) (P : α → Prop) : Prop :=
  match o with
  | none => True
  | some a => P a

instance {α : Type} (o : Option α) (P : α → Prop) [DecidablePred P] : Decidable (OptAll o P) :=
  match o with
  | none => isTrue trivial
  | some a => inferInstanceAs (Decidable (P a))

def isMeOrExt : Option Author → Bool
  | some .me => true
  | some (.ext _) => true
  | _ => false

/-- 引用目标在写入时已经存在 -/
def TargetOK (l : Log) : Target → Prop
  | .node m => (created l m).isSome = true
  | .fact k => KeyRecorded l k
  | .frag p => (fragAt l p).isSome = true

instance (l : Log) (t : Target) : Decidable (TargetOK l t) := by
  cases t <;> unfold TargetOK <;> infer_instance

/-- 直接依据：事实，或我的话 -/
def Direct (l : Log) : Target → Prop
  | .node _ => False
  | .fact k => KeyRecorded l k
  | .frag p => fragAuthor l p = some .me

instance (l : Log) (t : Target) : Decidable (Direct l t) := by
  cases t <;> unfold Direct <;> infer_instance

/-- 世界节点能引用的目标：引用节点时，被引用的必须也在世界模型 -/
def WorldTarget (l : Log) : Target → Prop
  | .node m => layerOf l m = some .world
  | _ => True

instance (l : Log) (t : Target) : Decidable (WorldTarget l t) := by
  cases t <;> unfold WorldTarget <;> infer_instance

/-- 一句正文的检查（核心原则 2 与“记录与检查”）：
    出处存在且作者是我或 AI；AI 起草的标程度，我的话不标；标“确定”的至少引用一处直接依据；
    引用的东西都已存在；世界节点不引用个人节点；决定的结论和承诺必须逐句确认。 -/
def SentenceOK (l : Log) (ly : Option Layer) (explicit : List Sentence) (s : Sentence) : Prop :=
  (fragAuthor l s.origin = some .me ∨ fragAuthor l s.origin = some .ai) ∧
  (fragAuthor l s.origin = some .ai → s.degree ≠ none) ∧
  (fragAuthor l s.origin = some .me → s.degree = none) ∧
  (s.degree = some .certain → ∃ t ∈ s.cites, Direct l t) ∧
  (∀ t ∈ s.cites, TargetOK l t) ∧
  (ly = some .world → ∀ t ∈ s.cites, WorldTarget l t) ∧
  (s.decision = true → s ∈ explicit)

instance (l : Log) (ly : Option Layer) (ex : List Sentence) (s : Sentence) :
    Decidable (SentenceOK l ly ex s) := by
  unfold SentenceOK; infer_instance

def VersionOK (l : Log) (ly : Option Layer) (explicit : List Sentence) (v : Version) : Prop :=
  ∀ s ∈ v.body, SentenceOK l ly explicit s

instance (l : Log) (ly : Option Layer) (ex : List Sentence) (v : Version) :
    Decidable (VersionOK l ly ex v) := by
  unfold VersionOK; infer_instance

/-- 同一个问题只有一个有效节点：新建时，除了这次一并结束的旧节点，没有别的有效节点回答同一个问题 -/
def UniqueOK (l : Log) (q : Question) (ends : List NodeId) : Prop :=
  ∀ m ∈ nodeIds l, active l m = true → m ∉ ends → question l m ≠ some q

instance (l : Log) (q : Question) (ends : List NodeId) : Decidable (UniqueOK l q ends) := by
  unfold UniqueOK; infer_instance

/-- 移层守卫（一次可以移一组）：移到个人模型时，组外没有有效的世界节点引用组里的节点；
    移到世界模型时，组里节点引用的节点要么也在组里，要么已经在世界模型 -/
def MoveOK (l : Log) (ns : List NodeId) : Layer → Prop
  | .personal => ∀ m ∈ nodeIds l, m ∉ ns → active l m = true → layerOf l m = some .world →
      OptAll (latest l m) (fun x => ∀ n ∈ ns, ¬ Cites x.2 (.node n))
  | .world => ∀ n ∈ ns, OptAll (latest l n) (fun x => ∀ s ∈ x.2.body, ∀ t ∈ s.cites,
      (∃ m ∈ ns, t = .node m) ∨ WorldTarget l t)

instance (l : Log) (ns : List NodeId) (ly : Layer) : Decidable (MoveOK l ns ly) := by
  cases ly <;> unfold MoveOK <;> infer_instance

/-- 移到个人模型被拒时，程序列出挡住它的引用者：组外引用组里节点的有效世界节点 -/
def moveBlockers (l : Log) (ns : List NodeId) : List NodeId :=
  (nodeIds l).filter (fun m => decide (m ∉ ns ∧ active l m = true ∧ layerOf l m = some .world ∧
    OptAll (latest l m) (fun x => ∃ n ∈ ns, Cites x.2 (.node n))))

/-- 认知版本的理由：我的一句话（包括我对稿子的确认，存成我的话） -/
def ReasonOK (l : Log) (r : Option FragId) : Prop :=
  r.isSome = true ∧ OptAll r (fun p => fragAuthor l p = some .me)

instance (l : Log) (r : Option FragId) : Decidable (ReasonOK l r) := by
  unfold ReasonOK; infer_instance

/-- 确认稿子写入版本时：稿子还在过目里、基于的是节点现在的最新版本；
    重新分析不改动出处是我的话的句子，除非我在逐句确认里单独决定（把旧句放进确认清单） -/
def ConfirmOK (l : Log) (n : NodeId) (v : Version) (ex : List Sentence) : Prop :=
  OptAll v.fromDraft (fun d => Pending l d n ∧
    OptAll (draftAt l d) (fun di => di.base = (latest l n).map (fun x => x.1)) ∧
    OptAll (latest l n) (fun x => ∀ s ∈ x.2.body, fragAuthor l s.origin = some .me →
      s ∈ v.body ∨ s ∈ ex))

instance (l : Log) (n : NodeId) (v : Version) (ex : List Sentence) : Decidable (ConfirmOK l n v ex) := by
  unfold ConfirmOK; infer_instance

/-- 可以单独关掉的守卫；关掉后用来构造反例，说明每个守卫都是必要的 -/
structure Guards where
  move : Bool := true     -- 移层守卫
  unique : Bool := true   -- 新建 / 合并 / 换阶段时原子地结束旧节点
  cas : Bool := true      -- 稿子必须基于节点的最新版本
  void : Bool := true     -- 有待裁决的冲突时，只有我能作废这项属性的事实
  deriving Repr

def CheckP (g : Guards) (l : Log) (e : Entry) : Prop :=
  match e.op with
  | .saveSource h fs =>
      hashSaved l h = false ∧ (fs.map (fun f => f.id)).Nodup ∧ ∀ f ∈ fs, fragAt l f.id = none
  | .saveRecord h => hashSaved l h = true
  | .outcome p _ => (fragAt l p).isSome = true
  | .addFact r => isMeOrExt (fragAuthor l r.origin) = true ∧ ¬ LiveSame l r.key r.value
  | .addSource k v p => isMeOrExt (fragAuthor l p) = true ∧ LiveSame l k v
  | .voidFact t => (recordAt l t).isSome = true ∧
      OptAll (recordAt l t) (fun r => e.actor ≠ .me → g.void = true → (fstate l r.key).conflicts = [])
  | .adopt k t =>
      e.actor = .me ∧ (recordAt l t).isSome = true ∧ OptAll (recordAt l t) (fun r => r.key = k) ∧
      t ∉ voidedTimes l ∧ OptAll (recordAt l t) (fun r => isMeOrExt (fragAuthor l r.origin) = true)
  | .setAuthority _ _ => e.actor = .me
  | .link p n => (fragAt l p).isSome = true ∧ (created l n).isSome = true
  | .draft n p v r => e.actor = .agent ∧ (fragAt l p).isSome = true ∧ pendingFor l n = r.toList ∧
      ∀ s ∈ v.body, s.text ∉ rejectedTexts l n
  | .rejectDraft d => e.actor = .me ∧ (draftAt l d).isSome = true ∧
      OptAll (draftAt l d) (fun di => Pending l d di.node)
  | .newNode n ly q src ends v ex =>
      e.actor = .me ∧ created l n = none ∧ (∀ m ∈ src, (created l m).isSome = true) ∧
      (∀ m ∈ ends, active l m = true) ∧ v.kind = .cognitive ∧
      (g.unique = true → UniqueOK l q ends) ∧ VersionOK l (some ly) ex v ∧ ConfirmOK l n v ex
  | .writeVersion n b v ex =>
      e.actor = .me ∧ active l n = true ∧
      (g.cas = true → (latest l n).map (fun x => x.1) = some b) ∧
      (v.kind = .cognitive → ReasonOK l v.reason) ∧
      VersionOK l (layerOf l n) ex v ∧ ConfirmOK l n v ex
  | .endNode n why => e.actor = .me ∧ active l n = true ∧ fragAuthor l why = some .me
  | .move ns ly => e.actor = .me ∧ (∀ n ∈ ns, (created l n).isSome = true) ∧
      (g.move = true → MoveOK l ns ly)
  | .ack n t => e.actor = .me ∧ active l n = true ∧ (latest l n).isSome = true ∧
      OptAll (latest l n) (fun x => Cites x.2 t)
  | .deleteRecord h => e.actor = .me ∧ hashSaved l h = true
  | .correctAuthor p _ => e.actor = .me ∧ (fragAt l p).isSome = true

instance (g : Guards) (l : Log) (e : Entry) : Decidable (CheckP g l e) := by
  unfold CheckP; split <;> infer_instance

def checkG (g : Guards) (l : Log) (e : Entry) : Bool := decide (CheckP g l e)

/-- 程序的写入检查（所有守卫都打开） -/
def check : Log → Entry → Bool := checkG {}

/-- 能走到的状态：从空日志开始，每一步都通过检查 -/
inductive Reachable (chk : Log → Entry → Bool) : Log → Prop
  | nil : Reachable chk []
  | step {l : Log} {e : Entry} : Reachable chk l → chk l e = true → Reachable chk (e :: l)

/-! ## 通用引理 -/

theorem checkP_of_check {l : Log} {e : Entry} (h : check l e = true) : CheckP {} l e :=
  of_decide_eq_true h

theorem Reachable.of_cons {chk : Log → Entry → Bool} {l : Log} {e : Entry}
    (h : Reachable chk (e :: l)) : Reachable chk l ∧ chk l e = true := by
  cases h with
  | step hl he => exact ⟨hl, he⟩

theorem Reachable.suffix {chk : Log → Entry → Bool} :
    ∀ (l₁ : Log) {l₂ : Log}, Reachable chk (l₁ ++ l₂) → Reachable chk l₂
  | [], _, h => h
  | _ :: l₁, _, h => Reachable.suffix l₁ (Reachable.of_cons h).1

/-- 日志里每一条写入，都通过了它写入那一刻的检查 -/
theorem Reachable.entry {chk : Log → Entry → Bool} {l₁ l₂ : Log} {e : Entry}
    (h : Reachable chk (l₁ ++ e :: l₂)) : chk l₂ e = true :=
  (Reachable.of_cons (Reachable.suffix l₁ h)).2

theorem fragAt_cons_of_some {l : Log} {p : FragId} {r : Time × Frag} (e : Entry)
    (h : fragAt l p = some r) : fragAt (e :: l) p = some r := by
  simp [fragAt, h]

theorem fragAt_append_of_some {l : Log} {p : FragId} {r : Time × Frag} :
    ∀ (ext : Log), fragAt l p = some r → fragAt (ext ++ l) p = some r
  | [], h => h
  | e :: ext, h => fragAt_cons_of_some e (fragAt_append_of_some ext h)

theorem fragAt_lt : ∀ {l : Log} {p : FragId} {t : Time} {f : Frag},
    fragAt l p = some (t, f) → t < l.length
  | [], _, _, _, h => by simp [fragAt] at h
  | e :: l, p, t, f, h => by
    simp only [fragAt] at h
    split at h
    · next r hr =>
      cases h
      have := fragAt_lt hr
      simp; nomega
    · split at h
      · cases h; simp
      · cases h

theorem fragAuthor_isSome {l : Log} {p : FragId} {a : Author} (h : fragAuthor l p = some a) :
    ∃ r, fragAt l p = some r := by
  unfold fragAuthor at h
  cases hr : fragAt l p with
  | none => simp [hr] at h
  | some r => exact ⟨r, rfl⟩

theorem fragAt_isSome_append {l : Log} {p : FragId} (ext : Log)
    (h : (fragAt l p).isSome = true) : (fragAt (ext ++ l) p).isSome = true := by
  cases hr : fragAt l p with
  | none => simp [hr] at h
  | some r => rw [fragAt_append_of_some ext hr]; rfl

theorem created_cons_of_some {l : Log} {n : NodeId} {r : Time × Layer × Question} (e : Entry)
    (h : created l n = some r) : created (e :: l) n = some r := by
  simp [created, h]

theorem created_append_of_some {l : Log} {n : NodeId} {r : Time × Layer × Question} :
    ∀ (ext : Log), created l n = some r → created (ext ++ l) n = some r
  | [], h => h
  | e :: ext, h => created_cons_of_some e (created_append_of_some ext h)

theorem created_isSome_append {l : Log} {n : NodeId} (ext : Log)
    (h : (created l n).isSome = true) : (created (ext ++ l) n).isSome = true := by
  cases hr : created l n with
  | none => simp [hr] at h
  | some r => rw [created_append_of_some ext hr]; rfl

theorem created_lt : ∀ {l : Log} {n : NodeId} {r : Time × Layer × Question},
    created l n = some r → r.1 < l.length
  | [], _, _, h => by simp [created] at h
  | e :: l, n, r, h => by
    simp only [created] at h
    split at h
    · next r' hr =>
      cases h
      have := created_lt hr
      simp; nomega
    · split at h
      · split at h
        · cases h; simp
        · cases h
      · cases h

theorem latest_lt : ∀ {l : Log} {n : NodeId} {x : Time × Version},
    latest l n = some x → x.1 < l.length
  | [], _, _, h => by simp [latest] at h
  | e :: l, n, x, h => by
    simp only [latest] at h
    split at h
    · split at h
      · cases h; simp
      · have := latest_lt h; simp; nomega
    · split at h
      · cases h; simp
      · have := latest_lt h; simp; nomega
    · have := latest_lt h; simp; nomega

theorem records_lt : ∀ {l : Log} {x : Time × FactRec}, x ∈ records l → x.1 < l.length
  | [], _, h => by simp [records] at h
  | e :: l, x, h => by
    simp only [records, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h; subst h; simp
      · simp at h
    · have := records_lt h; simp; nomega

theorem records_cons_sub {l : Log} {x : Time × FactRec} (e : Entry)
    (h : x ∈ records l) : x ∈ records (e :: l) := by
  simp only [records, List.mem_append]; exact Or.inr h

theorem records_append_sub {l : Log} {x : Time × FactRec} :
    ∀ (ext : Log), x ∈ records l → x ∈ records (ext ++ l)
  | [], h => h
  | e :: ext, h => records_cons_sub e (records_append_sub ext h)

theorem recordAt_mem {l : Log} {t : Time} {r : FactRec}
    (h : recordAt l t = some r) : (t, r) ∈ records l := by
  unfold recordAt at h
  cases hf : (records l).find? (fun x => x.1 == t) with
  | none => simp [hf] at h
  | some x =>
    simp [hf] at h
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp at hp
    subst h; subst hp
    exact hm

theorem recordAt_lt {l : Log} {t : Time} {r : FactRec}
    (h : recordAt l t = some r) : t < l.length :=
  records_lt (recordAt_mem h)

theorem keyRecorded_append {l : Log} {k : FactKey} (ext : Log)
    (h : KeyRecorded l k) : KeyRecorded (ext ++ l) k := by
  obtain ⟨x, hx, hk⟩ := h
  exact ⟨x, records_append_sub ext hx, hk⟩

theorem hashSaved_append {l : Log} {h : Hash} :
    ∀ (ext : Log), hashSaved l h = true → hashSaved (ext ++ l) h = true
  | [], hs => hs
  | e :: ext, hs => by simp [hashSaved, hashSaved_append ext hs]

theorem active_created : ∀ {l : Log} {n : NodeId},
    active l n = true → (created l n).isSome = true
  | [], _, h => by simp [active] at h
  | e :: l, n, h => by
    simp only [active] at h
    split at h
    · next m ly q src ends v ex hop =>
      by_cases hmn : m = n
      · subst hmn
        cases hc : created l m with
        | some r => simp [created, hc]
        | none => simp [created, hc, hop]
      · simp [hmn] at h
        exact created_isSome_append [e] (active_created h.2)
    · next m why hop =>
      by_cases hmn : m = n
      · simp [hmn] at h
      · simp [hmn] at h
        exact created_isSome_append [e] (active_created h)
    · exact created_isSome_append [e] (active_created h)

theorem created_mem_nodeIds : ∀ {l : Log} {n : NodeId},
    (created l n).isSome = true → n ∈ nodeIds l
  | [], _, h => by simp [created] at h
  | e :: l, n, h => by
    simp only [created] at h
    simp only [nodeIds, List.mem_append]
    split at h
    · next r hr => exact Or.inr (created_mem_nodeIds (by simp [hr]))
    · split at h
      · next m ly q src ends v ex hop =>
        split at h
        · next hmn => subst hmn; simp [hop]
        · simp at h
      · simp at h

theorem active_mem_nodeIds {l : Log} {n : NodeId} (h : active l n = true) : n ∈ nodeIds l :=
  created_mem_nodeIds (active_created h)

theorem draftAt_lt : ∀ {l : Log} {d : Time} {di : DraftInfo}, draftAt l d = some di → d < l.length
  | [], _, _, h => by simp [draftAt] at h
  | e :: l, d, di, h => by
    simp only [draftAt] at h
    split at h
    · next hd => subst hd; simp
    · have := draftAt_lt h; simp; nomega

end MyLife
