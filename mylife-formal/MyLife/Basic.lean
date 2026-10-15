/-!
# MyLife 形式化模型：基本类型

建模约定：
* 文字本身（原件内容、句子文本）放在仓库外的内容寻址库里，这里只用它的哈希 / 指纹（`Nat`）表示。
  所以下面所有检查和定理都与文字内容无关，删除内容不会破坏任何已证明的性质。
* 所有只追加的存储（原件、片段、事实、版本、吸收记录、过目、关联、操作日志）
  在模型里按写入时间合成一条日志 `Log`；这是证明手段，不要求实现也这样存。
-/

namespace MyLife

abbrev Hash := Nat       -- 原件内容哈希
abbrev FragId := Nat     -- 片段的稳定定位（原件哈希 + 位置 + 原文指纹，抽象成一个编号）
abbrev NodeId := Nat     -- 节点的稳定 id
abbrev Question := Nat   -- 节点回答的问题（节点身份）；相等与否由我判定，模型里给成显式的键
abbrev Text := Nat       -- 文本的指纹
abbrev Time := Nat       -- 写入时间 = 在日志里的位置
abbrev Value := Nat      -- 事实的值

/-- 片段的作者：我、AI、外部发布者，或者看不出作者 / 转述 -/
inductive Author where
  | me
  | ai
  | ext (publisher : Nat)
  | unknown
  deriving DecidableEq, Repr

/-- 一次写入由谁发起 -/
inductive Actor where
  | me
  | agent
  | program
  deriving DecidableEq, Repr

inductive Layer where
  | world
  | personal
  deriving DecidableEq, Repr

/-- AI 起草句子的程度：确定 / 推测 / 可疑 -/
inductive Degree where
  | certain
  | guess
  | doubtful
  deriving DecidableEq, Repr

/-- 片段：出处和吸收记录的最小定位单位 -/
structure Frag where
  id : FragId
  author : Author
  fp : Text
  deriving DecidableEq, Repr

/-- 事实的身份：对象 + 属性 + 适用范围（状态），或对象 + 事件 + 时间，抽象成 `attr` -/
structure FactKey where
  obj : Nat
  attr : Nat
  deriving DecidableEq, Repr

/-- 正文里的引用目标：节点、事实或片段 -/
inductive Target where
  | node (n : NodeId)
  | fact (k : FactKey)
  | frag (p : FragId)
  deriving DecidableEq, Repr

/-- 一句正文：文本 + 唯一的文字出处 + （AI 起草时的）程度 + 引用 + 是否是决定的结论或承诺。
    出处只有一个，是类型层面保证的“整理只在一个片段内进行”。 -/
structure Sentence where
  text : Text
  origin : FragId
  degree : Option Degree
  cites : List Target
  decision : Bool
  deriving DecidableEq, Repr

inductive VKind where
  | cognitive   -- 认知版本：认识本身变了
  | tidy        -- 整理版本：只整理表达
  deriving DecidableEq, Repr

/-- 节点的一个版本 -/
structure Version where
  kind : VKind
  concluded : Bool              -- 认识 / 疑问
  reason : Option FragId        -- 理由：我的一句话（我的确认也存成我的话）
  body : List Sentence
  fromDraft : Option Time       -- 这个版本确认的是哪份稿子（稿子的写入时间）；我直接写的为 none
  deriving DecidableEq, Repr

/-- 一条事实记录；它的作者就是出处片段的作者（推出，不另存） -/
structure FactRec where
  key : FactKey
  value : Value
  origin : FragId
  deriving DecidableEq, Repr

/-- 片段的处理结果 -/
inductive Outcome where
  | produced
  | dup
  | noInfo
  | unverified
  | skipped
  | unprocessed
  deriving DecidableEq, Repr

/-- 写入操作。每一种都是只追加的；更正、作废、撤销也是追加。 -/
inductive Op where
  | saveSource (h : Hash) (frags : List Frag)        -- 新原件，切成片段
  | saveRecord (h : Hash)                            -- 同样的内容再存：只追加保存记录
  | outcome (p : FragId) (o : Outcome)               -- 吸收记录
  | addFact (r : FactRec)                            -- 抽取一条新事实
  | addSource (k : FactKey) (v : Value) (p : FragId) -- 给已有事实追加来源
  | voidFact (t : Time)                              -- 作废写入时间为 t 的事实
  | adopt (k : FactKey) (t : Time)                   -- 冲突裁决：采用写入时间为 t 的事实
  | setAuthority (k : FactKey) (a : Author)          -- 定下这项属性以哪个作者为准
  | link (p : FragId) (n : NodeId)                   -- 关联：片段挂到节点
  | draft (n : NodeId) (p : FragId) (v : Version) (replaces : Option Time)
                                                     -- 稿子进过目（不是真源）；这个节点已有待定稿子时，
                                                     -- 新的候选并进去重新起草，replaces 指向被取代的那份
  | rejectDraft (d : Time)                           -- 我不要这份稿子（留作记录）
  | newNode (n : NodeId) (ly : Layer) (q : Question) (src : List NodeId) (ends : List NodeId)
      (v : Version) (explicit : List Sentence)       -- 新建（含分裂、合并、换阶段）；ends 原子地结束旧节点
  | writeVersion (n : NodeId) (base : Time) (v : Version) (explicit : List Sentence)
                                                     -- 确认稿子，写入新版本；base 是稿子基于的版本
  | endNode (n : NodeId) (why : FragId)              -- 结束节点，原因是我的一句话
  | move (ns : List NodeId) (ly : Layer)             -- 一组节点在世界 / 个人之间调整位置（一次写入）
  | ack (n : NodeId) (t : Target)                    -- 引用跟上了（“确认不用改”）
  | deleteRecord (h : Hash)                          -- 删除记录（内容从内容库移除，不含原内容）
  | correctAuthor (p : FragId) (a : Author)          -- 作者更正：片段原件不动，追加一条更正记录
  deriving Repr

structure Entry where
  op : Op
  actor : Actor
  deriving Repr

/-- 日志：最新的写入在表头。`e :: l` 里 `e` 的写入时间是 `l.length`。 -/
abbrev Log := List Entry

/-- `omega` 看不穿 `Time` 这类别名，先展开再算 -/
macro "nomega" : tactic =>
  `(tactic| ((try simp only [MyLife.Time, MyLife.Hash, MyLife.FragId, MyLife.NodeId,
      MyLife.Question, MyLife.Text, MyLife.Value] at *) <;> omega))

end MyLife
