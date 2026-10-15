import MyLife.Identity

/-!
# 吸收链路：只吸收新增、覆盖检查、幂等（Agent 维护层的目标）

AI 抽取被建模成任意函数 `Extractor`：同一个片段，两次运行可以给出完全不同的结果。
下面的定理对任何抽取器都成立，所以它们说的是“程序和检查保证了什么”，不依赖 AI 每次都答对：

* `ingest_only_new`：一次吸收新写进来的东西，除了原件本身和吸收记录，每一条都来自这份原件里
  原文指纹以前没处理过的片段（核心原则 3：每次输入只吸收新增的信息）。
* `ingest_covers`：吸收以后，这份原件的每个片段都有处理结果（覆盖检查）。
* `ingest_idempotent`：第一次吸收没有“未处理”的片段时，同一份输入再吸收一次，
  哪怕 AI 第二次给出完全不同的抽取结果，内容也不再变化，只多了保存记录和吸收记录。
-/

namespace MyLife

/-- AI 从一个片段里抽出的候选 -/
inductive Cand where
  | fact (k : FactKey) (v : Value)
  | link (n : NodeId)
  | draft (n : NodeId) (v : Version)

/-- 抽取器：`none` 表示没能抽出来（未处理） -/
abbrev Extractor := Frag → Option (List Cand)

/-- 程序：检查通过才写入，不通过就拒绝 -/
def tryStep (l : Log) (e : Entry) : Log := if check l e then e :: l else l

/-- 已经有处理结果（不是“未处理”）的片段里，有没有同样原文指纹的 -/
def known : Log → Text → Bool
  | [], _ => false
  | e :: l, fp =>
    (match e.op with
     | .outcome p o => decide (o ≠ .unprocessed ∧ (fragAt l p).map (fun r => r.2.fp) = some fp)
     | _ => false) || known l fp

/-- 对齐：同一身份同样的值已经有了，就只追加来源 -/
def candEntry (p : Frag) (l : Log) : Cand → Entry
  | .fact k v =>
    if LiveSame l k v then ⟨.addSource k v p.id, .agent⟩ else ⟨.addFact ⟨k, v, p.id⟩, .agent⟩
  | .link n => ⟨.link p.id n, .agent⟩
  | .draft n v => ⟨.draft n p.id v, .agent⟩

def absorb (p : Frag) (l : Log) (c : Cand) : Log := tryStep l (candEntry p l c)

def processFrag (ex : Extractor) (l : Log) (p : Frag) : Log :=
  if known l p.fp then tryStep l ⟨.outcome p.id .dup, .program⟩
  else
    match ex p with
    | none => tryStep l ⟨.outcome p.id .unprocessed, .agent⟩
    | some cs =>
      tryStep (cs.foldl (absorb p) l)
        ⟨.outcome p.id (if cs.isEmpty then .noInfo else .produced), .agent⟩

/-- 一份输入：内容哈希和切出的片段 -/
structure Source where
  hash : Hash
  frags : List Frag

/-- 收件：同样的内容再存只追加保存记录 -/
def saveEntry (l : Log) (x : Source) : Entry :=
  if hashSaved l x.hash then ⟨.saveRecord x.hash, .program⟩ else ⟨.saveSource x.hash x.frags, .program⟩

/-- 吸收：收件，再逐个片段处理（片段以第一次存入时切出的为准） -/
def ingest (ex : Extractor) (x : Source) (l : Log) : Log :=
  (fragsOf (tryStep l (saveEntry l x)) x.hash).foldl (processFrag ex) (tryStep l (saveEntry l x))

/-- 只是记账、不带新内容的写入：保存记录、吸收记录 -/
def bookkeeping : Op → Bool
  | .saveRecord _ => true
  | .outcome _ _ => true
  | _ => false

/-- 内容：去掉记账以后的写入 -/
def content (l : Log) : Log := l.filter (fun e => !bookkeeping e.op)

/-- 这条写入出自哪个片段 -/
def opFrag : Op → Option FragId
  | .addFact r => some r.origin
  | .addSource _ _ p => some p
  | .link p _ => some p
  | .draft _ p _ => some p
  | _ => none

/-! ## 只追加的扩展 -/

def Extends (l l' : Log) : Prop := ∃ ext, l' = ext ++ l

theorem Extends.refl (l : Log) : Extends l l := ⟨[], rfl⟩

theorem Extends.trans {a b c : Log} : Extends a b → Extends b c → Extends a c
  | ⟨x, hx⟩, ⟨y, hy⟩ => ⟨y ++ x, by rw [hy, hx, List.append_assoc]⟩

theorem foldl_inv {α : Type} (f : Log → α → Log) (I : Log → Prop) :
    ∀ (as : List α) (l : Log), I l → (∀ acc a, a ∈ as → I acc → I (f acc a)) → I (as.foldl f l)
  | [], _, h, _ => h
  | a :: as, l, h, step =>
    foldl_inv f I as (f l a) (step l a (List.mem_cons_self a as) h)
      (fun acc b hb hacc => step acc b (List.mem_cons_of_mem a hb) hacc)

theorem foldl_extends {α : Type} (f : Log → α → Log) (hf : ∀ acc a, Extends acc (f acc a))
    (as : List α) (l : Log) : Extends l (as.foldl f l) :=
  foldl_inv f (Extends l) as l (Extends.refl l) (fun acc a _ h => h.trans (hf acc a))

theorem tryStep_extends (l : Log) (e : Entry) : Extends l (tryStep l e) := by
  unfold tryStep; split
  · exact ⟨[e], rfl⟩
  · exact Extends.refl l

theorem absorb_extends (p : Frag) (l : Log) (c : Cand) : Extends l (absorb p l c) :=
  tryStep_extends _ _

theorem processFrag_extends (ex : Extractor) (l : Log) (p : Frag) : Extends l (processFrag ex l p) := by
  unfold processFrag
  split
  · exact tryStep_extends _ _
  · split
    · exact tryStep_extends _ _
    · exact (foldl_extends _ (absorb_extends p) _ l).trans (tryStep_extends _ _)

theorem ingest_extends (ex : Extractor) (x : Source) (l : Log) : Extends l (ingest ex x l) :=
  (tryStep_extends l _).trans (foldl_extends _ (processFrag_extends ex) _ _)

/-! ## 程序只做合规写入 -/

theorem tryStep_reachable {l : Log} (e : Entry) (h : Reachable check l) :
    Reachable check (tryStep l e) := by
  unfold tryStep; split
  · next hc => exact Reachable.step h hc
  · exact h

theorem processFrag_reachable (ex : Extractor) {l : Log} (p : Frag) (h : Reachable check l) :
    Reachable check (processFrag ex l p) := by
  unfold processFrag
  split
  · exact tryStep_reachable _ h
  · split
    · exact tryStep_reachable _ h
    · apply tryStep_reachable
      exact foldl_inv (absorb p) (Reachable check) _ l h (fun acc _ _ ha => tryStep_reachable _ ha)

/-- 吸收只会产生通过检查的写入 -/
theorem ingest_reachable (ex : Extractor) (x : Source) {l : Log} (h : Reachable check l) :
    Reachable check (ingest ex x l) :=
  foldl_inv (processFrag ex) (Reachable check) _ _ (tryStep_reachable _ h)
    (fun _ p _ ha => processFrag_reachable ex p ha)

/-! ## 原件和片段的单调性 -/

theorem known_append {l : Log} {fp : Text} : ∀ (ext : Log), known l fp = true → known (ext ++ l) fp = true
  | [], h => h
  | e :: ext, h => by simp [known, known_append ext h]

theorem known_of_extends {l l' : Log} {fp : Text} (h : Extends l l') (hk : known l fp = true) :
    known l' fp = true := by
  obtain ⟨ext, rfl⟩ := h; exact known_append ext hk

theorem hashSaved_of_extends {l l' : Log} {h : Hash} (he : Extends l l') (hs : hashSaved l h = true) :
    hashSaved l' h = true := by
  obtain ⟨ext, rfl⟩ := he; exact hashSaved_append ext hs

theorem fragsOf_eq_nil : ∀ {l : Log} {h : Hash}, hashSaved l h = false → fragsOf l h = []
  | [], _, _ => rfl
  | e :: l, h, hs => by
    rcases e with ⟨op, actor⟩
    simp only [hashSaved, Bool.or_eq_false_iff] at hs
    cases op <;> simp_all [fragsOf]

theorem fragsOf_cons_of_saved {l : Log} {h : Hash} (e : Entry) (hs : hashSaved l h = true) :
    fragsOf (e :: l) h = fragsOf l h := by
  simp [fragsOf, hs]

theorem fragsOf_of_extends {l l' : Log} {h : Hash} (he : Extends l l') (hs : hashSaved l h = true) :
    fragsOf l' h = fragsOf l h := by
  obtain ⟨ext, rfl⟩ := he
  induction ext with
  | nil => rfl
  | cons e ext ih => rw [List.cons_append, fragsOf_cons_of_saved e (hashSaved_append ext hs), ih]

theorem mem_fragsOf_frags : ∀ {l : Log} {h : Hash} {p : Frag}, p ∈ fragsOf l h → p ∈ frags l
  | [], _, _, hp => by simp [fragsOf] at hp
  | e :: l, h, p, hp => by
    simp only [fragsOf] at hp
    simp only [frags, List.mem_append]
    split at hp
    · exact Or.inr (mem_fragsOf_frags hp)
    · split at hp
      · next h' fs hop =>
        split at hp
        · left; simp [newFrags, hop]; exact hp
        · simp at hp
      · simp at hp

/-! ## 只吸收新增 -/

/-- 写入 e 是记账、是这份原件本身，或者出自一个原文指纹以前没处理过的片段 -/
def FreshFrom (l : Log) (ps : List Frag) (x : Source) (e : Entry) : Prop :=
  bookkeeping e.op = true ∨ e.op = .saveSource x.hash x.frags ∨
  ∃ p ∈ ps, opFrag e.op = some p.id ∧ known l p.fp = false

/-- 从 l 到 l' 只追加了满足 S 的写入 -/
def AddedOnly (S : Entry → Prop) (l l' : Log) : Prop := ∃ ext, l' = ext ++ l ∧ ∀ e ∈ ext, S e

theorem AddedOnly.refl (S : Entry → Prop) (l : Log) : AddedOnly S l l := ⟨[], rfl, by simp⟩

theorem AddedOnly.trans {S : Entry → Prop} {a b c : Log} :
    AddedOnly S a b → AddedOnly S b c → AddedOnly S a c
  | ⟨x, hx, sx⟩, ⟨y, hy, sy⟩ =>
    ⟨y ++ x, by rw [hy, hx, List.append_assoc], by
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact sy e h
      · exact sx e h⟩

theorem AddedOnly.extends {S : Entry → Prop} {l l' : Log} (h : AddedOnly S l l') : Extends l l' := by
  obtain ⟨ext, hl, _⟩ := h; exact ⟨ext, hl⟩

theorem AddedOnly.tryStep {S : Entry → Prop} (l : Log) {e : Entry} (h : S e) :
    AddedOnly S l (tryStep l e) := by
  unfold MyLife.tryStep; split
  · exact ⟨[e], rfl, by simp [h]⟩
  · exact AddedOnly.refl S l

theorem processFrag_fresh (ex : Extractor) (l : Log) (ps : List Frag) (x : Source) {acc : Log}
    {p : Frag} (hp : p ∈ ps) (hacc : AddedOnly (FreshFrom l ps x) l acc) :
    AddedOnly (FreshFrom l ps x) l (processFrag ex acc p) := by
  apply hacc.trans
  unfold processFrag
  split
  · exact AddedOnly.tryStep _ (Or.inl rfl)
  · next hk =>
    have hkl : known l p.fp = false := by
      cases h : known l p.fp
      · rfl
      · exact absurd (known_of_extends hacc.extends h) hk
    split
    · exact AddedOnly.tryStep _ (Or.inl rfl)
    · next cs _ =>
      apply AddedOnly.trans _ (AddedOnly.tryStep _ (Or.inl rfl))
      apply foldl_inv (absorb p) (AddedOnly (FreshFrom l ps x) acc) cs acc (AddedOnly.refl _ _)
      intro acc' c _ h'
      apply h'.trans
      apply AddedOnly.tryStep
      right; right
      refine ⟨p, hp, ?_, hkl⟩
      cases c with
      | fact k v => simp only [candEntry]; split <;> rfl
      | link n => rfl
      | draft n v => rfl

/-- **定理（只吸收新增）**：一次吸收新写进来的每一条，要么是记账（保存记录、吸收记录），
    要么是这份原件本身，要么出自这份原件里一个原文指纹以前没处理过的片段 -/
theorem ingest_only_new (ex : Extractor) (x : Source) (l : Log) :
    AddedOnly (FreshFrom l (fragsOf (tryStep l (saveEntry l x)) x.hash) x) l (ingest ex x l) := by
  unfold ingest
  apply foldl_inv
  · apply AddedOnly.tryStep
    unfold saveEntry
    split
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro acc p hp hacc
    exact processFrag_fresh ex l _ x hp hacc

/-! ## 覆盖检查 -/

def HasOutcome (L : Log) (p : FragId) : Prop :=
  ∃ l₁ e l o, L = l₁ ++ e :: l ∧ e.op = .outcome p o

theorem hasOutcome_of_extends {l l' : Log} {p : FragId} (he : Extends l l') (h : HasOutcome l p) :
    HasOutcome l' p := by
  obtain ⟨ext, rfl⟩ := he
  obtain ⟨l₁, e, l, o, rfl, hop⟩ := h
  exact ⟨ext ++ l₁, e, l, o, by simp, hop⟩

theorem tryStep_outcome {l : Log} {p : FragId} {o : Outcome} {a : Actor}
    (h : (fragAt l p).isSome = true) : tryStep l ⟨.outcome p o, a⟩ = ⟨.outcome p o, a⟩ :: l := by
  simp [tryStep, check, checkG, CheckP, h]

theorem known_outcome {l : Log} {p : Frag} {t : Time} {o : Outcome} {a : Actor}
    (hf : fragAt l p.id = some (t, p)) (ho : o ≠ .unprocessed) :
    known (⟨.outcome p.id o, a⟩ :: l) p.fp = true := by
  simp [known, hf, ho]

theorem foldl_all {α : Type} (f : Log → α → Log) (P : Log → α → Prop) (A : α → Prop) (base : Log)
    (hext : ∀ acc a, Extends acc (f acc a))
    (hmono : ∀ a l l', Extends l l' → P l a → P l' a)
    (hstep : ∀ acc a, A a → Extends base acc → P (f acc a) a) :
    ∀ (as : List α) (acc : Log), Extends base acc → (∀ a ∈ as, A a) → ∀ a ∈ as, P (as.foldl f acc) a
  | [], _, _, _, a, ha => by simp at ha
  | b :: bs, acc, hb, hA, a, ha => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hmono _ _ _ (foldl_extends f hext bs _) (hstep acc a (hA a (List.mem_cons_self _ _)) hb)
    · exact foldl_all f P A base hext hmono hstep bs (f acc b) (hb.trans (hext acc b))
        (fun c hc => hA c (List.mem_cons_of_mem _ hc)) a ha

theorem fragsOf_ingest (ex : Extractor) (x : Source) (l : Log) :
    fragsOf (ingest ex x l) x.hash = fragsOf (tryStep l (saveEntry l x)) x.hash := by
  cases hs : hashSaved (tryStep l (saveEntry l x)) x.hash with
  | true => exact fragsOf_of_extends (foldl_extends _ (processFrag_extends ex) _ _) hs
  | false => simp [ingest, fragsOf_eq_nil hs]

/-- 处理一个片段之后：它有处理结果；抽取器没失败时，它的原文指纹算已处理 -/
theorem processFrag_settles (ex : Extractor) {acc : Log} {p : Frag} {t : Time}
    (hf : fragAt acc p.id = some (t, p)) :
    HasOutcome (processFrag ex acc p) p.id ∧ (ex p ≠ none → known (processFrag ex acc p) p.fp = true) := by
  have hsome : (fragAt acc p.id).isSome = true := by simp [hf]
  unfold processFrag
  split
  · next hk =>
    rw [tryStep_outcome hsome]
    exact ⟨⟨[], _, acc, _, rfl, rfl⟩, fun _ => known_append [_] hk⟩
  · split
    · next hnone =>
      rw [tryStep_outcome hsome]
      exact ⟨⟨[], _, acc, _, rfl, rfl⟩, fun h => absurd hnone h⟩
    · next cs _ =>
      have hext := foldl_extends _ (absorb_extends p) cs acc
      obtain ⟨ext, hext'⟩ := hext
      have hf' : fragAt (cs.foldl (absorb p) acc) p.id = some (t, p) := by
        rw [hext']; exact fragAt_append_of_some ext hf
      have hsome' : (fragAt (cs.foldl (absorb p) acc) p.id).isSome = true := by simp [hf']
      rw [tryStep_outcome hsome']
      refine ⟨⟨[], _, _, _, rfl, rfl⟩, fun _ => known_outcome hf' ?_⟩
      split <;> simp

theorem frag_of_mem_fragsOf {l : Log} {h : Hash} {p : Frag} (hR : Reachable check l)
    (hp : p ∈ fragsOf l h) : ∃ t, fragAt l p.id = some (t, p) :=
  fragInv hR p (mem_fragsOf_frags hp)

/-- **定理（覆盖检查）**：吸收以后，这份原件的每个片段都有处理结果；抽取器在这些片段上都没失败时，
    它们的原文指纹都算已处理 -/
theorem ingest_covers (ex : Extractor) (x : Source) {l : Log} (hR : Reachable check l) :
    ∀ p ∈ fragsOf (ingest ex x l) x.hash,
      HasOutcome (ingest ex x l) p.id ∧ (ex p ≠ none → known (ingest ex x l) p.fp = true) := by
  rw [fragsOf_ingest]
  have hR₁ := tryStep_reachable (saveEntry l x) hR
  intro p hp
  apply foldl_all (processFrag ex)
    (fun L p => HasOutcome L p.id ∧ (ex p ≠ none → known L p.fp = true))
    (fun p => ∃ t, fragAt (tryStep l (saveEntry l x)) p.id = some (t, p))
    (tryStep l (saveEntry l x)) (processFrag_extends ex)
  · intro a L L' he ⟨h1, h2⟩
    exact ⟨hasOutcome_of_extends he h1, fun h => known_of_extends he (h2 h)⟩
  · intro acc a ⟨t, ht⟩ he
    obtain ⟨ext, rfl⟩ := he
    exact processFrag_settles ex (fragAt_append_of_some ext ht)
  · exact Extends.refl _
  · intro q hq; exact frag_of_mem_fragsOf hR₁ hq
  · exact hp

/-! ## 幂等 -/

theorem content_tryStep_book {l : Log} {e : Entry} (h : bookkeeping e.op = true) :
    content (tryStep l e) = content l := by
  unfold tryStep; split <;> simp [content, List.filter_cons, h]

/-- 这份原件已经存过、每个片段的原文指纹都处理过时，再吸收一次只追加记账，内容不变 -/
theorem ingest_noop (ex : Extractor) (x : Source) {l : Log} (hs : hashSaved l x.hash = true)
    (hk : ∀ p ∈ fragsOf l x.hash, known l p.fp = true) :
    content (ingest ex x l) = content l := by
  have hsave : saveEntry l x = ⟨.saveRecord x.hash, .program⟩ := by simp [saveEntry, hs]
  unfold ingest
  rw [hsave]
  have hext₁ := tryStep_extends l ⟨.saveRecord x.hash, .program⟩
  rw [fragsOf_of_extends hext₁ hs]
  have := foldl_inv (processFrag ex) (fun acc => Extends l acc ∧ content acc = content l)
    (fragsOf l x.hash) (tryStep l ⟨.saveRecord x.hash, .program⟩)
    ⟨hext₁, content_tryStep_book rfl⟩
    (by
      intro acc p hp ⟨he, hc⟩
      have hka : known acc p.fp = true := known_of_extends he (hk p hp)
      simp only [processFrag, hka, if_true]
      exact ⟨he.trans (tryStep_extends _ _), (content_tryStep_book rfl).trans hc⟩)
  exact this.2

theorem ingest_of_not_saved (ex : Extractor) (x : Source) {l : Log}
    (hs : hashSaved (tryStep l (saveEntry l x)) x.hash = false) : ingest ex x l = l := by
  have hl : hashSaved l x.hash = false := by
    cases h : hashSaved l x.hash
    · rfl
    · rw [hashSaved_of_extends (tryStep_extends l _) h] at hs; cases hs
  have hsave : saveEntry l x = ⟨.saveSource x.hash x.frags, .program⟩ := by simp [saveEntry, hl]
  have hrej : tryStep l (saveEntry l x) = l := by
    rw [hsave] at hs ⊢
    unfold tryStep at hs ⊢
    split
    · next hc => rw [if_pos hc] at hs; simp [hashSaved] at hs
    · rfl
  simp [ingest, hrej, fragsOf_eq_nil hl]

/-- **定理（幂等）**：第一次吸收时抽取器在每个片段上都没失败，那么同一份输入再吸收一次，
    不管 AI 第二次给出什么抽取结果，内容都不再变化 -/
theorem ingest_idempotent (ex₁ ex₂ : Extractor) (x : Source) {l : Log} (hR : Reachable check l)
    (htot : ∀ p, ex₁ p ≠ none) :
    content (ingest ex₂ x (ingest ex₁ x l)) = content (ingest ex₁ x l) := by
  cases hs : hashSaved (ingest ex₁ x l) x.hash with
  | true =>
    apply ingest_noop ex₂ x hs
    intro p hp
    exact (ingest_covers ex₁ x hR p hp).2 (htot p)
  | false =>
    have hs₁ : hashSaved (tryStep l (saveEntry l x)) x.hash = false := by
      cases h : hashSaved (tryStep l (saveEntry l x)) x.hash
      · rfl
      · have h2 : hashSaved (ingest ex₁ x l) x.hash = true :=
          hashSaved_of_extends (foldl_extends _ (processFrag_extends ex₁) _ _) h
        rw [h2] at hs; cases hs
    rw [ingest_of_not_saved ex₁ x hs₁, ingest_of_not_saved ex₂ x hs₁]

end MyLife
