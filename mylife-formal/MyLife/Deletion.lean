import MyLife.Dag
import MyLife.Ingest

/-!
# 删除的级联（原始依据层 · 删除）

我要求删除一份原件时，程序列出含这段内容的所有地方，我逐项决定一起删除还是保留。

* 列出的清单是什么：直接或间接依赖这份原件的所有写入（从它抽出的事实、出处在它里面的句子和
  这些句子的历史版本、引用这些事实或版本的版本、稿子、吸收记录……）。因为存储层是 DAG，
  按写入顺序从旧到新扫一遍日志就能算完（`affected`）。这里证明这份清单**恰好**是依赖它的写入：不漏，也不多。
* 删除只动内容库：片段 id、出处、事实、版本都不变，出处指向删除记录，所有可追溯的定理照样成立。
* 同样的内容以后再存：按哈希走“保存记录”，内容恢复。

日志之外的地方（runtime 的索引和 embedding、Git 历史、备份）不在模型里，由实现按这份清单去清理。
-/

namespace MyLife

/-- 直接或间接依赖时刻 s 那条写入的所有写入 -/
def affected : Log → Time → List Time
  | [], _ => []
  | e :: l, s =>
    if (refs l e).any (fun j => decide (j = s ∨ j ∈ affected l s)) then l.length :: affected l s
    else affected l s

theorem edge_cons {e : Entry} {l : Log} {i j : Time} :
    Edge (e :: l) i j ↔ (i = l.length ∧ j ∈ refs l e) ∨ Edge l i j := by
  constructor
  · rintro ⟨l₁, e', l', hL, hi, hj⟩
    cases l₁ with
    | nil =>
      simp at hL
      obtain ⟨rfl, rfl⟩ := hL
      exact Or.inl ⟨hi.symm, hj⟩
    | cons x l₁' =>
      simp at hL
      obtain ⟨rfl, hl⟩ := hL
      exact Or.inr ⟨l₁', e', l', hl, hi, hj⟩
  · rintro (⟨rfl, hj⟩ | ⟨l₁, e', l', hL, hi, hj⟩)
    · exact ⟨[], e, l, rfl, rfl, hj⟩
    · exact ⟨e :: l₁, e', l', by simp [hL], hi, hj⟩

theorem edge_src_lt {l : Log} {i j : Time} (h : Edge l i j) : i < l.length := by
  obtain ⟨l₁, e, l', rfl, rfl, _⟩ := h
  simp; nomega

theorem path_lift {e : Entry} {l : Log} {i s : Time} (h : Relation.TransGen (Edge l) i s) :
    Relation.TransGen (Edge (e :: l)) i s := by
  induction h with
  | single h => exact .single (edge_cons.mpr (Or.inr h))
  | tail _ h ih => exact .tail ih (edge_cons.mpr (Or.inr h))

theorem path_of_cons {e : Entry} {l : Log} {i s : Time}
    (h : Relation.TransGen (Edge (e :: l)) i s) (hi : i < l.length) :
    Relation.TransGen (Edge l) i s := by
  induction h with
  | single h =>
    rcases edge_cons.mp h with ⟨rfl, _⟩ | h
    · exact absurd hi (Nat.lt_irrefl _)
    · exact .single h
  | tail hab hbc ih =>
    have hb := Nat.lt_trans (path_lt hab) hi
    rcases edge_cons.mp hbc with ⟨hb', _⟩ | h
    · rw [hb'] at hb; exact absurd hb (Nat.lt_irrefl _)
    · exact .tail ih h

theorem transGen_head_cases {α : Type} {r : α → α → Prop} {a c : α} (h : Relation.TransGen r a c) :
    r a c ∨ ∃ b, r a b ∧ Relation.TransGen r b c := by
  induction h with
  | single h => exact Or.inl h
  | tail _ hbc ih =>
    rcases ih with hab | ⟨b', hab', hb'⟩
    · exact Or.inr ⟨_, hab, .single hbc⟩
    · exact Or.inr ⟨b', hab', .tail hb' hbc⟩

/-- **定理（级联清单恰好是依赖它的写入）**：i 在清单里，当且仅当在存储层的引用图里有一条从 i 到 s 的路径 -/
theorem affected_iff : ∀ {L : Log} {s i : Time},
    i ∈ affected L s ↔ Relation.TransGen (Edge L) i s
  | [], s, i => by
    simp only [affected, List.not_mem_nil, false_iff]
    intro h
    rcases transGen_head_cases h with h | ⟨_, h, _⟩ <;>
      (obtain ⟨l₁, e, l, hL, _⟩ := h; simp at hL)
  | e :: l, s, i => by
    have ih : ∀ {j}, j ∈ affected l s ↔ Relation.TransGen (Edge l) j s := affected_iff
    constructor
    · intro h
      simp only [affected] at h
      split at h
      · next hany =>
        rcases List.mem_cons.mp h with rfl | h
        · rw [List.any_eq_true] at hany
          obtain ⟨j, hj, hjs⟩ := hany
          simp only [decide_eq_true_eq] at hjs
          rcases hjs with rfl | hjA
          · exact .single (edge_cons.mpr (Or.inl ⟨rfl, hj⟩))
          · exact Relation.TransGen.trans (.single (edge_cons.mpr (Or.inl ⟨rfl, hj⟩)))
              (path_lift (ih.mp hjA))
        · exact path_lift (ih.mp h)
      · exact path_lift (ih.mp h)
    · intro h
      have hfirst : ∃ b, Edge (e :: l) i b := by
        rcases transGen_head_cases h with hab | ⟨b, hab, _⟩
        · exact ⟨s, hab⟩
        · exact ⟨b, hab⟩
      obtain ⟨b₀, hb₀⟩ := hfirst
      have hle : i < l.length + 1 := by simpa using edge_src_lt hb₀
      by_cases hi : i = l.length
      · subst hi
        have hcond : (refs l e).any (fun j => decide (j = s ∨ j ∈ affected l s)) = true := by
          rcases transGen_head_cases h with hab | ⟨b, hab, hbc⟩
          · rcases edge_cons.mp hab with ⟨_, hj⟩ | hab
            · exact List.any_eq_true.mpr ⟨s, hj, by simp⟩
            · exact absurd (edge_src_lt hab) (Nat.lt_irrefl _)
          · rcases edge_cons.mp hab with ⟨_, hj⟩ | hab
            · have hb := refs_lt hj
              exact List.any_eq_true.mpr ⟨b, hj, by simp [ih.mpr (path_of_cons hbc hb)]⟩
            · exact absurd (edge_src_lt hab) (Nat.lt_irrefl _)
        simp only [affected]
        rw [if_pos hcond]
        exact List.mem_cons_self _ _
      · have hi' : i < l.length := by nomega
        have hA := ih.mpr (path_of_cons h hi')
        simp only [affected]
        split
        · exact List.mem_cons_of_mem _ hA
        · exact hA

/-- 删除一份原件时程序列出的写入：存入它的那条写入，以及直接或间接依赖它的所有写入 -/
def deletionList (L : Log) (h : Hash) : List Time :=
  match hashTime L h with
  | some s => s :: affected L s
  | none => []

/-- **定理（删除清单不漏也不多）** -/
theorem deletionList_exact {L : Log} {h : Hash} {s i : Time} (hs : hashTime L h = some s) :
    i ∈ deletionList L h ↔ i = s ∨ Relation.TransGen (Edge L) i s := by
  simp only [deletionList, hs, List.mem_cons]
  rw [affected_iff]

/-! ## 删除只动内容；同样的内容再存，内容恢复 -/

/-- 内容库里现在有没有这份原件的内容（推出） -/
def contentPresent : Log → Hash → Bool
  | [], _ => false
  | e :: l, h =>
    match e.op with
    | .saveSource h' _ => if h' = h then true else contentPresent l h
    | .saveRecord h' => if h' = h then true else contentPresent l h
    | .deleteRecord h' => if h' = h then false else contentPresent l h
    | _ => contentPresent l h

theorem delete_hides (l : Log) (h : Hash) (a : Actor) :
    contentPresent (⟨.deleteRecord h, a⟩ :: l) h = false := by
  simp [contentPresent]

/-- **定理（删除只动内容）**：删除记录不改变片段、出处、事实、版本和“存过”的记录，
    所以出处仍然指得到（指向删除记录），所有可追溯的定理在删除后照样成立 -/
theorem delete_keeps_structure (l : Log) (h : Hash) (a : Actor) :
    frags (⟨.deleteRecord h, a⟩ :: l) = frags l ∧
    (∀ p, fragAt (⟨.deleteRecord h, a⟩ :: l) p = fragAt l p) ∧
    records (⟨.deleteRecord h, a⟩ :: l) = records l ∧
    versions (⟨.deleteRecord h, a⟩ :: l) = versions l ∧
    hashSaved (⟨.deleteRecord h, a⟩ :: l) h = hashSaved l h := by
  refine ⟨by simp [frags, newFrags], fun p => ?_, by simp [records], by simp [versions],
    by simp [hashSaved]⟩
  cases hf : fragAt l p <;> simp [fragAt, newFrags, hf]

theorem contentPresent_of_no_delete {l : Log} {h : Hash} :
    ∀ (ext : Log), (∀ e ∈ ext, ∀ a, e.op ≠ .deleteRecord a) →
      contentPresent l h = true → contentPresent (ext ++ l) h = true
  | [], _, hc => hc
  | e :: ext, hn, hc => by
    have ih := contentPresent_of_no_delete ext (fun e' he' => hn e' (List.mem_cons_of_mem _ he')) hc
    have he := hn e (List.mem_cons_self _ _)
    rcases e with ⟨op, actor⟩
    cases op
    case deleteRecord h' => exact absurd rfl (he h')
    all_goals
      simp only [List.cons_append, contentPresent]
      try split
      all_goals simp_all

/-- **定理（删除后再存，内容恢复）**：一份删过的原件（哈希仍记作“存过”），同样的内容再吸收一次，内容回到内容库 -/
theorem ingest_restores_deleted (ex : Extractor) (x : Source) {l : Log} (hs : hashSaved l x.hash = true) :
    contentPresent (ingest ex x l) x.hash = true := by
  have hsave : saveEntry l x = ⟨.saveRecord x.hash, .program⟩ := by simp [saveEntry, hs]
  have hstep : tryStep l (saveEntry l x) = ⟨.saveRecord x.hash, .program⟩ :: l := by
    rw [hsave]; simp [tryStep, check, checkG, CheckP, hs]
  obtain ⟨ext, heq, hfresh⟩ := ingest_only_new ex x l
  have hext₁ : ∃ ext', ingest ex x l = ext' ++ (⟨.saveRecord x.hash, .program⟩ :: l) := by
    have := foldl_extends _ (processFrag_extends ex)
      (fragsOf (⟨.saveRecord x.hash, .program⟩ :: l) x.hash) (⟨.saveRecord x.hash, .program⟩ :: l)
    unfold ingest
    rw [hstep]
    exact this
  obtain ⟨ext', heq'⟩ := hext₁
  have hn : ∀ e ∈ ext', ∀ a, e.op ≠ .deleteRecord a := by
    intro e he a hop
    have hmem : e ∈ ext := by
      have h2 : ext ++ l = ext' ++ ([⟨.saveRecord x.hash, .program⟩] ++ l) := by
        rw [← heq, heq']; rfl
      have h3 : ext = ext' ++ [⟨.saveRecord x.hash, .program⟩] := by
        rw [← List.append_assoc] at h2
        exact List.append_cancel_right h2
      rw [h3]; exact List.mem_append_left _ he
    rcases hfresh e hmem with hb | hs' | ⟨_, _, hf, _⟩
    · rw [hop] at hb; simp [bookkeeping] at hb
    · rw [hop] at hs'; cases hs'
    · rw [hop] at hf; simp [opFrag] at hf
  rw [heq']
  exact contentPresent_of_no_delete ext' hn (by simp [contentPresent])

end MyLife
