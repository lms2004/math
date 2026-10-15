import MyLife.Provenance

/-!
# 分层：世界模型不引用个人认知模型（核心思想 1、世界模型 6、记录与检查）

活视图里，节点之间按 id 引用，可以有环；但在层这一级是 DAG：
个人认知模型 → 世界模型 → 原始依据层，没有反方向的边。

这条性质不是逐条写入就能保证的：节点可以在两层之间移动，被引用的节点移到个人模型、
或者引用了个人节点的节点移到世界模型，都会在不新增任何引用的情况下破坏它。
所以检查里必须有移层守卫 `MoveOK`；不加这个守卫的反例见 `MyLife.Counterexamples`。
-/

namespace MyLife

/-- 世界模型不引用个人认知模型：有效的世界节点，它当前版本引用的节点都在世界模型 -/
def LayerInv (L : Log) : Prop :=
  ∀ n x m, active L n = true → layerOf L n = some .world → latest L n = some x →
    Cites x.2 (.node m) → layerOf L m = some .world

/-- 辅助不变量：任何节点的当前版本引用的节点都已经创建 -/
def CitedCreated (L : Log) : Prop :=
  ∀ n x m, latest L n = some x → Cites x.2 (.node m) → (created L m).isSome = true

theorem citedCreated {L : Log} (hR : Reachable check L) : CitedCreated L := by
  induction hR with
  | nil => intro nc xv nd h; simp [latest] at h
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    intro nc xv nd hx hcite
    rcases e with ⟨op, actor⟩
    cases op
    case newNode n' ly q src ends v ex =>
      simp only [CheckP] at hcP
      simp only [latest] at hx
      by_cases hn : n' = nc
      · simp [hn] at hx; subst hx
        obtain ⟨s, hs, hm⟩ := hcite
        exact created_isSome_append [_] ((hcP.2.2.2.2.2.2.1 s hs).2.2.2.2.1 _ hm)
      · simp [hn] at hx
        exact created_isSome_append [_] (ih nc xv nd hx hcite)
    case writeVersion n' b v ex =>
      simp only [CheckP] at hcP
      simp only [latest] at hx
      by_cases hn : n' = nc
      · simp [hn] at hx; subst hx
        obtain ⟨s, hs, hm⟩ := hcite
        exact created_isSome_append [_] ((hcP.2.2.2.2.1 s hs).2.2.2.2.1 _ hm)
      · simp [hn] at hx
        exact created_isSome_append [_] (ih nc xv nd hx hcite)
    all_goals
      simp only [latest] at hx
      exact created_isSome_append [_] (ih nc xv nd hx hcite)

/-- **定理（分层）**：在每个合规状态里，世界模型都不引用个人认知模型 -/
theorem layerInv {L : Log} (hR : Reachable check L) : LayerInv L := by
  induction hR with
  | nil => intro nc xv nd h; simp [active] at h
  | @step l e hl hc ih =>
    have hcP := checkP_of_check hc
    have hcc := citedCreated hl
    intro nc xv nd hact hly hx hcite
    rcases e with ⟨op, actor⟩
    cases op
    case newNode n' ly q src ends v ex =>
      simp only [CheckP] at hcP
      obtain ⟨_, hnew, _, _, _, _, hver, _⟩ := hcP
      simp only [active] at hact
      simp only [layerOf] at hly ⊢
      simp only [latest] at hx
      by_cases hn : n' = nc
      · subst hn
        simp at hly hx
        subst hx; subst hly
        obtain ⟨s, hs, hm⟩ := hcite
        have hw := (hver s hs).2.2.2.2.2.1 rfl _ hm
        simp only [WorldTarget] at hw
        by_cases hm' : n' = nd
        · simp [hm']
        · simp [hm', hw]
      · simp [hn] at hact hly hx
        have hact' : active l nc = true := by
          by_cases he : nc ∈ ends
          · simp [he] at hact
          · simpa [he] using hact
        have hw := ih nc xv nd hact' hly hx hcite
        have hmc := hcc nc xv nd hx hcite
        have hm' : n' ≠ nd := by
          intro h; subst h; rw [hnew] at hmc; simp at hmc
        simp [hm', hw]
    case writeVersion n' b v ex =>
      simp only [CheckP] at hcP
      obtain ⟨_, _, _, _, hver, _⟩ := hcP
      simp only [active] at hact
      simp only [layerOf] at hly ⊢
      simp only [latest] at hx
      by_cases hn : n' = nc
      · subst hn
        simp at hx; subst hx
        obtain ⟨s, hs, hm⟩ := hcite
        exact (hver s hs).2.2.2.2.2.1 hly _ hm
      · simp [hn] at hx
        exact ih nc xv nd hact hly hx hcite
    case move ns ly =>
      simp only [CheckP] at hcP
      obtain ⟨_, _, hmove⟩ := hcP
      have hmove := hmove trivial
      simp only [active] at hact
      simp only [latest] at hx
      simp only [layerOf] at hly ⊢
      by_cases hn : nc ∈ ns
      · simp [hn] at hly; subst hly
        simp only [MoveOK] at hmove
        have hm := hmove nc hn
        simp only [hx, OptAll] at hm
        obtain ⟨s, hs, hsm⟩ := hcite
        rcases hm s hs _ hsm with ⟨m, hm', hmeq⟩ | h
        · injection hmeq with hmeq; subst hmeq; simp [hm']
        · simp only [WorldTarget] at h
          by_cases hd : nd ∈ ns
          · simp [hd]
          · simp [hd, h]
      · simp [hn] at hly
        have hw := ih nc xv nd hact hly hx hcite
        by_cases hd : nd ∈ ns
        · cases ly with
          | world => simp [hd]
          | personal =>
            exfalso
            simp only [MoveOK] at hmove
            have := hmove nc (active_mem_nodeIds hact) hn hact hly
            simp only [hx, OptAll] at this
            exact this nd hd hcite
        · simp [hd, hw]
    case endNode n' why =>
      simp only [active] at hact
      simp only [layerOf] at hly ⊢
      simp only [latest] at hx
      by_cases hn : n' = nc
      · simp [hn] at hact
      · simp [hn] at hact
        exact ih nc xv nd hact hly hx hcite
    all_goals
      simp only [active, layerOf, latest] at hact hly hx ⊢
      exact ih nc xv nd hact hly hx hcite

/-- 分层在每个历史时刻也成立（结合 `MyLife.History`） -/
theorem layerInv_at_every_time {L : Log} (hR : Reachable check L) (t : Time) :
    LayerInv (snap L t) :=
  invariant_at_every_time LayerInv (fun _ h => layerInv h) hR t

end MyLife
