import MyLife.Propagation
import MyLife.Ingest
import MyLife.Counterexamples

/-!
# 审计：主要定理只依赖 Lean 的标准公理

构建时会打印每条定理依赖的公理。只要列表里没有 `sorryAx`（未完成的证明）
或 `Lean.ofReduceBool`（用编译代码代替证明），这些定理就是被 Lean 内核完整检查过的。
-/

open MyLife MyLife.Counterexamples

-- 结构：存储层是 DAG、节点来源无环
#print axioms storage_acyclic
#print axioms lineage_acyclic
-- 只追加与历史还原
#print axioms step_suffix
#print axioms snap_append
#print axioms invariant_at_every_time
-- 只有我能拍板、可追溯、看得出谁起草
#print axioms only_me_decides
#print axioms facts_traceable_not_ai
#print axioms added_sources_not_ai
#print axioms sentence_traceable
#print axioms degree_rules
#print axioms cognitive_has_reason
#print axioms decisions_confirmed
-- 分层
#print axioms layerInv
#print axioms layerInv_at_every_time
-- 不重复
#print axioms sources_unique
#print axioms fragInv
#print axioms uniqueInv
#print axioms factUnique
-- 事实的当前值
#print axioms conflict_keeps_current
#print axioms same_author_supersedes
#print axioms authority_supersedes
#print axioms authority_silences_others
#print axioms current_not_ai
#print axioms conflicts_only_me
#print axioms evidence_unaffected_by_cognition
-- 更新的传播
#print axioms cognitive_version_flags_citers
#print axioms fact_change_flags_citers
#print axioms ack_clears
#print axioms quiet_no_new_stale
#print axioms world_not_stale_by_personal
#print axioms node_change_by_me
-- 吸收链路
#print axioms ingest_reachable
#print axioms ingest_only_new
#print axioms ingest_covers
#print axioms ingest_idempotent
-- 反例
#print axioms move_guard_needed
#print axioms atomic_end_needed
#print axioms cas_needed
#print axioms void_guard_needed
#print axioms live_graph_may_cycle
