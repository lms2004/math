# MyLife 操作接口契约

这份契约是业务模型的人话版本，对应 Lean 里的写入检查 `CheckP`（`MyLife/Log.lean`）和推出的视图。
它是业务设计和技术设计的分界线：业务模型保证“只要每次写入都按这里检查、一次追加一条，
那些性质就成立”；技术设计只需要回答一个问题——怎么实现这份契约。

实现里每个 MCP 写入工具都应当对应下面的一种写入，做同样的检查，不满足就拒绝，并把被拦下的写入记入操作日志。

## 1. 写入操作

| 写入 | 谁发起 | 写入前检查（不满足就拒绝） | 对应设计 | Lean 定理 |
|---|---|---|---|---|
| 存原件 `saveSource` | 程序、Agent（我要求保存的） | 这个哈希没存过；切出的片段 id 互不重复，也没被用过 | 原始依据层 3、4 | `sources_unique`、`fragInv` |
| 保存记录 `saveRecord` | 程序 | 这个哈希存过（删除过的，内容恢复） | 原始依据层 3、删除 | `ingest_restores_deleted` |
| 吸收记录 `outcome` | 程序、Agent | 片段存在 | 吸收链路 5 | `ingest_covers` |
| 抽取事实 `addFact` | Agent、我 | 出处片段存在，现在的作者是我或外部发布者（不是 AI，也不是作者不明）；同一身份、同样的值没有有效记录（有就改成追加来源） | 吸收链路 3、4 | `facts_traceable_not_ai`、`factUnique` |
| 追加来源 `addSource` | Agent | 出处作者是我或外部发布者；同一身份、同样的值已有有效记录 | 吸收链路 4 | `added_sources_not_ai` |
| 作废事实 `voidFact` | Agent、我 | 记录存在；不是我发起时，这项属性没有待裁决的冲突 | Agent 的边界 1 | `conflicts_only_me` |
| 冲突裁决 `adopt` | 我 | 记录存在、属于这项属性、没作废，出处现在的作者是我或外部发布者 | 事实 · 当前值 | `current_not_ai` |
| 定权威作者 `setAuthority` | 我 | — | 事实 · 当前值 | `authority_supersedes`、`authority_overrides_listed` |
| 挂关联 `link` | Agent | 片段和节点都存在 | 数据和存放 · 关联 | — |
| 起草稿子 `draft` | Agent | 片段存在；这个节点已有待定稿子时必须指向它（并进去重新起草），没有时不能指向；稿子里没有我在这个节点上拒绝过的句子 | 吸收链路 4、6 | `pending_unique`、`rejected_never_reproposed` |
| 不要稿子 `rejectDraft` | 我 | 稿子还在过目里 | 过目 | `draft_leaves_review_only_by` |
| 新建节点 `newNode`（含分裂、合并、换阶段） | 我 | id 没用过；来源节点都存在；一并结束的旧节点都有效；是认知版本；除了一并结束的，没有别的有效节点回答同一个问题；正文检查；确认稿子时同下 | 核心原则 1 | `uniqueInv`、`lineage_acyclic` |
| 写新版本 `writeVersion` | 我 | 节点有效；基于的版本就是最新版本；认知版本有理由（我的话）；正文检查；确认稿子时：稿子还在过目里，基于节点现在的最新版本，上一版本里出处是我的话的句子原样保留或我逐句决定改 | 核心原则 1、2，分析链路 5 | `cognitive_has_reason`、`confirmed_draft_fresh`、`my_sentences_kept` |
| 结束节点 `endNode` | 我 | 节点有效；原因是我的一句话 | 核心原则 1 | — |
| 移层 `move`（一组） | 我 | 节点都存在；移到个人认知模型：组外没有有效的世界节点引用组里的节点；移到世界模型：组里节点引用的节点都在组里或已在世界模型 | 数据和存放 | `layerInv`、`moveBlockers` |
| 确认不用改 `ack` | 我 | 节点有效，当前版本引用了这个目标 | 更新的传播 2 | `ack_clears` |
| 删除 `deleteRecord` | 我 | 这个哈希存过 | 原始依据层 · 删除 | `delete_keeps_structure`、`deletionList_exact` |
| 作者更正 `correctAuthor` | 我 | 片段存在 | 原始依据层 · 作者 | `sentence_ok_now_or_flagged`、`fact_ok_now_or_flagged` |

**正文检查**（新建节点和写新版本时，对每一句做）：出处存在，现在的作者是我或 AI；AI 起草的标程度，我的话不标；
标“确定”的至少引用一处事实或我的话；引用的节点、事实、片段都已存在；世界节点只引用世界节点；
决定的结论和承诺在逐句确认清单里。（`degree_rules`、`sentence_traceable`、`decisions_confirmed`、`layerInv`）

## 2. 推出的视图（不存，由数据算出）

| 视图 | 内容 | Lean |
|---|---|---|
| Current Model | 所有有效节点的最新版本 | `currentNode` |
| 事实的状态 | 当前值、待裁决的冲突、被权威作者盖过的说法 | `fstate` |
| 过目事项 | 引用没跟上的（`Stale`）、出处作者被更正过的（`AuthorFlag`）、待定稿子（`pendingFor`） | `Propagation`、`Provenance`、`Review` |
| 句子的来源类别 | 原话 / 整理 / AI 起草 | `drafter` |
| 移层被挡时的引用者 | 程序列给我的节点 | `moveBlockers` |
| 删除清单 | 直接或间接依赖这份原件的所有写入 | `deletionList` |
| 重新吸收后受影响的节点 | 当前版本里有句子出处在这份原件里的有效节点 | `reingestAffected` |
| 任意历史时刻的状态 | 写入时间早于那一刻的部分 | `snap` |

## 3. 程序（由上面的写入组合而成）

| 程序 | 步骤 | Lean |
|---|---|---|
| 吸收 | 收件（存原件或保存记录）→ 逐个片段：原文已处理过的记为重复；否则抽取、对齐、写入，记处理结果 | `ingest_only_new`、`ingest_covers`、`ingest_idempotent` |
| 重新吸收 | 作废这份原件之前产生的事实（有待裁决冲突的作废不了，冲突留在过目里）→ 逐个片段重新抽取 → 列出受影响的节点；不动正文 | `reingest_voids_old`、`reingest_body_untouched`、`reingestAffected_complete` |

## 4. 技术设计必须先定的三件事

这三件不属于契约本身，但定错了，上面的性质在实现里就不成立：

1. **原子**：一次写入（数据变更、吸收记录、操作日志）要么全部成功，要么全部不写；
   检查和写入之间不能插入别的写入，否则原件唯一、问题唯一、稿子基于最新版本、冲突判断都会被并发打破。
2. **文字存在哪**：建议放在内容寻址库，Git 和日志里只存哈希；这样删除只动内容库，不用改写 Git 历史。
3. **引用用 id**：节点移层会换目录，引用一律用 id，路径由 id 推出。
