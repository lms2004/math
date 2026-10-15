import Lake
open Lake DSL

package «mylife-formal» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib MyLife where
