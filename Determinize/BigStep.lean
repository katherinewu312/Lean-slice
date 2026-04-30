import Determinize.SmallStep

namespace Determinize

namespace TExpr

/-- The `n`-step semantics obtained by iterating small-step `n` times. -/
noncomputable def nstep {τ : Ty} : Nat → TExpr τ → Dist (TExpr τ)
  | 0, e =>
      Dist.ret e
  | n + 1, e =>
      Dist.bind (nstep n e) (fun e' => step e')

end TExpr

end Determinize
