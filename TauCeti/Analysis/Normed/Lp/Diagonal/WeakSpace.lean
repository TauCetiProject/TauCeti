/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
import TauCeti.Analysis.Normed.Module.WeakSpace.Closure
import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace

/-!
# Harmonic diagonal counterexamples in the weak topology on `ℓ^p`

On `ℓ^p(ℕ, 𝕜)` (`1 ≤ p ≤ ∞`) over `ℝ` or `ℂ`, the harmonic diagonal multiplier
`J = lp.diagonalCLM (p := p) (lp.invNatSucc 𝕜)` is a compact operator of infinite-dimensional range.
It witnesses the sharp topological-versus-sequential dichotomy for compact operators on
infinite-dimensional spaces:

* Every level sphere `{u : ℓ^p(ℕ, 𝕜) | ‖J u‖ = r}` is sequentially closed in the weak topology
  (`lp.isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq`), because weakly convergent
  sequences are norm-bounded and `J` is weak-to-norm continuous on bounded sets.
* For every `0 ≤ r`, `0` belongs to the weak closure of `{u : ℓ^p(ℕ, 𝕜) | ‖J u‖ = r}`
  (`lp.zero_mem_closure_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq`), so for `0 < r` the
  level sphere is not closed in the weak topology
  (`lp.not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq`).
* Although `J` is weak-to-norm continuous on every norm-bounded subset of `ℓ^p(ℕ, 𝕜)`, it is not
  globally continuous from the weak topology to the norm topology
  (`lp.not_continuous_diagonalCLM_invNatSucc_toWeakSpace_symm`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Section 3.3, Example 1 and Remark 3, and Section 6.1.
-/

public section

open scoped lp ENNReal

namespace lp

section HarmonicDiagonalCounterexample

variable (𝕜 : Type*) [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On `ℓ^p(ℕ, 𝕜)` (`1 ≤ p ≤ ∞`), the level sphere `{u | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}` of
the compact harmonic diagonal multiplier `n ↦ (n + 1)⁻¹` is sequentially closed in the weak
topology. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq (r : ℝ) :
    IsSeqClosed
      (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ''
        {u : ℓ^p(ℕ, 𝕜) | ‖diagonalCLM (p := p) (invNatSucc 𝕜) u‖ = r}) :=
  (isCompactOperator_diagonalCLM_invNatSucc 𝕜 (p := p)).isSeqClosed_toWeakSpace_setOf_norm_eq r

/-- On `ℓ^p(ℕ, 𝕜)` (`1 ≤ p ≤ ∞`), `0` belongs to the weak closure of
`{u | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}` for every `0 ≤ r`. For `0 < r`, this witnesses the
failure of weak topological closedness on unbounded sets (at `r = 0` the set is `{0}`, which is
bounded and weakly closed). -/
theorem zero_mem_closure_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq {r : ℝ} (hr : 0 ≤ r) :
    (0 : WeakSpace 𝕜 ℓ^p(ℕ, 𝕜)) ∈
      closure (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ''
        {u : ℓ^p(ℕ, 𝕜) | ‖diagonalCLM (p := p) (invNatSucc 𝕜) u‖ = r}) :=
  (diagonalCLM (p := p) (invNatSucc 𝕜)).zero_mem_closure_toWeakSpace_setOf_norm_eq
    (by simp [Nat.cast_add_one_ne_zero, Set.infinite_univ]) hr

/-- On `ℓ^p(ℕ, 𝕜)` (`1 ≤ p ≤ ∞`) for `0 < r`, the level sphere
`{u | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}` is not closed in the weak topology. Together with
`lp.isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq`, this shows that sequential weak
closedness does not imply weak closedness for compact constraints. -/
theorem not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed
        (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ''
          {u : ℓ^p(ℕ, 𝕜) | ‖diagonalCLM (p := p) (invNatSucc 𝕜) u‖ = r}) :=
  (diagonalCLM (p := p) (invNatSucc 𝕜)).not_isClosed_toWeakSpace_setOf_norm_eq
    (by simp [Nat.cast_add_one_ne_zero, Set.infinite_univ]) hr

/-- **Compact operators need not be globally weak-to-norm continuous.** On `ℓ^p(ℕ, 𝕜)`
(`1 ≤ p ≤ ∞`), the compact harmonic diagonal operator `diagonalCLM (invNatSucc 𝕜)` is weak-to-norm
continuous on every bounded set (`IsCompactOperator.continuousOn_toWeakSpace_symm`) but is not
globally continuous from the weak topology to the norm topology. -/
theorem not_continuous_diagonalCLM_invNatSucc_toWeakSpace_symm :
    ¬ Continuous (fun w : WeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ↦
        diagonalCLM (p := p) (invNatSucc 𝕜) ((toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜)).symm w)) :=
  (diagonalCLM (p := p) (invNatSucc 𝕜)).not_continuous_toWeakSpace_symm
    (by simp [Nat.cast_add_one_ne_zero, Set.infinite_univ])

end HarmonicDiagonalCounterexample

end lp
