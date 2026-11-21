/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
public import TauCeti.Analysis.Normed.Module.WeakSpace.Sphere
public import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Spheres and harmonic diagonal counterexample in the weak topology on `ℓ^p`

For a bounded scalar family `d` on `ι`, the diagonal operator
`lp.diagonalCLM d` on `ℓ^p(ι, 𝕜)` is injective when no coefficient vanishes
(`lp.injective_diagonalCLM_iff`), compact when the coefficients tend to zero
(`lp.isCompactOperator_diagonalCLM`), and has infinite-dimensional range when infinitely many
coefficients are nonzero (`lp.finiteDimensional_range_diagonalCLM_iff`). For such an operator the
sphere `{u | ‖lp.diagonalCLM d u‖ = r}` of positive radius is weakly sequentially closed
(`lp.isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_eq`) but not weakly closed
(`lp.not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq`).

In particular, on `ℓ^p(ℕ, 𝕜)` (`1 ≤ p ≤ ∞`) over `ℝ` or `ℂ`, the harmonic diagonal multiplier
`J = lp.diagonalCLM (p := p) (lp.invNatSucc 𝕜)` is a compact operator of infinite-dimensional
range. It witnesses the sharp topological-versus-sequential dichotomy for compact operators on
infinite-dimensional spaces (verified in a single example at the end of the file):

* Every level sphere `{u : ℓ^p(ℕ, 𝕜) | ‖J u‖ = r}` is weakly sequentially closed
  (`lp.isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_eq`).
* For every `0 < r`, `0` belongs to the weak closure of `{u : ℓ^p(ℕ, 𝕜) | ‖J u‖ = r}`
  (`TauCeti.zero_mem_closure_toWeakSpace_setOf_norm_eq`), so the level sphere is not weakly
  closed (`lp.not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq`).
* Although `J` is weak-to-norm continuous on every norm-bounded subset of `ℓ^p(ℕ, 𝕜)`
  (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`), `J` is not globally
  continuous from the weak topology to the norm topology
  (`TauCeti.not_continuous_comp_toWeakSpace_symm`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Section 3.3, Example 1 and Remark 3, and Section 6.1.
-/

public section

open Filter Set Topology
open scoped lp ENNReal

namespace lp

section GeneralDiagonal

variable {ι 𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] {d : ℓ^∞(ι, 𝕜)}

/-- When infinitely many coefficients are nonzero, a sphere of positive radius of a diagonal
operator is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq (hd : {i | d i ≠ 0}.Infinite)
    {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u | ‖diagonalCLM d u‖ = r}) :=
  TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq (j := diagonalCLM (p := p) d)
    ((finiteDimensional_range_diagonalCLM_iff (p := p) d).not.2 hd) hr

/-- If the coefficients tend to zero, every sphere of a diagonal operator is weakly sequentially
closed. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_eq
    (hd : Tendsto (fun i ↦ ‖d i‖) cofinite (𝓝 0)) (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u | ‖diagonalCLM d u‖ = r}) :=
  (isCompactOperator_diagonalCLM d hd).isSeqClosed_toWeakSpace_setOf_norm_eq r

end GeneralDiagonal

section HarmonicDiagonalCounterexample

-- Concrete harmonic diagonal counterexample on `ℓ^p(ℕ, 𝕜)` (`1 ≤ p ≤ ∞`) for `r > 0`:
-- `J = diagonalCLM (invNatSucc 𝕜)` is compact and has infinite-dimensional range, so its level
-- sphere `{u | ‖J u‖ = r}` is weakly sequentially closed yet contains `0` in its weak closure and
-- is not weakly closed, and `J` is not globally weak-to-norm continuous.
example (𝕜 : Type*) [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ} (hr : 0 < r) :
    let J := diagonalCLM (p := p) (invNatSucc 𝕜)
    IsCompactOperator J ∧
      IsSeqClosed (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) '' {u | ‖J u‖ = r}) ∧
      (0 : WeakSpace 𝕜 ℓ^p(ℕ, 𝕜)) ∈ closure (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) '' {u | ‖J u‖ = r}) ∧
      ¬ IsClosed (toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜) '' {u | ‖J u‖ = r}) ∧
      ¬ Continuous fun w : WeakSpace 𝕜 ℓ^p(ℕ, 𝕜) ↦ J ((toWeakSpace 𝕜 ℓ^p(ℕ, 𝕜)).symm w) := by
  intro J
  have hJ_inf :
      ¬ FiniteDimensional 𝕜 (LinearMap.range (J : ℓ^p(ℕ, 𝕜) →ₗ[𝕜] ℓ^p(ℕ, 𝕜))) := by
    rw [finiteDimensional_range_diagonalCLM_iff,
      show {i | invNatSucc 𝕜 i ≠ 0} = Set.univ from Set.eq_univ_iff_forall.2
        ((injective_diagonalCLM_iff _).mp (injective_diagonalCLM_invNatSucc (p := p) 𝕜))]
    exact Set.infinite_univ
  refine ⟨isCompactOperator_diagonalCLM_invNatSucc 𝕜,
    (isCompactOperator_diagonalCLM_invNatSucc 𝕜).isSeqClosed_toWeakSpace_setOf_norm_eq r,
    TauCeti.zero_mem_closure_toWeakSpace_setOf_norm_eq hJ_inf hr.le,
    TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq hJ_inf hr,
    TauCeti.not_continuous_comp_toWeakSpace_symm hJ_inf⟩

end HarmonicDiagonalCounterexample

end lp
