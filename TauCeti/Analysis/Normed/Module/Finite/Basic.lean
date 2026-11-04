/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm.OpenMapping

/-!
# Bounds on maps from finite Banach modules

Over a complete ultrametric Tate ring, every linear map from a finite complete normed module
with contractive scalar action to a seminormed module with contractive scalar action is bounded.
The target need not be complete or ultrametric. The ring need not be commutative or noetherian,
and the modules need not be free.

The key input is quantitative finite spanning: a finite generating family admits coefficient
lifts bounded linearly in the norm of the vector. The composite of an arbitrary linear map
with that presentation is continuous on the finite free module, hence bounded over Tate scalars.
Combining these bounds gives `LinearMap.exists_bound_of_module_finite`.

Applied in both directions, this proves bounded equivalence of any two Banach module norms
on a finite module, expressed without choosing new norms by
`LinearEquiv.exists_norm_bounds_of_module_finite`. In particular, no prior compatibility of
the two topologies is required. Zero modules and empty generating families are included.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §3.7.
-/

public section

namespace LinearMap

variable {R M N : Type*} [SeminormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [CompleteSpace M]
  [Module.Finite R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Every linear map from a finite Banach module over a complete ultrametric Tate ring is
bounded. The target is only seminormed and need not be complete or ultrametric. -/
theorem exists_bound_of_module_finite (f : M →ₗ[R] N) :
    ∃ C > 0, ∀ x, ‖f x‖ ≤ C * ‖x‖ := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let q := Fintype.linearCombination R v
  obtain ⟨A, hA, hlift⟩ := TauCeti.exists_linearCombination_eq_and_norm_le v hv
  obtain ⟨B, hB, hbound⟩ := TauCeti.NormedRing.IsTate.bound_of_continuous
    (f.comp q) (f.comp q).continuous_on_pi
  refine ⟨B * A, mul_pos hB hA, fun x ↦ ?_⟩
  obtain ⟨c, hc, hcnorm⟩ := hlift x
  have hqc : q c = x := (Fintype.linearCombination_apply R v c).trans hc
  calc
    ‖f x‖ = ‖(f.comp q) c‖ := by rw [LinearMap.comp_apply, hqc]
    _ ≤ B * ‖c‖ := hbound c
    _ ≤ B * (A * ‖x‖) := mul_le_mul_of_nonneg_left hcnorm hB.le
    _ = (B * A) * ‖x‖ := (mul_assoc _ _ _).symm

end LinearMap

namespace LinearEquiv

variable {R M N : Type*} [SeminormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [CompleteSpace M]
  [Module.Finite R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [CompleteSpace N]

/-- An algebraic equivalence between finite Banach modules is bounded in both directions.
Taking the identity between two normed copies of the same module proves that their norms
are bounded-equivalent, without assuming their topologies agree. -/
theorem exists_norm_bounds_of_module_finite (e : M ≃ₗ[R] N) :
    ∃ C > 0, ∀ x, ‖e x‖ ≤ C * ‖x‖ ∧ ‖x‖ ≤ C * ‖e x‖ := by
  have : Module.Finite R N := Module.Finite.of_surjective e.toLinearMap e.surjective
  obtain ⟨A, hA, hforward⟩ := e.toLinearMap.exists_bound_of_module_finite
  obtain ⟨B, hB, hbackward⟩ := e.symm.toLinearMap.exists_bound_of_module_finite
  refine ⟨max A B, lt_max_of_lt_left hA, fun x ↦ ⟨?_, ?_⟩⟩
  · exact (hforward x).trans (mul_le_mul_of_nonneg_right (le_max_left A B) (norm_nonneg x))
  · have hx : ‖x‖ ≤ B * ‖e x‖ := by simpa using hbackward (e x)
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_right A B) (norm_nonneg (e x)))

end LinearEquiv
