/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Minimal polynomials of split endomorphisms

If the generalized eigenspaces of an endomorphism `f` of a finite-dimensional vector space span,
then `f` is annihilated by a power of the product of the linear factors `X - C μ` over its
eigenvalues `μ`. That product is separable over any field, since its roots are distinct, so this
is the input needed to apply Mathlib's
`Module.End.exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow` without assuming the field
is perfect.

## Main results

* `Module.End.minpoly_dvd_prod_X_sub_C_pow_of_iSup_maxGenEigenspace_eq_top`: the minimal
  polynomial of a split endomorphism divides the `finrank`-th power of the product of
  `X - C μ` over its eigenvalues.
-/

public section

open Module Polynomial

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If the generalized eigenspaces of `f` span, then the minimal polynomial of `f` divides the
`finrank`-th power of the product of `X - C μ` over the eigenvalues `μ` of `f`. -/
theorem minpoly_dvd_prod_X_sub_C_pow_of_iSup_maxGenEigenspace_eq_top {f : End K V}
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    minpoly K f ∣ (∏ μ ∈ (finite_hasEigenvalue f).toFinset, (X - C μ)) ^ finrank K V := by
  classical
  refine minpoly.dvd K _ (LinearMap.ext fun z ↦ ?_)
  have hz : z ∈ ⨆ μ, f.maxGenEigenspace μ := hf ▸ Submodule.mem_top
  induction hz using Submodule.iSup_induction' with
  | mem μ z hz =>
    rw [maxGenEigenspace_eq_genEigenspace_finrank] at hz
    by_cases hμ : f.HasEigenvalue μ
    · obtain ⟨q, hq⟩ := pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun μ ↦ X - C μ)
        ((finite_hasEigenvalue f).mem_toFinset.2 hμ)) (finrank K V)
      have hX : aeval f (X - C μ) = f - μ • 1 := by simp [Algebra.algebraMap_eq_smul_one]
      rw [hq, mul_comm, map_mul, map_pow, hX, mul_apply,
        LinearMap.mem_ker.1 (mem_genEigenspace_nat.1 hz), map_zero, LinearMap.zero_apply]
    · obtain rfl : z = 0 := by
        by_contra h
        exact hμ (hasEigenvalue_of_hasGenEigenvalue ((Submodule.ne_bot_iff _).2 ⟨z, hz, h⟩))
      simp
  | zero => simp
  | add _ _ _ _ h h' => simp only [map_add, h, h', add_zero, LinearMap.zero_apply]

end Module.End
