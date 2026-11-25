/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Generalized eigenspaces for nonzero eigenvalues lie in the range

Let `f` be an endomorphism of a module over a commutative ring and `μ` a unit. Since
`(X - μ) ^ n` and `X ^ k` are coprime, every power of `f` maps each generalized eigenspace of `f`
for `μ` onto itself. In particular every generalized eigenvector for `μ` lies in the range of `f`,
hence in every submodule containing it. Thus the generalized eigenspaces of `f` for unit
eigenvalues only see the range of `f`, and an endomorphism of a vector space has the same nonzero
eigenvalues as its restriction to any submodule containing its range.

## Main results

* `Module.End.surjOn_pow_genEigenspace_of_isUnit`: for a unit `μ`, every power of `f` maps each
  generalized eigenspace of `f` for `μ` onto itself.
* `Module.End.genEigenspace_le_of_range_le`: for a unit `μ`, every generalized eigenspace of `f`
  for `μ` lies in every submodule containing the range of `f`.
* `Module.End.hasEigenvalue_restrict_iff_of_range_le`: the restriction of `f` to a submodule
  containing its range has the same nonzero eigenvalues as `f`.
-/

public section

namespace Module.End

open Polynomial in
/-- For a unit `μ`, every power `f ^ k` maps each generalized eigenspace of `f` for `μ` onto
itself: since `(X - μ) ^ l` and `X ^ k` are coprime, a vector killed by `(f - μ) ^ l` is `f ^ k u`
for some `u` also killed by `(f - μ) ^ l`. -/
theorem surjOn_pow_genEigenspace_of_isUnit {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {f : End R M} {μ : R} (hμ : IsUnit μ) (n : ℕ∞) (k : ℕ) :
    Set.SurjOn ⇑(f ^ k) (f.genEigenspace μ n) (f.genEigenspace μ n) := fun x hx ↦ by
  obtain ⟨l, hl, hx⟩ := mem_genEigenspace.1 hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨a, b, hab⟩ : IsCoprime ((X - C μ) ^ l) (X ^ k) := by
    simpa using (isCoprime_X_sub_C_of_isUnit_sub (a := μ) (b := (0 : R)) (by simpa using hμ)).pow
  have hP : aeval f ((X - C μ) ^ l) = (f - μ • 1) ^ l := by
    simp [Algebra.algebraMap_eq_smul_one]
  refine ⟨aeval f b x, mem_genEigenspace.2 ⟨l, hl, ?_⟩, ?_⟩
  · have hc := LinearMap.congr_fun ((Commute.all ((X - C μ) ^ l) b).map (aeval f)).eq x
    simpa only [LinearMap.mem_ker, map_mul, mul_apply_eq_comp, hP, hx, map_zero] using hc
  · simpa [mul_comm b, mul_apply_eq_comp, hP, hx] using congr(aeval f $hab x)

/-- For a unit `μ`, the generalized eigenvectors for `μ` of an endomorphism `f` lie in every
submodule containing the range of `f`. -/
theorem genEigenspace_le_of_range_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : End R M} {S : Submodule R M} (hf : LinearMap.range f ≤ S) {μ : R} (hμ : IsUnit μ)
    (k : ℕ∞) : f.genEigenspace μ k ≤ S := fun w hw ↦ by
  obtain ⟨u, -, rfl⟩ := surjOn_pow_genEigenspace_of_isUnit hμ k 1 hw
  exact hf (by simp)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The restriction of an endomorphism `f` to a submodule containing its range has the same nonzero
eigenvalues as `f`. -/
theorem hasEigenvalue_restrict_iff_of_range_le {f : End K V} {S : Submodule K V}
    (hf : LinearMap.range f ≤ S) {μ : K} (hμ : μ ≠ 0) :
    HasEigenvalue (f.restrict fun w _ ↦ hf (LinearMap.mem_range_self f w)) μ ↔
      f.HasEigenvalue μ := by
  rw [hasEigenvalue_iff, hasEigenvalue_iff,
    ← (Submodule.map_injective_of_injective S.injective_subtype).ne_iff, Submodule.map_bot,
    ← Submodule.inf_genEigenspace,
    inf_eq_right.2 (genEigenspace_le_of_range_le hf hμ.isUnit 1)]

end Module.End
