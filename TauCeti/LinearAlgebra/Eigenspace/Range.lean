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

Let `f` be an endomorphism of a vector space and `μ ≠ 0`. A generalized eigenvector `w` for `μ`
satisfies `μ • w = f w - (f - μ) w`, so by induction on the exponent it lies in every submodule
containing the range of `f`. Thus the generalized eigenspaces of `f` for nonzero eigenvalues only
see the range of `f`, and `f` has the same nonzero eigenvalues as its restriction to any such
submodule. More precisely, over any commutative ring, for a unit `μ` every power of `f` maps each
generalized eigenspace for `μ` onto itself, since `(X - μ) ^ n` and `X ^ k` are coprime.

## Main results

* `Module.End.surjOn_pow_genEigenspace_of_isUnit`: for a unit `μ`, every power of `f` maps each
  generalized eigenspace of `f` for `μ` onto itself.
* `Module.End.genEigenspace_le_of_range_le`: for `μ ≠ 0`, every generalized eigenspace of `f` for
  `μ` lies in every submodule containing the range of `f`.
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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For `μ ≠ 0`, the generalized eigenvectors for `μ` of an endomorphism `f` lie in every submodule
containing the range of `f`. -/
theorem genEigenspace_le_of_range_le {f : End K V} {S : Submodule K V}
    (hf : LinearMap.range f ≤ S) {μ : K} (hμ : μ ≠ 0) (k : ℕ∞) : f.genEigenspace μ k ≤ S :=
  fun w hw ↦ by
  obtain ⟨l, -, hl⟩ := mem_genEigenspace.1 hw
  suffices h : ∀ (l : ℕ) (w : V), ((f - μ • 1) ^ l) w ∈ S → w ∈ S from
    h l w ((LinearMap.mem_ker.1 hl).symm ▸ S.zero_mem)
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    intro w hw
    rw [pow_succ, mul_apply_eq_comp] at hw
    have h := S.sub_mem (hf (LinearMap.mem_range_self f w)) (ih _ hw)
    rw [LinearMap.sub_apply, sub_sub_cancel, LinearMap.smul_apply, one_apply_eq_self] at h
    exact (S.smul_mem_iff hμ).1 h

/-- The restriction of an endomorphism `f` to a submodule containing its range has the same nonzero
eigenvalues as `f`. -/
theorem hasEigenvalue_restrict_iff_of_range_le {f : End K V} {S : Submodule K V}
    (hf : LinearMap.range f ≤ S) {μ : K} (hμ : μ ≠ 0) :
    HasEigenvalue (f.restrict fun w _ ↦ hf (LinearMap.mem_range_self f w)) μ ↔
      f.HasEigenvalue μ := by
  rw [hasEigenvalue_iff, hasEigenvalue_iff,
    ← (Submodule.map_injective_of_injective S.injective_subtype).ne_iff, Submodule.map_bot,
    ← Submodule.inf_genEigenspace,
    inf_eq_right.2 (genEigenspace_le_of_range_le hf hμ 1)]

end Module.End
