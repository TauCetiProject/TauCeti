/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.CyclicResolution.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Minimal
public import TauCeti.RingTheory.Polynomial.Truncated.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Minimal cyclic resolutions

The alternating rank-one resolution attached to an exact pair of zero-divisors `a, b` in a
commutative ring is minimal exactly when both elements belong to the Jacobson radical.

For `A = R[X]/(X ^ n)`, the class `x` of `X` is nilpotent. Consequently the resolution of
`A/(x ^ i)` alternating multiplication by `x ^ i` and `x ^ (n - i)` is minimal when
`0 < i < n`. For a nontrivial coefficient ring and positive `n`, these inequalities are also
necessary: at either endpoint one of the differentials is the identity. In particular this
identifies the minimal free resolution of each nonprojective indecomposable over
`k[X]/(X ^ n)`, over a field of arbitrary characteristic.

Minimality here is the Jacobson-radical criterion for complexes; no locality or Noetherianity
is needed. Over a local coefficient ring it is the usual maximal-ideal criterion.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 20,
  for minimal free resolutions.
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5, for the alternating
  hypersurface resolution.
-/

public section

open CategoryTheory MulOpposite Polynomial

namespace TauCeti

universe u

/-- An alternating rank-one complex in a commutative ring is minimal exactly when both
multipliers belong to the Jacobson radical of the scalar ring for right modules.
Exactness is not needed for this criterion. -/
@[simp] theorem isMinimal_cyclicModuleResolutionComplex_iff {A : Type u} [CommRing A] {a b : A}
    (hab : a * b = 0) (hba : b * a = 0) :
    (cyclicModuleResolutionComplex a b hab hba).IsMinimal ↔
      op a ∈ Ring.jacobson Aᵐᵒᵖ ∧ op b ∈ Ring.jacobson Aᵐᵒᵖ := by
  rw [ChainComplex.isMinimal_iff_range_d_succ_le]
  simp only [cyclicModuleResolutionComplex_d]
  -- The differential lemma retains the complex's spelling of its terms. Expose the regular
  -- modules so that the range and ideal-product lemmas match at their declared types.
  change (∀ j, LinearMap.range (LinearMap.toSpanSingleton Aᵐᵒᵖ Aᵐᵒᵖ
      (op (if Even j then a else b))) ≤ (Ring.jacobson Aᵐᵒᵖ • (⊤ : Ideal Aᵐᵒᵖ))) ↔ _
  simp only [LinearMap.range_toSpanSingleton, Ideal.smul_eq_mul, Ideal.mul_top,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h j ↦ ?_⟩
  · simpa using h 0
  · simpa using h 1
  · split_ifs <;> tauto

/-- For `0 < i < n`, the alternating free resolution of `A/(x ^ i)` over
`A = R[X]/(X ^ n)` is minimal. This holds over every commutative coefficient ring. -/
theorem isMinimal_cyclicModuleRootPowProjectiveResolution
    (R : Type u) [CommRing R] {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    (cyclicModuleRootPowProjectiveResolution R n i).complex.IsMinimal := by
  rw [cyclicModuleRootPowProjectiveResolution_complex,
    cyclicModuleProjectiveResolution_complex, isMinimal_cyclicModuleResolutionComplex_iff]
  have hx := (isNilpotent_root_X_pow (R := R) n).map (RingEquiv.toOpposite _)
  exact ⟨nilradical_le_jacobson _ (mem_nilradical.mpr (by
      simpa using hx.pow_of_pos hi.ne')),
    nilradical_le_jacobson _ (mem_nilradical.mpr (by
      simpa using hx.pow_of_pos (Nat.sub_pos_of_lt hin).ne'))⟩

/-- Over a nontrivial coefficient ring and for positive `n`, the alternating resolution of
`A/(x ^ i)` is minimal exactly when `0 < i < n`. Thus neither endpoint gives a minimal
resolution, although the alternating complex remains a projective resolution. -/
theorem isMinimal_cyclicModuleRootPowProjectiveResolution_iff
    (R : Type u) [CommRing R] [Nontrivial R] {n i : ℕ} (hn : 0 < n) :
    (cyclicModuleRootPowProjectiveResolution R n i).complex.IsMinimal ↔ 0 < i ∧ i < n := by
  refine ⟨fun h ↦ ?_, fun h ↦ isMinimal_cyclicModuleRootPowProjectiveResolution R h.1 h.2⟩
  have : Nontrivial (AdjoinRoot (X ^ n : R[X])) :=
    (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow n)).2 (by simpa)
  rw [cyclicModuleRootPowProjectiveResolution_complex,
    cyclicModuleProjectiveResolution_complex, isMinimal_cyclicModuleResolutionComplex_iff] at h
  have hnot : (1 : (AdjoinRoot (X ^ n : R[X]))ᵐᵒᵖ) ∉
      Ring.jacobson (AdjoinRoot (X ^ n : R[X]))ᵐᵒᵖ := by
    intro h1
    have := (Ring.mem_jacobson_iff.mp h1) (-1)
    simp at this
  constructor
  · by_contra hi
    have : i = 0 := by omega
    exact hnot (by simpa [this] using h.1)
  · by_contra hi
    have : n - i = 0 := by omega
    exact hnot (by simpa [this] using h.2)

end TauCeti
