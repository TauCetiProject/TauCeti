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
necessary: when `i = 0` or `n ≤ i`, one of the alternating maps is the identity. In particular
this identifies the minimal free resolution of each nonprojective indecomposable over
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
multipliers belong to the Jacobson radical of that ring. Exactness is not needed. -/
@[simp] theorem isMinimal_cyclicModuleResolutionComplex_iff {A : Type u} [CommRing A] {a b : A}
    (hab : a * b = 0) (hba : b * a = 0) :
    (cyclicModuleResolutionComplex a b hab hba).IsMinimal ↔
      a ∈ Ring.jacobson A ∧ b ∈ Ring.jacobson A := by
  have op_mem (x : A) : op x ∈ Ring.jacobson Aᵐᵒᵖ ↔ x ∈ Ring.jacobson A := by
    let e := RingEquiv.toOpposite A
    change x ∈ Ideal.comap e.toRingHom (Ring.jacobson Aᵐᵒᵖ) ↔ _
    rw [← Ideal.jacobson_bot, Ideal.comap_jacobson_of_surjective e.surjective,
      Ideal.comap_bot_of_injective e.toRingHom e.injective, Ideal.jacobson_bot]
  rw [ChainComplex.isMinimal_iff_range_d_succ_le]
  simp only [cyclicModuleResolutionComplex_d]
  -- The differential lemma retains the complex's spelling of its terms. Expose the regular
  -- modules so that the range and ideal-product lemmas match at their declared types.
  change (∀ j, LinearMap.range (LinearMap.toSpanSingleton Aᵐᵒᵖ Aᵐᵒᵖ
      (op (if Even j then a else b))) ≤ (Ring.jacobson Aᵐᵒᵖ • (⊤ : Ideal Aᵐᵒᵖ))) ↔ _
  simp only [LinearMap.range_toSpanSingleton, Ideal.smul_eq_mul, Ideal.mul_top,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, op_mem]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · simpa using h 0
  · simpa using h 1
  · rintro ⟨ha, hb⟩ j
    split_ifs
    · exact ha
    · exact hb

/-- For `0 < i < n`, the alternating free resolution of `A/(x ^ i)` over
`A = R[X]/(X ^ n)` is minimal. This holds over every commutative coefficient ring. -/
theorem isMinimal_cyclicModuleRootPowProjectiveResolution_complex
    (R : Type u) [CommRing R] {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    (cyclicModuleRootPowProjectiveResolution R n i).complex.IsMinimal := by
  rw [cyclicModuleRootPowProjectiveResolution_complex,
    cyclicModuleProjectiveResolution_complex, isMinimal_cyclicModuleResolutionComplex_iff]
  have hx := isNilpotent_root_X_pow (R := R) n
  exact ⟨nilradical_le_jacobson _ (mem_nilradical.mpr (hx.pow_of_pos hi.ne')),
    nilradical_le_jacobson _ (mem_nilradical.mpr (hx.pow_of_pos (Nat.sub_pos_of_lt hin).ne'))⟩

/-- Over a nontrivial coefficient ring and for positive `n`, the alternating resolution of
`A/(x ^ i)` is minimal exactly when `0 < i < n`. The alternating complex remains a projective
resolution for indices outside this range. -/
theorem isMinimal_cyclicModuleRootPowProjectiveResolution_complex_iff
    (R : Type u) [CommRing R] [Nontrivial R] {n i : ℕ} (hn : 0 < n) :
    (cyclicModuleRootPowProjectiveResolution R n i).complex.IsMinimal ↔ 0 < i ∧ i < n := by
  refine ⟨?_, fun ⟨hi, hin⟩ ↦ isMinimal_cyclicModuleRootPowProjectiveResolution_complex R hi hin⟩
  have : Nontrivial (AdjoinRoot (X ^ n : R[X])) :=
    (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow n)).mpr (by simpa)
  rw [cyclicModuleRootPowProjectiveResolution_complex,
    cyclicModuleProjectiveResolution_complex, isMinimal_cyclicModuleResolutionComplex_iff]
  rintro ⟨ha, hb⟩
  have hnot := (Ideal.ne_top_iff_one _).mp (Ring.jacobson_lt_top (AdjoinRoot (X ^ n : R[X]))).ne
  constructor
  · by_contra hi
    have : i = 0 := by omega
    exact hnot (by simpa [this] using ha)
  · by_contra hi
    have : n - i = 0 := by omega
    exact hnot (by simpa [this] using hb)

end TauCeti
