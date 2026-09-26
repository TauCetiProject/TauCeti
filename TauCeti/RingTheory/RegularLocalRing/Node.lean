/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.RingTheory.LocalRing.Polynomial
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Regularity of the local model `xy = πⁿ` of a node

Let `R` be a regular local ring with maximal ideal `𝔪_R`, for instance a discrete valuation ring,
and let `π ∈ 𝔪_R \ 𝔪_R²`, for instance a uniformizer. The ring `R[x, y] ⧸ (xy - πⁿ)` is the local
model of a node in a family of curves over `R`: its special fibre `xy = 0` is the union of two
lines meeting transversally at the origin, while for `n ≥ 1` its generic fibre over a discrete
valuation ring is smooth. This file determines when its total space is regular at the singular
point `(𝔪_R, x, y)` of the special fibre: exactly when `n = 1`.

Write `P = R[x, y]` and `𝔪 = (𝔪_R, x, y)`, the ideal of polynomials whose constant coefficient
lies in `𝔪_R`. The localization `P_𝔪` is a regular local ring, and the local ring in question is
`P_𝔪 ⧸ (xy - πⁿ)`. For `n ≥ 1` the equation lies in `𝔪`, and a quotient of a regular local ring
by a nonzero element of its maximal ideal is regular exactly when the element does not lie in the
square of the maximal ideal (`TauCeti.IsRegularLocalRing.quotient_span_singleton_iff`). For
`n ≥ 2` the equation lies in `𝔪²`, so the quotient is not regular. For `n = 1` its constant
coefficient `-π` does not lie in `𝔪_R²`, so the quotient is regular. For `n = 0`
the point `(𝔪_R, x, y)` does not lie on the model at all, since `xy = 1` there.

This is the regularity statement behind the resolution of the singularities of a nodal model of a
curve over a discrete valuation ring by repeated blowups, each of which replaces `n` by `n - 2`,
until the thickness of every node is at most one.

## Main results

* `TauCeti.isRegularLocalRing_quotient_X_mul_X_sub_C_pow_iff`: the ring
  `R[x, y]_𝔪 ⧸ (xy - πⁿ)` is a regular local ring exactly when `n = 1`.
* `TauCeti.isPrime_map_quotient_X_mul_X_sub_C_pow_iff`: the image of `𝔪` in
  `R[x, y] ⧸ (xy - πⁿ)` is a prime ideal exactly when `n ≠ 0`.
* `TauCeti.isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff`: the local ring of
  `R[x, y] ⧸ (xy - πⁿ)` at the image of `𝔪` is regular exactly when `n = 1`.
* `TauCeti.isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff_of_irreducible`: the
  same statement for a uniformizer `π` of a discrete valuation ring.

## Implementation notes

The base ring `R` is assumed to be a local ring satisfying `IsRegularRing`. This gives regularity
of `R[x, y]` via `MvPolynomial.isRegularRing_of_isRegularRing`, and hence of its localization
`R[x, y]_𝔪`. Discrete valuation rings satisfy this hypothesis through the Dedekind-domain
instance. The point `(𝔪_R, x, y)` is written as the preimage of `𝔪_R` under the constant
coefficient, so that it is visibly a prime ideal of `R[x, y]`.

## References

* [The Stacks Project, Example 55.14.1](https://stacks.math.columbia.edu/tag/0CDC)
-/

public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial

section IsRegularRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable [IsRegularRing R] {π : R}

/-- **The local model `xy = πⁿ` of a node is regular at the origin exactly when `n = 1`.**
For `π ∈ 𝔪_R \ 𝔪_R²` in a regular local ring `R` and `𝔪 = (𝔪_R, x, y)`, the ring
`R[x, y]_𝔪 ⧸ (xy - πⁿ)` is a regular local ring exactly when `n = 1`. For `n = 0` it is the zero
ring. -/
theorem isRegularLocalRing_quotient_X_mul_X_sub_C_pow_iff (hπ : π ∈ maximalIdeal R)
    (hπ2 : π ∉ maximalIdeal R ^ 2) (n : ℕ) :
    IsRegularLocalRing (Localization.AtPrime ((maximalIdeal R).comap (constantCoeff (σ := Fin 2))) ⧸
      span {(algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap (constantCoeff (σ := Fin 2))))
        (X 0 * X 1 - C π ^ n))}) ↔ n = 1 := by
  have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  set 𝔪 := (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)
  set B := Localization.AtPrime 𝔪
  set ι := algebraMap (MvPolynomial (Fin 2) R) B
  have hmem (p : MvPolynomial (Fin 2) R) (hp : constantCoeff p ∈ maximalIdeal R) :
      ι p ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B 𝔪 p).mpr hp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `xy - 1` is a unit of `B`, so the quotient is the zero ring
    have hu : IsUnit (ι (X 0 * X 1 - C π ^ 0)) :=
      IsLocalization.map_units B (⟨_, by simp [𝔪]⟩ : 𝔪.primeCompl)
    simp only [zero_ne_one, iff_false]
    intro h
    exact Ideal.Quotient.nontrivial_iff.mp inferInstance (span_singleton_eq_top.mpr hu)
  have hC : ι (C π) ∈ maximalIdeal B := hmem _ (by simpa using hπ)
  have hX (i : Fin 2) : ι (X i) ∈ maximalIdeal B := hmem _ (by simp)
  have hfm : ι (X 0 * X 1 - C π ^ n) ∈ maximalIdeal B := by
    rw [map_sub, map_mul, map_pow]
    exact sub_mem (mul_mem_right _ _ (hX 0)) (pow_mem_of_mem _ hC n hn)
  have hf0 : ι (X 0 * X 1 - C π ^ n) ≠ 0 := by
    rw [Ne, IsLocalization.to_map_eq_zero_iff B (primeCompl_le_nonZeroDivisors 𝔪)]
    intro h
    have h' := congrArg constantCoeff h
    simp only [map_sub, map_mul, constantCoeff_X, map_pow, constantCoeff_C, zero_mul, zero_sub,
      neg_eq_zero, map_zero] at h'
    exact hπ2 (pow_eq_zero_iff hn.ne' |>.mp h' ▸ zero_mem _)
  rw [TauCeti.IsRegularLocalRing.quotient_span_singleton_iff hfm hf0]
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- for `n ≥ 2` both `xy` and `πⁿ` lie in the square of the maximal ideal
    by_contra hn1
    refine h ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [map_sub, map_mul, map_pow, pow_add, pow_two]
    exact sub_mem (mul_mem_mul (hX 0) (hX 1))
      (mul_mem_left _ _ (by rw [pow_two]; exact mul_mem_mul hC hC))
  · -- for `n = 1` the constant coefficient `-π` of the equation does not lie in `𝔪_R²`
    rintro rfl
    exact algebraMap_notMem_maximalIdeal_sq (by simpa using hπ2)

omit [IsRegularRing R] in
/-- The image of `𝔪 = (𝔪_R, x, y)` in `R[x, y] ⧸ (xy - πⁿ)` is a prime ideal exactly when
`n ≠ 0`, that is, exactly when the origin of the special fibre lies on the model. -/
theorem isPrime_map_quotient_X_mul_X_sub_C_pow_iff (hπ : π ∈ maximalIdeal R) (n : ℕ) :
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (Ideal.Quotient.mk (span {X 0 * X 1 - C π ^ n}))).IsPrime ↔ n ≠ 0 := by
  refine ⟨?_, fun hn ↦ map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_⟩
  · -- for `n = 0` the image of `x` is a unit
    rintro h rfl
    have hX0 : X (0 : Fin 2) ∈
        (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R) := by simp
    refine h.ne_top (eq_top_of_isUnit_mem _ (mem_map_of_mem _ hX0)
      (IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (X 1)) ?_))
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    simp
  · rw [mk_ker, span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_comap]
    simpa [hn] using hπ

/-- **The local ring of `R[x, y] ⧸ (xy - πⁿ)` at the origin of its special fibre is regular exactly
when `n = 1`.** Here `π ∈ 𝔪_R \ 𝔪_R²` for a regular local ring `R`, and the origin is the image of
`𝔪 = (𝔪_R, x, y)`, which is a prime ideal exactly when `n ≠ 0`
(`TauCeti.isPrime_map_quotient_X_mul_X_sub_C_pow_iff`). -/
theorem isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff (hπ : π ∈ maximalIdeal R)
    (hπ2 : π ∉ maximalIdeal R ^ 2) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (Ideal.Quotient.mk (span {X 0 * X 1 - C π ^ n}))).IsPrime] :
    IsRegularLocalRing (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (Ideal.Quotient.mk (span {X 0 * X 1 - C π ^ n})))) ↔ n = 1 := by
  set 𝔪 := (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)
  set f : MvPolynomial (Fin 2) R := X 0 * X 1 - C π ^ n
  set q := Ideal.Quotient.mk (span {f})
  set B := Localization.AtPrime 𝔪
  set J := span {algebraMap (MvPolynomial (Fin 2) R) B f}
  -- `B ⧸ (f)` is the localization of `R[x, y] ⧸ (f)` at the image of `𝔪`
  have hfJ : span {f} ≤ J.comap (algebraMap (MvPolynomial (Fin 2) R) B) := by
    rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_comap]
    exact mem_span_singleton_self _
  let : Algebra (MvPolynomial (Fin 2) R ⧸ span {f}) (B ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hfJ
  have hloc := IsLocalization.of_surjective (S := B) (S' := B ⧸ J) 𝔪.primeCompl q
      Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (RingHom.ext fun _ ↦ rfl)
      (by rw [mk_ker, mk_ker, Ideal.map_span, Set.image_singleton])
  have hcomap : (𝔪.map q).comap q = 𝔪 := by
    rw [comap_map_of_surjective' q Ideal.Quotient.mk_surjective, mk_ker, sup_eq_left,
      span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have hn : n ≠ 0 := (isPrime_map_quotient_X_mul_X_sub_C_pow_iff hπ n).mp inferInstance
    simpa [𝔪, f, hn] using hπ
  have hsub : 𝔪.primeCompl.map q = (𝔪.map q).primeCompl := by
    ext a
    refine ⟨?_, fun ha ↦ ?_⟩
    · rintro ⟨p, hp, rfl⟩
      rw [mem_primeCompl_iff, ← mem_comap, hcomap]
      exact hp
    · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [mem_primeCompl_iff, ← mem_comap, hcomap] at ha
      exact ⟨p, ha, rfl⟩
  rw [hsub] at hloc
  let e := IsLocalization.algEquiv (𝔪.map q).primeCompl (Localization.AtPrime (𝔪.map q)) (B ⧸ J)
  rw [← isRegularLocalRing_quotient_X_mul_X_sub_C_pow_iff hπ hπ2 n]
  exact ⟨fun _ ↦ .of_ringEquiv (R := Localization.AtPrime (𝔪.map q)) e.toRingEquiv,
    fun _ ↦ .of_ringEquiv (R := B ⧸ J) e.symm.toRingEquiv⟩

end IsRegularRing

section IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

/-- **The local model `xy = πⁿ` of a node over a discrete valuation ring is regular at the origin
exactly when `n = 1`.** For a uniformizer `π` of a discrete valuation ring `R`, the local ring of
`R[x, y] ⧸ (xy - πⁿ)` at the image of `(π, x, y)` is regular exactly when `n = 1`. -/
theorem isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff_of_irreducible
    (hπ : Irreducible π) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (Ideal.Quotient.mk (span {X 0 * X 1 - C π ^ n}))).IsPrime] :
    IsRegularLocalRing (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (Ideal.Quotient.mk (span {X 0 * X 1 - C π ^ n})))) ↔ n = 1 := by
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  refine isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff
    (hm ▸ mem_span_singleton_self π) (fun h ↦ hπ.not_isUnit ?_) n
  rw [hm, span_singleton_pow, mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact IsUnit.of_mul_eq_one c
    (mul_left_cancel₀ hπ.ne_zero (by rw [← mul_assoc, ← pow_two, ← hc, mul_one]))

end IsDiscreteValuationRing

end TauCeti
