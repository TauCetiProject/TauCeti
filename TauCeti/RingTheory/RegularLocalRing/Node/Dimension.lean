/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import TauCeti.RingTheory.Node.Localization
public import TauCeti.RingTheory.KrullDimension.Polynomial

/-!
# Dimension and embedding dimension at a thick node

Over a discrete valuation ring, the local ring of `xy = πⁿ` at the closed origin has
Krull dimension two. For `n ≥ 2` its maximal ideal needs exactly three generators:
the equation belongs to the square of the ambient maximal ideal and therefore imposes
no linear relation on the cotangent space. These calculations explain the failure of
regularity at thick nodes in models of curves.

More generally, over a Noetherian local domain the Krull dimension is `dim R + 1`, and
over a regular local base the maximal ideal needs `dim R + 2` generators when `n ≥ 2`.
The local ring is taken at the image of `(𝔪_R, x, y)`. These calculations only need `π`
in the maximal ideal, not that it generate it.

## References

* The Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial

variable {R : Type*} [CommRing R] {π : R}

section IsDomain

variable [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

/-- Over a Noetherian local domain, the local ring of the nodal equation at the image of
the base maximal ideal and the two coordinates has dimension one more than the base.
The primality hypothesis excludes the absent point when `n = 0`. -/
theorem ringKrullDim_localization_quotient_X_mul_X_sub_C_pow (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] :
    ringKrullDim (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)).toRingHom)) = ringKrullDim R + 1 := by
  let B := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R))
  let f := algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))
  have hn : n ≠ 0 := (isPrime_map_quotient_X_mul_X_sub_C_pow_iff hπ n).mp inferInstance
  have hfm : f ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B
      ((maximalIdeal R).comap constantCoeff) _).mpr (by simpa [hn] using hπ)
  have hf : f ≠ 0 := by
    intro hz
    have h : X 0 * X 1 - C (π ^ n) = (0 : MvPolynomial (Fin 2) R) :=
      IsLocalization.injective B
        (primeCompl_le_nonZeroDivisors ((maximalIdeal R).comap constantCoeff))
        (by simpa only [f, map_zero] using hz)
    have := congrArg (fun p : MvPolynomial (Fin 2) R ↦
      p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) h
    simp only [coeff_sub, coeff_X_mul, coeff_X, coeff_C] at this
    norm_num [eq_comm, Finsupp.add_eq_zero_iff] at this
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf) hfm
  have hquot : ringKrullDim (B ⧸ span {f}) = ringKrullDim R + 1 := by
    apply ENat.WithBot.add_one_cancel.mp
    convert hdrop using 1
    norm_num [B, ringKrullDim_localization_comap_constantCoeff, add_assoc]
  rw [ringKrullDim_eq_of_ringEquiv (S := B ⧸ span {f}) (localizationQuotientXMulXSubCPowEquiv hπ n)]
  exact hquot

end IsDomain

section IsRegularRing

variable [IsLocalRing R] [IsRegularRing R]

/-- Over a regular local base, the maximal ideal at the closed point of a node of
thickness at least two needs `dim R + 2` generators, since the equation has no linear term. -/
theorem spanFinrank_maximalIdeal_localization_quotient_X_mul_X_sub_C_pow
    (hπ : π ∈ maximalIdeal R) (n : ℕ)
    (hn : 2 ≤ n)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] :
    (maximalIdeal (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)).toRingHom))).spanFinrank =
      ringKrullDim R + 2 := by
  let B := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R))
  let f := algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))
  let A := Localization.AtPrime
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom)
  let e : A ≃+* (B ⧸ span {f}) := localizationQuotientXMulXSubCPowEquiv hπ n
  have : IsLocalRing (B ⧸ span {f}) := e.isLocalRing
  have hX (i : Fin 2) : algebraMap (MvPolynomial (Fin 2) R) B (X i) ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B
      ((maximalIdeal R).comap constantCoeff) _).mpr (by simp)
  have hC : algebraMap (MvPolynomial (Fin 2) R) B (C π) ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B
      ((maximalIdeal R).comap constantCoeff) _).mpr (by simpa using hπ)
  have hf : f ∈ maximalIdeal B ^ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [f, map_sub, map_mul, map_pow, pow_add, pow_two]
    exact sub_mem (mul_mem_mul (hX 0) (hX 1))
      (mul_mem_right _ _ (mul_mem_mul hC hC))
  have hspan := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
    (maximalIdeal B).fg_of_isNoetherianRing ((span_singleton_le_iff_mem _).mpr hf)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hspan
  have : IsRegularLocalRing B :=
    _root_.IsRegularLocalRing.of_isRegularRing_of_isLocalRing B
  have hB : ((maximalIdeal B).spanFinrank : WithBot ℕ∞) = ringKrullDim R + 2 := by
    simpa [B, ringKrullDim_localization_comap_constantCoeff] using
      _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)
  have hmap := map_ringEquiv_maximalIdeal (R := A) (S := B ⧸ span {f}) e
  have he := Ideal.spanFinrank_map_eq_of_ringEquiv e (maximalIdeal A)
  rw [hmap] at he
  rw [← hB]
  exact_mod_cast he.symm.trans hspan

end IsRegularRing

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- The local ring of a nodal equation over a DVR at the image of the maximal ideal
and both coordinates has Krull dimension two. -/
theorem ringKrullDim_localization_quotient_X_mul_X_sub_C_pow_of_isDiscreteValuationRing
    (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] :
    ringKrullDim (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)).toRingHom)) = 2 := by
  rw [ringKrullDim_localization_quotient_X_mul_X_sub_C_pow hπ n,
    IsDiscreteValuationRing.ringKrullDim_eq_one]
  norm_num

/-- Over a DVR, the maximal ideal at the closed point of a node of thickness at least two
needs exactly three generators. -/
theorem spanFinrank_maximalIdeal_localization_quotient_X_mul_X_sub_C_pow_of_isDiscreteValuationRing
    (hπ : π ∈ maximalIdeal R) (n : ℕ) (hn : 2 ≤ n)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] :
    (maximalIdeal (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)).toRingHom))).spanFinrank = 3 := by
  have h := spanFinrank_maximalIdeal_localization_quotient_X_mul_X_sub_C_pow hπ n hn
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
  exact_mod_cast h

end IsDiscreteValuationRing

end TauCeti
