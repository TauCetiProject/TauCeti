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
# Embedding dimension at a thick node

Over a regular local base `R`, the maximal ideal of the local ring of `xy = πⁿ` at the image
of `(𝔪_R, x, y)` needs `dim R + 2` generators when `n ≥ 2`, and so exactly three generators
over a discrete valuation ring: the equation belongs to the square of the ambient maximal ideal
and therefore imposes no linear relation on the cotangent space. Together with the Krull
dimension computed in `TauCeti.RingTheory.Node.Dimension`, this explains the failure of
regularity at thick nodes in models of curves. These calculations only need `π` in the maximal
ideal, not that it generate it.

## References

* The Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial

variable {R : Type*} [CommRing R] {π : R}

section IsRegularRing

variable [IsLocalRing R] [IsRegularRing R]

/-- Over a regular local base, the maximal ideal at the closed point of a node of
thickness at least two needs `dim R + 2` generators, since the equation has no linear term. -/
theorem spanFinrank_maximalIdeal_localization_quotient_X_mul_X_sub_C_pow
    (n : ℕ) (hn : 2 ≤ n)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    (maximalIdeal (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n))))).spanFinrank =
      ringKrullDim R + 2 := by
  let B := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R))
  let f := algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))
  let A := Localization.AtPrime
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)))
  let e : A ≃+* (B ⧸ span {f}) := localizationQuotientXMulXSubCPowEquiv π n
  have : IsLocalRing (B ⧸ span {f}) := e.isLocalRing
  have hspan := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
    (maximalIdeal B).fg_of_isNoetherianRing
    ((span_singleton_le_iff_mem _).mpr (algebraMap_X_mul_X_sub_C_pow_mem_maximalIdeal_sq
      (mem_maximalIdeal_of_isPrime_map_quotient_X_mul_X_sub_C_pow (π := π) n) hn))
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hspan
  have : IsRegularLocalRing B :=
    _root_.IsRegularLocalRing.of_isRegularRing_of_isLocalRing B
  have hB : ((maximalIdeal B).spanFinrank : WithBot ℕ∞) = ringKrullDim R + 2 := by
    simpa [B, ringKrullDim_localization_comap_mvPolynomial_constantCoeff] using
      _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)
  have hmap := map_ringEquiv_maximalIdeal (R := A) (S := B ⧸ span {f}) e
  have he := Ideal.spanFinrank_map_eq_of_ringEquiv e (maximalIdeal A)
  rw [hmap] at he
  rw [← hB]
  exact_mod_cast he.symm.trans hspan

end IsRegularRing

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- Over a DVR, the maximal ideal at the closed point of a node of thickness at least two
needs exactly three generators. -/
theorem spanFinrank_maximalIdeal_localization_quotient_X_mul_X_sub_C_pow_of_isDiscreteValuationRing
    (n : ℕ) (hn : 2 ≤ n)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    (maximalIdeal (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n))))).spanFinrank = 3 := by
  have h := spanFinrank_maximalIdeal_localization_quotient_X_mul_X_sub_C_pow (π := π) n hn
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
  exact_mod_cast h

end IsDiscreteValuationRing

end TauCeti
