/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.RootAveraging.Rational

/-!
# Descent of rational root averaging

The root-average formula for an integral rational series holds in the fraction field of
`K⟦X⟧` whenever the coefficient field `K` embeds in `ℂ_p` compatibly with its map from
`ℤ_p`. In particular one can work over a cyclotomic coefficient field rather than over
`ℂ_p`. No topology, norm, or completeness of `K` is required.

A polynomial with unit constant coefficient remains a unit after root translation over
`K`. Thus every denominator appearing in the formula is nonzero. The integral series is
transformed by the bounded psi operator before extending coefficients; the result does
not assert that arbitrary formal series admit substitution at a nonzero constant term.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  §3.5.3–3.5.5, equations (3-5), (3-6), and (3-9).
-/

public section

open PowerSeries TauCeti TauCeti.IwasawaAveraging

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]

namespace TauCeti.IwasawaAveraging

/-- Root translation of an integral polynomial with unit constant coefficient is a unit
over every coefficient field embedded compatibly in `ℂ_p`. In particular its image in
`FractionRing K⟦X⟧` is a nonzero denominator. -/
theorem isUnit_eval₂_rootTranslation_of_embedding (ζ : K) (hζ : ζ ^ p = 1)
    (j : ℤ_[p] →+* K) (e : K →+* ℂ_[p])
    (he : e.comp j = (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom)
    (i : ℕ) (Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0)) :
    IsUnit (Q.eval₂ (C.comp j) (C (ζ ^ i) * (1 + X) - 1)) := by
  have hroot : (e ζ) ^ p = 1 := by rw [← map_pow, hζ, map_one]
  have hnorm : ‖e ζ‖ = 1 :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : p.Prime).pos, hroot⟩).norm_eq_one
  have hmem : e ζ ∈ 𝓞_ℂ_[p] := by
    apply (Valuation.mem_valuationSubring_iff _ _).2
    rw [← NNReal.coe_le_coe, PadicComplex.valuation_coe, hnorm]
    exact le_rfl
  let ζ₀ : 𝓞_ℂ_[p] := ⟨e ζ, hmem⟩
  have hζ₀ : ζ₀ ^ p = 1 := Subtype.ext hroot
  have hu := isUnit_eval₂_rootTranslation p ζ₀ hζ₀ i Q hQ
  have hm : PowerSeries.map e
      (Q.eval₂ (C.comp j) (C (ζ ^ i) * (1 + X) - 1)) =
      Q.eval₂ (C.comp ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom))
        (C ((e ζ) ^ i) * (1 + X) - 1) := by
    rw [Polynomial.hom_eval₂]
    simp only [map_sub, map_mul, map_add, map_one, map_X, map_C, map_pow]
    congr 1
    apply RingHom.ext
    intro a
    simpa using congrArg C (RingHom.congr_fun he a)
  rw [← hm] at hu
  exact isUnit_of_map_unit (PowerSeries.map e) _ hu

end TauCeti.IwasawaAveraging

namespace IsPrimitiveRoot

variable {ζ : K}

/-- Rational root averaging descends from `ℂ_p` to any compatibly embedded coefficient
field. All quotients are taken in the fraction field of the power-series ring. -/
theorem mul_map_subst_psiSeries_eq_sum_div_of_embedding (hζ : IsPrimitiveRoot ζ p)
    (j : ℤ_[p] →+* K) (e : K →+* ℂ_[p])
    (he : e.comp j = (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom)
    (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0))
    (F : PowerSeries ℤ_[p]) (hF : (Q : PowerSeries ℤ_[p]) * F = P) :
    (p : FractionRing (PowerSeries K)) *
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.map j ((psiSeries p F).subst ((1 + X) ^ p - 1))) =
      ∑ i : Fin p,
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (P.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) /
          algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (Q.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) := by
  let E : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries ℂ_[p]) :=
    IsFractionRing.map (PowerSeries.map_injective e e.injective)
  have hE (S : PowerSeries K) :
      E (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) S) =
        algebraMap (PowerSeries ℂ_[p]) (FractionRing (PowerSeries ℂ_[p]))
          (PowerSeries.map e S) := IsLocalization.map_eq _ _
  have hpoly (S : Polynomial ℤ_[p]) (i : ℕ) :
      PowerSeries.map e (S.eval₂ (C.comp j) (C (ζ ^ i) * (1 + X) - 1)) =
        S.eval₂ (C.comp ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom))
          (C ((e ζ) ^ i) * (1 + X) - 1) := by
    rw [Polynomial.hom_eval₂]
    simp only [map_sub, map_mul, map_add, map_one, map_X, map_C, map_pow]
    congr 1
    apply RingHom.ext
    intro a
    simpa using congrArg C (RingHom.congr_fun he a)
  apply E.injective
  simp only [map_mul, map_natCast, map_sum, map_div₀, hE, hpoly]
  rw [← RingHom.comp_apply (PowerSeries.map e) (PowerSeries.map j),
    ← PowerSeries.map_comp, he]
  exact (hζ.map_of_injective e.injective).mul_map_subst_psiSeries_eq_sum_div P Q hQ F hF

end IsPrimitiveRoot

section Examples

local notation "ι₂" => algebraMap (PowerSeries ℚ_[2]) (FractionRing (PowerSeries ℚ_[2]))

-- A geometric rational series at p = 2 has denominators 1 - X and 3 + X.
-- The second denominator retains the nonzero translated constant term.
example (F : PowerSeries ℤ_[2]) (hF : (1 - X) * F = 1) :
    (2 : FractionRing (PowerSeries ℚ_[2])) *
        ι₂ (PowerSeries.map PadicInt.Coe.ringHom
          ((psiSeries 2 F).subst ((1 + X) ^ 2 - 1))) =
      (ι₂ (1 - X))⁻¹ + (ι₂ (3 + X))⁻¹ := by
  have h := (IsPrimitiveRoot.neg_one 0 (by decide) :
    IsPrimitiveRoot (-1 : ℚ_[2]) 2).mul_map_subst_psiSeries_eq_sum_div_of_embedding
      PadicInt.Coe.ringHom (algebraMap ℚ_[2] ℂ_[2]) rfl
      (1 : Polynomial ℤ_[2]) (1 - Polynomial.X) (by simp) F (by simpa using hF)
  suffices h' : (2 : FractionRing (PowerSeries ℚ_[2])) *
      ι₂ (PowerSeries.map PadicInt.Coe.ringHom
        ((psiSeries 2 F).subst ((1 + X) ^ 2 - 1))) =
        (1 - ι₂ X)⁻¹ + (1 - (-ι₂ X + -1 - 1))⁻¹ by
    convert h' using 2
    · simp
    · congr 1
      simp only [map_add, map_ofNat]
      ring
  simpa [Fin.sum_univ_two] using h

-- Unit constant coefficients rule out zero denominators over ℚ_2, not just over ℂ_2.
example (i : ℕ) (Q : Polynomial ℤ_[2]) (hQ : IsUnit (Q.coeff 0)) :
    ι₂ (Q.eval₂ (C.comp PadicInt.Coe.ringHom)
      (C ((-1 : ℚ_[2]) ^ i) * (1 + X) - 1)) ≠ 0 := by
  exact ((isUnit_eval₂_rootTranslation_of_embedding (-1 : ℚ_[2]) (by norm_num)
    PadicInt.Coe.ringHom (algebraMap ℚ_[2] ℂ_[2]) rfl i Q hQ).map ι₂).ne_zero

-- Without the unit hypothesis, X + 2 translates to -X at the nontrivial dyadic root.
-- The translated series is nonzero but is not a unit of ℚ_2⟦X⟧.
example : ¬ IsUnit ((Polynomial.X + 2 : Polynomial ℤ_[2]).eval₂
    (C.comp (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]))
    (C (-1) * (1 + X) - 1)) := by
  norm_num [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  rw [map_ofNat]
  ring

end Examples
