/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.RootAveraging.Integral
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# Root averaging for integral rational series

An integral series represented by `P / Q`, with `Q(0)` a unit, remains a rational function
under every root translation. Its integral root average therefore becomes a finite sum of
rational functions in the fraction field of `ℂ_p⟦X⟧`. The identity also holds over any
`ℤ_p`-algebra domain containing a primitive `p`-th root of unity, using inverses of units
in its power-series ring or division in any field algebra over that ring. This identifies
the bounded psi operator without substituting an arbitrary rational function into a formal
series with nonzero constant term.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  §3.5.3–3.5.5, equations (3-5), (3-6), and (3-9).
-/

public section

open PowerSeries TauCeti TauCeti.IwasawaAveraging

variable {p : ℕ} [Fact p.Prime]

local notation "κ" =>
  RingHom.comp C (RingHom.comp (algebraMap ℚ_[p] ℂ_[p]) PadicInt.Coe.ringHom)
local notation "ι" => algebraMap (PowerSeries ℂ_[p]) (FractionRing (PowerSeries ℂ_[p]))

namespace TauCeti.IwasawaAveraging

/-- An integral rational series translates to the quotient of its translated numerator
and denominator in the fraction field of `ℂ_p⟦X⟧`. -/
theorem rootTranslation_eq_div (ζ : 𝓞_ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ)
    (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0))
    (F : PowerSeries ℤ_[p]) (hF : (Q : PowerSeries ℤ_[p]) * F = P) :
    ι (PowerSeries.map (𝓞_ℂ_[p]).subtype (rootTranslation p ζ hζ i F)) =
      ι (P.eval₂ κ (C ((ζ : ℂ_[p]) ^ i) * (1 + X) - 1)) /
        ι (Q.eval₂ κ (C ((ζ : ℂ_[p]) ^ i) * (1 + X) - 1)) := by
  have hu := isUnit_eval₂_rootTranslation p (ζ : ℂ_[p])
    (by exact_mod_cast hζ)
    ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom) i Q hQ
  apply (eq_div_iff (hu.map ι).ne_zero).2
  have h := congrArg
    (fun S ↦ ι (PowerSeries.map (𝓞_ℂ_[p]).subtype (rootTranslation p ζ hζ i S))) hF
  simpa only [map_mul, map_rootTranslation_coe, mul_comm] using h

end TauCeti.IwasawaAveraging

namespace IsPrimitiveRoot

/-- For every primitive `p`-th root in `ℂ_p`, the bounded psi projection of an integral
rational series is its finite root average, expressed as rational functions. -/
theorem mul_map_subst_psiSeries_eq_sum_div {ζ : ℂ_[p]} (hζ : IsPrimitiveRoot ζ p)
    (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0))
    (F : PowerSeries ℤ_[p]) (hF : (Q : PowerSeries ℤ_[p]) * F = P) :
    (p : FractionRing (PowerSeries ℂ_[p])) *
        ι (PowerSeries.map ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom)
          ((psiSeries p F).subst ((1 + X) ^ p - 1))) =
      ∑ i : Fin p, ι (P.eval₂ κ (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) /
        ι (Q.eval₂ κ (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) := by
  have hnorm : ‖ζ‖ = 1 := (hζ.isOfFinOrder (Fact.out : p.Prime).ne_zero).norm_eq_one
  have hmem : ζ ∈ 𝓞_ℂ_[p] := by
    apply (Valuation.mem_valuationSubring_iff _ _).2
    rw [← NNReal.coe_le_coe,
      PadicComplex.valuation_coe, hnorm]
    exact le_rfl
  let ζ₀ : 𝓞_ℂ_[p] := ⟨ζ, hmem⟩
  have hζ₀ : IsPrimitiveRoot ζ₀ p :=
    hζ.of_map_of_injective (f := (𝓞_ℂ_[p]).subtype) Subtype.val_injective
  have h := congrArg (fun S ↦ ι (PowerSeries.map (𝓞_ℂ_[p]).subtype S))
    (hζ₀.sum_rootTranslation F).symm
  simp only [map_mul, map_natCast, map_sum,
    rootTranslation_eq_div ζ₀ hζ₀.pow_eq_one _ P Q hQ F hF] at h
  convert h using 1
  congr 2
  ext n
  simp

end IsPrimitiveRoot

private theorem map_sum_rootTranslation_mul_inverse {A B : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (j : ℤ_[p] →+* A) {ζ : A} (hζ : ζ ^ p = 1)
    (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0)) :
    PowerSeries.map e (∑ i : Fin p,
        P.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1) *
          Ring.inverse (Q.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1))) =
      ∑ i : Fin p, P.eval₂ (C.comp (e.comp j)) (C (e ζ ^ (i : ℕ)) * (1 + X) - 1) *
        Ring.inverse (Q.eval₂ (C.comp (e.comp j)) (C (e ζ ^ (i : ℕ)) * (1 + X) - 1)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, (isUnit_eval₂_rootTranslation p ζ hζ j i Q hQ).map_ringInverse]
  have hc : (PowerSeries.map e).comp C = C.comp e := RingHom.ext (PowerSeries.map_C e)
  simp only [Polynomial.hom_eval₂, map_sub, map_mul, map_add, map_one, map_X, map_C,
    map_pow, ← RingHom.comp_assoc, hc]

private theorem mul_map_subst_psiSeries_eq_cyclotomic_sum
    (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0))
    (F : ℤ_[p]⟦X⟧) (hF : (Q : ℤ_[p]⟦X⟧) * F = P) :
    let f := Polynomial.cyclotomic p ℤ_[p]
    let x := AdjoinRoot.root f
    (p : (AdjoinRoot f)⟦X⟧) *
        PowerSeries.map (AdjoinRoot.of f) ((psiSeries p F).subst ((1 + X) ^ p - 1)) =
      ∑ i : Fin p, P.eval₂ (C.comp (AdjoinRoot.of f)) (C (x ^ (i : ℕ)) * (1 + X) - 1) *
        Ring.inverse (Q.eval₂ (C.comp (AdjoinRoot.of f)) (C (x ^ (i : ℕ)) * (1 + X) - 1)) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] p
  let f := Polynomial.cyclotomic p ℤ_[p]
  let j : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hξ₀ : (Polynomial.cyclotomic p ℂ_[p]).IsRoot ξ :=
    (Polynomial.isRoot_cyclotomic_iff_charZero (Fact.out : p.Prime).pos).2 hξ
  have hroot : f.eval₂ j ξ = 0 := by
    rwa [← Polynomial.eval_map, Polynomial.map_cyclotomic]
  let e := AdjoinRoot.lift j ξ hroot
  have he : Function.Injective e := by
    refine (injective_iff_map_eq_zero e).2 fun x hx ↦ ?_
    obtain ⟨G, rfl⟩ := AdjoinRoot.mk_surjective x
    have heval : G.eval₂ j ξ = 0 := (AdjoinRoot.lift_mk hroot G).symm.trans hx
    have hirr : Irreducible (Polynomial.cyclotomic p ℚ_[p]) := by
      simpa only [pow_one] using irreducible_cyclotomic_prime_pow_ratPadic p 1
    apply AdjoinRoot.mk_eq_zero.2
    apply (Polynomial.map_dvd_map PadicInt.Coe.ringHom Subtype.val_injective
      (Polynomial.cyclotomic.monic p ℤ_[p])).1
    rw [Polynomial.map_cyclotomic]
    refine (hirr.dvd_iff_aeval_eq_zero (b := ξ) ?_).1 ?_
    · rwa [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    · simpa only [Polynomial.aeval_def, Polynomial.eval₂_map] using heval
  have hc : e.comp (AdjoinRoot.of f) = j := AdjoinRoot.lift_comp_of hroot
  have hξe : e (AdjoinRoot.root f) = ξ := AdjoinRoot.lift_root hroot
  have hx : AdjoinRoot.root f ^ p = 1 := by
    apply he
    simpa only [map_pow, map_one, hξe] using hξ.pow_eq_one
  dsimp only
  apply PowerSeries.map_injective e he
  rw [map_sum_rootTranslation_mul_inverse e _ hx P Q hQ, map_mul, map_natCast,
    ← RingHom.comp_apply, ← PowerSeries.map_comp, hc, hξe]
  apply IsFractionRing.injective _ (FractionRing (PowerSeries ℂ_[p]))
  rw [map_mul, map_natCast, hξ.mul_map_subst_psiSeries_eq_sum_div P Q hQ F hF, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, (isUnit_eval₂_rootTranslation p ξ hξ.pow_eq_one _ i Q hQ).map_ringInverse,
    Ring.inverse_eq_inv, div_eq_mul_inv]

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R] {ζ : R}

/-- The bounded psi projection of an integral rational series is its finite root average
in `R⟦X⟧`, using the inverses of the translated denominator units. -/
theorem mul_map_subst_psiSeries_eq_sum_mul_inverse (hζ : IsPrimitiveRoot ζ p)
    (j : ℤ_[p] →+* R) (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0))
    (F : PowerSeries ℤ_[p]) (hF : (Q : PowerSeries ℤ_[p]) * F = P) :
    (p : R⟦X⟧) * PowerSeries.map j ((psiSeries p F).subst ((1 + X) ^ p - 1)) =
      ∑ i : Fin p, P.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1) *
        Ring.inverse (Q.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) := by
  have hx : AdjoinRoot.root (Polynomial.cyclotomic p ℤ_[p]) ^ p = 1 := by
    have h := AdjoinRoot.mk_eq_zero.2 (Polynomial.cyclotomic.dvd_X_pow_sub_one p ℤ_[p])
    simpa only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] using h
  have hz : (Polynomial.cyclotomic p ℤ_[p]).eval₂ j ζ = 0 := by
    simp only [Polynomial.cyclotomic_prime, Polynomial.eval₂_finsetSum]
    simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using
      hζ.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  have h := congrArg (PowerSeries.map (AdjoinRoot.lift j ζ hz))
    (mul_map_subst_psiSeries_eq_cyclotomic_sum P Q hQ F hF)
  simpa only [map_mul, map_natCast, ← RingHom.comp_apply, ← PowerSeries.map_comp,
    map_sum_rootTranslation_mul_inverse _ _ hx P Q hQ, AdjoinRoot.lift_comp_of,
    AdjoinRoot.lift_root] using h

/-- Rational root averaging in any field algebra over the receiving power-series ring.
In particular one may take its fraction field over a cyclotomic coefficient field. -/
theorem mul_map_subst_psiSeries_eq_sum_div_of_algebra (hζ : IsPrimitiveRoot ζ p)
    (j : ℤ_[p] →+* R) (L : Type*) [Field L] [Algebra R⟦X⟧ L]
    (P Q : Polynomial ℤ_[p]) (hQ : IsUnit (Q.coeff 0))
    (F : PowerSeries ℤ_[p]) (hF : (Q : PowerSeries ℤ_[p]) * F = P) :
    (p : L) * algebraMap R⟦X⟧ L (PowerSeries.map j ((psiSeries p F).subst ((1 + X) ^ p - 1))) =
      ∑ i : Fin p, algebraMap R⟦X⟧ L (P.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) /
        algebraMap R⟦X⟧ L (Q.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1)) := by
  have h := congrArg (algebraMap R⟦X⟧ L)
    (hζ.mul_map_subst_psiSeries_eq_sum_mul_inverse j P Q hQ F hF)
  simpa only [map_mul, map_natCast, map_sum, fun i : Fin p ↦
    (isUnit_eval₂_rootTranslation p ζ hζ.pow_eq_one j i Q hQ).map_ringInverse
      (algebraMap R⟦X⟧ L), Ring.inverse_eq_inv, div_eq_mul_inv] using h

end IsPrimitiveRoot

section Examples

local notation "ι₂" => algebraMap (PowerSeries ℚ_[2]) (FractionRing (PowerSeries ℚ_[2]))

-- The two denominators of the geometric rational series are 1 - X and 3 + X.
example (F : PowerSeries ℤ_[2]) (hF : (1 - X) * F = 1) :
    (2 : FractionRing (PowerSeries ℚ_[2])) *
        ι₂ (PowerSeries.map PadicInt.Coe.ringHom
          ((psiSeries 2 F).subst ((1 + X) ^ 2 - 1))) =
      (ι₂ (1 - X))⁻¹ + (ι₂ (3 + X))⁻¹ := by
  let j : ℤ_[2] →+* ℚ_[2] := PadicInt.Coe.ringHom
  have h := (IsPrimitiveRoot.neg_one_of_two_ne_zero (by norm_num) :
    IsPrimitiveRoot (-1 : ℚ_[2]) 2).mul_map_subst_psiSeries_eq_sum_div_of_algebra
      j (FractionRing (PowerSeries ℚ_[2])) (1 : Polynomial ℤ_[2]) (1 - Polynomial.X)
      (by simp) F (by simpa using hF)
  have h₀ : (1 - Polynomial.X : Polynomial ℤ_[2]).eval₂ (C.comp j)
      (C ((-1 : ℚ_[2]) ^ (0 : ℕ)) * (1 + X) - 1) = 1 - X := by simp
  have h₁ : (1 - Polynomial.X : Polynomial ℤ_[2]).eval₂ (C.comp j)
      (C ((-1 : ℚ_[2]) ^ (1 : ℕ)) * (1 + X) - 1) = 3 + X := by
    simp only [pow_one, Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X,
      map_neg, map_one]
    ring
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Polynomial.eval₂_one, map_one,
    one_div, h₀, h₁, Nat.cast_ofNat, j] using h

-- Unit constant coefficients rule out zero denominators over ℚ₂.
example (i : ℕ) (Q : Polynomial ℤ_[2]) (hQ : IsUnit (Q.coeff 0)) :
    ι₂ (Q.eval₂ (C.comp PadicInt.Coe.ringHom)
      (C ((-1 : ℚ_[2]) ^ i) * (1 + X) - 1)) ≠ 0 := by
  exact ((isUnit_eval₂_rootTranslation 2 (-1 : ℚ_[2]) (by norm_num)
    PadicInt.Coe.ringHom i Q hQ).map ι₂).ne_zero

end Examples
