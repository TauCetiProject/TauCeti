/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.RootAveraging.Integral
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Root averaging for integral rational series

An integral series represented by `P / Q`, with `Q(0)` a unit, remains a rational function
under every root translation. Its integral root average therefore becomes a finite sum of
rational functions in the fraction field of `ℂ_p⟦X⟧`. This identifies the bounded psi
operator on these series without substituting an arbitrary rational function into a formal
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
  apply (eq_div_iff ((isUnit_eval₂_rootTranslation p ζ hζ i Q hQ).map ι).ne_zero).2
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
