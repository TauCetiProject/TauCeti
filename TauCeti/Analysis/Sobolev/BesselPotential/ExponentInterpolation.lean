/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.ToLp
public import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Complex interpolation of Bessel-potential spaces of one order

Let `E` be a finite-dimensional real inner product space and `H^{s,p} = H^{s,p}(E, F)` Mathlib's
Bessel-potential spaces. For one order `s` and two exponents `1 ≤ p₀, p₁ ≤ ∞` the spaces
`H^{s,p₀}` and `H^{s,p₁}` form a compatible couple inside the tempered distributions
(`TauCeti.CompatibleCouple.besselPotentialSpace E F s p₀ s p₁`). This file proves that for
`0 < θ < 1` its complex interpolation space is again a Bessel-potential space of order `s`,
isometrically:

`[H^{s,p₀}, H^{s,p₁}]_θ = H^{s,p}`, `1 / p = (1 - θ) / p₀ + θ / p₁`, `p < ∞`

(`TauCeti.CompatibleCouple.besselPotentialSpaceOfOrderComplexMethodEquiv`), for values in a complex
Hilbert space.

The proof transports Calderón's identity `[L^{p₀}, L^{p₁}]_θ = Lᵖ`
(`TauCeti.CompatibleCouple.lebesgueComplexMethodEquiv`) along the Bessel potential `J^s`. For each
exponent, `u ↦ J^s u` is the linear isometric equivalence `H^{s,p} ≃ₗᵢ Lᵖ`
(`BesselPotentialSpace.toLpₗᵢ`), and the two equivalences for `p₀` and `p₁` agree on the
intersections: two elements of `H^{s,p₀}` and `H^{s,p₁}` are the same tempered distribution
exactly when their functions `J^s u` agree almost everywhere
(`BesselPotentialSpace.toDistr_eq_toDistr_iff`).
So they induce an isometric equivalence of the complex interpolation spaces of the two couples
(`TauCeti.CompatibleCouple.besselPotentialSpaceOfOrderLebesgueEquiv`), and
`[H^{s,p₀}, H^{s,p₁}]_θ ≃ [L^{p₀}, L^{p₁}]_θ ≃ Lᵖ ≃ H^{s,p}`. The composite keeps the underlying
tempered distribution
(`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceOfOrderComplexMethodEquiv_apply`).

Two orders `s₀ ≠ s₁` cannot be handled this way, since `J^{s₀}` and `J^{s₁}` do not agree on the
intersection; that case, Bergh–Löfström, Theorem 6.4.5 (7), is
`TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodContinuousLinearEquiv`, proved with the
`Lᵖ` bounds for Bessel potentials of imaginary order and with equivalent rather than equal norms.

## Main declarations

* `TauCeti.CompatibleCouple.mem_besselPotentialSpace_inter_iff_toLp_ae_eq`: the intersection
  `H^{s,p₀} ∩ H^{s,p₁}` of the couple `(H^{s,p₀}, H^{s,p₁})`.
* `TauCeti.CompatibleCouple.besselPotentialSpaceOfOrderLebesgueEquiv`: the isometric isomorphism
  `[H^{s,p₀}, H^{s,p₁}]_θ ≃ₗᵢ[ℂ] [L^{p₀}, L^{p₁}]_θ` induced by `J^s`, for every `θ`.
* `TauCeti.CompatibleCouple.besselPotentialSpaceOfOrderComplexMethodEquiv`: the isometric
  isomorphism `[H^{s,p₀}, H^{s,p₁}]_θ ≃ₗᵢ[ℂ] H^{s,p}`, which keeps the underlying tempered
  distribution.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 4.1.2 (endpoint isomorphisms), Theorem 5.1.2 and Theorem 6.4.5 (7).
* H. Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, North-Holland,
  1978, §2.4.2.
-/

public section

noncomputable section

open MeasureTheory Set TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

namespace CompatibleCouple

open BesselPotentialSpace

section Couple

variable {s : ℝ} {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]

/-- The intersection `H^{s,p₀} ∩ H^{s,p₁}` consists of the pairs whose `Lᵖ` functions `J^s u`
agree almost everywhere. -/
theorem mem_besselPotentialSpace_inter_iff_toLp_ae_eq
    {x : H^{s, p₀}(E, F) × H^{s, p₁}(E, F)} :
    x ∈ (besselPotentialSpace E F s p₀ s p₁).inter ↔ x.1.toLp =ᵐ[volume] x.2.toLp := by
  rw [mem_inter_iff, besselPotentialSpace_embed₀_apply,
    besselPotentialSpace_embed₁_apply, toDistr_eq_toDistr_iff]

/-- The Bessel potentials `J^s : H^{s,p₀} → L^{p₀}` and `J^s : H^{s,p₁} → L^{p₁}` agree on the
intersection `H^{s,p₀} ∩ H^{s,p₁}`. -/
theorem lebesgue_fstToSum_toLpₗᵢ_interFst (x : (besselPotentialSpace E F s p₀ s p₁).inter) :
    (lebesgue ℂ F (volume : Measure E) p₀ p₁).fstToSum ((toLpₗᵢ E F s p₀).toContinuousLinearEquiv
        ((besselPotentialSpace E F s p₀ s p₁).interFst x)) =
      (lebesgue ℂ F (volume : Measure E) p₀ p₁).sndToSum ((toLpₗᵢ E F s p₁).toContinuousLinearEquiv
        ((besselPotentialSpace E F s p₀ s p₁).interSnd x)) :=
  (lebesgue ℂ F (volume : Measure E) p₀ p₁).sumSpace_ext <| by
    simpa [toDistr_eq_toDistr_iff, L1AddLinfty.ofLp_eq_ofLp_iff] using
      (besselPotentialSpace E F s p₀ s p₁).embed₀_interFst x

/-- The inverse Bessel potentials `J^{-s} : L^{p₀} → H^{s,p₀}` and `J^{-s} : L^{p₁} → H^{s,p₁}`
agree on the intersection `L^{p₀} ∩ L^{p₁}`. -/
theorem besselPotentialSpace_fstToSum_toLpₗᵢ_symm_interFst
    (y : (lebesgue ℂ F (volume : Measure E) p₀ p₁).inter) :
    (besselPotentialSpace E F s p₀ s p₁).fstToSum
        ((toLpₗᵢ E F s p₀).toContinuousLinearEquiv.symm
          ((lebesgue ℂ F (volume : Measure E) p₀ p₁).interFst y)) =
      (besselPotentialSpace E F s p₀ s p₁).sndToSum
        ((toLpₗᵢ E F s p₁).toContinuousLinearEquiv.symm
          ((lebesgue ℂ F (volume : Measure E) p₀ p₁).interSnd y)) :=
  (besselPotentialSpace E F s p₀ s p₁).sumSpace_ext <| by
    -- Keep `(toLpₗᵢ _ _ s _).symm f` unexpanded and read its `toLp` as `toLpₗᵢ`, so that
    -- `apply_symm_apply` returns `f`.
    simpa [toDistr_eq_toDistr_iff, L1AddLinfty.ofLp_eq_ofLp_iff, -toLpₗᵢ_symm_apply,
      ← toLpₗᵢ_apply] using (lebesgue ℂ F (volume : Measure E) p₀ p₁).embed₀_interFst y

variable (E F s) in
/-- **The Bessel potential on complex interpolation spaces.** For every `θ`, the Bessel potential
`J^s` induces an isometric isomorphism `[H^{s,p₀}, H^{s,p₁}]_θ ≃ₗᵢ[ℂ] [L^{p₀}, L^{p₁}]_θ` between
the complex interpolation spaces of the couple of Bessel-potential spaces of order `s` and of the
Lebesgue couple. It lies over the map `u₀ + u₁ ↦ J^s u₀ + J^s u₁` of sum spaces. -/
def besselPotentialSpaceOfOrderLebesgueEquiv (θ : ℝ) :
    (besselPotentialSpace E F s p₀ s p₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      (lebesgue ℂ F (volume : Measure E) p₀ p₁).ComplexMethodSpace θ where
  toLinearEquiv := (ComplexMethodSpace.mapEquiv θ (toLpₗᵢ E F s p₀).toContinuousLinearEquiv
    (toLpₗᵢ E F s p₁).toContinuousLinearEquiv lebesgue_fstToSum_toLpₗᵢ_interFst
    besselPotentialSpace_fstToSum_toLpₗᵢ_symm_interFst).toLinearEquiv
  norm_map' := ComplexMethodSpace.norm_mapEquiv _ _ _ _ (toLpₗᵢ E F s p₀).norm_map
    (toLpₗᵢ E F s p₁).norm_map

/-- `besselPotentialSpaceOfOrderLebesgueEquiv` lies over the map `u₀ + u₁ ↦ J^s u₀ + J^s u₁` of
sum spaces. -/
@[simp]
theorem toSum_besselPotentialSpaceOfOrderLebesgueEquiv_apply {θ : ℝ}
    (u : (besselPotentialSpace E F s p₀ s p₁).ComplexMethodSpace θ) :
    ComplexMethodSpace.toSum (besselPotentialSpaceOfOrderLebesgueEquiv E F s θ u) =
      (besselPotentialSpace E F s p₀ s p₁).sumLift
        ((lebesgue ℂ F (volume : Measure E) p₀ p₁).fstToSum.comp
          ((toLpₗᵢ E F s p₀).toContinuousLinearEquiv : H^{s, p₀}(E, F) →L[ℂ] _))
        ((lebesgue ℂ F (volume : Measure E) p₀ p₁).sndToSum.comp
          ((toLpₗᵢ E F s p₁).toContinuousLinearEquiv : H^{s, p₁}(E, F) →L[ℂ] _))
        (fun x ↦ by simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
          lebesgue_fstToSum_toLpₗᵢ_interFst x) (ComplexMethodSpace.toSum u) :=
  ComplexMethodSpace.toSum_mapEquiv _ _ _ _ u

/-- The inverse of `besselPotentialSpaceOfOrderLebesgueEquiv` lies over the map
`f₀ + f₁ ↦ J^{-s} f₀ + J^{-s} f₁` of sum spaces. -/
@[simp]
theorem toSum_besselPotentialSpaceOfOrderLebesgueEquiv_symm_apply {θ : ℝ}
    (v : (lebesgue ℂ F (volume : Measure E) p₀ p₁).ComplexMethodSpace θ) :
    ComplexMethodSpace.toSum ((besselPotentialSpaceOfOrderLebesgueEquiv E F s θ).symm v) =
      (lebesgue ℂ F (volume : Measure E) p₀ p₁).sumLift
        ((besselPotentialSpace E F s p₀ s p₁).fstToSum.comp
          ((toLpₗᵢ E F s p₀).toContinuousLinearEquiv.symm :
            Lp F p₀ (volume : Measure E) →L[ℂ] _))
        ((besselPotentialSpace E F s p₀ s p₁).sndToSum.comp
          ((toLpₗᵢ E F s p₁).toContinuousLinearEquiv.symm :
            Lp F p₁ (volume : Measure E) →L[ℂ] _))
        (fun y ↦ by simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
          besselPotentialSpace_fstToSum_toLpₗᵢ_symm_interFst y)
        (ComplexMethodSpace.toSum v) :=
  ComplexMethodSpace.toSum_mapEquiv_symm _ _ _ _ v

end Couple

/-! ### The identification `[H^{s,p₀}, H^{s,p₁}]_θ = H^{s,p}` -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {s : ℝ} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] {θ : ℝ}
  (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)

variable (E H s p₀ p₁) in
/-- **Complex interpolation of Bessel-potential spaces of one order** (Bergh–Löfström,
Theorem 5.1.2 through the Bessel potential). For `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and the
interpolated exponent `1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`, Calderón's complex
interpolation space `[H^{s,p₀}, H^{s,p₁}]_θ` of the couple `(H^{s,p₀}(E, H), H^{s,p₁}(E, H))` is the
Bessel-potential space `H^{s,p}(E, H)`, with equal norms. The isometry keeps the underlying
tempered distribution
(`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceOfOrderComplexMethodEquiv_apply`). -/
def besselPotentialSpaceOfOrderComplexMethodEquiv :
    (besselPotentialSpace E H s p₀ s p₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] H^{s, p}(E, H) :=
  (besselPotentialSpaceOfOrderLebesgueEquiv E H s θ).trans
    ((lebesgueComplexMethodEquiv hθ hp hp_top).trans (toLpₗᵢ E H s p).symm)

/-- The inverse of `besselPotentialSpaceOfOrderComplexMethodEquiv` sends `u ∈ H^{s,p}` to the
element of `[H^{s,p₀}, H^{s,p₁}]_θ` with the same tempered distribution. -/
@[simp]
theorem sumSpaceEmbed_toSum_besselPotentialSpaceOfOrderComplexMethodEquiv_symm_apply
    (u : H^{s, p}(E, H)) :
    (besselPotentialSpace E H s p₀ s p₁).sumSpaceEmbed (ComplexMethodSpace.toSum
        ((besselPotentialSpaceOfOrderComplexMethodEquiv E H s p₀ p₁ hθ hp hp_top).symm u)) =
      u.toDistr := by
  set v := lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top u.toLp
  -- Decompose the element `v` of `[L^{p₀}, L^{p₁}]_θ` representing `J^s u` as `f₀ + f₁`.
  obtain ⟨f₀, f₁, hf⟩ :=
    (lebesgue ℂ H (volume : Measure E) p₀ p₁).exists_fstToSum_add_sndToSum_eq
      (ComplexMethodSpace.toSum v)
  have hsum : ⇑f₀ + ⇑f₁ =ᵐ[volume] u.toLp :=
    lebesgue_sumSpaceEmbed_fstToSum_add_sndToSum_eq_ofLp_iff.1 <| by
      rw [hf, sumSpaceEmbed_toSum_lpToLebesgueComplexMethod]
  have hsymm : (besselPotentialSpaceOfOrderComplexMethodEquiv E H s p₀ p₁ hθ hp hp_top).symm u =
      (besselPotentialSpaceOfOrderLebesgueEquiv E H s θ).symm v := by
    simp only [besselPotentialSpaceOfOrderComplexMethodEquiv, LinearIsometryEquiv.symm_trans,
      LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_symm, toLpₗᵢ_apply,
      lebesgueComplexMethodEquiv_symm_apply, v]
  rw [hsymm, toSum_besselPotentialSpaceOfOrderLebesgueEquiv_symm_apply, ← hf, map_add,
    sumLift_fstToSum, sumLift_sndToSum, map_add]
  simp only [ContinuousLinearMap.comp_apply, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum,
    besselPotentialSpace_embed₀_apply, besselPotentialSpace_embed₁_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    toLpₗᵢ_symm_apply]
  rw [← map_add, ← besselPotential_neg_toLp_eq (f := u),
    Lp.toTemperedDistribution_add_toTemperedDistribution_eq_iff.2 hsum]

/-- `besselPotentialSpaceOfOrderComplexMethodEquiv` keeps the underlying tempered distribution:
an element of `[H^{s,p₀}, H^{s,p₁}]_θ` is sent to the element of `H^{s,p}` with the same
distribution. -/
@[simp]
theorem toDistr_besselPotentialSpaceOfOrderComplexMethodEquiv_apply
    (u : (besselPotentialSpace E H s p₀ s p₁).ComplexMethodSpace θ) :
    (besselPotentialSpaceOfOrderComplexMethodEquiv E H s p₀ p₁ hθ hp hp_top u).toDistr =
      (besselPotentialSpace E H s p₀ s p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
  conv_rhs =>
    rw [← (besselPotentialSpaceOfOrderComplexMethodEquiv E H s p₀ p₁ hθ hp hp_top).symm_apply_apply
      u]
  rw [sumSpaceEmbed_toSum_besselPotentialSpaceOfOrderComplexMethodEquiv_symm_apply]

end Hilbert

end CompatibleCouple

end TauCeti
