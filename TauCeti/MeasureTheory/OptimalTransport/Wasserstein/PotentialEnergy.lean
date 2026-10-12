/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.GeodesicConvex
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic

/-!
# Potential energy and its displacement convexity

The *potential energy* of a measure `μ` in a potential `V : X → ℝ` is `∫ V dμ`. It is one of the
three basic energies on the Wasserstein space (with the interaction and internal energies), and the
drift term of the Fokker–Planck equation as a Wasserstein gradient flow.

Since `V` need not be integrable, the energy takes values in `EReal`, with the convention
`TauCeti.potentialEnergy`: it is `⊤` when the positive part of `V` has infinite integral, and
otherwise the integral of the positive part minus that of the negative part, which may be `⊥`. It
agrees with the Bochner integral for integrable `V` (`TauCeti.potentialEnergy_of_integrable`), and
a lower bound by an integrable function rules out the value `⊥`
(`TauCeti.potentialEnergy_ne_bot_of_le`).

On a real normed space `E`, convexity of `V` passes to the potential energy along every
interpolation of measures by a plan. If `V` is `m`-strongly convex in Mathlib's sense
(`StrongConvexOn univ m V`, where `m` may be negative) and `π` is a measure on `E × E`, then for
`t ∈ [0, 1]`, with `μ_t` the law of `(1 - t) • x + t • y` under `π`,

`∫ V dμ_t ≤ (1 - t) ∫ V dπ.fst + t ∫ V dπ.snd - (m / 2) t (1 - t) ∫ ‖x - y‖² dπ`

(`StrongConvexOn.potentialEnergy_map_le`). This is the pointwise convexity inequality integrated
against `π`. For an optimal plan for the quadratic cost, the last integral is the squared
`2`-Wasserstein distance of the two marginals and `μ_t` is a Wasserstein geodesic, so the potential
energy is `m`-geodesically convex on the space `P₂(E)` of laws with finite second moment, as soon as
`V` grows at most quadratically from below (`StrongConvexOn.geodesicallyConvex_potentialEnergy`).
The geodesic used is the interpolation of an optimal plan
(`TauCeti.WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul`), so this is the weak form of
displacement convexity: two laws are joined by some geodesic along which the inequality holds. The
plan-level inequality does not need the plan to be optimal, so it also applies to interpolations
along non-optimal plans, such as generalized geodesics.

## Main definitions

* `TauCeti.potentialEnergy V μ`: the potential energy `∫ V dμ`, as an extended real.

## Main results

* `TauCeti.potentialEnergy_of_integrable`: for integrable `V`, the potential energy is the Bochner
  integral of `V`.
* `TauCeti.integrable_iff_potentialEnergy_ne_top_and_ne_bot`: an almost everywhere strongly
  measurable potential is integrable exactly when its potential energy is finite.
* `TauCeti.potentialEnergy_mono`: the potential energy is monotone in the potential.
* `TauCeti.potentialEnergy_dirac`: the potential energy of a Dirac mass at `x` is `V x`.
* `TauCeti.potentialEnergy_ne_bot_of_hasFiniteMoment`: a potential with at most quadratic negative
  part has potential energy `≠ ⊥` against every finite measure with finite second moment.
* `StrongConvexOn.potentialEnergy_map_le`: the convexity inequality of the potential energy of an
  `m`-strongly convex potential along the interpolation of a plan.
* `StrongConvexOn.geodesicallyConvex_potentialEnergy`: the potential energy of an `m`-strongly
  convex potential with at most quadratic negative part is `m`-geodesically convex on the
  `2`-Wasserstein space of a separable Banach space.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.3, Proposition 9.3.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §7.3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

section Definition

variable {X : Type*} [MeasurableSpace X] {V W : X → ℝ} {μ : Measure X}

/-- The *potential energy* `∫ V dμ` of a measure `μ` in a potential `V : X → ℝ`, as an extended
real. It is `⊤` when the positive part of `V` has infinite integral against `μ`; otherwise it is the
integral of the positive part minus the integral of the negative part, which is `⊥` when only the
latter is infinite. -/
def potentialEnergy (V : X → ℝ) (μ : Measure X) : EReal :=
  if ∫⁻ x, ENNReal.ofReal (V x) ∂μ = ∞ then ⊤
  else (∫⁻ x, ENNReal.ofReal (V x) ∂μ : EReal) - (∫⁻ x, ENNReal.ofReal (-V x) ∂μ : EReal)

/-- When the positive part of the potential has finite integral, the potential energy is the
integral of the positive part minus that of the negative part. -/
theorem potentialEnergy_of_lintegral_ne_top (h : ∫⁻ x, ENNReal.ofReal (V x) ∂μ ≠ ∞) :
    potentialEnergy V μ =
      (∫⁻ x, ENNReal.ofReal (V x) ∂μ : EReal) - (∫⁻ x, ENNReal.ofReal (-V x) ∂μ : EReal) := by
  simp only [potentialEnergy, h, ite_false]

/-- The potential energy is `⊤` exactly when the positive part of the potential has infinite
integral. -/
theorem potentialEnergy_eq_top_iff :
    potentialEnergy V μ = ⊤ ↔ ∫⁻ x, ENNReal.ofReal (V x) ∂μ = ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [potentialEnergy, h, ite_true]⟩
  by_contra hV
  rw [potentialEnergy_of_lintegral_ne_top hV, ← EReal.coe_ennreal_toReal hV] at h
  exact (EReal.sub_le_of_le_add (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))).not_gt
    (h ▸ EReal.coe_lt_top _)

/-- The potential energy is `⊥` exactly when the positive part of the potential has finite
integral and its negative part has infinite integral. -/
theorem potentialEnergy_eq_bot_iff :
    potentialEnergy V μ = ⊥ ↔
      ∫⁻ x, ENNReal.ofReal (V x) ∂μ ≠ ∞ ∧ ∫⁻ x, ENNReal.ofReal (-V x) ∂μ = ∞ := by
  by_cases hV : ∫⁻ x, ENNReal.ofReal (V x) ∂μ = ∞
  · simp [potentialEnergy, hV]
  rw [potentialEnergy_of_lintegral_ne_top hV, ← EReal.coe_ennreal_toReal hV]
  refine ⟨fun h ↦ ⟨hV, by_contra fun hV' ↦ ?_⟩, fun h ↦ by simp [h.2]⟩
  rw [← EReal.coe_ennreal_toReal hV', ← EReal.coe_sub] at h
  exact EReal.coe_ne_bot _ h

/-- For an integrable potential, the potential energy is the Bochner integral of the potential. -/
theorem potentialEnergy_of_integrable (h : Integrable V μ) :
    potentialEnergy V μ = ((∫ x, V x ∂μ : ℝ) : EReal) := by
  have h₁ := h.lintegral_lt_top.ne
  have h₂ := h.neg.lintegral_lt_top.ne
  simp only [Pi.neg_apply] at h₂
  rw [potentialEnergy_of_lintegral_ne_top h₁,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h, EReal.coe_sub,
    EReal.coe_ennreal_toReal h₁, EReal.coe_ennreal_toReal h₂]

/-- An almost everywhere strongly measurable potential is integrable exactly when its potential
energy is finite. -/
theorem integrable_iff_potentialEnergy_ne_top_and_ne_bot (hV : AEStronglyMeasurable V μ) :
    Integrable V μ ↔ potentialEnergy V μ ≠ ⊤ ∧ potentialEnergy V μ ≠ ⊥ := by
  refine ⟨fun h ↦ by simp [potentialEnergy_of_integrable h], fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [Ne, potentialEnergy_eq_top_iff] at h₁
  rw [Ne, potentialEnergy_eq_bot_iff, not_and] at h₂
  refine ⟨hV, (hasFiniteIntegral_iff_norm V).2 ?_⟩
  calc ∫⁻ x, ENNReal.ofReal ‖V x‖ ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (V x) + ENNReal.ofReal (-V x)) ∂μ := lintegral_mono fun x ↦ by
        rw [Real.norm_eq_abs, abs_eq_max_neg, ENNReal.ofReal_max]
        exact max_le le_self_add le_add_self
    _ = ∫⁻ x, ENNReal.ofReal (V x) ∂μ + ∫⁻ x, ENNReal.ofReal (-V x) ∂μ :=
      lintegral_add_left' hV.aemeasurable.ennreal_ofReal _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 h₁, lt_top_iff_ne_top.2 (h₂ h₁)⟩

/-- The potential energy is monotone in the potential. -/
theorem potentialEnergy_mono (h : V ≤ᵐ[μ] W) : potentialEnergy V μ ≤ potentialEnergy W μ := by
  by_cases hW : ∫⁻ x, ENNReal.ofReal (W x) ∂μ = ∞
  · rw [potentialEnergy_eq_top_iff.2 hW]
    exact le_top
  have hle : ∫⁻ x, ENNReal.ofReal (V x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (W x) ∂μ :=
    lintegral_mono_ae (h.mono fun x hx ↦ ENNReal.ofReal_le_ofReal hx)
  rw [potentialEnergy_of_lintegral_ne_top (ne_top_of_le_ne_top hW hle),
    potentialEnergy_of_lintegral_ne_top hW]
  exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hle)
    (EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono_ae (h.mono fun x hx ↦ ENNReal.ofReal_le_ofReal (neg_le_neg hx))))

/-- The potential energy depends on the potential only up to `μ`-almost everywhere equality. -/
theorem potentialEnergy_congr_ae (h : V =ᵐ[μ] W) : potentialEnergy V μ = potentialEnergy W μ :=
  le_antisymm (potentialEnergy_mono h.le) (potentialEnergy_mono h.symm.le)

/-- A potential bounded below by an integrable function has potential energy `≠ ⊥`. -/
theorem potentialEnergy_ne_bot_of_le (hW : Integrable W μ) (h : W ≤ᵐ[μ] V) :
    potentialEnergy V μ ≠ ⊥ := fun hV ↦ by
  have := potentialEnergy_mono h
  rw [hV, potentialEnergy_of_integrable hW, le_bot_iff] at this
  exact EReal.coe_ne_bot _ this

/-- The potential energy of the zero measure is `0`. -/
@[simp]
theorem potentialEnergy_zero_measure (V : X → ℝ) : potentialEnergy V 0 = 0 := by
  simp [potentialEnergy]

/-- The potential energy of a Dirac mass at `x` is `V x`. -/
@[simp]
theorem potentialEnergy_dirac [MeasurableSingletonClass X] (V : X → ℝ) (x : X) :
    potentialEnergy V (Measure.dirac x) = V x := by
  rw [potentialEnergy_of_lintegral_ne_top (by simp), lintegral_dirac, lintegral_dirac,
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_sub,
    max_zero_sub_max_neg_zero_eq_self]

/-- The potential energy of a pushforward measure is the potential energy of the composed
potential. -/
theorem potentialEnergy_map {Y : Type*} [MeasurableSpace Y] {f : Y → X} {ν : Measure Y}
    (hV : Measurable V) (hf : AEMeasurable f ν) :
    potentialEnergy V (ν.map f) = potentialEnergy (fun y ↦ V (f y)) ν := by
  simp only [potentialEnergy, lintegral_map' hV.ennreal_ofReal.aemeasurable hf,
    lintegral_map' (f := fun x ↦ ENNReal.ofReal (-V x)) hV.neg.ennreal_ofReal.aemeasurable hf]

end Definition

section Growth

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- A potential whose negative part grows at most quadratically has potential energy `≠ ⊥`
against every finite measure with finite second moment. -/
theorem potentialEnergy_ne_bot_of_hasFiniteMoment {V : E → ℝ} {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasFiniteMoment 2 μ) {A B : ℝ} (hVAB : ∀ x, -(A + B * ‖x‖ ^ 2) ≤ V x) :
    potentialEnergy V μ ≠ ⊥ := by
  have hnorm : AEStronglyMeasurable (fun x : E ↦ ‖x‖) μ :=
    continuous_norm.measurable.aestronglyMeasurable
  have hmem : MemLp (fun x : E ↦ ‖x‖) 2 μ :=
    (memLp_congr_enorm hnorm measurable_edist_right.aestronglyMeasurable
      (.of_forall fun x ↦ by simp [edist_eq_enorm_sub])).2
      (hμ.memLp (x := 0) measurable_edist_right.aestronglyMeasurable)
  have hsq := (memLp_two_iff_integrable_sq_norm hnorm).1 hmem
  simp only [norm_norm] at hsq
  exact potentialEnergy_ne_bot_of_le ((integrable_const A).add (hsq.const_mul B)).neg
    (.of_forall hVAB)

end Growth

section Convexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {V : E → ℝ} {m : ℝ}

/-- **Convexity of the potential energy along a plan.** If `V` is `m`-strongly convex, then along
the interpolation `t ↦ μ_t`, with `μ_t` the law of `(1 - t) • x + t • y` under a measure `π` on
`E × E`, the potential energy satisfies, for `t ∈ [0, 1]`,
`∫ V dμ_t ≤ (1 - t) ∫ V dπ.fst + t ∫ V dπ.snd - (m / 2) t (1 - t) ∫ ‖x - y‖² dπ`.
The potential energies of the two marginals must not be `⊥`, and `‖x - y‖²` must be integrable. -/
theorem _root_.StrongConvexOn.potentialEnergy_map_le (hV : StrongConvexOn univ m V)
    (hVm : Measurable V) {π : Measure (E × E)} (h₀ : potentialEnergy V π.fst ≠ ⊥)
    (h₁ : potentialEnergy V π.snd ≠ ⊥) (hπ : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) π)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    potentialEnergy V (π.map fun z ↦ (1 - t) • z.1 + t • z.2) ≤
      ((1 - t : ℝ) : EReal) * potentialEnergy V π.fst + (t : EReal) * potentialEnergy V π.snd -
        ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π : ℝ) : EReal) := by
  rcases ht.1.eq_or_lt with rfl | ht₀
  · simp [Measure.fst]
  rcases ht.2.eq_or_lt with rfl | ht₁
  · simp [Measure.snd]
  have hmeas : Measurable fun z : E × E ↦ (1 - t) • z.1 + t • z.2 := by fun_prop
  by_cases hfin : potentialEnergy V π.fst ≠ ⊤ ∧ potentialEnergy V π.snd ≠ ⊤
  swap
  · -- One endpoint has energy `⊤`, so the right-hand side is `⊤`.
    have h₀' : ((1 - t : ℝ) : EReal) * potentialEnergy V π.fst ≠ ⊥ :=
      (EReal.mul_ne_bot _ _).2 ⟨.inl (EReal.coe_ne_bot _), .inr h₀, .inl (EReal.coe_ne_top _),
        .inl (EReal.coe_nonneg.2 (sub_nonneg.2 ht.2))⟩
    have h₁' : (t : EReal) * potentialEnergy V π.snd ≠ ⊥ :=
      (EReal.mul_ne_bot _ _).2 ⟨.inl (EReal.coe_ne_bot _), .inr h₁, .inl (EReal.coe_ne_top _),
        .inl (EReal.coe_nonneg.2 ht.1)⟩
    have htop : ((1 - t : ℝ) : EReal) * potentialEnergy V π.fst +
        (t : EReal) * potentialEnergy V π.snd = ⊤ := by
      rcases not_and_or.1 hfin with h | h <;> rw [not_not] at h <;> rw [h]
      · rw [EReal.coe_mul_top_of_pos (sub_pos.2 ht₁), EReal.top_add_of_ne_bot h₁']
      · rw [EReal.coe_mul_top_of_pos ht₀, EReal.add_top_of_ne_bot h₀']
    rw [htop, EReal.top_sub_coe]
    exact le_top
  obtain ⟨hfin₀, hfin₁⟩ := hfin
  have hi₀ : Integrable V π.fst :=
    (integrable_iff_potentialEnergy_ne_top_and_ne_bot hVm.aestronglyMeasurable).2 ⟨hfin₀, h₀⟩
  have hi₁ : Integrable V π.snd :=
    (integrable_iff_potentialEnergy_ne_top_and_ne_bot hVm.aestronglyMeasurable).2 ⟨hfin₁, h₁⟩
  have hi₀' : Integrable (fun z : E × E ↦ V z.1) π :=
    (integrable_map_measure hVm.aestronglyMeasurable measurable_fst.aemeasurable).1 hi₀
  have hi₁' : Integrable (fun z : E × E ↦ V z.2) π :=
    (integrable_map_measure hVm.aestronglyMeasurable measurable_snd.aemeasurable).1 hi₁
  -- The pointwise convexity inequality, integrated against `π`.
  have hle (z : E × E) : V ((1 - t) • z.1 + t • z.2) ≤
      (1 - t) * V z.1 + t * V z.2 - m / 2 * t * (1 - t) * ‖z.1 - z.2‖ ^ 2 := by
    have := hV.2 (mem_univ z.1) (mem_univ z.2) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
    simp only [smul_eq_mul] at this
    linarith
  have hint₀ : Integrable (fun z : E × E ↦ (1 - t) * V z.1 + t * V z.2) π :=
    (hi₀'.const_mul _).add (hi₁'.const_mul _)
  have hint : Integrable (fun z : E × E ↦
      (1 - t) * V z.1 + t * V z.2 - m / 2 * t * (1 - t) * ‖z.1 - z.2‖ ^ 2) π :=
    hint₀.sub (hπ.const_mul _)
  rw [potentialEnergy_map hVm hmeas.aemeasurable]
  refine (potentialEnergy_mono (.of_forall hle)).trans_eq ?_
  rw [potentialEnergy_of_integrable hint, potentialEnergy_of_integrable hi₀,
    potentialEnergy_of_integrable hi₁, integral_sub hint₀ (hπ.const_mul _),
    integral_add (hi₀'.const_mul _) (hi₁'.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, Measure.fst, Measure.snd,
    integral_map measurable_fst.aemeasurable hVm.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hVm.aestronglyMeasurable]
  norm_cast

variable [CompleteSpace E]

/-- **Displacement convexity of the potential energy.** On a separable Banach space `E`, the
potential energy of an `m`-strongly convex measurable potential `V` whose negative part grows at
most quadratically is `m`-geodesically convex on the `2`-Wasserstein space `P₂(E)`: two laws of
finite potential energy are joined by a Wasserstein geodesic, the interpolation of an optimal plan,
along which `∫ V dμ_t ≤ (1 - t) ∫ V dμ₀ + t ∫ V dμ₁ - (m / 2) t (1 - t) W₂(μ₀, μ₁)²`. -/
theorem _root_.StrongConvexOn.geodesicallyConvex_potentialEnergy (hV : StrongConvexOn univ m V)
    (hVm : Measurable V) {A B : ℝ} (hVAB : ∀ x, -(A + B * ‖x‖ ^ 2) ≤ V x) :
    GeodesicallyConvex m fun μ : WassersteinSpace 2 E ↦
      potentialEnergy V ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [geodesicallyConvex_def]
  intro μ₀ μ₁ _ _
  -- The interpolation of an optimal plan for the quadratic cost is a geodesic.
  obtain ⟨π, hπ, hmem, hdist, γ, hγ, hγt⟩ :=
    WassersteinSpace.exists_dist_sq_eq_integral_isGeodesicSegment_map_smul_add_smul μ₀ μ₁
  refine ⟨γ, hγ, hγ.convexAlong_iff.2 fun t ht ↦ ?_⟩
  rw [hγt t ht, hdist, ← hπ.fst_eq, ← hπ.snd_eq]
  exact hV.potentialEnergy_map_le hVm
    (hπ.fst_eq ▸ potentialEnergy_ne_bot_of_hasFiniteMoment (WassersteinSpace.hasFiniteMoment μ₀)
      hVAB)
    (hπ.snd_eq ▸ potentialEnergy_ne_bot_of_hasFiniteMoment (WassersteinSpace.hasFiniteMoment μ₁)
      hVAB)
    ((memLp_two_iff_integrable_sq_norm (by fun_prop)).1 hmem) ht

end Convexity

end TauCeti
