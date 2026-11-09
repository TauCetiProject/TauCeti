/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.OptimalTransport.Duality.CyclicalMonotonicity

/-!
# Duality for the Wasserstein distance

Kantorovich weak duality bounds the dual value of a feasible pair of potentials by the transport
cost. This file records the form of that bound for the `p`-Wasserstein distance when the
potentials are only feasible for the cost read at quantized points: if
`f₁ y + f₂ y' ≤ d(Q₁ y, Q₂ y') ^ p` for measurable maps `Q₁`, `Q₂`, then the dual value of
`(f₁, f₂)` against laws `A` and `B` is at most the `p`-th power of `W_p (A, B)` enlarged by the
two `L^p` displacements `‖d(·, Q₁ ·)‖_{L^p (A)}` and `‖d(·, Q₂ ·)‖_{L^p (B)}`.

Such potentials arise from strong duality on a finite subspace onto which the laws have been
quantized, and the bound transfers the finite dual certificate back to the original laws.

For the quadratic cost, Kantorovich duality concentrates a coupling realizing a finite `W₂`
distance on a measurable set that is cyclically monotone for the cost `‖x - y‖ ^ 2 / 2`.

## Main statements

* `TauCeti.ofReal_integral_add_integral_le_wassersteinEDist_add_rpow` — weak duality for potentials
  that are feasible for the quantized cost.
* `TauCeti.exists_isCyclicallyMonotone_of_eLpNorm_eq` — a coupling realizing a finite `W₂`
  distance is concentrated on a measurable set that is cyclically monotone for the quadratic cost.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {Y : Type*} [MeasurableSpace Y] [PseudoMetricSpace Y] [OpensMeasurableSpace Y]
  [TopologicalSpace.SeparableSpace Y] {p : ℝ≥0∞}

/-- **Weak duality for quantized potentials.** If `f₁ y + f₂ y'` is bounded by the `p`-th power of
the distance between the quantized points `Q₁ y` and `Q₂ y'`, then the dual value of `(f₁, f₂)` is
bounded by the `p`-th power of `W_p (A, B)` enlarged by the two quantization displacements. -/
theorem ofReal_integral_add_integral_le_wassersteinEDist_add_rpow (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {Q₁ Q₂ : Y → Y} (hQ₁ : Measurable Q₁) (hQ₂ : Measurable Q₂) {f₁ f₂ : Y → ℝ}
    (hf : ∀ y y', f₁ y + f₂ y' ≤ dist (Q₁ y) (Q₂ y') ^ p.toReal)
    {A B : Measure Y}
    (hf₁ : Integrable f₁ A) (hf₂ : Integrable f₂ B) :
    ENNReal.ofReal (∫ y, f₁ y ∂A + ∫ y, f₂ y ∂B) ≤
      (wassersteinEDist p A B + (eLpNorm (fun y ↦ edist y (Q₁ y)) p A +
        eLpNorm (fun y ↦ edist y (Q₂ y)) p B)) ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set e := eLpNorm (fun y ↦ edist y (Q₁ y)) p A + eLpNorm (fun y ↦ edist y (Q₂ y)) p B
  set D := ENNReal.ofReal (∫ y, f₁ y ∂A + ∫ y, f₂ y ∂B)
  -- the pair is feasible for the cost read at the quantized points
  have hfeas :
      DualFeasible (fun z : Y × Y ↦ ((edist (Q₁ z.1) (Q₂ z.2) ^ p.toReal : ℝ≥0∞) : EReal))
        f₁ f₂ := by
    refine dualFeasible_iff_ofReal_add_le.2 fun y y' ↦ ?_
    rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr.le]
    exact ENNReal.ofReal_le_ofReal (hf y y')
  have hmeas : Measurable fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2) :=
    (hQ₁.comp measurable_fst).edist (hQ₂.comp measurable_snd)
  have hd₁ : Measurable fun y ↦ edist y (Q₁ y) := measurable_id.edist hQ₁
  have hd₂ : Measurable fun y ↦ edist y (Q₂ y) := measurable_id.edist hQ₂
  -- against each coupling, weak duality and Minkowski's inequality bound the dual value
  have key : ∀ γ, IsCoupling γ A B →
      D ^ p.toReal⁻¹ ≤ eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p γ + e := by
    intro γ hγ
    have hdual := hfeas.ofReal_kantorovichDualValue_le_lintegral hf₁ hf₂ hγ
    rw [kantorovichDualValue_def, ← eLpNorm_rpow_eq_lintegral hp0 hp hmeas.aemeasurable] at hdual
    have hle : D ^ p.toReal⁻¹ ≤ eLpNorm (fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2)) p γ :=
      calc D ^ p.toReal⁻¹
          ≤ (eLpNorm (fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2)) p γ ^ p.toReal) ^ p.toReal⁻¹ := by
            gcongr
        _ = _ := ENNReal.rpow_rpow_inv hr.ne' _
    -- move each quantized point back to the point it quantizes
    have hmarg₁ : eLpNorm (fun z : Y × Y ↦ edist z.1 (Q₁ z.1)) p γ
        = eLpNorm (fun y ↦ edist y (Q₁ y)) p A :=
      eLpNorm_comp_measurePreserving hd₁.aestronglyMeasurable hγ.measurePreserving_fst
    have hmarg₂ : eLpNorm (fun z : Y × Y ↦ edist z.2 (Q₂ z.2)) p γ
        = eLpNorm (fun y ↦ edist y (Q₂ y)) p B :=
      eLpNorm_comp_measurePreserving hd₂.aestronglyMeasurable hγ.measurePreserving_snd
    refine hle.trans ?_
    calc eLpNorm (fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2)) p γ
        ≤ eLpNorm ((fun z : Y × Y ↦ edist z.1 z.2) +
            ((fun z : Y × Y ↦ edist z.1 (Q₁ z.1)) + fun z ↦ edist z.2 (Q₂ z.2))) p γ := by
          refine eLpNorm_mono_enorm hmeas.aestronglyMeasurable fun z ↦ ?_
          simp only [enorm_eq_self, Pi.add_apply]
          calc edist (Q₁ z.1) (Q₂ z.2)
              ≤ edist (Q₁ z.1) z.1 + edist z.1 z.2 + edist z.2 (Q₂ z.2) :=
                edist_triangle4 _ _ _ _
            _ = edist z.1 z.2 + (edist z.1 (Q₁ z.1) + edist z.2 (Q₂ z.2)) := by
                rw [edist_comm (Q₁ z.1)]
                ring
      _ ≤ eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p γ +
            (eLpNorm (fun z : Y × Y ↦ edist z.1 (Q₁ z.1)) p γ +
              eLpNorm (fun z : Y × Y ↦ edist z.2 (Q₂ z.2)) p γ) :=
          (eLpNorm_add_le hp1).trans (add_le_add le_rfl (eLpNorm_add_le hp1))
      _ = eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p γ + e := by rw [hmarg₁, hmarg₂]
  have hroot : D ^ p.toReal⁻¹ ≤ wassersteinEDist p A B + e :=
    tsub_le_iff_right.1 (le_wassersteinEDist fun γ hγ ↦ tsub_le_iff_right.2 (key γ hγ))
  calc D = (D ^ p.toReal⁻¹) ^ p.toReal := (ENNReal.rpow_inv_rpow hr.ne' D).symm
    _ ≤ (wassersteinEDist p A B + e) ^ p.toReal := by gcongr

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A coupling realizing `W₂ (μ, ν) < ∞` is concentrated on a measurable set that is cyclically
monotone for the quadratic cost. -/
theorem exists_isCyclicallyMonotone_of_eLpNorm_eq {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {π : Measure (E × E)}
    (hπ : IsCoupling π μ ν)
    (hopt : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 π = wassersteinEDist 2 μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ S : Set (E × E), MeasurableSet S ∧
      IsCyclicallyMonotone (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 / 2) S ∧ π Sᶜ = 0 := by
  have h2 := (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top).2 ⟨hπ, hopt⟩
  rw [ENNReal.toReal_ofNat] at h2
  have hq := isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two h2
  -- The half-squared cost is dominated by the squared distance, whose integral is `W₂ ^ 2`.
  have hcost : transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
    rw [← hq.lintegral_eq]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun z ↦
      (le_mul_of_one_le_left zero_le one_le_two).trans_eq
        (edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two z).symm)
    have h2' := h2.lintegral_edist_rpow_eq measurable_edist two_ne_zero ENNReal.ofNat_ne_top
    rw [ENNReal.toReal_ofNat] at h2'
    rw [h2']
    exact ENNReal.rpow_ne_top_of_nonneg zero_le_two hfin
  obtain ⟨S, hS, hcm, hπS⟩ :=
    hq.exists_isCyclicallyMonotone_of_lowerSemicontinuous
      continuous_ofReal_norm_sub_sq_div_two.lowerSemicontinuous hcost
  exact ⟨S, hS, (isCyclicallyMonotone_ofReal_iff fun _ ↦ by positivity).1 hcm, hπS⟩

end Quadratic

end TauCeti
