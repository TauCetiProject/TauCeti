/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import TauCeti.Dynamics.Ergodic.Action.Koopman
import TauCeti.Analysis.Semigroups.Group.MeanErgodic
import TauCeti.Dynamics.Ergodic.Action.Eigenfunction
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Group.ErgodicExtreme

/-!
# Ergodicity and the Koopman group of a flow

Let `ℝ` act jointly measurably on `X`, preserving a finite measure `μ`, and let `U_t` be the
Koopman group on complex `L²(μ)`, `U_t f = f ∘ (t +ᵥ ·)` (`TauCeti.koopmanGroup`).

The action is ergodic exactly when the only vectors of `L²(μ)` fixed by the Koopman group are the
almost everywhere constant functions (`TauCeti.ergodicVAdd_iff_forall_koopmanGroup_eq`): a fixed
vector of an ergodic action is almost invariant, hence constant, and conversely the indicator of an
almost invariant set is a fixed vector.

For an ergodic action preserving a probability measure, the projection onto the fixed vectors is
therefore `f ↦ (∫ f) 1`, and the continuous-time mean ergodic theorem
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_inner`) gives the limit of
the averaged correlations: `T⁻¹ ∫₀ᵀ ⟪g, U_t f⟫ dt → (∫ f) conj (∫ g)`
(`TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd`).

## Main results

* `TauCeti.exists_ae_eq_const_of_koopmanGroup_eq`: Koopman-fixed vectors of an ergodic action are
  almost everywhere constant;
* `TauCeti.ergodicVAdd_of_forall_koopmanGroup_eq`, `TauCeti.ergodicVAdd_iff_forall_koopmanGroup_eq`:
  the converse, and the characterisation of ergodicity by Koopman-fixed vectors;
* `TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd`: averaged correlations of an ergodic
  action.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal ComplexConjugate InnerProductSpace

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X]
  {μ : Measure X} [SFinite μ]

/-- **Koopman-fixed vectors of an ergodic action are constant.** For an ergodic jointly
measurable action of `ℝ` preserving `μ`, a vector of complex `L²(μ)` fixed by the Koopman group is
almost everywhere constant. -/
theorem exists_ae_eq_const_of_koopmanGroup_eq [ErgodicVAdd ℝ X μ] (u : Lp ℂ 2 μ)
    (hu : ∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t u = u) :
    ∃ c : ℂ, u =ᵐ[μ] Function.const X c := by
  have hmem : u ∈ (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top).eigenspace
      (koopmanGroup_isUnitary μ ℂ).isComplexLinear 0 :=
    (Semigroups.StronglyContinuousGroup.mem_eigenspace_iff _ _ _ _).2 fun t =>
      (Eq.congr_left (hu t)).2 (by simp)
  refine ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀ ℝ
    (Lp.aestronglyMeasurable u).aemeasurable.nullMeasurable fun t => ?_
  filter_upwards [(mem_eigenspace_koopmanGroup_iff 0 u).1 hmem t] with x hx
  simpa using hx

/-- **Ergodicity from Koopman-fixed vectors.** A jointly measurable action of `ℝ` preserving a
finite measure `μ` is ergodic if every vector of complex `L²(μ)` fixed by the Koopman group is
almost everywhere constant. -/
theorem ergodicVAdd_of_forall_koopmanGroup_eq [VAddInvariantMeasure ℝ X μ] [IsFiniteMeasure μ]
    (h : ∀ u : Lp ℂ 2 μ, (∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t u = u) →
      ∃ c : ℂ, u =ᵐ[μ] Function.const X c) :
    ErgodicVAdd ℝ X μ where
  aeconst_of_forall_preimage_vadd_ae_eq {s} hs hinv := by
    -- the indicator of `s` is a Koopman-fixed vector, hence almost everywhere constant
    have hcoe := indicatorConstLp_coeFn (p := 2) (μ := μ) (c := (1 : ℂ)) (hs := hs)
      (hμs := measure_ne_top μ s)
    obtain ⟨c, hc⟩ := h (indicatorConstLp 2 hs (measure_ne_top μ s) 1) fun t => by
      rw [koopmanGroup_indicatorConstLp]
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (c := (1 : ℂ))
          (hs := hs.preimage (measurable_const_vadd t)) (hμs := by
            rw [(measurePreserving_vadd t μ).measure_preimage hs.nullMeasurableSet]
            exact measure_ne_top μ s), hcoe,
        indicator_ae_eq_of_ae_eq_set (f := fun _ : X => (1 : ℂ)) (hinv t)] with x h₁ h₂ h₃
      rw [h₁, h₂, h₃]
    exact EventuallyEmptyOrUniv.of_indicator_const
      (eventuallyConst_iff_exists_eventuallyEq.2 ⟨c, hcoe.symm.trans hc⟩) one_ne_zero

/-- **Ergodicity and Koopman-fixed vectors.** A jointly measurable action of `ℝ` preserving a
finite measure `μ` is ergodic exactly when every vector of complex `L²(μ)` fixed by the Koopman
group is almost everywhere constant. -/
theorem ergodicVAdd_iff_forall_koopmanGroup_eq [VAddInvariantMeasure ℝ X μ] [IsFiniteMeasure μ] :
    ErgodicVAdd ℝ X μ ↔ ∀ u : Lp ℂ 2 μ,
      (∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t u = u) →
        ∃ c : ℂ, u =ᵐ[μ] Function.const X c :=
  ⟨fun _ => exists_ae_eq_const_of_koopmanGroup_eq, ergodicVAdd_of_forall_koopmanGroup_eq⟩

/-- **Averaged correlations of an ergodic action.** For an ergodic jointly measurable action of
`ℝ` preserving a probability measure `μ`, and `f g` in complex `L²(μ)`, the averages
`T⁻¹ ∫₀ᵀ ⟪g, U_t f⟫ dt` of the Koopman correlations tend to `(∫ f) conj (∫ g)`. -/
theorem tendsto_average_inner_koopmanGroup_of_ergodicVAdd [IsProbabilityMeasure μ]
    [ErgodicVAdd ℝ X μ] (f g : Lp ℂ 2 μ) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        ⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ) atTop
      (𝓝 ((∫ x, f x ∂μ) * conj (∫ x, g x ∂μ))) := by
  set U := koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top
  have hU : U.IsUnitary := koopmanGroup_isUnitary μ ℂ
  have := Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_fixedSubmodule U
    hU.isComplexLinear
  set K := U.fixedSubmodule hU.isComplexLinear
  -- the projection of `f` onto the fixed vectors is the constant `∫ f`
  have hproj : K.starProjection f = Lp.const 2 μ (∫ x, f x ∂μ) := by
    obtain ⟨c, hc⟩ := exists_ae_eq_const_of_koopmanGroup_eq _
      ((Semigroups.StronglyContinuousGroup.mem_fixedSubmodule_iff U _ _).1
        (K.starProjection_apply_mem f))
    have hPc : K.starProjection f = Lp.const 2 μ c := Lp.ext (hc.trans (Lp.coeFn_const 2 μ c).symm)
    have hone : Lp.const 2 μ (1 : ℂ) ∈ K :=
      (Semigroups.StronglyContinuousGroup.mem_fixedSubmodule_iff U _ _).2
        (koopmanGroup_const μ ℂ 2 ENNReal.ofNat_ne_top 1)
    have h := K.inner_starProjection_left_eq_right (Lp.const 2 μ (1 : ℂ)) f
    rw [K.starProjection_eq_self_iff.2 hone, hPc, L2.inner_const_left, L2.inner_const_left,
      integral_congr_ae (Lp.coeFn_const 2 μ c)] at h
    rw [hPc]
    congr 1
    simpa using h.symm
  convert hU.tendsto_average_inner f g using 2
  rw [hproj, L2.inner_const_right, RCLike.inner_apply, mul_comm]

end TauCeti
