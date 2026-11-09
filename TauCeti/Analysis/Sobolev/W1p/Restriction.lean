/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Restriction of first-order Sobolev functions

A weakly differentiable function on an open set remains weakly differentiable on every smaller
open set.  This file packages that operation as the contractive continuous linear map
`TauCeti.W1p.restrictL`.  Its value and weak gradient are represented by the same functions on
the smaller domain, and restriction is functorial.

Restriction is the basic localization operation for Sobolev spaces.  In particular, it lets
interior regularity arguments pass from a weak solution on `Ω` to smaller open sets.

## Main declarations

* `TauCeti.W1p.restrictL`: the contractive restriction map from `W^{1,p}(Ω)` to
  `W^{1,p}(U)` for `U ⊆ Ω`.
* `TauCeti.W1p.value_restrictL` and `TauCeti.W1p.gradient_restrictL`: restriction commutes with
  the value and weak-gradient projections; their `_ae` variants identify representatives.
* `TauCeti.W1p.value_restrictL_ofTestFunctionₗ_ae`: a restricted test function has its original
  value almost everywhere on the smaller open set.
* `TauCeti.W1p.restrictL_self` and `TauCeti.W1p.restrictL_restrictL`: restriction is functorial.
* `TauCeti.W1p.setIntegral_norm_gradient_sub_sq_eq`: the `L²` distance on the smaller set between
  the weak gradients of a function and of a function defined only there.
* `TauCeti.W1p.continuous_setAverage_value`: the mean of the value component over a fixed
  finite-measure subset depends continuously on the Sobolev function.
* `TauCeti.W1p.isClosed_setOf_eLpNorm_value_sub_le`: for a continuous centering `m`, the bound
  `‖w - m w‖_{L^q(U)} ≤ C ‖∇w‖_{Lᵖ(U)}` cuts out a closed subset of `W^{1,p}(U)`, for every `q`;
  `TauCeti.W1p.isClosed_setOf_eLpNorm_value_sub_setAverage_le` takes `m w = ⨍_S w`.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {S : Set E}

/-! ### Restriction of ambient jets -/

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- Restriction of an `Lᵖ` value-gradient jet to a smaller open set. -/
def Sobolev1JetLp.restrictL (hU : U ≤ Omega) :
    Sobolev1JetLp mu Omega p →L[ℝ] Sobolev1JetLp mu U p :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Restricting an ambient jet keeps the same representative on the smaller open set. -/
theorem Sobolev1JetLp.coeFn_restrictL (hU : U ≤ Omega) (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.restrictL hU J =ᵐ[mu.restrict U] J := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (by simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Restriction of ambient jets does not increase the `Lᵖ` norm. -/
theorem Sobolev1JetLp.norm_restrictL_le (hU : U ≤ Omega) (J : Sobolev1JetLp mu Omega p) :
    ‖Sobolev1JetLp.restrictL hU J‖ ≤ ‖J‖ := by
  have hop : ‖Sobolev1JetLp.restrictL (mu := mu) (p := p) hU‖ ≤ 1 := by
    simpa only [Sobolev1JetLp.restrictL, ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E := Sobolev1Jet E) (p := p)
        (μ := mu.restrict U) (ν := mu.restrict Omega) (c := 1) (by simp)
        (by simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
  simpa only [one_mul] using
    (Sobolev1JetLp.restrictL (mu := mu) (p := p) hU).le_of_opNorm_le hop J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- The value component of a restricted ambient jet is the restriction of its value component. -/
@[simp]
theorem Sobolev1JetLp.value_restrictL (hU : U ≤ Omega) (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.value (Sobolev1JetLp.restrictL hU J) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
        (Sobolev1JetLp.value J) := by
  apply Lp.ext
  have hmeasure : mu.restrict U ≤ (1 : ENNReal) • mu.restrict Omega := by
    simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  have hvalue := (Sobolev1JetLp.value_apply_ae J).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  filter_upwards [Sobolev1JetLp.value_apply_ae (Sobolev1JetLp.restrictL hU J),
    Sobolev1JetLp.coeFn_restrictL hU J,
    Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hmeasure (Sobolev1JetLp.value J), hvalue]
    with x hleft hrestrict hright hvalue
  rw [hleft, hrestrict, hright, hvalue]

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- The gradient component of a restricted ambient jet is the restriction of its gradient
component. -/
@[simp]
theorem Sobolev1JetLp.gradient_restrictL (hU : U ≤ Omega) (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.gradient (Sobolev1JetLp.restrictL hU J) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
        (Sobolev1JetLp.gradient J) := by
  apply Lp.ext
  have hmeasure : mu.restrict U ≤ (1 : ENNReal) • mu.restrict Omega := by
    simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  have hgradient := (Sobolev1JetLp.gradient_apply_ae J).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  filter_upwards [Sobolev1JetLp.gradient_apply_ae (Sobolev1JetLp.restrictL hU J),
    Sobolev1JetLp.coeFn_restrictL hU J,
    Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hmeasure (Sobolev1JetLp.gradient J), hgradient]
    with x hleft hrestrict hright hgradient
  rw [hleft, hrestrict, hright, hgradient]

/-! ### Restriction of Sobolev functions -/

/-- The restricted jet still satisfies the weak-derivative identity. -/
private theorem Sobolev1JetLp.restrictL_mem_w1pSubmodule (hU : U ≤ Omega)
    (u : W1p mu Omega p) :
    Sobolev1JetLp.restrictL hU (u : Sobolev1JetLp mu Omega p) ∈ w1pSubmodule mu U p := by
  rw [mem_w1pSubmodule_iff_hasWeakFDerivOn]
  let J := Sobolev1JetLp.restrictL hU (u : Sobolev1JetLp mu Omega p)
  have hJ := Sobolev1JetLp.coeFn_restrictL (mu := mu) (p := p) hU
    (u : Sobolev1JetLp mu Omega p)
  have hu_value := (W1p.value_apply_ae u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  have hvalue : Sobolev1JetLp.value J =ᵐ[mu.restrict U] W1p.value u := by
    filter_upwards [Sobolev1JetLp.value_apply_ae J, hu_value, hJ] with x hJv huv hJu
    rw [hJv, huv, hJu]
  have hu_gradient := (W1p.gradient_apply_ae u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  have hgradient : Sobolev1JetLp.gradient J =ᵐ[mu.restrict U] W1p.gradient u := by
    filter_upwards [Sobolev1JetLp.gradient_apply_ae J, hu_gradient, hJ]
      with x hJg hug hJu
    rw [hJg, hug, hJu]
  refine ((W1p.hasWeakFDerivOn u).mono hU).congr_ae hvalue.symm |>.congr_ae_deriv ?_
  filter_upwards [hgradient] with x hx
  rw [Sobolev1JetLp.candidateWeakFDeriv_def, hx]

/-- **Restriction of first-order Sobolev functions.**  If `U ⊆ Ω`, this is the continuous
linear map `W^{1,p}(Ω) → W^{1,p}(U)` obtained by restricting both the value and weak gradient.
It has operator norm at most one. -/
def W1p.restrictL (hU : U ≤ Omega) : W1p mu Omega p →L[ℝ] W1p mu U p :=
  ContinuousLinearMap.codRestrict
    ((Sobolev1JetLp.restrictL hU).comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL)
    (w1pSubmodule mu U p).toSubmodule
    (Sobolev1JetLp.restrictL_mem_w1pSubmodule hU)

/-- The ambient jet of a restricted Sobolev function is the restriction of its ambient jet. -/
@[simp]
theorem W1p.coe_restrictL (hU : U ≤ Omega) (u : W1p mu Omega p) :
    ((W1p.restrictL hU u : W1p mu U p) : Sobolev1JetLp mu U p) =
      Sobolev1JetLp.restrictL hU (u : Sobolev1JetLp mu Omega p) :=
  (rfl)

/-- The value component of a restricted Sobolev function is the restriction of its value
component. -/
@[simp]
theorem W1p.value_restrictL (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.value (W1p.restrictL hU u) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (W1p.value u) := by
  rw [W1p.value_coe, W1p.coe_restrictL, Sobolev1JetLp.value_restrictL, W1p.value_coe]

/-- The gradient component of a restricted Sobolev function is the restriction of its gradient
component. -/
@[simp]
theorem W1p.gradient_restrictL (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.gradient (W1p.restrictL hU u) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (W1p.gradient u) := by
  rw [W1p.gradient_coe, W1p.coe_restrictL, Sobolev1JetLp.gradient_restrictL,
    W1p.gradient_coe]

/-- Restriction keeps the same value representative on the smaller open set. -/
theorem W1p.value_restrictL_ae (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict U] W1p.value u := by
  rw [W1p.value_restrictL]
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (by simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (W1p.value u)

/-- Restricting a test function from `Omega` to `U` preserves its value almost everywhere on
`U`. -/
theorem W1p.value_restrictL_ofTestFunctionₗ_ae (hU : U ≤ Omega) (φ : 𝓓(Omega, ℝ)) :
    W1p.value (W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p φ)) =ᵐ[mu.restrict U] φ :=
  (W1p.value_restrictL_ae hU _).trans
    (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hU)
      (W1p.value_ofTestFunctionₗ_ae φ))

/-- Restriction keeps the same weak-gradient representative on the smaller open set. -/
theorem W1p.gradient_restrictL_ae (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.gradient (W1p.restrictL hU u) =ᵐ[mu.restrict U] W1p.gradient u := by
  rw [W1p.gradient_restrictL]
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (by simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (W1p.gradient u)

/-- Restriction does not increase the Sobolev norm. -/
theorem W1p.norm_restrictL_le (hU : U ≤ Omega) (u : W1p mu Omega p) :
    ‖W1p.restrictL hU u‖ ≤ ‖u‖ :=
  Sobolev1JetLp.norm_restrictL_le hU (u : Sobolev1JetLp mu Omega p)

/-- The restriction operator has norm at most one. -/
theorem W1p.norm_restrictL_le_one (hU : U ≤ Omega) :
    ‖W1p.restrictL (mu := mu) (p := p) hU‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using W1p.norm_restrictL_le hU u

/-- Restricting a Sobolev function to its original domain does nothing. -/
@[simp]
theorem W1p.restrictL_self (u : W1p mu Omega p) : W1p.restrictL le_rfl u = u := by
  apply W1p.ext_value
  apply Lp.ext
  exact W1p.value_restrictL_ae le_rfl u

/-- Restriction is functorial: restricting from `Ω` to `U` and then to `V` agrees with direct
restriction from `Ω` to `V`. -/
@[simp]
theorem W1p.restrictL_restrictL (hU : U ≤ Omega) (hV : V ≤ U) (u : W1p mu Omega p) :
    W1p.restrictL hV (W1p.restrictL hU u) = W1p.restrictL (hV.trans hU) u := by
  apply W1p.ext_value
  apply Lp.ext
  have hsecond : W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict V] W1p.value u :=
    (W1p.value_restrictL_ae hU u).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hV)))
  exact ((W1p.value_restrictL_ae hV (W1p.restrictL hU u)).trans hsecond).trans
    (W1p.value_restrictL_ae (hV.trans hU) u).symm

/-- The squared `L²(U)` distance between the weak gradients of `u ∈ W^{1,2}(Ω)` and
`w ∈ W^{1,2}(U)` is the squared norm of the weak gradient of the difference of the restriction of
`u` to `U` and `w`. -/
theorem W1p.setIntegral_norm_gradient_sub_sq_eq (hU : U ≤ Omega) (u : W1p mu Omega 2)
    (w : W1p mu U 2) :
    ∫ x in U, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ∂mu =
      ‖W1p.gradient (W1p.restrictL hU u - w)‖ ^ 2 := by
  have hsub : W1p.gradient (W1p.restrictL hU u - w) =
      W1p.gradient (W1p.restrictL hU u) - W1p.gradient w := by
    simp only [← W1p.gradientL_apply, map_sub]
  rw [← MeasureTheory.Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_restrictL_ae hU u,
    Lp.coeFn_sub (W1p.gradient (W1p.restrictL hU u)) (W1p.gradient w)] with x h1 h2
  rw [hsub, h2, Pi.sub_apply, h1]

/-! ### Subset averages -/

omit [FiniteDimensional ℝ E] in
/-- The mean of the value of a first-order Sobolev function over a fixed subset of finite
measure depends continuously on the function. -/
theorem W1p.continuous_setAverage_value (hSU : S ⊆ (U : Set E))
    (hSfin : mu S ≠ ∞) :
    Continuous fun v : W1p mu U p => ⨍ y in S, W1p.value v y ∂mu := by
  have hrs : (mu.restrict (U : Set E)).restrict S = mu.restrict S :=
    Measure.restrict_restrict_of_subset hSU
  have hmeas : (mu.restrict (U : Set E)) S = mu S := by
    rw [← Measure.restrict_apply_univ, hrs, Measure.restrict_apply_univ]
  have hEq : ∀ v : W1p mu U p, (⨍ y in S, W1p.value v y ∂mu) =
      (mu.real S)⁻¹ * ∫ y in S, W1p.valueL v y ∂(mu.restrict (U : Set E)) := fun v => by
    rw [setAverage_eq, smul_eq_mul, W1p.valueL_apply, hrs]
  have hSlt : (mu.restrict (U : Set E)) S < ∞ := by
    rw [hmeas]
    exact hSfin.lt_top
  have hF : Continuous fun f : Lp ℝ p (mu.restrict (U : Set E)) =>
      ∫ y in S, f y ∂(mu.restrict (U : Set E)) :=
    (Set.setIntegralLp (𝕜 := ℝ) (F := ℝ) (μ := mu.restrict (U : Set E)) (p := p) S
      hSlt).continuous.congr fun f => Set.setIntegralLp_apply (𝕜 := ℝ) S hSlt f
  simp only [hEq]
  exact continuous_const.mul
    (hF.comp' (W1p.valueL (mu := mu) (Omega := U) (p := p)).continuous)

/-! ### Lower semicontinuity of centered norms -/

omit [FiniteDimensional ℝ E] in
/-- **Lower semicontinuity of a centered `L^q` norm.** If `m : W^{1,p}(U) → ℝ` is continuous, then
for every exponent `q` and constant `C` the Sobolev functions `w ∈ W^{1,p}(U)` with
`‖w - m w‖_{L^q(U)} ≤ C ‖∇w‖_{Lᵖ(U)}` form a closed set.

The left-hand side need not be continuous in `w`: `W^{1,p}` convergence controls the values only in
`Lᵖ`, which says nothing about `L^q` norms for `q > p`. It is lower semicontinuous instead:
convergence in `W^{1,p}(U)` gives an almost everywhere convergent subsequence of the values, and
Fatou's lemma applies. -/
theorem W1p.isClosed_setOf_eLpNorm_value_sub_le {m : W1p mu U p → ℝ} (hm : Continuous m)
    (q : ℝ≥0∞) (C : ℝ≥0) :
    IsClosed {w : W1p mu U p |
      eLpNorm (fun x ↦ W1p.value w x - m w) q (mu.restrict U) ≤ C * ‖W1p.gradient w‖ₑ} := by
  refine IsSeqClosed.isClosed fun v u hv hvu => ?_
  have hvalue : Tendsto (fun k => W1p.value (v k)) atTop (𝓝 (W1p.value u)) := by
    simpa only [W1p.valueL_apply, Function.comp_def] using
      ((map_continuous (W1p.valueL (mu := mu) (Omega := U) (p := p))).tendsto u).comp hvu
  have hgradient : Tendsto (fun k => W1p.gradient (v k)) atTop (𝓝 (W1p.gradient u)) := by
    simpa only [W1p.gradientL_apply, Function.comp_def] using
      ((map_continuous (W1p.gradientL (mu := mu) (Omega := U) (p := p))).tendsto u).comp hvu
  have hbound : Tendsto (fun k => (C : ℝ≥0∞) * ‖W1p.gradient (v k)‖ₑ) atTop
      (𝓝 ((C : ℝ≥0∞) * ‖W1p.gradient u‖ₑ)) :=
    ENNReal.Tendsto.const_mul ((continuous_enorm.tendsto _).comp hgradient)
      (Or.inr ENNReal.coe_ne_top)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvalue).exists_seq_tendsto_ae
  have hae' : ∀ᵐ x ∂mu.restrict U, Tendsto (fun i => W1p.value (v (ns i)) x - m (v (ns i)))
      atTop (𝓝 (W1p.value u x - m u)) :=
    hae.mono fun x hx => hx.sub (((hm.tendsto u).comp hvu).comp hns.tendsto_atTop)
  calc eLpNorm (fun x ↦ W1p.value u x - m u) q (mu.restrict U)
      ≤ atTop.liminf fun i => eLpNorm (fun x ↦ W1p.value (v (ns i)) x - m (v (ns i))) q
          (mu.restrict U) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun _ => (Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const) _
          ((Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const) hae'
    _ ≤ atTop.liminf fun i => (C : ℝ≥0∞) * ‖W1p.gradient (v (ns i))‖ₑ :=
        liminf_le_liminf (.of_forall fun i => hv (ns i))
    _ = (C : ℝ≥0∞) * ‖W1p.gradient u‖ₑ := (hbound.comp hns.tendsto_atTop).liminf_eq

omit [FiniteDimensional ℝ E] in
/-- **Lower semicontinuity of the deviation from a mean.** If `S ⊆ U` has finite measure, then
for every exponent `q` and constant `C` the Sobolev functions `w ∈ W^{1,p}(U)` with
`‖w - ⨍_S w‖_{L^q(U)} ≤ C ‖∇w‖_{Lᵖ(U)}` form a closed set. -/
theorem W1p.isClosed_setOf_eLpNorm_value_sub_setAverage_le (hSU : S ⊆ (U : Set E))
    (hSfin : mu S ≠ ∞) (q : ℝ≥0∞) (C : ℝ≥0) :
    IsClosed {w : W1p mu U p |
      eLpNorm (fun x ↦ W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) q (mu.restrict U) ≤
        C * ‖W1p.gradient w‖ₑ} :=
  W1p.isClosed_setOf_eLpNorm_value_sub_le (W1p.continuous_setAverage_value hSU hSfin) q C

end TauCeti
