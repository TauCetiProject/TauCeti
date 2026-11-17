/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Vector.InnerProduct
public import TauCeti.Probability.Process.Filtration.AmbientNullAugmentation
public import TauCeti.Probability.Process.Filtration.Comp
public import TauCeti.Probability.Process.Filtration.Natural
import TauCeti.Probability.Independence.Completion
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Independence.Sup

/-!
# Vector Brownian motion relative to a filtration

Defines `IsFilteredPreBrownian` and `IsFilteredBrownian` for `E`-valued processes relative to a
filtration `ℱ`: `W` satisfies `IsPreBrownian` (resp. `IsBrownian`), is adapted to `ℱ`, and every
increment `W t - W s` (`s ≤ t`) is independent of `ℱ s`.

Coordinatewise `IsFilteredPreBrownianReal` alone does not imply `IsFilteredPreBrownian`, nor does
marginal independence of each `⟪b i, W t - W s⟫` from `ℱ s` at a fixed `(s, t)` yield joint
independence without subdividing `[s, t]`; `isFilteredPreBrownian_iff_orthonormalBasis` packages
joint independence of the coordinate increment vector from `ℱ s`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1, §2.7.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999,
  Chapter I, §4; Chapter III, §2.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {Ω ι E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Defs

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → E}

/-- `W : ℝ≥0 → Ω → E` is a **vector pre-Brownian motion relative to `ℱ`** under `P` if it is
`IsPreBrownian`, adapted to `ℱ`, with increments `W t - W s` (`s ≤ t`) independent of `ℱ s`. -/
structure IsFilteredPreBrownian (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownian W P where
  /-- `W t` is `ℱ t`-measurable for every `t`. -/
  adapted : Adapted ℱ W
  /-- For `s ≤ t`, the increment `W t - W s` is independent of `ℱ s`. -/
  indep_sub ⦃s t : ℝ≥0⦄ : s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P

/-- `W : ℝ≥0 → Ω → E` is a **vector Brownian motion relative to `ℱ`** under `P` if it is
`IsFilteredPreBrownian` with `P`-almost surely continuous sample paths. -/
structure IsFilteredBrownian (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop extends IsFilteredPreBrownian ℱ W P where
  /-- Almost every sample path `t ↦ W t ω` is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (W · ω)

namespace IsFilteredPreBrownian

/-- Every time marginal of a filtered vector pre-Brownian motion is ambient-measurable. -/
theorem measurable (hW : IsFilteredPreBrownian ℱ W P) (t : ℝ≥0) : Measurable (W t) :=
  (hW.adapted t).mono (ℱ.le t) le_rfl

/-- Any `ℱ s`-measurable random variable is independent of `W t - W s` (`s ≤ t`). -/
theorem indepFun_sub (hW : IsFilteredPreBrownian ℱ W P) {s t : ℝ≥0} (hst : s ≤ t)
    {G : Type*} [MeasurableSpace G] {Y : Ω → G} (hY : Measurable[ℱ s] Y) :
    IndepFun Y (W t - W s) P :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_left (hW.indep_sub hst).symm hY.comap_le)

/-- Fixed-time a.s. equality preserves `IsFilteredPreBrownian` for `ℱ`-adapted modifications. -/
theorem congr (hW : IsFilteredPreBrownian ℱ W P) (hW' : Adapted ℱ W')
    (h : ∀ t, W t =ᵐ[P] W' t) : IsFilteredPreBrownian ℱ W' P :=
  ⟨hW.toIsPreBrownian.congr h, hW',
    fun s t hst ↦ (hW.indep_sub hst).comap_congr_left ((h t).sub (h s))⟩

/-- Indistinguishable adapted processes have the same `IsFilteredPreBrownian` property. -/
theorem congr_indist (hW : IsFilteredPreBrownian ℱ W P) (hW' : Adapted ℱ W')
    (h : W ≡ᵐ[P] W') : IsFilteredPreBrownian ℱ W' P :=
  hW.congr hW' fun t ↦ h.mono fun _ hω ↦ hω t

/-- `IsFilteredPreBrownian` passes to any smaller filtration `𝒢 ≤ ℱ` to which `W` is adapted. -/
theorem of_le (hW : IsFilteredPreBrownian ℱ W P) {𝒢 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ ℱ)
    (hadapt : Adapted 𝒢 W) : IsFilteredPreBrownian 𝒢 W P :=
  ⟨hW.toIsPreBrownian, hadapt, fun s _ hst ↦ indep_of_indep_of_le_right (hW.indep_sub hst) (h𝒢 s)⟩

/-- Adjoining ambient-measurable `P`-null sets to `ℱ` preserves `IsFilteredPreBrownian`. -/
theorem ambientNullAugmentation (hW : IsFilteredPreBrownian ℱ W P) :
    IsFilteredPreBrownian (ℱ.ambientNullAugmentation P) W P :=
  ⟨hW.toIsPreBrownian, fun t ↦ (hW.adapted t).mono (ℱ.le_ambientNullAugmentation P t) le_rfl,
    fun _ _ hst ↦ (hW.indep_sub hst).ambientNullAugmentation_right⟩

end IsFilteredPreBrownian

namespace IsFilteredBrownian

/-- Forget the filtration and view a filtered vector Brownian motion as an `IsBrownian` process. -/
theorem toIsBrownian (hW : IsFilteredBrownian ℱ W P) : IsBrownian W P :=
  ⟨hW.toIsPreBrownian, hW.ae_continuous⟩

/-- Package `IsBrownian` with adaptedness and increment independence into `IsFilteredBrownian`. -/
theorem of_isBrownian (hW : IsBrownian W P) (hadapt : Adapted ℱ W)
    (hindep : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P) :
    IsFilteredBrownian ℱ W P := ⟨⟨hW.toIsPreBrownian, hadapt, hindep⟩, hW.ae_continuous⟩

/-- Indistinguishable adapted processes share the `IsFilteredBrownian` property. -/
theorem congr_indist (hW : IsFilteredBrownian ℱ W P) (hW' : Adapted ℱ W')
    (h : W ≡ᵐ[P] W') : IsFilteredBrownian ℱ W' P :=
  ⟨hW.toIsFilteredPreBrownian.congr_indist hW' h, (hW.toIsBrownian.congr_indist h).ae_continuous⟩

/-- `IsFilteredBrownian` passes to any smaller filtration `𝒢 ≤ ℱ` to which `W` is adapted. -/
theorem of_le (hW : IsFilteredBrownian ℱ W P) {𝒢 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ ℱ)
    (hadapt : Adapted 𝒢 W) : IsFilteredBrownian 𝒢 W P :=
  ⟨hW.toIsFilteredPreBrownian.of_le h𝒢 hadapt, hW.ae_continuous⟩

/-- Adjoining ambient-measurable `P`-null sets to `ℱ` preserves `IsFilteredBrownian`. -/
theorem ambientNullAugmentation (hW : IsFilteredBrownian ℱ W P) :
    IsFilteredBrownian (ℱ.ambientNullAugmentation P) W P :=
  ⟨hW.toIsFilteredPreBrownian.ambientNullAugmentation, hW.ae_continuous⟩

end IsFilteredBrownian

/-- Equivalence between `IsFilteredBrownian ℱ W P` and `IsBrownian W P` plus `ℱ`-compatibility. -/
theorem isFilteredBrownian_iff : IsFilteredBrownian ℱ W P ↔ IsBrownian W P ∧ Adapted ℱ W ∧
    ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P :=
  ⟨fun h ↦ ⟨h.toIsBrownian, h.adapted, h.indep_sub⟩,
    fun ⟨hW, hadapt, hindep⟩ ↦ .of_isBrownian hW hadapt hindep⟩

/-- On `E = ℝ`, `IsFilteredPreBrownian` is equivalent to `IsFilteredPreBrownianReal`. -/
@[simp]
theorem isFilteredPreBrownian_real_iff {W : ℝ≥0 → Ω → ℝ} :
    IsFilteredPreBrownian ℱ W P ↔ IsFilteredPreBrownianReal ℱ W P :=
  ⟨fun h ↦ ⟨isPreBrownian_real_iff.mp h.toIsPreBrownian, h.adapted, h.indep_sub⟩,
    fun h ↦ ⟨isPreBrownian_real_iff.mpr h.toIsPreBrownianReal, h.adapted, h.indep_sub⟩⟩

/-- On `E = ℝ`, `IsFilteredBrownian` is equivalent to `IsBrownianReal` plus `ℱ`-compatibility. -/
theorem isFilteredBrownian_real_iff {W : ℝ≥0 → Ω → ℝ} :
    IsFilteredBrownian ℱ W P ↔ IsBrownianReal W P ∧ Adapted ℱ W ∧
      ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P := by
  rw [isFilteredBrownian_iff, isBrownian_real_iff]

end Defs

section Borel

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

/-- On `[Subsingleton E]`, every process on a probability space satisfies `IsFilteredBrownian`. -/
theorem IsFilteredBrownian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E) : IsFilteredBrownian ℱ W P :=
  .of_isBrownian (.of_subsingleton W)
    (fun t ↦ Subsingleton.elim (W t) (fun _ ↦ (0 : E)) ▸ measurable_const) fun s t _ ↦ by
      rw [Subsingleton.elim (W t - W s) (fun _ ↦ (0 : E)), MeasurableSpace.comap_const]
      exact indep_bot_left (ℱ s)

/-- On `[Subsingleton E]`, any process on a probability space satisfies `IsFilteredPreBrownian`. -/
theorem IsFilteredPreBrownian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E) : IsFilteredPreBrownian ℱ W P :=
  (IsFilteredBrownian.of_subsingleton ℱ W).toIsFilteredPreBrownian

/-- Completing the ambient space and adjoining all null events preserves `IsFilteredPreBrownian`. -/
theorem IsFilteredPreBrownian.nullAugment (hW : IsFilteredPreBrownian ℱ W P) :
    @IsFilteredPreBrownian (NullMeasurableSpace Ω P) E inferInstance _ _ _
      (ℱ.nullAugment P) (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω) P.completion :=
  ⟨hW.toIsPreBrownian.completion, fun t ↦ (hW.adapted t).mono (ℱ.le_nullAugment P t) le_rfl,
    fun _ _ hst ↦ (hW.indep_sub hst).nullAugment_right⟩

/-- Completing the ambient space and adjoining all null events preserves `IsFilteredBrownian`. -/
theorem IsFilteredBrownian.nullAugment (hW : IsFilteredBrownian ℱ W P) :
    @IsFilteredBrownian (NullMeasurableSpace Ω P) E inferInstance _ _ _
      (ℱ.nullAugment P) (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω) P.completion :=
  ⟨hW.toIsFilteredPreBrownian.nullAugment, hW.ae_continuous⟩

end Borel

section SecondCountable

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

section LinearIsometry

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- Linear isometry equivalences preserve `IsFilteredPreBrownian`. -/
theorem IsFilteredPreBrownian.comp_linearIsometryEquiv (hW : IsFilteredPreBrownian ℱ W P)
    (f : E ≃ₗᵢ[ℝ] F) : IsFilteredPreBrownian ℱ (fun t ω ↦ f (W t ω)) P where
  toIsPreBrownian := hW.toIsPreBrownian.comp_linearIsometryEquiv f
  adapted t := f.continuous.measurable.comp (hW.adapted t)
  indep_sub s t hst := indep_of_indep_of_le_left (hW.indep_sub hst)
    (MeasurableSpace.comap_le_comap_of_eq_comp f f.continuous.measurable (by ext ω; simp [map_sub]))

/-- `f ∘ W` satisfies `IsFilteredPreBrownian` iff `W` does, for `f : E ≃ₗᵢ[ℝ] F`. -/
theorem isFilteredPreBrownian_comp_linearIsometryEquiv_iff (f : E ≃ₗᵢ[ℝ] F) :
    IsFilteredPreBrownian ℱ (fun t ω ↦ f (W t ω)) P ↔ IsFilteredPreBrownian ℱ W P :=
  ⟨fun h ↦ by simpa using h.comp_linearIsometryEquiv f.symm, fun h ↦ h.comp_linearIsometryEquiv f⟩

/-- Linear isometry equivalences preserve `IsFilteredBrownian`. -/
theorem IsFilteredBrownian.comp_linearIsometryEquiv (hW : IsFilteredBrownian ℱ W P)
    (f : E ≃ₗᵢ[ℝ] F) : IsFilteredBrownian ℱ (fun t ω ↦ f (W t ω)) P :=
  ⟨hW.toIsFilteredPreBrownian.comp_linearIsometryEquiv f,
    (hW.toIsBrownian.comp_linearIsometryEquiv f).ae_continuous⟩

/-- `f ∘ W` satisfies `IsFilteredBrownian` iff `W` does, for `f : E ≃ₗᵢ[ℝ] F`. -/
theorem isFilteredBrownian_comp_linearIsometryEquiv_iff (f : E ≃ₗᵢ[ℝ] F) :
    IsFilteredBrownian ℱ (fun t ω ↦ f (W t ω)) P ↔ IsFilteredBrownian ℱ W P :=
  ⟨fun h ↦ by simpa using h.comp_linearIsometryEquiv f.symm, fun h ↦ h.comp_linearIsometryEquiv f⟩

end LinearIsometry

namespace IsFilteredPreBrownian

/-- For nonzero `u : E`, `‖u‖⁻¹ * ⟪u, W t ω⟫` satisfies `IsFilteredPreBrownianReal ℱ`. -/
theorem isFilteredPreBrownianReal_norm_inv_mul_inner (hW : IsFilteredPreBrownian ℱ W P) {u : E}
    (hu : u ≠ 0) : IsFilteredPreBrownianReal ℱ (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P where
  toIsPreBrownianReal := hW.isPreBrownianReal_norm_inv_mul_inner hu
  adapted t := (continuous_const.mul (innerSL ℝ u).continuous).measurable.comp (hW.adapted t)
  indep_sub s t hst := indep_of_indep_of_le_left (hW.indep_sub hst)
    (MeasurableSpace.comap_le_comap_of_eq_comp (fun x : E ↦ ‖u‖⁻¹ * ⟪u, x⟫)
      (continuous_const.mul (innerSL ℝ u).continuous).measurable
      (by ext ω; simp [inner_sub_right, mul_sub]))

/-- For a unit vector `u : E` (`‖u‖ = 1`), `⟪u, W t ω⟫` satisfies `IsFilteredPreBrownianReal ℱ`. -/
theorem isFilteredPreBrownianReal_inner_of_norm_eq_one (hW : IsFilteredPreBrownian ℱ W P) {u : E}
    (hu : ‖u‖ = 1) : IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪u, W t ω⟫) P := by
  simpa [hu] using
    hW.isFilteredPreBrownianReal_norm_inv_mul_inner (u := u) (norm_ne_zero_iff.mp (by simp [hu]))

/-- Negating a filtered vector pre-Brownian motion preserves `IsFilteredPreBrownian`. -/
theorem neg (hW : IsFilteredPreBrownian ℱ W P) : IsFilteredPreBrownian ℱ (-W) P :=
  hW.comp_linearIsometryEquiv (.neg ℝ)

/-- On a second-countable Borel space, a filtered vector pre-Brownian motion is strongly adapted. -/
theorem stronglyAdapted (hW : IsFilteredPreBrownian ℱ W P) : StronglyAdapted ℱ W :=
  fun t ↦ (hW.adapted t).stronglyMeasurable

/-- Every marginal `W t` is independent of any `ℱ 0`-measurable random variable `ξ`. -/
theorem indepFun_eval_of_measurable_zero (hW : IsFilteredPreBrownian ℱ W P) {G : Type*}
    [MeasurableSpace G] {ξ : Ω → G} (hξ : Measurable[ℱ 0] ξ) (t : ℝ≥0) : IndepFun (W t) ξ P :=
  ((IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le_right (hW.indep_sub (zero_le (a := t))) hξ.comap_le)).congr
    (hW.eval_zero_ae_eq_zero.mono fun _ hω ↦ by simp [hω]) .rfl

/-- Increments over `(s, t]` and `(u, v]` (`s ≤ u`, `t ≤ u`, `u ≤ v`) are independent. -/
theorem indepFun_sub_sub (hW : IsFilteredPreBrownian ℱ W P) {s t u v : ℝ≥0}
    (hsu : s ≤ u) (htu : t ≤ u) (huv : u ≤ v) : IndepFun (W t - W s) (W v - W u) P :=
  hW.adapted.indepFun_sub_sub hsu htu (hW.indep_sub huv)

/-- A filtered vector pre-Brownian motion has independent increments. -/
theorem hasIndepIncrements (hW : IsFilteredPreBrownian ℱ W P) : HasIndepIncrements W P :=
  have := hW.isProbabilityMeasure; hW.adapted.hasIndepIncrements hW.indep_sub

/-- For every `s`, the future increment process `(W t - W s)_{t ≥ s}` is independent of `ℱ s`. -/
theorem indep_comap_sub_Ici (hW : IsFilteredPreBrownian ℱ W P) (s : ℝ≥0) :
    Indep (.comap (fun ω (t : Set.Ici s) ↦ W t ω - W s ω) inferInstance) (ℱ s) P :=
  have := hW.isProbabilityMeasure; hW.adapted.indep_comap_sub_Ici hW.indep_sub s

/-- For every `s`, the shifted process `u ↦ W (s + u) - W s` is independent of `ℱ s`. -/
theorem indep_comap_shift (hW : IsFilteredPreBrownian ℱ W P) (s : ℝ≥0) :
    Indep (.comap (fun ω u ↦ W (s + u) ω - W s ω) inferInstance) (ℱ s) P :=
  have := hW.isProbabilityMeasure; hW.adapted.indep_comap_shift hW.indep_sub s

/-- Diffusive scaling `(√c)⁻¹ • W (c * t)` (`c ≠ 0`) preserves `IsFilteredPreBrownian`. -/
theorem smul (hW : IsFilteredPreBrownian ℱ W P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsFilteredPreBrownian (ℱ.comp (mul_right_mono (a := c)))
      (fun t ω ↦ (√(c : ℝ))⁻¹ • W (c * t) ω) P where
  toIsPreBrownian := hW.toIsPreBrownian.smul hc
  adapted t := (measurable_const_smul _).comp (hW.adapted.comp (mul_right_mono (a := c)) t)
  indep_sub s t hst := by
    rw [Filtration.comp_apply]
    exact indep_of_indep_of_le_left (hW.indep_sub (mul_right_mono (a := c) hst))
      (MeasurableSpace.comap_le_comap_of_eq_comp (fun x : E ↦ (√(c : ℝ))⁻¹ • x)
        (measurable_const_smul _) (by ext ω; simp [smul_sub]))

/-- `t ↦ W (t₀ + t) - W t₀` satisfies `IsFilteredPreBrownian` on `ℱ.comp (add_right_mono)`. -/
theorem shift (hW : IsFilteredPreBrownian ℱ W P) (t₀ : ℝ≥0) :
    IsFilteredPreBrownian (ℱ.comp (add_right_mono (a := t₀)))
      (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P where
  toIsPreBrownian := hW.toIsPreBrownian.shift t₀
  adapted t := (hW.adapted.comp (add_right_mono (a := t₀)) t).sub
    ((Filtration.measurable_comp_iff ℱ _ t).2 (hW.adapted.measurable_le le_self_add))
  indep_sub s t hst := by
    rw [Filtration.comp_apply, ← Pi.sub_def, ← Pi.sub_def, sub_sub_sub_cancel_right]
    exact hW.indep_sub (by gcongr)

/-- Right-continuing `ℱ` preserves `IsFilteredPreBrownian` under a.s. right-continuity. -/
theorem rightCont (hW : IsFilteredPreBrownian ℱ W P)
    (hcont : ∀ s, ∀ᵐ ω ∂P, ContinuousWithinAt (W · ω) (Set.Ioi s) s) :
    IsFilteredPreBrownian ℱ.rightCont W P :=
  ⟨hW.toIsPreBrownian, fun t ↦ (hW.adapted t).mono (ℱ.le_rightCont t) le_rfl,
    fun s _ hst ↦ have := hW.isProbabilityMeasure
      hW.adapted.indep_comap_sub_rightCont hst (fun _ _ hut ↦ hW.indep_sub hut) (hcont s)⟩

/-- Usual augmentation on the completed space preserves `IsFilteredPreBrownian`. -/
theorem rightCont_nullAugment (hW : IsFilteredPreBrownian ℱ W P)
    (hcont : ∀ s, ∀ᵐ ω ∂P, ContinuousWithinAt (W · ω) (Set.Ioi s) s) :
    @IsFilteredPreBrownian (NullMeasurableSpace Ω P) E inferInstance _ _ _
      (ℱ.nullAugment P).rightCont (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω) P.completion :=
  hW.nullAugment.rightCont hcont

/-- Any filtered vector pre-Brownian motion is filtered relative to its own natural filtration. -/
theorem natural (hW : IsFilteredPreBrownian ℱ W P) :
    IsFilteredPreBrownian (Filtration.natural W fun t ↦ (hW.measurable t).stronglyMeasurable) W P :=
  hW.of_le ((Filtration.natural_le_iff W _ ℱ).mpr hW.adapted)
    (Filtration.stronglyAdapted_natural _).adapted

/-- Enlarging `ℱ` by `𝒢 ≤ mΩ` independent of `⨆ t, ℱ t` preserves `IsFilteredPreBrownian`. -/
theorem sup_const (hW : IsFilteredPreBrownian ℱ W P) {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    (hIndep : Indep 𝒢 (⨆ t, ℱ t) P) :
    IsFilteredPreBrownian (ℱ ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P where
  toIsPreBrownian := hW.toIsPreBrownian
  adapted t := (hW.adapted t).mono le_sup_left le_rfl
  indep_sub s t hst := by
    have := hW.isProbabilityMeasure
    have hm : MeasurableSpace.comap (W t - W s) inferInstance ≤ ℱ t :=
      ((hW.adapted t).sub (hW.adapted.measurable_le hst)).comap_le
    exact (((hW.indep_sub hst).symm).sup_left (indep_of_indep_of_le_right hIndep <|
      sup_le ((ℱ.mono hst).trans (le_iSup ℱ t)) (hm.trans (le_iSup ℱ t)))
      (ℱ.le s) h𝒢 (hm.trans (ℱ.le t))).symm

end IsFilteredPreBrownian

namespace IsFilteredBrownian

/-- For nonzero `u : E`, `‖u‖⁻¹ * ⟪u, W t ω⟫` satisfies `IsFilteredBrownian ℱ`. -/
theorem isFilteredBrownian_norm_inv_mul_inner (hW : IsFilteredBrownian ℱ W P)
    {u : E} (hu : u ≠ 0) : IsFilteredBrownian ℱ (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P :=
  ⟨isFilteredPreBrownian_real_iff.mpr (hW.isFilteredPreBrownianReal_norm_inv_mul_inner hu),
    (hW.toIsBrownian.isBrownianReal_norm_inv_mul_inner hu).cont⟩

/-- For a unit vector `u : E` (`‖u‖ = 1`), `⟪u, W t ω⟫` satisfies `IsFilteredBrownian ℱ`. -/
theorem isFilteredBrownian_inner_of_norm_eq_one (hW : IsFilteredBrownian ℱ W P)
    {u : E} (hu : ‖u‖ = 1) : IsFilteredBrownian ℱ (fun t ω ↦ ⟪u, W t ω⟫) P :=
  ⟨isFilteredPreBrownian_real_iff.mpr (hW.isFilteredPreBrownianReal_inner_of_norm_eq_one hu),
    (hW.toIsBrownian.isBrownianReal_inner_of_norm_eq_one hu).cont⟩

/-- Negating a filtered vector Brownian motion preserves `IsFilteredBrownian`. -/
theorem neg (hW : IsFilteredBrownian ℱ W P) : IsFilteredBrownian ℱ (-W) P :=
  hW.comp_linearIsometryEquiv (.neg ℝ)

/-- On a second-countable Borel space, a filtered vector Brownian motion is strongly adapted. -/
theorem stronglyAdapted (hW : IsFilteredBrownian ℱ W P) : StronglyAdapted ℱ W :=
  hW.toIsFilteredPreBrownian.stronglyAdapted

/-- Diffusive scaling `(√c)⁻¹ • W (c * t)` (`c ≠ 0`) preserves `IsFilteredBrownian`. -/
theorem smul (hW : IsFilteredBrownian ℱ W P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsFilteredBrownian (ℱ.comp (mul_right_mono (a := c)))
      (fun t ω ↦ (√(c : ℝ))⁻¹ • W (c * t) ω) P :=
  ⟨hW.toIsFilteredPreBrownian.smul hc, (hW.toIsBrownian.smul hc).ae_continuous⟩

/-- `t ↦ W (t₀ + t) - W t₀` satisfies `IsFilteredBrownian` on `ℱ.comp (add_right_mono)`. -/
theorem shift (hW : IsFilteredBrownian ℱ W P) (t₀ : ℝ≥0) :
    IsFilteredBrownian (ℱ.comp (add_right_mono (a := t₀))) (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P :=
  ⟨hW.toIsFilteredPreBrownian.shift t₀, (hW.toIsBrownian.shift t₀).ae_continuous⟩

/-- Right-continuing the filtration preserves `IsFilteredBrownian`. -/
theorem rightCont (hW : IsFilteredBrownian ℱ W P) : IsFilteredBrownian ℱ.rightCont W P :=
  ⟨hW.toIsFilteredPreBrownian.rightCont
      fun _ ↦ hW.ae_continuous.mono fun _ hω ↦ hω.continuousAt.continuousWithinAt, hW.ae_continuous⟩

/-- Usual augmentation on the completed space preserves `IsFilteredBrownian`. -/
theorem rightCont_nullAugment (hW : IsFilteredBrownian ℱ W P) :
    @IsFilteredBrownian (NullMeasurableSpace Ω P) E inferInstance _ _ _
      (ℱ.nullAugment P).rightCont (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω) P.completion :=
  hW.nullAugment.rightCont

/-- Any filtered vector Brownian motion is filtered relative to its own natural filtration. -/
theorem natural (hW : IsFilteredBrownian ℱ W P) :
    IsFilteredBrownian (Filtration.natural W fun t ↦ (hW.measurable t).stronglyMeasurable) W P :=
  ⟨hW.toIsFilteredPreBrownian.natural, hW.ae_continuous⟩

/-- Enlarging `ℱ` by `𝒢 ≤ mΩ` independent of `⨆ t, ℱ t` preserves `IsFilteredBrownian`. -/
theorem sup_const (hW : IsFilteredBrownian ℱ W P) {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    (hIndep : Indep 𝒢 (⨆ t, ℱ t) P) : IsFilteredBrownian (ℱ ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P :=
  ⟨hW.toIsFilteredPreBrownian.sup_const h𝒢 hIndep, hW.ae_continuous⟩

end IsFilteredBrownian

end SecondCountable

section Complete

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] {W : ℝ≥0 → Ω → E}

/-- Strongly measurable `IsPreBrownian` processes are filtered in their natural filtration. -/
theorem IsPreBrownian.isFilteredPreBrownian_natural (hW : IsPreBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    IsFilteredPreBrownian (Filtration.natural W hmeas) W P where
  toIsPreBrownian := hW
  adapted t := (Filtration.stronglyAdapted_natural hmeas t).measurable
  indep_sub s t hst := by
    rw [Filtration.natural_eq_comap]
    exact indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).mp (hW.indepFun_shift s))
      (MeasurableSpace.comap_le_comap_of_eq_comp (fun x : ℝ≥0 → E ↦ x (t - s))
        (measurable_pi_apply _) (by ext ω; simp [add_tsub_cancel_of_le hst]))

/-- Strongly measurable `IsBrownian` processes are filtered in their natural filtration. -/
theorem IsBrownian.isFilteredBrownian_natural (hW : IsBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) : IsFilteredBrownian (Filtration.natural W hmeas) W P :=
  ⟨hW.toIsPreBrownian.isFilteredPreBrownian_natural hmeas, hW.ae_continuous⟩

/-- Strongly measurable `IsBrownian` processes are filtered in the usual natural filtration. -/
theorem IsBrownian.isFilteredBrownian_rightCont_nullAugment_natural (hW : IsBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    @IsFilteredBrownian (NullMeasurableSpace Ω P) E inferInstance _ _ _
      ((Filtration.natural W hmeas).nullAugment P).rightCont
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω) P.completion :=
  (hW.isFilteredBrownian_natural hmeas).rightCont_nullAugment

/-- Enlarging `Filtration.natural W` by independent `𝒢 ≤ mΩ` preserves `IsFilteredPreBrownian`. -/
theorem IsPreBrownian.isFilteredPreBrownian_natural_sup_const (hW : IsPreBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    (hIndep : Indep 𝒢 (.comap (fun ω t ↦ W t ω) inferInstance) P) :
    IsFilteredPreBrownian (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P :=
  (hW.isFilteredPreBrownian_natural hmeas).sup_const h𝒢 <| indep_of_indep_of_le_right hIndep <| by
    rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun _ ↦ iSup₂_le fun s _ ↦
      le_iSup (fun r ↦ MeasurableSpace.comap (W r) inferInstance) s

/-- Enlarging `Filtration.natural W` by an independent `𝒢 ≤ mΩ` preserves `IsFilteredBrownian`. -/
theorem IsBrownian.isFilteredBrownian_natural_sup_const (hW : IsBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    (hIndep : Indep 𝒢 (.comap (fun ω t ↦ W t ω) inferInstance) P) :
    IsFilteredBrownian (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P :=
  ⟨hW.toIsPreBrownian.isFilteredPreBrownian_natural_sup_const hmeas h𝒢 hIndep, hW.ae_continuous⟩

/-- Enlarging `Filtration.natural W` by an independent `ξ` preserves `IsFilteredPreBrownian`. -/
theorem IsPreBrownian.isFilteredPreBrownian_natural_sup_comap (hW : IsPreBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) {G : Type*} [MeasurableSpace G] {ξ : Ω → G}
    (hξ : Measurable ξ) (hIndep : IndepFun ξ (fun ω t ↦ W t ω) P) :
    IsFilteredPreBrownian (Filtration.natural W hmeas ⊔
      Filtration.const ℝ≥0 (.comap ξ inferInstance) hξ.comap_le) W P :=
  hW.isFilteredPreBrownian_natural_sup_const hmeas hξ.comap_le ((IndepFun_iff_Indep ..).mp hIndep)

/-- Enlarging `Filtration.natural W` by an independent `ξ` preserves `IsFilteredBrownian`. -/
theorem IsBrownian.isFilteredBrownian_natural_sup_comap (hW : IsBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) {G : Type*} [MeasurableSpace G] {ξ : Ω → G}
    (hξ : Measurable ξ) (hIndep : IndepFun ξ (fun ω t ↦ W t ω) P) :
    IsFilteredBrownian (Filtration.natural W hmeas ⊔
      Filtration.const ℝ≥0 (.comap ξ inferInstance) hξ.comap_le) W P :=
  ⟨hW.toIsPreBrownian.isFilteredPreBrownian_natural_sup_comap hmeas hξ hIndep, hW.ae_continuous⟩

end Complete

section OrthonormalBasis

variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

/-- Orthonormal basis coordinates `⟪b i, W t ω⟫` satisfy `IsFilteredPreBrownianReal ℱ`. -/
theorem IsFilteredPreBrownian.isFilteredPreBrownianReal_orthonormalBasis
    (hW : IsFilteredPreBrownian ℱ W P) (b : OrthonormalBasis ι ℝ E) (i : ι) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪b i, W t ω⟫) P :=
  have := b.toBasis.finiteDimensional_of_finite
  hW.isFilteredPreBrownianReal_inner_of_norm_eq_one (b.orthonormal.1 i)

/-- Orthonormal basis coordinates `⟪b i, W t ω⟫` satisfy `IsFilteredBrownian ℱ`. -/
theorem IsFilteredBrownian.isFilteredBrownian_orthonormalBasis
    (hW : IsFilteredBrownian ℱ W P) (b : OrthonormalBasis ι ℝ E) (i : ι) :
    IsFilteredBrownian ℱ (fun t ω ↦ ⟪b i, W t ω⟫) P :=
  have := b.toBasis.finiteDimensional_of_finite
  hW.isFilteredBrownian_inner_of_norm_eq_one (b.orthonormal.1 i)

/-- Characterization of `IsFilteredPreBrownian ℱ W P` via a finite orthonormal basis `b`. -/
theorem isFilteredPreBrownian_iff_orthonormalBasis (b : OrthonormalBasis ι ℝ E) :
    IsFilteredPreBrownian ℱ W P ↔ IsPreBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P ∧
      (∀ i, Adapted ℱ (fun t ω ↦ ⟪b i, W t ω⟫)) ∧
      ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
        Indep (.comap (fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫) inferInstance) (ℱ s) P := by
  have : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  have hf : Measurable fun (x : E) (i : ι) ↦ ⟪b i, x⟫ :=
    (continuous_pi fun i ↦ (innerSL ℝ (b i)).continuous).measurable
  have hg : Measurable fun z : ι → ℝ ↦ ∑ i, z i • b i := Continuous.measurable (by fun_prop)
  refine ⟨fun hW ↦ ⟨hW.isPreBrownianVector_orthonormalBasis b,
      fun i ↦ (hW.isFilteredPreBrownianReal_orthonormalBasis b i).adapted, fun s t hst ↦
        indep_of_indep_of_le_left (hW.indep_sub hst) (MeasurableSpace.comap_le_comap_of_eq_comp _ hf
          (by ext ω i; simp [inner_sub_right]))⟩, fun ⟨hB, hadapt, hindep⟩ ↦ ?_⟩
  refine ⟨(isPreBrownian_iff_isPreBrownianVector b).mpr hB, fun t ↦ ?_, fun s t hst ↦
    indep_of_indep_of_le_left (hindep hst) (MeasurableSpace.comap_le_comap_of_eq_comp _ hg
      (by ext ω; simpa [inner_sub_right] using (b.sum_repr' (W t ω - W s ω)).symm))⟩
  have heq : W t = (fun z : ι → ℝ ↦ ∑ i, z i • b i) ∘ fun ω i ↦ ⟪b i, W t ω⟫ := by
    ext ω; exact (b.sum_repr' (W t ω)).symm
  exact heq ▸ hg.comp ((@measurable_pi_iff Ω ι (fun _ ↦ ℝ) (ℱ t) _ _).mpr fun i ↦ hadapt i t)

/-- Characterization of `IsFilteredBrownian ℱ W P` via a finite orthonormal basis `b`. -/
theorem isFilteredBrownian_iff_orthonormalBasis (b : OrthonormalBasis ι ℝ E) :
    IsFilteredBrownian ℱ W P ↔ IsBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P ∧
      (∀ i, Adapted ℱ (fun t ω ↦ ⟪b i, W t ω⟫)) ∧
      ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
        Indep (.comap (fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫) inferInstance) (ℱ s) P :=
  ⟨fun hW ↦ ⟨hW.toIsBrownian.isBrownianVector_orthonormalBasis b,
      ((isFilteredPreBrownian_iff_orthonormalBasis b).mp hW.toIsFilteredPreBrownian).2⟩,
    fun ⟨hB, hadapt, hindep⟩ ↦
      have hpre := (isFilteredPreBrownian_iff_orthonormalBasis b).mpr ⟨hB.1, hadapt, hindep⟩
      .of_isBrownian ((isBrownian_iff_isBrownianVector b).mpr hB) hpre.adapted hpre.indep_sub⟩

end OrthonormalBasis

section FiniteDimensional

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Strongly measurable marginals of the Kolmogorov vector pre-Brownian motion. -/
theorem stronglyMeasurable_sum_smul_stdOrthonormalBasis (t : ℝ≥0) :
    StronglyMeasurable fun ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ ↦
      ∑ i, ω i t • stdOrthonormalBasis ℝ E i :=
  Measurable.stronglyMeasurable <| (Continuous.measurable (by fun_prop :
    Continuous fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)).comp <|
    measurable_pi_iff.mpr fun i ↦ (measurable_pi_apply t).comp (measurable_pi_apply i)

/-- Unconditional witness of `IsFilteredPreBrownian` on any finite-dimensional space `E`. -/
theorem isFilteredPreBrownian_sum_smul_pi_brownianProjectiveLimit :
    IsFilteredPreBrownian
      (Filtration.natural (fun t (ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ) ↦
        ∑ i, ω i t • stdOrthonormalBasis ℝ E i) stronglyMeasurable_sum_smul_stdOrthonormalBasis)
      (fun t (ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ) ↦ ∑ i, ω i t • stdOrthonormalBasis ℝ E i)
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ brownianProjectiveLimit) :=
  isPreBrownian_sum_smul_pi_brownianProjectiveLimit.isFilteredPreBrownian_natural
    stronglyMeasurable_sum_smul_stdOrthonormalBasis

/-- An adapted `E`-valued process with marginals `(stdGaussian E).map (√t • ·)` and increments
`X t - X s` (`s ≤ t`) independent of `ℱ s` satisfies `IsFilteredPreBrownian ℱ X P`. -/
theorem _root_.MeasureTheory.Adapted.isFilteredPreBrownian {ℱ : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → E} (hX : Adapted ℱ X)
    (hlaw : ∀ t : ℝ≥0, HasLaw (X t) ((stdGaussian E).map (fun x : E ↦ √(t : ℝ) • x)) P)
    (hindep : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) P) :
    IsFilteredPreBrownian ℱ X P :=
  have := (hlaw 0).isProbabilityMeasure
  ⟨HasIndepIncrements.isPreBrownian_of_hasLaw hlaw (hX.hasIndepIncrements hindep), hX, hindep⟩

end FiniteDimensional

end TauCeti.Probability
