/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Vector.InnerProduct
public import TauCeti.Probability.Process.Filtration.AmbientNullAugmentation
import TauCeti.Probability.Independence.Completion
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Independence.Sup
import TauCeti.Probability.Process.Filtration.Natural

/-!
# Vector Brownian motion relative to a filtration

`TauCeti.Probability.IsPreBrownian` and `TauCeti.Probability.IsBrownian` prescribe the Gaussian
finite-dimensional laws and almost-sure path continuity of an `E`-valued Brownian motion `W`,
without reference to a filtration. Stochastic integration, martingale arguments, and stochastic
differential equations with noncentered random initial conditions require a filtration `ℱ` to
which `W` is adapted and from whose past `ℱ s` every increment `W t - W s` (`s ≤ t`) is
independent.

This file defines `TauCeti.Probability.IsFilteredPreBrownian` and
`TauCeti.Probability.IsFilteredBrownian` for processes taking values in a real inner-product space
`E`, develops their invariance and projection properties, characterizes them in an orthonormal
basis, and proves that enlarging a filtration (in particular, the natural filtration of `W`) by an
independent initial `σ`-algebra preserves the filtered Brownian property while making an
independent initial random vector adapted at time `0`.

Note that coordinatewise `IsFilteredPreBrownianReal` together with `IsPreBrownianVector` does *not*
imply `IsFilteredPreBrownian` on an arbitrary filtration `ℱ`, because individual independence of
`⟪b i, W t - W s⟫` from `ℱ s` for each `i` does not force the *joint* increment vector to be
independent of `ℱ s` (for instance, `ℱ 0 = σ(sgn(B₀ 1 · B₁ 1))` for planar Brownian motion). The
orthonormal-basis equivalence `isFilteredPreBrownian_iff_orthonormalBasis` therefore requires joint
independence of the coordinate increment vector from `ℱ s`.

## Main declarations

* `TauCeti.Probability.IsFilteredPreBrownian`, `TauCeti.Probability.IsFilteredBrownian`:
  vector pre-Brownian and Brownian motion in `E` relative to a filtration `ℱ`.
* `TauCeti.Probability.isFilteredPreBrownian_real_iff`: compatibility with
  `TauCeti.Probability.IsFilteredPreBrownianReal` when `E = ℝ`.
* `TauCeti.Probability.IsFilteredPreBrownian.of_le`,
  `TauCeti.Probability.IsFilteredPreBrownian.ambientNullAugmentation`,
  `TauCeti.Probability.IsFilteredPreBrownian.sup_const`: filtration restriction, original-space
  null augmentation, and enlargement by an independent constant `σ`-algebra.
* `TauCeti.Probability.IsPreBrownian.isFilteredPreBrownian_natural`,
  `TauCeti.Probability.IsPreBrownian.isFilteredPreBrownian_natural_sup_comap`: a vector
  pre-Brownian motion is filtered with respect to its natural filtration, and remains so after
  adjoining an independent initial random variable `ξ` (making `ξ + W` adapted).
* `TauCeti.Probability.IsFilteredPreBrownian.comp_linearIsometryEquiv`,
  `TauCeti.Probability.IsFilteredPreBrownian.isFilteredPreBrownianReal_inner_of_norm_eq_one`,
  `TauCeti.Probability.isFilteredPreBrownian_iff_orthonormalBasis`: invariance under linear
  isometries, unit-vector scalar projections, and the orthonormal-basis dictionary.
* `MeasureTheory.Adapted.isFilteredPreBrownian`: Lévy-style increment characterization of filtered
  vector pre-Brownian motion on a finite-dimensional real inner-product space.

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

/-- `W : ℝ≥0 → Ω → E` is a **vector pre-Brownian motion relative to `ℱ`** under `P` if it is a
vector pre-Brownian motion in `E`, is adapted to `ℱ`, and every increment `W t - W s` (`s ≤ t`)
is independent of `ℱ s`. -/
structure IsFilteredPreBrownian (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownian W P where
  /-- `W t` is `ℱ t`-measurable for every `t`. -/
  adapted : Adapted ℱ W
  /-- For `s ≤ t`, the increment `W t - W s` is independent of `ℱ s`. -/
  indep_sub ⦃s t : ℝ≥0⦄ : s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P

/-- `W : ℝ≥0 → Ω → E` is a **vector Brownian motion relative to `ℱ`** under `P` if it is a vector
pre-Brownian motion relative to `ℱ` with `P`-almost surely continuous sample paths. -/
structure IsFilteredBrownian (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop extends IsFilteredPreBrownian ℱ W P where
  /-- Almost every sample path `t ↦ W t ω` is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (W · ω)

/-- Forget the filtration and view a filtered vector Brownian motion as an `IsBrownian` process. -/
theorem IsFilteredBrownian.toIsBrownian {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}
    (hW : IsFilteredBrownian ℱ W P) : IsBrownian W P :=
  ⟨hW.toIsPreBrownian, hW.ae_continuous⟩

/-- Package an `IsBrownian` process together with adaptedness and increment independence into
`IsFilteredBrownian`. -/
theorem IsFilteredBrownian.of_isBrownian {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}
    (hW : IsBrownian W P) (hadapt : Adapted ℱ W)
    (hindep : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P) :
    IsFilteredBrownian ℱ W P :=
  ⟨⟨hW.toIsPreBrownian, hadapt, hindep⟩, hW.ae_continuous⟩

/-- Equivalence between `IsFilteredBrownian ℱ W P` and `IsBrownian W P` plus filtration
compatibility. -/
theorem isFilteredBrownian_iff {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E} :
    IsFilteredBrownian ℱ W P ↔
      IsBrownian W P ∧ Adapted ℱ W ∧
        ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P :=
  ⟨fun h ↦ ⟨h.toIsBrownian, h.adapted, h.indep_sub⟩,
    fun ⟨hW, hadapt, hindep⟩ ↦ .of_isBrownian hW hadapt hindep⟩

namespace IsFilteredPreBrownian

variable {ℱ : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → E}

/-- Every time marginal of a filtered vector pre-Brownian motion is ambient-measurable. -/
theorem measurable (hW : IsFilteredPreBrownian ℱ W P) (t : ℝ≥0) : Measurable (W t) :=
  (hW.adapted t).mono (ℱ.le t) le_rfl

/-- Any `ℱ s`-measurable random variable is independent of a subsequent Brownian increment
`W t - W s` (`s ≤ t`). -/
theorem indepFun_sub (hW : IsFilteredPreBrownian ℱ W P) {s t : ℝ≥0} (hst : s ≤ t)
    {G : Type*} [MeasurableSpace G] {Y : Ω → G} (hY : Measurable[ℱ s] Y) :
    IndepFun Y (W t - W s) P :=
  (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_left (hW.indep_sub hst).symm hY.comap_le)

/-- Fixed-time almost-sure equality preserves `IsFilteredPreBrownian` when the modification is
adapted to the same filtration `ℱ`. -/
theorem congr (hW : IsFilteredPreBrownian ℱ W P) (hW' : Adapted ℱ W')
    (h : ∀ t, W t =ᵐ[P] W' t) : IsFilteredPreBrownian ℱ W' P where
  toIsPreBrownian := hW.toIsPreBrownian.congr h
  adapted := hW'
  indep_sub s t hst := by
    have hi : @IndepFun Ω E Ω mΩ inferInstance (ℱ s) (W t - W s) id P := by
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hW.indep_sub hst
    have hj := hi.congr ((h t).sub (h s)) (Filter.EventuallyEq.refl ..)
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hj

/-- Indistinguishable adapted processes have the same `IsFilteredPreBrownian` property. -/
theorem congr_indistinguishable (hW : IsFilteredPreBrownian ℱ W P) (hW' : Adapted ℱ W')
    (h : W ≡ᵐ[P] W') : IsFilteredPreBrownian ℱ W' P :=
  hW.congr hW' fun t ↦ h.mono fun _ hω ↦ hω t

/-- `IsFilteredPreBrownian` passes to any smaller filtration `𝒢 ≤ ℱ` to which `W` is adapted. -/
theorem of_le (hW : IsFilteredPreBrownian ℱ W P) {𝒢 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ ℱ)
    (hadapt : Adapted 𝒢 W) : IsFilteredPreBrownian 𝒢 W P where
  toIsPreBrownian := hW.toIsPreBrownian
  adapted := hadapt
  indep_sub s _ hst := indep_of_indep_of_le_right (hW.indep_sub hst) (h𝒢 s)

/-- Adjoining ambient-measurable `P`-null sets to `ℱ` preserves `IsFilteredPreBrownian`. -/
theorem ambientNullAugmentation (hW : IsFilteredPreBrownian ℱ W P) :
    IsFilteredPreBrownian (ℱ.ambientNullAugmentation P) W P where
  toIsPreBrownian := hW.toIsPreBrownian
  adapted t := (hW.adapted t).mono (ℱ.le_ambientNullAugmentation P t) le_rfl
  indep_sub s _ hst := by
    apply indep_of_indep_of_le_right (hW.indep_sub hst).eventuallyMeasurableSpace_right
    rw [Filtration.ambientNullAugmentation_apply, Filtration.nullAugment_apply]
    exact inf_le_right

end IsFilteredPreBrownian

namespace IsFilteredBrownian

variable {ℱ : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → E}

/-- Indistinguishable adapted processes share the `IsFilteredBrownian` property. -/
theorem congr_indistinguishable (hW : IsFilteredBrownian ℱ W P) (hW' : Adapted ℱ W')
    (h : W ≡ᵐ[P] W') : IsFilteredBrownian ℱ W' P :=
  .of_isBrownian (hW.toIsBrownian.congr_indistinguishable h) hW'
    (hW.toIsFilteredPreBrownian.congr_indistinguishable hW' h).indep_sub

/-- `IsFilteredBrownian` passes to any smaller filtration `𝒢 ≤ ℱ` to which `W` is adapted. -/
theorem of_le (hW : IsFilteredBrownian ℱ W P) {𝒢 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ ℱ)
    (hadapt : Adapted 𝒢 W) : IsFilteredBrownian 𝒢 W P :=
  ⟨hW.toIsFilteredPreBrownian.of_le h𝒢 hadapt, hW.ae_continuous⟩

/-- Adjoining ambient-measurable `P`-null sets to `ℱ` preserves `IsFilteredBrownian`. -/
theorem ambientNullAugmentation (hW : IsFilteredBrownian ℱ W P) :
    IsFilteredBrownian (ℱ.ambientNullAugmentation P) W P :=
  ⟨hW.toIsFilteredPreBrownian.ambientNullAugmentation, hW.ae_continuous⟩

end IsFilteredBrownian

/-- On `E = ℝ`, `IsFilteredPreBrownian` is equivalent to `IsFilteredPreBrownianReal`. -/
@[simp]
theorem isFilteredPreBrownian_real_iff {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} :
    IsFilteredPreBrownian ℱ W P ↔ IsFilteredPreBrownianReal ℱ W P :=
  ⟨fun h ↦ ⟨isPreBrownian_real_iff.mp h.toIsPreBrownian, h.adapted, h.indep_sub⟩,
    fun h ↦ ⟨isPreBrownian_real_iff.mpr h.toIsPreBrownianReal, h.adapted, h.indep_sub⟩⟩

/-- On `E = ℝ`, `IsFilteredBrownian` is equivalent to `IsBrownianReal` together with adaptedness
and independence of increments from `ℱ`. -/
theorem isFilteredBrownian_real_iff {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} :
    IsFilteredBrownian ℱ W P ↔
      IsBrownianReal W P ∧ Adapted ℱ W ∧
        ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P := by
  rw [isFilteredBrownian_iff, isBrownian_real_iff]

end Defs

section Borel

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- On a `0`-dimensional real inner-product space (`Subsingleton E`), every process on a
probability space is a filtered vector Brownian motion relative to any filtration `ℱ`. -/
theorem IsFilteredBrownian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E) : IsFilteredBrownian ℱ W P := by
  refine .of_isBrownian (.of_subsingleton W)
    (fun t ↦ by rw [Subsingleton.elim (W t) (fun _ ↦ (0 : E))]; exact measurable_const)
    fun s t _ ↦ ?_
  have hconst : W t - W s = fun _ ↦ (0 : E) := Subsingleton.elim _ _
  rw [hconst, MeasurableSpace.comap_const]
  exact indep_bot_left (ℱ s)

/-- On a `0`-dimensional real inner-product space (`Subsingleton E`), every process on a
probability space is a filtered vector pre-Brownian motion relative to any filtration `ℱ`. -/
theorem IsFilteredPreBrownian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → E) : IsFilteredPreBrownian ℱ W P :=
  (IsFilteredBrownian.of_subsingleton ℱ W).toIsFilteredPreBrownian

end Borel

section SecondCountable

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

namespace IsFilteredPreBrownian

variable {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

/-- Normalized inner product `‖u‖⁻¹ * ⟪u, W t ω⟫` against any nonzero `u : E` is a scalar
filtered pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal_norm_inv_mul_inner (hW : IsFilteredPreBrownian ℱ W P)
    {u : E} (hu : u ≠ 0) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P where
  toIsPreBrownianReal := hW.isPreBrownianReal_norm_inv_mul_inner hu
  adapted t := ((continuous_const.mul (innerSL ℝ u).continuous).measurable).comp (hW.adapted t)
  indep_sub s t hst := by
    have hcomp : ((fun ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) - fun ω ↦ ‖u‖⁻¹ * ⟪u, W s ω⟫) =
        (fun x : E ↦ ‖u‖⁻¹ * ⟪u, x⟫) ∘ (W t - W s) := by
      ext ω
      simp [inner_sub_right, mul_sub]
    have hg : Measurable fun x : E ↦ ‖u‖⁻¹ * ⟪u, x⟫ :=
      (continuous_const.mul (innerSL ℝ u).continuous).measurable
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact indep_of_indep_of_le_left (hW.indep_sub hst) (MeasurableSpace.comap_mono hg.comap_le)

/-- Inner product `⟪u, W t ω⟫` against a unit vector `u : E` (`‖u‖ = 1`) is a scalar filtered
pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal_inner_of_norm_eq_one (hW : IsFilteredPreBrownian ℱ W P)
    {u : E} (hu : ‖u‖ = 1) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪u, W t ω⟫) P := by
  have hu0 : u ≠ 0 := by
    intro h0
    simp [h0] at hu
  simpa [hu] using hW.isFilteredPreBrownianReal_norm_inv_mul_inner hu0

/-- Linear isometry equivalences preserve `IsFilteredPreBrownian`. -/
theorem comp_linearIsometryEquiv [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hW : IsFilteredPreBrownian ℱ W P) (f : E ≃ₗᵢ[ℝ] F) :
    IsFilteredPreBrownian ℱ (fun t ω ↦ f (W t ω)) P where
  toIsPreBrownian := hW.toIsPreBrownian.comp_linearIsometryEquiv f
  adapted t := f.continuous.measurable.comp (hW.adapted t)
  indep_sub s t hst := by
    have hcomp : ((fun ω ↦ f (W t ω)) - fun ω ↦ f (W s ω)) = f ∘ (W t - W s) := by
      ext ω
      simp [map_sub]
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact indep_of_indep_of_le_left (hW.indep_sub hst)
      (MeasurableSpace.comap_mono f.continuous.measurable.comap_le)

/-- Negating a filtered vector pre-Brownian motion preserves `IsFilteredPreBrownian`. -/
theorem neg (hW : IsFilteredPreBrownian ℱ W P) : IsFilteredPreBrownian ℱ (-W) P :=
  hW.comp_linearIsometryEquiv (LinearIsometryEquiv.neg ℝ)

end IsFilteredPreBrownian

/-- `f ∘ W` is a filtered vector pre-Brownian motion if and only if `W` is, for any linear
isometry equivalence `f : E ≃ₗᵢ[ℝ] F`. -/
theorem isFilteredPreBrownian_comp_linearIsometryEquiv_iff [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E} (f : E ≃ₗᵢ[ℝ] F) :
    IsFilteredPreBrownian ℱ (fun t ω ↦ f (W t ω)) P ↔ IsFilteredPreBrownian ℱ W P :=
  ⟨fun h ↦ by simpa using h.comp_linearIsometryEquiv f.symm,
    fun h ↦ h.comp_linearIsometryEquiv f⟩

namespace IsFilteredBrownian

variable {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

/-- Normalized inner product `‖u‖⁻¹ * ⟪u, W t ω⟫` against any nonzero `u : E` is a scalar
filtered Brownian motion relative to `ℱ`. -/
theorem isFilteredBrownian_norm_inv_mul_inner (hW : IsFilteredBrownian ℱ W P)
    {u : E} (hu : u ≠ 0) :
    IsFilteredBrownian ℱ (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P :=
  ⟨isFilteredPreBrownian_real_iff.mpr (hW.isFilteredPreBrownianReal_norm_inv_mul_inner hu),
    (isBrownian_real_iff.mpr
      (hW.toIsBrownian.isBrownianReal_norm_inv_mul_inner hu)).ae_continuous⟩

/-- Inner product `⟪u, W t ω⟫` against a unit vector `u : E` (`‖u‖ = 1`) is a scalar filtered
Brownian motion relative to `ℱ`. -/
theorem isFilteredBrownian_inner_of_norm_eq_one (hW : IsFilteredBrownian ℱ W P)
    {u : E} (hu : ‖u‖ = 1) :
    IsFilteredBrownian ℱ (fun t ω ↦ ⟪u, W t ω⟫) P :=
  ⟨isFilteredPreBrownian_real_iff.mpr (hW.isFilteredPreBrownianReal_inner_of_norm_eq_one hu),
    (isBrownian_real_iff.mpr
      (hW.toIsBrownian.isBrownianReal_inner_of_norm_eq_one hu)).ae_continuous⟩

/-- Linear isometry equivalences preserve `IsFilteredBrownian`. -/
theorem comp_linearIsometryEquiv [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hW : IsFilteredBrownian ℱ W P) (f : E ≃ₗᵢ[ℝ] F) :
    IsFilteredBrownian ℱ (fun t ω ↦ f (W t ω)) P :=
  ⟨hW.toIsFilteredPreBrownian.comp_linearIsometryEquiv f,
    (hW.toIsBrownian.comp_linearIsometryEquiv f).ae_continuous⟩

/-- Negating a filtered vector Brownian motion preserves `IsFilteredBrownian`. -/
theorem neg (hW : IsFilteredBrownian ℱ W P) : IsFilteredBrownian ℱ (-W) P :=
  hW.comp_linearIsometryEquiv (LinearIsometryEquiv.neg ℝ)

end IsFilteredBrownian

/-- `f ∘ W` is a filtered vector Brownian motion if and only if `W` is, for any linear isometry
equivalence `f : E ≃ₗᵢ[ℝ] F`. -/
theorem isFilteredBrownian_comp_linearIsometryEquiv_iff [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E} (f : E ≃ₗᵢ[ℝ] F) :
    IsFilteredBrownian ℱ (fun t ω ↦ f (W t ω)) P ↔ IsFilteredBrownian ℱ W P :=
  ⟨fun h ↦ by simpa using h.comp_linearIsometryEquiv f.symm,
    fun h ↦ h.comp_linearIsometryEquiv f⟩

namespace IsFilteredPreBrownian

variable {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

/-- On a second-countable Borel inner-product space, a filtered vector pre-Brownian motion is
strongly adapted to `ℱ`. -/
theorem stronglyAdapted (hW : IsFilteredPreBrownian ℱ W P) : StronglyAdapted ℱ W :=
  fun t ↦ (hW.adapted t).stronglyMeasurable

/-- Increments of a filtered vector pre-Brownian motion over `(s, t]` and `(u, v]` with `s ≤ u`,
`t ≤ u`, `u ≤ v` are independent. -/
theorem indepFun_sub_sub (hW : IsFilteredPreBrownian ℱ W P) {s t u v : ℝ≥0}
    (hsu : s ≤ u) (htu : t ≤ u) (huv : u ≤ v) :
    IndepFun (W t - W s) (W v - W u) P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left (hW.indep_sub huv).symm
    ((hW.adapted.measurable_le htu).sub (hW.adapted.measurable_le hsu)).comap_le

/-- A filtered vector pre-Brownian motion has independent increments (without requiring
completeness of `E`). -/
theorem hasIndepIncrements (hW : IsFilteredPreBrownian ℱ W P) : HasIndepIncrements W P :=
  have := hW.isProbabilityMeasure
  hW.adapted.hasIndepIncrements hW.indep_sub

/-- For every `s : ℝ≥0`, the entire future increment process `(W t - W s)_{t ≥ s}` is independent
of `ℱ s`. -/
theorem indep_comap_sub_Ici (hW : IsFilteredPreBrownian ℱ W P) (s : ℝ≥0) :
    Indep (.comap (fun ω (t : Set.Ici s) ↦ W t ω - W s ω) inferInstance) (ℱ s) P :=
  have := hW.isProbabilityMeasure
  hW.adapted.indep_comap_sub_Ici hW.indep_sub s

/-- For every `s : ℝ≥0`, the shifted increment process `u ↦ W (s + u) - W s` is independent of
`ℱ s`. -/
theorem indep_comap_shift (hW : IsFilteredPreBrownian ℱ W P) (s : ℝ≥0) :
    Indep (.comap (fun ω u ↦ W (s + u) ω - W s ω) inferInstance) (ℱ s) P := by
  refine indep_of_indep_of_le_left (hW.indep_comap_sub_Ici s) ?_
  have hg : Measurable fun (z : Set.Ici s → E) (u : ℝ≥0) ↦
      z ⟨s + u, Set.mem_Ici.mpr le_self_add⟩ := by
    fun_prop
  have hcomp : (fun ω u ↦ W (s + u) ω - W s ω) =
      (fun (z : Set.Ici s → E) (u : ℝ≥0) ↦ z ⟨s + u, Set.mem_Ici.mpr le_self_add⟩) ∘
        fun ω (t : Set.Ici s) ↦ W t ω - W s ω :=
    rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

/-- For any `t₀ : ℝ≥0`, the shifted increment process `t ↦ W (t₀ + t) - W t₀` is a filtered vector
pre-Brownian motion relative to the shifted filtration `t ↦ ℱ (t₀ + t)`. -/
theorem shift (hW : IsFilteredPreBrownian ℱ W P) (t₀ : ℝ≥0) :
    IsFilteredPreBrownian
      ⟨fun t ↦ ℱ (t₀ + t), fun _ _ h ↦ ℱ.mono (by gcongr), fun t ↦ ℱ.le (t₀ + t)⟩
      (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P where
  toIsPreBrownian := hW.toIsPreBrownian.shift t₀
  adapted t := (hW.adapted (t₀ + t)).sub (hW.adapted.measurable_le le_self_add)
  indep_sub s t hst := by
    have hsub : ((fun ω ↦ W (t₀ + t) ω - W t₀ ω) - fun ω ↦ W (t₀ + s) ω - W t₀ ω) =
        W (t₀ + t) - W (t₀ + s) := by
      ext ω
      simp
    rw [hsub]
    exact hW.indep_sub (by gcongr)

/-- Any filtered vector pre-Brownian motion is also a filtered vector pre-Brownian motion relative
to its own natural filtration. -/
theorem natural (hW : IsFilteredPreBrownian ℱ W P) :
    IsFilteredPreBrownian
      (Filtration.natural W fun t ↦ (hW.measurable t).stronglyMeasurable) W P :=
  hW.of_le ((Filtration.natural_le_iff W _ ℱ).mpr hW.adapted)
    (Filtration.stronglyAdapted_natural _).adapted

/-- Enlarging `ℱ` by a constant sub-`σ`-algebra `𝒢 ≤ mΩ` independent of `⨆ t, ℱ t` preserves
`IsFilteredPreBrownian`. -/
theorem sup_const (hW : IsFilteredPreBrownian ℱ W P) {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    (hIndep : Indep 𝒢 (⨆ t, ℱ t) P) :
    IsFilteredPreBrownian (ℱ ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P where
  toIsPreBrownian := hW.toIsPreBrownian
  adapted t := (hW.adapted t).mono le_sup_left le_rfl
  indep_sub s t hst := by
    have := hW.isProbabilityMeasure
    have hm : MeasurableSpace.comap (W t - W s) inferInstance ≤ ℱ t :=
      ((hW.adapted t).sub (hW.adapted.measurable_le hst)).comap_le
    have hsup : ℱ s ⊔ MeasurableSpace.comap (W t - W s) inferInstance ≤ ⨆ r, ℱ r :=
      sup_le ((ℱ.mono hst).trans (le_iSup ℱ t)) (hm.trans (le_iSup ℱ t))
    exact (((hW.indep_sub hst).symm).sup_left (indep_of_indep_of_le_right hIndep hsup)
      (ℱ.le s) h𝒢 (hm.trans (ℱ.le t))).symm

end IsFilteredPreBrownian

namespace IsFilteredBrownian

variable {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E}

/-- On a second-countable Borel inner-product space, a filtered vector Brownian motion is strongly
adapted to `ℱ`. -/
theorem stronglyAdapted (hW : IsFilteredBrownian ℱ W P) : StronglyAdapted ℱ W :=
  hW.toIsFilteredPreBrownian.stronglyAdapted

/-- For any `t₀ : ℝ≥0`, the shifted increment process `t ↦ W (t₀ + t) - W t₀` is a filtered vector
Brownian motion relative to `t ↦ ℱ (t₀ + t)`. -/
theorem shift (hW : IsFilteredBrownian ℱ W P) (t₀ : ℝ≥0) :
    IsFilteredBrownian
      ⟨fun t ↦ ℱ (t₀ + t), fun _ _ h ↦ ℱ.mono (by gcongr), fun t ↦ ℱ.le (t₀ + t)⟩
      (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P :=
  ⟨hW.toIsFilteredPreBrownian.shift t₀, (hW.toIsBrownian.shift t₀).ae_continuous⟩

/-- Enlarging `ℱ` by a constant sub-`σ`-algebra `𝒢 ≤ mΩ` independent of `⨆ t, ℱ t` preserves
`IsFilteredBrownian`. -/
theorem sup_const (hW : IsFilteredBrownian ℱ W P) {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    (hIndep : Indep 𝒢 (⨆ t, ℱ t) P) :
    IsFilteredBrownian (ℱ ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P :=
  ⟨hW.toIsFilteredPreBrownian.sup_const h𝒢 hIndep, hW.ae_continuous⟩

end IsFilteredBrownian

end SecondCountable

section Complete

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- A vector pre-Brownian motion whose time marginals are strongly measurable is a filtered vector
pre-Brownian motion relative to its natural filtration. -/
theorem IsPreBrownian.isFilteredPreBrownian_natural {W : ℝ≥0 → Ω → E} (hW : IsPreBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    IsFilteredPreBrownian (Filtration.natural W hmeas) W P where
  toIsPreBrownian := hW
  adapted t := (Filtration.stronglyAdapted_natural hmeas t).measurable
  indep_sub s t hst := by
    rw [Filtration.natural_eq_comap]
    refine indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).mp (hW.indepFun_shift s)) ?_
    have hcomp : W t - W s = (fun x : ℝ≥0 → E ↦ x (t - s)) ∘ fun ω u ↦ W (s + u) ω - W s ω := by
      ext ω
      simp [add_tsub_cancel_of_le hst]
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- A vector Brownian motion whose time marginals are strongly measurable is a filtered vector
Brownian motion relative to its natural filtration. -/
theorem IsBrownian.isFilteredBrownian_natural {W : ℝ≥0 → Ω → E} (hW : IsBrownian W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    IsFilteredBrownian (Filtration.natural W hmeas) W P :=
  ⟨hW.toIsPreBrownian.isFilteredPreBrownian_natural hmeas, hW.ae_continuous⟩

/-- Enlarging the natural filtration of `W` by any initial `σ`-algebra `𝒢 ≤ mΩ` independent of the
path `t ↦ W t` preserves `IsFilteredPreBrownian`. -/
theorem IsPreBrownian.isFilteredPreBrownian_natural_sup_const {W : ℝ≥0 → Ω → E}
    (hW : IsPreBrownian W P) (hmeas : ∀ t, StronglyMeasurable (W t)) {𝒢 : MeasurableSpace Ω}
    (h𝒢 : 𝒢 ≤ mΩ) (hIndep : Indep 𝒢 (.comap (fun ω t ↦ W t ω) inferInstance) P) :
    IsFilteredPreBrownian
      (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P := by
  refine (hW.isFilteredPreBrownian_natural hmeas).sup_const h𝒢
    (indep_of_indep_of_le_right hIndep ?_)
  rw [MeasurableSpace.comap_process_pi]
  exact iSup_le fun t ↦ iSup₂_le fun s _ ↦
    le_iSup (fun r ↦ MeasurableSpace.comap (W r) inferInstance) s

/-- Enlarging the natural filtration of `W` by any initial `σ`-algebra `𝒢 ≤ mΩ` independent of the
path `t ↦ W t` preserves `IsFilteredBrownian`. -/
theorem IsBrownian.isFilteredBrownian_natural_sup_const {W : ℝ≥0 → Ω → E}
    (hW : IsBrownian W P) (hmeas : ∀ t, StronglyMeasurable (W t)) {𝒢 : MeasurableSpace Ω}
    (h𝒢 : 𝒢 ≤ mΩ) (hIndep : Indep 𝒢 (.comap (fun ω t ↦ W t ω) inferInstance) P) :
    IsFilteredBrownian
      (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 𝒢 h𝒢) W P :=
  ⟨hW.toIsPreBrownian.isFilteredPreBrownian_natural_sup_const hmeas h𝒢 hIndep, hW.ae_continuous⟩

/-- Enlarging the natural filtration of `W` by an independent initial random variable `ξ : Ω → G`
preserves `IsFilteredPreBrownian` and makes `ξ` measurable at time `0`. -/
theorem IsPreBrownian.isFilteredPreBrownian_natural_sup_comap {W : ℝ≥0 → Ω → E}
    (hW : IsPreBrownian W P) (hmeas : ∀ t, StronglyMeasurable (W t)) {G : Type*}
    [MeasurableSpace G] {ξ : Ω → G} (hξ : Measurable ξ)
    (hIndep : IndepFun ξ (fun ω t ↦ W t ω) P) :
    IsFilteredPreBrownian
      (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 (.comap ξ inferInstance) hξ.comap_le)
      W P :=
  hW.isFilteredPreBrownian_natural_sup_const hmeas hξ.comap_le
    ((IndepFun_iff_Indep _ _ _).mp hIndep)

/-- Enlarging the natural filtration of `W` by an independent initial random variable `ξ : Ω → G`
preserves `IsFilteredBrownian` and makes `ξ` measurable at time `0`. -/
theorem IsBrownian.isFilteredBrownian_natural_sup_comap {W : ℝ≥0 → Ω → E}
    (hW : IsBrownian W P) (hmeas : ∀ t, StronglyMeasurable (W t)) {G : Type*}
    [MeasurableSpace G] {ξ : Ω → G} (hξ : Measurable ξ)
    (hIndep : IndepFun ξ (fun ω t ↦ W t ω) P) :
    IsFilteredBrownian
      (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 (.comap ξ inferInstance) hξ.comap_le)
      W P :=
  ⟨hW.toIsPreBrownian.isFilteredPreBrownian_natural_sup_comap hmeas hξ hIndep, hW.ae_continuous⟩

end Complete

section AdaptedAddLeft

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Enlarging the natural filtration of `W` by an independent initial random vector `ξ : Ω → E`
makes the translated Brownian motion `t ↦ ξ + W t` adapted to the enlarged filtration. -/
theorem adapted_add_left_natural_sup_comap {W : ℝ≥0 → Ω → E}
    (hmeas : ∀ t, StronglyMeasurable (W t)) {ξ : Ω → E} (hξ : Measurable ξ) :
    Adapted
      (Filtration.natural W hmeas ⊔ Filtration.const ℝ≥0 (.comap ξ inferInstance) hξ.comap_le)
      (fun t ω ↦ ξ ω + W t ω) := fun t ↦
  ((comap_measurable ξ).mono le_sup_right le_rfl).add
    (((Filtration.stronglyAdapted_natural hmeas t).measurable).mono le_sup_left le_rfl)

end AdaptedAddLeft

section OrthonormalBasis

variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- Coordinate projections `⟪b i, W t ω⟫` along an orthonormal basis `b` of a filtered vector
pre-Brownian motion are scalar filtered pre-Brownian motions relative to `ℱ`. -/
theorem IsFilteredPreBrownian.isFilteredPreBrownianReal_orthonormalBasis
    {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → E} (hW : IsFilteredPreBrownian ℱ W P)
    (b : OrthonormalBasis ι ℝ E) (i : ι) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪b i, W t ω⟫) P := by
  have : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  exact hW.isFilteredPreBrownianReal_inner_of_norm_eq_one (b.orthonormal.1 i)

/-- Characterization of `IsFilteredPreBrownian ℱ W P` in terms of a finite orthonormal basis `b`:
the coordinate processes form an `IsPreBrownianVector`, each coordinate is adapted to `ℱ`, and for
every `s ≤ t` the joint coordinate increment vector `i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫` is
independent of `ℱ s`. -/
theorem isFilteredPreBrownian_iff_orthonormalBasis {ℱ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → E} (b : OrthonormalBasis ι ℝ E) :
    IsFilteredPreBrownian ℱ W P ↔
      IsPreBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P ∧
        (∀ i, Adapted ℱ (fun t ω ↦ ⟪b i, W t ω⟫)) ∧
        ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
          Indep (.comap (fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫) inferInstance) (ℱ s) P := by
  have : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  constructor
  · intro hW
    refine ⟨hW.isPreBrownianVector_inner b,
      fun i ↦ (hW.isFilteredPreBrownianReal_orthonormalBasis b i).adapted, fun s t hst ↦ ?_⟩
    have hcomp : (fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫) =
        (fun (x : E) (i : ι) ↦ ⟪b i, x⟫) ∘ (W t - W s) := by
      ext ω i
      simp [inner_sub_right]
    have hg : Measurable fun (x : E) (i : ι) ↦ ⟪b i, x⟫ :=
      (continuous_pi fun i ↦ (innerSL ℝ (b i)).continuous).measurable
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact indep_of_indep_of_le_left (hW.indep_sub hst) (MeasurableSpace.comap_mono hg.comap_le)
  · rintro ⟨hB, hadapt, hindep⟩
    have hsum_meas : Measurable fun z : ι → ℝ ↦ ∑ i, z i • b i :=
      Continuous.measurable (by fun_prop)
    refine ⟨(isPreBrownian_iff_isPreBrownianVector b).mpr hB, fun t ↦ ?_, fun s t hst ↦ ?_⟩
    · have hcoord : Measurable[ℱ t] (fun ω i ↦ ⟪b i, W t ω⟫) :=
        (@measurable_pi_iff Ω ι (fun _ ↦ ℝ) (ℱ t) _ _).mpr fun i ↦ hadapt i t
      have heq : W t = (fun z : ι → ℝ ↦ ∑ i, z i • b i) ∘ fun ω i ↦ ⟪b i, W t ω⟫ := by
        ext ω
        simpa [b.repr_apply_apply] using (b.sum_repr (W t ω)).symm
      rw [heq]
      exact hsum_meas.comp hcoord
    · have hcomp : W t - W s =
          (fun z : ι → ℝ ↦ ∑ i, z i • b i) ∘ fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫ := by
        ext ω
        simpa [b.repr_apply_apply, inner_sub_right] using (b.sum_repr (W t ω - W s ω)).symm
      rw [hcomp, ← MeasurableSpace.comap_comp]
      exact indep_of_indep_of_le_left (hindep hst) (MeasurableSpace.comap_mono hsum_meas.comap_le)

/-- Characterization of `IsFilteredBrownian ℱ W P` in terms of a finite orthonormal basis `b`. -/
theorem isFilteredBrownian_iff_orthonormalBasis {ℱ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → E} (b : OrthonormalBasis ι ℝ E) :
    IsFilteredBrownian ℱ W P ↔
      IsBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P ∧
        (∀ i, Adapted ℱ (fun t ω ↦ ⟪b i, W t ω⟫)) ∧
        ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
          Indep (.comap (fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫) inferInstance) (ℱ s) P := by
  constructor
  · intro hW
    obtain ⟨_, hadapt, hindep⟩ :=
      (isFilteredPreBrownian_iff_orthonormalBasis b).mp hW.toIsFilteredPreBrownian
    exact ⟨hW.toIsBrownian.isBrownianVector_inner b, hadapt, hindep⟩
  · rintro ⟨hB, hadapt, hindep⟩
    exact .of_isBrownian ((isBrownian_iff_isBrownianVector b).mpr hB)
      ((isFilteredPreBrownian_iff_orthonormalBasis b).mpr
        ⟨hB.toIsPreBrownianVector, hadapt, hindep⟩).adapted
      ((isFilteredPreBrownian_iff_orthonormalBasis b).mpr
        ⟨hB.toIsPreBrownianVector, hadapt, hindep⟩).indep_sub

end OrthonormalBasis

section FiniteDimensional

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- On a finite-dimensional real inner-product space, every marginal `W t` of a filtered vector
pre-Brownian motion is independent of any `ℱ 0`-measurable random variable `ξ`. -/
theorem IsFilteredPreBrownian.indepFun_eval_of_measurable_zero {ℱ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → E} (hW : IsFilteredPreBrownian ℱ W P) {G : Type*} [MeasurableSpace G]
    {ξ : Ω → G} (hξ : Measurable[ℱ 0] ξ) (t : ℝ≥0) :
    IndepFun (W t) ξ P := by
  have h : IndepFun (W t - W 0) ξ P :=
    indep_of_indep_of_le_right (hW.indep_sub (zero_le (a := t))) hξ.comap_le
  refine h.congr ?_ Filter.EventuallyEq.rfl
  filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
  simp [hω]

/-- Strongly measurable time marginals of the canonical Kolmogorov vector pre-Brownian motion on
`Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ`. -/
theorem stronglyMeasurable_sum_smul_pi (t : ℝ≥0) :
    StronglyMeasurable fun ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ ↦
      ∑ i, ω i t • stdOrthonormalBasis ℝ E i :=
  ((Continuous.measurable (by fun_prop :
      Continuous fun x : Fin (Module.finrank ℝ E) → ℝ ↦
        ∑ i, x i • stdOrthonormalBasis ℝ E i)).comp
    (measurable_pi_iff.mpr fun i ↦
      (measurable_pi_apply t).comp (measurable_pi_apply i))).stronglyMeasurable

/-- Unconditional concrete witness of `IsFilteredPreBrownian` on any finite-dimensional real
inner-product space `E`, relative to its natural filtration on the product Kolmogorov space. -/
theorem isFilteredPreBrownian_sum_smul_pi_gaussianLimit :
    IsFilteredPreBrownian
      (Filtration.natural
        (fun t (ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ) ↦
          ∑ i, ω i t • stdOrthonormalBasis ℝ E i)
        stronglyMeasurable_sum_smul_pi)
      (fun t (ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ) ↦
        ∑ i, ω i t • stdOrthonormalBasis ℝ E i)
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ gaussianLimit) :=
  isPreBrownian_sum_smul_pi_gaussianLimit.isFilteredPreBrownian_natural
    stronglyMeasurable_sum_smul_pi

end FiniteDimensional

end TauCeti.Probability

namespace MeasureTheory.Adapted

open TauCeti.Probability ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {X : ℝ≥0 → Ω → E}

/-- An adapted process in a finite-dimensional real inner-product space `E` starting at `0` almost
surely whose increments `X t - X s` (`s ≤ t`) have law `(stdGaussian E).map (√(t - s) • ·)` and are
independent of `ℱ s` is a filtered vector pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownian (hX : Adapted ℱ X) (h0 : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
      HasLaw (X t - X s) ((stdGaussian E).map (fun x : E ↦ √((t - s : ℝ≥0) : ℝ) • x)) P)
    (hindep : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) P) :
    IsFilteredPreBrownian ℱ X P := by
  have := (hlaw (le_refl 0)).isProbabilityMeasure
  refine ⟨HasIndepIncrements.isPreBrownian_of_hasLaw (fun t ↦ ?_)
    (hX.hasIndepIncrements hindep), hX, hindep⟩
  refine (tsub_zero t ▸ hlaw (zero_le (a := t))).congr ?_
  filter_upwards [h0] with ω hω
  simp [hω]

end MeasureTheory.Adapted
