/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Distribution.Mass.Measure
public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Borel weights and Borel restrictions of functionals of locally finite mass

Let `Ω` be an open set of a finite-dimensional real normed space `E` and let
`T : 𝓓^{n}(Ω, F) → ℝ` be a real-linear map of locally finite mass, with mass measure `‖T‖`
(`Distribution.massMeasure`). With `F = E [⋀^Fin k]→L[ℝ] ℝ` this is a `k`-current of locally
finite mass. Since `|T φ| ≤ ∫ ‖φ‖ d‖T‖` and the tests are dense in `L¹(‖T‖; F)`
(`TestFunction.denseRange_toLp`), `T` extends uniquely to a continuous linear functional
`Distribution.extendL1 T` on `L¹(‖T‖; F)` of norm at most one. This extension evaluates `T`
on every `F`-valued function integrable for `‖T‖`, for instance on compactly supported continuous
forms, and on tests multiplied by Borel weights.

For a function `g : Ω → ℝ` locally integrable for `‖T‖` this defines the *weighted* functional
`T ⌞ g = Distribution.withDensity T g`, `(T ⌞ g) φ = T̄ (g φ)`, where `T̄` is the extension. It is
again continuous and real-linear with locally finite mass, its mass measure is at most
`|g| ‖T‖`, it is additive in `g`, and for a smooth `g` it is the smooth multiple
`T ∘ (g ·)`. Locally bounded Borel weights are locally integrable for `‖T‖`, which is finite on
compact subsets of `Ω`; so are the indicators of Borel sets.

The *Borel restriction* `T ⌞ s = Distribution.restrict T s` to a measurable subset `s` of `Ω` is
the weight by the indicator of `s`. Its mass measure is exactly the restriction of `‖T‖` to `s`, and
`T = T ⌞ s + T ⌞ sᶜ`. In particular the Borel restriction of a functional of finite mass has
finite mass `‖T‖ s`. Nothing is claimed about the boundary of `T ⌞ s` for a current `T`: it need
not have locally finite mass even when the boundary of `T` does.

## Main declarations

* `Distribution.extendL1`: the extension of `T` to `L¹(‖T‖; F)`, with `extendL1_toLp`,
  `norm_extendL1_apply_le` and the uniqueness statement `extendL1_unique`.
* `Distribution.withDensity`: the weighted functional `T ⌞ g`, with `withDensity_apply`, the
  domination `enorm_withDensity_apply_le`, `hasLocallyFiniteMass_withDensity`,
  `massMeasure_withDensity_le`, `withDensity_one_apply`, `withDensity_add` and
  `withDensity_apply_of_contDiff`.
* `Distribution.restrict`: the Borel restriction `T ⌞ s`, with `massMeasure_restrict`,
  `restrict_apply_add_restrict_compl_apply` and `mass_restrict`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the extension of a current representable by
  integration to `‖T‖`-integrable forms, and its restriction `T ⌞ A` to Borel sets).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (currents of locally finite
  mass and their restrictions).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}
  [MeasurableSpace E] [BorelSpace E]
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ] {T : 𝓕}
  {g g' : Ω → ℝ}

/-- The domination `|T φ| ≤ ∫ ‖φ‖ d‖T‖`, as a bound by the `L¹(‖T‖)` norm. -/
private theorem norm_apply_le_norm_toLp (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    ‖LinearMap.ofClass T φ‖ ≤ 1 * ‖TestFunction.toLp 1 (massMeasure T) φ‖ := by
  rw [LinearMap.coe_ofClass, one_mul, ← enorm_le_iff_norm_le, TestFunction.enorm_toLp,
    eLpNorm_one_eq_lintegral_enorm]
  · exact enorm_apply_le_lintegral_massMeasure hT φ
  · exact (φ.continuous.comp continuous_subtype_val).aestronglyMeasurable

variable (T) in
/-- The **extension of a functional of locally finite mass to `L¹(‖T‖)`**: the continuous linear
functional on `L¹(‖T‖; F)` that agrees with `T` on test functions (`Distribution.extendL1_toLp`)
and has norm at most one (`Distribution.norm_extendL1_apply_le`). It is unique with these
properties (`Distribution.extendL1_unique`). If `T` does not have locally finite mass, it is the
zero functional on the zero space. -/
def extendL1 (T : 𝓕) : Lp F 1 (massMeasure T) →L[ℝ] ℝ :=
  (LinearMap.ofClass T).extendOfNorm (TestFunction.toLp 1 (massMeasure T))

/-- A test multiplied by a locally integrable weight is integrable. -/
private theorem integrable_smul (hg : LocallyIntegrable g (massMeasure T)) (φ : 𝓓^{n}(Ω, F)) :
    Integrable (fun x : Ω => g x • φ x) (massMeasure T) := by
  simpa using TestFunction.integrable_bilin_subtype (ContinuousLinearMap.lsmul ℝ ℝ).flip hg φ

/-- Multiplication of tests by a locally integrable weight, with values in `L¹(‖T‖; F)`. -/
private def smulToL1 (hg : LocallyIntegrable g (massMeasure T)) :
    𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F 1 (massMeasure T) where
  toFun φ := (integrable_smul hg φ).toL1 _
  map_add' φ ψ := by
    rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
    exact Filter.Eventually.of_forall fun x => by simp [smul_add]
  map_smul' c φ := by
    rw [RingHom.id_apply, ← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
    exact Filter.Eventually.of_forall fun x => by simp [smul_comm c]

private theorem enorm_smulToL1 (hg : LocallyIntegrable g (massMeasure T)) (φ : 𝓓^{n}(Ω, F)) :
    ‖smulToL1 hg φ‖ₑ = ∫⁻ x, ‖g x‖ₑ * ‖φ x‖ₑ ∂massMeasure T := by
  simp [smulToL1, Integrable.enorm_toL1, enorm_smul]

/-- The weight `|g| ‖T‖` is finite on compact sets for locally integrable `g`. -/
private theorem isFiniteMeasureOnCompacts_withDensity (hg : LocallyIntegrable g (massMeasure T)) :
    IsFiniteMeasureOnCompacts ((massMeasure T).withDensity fun x => ‖g x‖ₑ) := by
  refine ⟨fun K hK => ?_⟩
  rw [withDensity_apply _ hK.measurableSet]
  exact (hg.integrableOn_isCompact hK).hasFiniteIntegral

private theorem lintegral_withDensity_enorm (hg : LocallyIntegrable g (massMeasure T))
    (φ : 𝓓^{n}(Ω, F)) :
    ∫⁻ x, ‖φ x‖ₑ ∂(massMeasure T).withDensity (fun x => ‖g x‖ₑ) =
      ∫⁻ x, ‖g x‖ₑ * ‖φ x‖ₑ ∂massMeasure T :=
  lintegral_withDensity_eq_lintegral_mul₀ hg.aestronglyMeasurable.enorm
    (φ.continuous.comp continuous_subtype_val).enorm.aemeasurable

variable [CompleteSpace F]

section Extension

/-- **The extension evaluates `T` on tests.** -/
@[simp]
theorem extendL1_toLp (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    extendL1 T (TestFunction.toLp 1 (massMeasure T) φ) = T φ :=
  LinearMap.extendOfNorm_eq (TestFunction.denseRange_toLp ENNReal.one_ne_top)
    ⟨1, norm_apply_le_norm_toLp hT⟩ φ

/-- **The extension has norm at most one:** `|T̄ f| ≤ ∫ ‖f‖ d‖T‖`. -/
theorem norm_extendL1_apply_le (hT : HasLocallyFiniteMass T) (f : Lp F 1 (massMeasure T)) :
    ‖extendL1 T f‖ ≤ ‖f‖ := by
  simpa [extendL1] using LinearMap.norm_extendOfNorm_apply_le
    (TestFunction.denseRange_toLp ENNReal.one_ne_top) 1 (norm_apply_le_norm_toLp hT) f

/-- The operator norm of the extension is at most one. -/
theorem opNorm_extendL1_le (hT : HasLocallyFiniteMass T) : ‖extendL1 T‖ ≤ 1 :=
  (extendL1 T).opNorm_le_bound zero_le_one fun f => by
    simpa using norm_extendL1_apply_le hT f

/-- **Uniqueness of the extension.** A continuous linear functional on `L¹(‖T‖; F)` that agrees
with `T` on tests is the extension of `T`. -/
theorem extendL1_unique (hT : HasLocallyFiniteMass T) (S : Lp F 1 (massMeasure T) →L[ℝ] ℝ)
    (hS : ∀ φ : 𝓓^{n}(Ω, F), S (TestFunction.toLp 1 (massMeasure T) φ) = T φ) :
    extendL1 T = S :=
  LinearMap.extendOfNorm_unique (TestFunction.denseRange_toLp ENNReal.one_ne_top) 1
    (norm_apply_le_norm_toLp hT) S (LinearMap.ext hS)

end Extension

section WithDensity

/-- The weighted functional as a linear map. -/
private def withDensityLM (hg : LocallyIntegrable g (massMeasure T)) : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ :=
  (extendL1 T).toLinearMap ∘ₗ smulToL1 hg

private theorem enorm_withDensityLM_apply_le (hT : HasLocallyFiniteMass T)
    (hg : LocallyIntegrable g (massMeasure T)) (φ : 𝓓^{n}(Ω, F)) :
    ‖withDensityLM hg φ‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ * ‖φ x‖ₑ ∂massMeasure T := by
  rw [← enorm_smulToL1 hg, enorm_le_iff_norm_le]
  exact norm_extendL1_apply_le hT _

open Classical in
variable (T) in
/-- The **weighted functional** `T ⌞ g`: for a weight `g : Ω → ℝ` locally integrable for the mass
measure `‖T‖`, the continuous linear map `φ ↦ T̄ (g φ)`, where `T̄ = Distribution.extendL1 T` is the
extension of `T` to `L¹(‖T‖)`. For a smooth `g` it is `T ∘ (g ·)`
(`Distribution.withDensity_apply_of_contDiff`). If `T` does not have locally finite mass or `g` is
not locally integrable, it is zero by convention. -/
def withDensity (g : Ω → ℝ) : 𝓓^{n}(Ω, F) →L[ℝ] ℝ :=
  if h : HasLocallyFiniteMass T ∧ LocallyIntegrable g (massMeasure T) then
    haveI := isFiniteMeasureOnCompacts_withDensity h.2
    { toLinearMap := withDensityLM h.2
      cont := (hasLocallyFiniteMass_of_enorm_apply_le _ fun φ => by
        rw [lintegral_withDensity_enorm h.2]
        exact enorm_withDensityLM_apply_le h.1 h.2 φ).continuous }
  else 0

/-- The value of `T ⌞ g` on a test `φ` is the value of the extension `T̄` on `g φ`. -/
theorem withDensity_apply (hT : HasLocallyFiniteMass T) (hg : LocallyIntegrable g (massMeasure T))
    (φ : 𝓓^{n}(Ω, F)) {f : Lp F 1 (massMeasure T)} (hf : ⇑f =ᵐ[massMeasure T] fun x => g x • φ x) :
    withDensity T g φ = extendL1 T f := by
  rw [withDensity, dite_eq_left ⟨hT, hg⟩]
  exact congrArg (extendL1 T) (Lp.ext ((integrable_smul hg φ).coeFn_toL1.trans hf.symm))

/-- **Domination of the weighted functional:** `|(T ⌞ g) φ| ≤ ∫ |g| ‖φ‖ d‖T‖`. -/
theorem enorm_withDensity_apply_le (φ : 𝓓^{n}(Ω, F)) :
    ‖withDensity T g φ‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ * ‖φ x‖ₑ ∂massMeasure T := by
  by_cases h : HasLocallyFiniteMass T ∧ LocallyIntegrable g (massMeasure T)
  · rw [withDensity, dite_eq_left h]
    exact enorm_withDensityLM_apply_le h.1 h.2 φ
  · simp [withDensity, dite_eq_right h]

/-- The weighted functional has locally finite mass. -/
theorem hasLocallyFiniteMass_withDensity (hg : LocallyIntegrable g (massMeasure T)) :
    HasLocallyFiniteMass (withDensity T g) :=
  haveI := isFiniteMeasureOnCompacts_withDensity hg
  hasLocallyFiniteMass_of_enorm_apply_le _ fun φ => by
    rw [lintegral_withDensity_enorm hg]
    exact enorm_withDensity_apply_le φ

/-- **The mass measure of a weighted functional** is at most `|g| ‖T‖`. -/
theorem massMeasure_withDensity_le (hg : LocallyIntegrable g (massMeasure T)) :
    massMeasure (withDensity T g) ≤ (massMeasure T).withDensity fun x => ‖g x‖ₑ := by
  have := isFiniteMeasureOnCompacts_withDensity hg
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  refine massMeasure_le_of_enorm_apply_le _ fun φ => ?_
  rw [lintegral_withDensity_enorm hg]
  exact enorm_withDensity_apply_le φ

/-- The weight one gives back the functional. -/
@[simp]
theorem withDensity_one_apply (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    withDensity T 1 φ = T φ := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  rw [withDensity_apply (g := 1) hT (locallyIntegrable_const 1) φ
    ((TestFunction.coeFn_toLp φ).trans (Filter.Eventually.of_forall fun x => by simp)),
    extendL1_toLp hT]

/-- The weighted functional is additive in the weight. -/
theorem withDensity_add (hg : LocallyIntegrable g (massMeasure T))
    (hg' : LocallyIntegrable g' (massMeasure T)) :
    withDensity T (g + g') = withDensity T g + withDensity T g' := by
  by_cases hT : HasLocallyFiniteMass T
  · ext φ
    have h := (integrable_smul hg φ).coeFn_toL1
    have h' := (integrable_smul hg' φ).coeFn_toL1
    rw [add_apply, withDensity_apply hT hg φ h,
      withDensity_apply hT hg' φ h', ← map_add, withDensity_apply hT (hg.add hg') φ]
    filter_upwards [Lp.coeFn_add (integrable_smul hg φ |>.toL1 _)
      (integrable_smul hg' φ |>.toL1 _), h, h'] with x hx hx₁ hx₂
    rw [hx, Pi.add_apply, hx₁, hx₂, Pi.add_apply, add_smul]
  · simp [withDensity, hT]

/-- **Smooth weights.** For a smooth function `f`, the weighted functional `T ⌞ f` is the smooth
multiple `T ∘ (f ·)`. -/
theorem withDensity_apply_of_contDiff (hT : HasLocallyFiniteMass T) {f : E → ℝ}
    (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) :
    withDensity T (fun x : Ω => f x) φ = T (TestFunction.smulLeftCLM hf φ) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  rw [withDensity_apply (g := fun x : Ω => f x) hT
    (hf.continuous.comp continuous_subtype_val).locallyIntegrable φ
    ((TestFunction.coeFn_toLp (TestFunction.smulLeftCLM hf φ)).trans
      (Filter.Eventually.of_forall fun x => by simp)),
    extendL1_toLp hT]

end WithDensity

section Restrict

variable {s : Set Ω}

omit [CompleteSpace F] in
private theorem locallyIntegrable_indicator (hs : MeasurableSet s) :
    LocallyIntegrable (s.indicator (1 : Ω → ℝ)) (massMeasure T) :=
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  (locallyIntegrable_const 1).indicator hs

variable (T) in
/-- The **Borel restriction** `T ⌞ s` of a functional of locally finite mass to a subset `s` of `Ω`:
the weighted functional `T ⌞ 1_s`, so that `(T ⌞ s) φ = T̄ (1_s φ)` with `T̄` the extension of `T`
to `L¹(‖T‖)`. For a measurable `s` its mass measure is the restriction of `‖T‖` to `s`
(`Distribution.massMeasure_restrict`). -/
def restrict (s : Set Ω) : 𝓓^{n}(Ω, F) →L[ℝ] ℝ :=
  withDensity T (s.indicator 1)

/-- The Borel restriction is the weighted functional for the indicator of `s`. -/
theorem restrict_eq_withDensity : restrict T s = withDensity T (s.indicator 1) :=
  (rfl)

/-- **Domination of the Borel restriction:** `|(T ⌞ s) φ| ≤ ∫_s ‖φ‖ d‖T‖`. -/
theorem enorm_restrict_apply_le (hs : MeasurableSet s) (φ : 𝓓^{n}(Ω, F)) :
    ‖restrict T s φ‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ ∂(massMeasure T).restrict s := by
  rw [restrict_eq_withDensity]
  refine (enorm_withDensity_apply_le φ).trans_eq ?_
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx]

/-- The Borel restriction has locally finite mass. -/
theorem hasLocallyFiniteMass_restrict (hs : MeasurableSet s) :
    HasLocallyFiniteMass (restrict T s) := by
  rw [restrict_eq_withDensity]
  exact hasLocallyFiniteMass_withDensity (locallyIntegrable_indicator hs)

/-- A functional of locally finite mass is the sum of its Borel restrictions to a measurable set
and to its complement. -/
theorem restrict_apply_add_restrict_compl_apply (hT : HasLocallyFiniteMass T)
    (hs : MeasurableSet s) (φ : 𝓓^{n}(Ω, F)) :
    restrict T s φ + restrict T sᶜ φ = T φ := by
  rw [restrict_eq_withDensity, restrict_eq_withDensity, ← add_apply,
    ← withDensity_add (locallyIntegrable_indicator hs) (locallyIntegrable_indicator hs.compl),
    indicator_self_add_compl, withDensity_one_apply hT]

/-- The Borel restriction to all of `Ω` is the functional itself. -/
@[simp]
theorem restrict_univ_apply (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    restrict T univ φ = T φ := by
  rw [restrict_eq_withDensity, indicator_univ, withDensity_one_apply hT]

/-- **The mass measure of a Borel restriction** is the restriction of the mass measure:
`‖T ⌞ s‖ = ‖T‖ ⌞ s`. -/
theorem massMeasure_restrict (hT : HasLocallyFiniteMass T) (hs : MeasurableSet s) :
    massMeasure (restrict T s) = (massMeasure T).restrict s := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  -- `‖T ⌞ s‖ ≤ ‖T‖ ⌞ s` by minimality.
  have hle (t : Set Ω) (ht : MeasurableSet t) :
      massMeasure (restrict T t) ≤ (massMeasure T).restrict t :=
    massMeasure_le_of_enorm_apply_le _ (enorm_restrict_apply_le ht)
  refine le_antisymm (hle s hs) ?_
  -- `T = T ⌞ s + T ⌞ sᶜ` is dominated by `ν = ‖T ⌞ s‖ + ‖T‖ ⌞ sᶜ`, so `‖T‖ ≤ ν`.
  set ν := massMeasure (restrict T s) + (massMeasure T).restrict sᶜ
  have hν : ν ≤ massMeasure T :=
    (add_le_add_left (hle s hs) _).trans (Measure.restrict_add_restrict_compl hs).le
  have : IsLocallyFiniteMeasure ν := Measure.isLocallyFiniteMeasure_of_le hν
  have hTν : massMeasure T ≤ ν := massMeasure_le_of_enorm_apply_le ν fun φ => by
    rw [← restrict_apply_add_restrict_compl_apply hT hs φ, lintegral_add_measure]
    exact (enorm_add_le _ _).trans (add_le_add
      (enorm_apply_le_lintegral_massMeasure (hasLocallyFiniteMass_restrict hs) φ)
      (enorm_restrict_apply_le hs.compl φ))
  -- On subsets of `s` the second summand of `ν` vanishes.
  refine Measure.le_iff.2 fun t ht => ?_
  rw [Measure.restrict_apply ht]
  calc massMeasure T (t ∩ s) ≤ ν (t ∩ s) := hTν _
    _ = massMeasure (restrict T s) (t ∩ s) := by
        simp [ν, Measure.restrict_apply (ht.inter hs), inter_assoc]
    _ ≤ massMeasure (restrict T s) t := measure_mono inter_subset_left

/-- The mass of a Borel restriction is the mass measure of the set; in particular the Borel
restriction of a functional of finite mass has finite mass. -/
theorem mass_restrict (hT : HasLocallyFiniteMass T) (hs : MeasurableSet s) :
    mass (restrict T s) = massMeasure T s := by
  rw [← massMeasure_univ (hasLocallyFiniteMass_restrict hs), massMeasure_restrict hT hs,
    Measure.restrict_apply_univ]

end Restrict

end Distribution
