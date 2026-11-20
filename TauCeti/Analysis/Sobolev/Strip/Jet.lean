/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv

/-!
# The strip measure and jets of sections over the strip

Sections of a trivial bundle with fibre `V` over the strip `ℝ × [0, 1]` are maps
`ξ : ℝ × ℝ → V`. This file collects the measure and the jets shared by the Sobolev spaces built
over the strip: the Sobolev space with boundary conditions in
`TauCeti.Analysis.Sobolev.Strip.Basic` and the Sobolev space of the cylinder `ℝ × S¹`, whose
fundamental domain is the strip, in `TauCeti.Analysis.Sobolev.Cylinder`.

* `TauCeti.StripSobolev.stripMeasure` is Lebesgue measure on `ℝ × [0, 1]`; it is the product of
  Lebesgue measure on `ℝ` and on `[0, 1]` (`TauCeti.StripSobolev.stripMeasure_eq_prod`).
* The **jet** of a section is `TauCeti.StripSobolev.jet ξ = (ξ, ∂s ξ, ∂t ξ)`. It is continuous for
  `C¹` maps, linear on differentiable maps, vanishes where the section vanishes near a point,
  bounds each of its components (`TauCeti.StripSobolev.norm_le_norm_jet`,
  `TauCeti.StripSobolev.norm_fderiv_one_zero_le_norm_jet`,
  `TauCeti.StripSobolev.norm_fderiv_zero_one_le_norm_jet`), and is in `Lᵖ` on the strip for a
  `C¹` map vanishing for `|s|` large (`TauCeti.StripSobolev.memLp_jet_of_contDiff`).
* **Translation in the `s` direction** preserves the strip measure
  (`TauCeti.StripSobolev.measurePreserving_add_strip`) and commutes with taking jets
  (`TauCeti.StripSobolev.jet_comp_add`). It acts on `Lᵖ` of the strip by linear isometric
  equivalences (`TauCeti.StripSobolev.translateLp`), an action of the additive group `ℝ`
  (`TauCeti.StripSobolev.translateLp_zero`, `TauCeti.StripSobolev.translateLp_translateLp`,
  `TauCeti.StripSobolev.translateLp_symm`).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lebesgue measure on the strip `ℝ × [0, 1]`, the fundamental domain of the cylinder
`ℝ × S¹`. -/
abbrev stripMeasure : Measure (ℝ × ℝ) := volume.restrict (univ ×ˢ Icc 0 1)

/-- The strip measure is the product of Lebesgue measure on `ℝ` and on `[0, 1]`, so that
integrals over the strip are iterated integrals over the segments `{s} × [0, 1]`. -/
theorem stripMeasure_eq_prod :
    stripMeasure = (volume : Measure ℝ).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
  unfold stripMeasure
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- The jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`. -/
def jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V :=
  (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))

/-- The components of the jet. -/
theorem jet_apply (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    jet ξ z = (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) :=
  (rfl)

/-- The jet bounds the section. -/
theorem norm_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : ‖ξ z‖ ≤ ‖jet ξ z‖ := by
  rw [jet_apply]
  exact norm_fst_le (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))

/-- The jet bounds the `s`-derivative. -/
theorem norm_fderiv_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z (1, 0)‖ ≤ ‖jet ξ z‖ := by
  rw [jet_apply]
  exact (norm_fst_le (fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))).trans
    (norm_snd_le (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)))

/-- The jet bounds the `t`-derivative. -/
theorem norm_fderiv_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z (0, 1)‖ ≤ ‖jet ξ z‖ := by
  rw [jet_apply]
  exact (norm_snd_le (fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))).trans
    (norm_snd_le (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)))

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a `C¹` map is continuous. -/
theorem continuous_jet (hξ : ContDiff ℝ 1 ξ) : Continuous (jet ξ) := by
  have := hξ.continuous_fderiv (by norm_num)
  have := hξ.continuous
  unfold jet
  fun_prop

/-- The jet is additive on differentiable maps. -/
theorem jet_add (hξ : Differentiable ℝ ξ) (hη : Differentiable ℝ η) :
    jet (ξ + η) = jet ξ + jet η := by
  funext z
  simp [jet, fderiv_add (hξ z) (hη z)]

/-- The jet commutes with scalar multiplication. -/
theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) : jet (c • ξ) = c • jet ξ := by
  funext z
  simp [jet, fderiv_const_smul_field]

/-- The jet of a section vanishing for `|s| ≥ R` vanishes for `|s| > R`. -/
theorem jet_eq_zero_of_lt_abs {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {z : ℝ × ℝ}
    (hz : R < |z.1|) : jet ξ z = 0 := by
  have : ∀ᶠ w : ℝ × ℝ in 𝓝 z, R < |w.1| :=
    (continuous_abs.comp continuous_fst).continuousAt.eventually (lt_mem_nhds hz)
  have h : ξ =ᶠ[𝓝 z] 0 := by
    filter_upwards [this] with w hw
    exact hR w.1 w.2 hw.le
  simp [jet, h.fderiv_eq, h.eq_of_nhds]

/-- The jet of a `C¹` map vanishing for `|s|` large is in `Lᵖ` on the strip for every `p`. -/
theorem memLp_jet_of_contDiff (hξ : ContDiff ℝ 1 ξ) {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {p : ℝ≥0∞} : MemLp (jet ξ) p stripMeasure := by
  set K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hae : jet ξ =ᵐ[stripMeasure] K.indicator (jet ξ) := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
    · rw [indicator_of_notMem hzK]
      refine jet_eq_zero_of_lt_abs hR ?_
      by_contra h
      exact hzK ⟨abs_le.1 (not_lt.1 h), hz.2⟩
  refine (memLp_congr_ae hae).2 ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet]
  have : IsFiniteMeasure (stripMeasure.restrict K) :=
    isFiniteMeasure_restrict.2 ((Measure.restrict_apply_le _ K).trans_lt
      hK.measure_lt_top).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_jet hξ).continuousOn
  exact MemLp.of_bound (continuous_jet hξ).aestronglyMeasurable C
    ((ae_restrict_mem hK.measurableSet).mono hC)

/-! ### Translation in the `s` direction -/

/-- Translation by `a` in the `s` direction preserves the strip measure. -/
theorem measurePreserving_add_strip (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ z + (a, 0)) stripMeasure stripMeasure := by
  have h₀ : MeasurePreserving (fun z : ℝ × ℝ ↦ z + (a, 0)) volume volume := by
    have h := (measurePreserving_add_right (volume : Measure ℝ) a).prod
      (MeasurePreserving.id (volume : Measure ℝ))
    rw [← Measure.volume_eq_prod] at h
    convert h using 1
    ext z <;> simp
  have h := h₀.restrict_preimage
    (MeasurableSet.univ.prod (measurableSet_Icc (a := (0 : ℝ)) (b := 1)))
  have hpre : (fun z : ℝ × ℝ ↦ z + (a, 0)) ⁻¹' (univ ×ˢ Icc 0 1) = univ ×ˢ Icc (0 : ℝ) 1 := by
    ext z
    simp
  rwa [hpre] at h

/-- The jet of a translate is the translate of the jet. -/
theorem jet_comp_add (a : ℝ) (z : ℝ × ℝ) :
    jet (fun w ↦ ξ (w + (a, 0))) z = jet ξ (z + (a, 0)) := by
  simp only [jet_apply, fderiv_comp_add_right]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation by `a` in the `s` direction, on `Lᵖ` of the strip, as a linear isometric
equivalence with inverse the translation by `-a`. -/
def translateLp (a : ℝ) : Lp E p stripMeasure ≃ₗᵢ[ℝ] Lp E p stripMeasure :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_add_strip a)
    (measurePreserving_add_strip (-a)) (EventuallyEq.of_eq (funext fun z ↦ by ext <;> simp))

/-- `translateLp a` is the composition with the translation by `a`. -/
theorem translateLp_apply (a : ℝ) (x : Lp E p stripMeasure) :
    translateLp a x = Lp.compMeasurePreserving _ (measurePreserving_add_strip a) x :=
  Lp.compMeasurePreservingₗᵢEquiv_apply ℝ _ _ _ x

/-- The translate of an `Lᵖ` class is represented by the translate of its representative. -/
theorem coeFn_translateLp (a : ℝ) (x : Lp E p stripMeasure) :
    translateLp a x =ᵐ[stripMeasure] fun z ↦ x (z + (a, 0)) := by
  rw [translateLp_apply]
  exact Lp.coeFn_compMeasurePreserving _ _

/-- Translation by `a`, then by `b`, is translation by `a + b`. -/
@[simp]
theorem translateLp_translateLp (a b : ℝ) (x : Lp E p stripMeasure) :
    translateLp a (translateLp b x) = translateLp (a + b) x := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translateLp a (translateLp b x), coeFn_translateLp (a + b) x,
    (measurePreserving_add_strip a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateLp b x)] with z h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃, add_assoc]
  simp

/-- Translation by `0` is the identity. -/
@[simp]
theorem translateLp_zero (x : Lp E p stripMeasure) : translateLp 0 x = x := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translateLp 0 x] with z hz
  rwa [Prod.mk_zero_zero, add_zero] at hz

/-- The inverse of translation by `a` is translation by `-a`. -/
@[simp]
theorem translateLp_symm (a : ℝ) : (translateLp (E := E) (p := p) a).symm = translateLp (-a) :=
  LinearIsometryEquiv.ext fun x ↦ (LinearIsometryEquiv.symm_apply_eq _).2 <| by
    rw [translateLp_translateLp, add_neg_cancel, translateLp_zero]

end

end TauCeti.StripSobolev
