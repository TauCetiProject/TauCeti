/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Module
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import TauCeti.Topology.Compactness.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The strip measure and jets of sections over the strip

Sections of a trivial bundle with fibre `V` over the strip `ℝ × [0, 1]` are maps
`ξ : ℝ × ℝ → V`. This file collects the measure and the jets shared by the Sobolev spaces built
over the strip: the Sobolev space with boundary conditions in
`TauCeti.Analysis.Sobolev.Strip.Basic` and the Sobolev space of the cylinder `ℝ × S¹`, whose
fundamental domain is the strip, in `TauCeti.Analysis.Sobolev.Cylinder`.

* `TauCeti.StripSobolev.stripMeasure` is Lebesgue measure on `ℝ × [0, 1]`; it is the product of
  Lebesgue measure on `ℝ` and on `[0, 1]` (`TauCeti.StripSobolev.stripMeasure_eq_prod`), and
  Lebesgue measure on the bands `ℝ × [0, 1)` and `ℝ × (0, 1)`
  (`TauCeti.StripSobolev.stripMeasure_eq_restrict_univ_prod_Ico`,
  `TauCeti.StripSobolev.stripMeasure_eq_restrict_univ_prod_Ioo`).
  A section that is bounded on a box `[-R, R] × [0, 1]` and vanishes outside it lies in every `Lᵖ`
  of the strip (`TauCeti.StripSobolev.memLp_stripMeasure_of_bound_of_eq_zero`), in particular a
  continuous section vanishing for `|s|` large
  (`TauCeti.StripSobolev.memLp_stripMeasure_of_continuous`); so does `z ↦ Y (t, u z) (δ z)` for
  `δ` in `Lᵖ`, `u` continuous and `Y (t, x)` a continuous field vanishing for `x` outside a compact
  set (`TauCeti.StripSobolev.memLp_apply_of_eventually_eq_zero`).
* The **jet** of a section is `TauCeti.StripSobolev.jet ξ = (ξ, ∂s ξ, ∂t ξ)`. It is continuous for
  `C¹` maps, linear on differentiable maps, vanishes where the section vanishes near a point,
  bounds each of its components (`TauCeti.StripSobolev.norm_le_norm_jet`,
  `TauCeti.StripSobolev.norm_fderiv_one_zero_le_norm_jet`,
  `TauCeti.StripSobolev.norm_fderiv_zero_one_le_norm_jet`), and is in `Lᵖ` on the strip for a
  `C¹` map vanishing for `|s|` large (`TauCeti.StripSobolev.memLp_jet_of_contDiff`). For a
  section vanishing for `s ∉ (a, b)`, a function vanishing wherever the jet does has the same
  integral over the strip and over `[a, b] × [0, 1]`
  (`TauCeti.StripSobolev.integral_strip_eq_setIntegral_Icc_of_jet_eq_zero`), and is integrable
  on the strip when it is continuous (`TauCeti.StripSobolev.integrable_of_jet_eq_zero`). For a
  compactly supported `C¹` map, the pairing `⟪g, M (jet ξ)⟫` of a locally integrable function
  with a continuous coefficient field applied to the jet is integrable on the plane
  (`TauCeti.StripSobolev.integrable_inner_apply_jet`). The jet also
  bounds the whole derivative (`TauCeti.StripSobolev.norm_fderiv_le_two_mul_norm_jet`), so a `C¹`
  cutoff supported in a set `P` multiplies a section into a map whose derivative is bounded in
  `Lᵖ(ℝ²)` by the jet on `P` (`TauCeti.StripSobolev.eLpNorm_fderiv_smul_le`).
* The **restricted value** `TauCeti.StripSobolev.restrictValue T` takes an `L²` jet on the strip
  to its value on the compact piece `[-T, T] × [0, 1]`, the operator whose compactness is
  Rellich's theorem on the cylinder and on the strip.
* **Multiplication by a function `β(s)`** acts on jets through the coefficient field
  `TauCeti.StripSobolev.cutoffCoeff`, `(ξ, ξ_s, ξ_t) ↦ (β ξ, β ξ_s + β' ξ, β ξ_t)`
  (`TauCeti.StripSobolev.jet_smul_fst_eq_cutoffCoeff`), which is multiplicative and additive in
  `β` and essentially bounded on the strip when `β` is `C¹` with `β` and `β'` bounded
  (`TauCeti.StripSobolev.memLp_cutoffCoeff`).
* **Translation in the `s` direction** preserves the strip measure
  (`TauCeti.StripSobolev.measurePreserving_add_strip`) and commutes with taking jets
  (`TauCeti.StripSobolev.jet_comp_add`). It acts on `Lᵖ` of the strip by linear isometric
  equivalences (`TauCeti.StripSobolev.translateLp`), an action of the additive group `ℝ`
  (`TauCeti.StripSobolev.translateLp_zero`, `TauCeti.StripSobolev.translateLp_translateLp`,
  `TauCeti.StripSobolev.translateLp_symm`).
* For a space `S` of sections with jets in `Lᵖ` (`TauCeti.StripSobolev.HasLpJets`),
  `TauCeti.StripSobolev.jetLp p S` is the `Lᵖ` jet and `TauCeti.StripSobolev.jetClosure p S` the
  closure of the `Lᵖ` jets. For `1 ≤ p < ∞` it is the Sobolev space `W^{1,p}` shared by the strip
  and the cylinder; for `p = ∞` it is only the closure of the jets of `S`, not `W^{1,∞}`. The jets
  of the elements of `S` are dense in it (`TauCeti.StripSobolev.toJetClosure`,
  `TauCeti.StripSobolev.denseRange_toJetClosure`). When `S` is translation invariant
  (`TauCeti.StripSobolev.IsTranslationInvariant`), translation is a linear isometric equivalence
  of `jetClosure p S` (`TauCeti.StripSobolev.translate`).
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

/-- The strip measure is Lebesgue measure on the band `ℝ × [0, 1)`: the two differ by the null
line `ℝ × {1}`. -/
theorem stripMeasure_eq_restrict_univ_prod_Ico :
    stripMeasure = volume.restrict ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1) := by
  rw [stripMeasure_eq_prod, Measure.restrict_congr_set (μ := volume (α := ℝ))
    (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := 1)).symm, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- The strip measure is Lebesgue measure on the open band `ℝ × (0, 1)`: the two differ by the
null lines `ℝ × {0}` and `ℝ × {1}`. -/
theorem stripMeasure_eq_restrict_univ_prod_Ioo :
    stripMeasure = volume.restrict ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) := by
  rw [stripMeasure_eq_prod, Measure.restrict_congr_set (μ := volume (α := ℝ))
    (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1)).symm, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ]

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

/-- The operator norm of the derivative is at most twice the norm of the jet. -/
theorem norm_fderiv_le_two_mul_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z‖ ≤ 2 * ‖jet ξ z‖ := by
  linarith [(fderiv ℝ ξ z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one,
    norm_fderiv_one_zero_le_norm_jet ξ z, norm_fderiv_zero_one_le_norm_jet ξ z]

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

/-- The jet of a difference of differentiable maps is the difference of their jets. -/
theorem jet_sub (hξ : Differentiable ℝ ξ) (hη : Differentiable ℝ η) :
    jet (ξ - η) = jet ξ - jet η := by
  funext z
  simp [jet, fderiv_sub (hξ z) (hη z)]

/-- The jet commutes with scalar multiplication. -/
theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) : jet (c • ξ) = c • jet ξ := by
  funext z
  simp [jet, fderiv_const_smul_field]

/-- The jet of a section vanishing for `s ∉ (a, b)` vanishes for `s ∉ [a, b]`. -/
theorem jet_eq_zero_of_notMem_Icc {a b : ℝ} (hvan : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0)
    {z : ℝ × ℝ} (hz : z.1 ∉ Icc a b) : jet ξ z = 0 := by
  have h : ξ =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isClosed_Icc.isOpen_compl.preimage continuous_fst).mem_nhds hz] with w hw
    exact hvan w.1 w.2 fun h ↦ hw (Ioo_subset_Icc_self h)
  simp [jet, h.fderiv_eq, h.eq_of_nhds]

omit [NormedSpace ℝ V] in
/-- A section vanishing for `|s| ≥ R` vanishes for `s ∉ (-R, R)`. -/
theorem eq_zero_of_notMem_Ioo_neg {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) (s t : ℝ)
    (hs : s ∉ Ioo (-R) R) : ξ (s, t) = 0 :=
  hR s t (by rwa [mem_Ioo, ← abs_lt, not_lt] at hs)

/-- **The jet of a section cut off in `s`.** If `β` has derivative `β'` at `z.1` and `ξ` is
differentiable at `z`, then the jet of `w ↦ β(w.1) ξ w` at `z` is `β(z.1) (ξ, ∂s ξ, ∂t ξ)` plus
`(0, β' ξ z, 0)`: the factor only differentiates in the `s` direction. -/
theorem jet_smul_fst {β : ℝ → ℝ} {β' : ℝ} {z : ℝ × ℝ} (hβ : HasDerivAt β β' z.1)
    (hξ : DifferentiableAt ℝ ξ z) :
    jet (fun w ↦ β w.1 • ξ w) z = β z.1 • jet ξ z + (0, β' • ξ z, 0) := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 • ξ w) _ z :=
    (hβ.hasFDerivAt.comp z hasFDerivAt_fst).smul hξ.hasFDerivAt
  simp only [jet_apply, hd.fderiv]
  ext <;> simp [add_comm]

/-- The jet of a section vanishing for `|s| ≥ R` vanishes for `|s| > R`. -/
theorem jet_eq_zero_of_lt_abs {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {z : ℝ × ℝ}
    (hz : R < |z.1|) : jet ξ z = 0 :=
  jet_eq_zero_of_notMem_Icc (eq_zero_of_notMem_Ioo_neg hR) (by rwa [mem_Icc, ← abs_le, not_le])

omit [NormedSpace ℝ V] in
/-- A section bounded on `[-R, R] × [0, 1]` and vanishing for `|s| > R` lies in every `Lᵖ` of the
strip. -/
theorem memLp_stripMeasure_of_bound_of_eq_zero {u : ℝ × ℝ → V}
    (hu : AEStronglyMeasurable u stripMeasure) {C R : ℝ}
    (hC : ∀ z ∈ Icc (-R) R ×ˢ Icc 0 1, ‖u z‖ ≤ C) (hR : ∀ z : ℝ × ℝ, R < |z.1| → u z = 0)
    (p : ℝ≥0∞) : MemLp u p stripMeasure := by
  set K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  have hK : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : u =ᵐ[stripMeasure] K.indicator u := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ ?_
    by_cases hzR : |z.1| ≤ R
    · rw [indicator_of_mem (show z ∈ K from ⟨abs_le.1 hzR, hz.2⟩)]
    · rw [hR z (not_le.1 hzR), indicator_apply_eq_zero.2 fun _ ↦ hR z (not_le.1 hzR)]
  refine (memLp_congr_ae hae).2 ((memLp_indicator_iff_restrict hK.nullMeasurableSet).2 ?_)
  have : IsFiniteMeasure (stripMeasure.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ, stripMeasure, Measure.restrict_apply hK]
    exact (measure_mono inter_subset_left).trans_lt
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)⟩
  exact MemLp.of_bound hu.restrict C ((ae_restrict_mem hK).mono hC)

omit [NormedSpace ℝ V] in
/-- A continuous section vanishing for `|s| > R` is bounded on the strip `ℝ × [0, 1]`. -/
theorem exists_forall_mem_strip_norm_le {u : ℝ × ℝ → V} (hu : Continuous u) {R : ℝ}
    (hR : ∀ z : ℝ × ℝ, R < |z.1| → u z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖u z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-R) R ×ˢ Icc (0 : ℝ) 1) hu.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  by_cases hzR : R < |z.1|
  · rw [hR z hzR, norm_zero]
    exact le_max_right _ _
  · exact (hC z ⟨abs_le.1 (not_lt.1 hzR), hz.2⟩).trans (le_max_left _ _)

omit [NormedSpace ℝ V] in
/-- A continuous section vanishing for `|s| > R` lies in every `Lᵖ` of the strip. -/
theorem memLp_stripMeasure_of_continuous {u : ℝ × ℝ → V} (hu : Continuous u) {R : ℝ}
    (hR : ∀ z : ℝ × ℝ, R < |z.1| → u z = 0) (p : ℝ≥0∞) : MemLp u p stripMeasure := by
  obtain ⟨C, -, hC⟩ := exists_forall_mem_strip_norm_le hu hR
  exact memLp_stripMeasure_of_bound_of_eq_zero hu.aestronglyMeasurable
    (fun z hz ↦ hC z ⟨mem_univ _, hz.2⟩) hR p

omit [NormedSpace ℝ V] in
/-- The variation `z ↦ Y (t, u z) (δ z)` of a continuous field `Y (t, x)` vanishing for `x` outside
a compact set lies in `Lᵖ` of the strip when `δ` does. -/
theorem memLp_apply_of_eventually_eq_zero {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {Y : ℝ × V → W →L[ℝ] W} (hY : Continuous Y)
    (hYc : ∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) {u : ℝ × ℝ → V} (hu : Continuous u)
    {δ : ℝ × ℝ → W} {p : ℝ≥0∞} (hδ : MemLp δ p stripMeasure) :
    MemLp (fun z ↦ Y (z.2, u z) (δ z)) p stripMeasure := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_forall_norm_le_of_eventually_eq_zero
      hY.continuousOn hYc
  have hYu : Continuous fun z : ℝ × ℝ ↦ Y (z.2, u z) := hY.comp (continuous_snd.prodMk hu)
  refine hδ.of_le_mul (c := C) ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
    (g := fun (L : W →L[ℝ] W) v ↦ L v) hYu.aestronglyMeasurable hδ.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
  exact (Y (z.2, u z)).le_of_opNorm_le (hC z.2 hz.2 (u z)) (δ z)

/-- For a section vanishing for `|s| ≥ R`, a continuous function vanishing wherever the jet of the
section vanishes is integrable on the strip. -/
theorem integrable_of_jet_eq_zero {E : Type*} [NormedAddCommGroup E] {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {F : ℝ × ℝ → E} (hF : Continuous F)
    (h0 : ∀ z, jet ξ z = 0 → F z = 0) : Integrable F stripMeasure :=
  memLp_one_iff_integrable.1 <|
    memLp_stripMeasure_of_continuous hF (fun z hz ↦ h0 z (jet_eq_zero_of_lt_abs hR hz)) 1

/-- The jet of a `C¹` map vanishing for `|s|` large is in `Lᵖ` on the strip for every `p`. -/
theorem memLp_jet_of_contDiff (hξ : ContDiff ℝ 1 ξ) {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {p : ℝ≥0∞} : MemLp (jet ξ) p stripMeasure :=
  memLp_stripMeasure_of_continuous (continuous_jet hξ) (fun _ hz ↦ jet_eq_zero_of_lt_abs hR hz) p

/-- For a section vanishing for `s ∉ (a, b)`, the integral over the strip of a function vanishing
wherever the jet of the section vanishes is its integral over `[a, b] × [0, 1]`. -/
theorem integral_strip_eq_setIntegral_Icc_of_jet_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} (hvan : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) {F : ℝ × ℝ → E}
    (hF : ∀ z, jet ξ z = 0 → F z = 0) :
    ∫ z, F z ∂stripMeasure = ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, F z :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc)
    (prod_mono (subset_univ _) subset_rfl) fun z hz ↦
      hF z (jet_eq_zero_of_notMem_Icc hvan fun h ↦ hz.2 ⟨h, hz.1.2⟩)

/-- For a section vanishing for `|s| ≥ R`, the integral over the strip of a function vanishing
wherever the jet of the section vanishes is its integral over `[-R, R] × [0, 1]`. -/
theorem integral_strip_eq_setIntegral_of_jet_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {F : ℝ × ℝ → E}
    (hF : ∀ z, jet ξ z = 0 → F z = 0) :
    ∫ z, F z ∂stripMeasure = ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, F z :=
  integral_strip_eq_setIntegral_Icc_of_jet_eq_zero (eq_zero_of_notMem_Ioo_neg hR) hF

/-- Multiplying a `C¹` map by a `C¹` cutoff `χ` with `|χ| ≤ 1` and `‖Dχ‖ ≤ C`, whose topological
support lies in a measurable set `P`, gives a map whose derivative is bounded in `Lᵖ(ℝ × ℝ)` by
`C + 2` times the jet in `Lᵖ(P)`. -/
theorem eLpNorm_fderiv_smul_le {χ : ℝ × ℝ → ℝ} {C : ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχ1 : ∀ z, |χ z| ≤ 1) (hC : ∀ z, ‖fderiv ℝ χ z‖ ≤ C) {P : Set (ℝ × ℝ)}
    (hP : MeasurableSet P) (hχP : tsupport χ ⊆ P) (hξ : ContDiff ℝ 1 ξ) {p : ℝ≥0∞} :
    eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) p volume ≤
      ENNReal.ofReal (C + 2) * eLpNorm (jet ξ) p (volume.restrict P) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hpt : ∀ z, ‖fderiv ℝ (fun z ↦ χ z • ξ z) z‖ ≤ (C + 2) * ‖P.indicator (jet ξ) z‖ := by
    intro z
    by_cases hz : z ∈ P
    · rw [indicator_of_mem hz,
        fderiv_fun_smul (hχ.differentiable one_ne_zero z) (hξ.differentiable one_ne_zero z)]
      calc _ ≤ ‖χ z‖ * ‖fderiv ℝ ξ z‖ + ‖fderiv ℝ χ z‖ * ‖ξ z‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ 1 * (2 * ‖jet ξ z‖) + C * ‖jet ξ z‖ := by
            gcongr
            exacts [(Real.norm_eq_abs _).trans_le (hχ1 z), norm_fderiv_le_two_mul_norm_jet ξ z,
              hC z, norm_le_norm_jet ξ z]
        _ = (C + 2) * ‖jet ξ z‖ := by ring
    · have h0 : (fun z ↦ χ z • ξ z) =ᶠ[𝓝 z] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (hχP h)] with w hw
        simp [hw]
      rw [h0.fderiv_eq, indicator_of_notMem hz]
      simp
  calc eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) p volume
      ≤ ENNReal.ofReal (C + 2) * eLpNorm (P.indicator (jet ξ)) p volume :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          ((hχ.smul hξ).continuous_fderiv one_ne_zero).aestronglyMeasurable
          (Eventually.of_forall hpt) p
    _ = ENNReal.ofReal (C + 2) * eLpNorm (jet ξ) p (volume.restrict P) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hP.nullMeasurableSet]

/-! ### The restricted value -/

/-- The value of an `L²` jet on the strip, restricted to the compact piece `[-T, T] × [0, 1]`. -/
def restrictValue (T : ℝ) :
    Lp (V × V × V) 2 stripMeasure →L[ℝ]
      Lp V 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)) :=
  (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 (Icc (-T) T ×ˢ Icc 0 1)).comp
    ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure)

/-- The restricted value of an `L²` jet is represented by the first component of the jet. -/
theorem coeFn_restrictValue (T : ℝ) (f : Lp (V × V × V) 2 stripMeasure) :
    restrictValue T f =ᵐ[stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)] fun z ↦ (f z).1 :=
  (LpToLpRestrictCLM_coeFn ℝ _ _).trans
    (ae_restrict_of_ae ((ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL f))

/-! ### Multiplication by a function of `s` -/

section Cutoff

variable (V) in
/-- The map `(a, b, c) ↦ (0, a, 0)` on jets, moving the value into the `s`-derivative slot. -/
def sSlot : V × V × V →L[ℝ] V × V × V :=
  (ContinuousLinearMap.inr ℝ V (V × V)).comp
    ((ContinuousLinearMap.inl ℝ V V).comp (ContinuousLinearMap.fst ℝ V (V × V)))

/-- `sSlot V` moves the value of a jet into the `s`-derivative slot. -/
@[simp]
theorem sSlot_apply (v : V × V × V) : sSlot V v = (0, v.1, 0) := by
  simp [sSlot]

variable (V) in
/-- The coefficient field of multiplication by a function `β(s)` of the first variable, acting
on jets: `(ξ, ξ_s, ξ_t) ↦ (β ξ, β ξ_s + β' ξ, β ξ_t)`. On the jet of a section `ξ` it is the jet
of `β(s) ξ` (`TauCeti.StripSobolev.jet_smul_fst_eq_cutoffCoeff`). -/
def cutoffCoeff (β : ℝ → ℝ) (z : ℝ × ℝ) : V × V × V →L[ℝ] V × V × V :=
  β z.1 • ContinuousLinearMap.id ℝ (V × V × V) + deriv β z.1 • sSlot V

/-- Multiplication by `β(s)` is `β(s)` times the identity plus `β'(s)` times `sSlot V`. -/
theorem cutoffCoeff_def (β : ℝ → ℝ) (z : ℝ × ℝ) :
    cutoffCoeff V β z = β z.1 • ContinuousLinearMap.id ℝ (V × V × V) + deriv β z.1 • sSlot V :=
  (rfl)

/-- The components of `cutoffCoeff V β z v`. -/
@[simp]
theorem cutoffCoeff_apply (β : ℝ → ℝ) (z : ℝ × ℝ) (v : V × V × V) :
    cutoffCoeff V β z v = (β z.1 • v.1, β z.1 • v.2.1 + deriv β z.1 • v.1, β z.1 • v.2.2) := by
  obtain ⟨a, b, c⟩ := v
  simp [cutoffCoeff]

/-- Multiplication by `β(s)` followed by multiplication by `γ(s)` is multiplication by
`β(s) γ(s)`. -/
theorem cutoffCoeff_comp_cutoffCoeff {β γ : ℝ → ℝ} {z : ℝ × ℝ} (hβ : DifferentiableAt ℝ β z.1)
    (hγ : DifferentiableAt ℝ γ z.1) :
    (cutoffCoeff V β z).comp (cutoffCoeff V γ z) = cutoffCoeff V (β * γ) z := by
  have h : deriv (β * γ) z.1 = deriv β z.1 * γ z.1 + β z.1 * deriv γ z.1 :=
    (hβ.hasDerivAt.mul hγ.hasDerivAt).deriv
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, cutoffCoeff_apply, Pi.mul_apply, h, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> module

/-- Multiplication by `β(s)` plus multiplication by `γ(s)` is multiplication by `β(s) + γ(s)`. -/
theorem cutoffCoeff_add_cutoffCoeff {β γ : ℝ → ℝ} {z : ℝ × ℝ} (hβ : DifferentiableAt ℝ β z.1)
    (hγ : DifferentiableAt ℝ γ z.1) :
    cutoffCoeff V β z + cutoffCoeff V γ z = cutoffCoeff V (β + γ) z := by
  have h : deriv (β + γ) z.1 = deriv β z.1 + deriv γ z.1 :=
    (hβ.hasDerivAt.add hγ.hasDerivAt).deriv
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [add_apply, cutoffCoeff_apply, Pi.add_apply, h, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> module

/-- Multiplication by the constant function `1` is the identity. -/
@[simp]
theorem cutoffCoeff_one (z : ℝ × ℝ) :
    cutoffCoeff V 1 z = ContinuousLinearMap.id ℝ (V × V × V) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [cutoffCoeff, Pi.one_def]

/-- The jet of `β(s) ξ` is `cutoffCoeff V β` applied to the jet of `ξ`. -/
theorem jet_smul_fst_eq_cutoffCoeff {β : ℝ → ℝ} {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hβ : DifferentiableAt ℝ β z.1) (hξ : DifferentiableAt ℝ ξ z) :
    jet (fun w ↦ β w.1 • ξ w) z = cutoffCoeff V β z (jet ξ z) := by
  have hβ' : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv β z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    hβ.hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst
  have h : fderiv ℝ (fun w ↦ β w.1 • ξ w) z = β z.1 • fderiv ℝ ξ z +
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv β z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight (ξ z) :=
    (hβ'.smul hξ.hasFDerivAt).fderiv
  simp only [jet_apply, cutoffCoeff_apply, h]
  simp [add_comm]

/-- The coefficient of multiplication by `β(s)` has norm at most `|β(s)| + |β'(s)|`. -/
theorem norm_cutoffCoeff_le (β : ℝ → ℝ) (z : ℝ × ℝ) :
    ‖cutoffCoeff V β z‖ ≤ |β z.1| + |deriv β z.1| := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  · refine mul_le_of_le_one_right (abs_nonneg _) ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
    simp [Prod.norm_def]

/-- For a `C¹` function `β` with `β` and `β'` bounded, the coefficient field of multiplication by
`β(s)` is essentially bounded. -/
theorem memLp_cutoffCoeff {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β) {B : ℝ} (hβB : ∀ s, |β s| ≤ B)
    (hβ'B : ∀ s, |deriv β s| ≤ B) : MemLp (cutoffCoeff V β) ∞ stripMeasure := by
  have hc : Continuous (cutoffCoeff V β) :=
    ((hβ.continuous.comp continuous_fst).smul continuous_const).add
      (((hβ.continuous_deriv le_rfl).comp continuous_fst).smul continuous_const)
  exact memLp_top_of_bound hc.aestronglyMeasurable (B + B) (ae_of_all _ fun z ↦
    (norm_cutoffCoeff_le β z).trans (add_le_add (hβB _) (hβ'B _)))

end Cutoff

/-! ### Translation in the `s` direction -/

/-- Translation by `a` in the `s` direction preserves the strip measure. -/
theorem measurePreserving_add_strip (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ z + (a, 0)) stripMeasure stripMeasure := by
  -- `volume` on `ℝ × ℝ` is `volume.prod volume`, whose translation invariance is an instance.
  have h : MeasurePreserving (fun z : ℝ × ℝ ↦ z + (a, 0)) volume volume :=
    measurePreserving_add_right (volume.prod volume) (a, 0)
  replace h := h.restrict_preimage
    (MeasurableSet.univ.prod (measurableSet_Icc (a := (0 : ℝ)) (b := 1)))
  have hpre : (fun z : ℝ × ℝ ↦ z + (a, 0)) ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1) =
      univ ×ˢ Icc (0 : ℝ) 1 := by
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

/-- The jet of a compactly supported map has compact support: it vanishes off the support of the
map. -/
theorem hasCompactSupport_jet (hξ : HasCompactSupport ξ) : HasCompactSupport (jet ξ) := by
  refine hξ.mono' fun z hz ↦ ?_
  by_contra h
  exact hz (by simp [jet_apply, image_eq_zero_of_notMem_tsupport h,
    fderiv_of_notMem_tsupport ℝ h])

open scoped InnerProductSpace in
/-- For a locally integrable function `g`, a continuous coefficient field `M` and a compactly
supported `C¹` map `ξ`, the function `z ↦ ⟪g z, M z (jet ξ z)⟫` is integrable on the plane: it
vanishes off the support of `ξ`. -/
theorem integrable_inner_apply_jet {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hMc : Continuous M) {g : ℝ × ℝ → W}
    (hg : LocallyIntegrable g) (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) :
    Integrable fun z ↦ ⟪g z, M z (jet ξ z)⟫_ℝ := by
  set K := tsupport ξ
  have hK : IsCompact K := hξc
  have hMj : Continuous fun z ↦ M z (jet ξ z) := hMc.clm_apply (continuous_jet hξ)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hMj.continuousOn
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := K) ?_ fun z hz ↦ ?_
  · refine ((hg.integrableOn_isCompact hK).norm.const_mul C).mono'
      (hg.aestronglyMeasurable.restrict.inner hMj.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    rw [Real.norm_eq_abs, mul_comm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _))
  · have h0 : ξ =ᶠ[𝓝 z] fun _ ↦ 0 := notMem_tsupport_iff_eventuallyEq.1 hz
    simp [jet_apply, h0.fderiv_eq, h0.eq_of_nhds, Prod.mk_zero_zero]

/-- The jet of the translate of a map is the translate of its jet. -/
theorem jet_comp_add_right (ξ : ℝ × ℝ → V) (c : ℝ × ℝ) :
    jet (fun z ↦ ξ (z + c)) = fun z ↦ jet ξ (z + c) := by
  funext z
  simp [jet_apply, fderiv_comp_add_right]

/-- The squared norm of the jet is at most the pointwise `W^{1,2}` energy density. -/
theorem sq_norm_jet_le (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖jet ξ z‖ ^ 2 ≤ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  have h : ‖jet ξ z‖ ≤ √(‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) := by
    simp only [jet, Prod.norm_def, max_le_iff]
    refine ⟨?_, ?_, ?_⟩ <;> refine Real.le_sqrt_of_sq_le ?_ <;> nlinarith [sq_nonneg ‖ξ z‖,
      sq_nonneg ‖fderiv ℝ ξ z (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ z (0, 1)‖]
  calc ‖jet ξ z‖ ^ 2 ≤ (√(‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 +
        ‖ξ z‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt (by positivity)

/-- The pointwise `W^{1,2}` energy density `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` of a `C¹` map is
continuous. -/
theorem continuous_norm_partialDeriv_sq_add_norm_sq (hξ : ContDiff ℝ 1 ξ) :
    Continuous fun z ↦ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  have hd := hξ.continuous_fderiv one_ne_zero
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add (hξ.continuous.norm.pow 2)

/-- The pointwise `W^{1,2}` energy density `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` vanishes where the jet
does. -/
theorem norm_partialDeriv_sq_add_norm_sq_eq_zero_of_jet_eq_zero {z : ℝ × ℝ} (hz : jet ξ z = 0) :
    ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2 = 0 := by
  simp only [jet_apply, Prod.mk_eq_zero] at hz
  simp [hz]

omit [NormedSpace ℝ V] in
/-- The squared norm of a continuous section vanishing for `|s| ≥ R` is integrable on the
strip. -/
theorem integrable_norm_sq_of_continuous (hξ : Continuous ξ) {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) : Integrable (fun z ↦ ‖ξ z‖ ^ 2) stripMeasure :=
  (memLp_stripMeasure_of_continuous hξ (fun z hz ↦ hR z.1 z.2 hz.le) 2).integrable_norm_pow
    two_ne_zero

/-- The `Lᵖ` norm of a map is at most the `Lᵖ` norm of its jet. -/
theorem eLpNorm_le_eLpNorm_jet {μ : Measure (ℝ × ℝ)} (hξ : AEStronglyMeasurable ξ μ)
    (p : ℝ≥0∞) : eLpNorm ξ p μ ≤ eLpNorm (jet ξ) p μ :=
  eLpNorm_mono hξ (norm_le_norm_jet ξ)

/-- The `Lᵖ` norm of the `t`-derivative is at most the `Lᵖ` norm of the jet. -/
theorem eLpNorm_fderiv_zero_one_le_eLpNorm_jet {μ : Measure (ℝ × ℝ)}
    (hξ : AEStronglyMeasurable (fun z ↦ fderiv ℝ ξ z (0, 1)) μ) (p : ℝ≥0∞) :
    eLpNorm (fun z ↦ fderiv ℝ ξ z (0, 1)) p μ ≤ eLpNorm (jet ξ) p μ :=
  eLpNorm_mono hξ (norm_fderiv_zero_one_le_norm_jet ξ)

/-- The `Lᵖ` norm of the derivative is at most twice the `Lᵖ` norm of the jet. -/
theorem eLpNorm_fderiv_le_two_mul_eLpNorm_jet {μ : Measure (ℝ × ℝ)}
    (hξ : AEStronglyMeasurable (fderiv ℝ ξ) μ) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ ξ) p μ ≤ 2 * eLpNorm (jet ξ) p μ :=
  (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hξ
    (.of_forall (norm_fderiv_le_two_mul_norm_jet ξ)) p).trans_eq (by simp)

/-! ### The `Lᵖ` jets of a space of sections and their closure -/

/-- A space `S` of maps `ξ : ℝ × ℝ → V` whose elements are differentiable with jet in `Lᵖ` of the
strip. For `1 ≤ p < ∞` the closure of their `Lᵖ` jets (`TauCeti.StripSobolev.jetClosure`) is a
Sobolev space `W^{1,p}` of sections over the strip, such as the space
`TauCeti.CylinderSobolev.W1p` of the cylinder and, for `p = 2`, the space
`TauCeti.StripSobolev.H1` of the strip with boundary conditions. For `p = ∞` it is only the
closure of the jets of `S`, a proper subspace of `W^{1,∞}` in general. -/
class HasLpJets (p : ℝ≥0∞) (S : Submodule ℝ (ℝ × ℝ → V)) : Prop where
  /-- The elements of `S` are differentiable. -/
  differentiable : ∀ ξ ∈ S, Differentiable ℝ ξ
  /-- The elements of `S` have jet in `Lᵖ` of the strip. -/
  memLp_jet : ∀ ξ ∈ S, MemLp (jet ξ) p stripMeasure

section JetLp

variable (p : ℝ≥0∞) (S : Submodule ℝ (ℝ × ℝ → V)) [HasLpJets p S]

/-- The `Lᵖ` jet `(ξ, ∂s ξ, ∂t ξ)` of the elements of a space `S` of sections with jets in `Lᵖ`,
as a linear map into `Lᵖ(ℝ × [0, 1], V × V × V)`. -/
def jetLp : S →ₗ[ℝ] Lp (V × V × V) p stripMeasure where
  toFun ξ := (HasLpJets.memLp_jet _ ξ.property).toLp (jet (ξ : ℝ × ℝ → V))
  map_add' ξ η := by
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by
      rw [jet_add (HasLpJets.differentiable p _ ξ.property)
        (HasLpJets.differentiable p _ η.property)])
  map_smul' c ξ := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_smul])

variable {S}

/-- The `Lᵖ` jet of an element of `S` is represented by its jet. -/
theorem coeFn_jetLp (ξ : S) : jetLp p S ξ =ᵐ[stripMeasure] jet (ξ : ℝ × ℝ → V) :=
  MemLp.coeFn_toLp (HasLpJets.memLp_jet _ ξ.property)

/-- The `Lᵖ` jet of an element of `S` is the class of its jet. -/
theorem jetLp_apply (ξ : S) :
    jetLp p S ξ = (HasLpJets.memLp_jet _ ξ.property).toLp (jet (ξ : ℝ × ℝ → V)) :=
  (rfl)

/-- The norm of the `Lᵖ` jet of an element of `S` is the `Lᵖ` norm of its jet on the strip. -/
theorem norm_jetLp (ξ : S) :
    ‖jetLp p S ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) p stripMeasure).toReal := by
  rw [jetLp_apply, Lp.norm_toLp]

/-- The squared norm of the `L²` jet of an element of `S` is the integral of the squared norm of
its jet over the strip. -/
theorem sq_norm_jetLp [HasLpJets 2 S] (ξ : S) :
    ‖jetLp 2 S ξ‖ ^ 2 = ∫ z, ‖jet (ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure := by
  rw [jetLp_apply, MemLp.norm_toLp_sq]

/-- The squared norm of the `L²` jet of a `C¹` element of `S` is at most its `W^{1,2}` energy
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²)` over the strip. -/
theorem sq_norm_jetLp_le_integral [HasLpJets 2 S] (ξ : S) (hξ : ContDiff ℝ 1 (ξ : ℝ × ℝ → V)) :
    ‖jetLp 2 S ξ‖ ^ 2 ≤ ∫ z, (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 + ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) ∂stripMeasure := by
  have hjm := HasLpJets.memLp_jet (p := 2) _ ξ.property
  rw [sq_norm_jetLp]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ by positivity) ?_
    (Eventually.of_forall fun z ↦ sq_norm_jet_le _ z)
  refine ((hjm.integrable_norm_pow two_ne_zero).const_mul 3).mono' ?_
    (Eventually.of_forall fun z ↦ ?_)
  · exact (continuous_norm_partialDeriv_sq_add_norm_sq hξ).aestronglyMeasurable
  · have h₁ := norm_fderiv_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) z
    have h₂ := norm_fderiv_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) z
    have h₃ := norm_le_norm_jet (ξ : ℝ × ℝ → V) z
    rw [Real.norm_of_nonneg (by positivity)]
    linarith [pow_le_pow_left₀ (norm_nonneg _) h₁ 2, pow_le_pow_left₀ (norm_nonneg _) h₂ 2,
      pow_le_pow_left₀ (norm_nonneg _) h₃ 2]

/-- The squared norm of the restricted value of the jet of an element `ξ` of `S` is the integral
of `‖ξ‖²` over `[-T, T] × [0, 1]`. -/
theorem sq_norm_restrictValue_jetLp [HasLpJets 2 S] (T : ℝ) (ξ : S) :
    ‖restrictValue T (jetLp 2 S ξ)‖ ^ 2 =
      ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 := by
  -- On subsets of the strip, the strip measure is Lebesgue measure.
  have hμ : stripMeasure.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) =
      volume.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc),
      inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]
  rw [← Lp.integral_norm_sq_eq_norm_sq, ← hμ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictValue T (jetLp 2 S ξ), ae_restrict_of_ae (coeFn_jetLp 2 ξ)]
    with z h₁ h₂
  rw [h₁, h₂, jet_apply]

variable [Fact (1 ≤ p)]

variable (S) in
/-- The closure in `Lᵖ(ℝ × [0, 1], V × V × V)` of the jets of the elements of `S`, that is, the
completion of `S` in the `W^{1,p}` norm. -/
def jetClosure : Submodule ℝ (Lp (V × V × V) p stripMeasure) :=
  (LinearMap.range (jetLp p S)).topologicalClosure

variable (S) in
/-- The definition of `jetClosure`: the closure of the span of the jets of the elements of `S`. -/
theorem jetClosure_def : jetClosure p S = (LinearMap.range (jetLp p S)).topologicalClosure :=
  (rfl)

variable (S) in
/-- `jetClosure p S` is the closure of the set of jets of the elements of `S`. -/
theorem coe_jetClosure :
    (jetClosure p S : Set (Lp (V × V × V) p stripMeasure)) = closure (Set.range (jetLp p S)) := by
  rw [jetClosure_def, Submodule.topologicalClosure_coe, LinearMap.coe_range]

variable (S) in
/-- `jetClosure p S` is a closed subspace of `Lᵖ`. -/
theorem isClosed_jetClosure :
    IsClosed (jetClosure p S : Set (Lp (V × V × V) p stripMeasure)) :=
  Submodule.isClosed_topologicalClosure _

variable (S) in
/-- `jetClosure p S` is complete: it is a closed subspace of the complete space `Lᵖ`. -/
instance [CompleteSpace V] : CompleteSpace (jetClosure p S) :=
  Submodule.topologicalClosure.completeSpace _

variable {p}

/-- A closed set containing the jets of all elements of `S` contains `jetClosure p S`. -/
theorem jetClosure_subset_of_isClosed {s : Set (Lp (V × V × V) p stripMeasure)}
    (hs : IsClosed s) (h : Set.range (jetLp p S) ⊆ s) :
    (jetClosure p S : Set (Lp (V × V × V) p stripMeasure)) ⊆ s := by
  rw [coe_jetClosure]
  exact closure_minimal h hs

/-- The jet of an element of `S` lies in `jetClosure p S`. -/
theorem jetLp_mem_jetClosure (ξ : S) : jetLp p S ξ ∈ jetClosure p S :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ ξ)

variable (p S) in
/-- The jet of an element of `S`, as an element of `jetClosure p S`. -/
def toJetClosure : S →ₗ[ℝ] jetClosure p S :=
  (jetLp p S).codRestrict (jetClosure p S) jetLp_mem_jetClosure

/-- The jet of an element of `S` in `jetClosure p S` is its `Lᵖ` jet. -/
@[simp]
theorem coe_toJetClosure (ξ : S) :
    (toJetClosure p S ξ : Lp (V × V × V) p stripMeasure) = jetLp p S ξ :=
  (rfl)

/-- The jet of an element of `S` in `jetClosure p S` is its `Lᵖ` jet, with the proof that it lies
in `jetClosure p S`. -/
theorem toJetClosure_apply (ξ : S) :
    toJetClosure p S ξ = ⟨jetLp p S ξ, jetLp_mem_jetClosure ξ⟩ :=
  (rfl)

/-- The norm of the jet of an element of `S` in `jetClosure p S` is the `Lᵖ` norm of its jet on
the strip. -/
theorem norm_toJetClosure (ξ : S) :
    ‖toJetClosure p S ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) p stripMeasure).toReal := by
  rw [← Submodule.norm_coe, coe_toJetClosure, norm_jetLp]

variable (p S) in
/-- The jets of the elements of `S` are dense in `jetClosure p S`. -/
theorem denseRange_toJetClosure : DenseRange (toJetClosure p S) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact (coe_jetClosure p S).subset

/-- A closed subset of `jetClosure p S` containing the jets of all elements of `S` is
everything. -/
@[elab_as_elim]
theorem jetClosure_induction {P : jetClosure p S → Prop} (hP : IsClosed {x | P x})
    (h : ∀ ξ : S, P (toJetClosure p S ξ)) (x : jetClosure p S) : P x :=
  (denseRange_toJetClosure p S).induction_on x hP h

/-- A closed relation on `jetClosure p S` holding for the jets of all pairs of elements of `S`
holds for all pairs. -/
theorem jetClosure_induction₂ {P : jetClosure p S → jetClosure p S → Prop}
    (hP : IsClosed {x : jetClosure p S × jetClosure p S | P x.1 x.2})
    (h : ∀ ξ η : S, P (toJetClosure p S ξ) (toJetClosure p S η)) (x y : jetClosure p S) :
    P x y :=
  (denseRange_toJetClosure p S).induction_on₂ hP h x y

end JetLp

/-! ### Spaces of sections invariant under translation -/

/-- A space `S` of maps `ξ : ℝ × ℝ → V` that is invariant under translation in the `s` direction,
`ξ ↦ ξ (· + a, ·)`. Translation then acts on `jetClosure p S` as a linear isometric equivalence
(`TauCeti.StripSobolev.translate`). -/
class IsTranslationInvariant (S : Submodule ℝ (ℝ × ℝ → V)) : Prop where
  /-- The translate `ξ (· + a, ·)` of an element of `S` lies in `S`. -/
  comp_add_right_mem : ∀ ξ ∈ S, ∀ a : ℝ, (fun z ↦ ξ (z + (a, 0))) ∈ S

section Translate

variable {p : ℝ≥0∞} {S : Submodule ℝ (ℝ × ℝ → V)} [HasLpJets p S] [IsTranslationInvariant S]

variable (p) in
/-- The translate of the `Lᵖ` jet of an element of `S` is the `Lᵖ` jet of its translate. -/
theorem translateLp_jetLp [Fact (1 ≤ p)] (a : ℝ) (ξ : S) :
    translateLp a (jetLp p S ξ) =
      jetLp p S ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.property a⟩ := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_translateLp a (jetLp p S ξ),
    (measurePreserving_add_strip a).quasiMeasurePreserving.ae_eq_comp (coeFn_jetLp p ξ),
    coeFn_jetLp p ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.property a⟩] with z h₁ h₂ h₃
  rw [h₁, h₃, jet_comp_add_right]
  exact h₂

variable [Fact (1 ≤ p)]

/-- Translation maps `jetClosure p S` into itself. -/
theorem translateLp_mem_jetClosure (a : ℝ) {f : Lp (V × V × V) p stripMeasure}
    (hf : f ∈ jetClosure p S) : translateLp a f ∈ jetClosure p S := by
  have h : (jetClosure p S : Set (Lp (V × V × V) p stripMeasure)) ⊆
      translateLp a ⁻¹' jetClosure p S :=
    jetClosure_subset_of_isClosed
      ((isClosed_jetClosure p S).preimage (translateLp a).continuous) <| by
      rintro _ ⟨ξ, rfl⟩
      rw [mem_preimage, translateLp_jetLp]
      exact jetLp_mem_jetClosure _
  exact h hf

/-- An `Lᵖ` jet lies in `jetClosure p S` exactly when its translate does: translation maps
`jetClosure p S` onto itself. -/
@[simp]
theorem translateLp_mem_jetClosure_iff (a : ℝ) {f : Lp (V × V × V) p stripMeasure} :
    translateLp a f ∈ jetClosure p S ↔ f ∈ jetClosure p S := by
  refine ⟨fun h ↦ ?_, translateLp_mem_jetClosure a⟩
  simpa using translateLp_mem_jetClosure (-a) h

variable (p S) in
/-- Translation by `a` in the `s` direction, `x ↦ x (· + a, ·)`, as a linear isometric
equivalence of `jetClosure p S`. Its inverse is translation by `-a`
(`TauCeti.StripSobolev.translate_symm`). -/
def translate (a : ℝ) : jetClosure p S ≃ₗᵢ[ℝ] jetClosure p S :=
  ((translateLp a).submoduleMap (jetClosure p S)).trans <|
    LinearIsometryEquiv.ofEq _ _ <| le_antisymm
      (Submodule.map_le_iff_le_comap.2 fun _ ↦ translateLp_mem_jetClosure a)
      fun f hf ↦ ⟨_, translateLp_mem_jetClosure (-a) hf, by simp⟩

/-- Translation on `jetClosure p S` is translation of `Lᵖ` jets. -/
@[simp]
theorem coe_translate (a : ℝ) (x : jetClosure p S) :
    (translate p S a x : Lp (V × V × V) p stripMeasure) = translateLp a x :=
  (rfl)

/-- Translation of the jet of an element of `S` is the jet of its translate. -/
@[simp]
theorem translate_toJetClosure (a : ℝ) (ξ : S) :
    translate p S a (toJetClosure p S ξ) =
      toJetClosure p S ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.property a⟩ :=
  Subtype.ext <| by rw [coe_translate, coe_toJetClosure, coe_toJetClosure, translateLp_jetLp]

/-- The inverse of translation by `a` on `jetClosure p S` is translation by `-a`. -/
@[simp]
theorem translate_symm (a : ℝ) : (translate p S a).symm = translate p S (-a) :=
  LinearIsometryEquiv.ext fun x ↦ (translate p S a).symm_apply_eq.2 <| Subtype.ext <| by simp

variable (p) in
/-- **The `W^{1,p}` norm is translation invariant**: an element of `S` and its translate in the
`s` direction have `Lᵖ` jets of the same norm. -/
theorem norm_jetLp_comp_add_right (a : ℝ) (ξ : S) :
    ‖jetLp p S ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.property a⟩‖ =
      ‖jetLp p S ξ‖ := by
  rw [← translateLp_jetLp, LinearIsometryEquiv.norm_map]

end Translate

end TauCeti.StripSobolev
