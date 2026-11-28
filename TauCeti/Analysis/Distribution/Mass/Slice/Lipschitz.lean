/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Slice.Basic
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Normed.Module.Alternating.SecondCountable
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Slicing of currents by Lipschitz and locally Lipschitz functions

This file extends slicing of locally normal currents from smooth functions to Lipschitz and locally
Lipschitz functions, following Federer, *Geometric Measure Theory*, §§4.3.1–4.3.2, and Simon,
*Introduction to Geometric Measure Theory*, Chapter 6, §5.

When `E` is finite-dimensional and `u : E → ℝ` is `K`-Lipschitz on `Ω`, McShane extension
(`LipschitzOnWith.extend_real`), bump-convolution smoothing
(`LipschitzWith.exists_contDiff_lipschitzWith_dist_lt`), and an upward shift yield smooth
`K`-Lipschitz `g_j` with `u < g_j` on `Ω` converging uniformly to `u`. Hence
`1_{g_j < t} → 1_{u < t}` everywhere on `Ω` for every `t`, so `⟨T, g_j, t⟩ → ⟨T, u, t⟩` weakly.
By contrast, the slicing inequalities, normality, local normality, and measurability results below
hold without assuming finite-dimensionality, since in infinite dimensions every test form and
slice is zero.

## Main declarations

* `Distribution.exists_contDiff_lipschitzWith_slice_tendsto`: on a finite-dimensional space `E`,
  shifted smooth `K`-Lipschitz approximants `g_j` whose slices converge pointwise on test forms
  at every level `t ∈ ℝ`.
* `Distribution.measurable_uncurry_slice_apply_of_lipschitzOnWith`: joint pairing measurability for
  weakly measurable families of locally normal currents sliced by a Lipschitz function on `Ω`.
* `Distribution.slice_eq_zero_of_lipschitzOnWith_zero`: a slice by a `0`-Lipschitz function on `Ω`
  is zero.
* `Distribution.lintegral_mass_slice_le_of_lipschitzOnWith`,
  `Distribution.lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace`: the slicing
  inequality for `K`-Lipschitz functions on `Ω` (sharp constant `K` on inner product spaces).
* `Distribution.setLIntegral_mass_slice_le_of_lipschitzOnWith`,
  `Distribution.setLIntegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace`: localization
  to a strip `{a < u < b}`.
* `Distribution.lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith`,
  `Distribution.lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_of_innerProductSpace`:
  weighted mass-measure slicing inequalities for nonnegative Borel weights.
* `Distribution.ae_isNormal_slice_of_lipschitzOnWith`,
  `Distribution.ae_isNormal_massRestrict_lt_of_lipschitzOnWith`: for normal `T` and `u` Lipschitz
  on `Ω`, `⟨T, u, t⟩` and `T ⌞ {u < t}` are normal for Lebesgue-a.e. `t`.
* `Distribution.ae_isLocallyNormal_slice_of_locallyLipschitzOn`,
  `Distribution.ae_isLocallyNormal_massRestrict_lt_of_locallyLipschitzOn`,
  `Distribution.aemeasurable_lintegral_massMeasure_slice_of_locallyLipschitzOn`: for locally
  normal `T` and `u` locally Lipschitz on `Ω`, `⟨T, u, t⟩` and `T ⌞ {u < t}` are locally normal
  for Lebesgue-a.e. `t`, and weighted mass integrals `t ↦ ∫⁻ x, w x ∂‖⟨T, u, t⟩‖` are a.e.
  measurable when `F` is second countable.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {K : ℝ≥0} {u : E → ℝ}

/-! ### Smooth Lipschitz approximation of slices -/

/-- **Shifted smooth Lipschitz approximation for slices.** On a finite-dimensional space `E`,
for `u` that is `K`-Lipschitz on `Ω`, there exists a sequence of globally smooth `K`-Lipschitz
functions `g_j : E → ℝ` converging to `u` on `Ω` from strictly above (`u x < g_j x` on `Ω`)
such that `⟨T, g_j, t⟩ φ → ⟨T, u, t⟩ φ` as `j → ∞` for every current `T` on `Ω`, every `t ∈ ℝ`,
and every test form `φ`. -/
theorem exists_contDiff_lipschitzWith_slice_tendsto [FiniteDimensional ℝ E]
    (hu : LipschitzOnWith K u Ω) :
    ∃ g : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (g j)) ∧
      (∀ j, LipschitzWith K (g j)) ∧
      (∀ (x : Ω) (j : ℕ), u x < g j x) ∧
      (∀ x : Ω, Tendsto (fun j => g j x) atTop (𝓝 (u x))) ∧
      ∀ {m : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
        (T : 𝓓(Ω, E [⋀^Fin (m + 1)]→L[ℝ] G) →L[ℝ] ℝ) (t : ℝ)
        (φ : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] G)),
        Tendsto (fun j => slice T (g j) t φ) atTop (𝓝 (slice T u t φ)) := by
  obtain ⟨u_ext, hu_lip, hu_eq⟩ := hu.extend_real
  choose w hw_smooth hw_lip hw_dist using fun j : ℕ =>
    hu_lip.exists_contDiff_lipschitzWith_dist_lt (ε := ((j : ℝ) + 1)⁻¹ / 4) (by positivity)
  let g : ℕ → E → ℝ := fun j x => w j x + ((j : ℝ) + 1)⁻¹ / 2
  have hg_smooth (j : ℕ) : ContDiff ℝ ∞ (g j) := (hw_smooth j).add contDiff_const
  have hg_lip (j : ℕ) : LipschitzWith K (g j) := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [g, add_sub_add_right_eq_sub] using (hw_lip j).dist_le_mul x y
  have hg_bounds (x : Ω) (j : ℕ) : u x < g j x ∧ g j x - u x < ((j : ℝ) + 1)⁻¹ := by
    obtain ⟨hd1, hd2⟩ := abs_lt.1 <| show |w j x - u x| < ((j : ℝ) + 1)⁻¹ / 4 by
      simpa [Real.dist_eq, hu_eq x.property] using hw_dist j x
    exact ⟨by dsimp [g]; linarith, by dsimp [g]; linarith⟩
  have hg_lim (x : Ω) : Tendsto (fun j => g j x) atTop (𝓝 (u x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))))
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 (hg_bounds x j).1)]
    exact (hg_bounds x j).2.le
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  have hg_meas (j : ℕ) : Measurable fun x : Ω => g j x :=
    ((hg_smooth j).continuous.comp continuous_subtypeVal).measurable
  refine ⟨g, hg_smooth, hg_lip, fun x j => (hg_bounds x j).1, hg_lim, fun T t φ => ?_⟩
  have hiff (x : Ω) : ∀ᶠ j in atTop, g j x < t ↔ u x < t := by
    by_cases hx : u x < t
    · exact ((tendsto_order.1 (hg_lim x)).2 t hx).mono fun j hj => iff_of_true hj hx
    · exact .of_forall fun j => iff_of_false (fun hj => hx ((hg_bounds x j).1.trans hj)) hx
  exact tendsto_slice_apply_of_eventually_iff T hg_meas hu_meas (ae_of_all _ hiff)
    (ae_of_all _ hiff) φ

/-- For a weakly measurable family of locally normal `(k + 1)`-currents
`T : α → 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ` and a function `u : E → ℝ` Lipschitz on `Ω`,
the joint pairing `(a, t) ↦ ⟨T a, u, t⟩ φ` is measurable on `α × ℝ`. -/
theorem measurable_uncurry_slice_apply_of_lipschitzOnWith {α : Type*} [MeasurableSpace α]
    {T : α → 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hTm : ∀ ψ, Measurable fun a => T a ψ) (hTn : ∀ a, IsLocallyNormal (T a))
    (hu : LipschitzOnWith K u Ω) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Measurable fun p : α × ℝ => slice (T p.1) u p.2 φ := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · simp_rw [show ∀ p : α × ℝ, slice (T p.1) u p.2 φ = 0 from fun p => by
      rw [slice_eq_zero_of_not_finiteDimensional (T := T p.1) hE]; rfl]
    exact measurable_const
  obtain ⟨g, hg_smooth, -, -, -, hg_slice⟩ := exists_contDiff_lipschitzWith_slice_tendsto hu
  exact measurable_of_tendsto_metrizable
    (fun j => measurable_uncurry_slice_apply_of_contDiff hTm hTn (hg_smooth j) φ)
    (tendsto_pi_nhds.2 fun ⟨a, t⟩ => hg_slice (T a) t φ)

/-! ### The slicing inequality for Lipschitz functions -/

private theorem exists_measurable_mass_slice_le_of_lipschitzOnWith_aux
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) (c : ℝ≥0∞)
    (hsmooth : ∀ g : E → ℝ, ContDiff ℝ ∞ g → ∃ m : ℝ → ℝ≥0∞, Measurable m ∧
      (∀ t, mass (slice T g t) ≤ m t) ∧
      ∫⁻ t, m t ≤ c * ∫⁻ x : Ω, ‖fderiv ℝ g x‖ₑ ∂massMeasure T) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice T u t) ≤ m t) ∧
      ∫⁻ t, m t ≤ c * (K : ℝ≥0∞) * mass T := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · refine ⟨0, measurable_const, fun t => ?_, by simp⟩
    simp [slice_eq_zero_of_not_finiteDimensional (T := T) hE]
  obtain ⟨g, hg_smooth, hg_lip, -, -, hg_slice⟩ := exists_contDiff_lipschitzWith_slice_tendsto hu
  choose mj hmj_meas hmj_le hmj_int using fun j => hsmooth (g j) (hg_smooth j)
  refine ⟨fun t => liminf (fun j => mj j t) atTop, Measurable.liminf hmj_meas,
    fun t => (mass_le_liminf (hg_slice T t)).trans
      (liminf_le_liminf (.of_forall fun j => hmj_le j t)),
    (lintegral_liminf_le hmj_meas).trans <| liminf_le_of_frequently_le' <| .of_forall fun j =>
      (hmj_int j).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_right (lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass
    fun x => (hg_lip j).eNorm_fderiv_le ℝ) c

/-- **Measurable majorant for the mass of Lipschitz slices** on a general normed space:
if `T` is locally normal on `Ω` and `u` is `K`-Lipschitz on `Ω`, there exists a Borel
measurable `m : ℝ → ℝ≥0∞` dominating `t ↦ mass ⟨T, u, t⟩` with
`∫⁻ t, m t ≤ (k + 1) * K * mass T`. -/
theorem exists_measurable_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice T u t) ≤ m t) ∧
      ∫⁻ t, m t ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * mass T :=
  exists_measurable_mass_slice_le_of_lipschitzOnWith_aux hT hu (k + 1) fun _ hg =>
    exists_measurable_mass_slice_le hT hg

/-- **The Lipschitz slicing inequality** on a general normed space:
`∫⁻ t, mass ⟨T, u, t⟩ ≤ (k + 1) * K * mass T`. -/
theorem lintegral_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t, mass (slice T u t) ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * mass T := by
  obtain ⟨_, -, hm_le, hm_int⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hT hu
  exact (lintegral_mono hm_le).trans hm_int

/-- **Local Lipschitz slicing inequality** on an open subset `U ≤ Ω` of a normed space: for a
locally normal `(k + 1)`-current `T` on `Ω` and `u : E → ℝ` that is `K`-Lipschitz on `U` and
measurable on `Ω`, `∫⁻ t, localMass ⟨T, u, t⟩ U ≤ (k + 1) * K * localMass T U`. -/
theorem lintegral_localMass_slice_le_of_lipschitzOnWith {U : Opens E} (hU : U ≤ Ω)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u U) (huΩ : Measurable fun x : Ω => u x) :
    ∫⁻ t, localMass (slice T u t) U ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * localMass T U := by
  simp_rw [← mass_comp_monoCLM hU (f := T)]
  simpa only [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU huΩ] using
    lintegral_mass_slice_le_of_lipschitzOnWith hT.comp_monoCLM hu

private theorem setLIntegral_mass_slice_le_of_lipschitzOnWith_aux
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hu : LipschitzOnWith K u Ω) (a b : ℝ) (c : ℝ≥0∞)
    (hsmooth : ∀ g : E → ℝ, ContDiff ℝ ∞ g → ∃ m : ℝ → ℝ≥0∞, Measurable m ∧
      (∀ t, mass (slice T g t) ≤ m t) ∧
      ∫⁻ t, m t ≤ c * ∫⁻ x : Ω, ‖fderiv ℝ g x‖ₑ ∂massMeasure T) :
    ∫⁻ t in Ioo a b, mass (slice T u t) ≤ c * (K : ℝ≥0∞) * massMeasure T {x | u x ∈ Ioo a b} := by
  by_cases hE : FiniteDimensional ℝ E
  swap; · simp [slice_eq_zero_of_not_finiteDimensional (T := T) hE]
  by_cases hab : a < b
  swap; · simp [Ioo_eq_empty hab]
  obtain ⟨w, hw, huw⟩ := hu.extend_real
  choose v hv hvL hvd hv0 using fun j : ℕ =>
    hw.exists_contDiff_lipschitzWith_dist_max_min_lt_fderiv_eq_zero a b
      (mul_pos (sub_pos.2 hab) (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)))
  let w' : E → ℝ := fun x => max a (min (w x) b)
  have hw'_meas : Measurable fun x : Ω => w' x :=
    ((continuous_const.max (hw.continuous.min continuous_const)).comp
      continuous_subtypeVal).measurable
  have hlim : ∀ x ∈ Ω, Tendsto (fun j => v j x) atTop (𝓝 (w' x)) := fun x _ => by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hvd j x).le) <| by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
  choose mj hmj_meas hmj_le hmj_int using fun j => hsmooth (v j) (hv j)
  have hcount := (Measure.countable_meas_level_set_pos (μ := massMeasure T) hw'_meas).union
    (Measure.countable_meas_level_set_pos (μ := massMeasure (T ∘L extDerivCLM)) hw'_meas)
  have hae : ∀ᵐ t, mass (slice T w' t) ≤ liminf (fun j => mj j t) atTop := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hcount.measure_zero volume)] with t ht
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, nonpos_iff_eq_zero] at ht
    exact (mass_le_liminf (tendsto_slice_apply T
        (fun j => ((hv j).continuous.comp continuous_subtypeVal).measurable) hw'_meas hlim
        ht.1 ht.2)).trans (liminf_le_liminf (.of_forall fun j => hmj_le j t))
  have hGint : ∫⁻ t, liminf (fun j => mj j t) atTop ≤
      c * (K : ℝ≥0∞) * massMeasure T {x | u x ∈ Ioo a b} := by
    refine (lintegral_liminf_le hmj_meas).trans
      (liminf_le_of_frequently_le' (.of_forall fun j => (hmj_int j).trans ?_))
    rw [mul_assoc]
    gcongr
    have hset : {x : Ω | w x ∈ Ioo a b} = {x : Ω | u x ∈ Ioo a b} := by
      ext x; simp [huw x.property]
    rw [← hset]
    refine (lintegral_mono fun x => ?_).trans (lintegral_indicator_const_le _ _)
    by_cases hx : (x : Ω) ∈ {x : Ω | w x ∈ Ioo a b}
    · rw [indicator_of_mem hx]; exact (hvL j).eNorm_fderiv_le ℝ
    · rw [indicator_of_notMem hx, hv0 j x hx, ← ofReal_norm]; simp
  refine (setLIntegral_mono_ae (Measurable.liminf hmj_meas).aemeasurable
    (hae.mono fun t ht hts => ?_)).trans ((setLIntegral_le_lintegral _ _).trans hGint)
  have htrunc : slice T w t = slice T w' t := slice_congr T
    (hw.continuous.comp continuous_subtypeVal).measurable hw'_meas (ext fun x => by
      simp only [w', mem_ofPred_eq, max_lt_iff, min_lt_iff, hts.1, true_and]
      exact ⟨Or.inl, fun h => h.resolve_right hts.2.not_gt⟩)
  simpa [slice_congr_of_eqOn T huw, htrunc] using ht

/-- **The Lipschitz slicing inequality on a strip** on a general normed space:
`∫⁻ t in Ioo a b, mass ⟨T, u, t⟩ ≤ (k + 1) * K * ‖T‖ {a < u < b}`. -/
theorem setLIntegral_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) (a b : ℝ) :
    ∫⁻ t in Ioo a b, mass (slice T u t) ≤
      (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * massMeasure T {x | u x ∈ Ioo a b} :=
  setLIntegral_mass_slice_le_of_lipschitzOnWith_aux hu a b (k + 1) fun _ hg =>
    exists_measurable_mass_slice_le hT hg

/-! ### Almost-everywhere normality and local normality of slices -/

/-- For a locally normal current `T` of finite mass and `u` Lipschitz on `Ω`,
`mass ⟨T, u, t⟩ < ⊤` for Lebesgue-a.e. `t ∈ ℝ`. -/
theorem ae_mass_slice_lt_top_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hmass : mass T ≠ ⊤) (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ, mass (slice T u t) < ⊤ := by
  obtain ⟨m, hm_meas, hm_le, hm_int⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hT hu
  filter_upwards [ae_lt_top hm_meas (ne_top_of_le_ne_top (by finiteness) hm_int)] with t ht
  exact (hm_le t).trans_lt ht

/-- **Slices of a normal current by a Lipschitz function are normal almost everywhere.** -/
theorem ae_isNormal_slice_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ, IsNormal (slice T u t) :=
  ae_isNormal_slice_of_ae_mass_lt_top hT fun _ hS =>
    ae_mass_slice_lt_top_of_lipschitzOnWith hS.isLocallyNormal hS.mass_ne_top hu

/-- **Sublevel restrictions `T ⌞ {u < t}` of a normal current by a Lipschitz function on `Ω` are
normal almost everywhere.** -/
theorem ae_isNormal_massRestrict_lt_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ,
      IsNormal (massRestrict T (measurableSet_lt hu.continuousOn.domRestrict.measurable
        (measurable_const (a := t)))) := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  obtain ⟨hT1, hT2⟩ := isNormal_succ_iff.1 hT
  filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT1 hu] with t ht
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hu_meas (measurable_const (a := t))
  rw [massRestrict_congr_set (T := T) _ hA (by ext x; rfl)]
  refine isNormal_succ_iff.2 ⟨mass_massRestrict_ne_top hT1 hA, ?_⟩
  rw [massRestrict_lt_comp_extDerivCLM T hu_meas t, FunLike.coe_add]
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨ht.ne, mass_massRestrict_ne_top hT2 hA⟩) mass_add_le

/-- For a locally normal current `T` and `u` locally Lipschitz on `Ω`, the slice `⟨T, u, t⟩` has
locally finite mass for Lebesgue-a.e. `t ∈ ℝ`. -/
theorem ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ, HasLocallyFiniteMass (slice T u t) := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · exact .of_forall fun t => by
      rw [slice_eq_zero_of_not_finiteDimensional (T := T) hE]; exact hasLocallyFiniteMass_zero
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  let Kex := CompactExhaustion.choice Ω
  let C (n : ℕ) : Set E := (↑) '' Kex (n + 1)
  have hC_cpt (n : ℕ) : IsCompact (C n) := (Kex.isCompact (n + 1)).image continuous_subtypeVal
  have hC_sub (n : ℕ) : C n ⊆ Ω := Subtype.coe_image_subset _ _
  let W (n : ℕ) : Opens E :=
    ⟨(↑) '' interior (Kex (n + 1)), Ω.isOpen.isOpenMap_subtypeVal _ isOpen_interior⟩
  have hW_sub_C (n : ℕ) : (W n : Set E) ⊆ C n := image_mono interior_subset
  have hW_le (n : ℕ) : W n ≤ Ω := (hW_sub_C n).trans (hC_sub n)
  choose L hL using fun n => (hu.mono (hC_sub n)).exists_lipschitzOnWith_of_compact (hC_cpt n)
  filter_upwards [ae_all_iff.2 fun n => ae_mass_slice_lt_top_of_lipschitzOnWith hT.comp_monoCLM
    (by rw [coe_comp, mass_comp_monoCLM (hW_le n)]
        exact ne_top_of_le_ne_top ((hasLocallyFiniteMass_iff_localMass_ne_top T).1
          hT.hasLocallyFiniteMass (C n) (hC_cpt n) (hC_sub n)) (localMass_mono (hW_sub_C n)))
    ((hL n).mono (hW_sub_C n))] with t ht
  refine (hasLocallyFiniteMass_iff_localMass_ne_top _).2 fun K₀ hK₀ hK₀Ω => ?_
  obtain ⟨n, hn⟩ := Kex.exists_superset_of_isCompact
    (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK₀
      (by rwa [Subtype.range_coe]))
  refine ne_top_of_le_ne_top ?_ (localMass_mono (U' := (W n : Set E)) fun x hx =>
    ⟨⟨x, hK₀Ω hx⟩, Kex.subset_interior_succ n (hn hx), rfl⟩)
  rw [← mass_comp_monoCLM (hW_le n), ← coe_comp, slice_comp_monoCLM hT (hW_le n) hu_meas t]
  exact (ht n).ne

/-- **Slices of a locally normal current by a locally Lipschitz function are locally normal
almost everywhere.** -/
theorem ae_isLocallyNormal_slice_of_locallyLipschitzOn
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ, IsLocallyNormal (slice T u t) := by
  cases k with
  | zero => simpa only [isLocallyNormal_finZero_iff] using
    ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu
  | succ k =>
    filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu,
      ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT.comp_extDerivCLM hu] with t ht1 ht2
    rw [isLocallyNormal_succ_iff, slice_comp_extDerivCLM T u t]
    exact ⟨ht1, ht2.neg⟩

/-- **Sublevel restrictions `T ⌞ {u < t}` of a locally normal current by a locally Lipschitz
function on `Ω` are locally normal almost everywhere.** -/
theorem ae_isLocallyNormal_massRestrict_lt_of_locallyLipschitzOn
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ,
      IsLocallyNormal (massRestrict T (measurableSet_lt hu.continuousOn.domRestrict.measurable
        (measurable_const (a := t)))) := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu] with t ht
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hu_meas (measurable_const (a := t))
  rw [massRestrict_congr_set (T := T) _ hA (by ext x; rfl)]
  refine isLocallyNormal_succ_iff.2 ⟨hasLocallyFiniteMass_massRestrict hA, ?_⟩
  rw [massRestrict_lt_comp_extDerivCLM T hu_meas t, FunLike.coe_add]
  exact ht.add (hasLocallyFiniteMass_massRestrict hA)

/-- **A slice by a `0`-Lipschitz function on `Ω` is zero** for any locally normal current. -/
theorem slice_eq_zero_of_lipschitzOnWith_zero
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith 0 u Ω) (t : ℝ) :
    slice T u t = 0 := by
  by_cases hΩ : Nonempty Ω
  · obtain ⟨x₀⟩ := hΩ
    rw [slice_congr_of_eqOn T (fun x hx => by
      simpa using hu.dist_le_mul x hx (x₀ : E) x₀.property), slice_const hT]
  · rw [not_nonempty_iff] at hΩ
    rw [slice_congr_of_eqOn T (v := fun _ => (0 : ℝ)) (fun x hx => (hΩ.false ⟨x, hx⟩).elim),
      slice_const hT]

/-- For a locally normal `(k + 1)`-current `T`, `u` locally Lipschitz on `Ω`, a second-countable
codomain `F`, and a Borel measurable weight `w : Ω → ℝ≥0∞`,
`t ↦ ∫⁻ x, w x ∂‖⟨T, u, t⟩‖` is Lebesgue-a.e. measurable. -/
theorem aemeasurable_lintegral_massMeasure_slice_of_locallyLipschitzOn
    [SecondCountableTopology F] {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : LocallyLipschitzOn Ω u) {w : Ω → ℝ≥0∞} (hw : Measurable w) :
    AEMeasurable (fun t : ℝ => ∫⁻ x : Ω, w x ∂massMeasure (slice T u t)) := by
  by_cases hE : FiniteDimensional ℝ E
  · exact aemeasurable_lintegral_massMeasure (measurable_slice_apply T u)
      (ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu) hw
  · simp [slice_eq_zero_of_not_finiteDimensional (T := T) hE, aemeasurable_const]

private theorem lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_aux
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) {c₀ : ℝ≥0∞} (hc₀top : c₀ ≠ ⊤)
    (hmaj : ∀ U : Opens E, U ≤ Ω →
      ∃ m : ℝ → ℝ≥0∞, Measurable m ∧
        (∀ t, mass (slice (T ∘L (monoCLM ℝ : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) u t) ≤
          m t) ∧
        ∫⁻ t, m t ≤ c₀ * mass (T ∘L (monoCLM ℝ : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)))
    {w : Ω → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤
      c₀ * ∫⁻ x : Ω, w x ∂massMeasure T := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  refine Measure.lintegral_lintegral_le_of_isOpen hc₀top (fun U hU => ?_) hw
  let V : Opens E := ⟨(↑) '' U, Ω.isOpen.isOpenMap_subtypeVal _ hU⟩
  have hV : V ≤ Ω := Subtype.coe_image_subset _ _
  obtain ⟨m, hm_meas, hm_le, hm_int⟩ := hmaj V hV
  refine ⟨m, hm_meas, ?_, ?_⟩
  · filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT
      hu.locallyLipschitzOn] with t ht
    rw [massMeasure_eq_localMass_image ht hU]
    change localMass (slice T u t) (V : Set E) ≤ m t
    rw [← mass_comp_monoCLM hV, ← coe_comp, slice_comp_monoCLM hT hV hu_meas t]
    exact hm_le t
  · rw [massMeasure_eq_localMass_image hT.hasLocallyFiniteMass hU]
    change _ ≤ c₀ * localMass T (V : Set E)
    rw [← mass_comp_monoCLM hV]
    simpa only [coe_comp] using hm_int

/-- **Weighted Lipschitz slicing inequality** on a general normed space: for a locally normal
`(k + 1)`-current `T`, `K`-Lipschitz `u` on `Ω`, and Borel measurable `w : Ω → ℝ≥0∞`,
`∫⁻ t, ∫⁻ x, w x ∂‖⟨T, u, t⟩‖ ≤ (k + 1) * K * ∫⁻ x, w x ∂‖T‖`. -/
theorem lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) {w : Ω → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤
      (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * ∫⁻ x : Ω, w x ∂massMeasure T :=
  lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_aux hT hu (by finiteness)
    (fun _ hU => exists_measurable_mass_slice_le_of_lipschitzOnWith hT.comp_monoCLM (hu.mono hU))
    hw

/-! ### Sharp constants on inner product spaces -/

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}

/-- **Sharp measurable majorant for the mass of Lipschitz slices on an inner product space**
(Federer 4.3.2(2)): `∫⁻ t, m t ≤ K * mass T`, with no dimension-dependent factor. -/
theorem exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice T u t) ≤ m t) ∧
      ∫⁻ t, m t ≤ (K : ℝ≥0∞) * mass T := by
  simpa only [one_mul] using
    exists_measurable_mass_slice_le_of_lipschitzOnWith_aux hT hu 1 fun _ hg => by
      simpa only [one_mul] using exists_measurable_mass_slice_le_of_innerProductSpace hT hg

/-- **The sharp Lipschitz slicing inequality on an inner product space** (Federer 4.3.2(2)):
`∫⁻ t, mass ⟨T, u, t⟩ ≤ K * mass T`. -/
theorem lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t, mass (slice T u t) ≤ (K : ℝ≥0∞) * mass T := by
  obtain ⟨_, -, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hT hu
  exact (lintegral_mono hm_le).trans hm_int

/-- **Sharp local Lipschitz slicing inequality** on an open subset `U ≤ Ω` of an inner product
space: for a locally normal `(k + 1)`-current `T` on `Ω` and `u : E → ℝ` that is `K`-Lipschitz on
`U` and measurable on `Ω`, `∫⁻ t, localMass ⟨T, u, t⟩ U ≤ K * localMass T U`. -/
theorem lintegral_localMass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {U : Opens E} (hU : U ≤ Ω)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u U) (huΩ : Measurable fun x : Ω => u x) :
    ∫⁻ t : ℝ, localMass (slice T u t) U ≤ (K : ℝ≥0∞) * localMass T U := by
  simp_rw [← mass_comp_monoCLM hU (f := T)]
  simpa only [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU huΩ] using
    lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hT.comp_monoCLM hu

/-- **Sharp weighted Lipschitz slicing inequality on an inner product space** (Federer 4.3.2(2)):
for a locally normal `(k + 1)`-current `T`, `K`-Lipschitz `u` on `Ω`, and Borel measurable
`w : Ω → ℝ≥0∞`, `∫⁻ t, ∫⁻ x, w x ∂‖⟨T, u, t⟩‖ ≤ K * ∫⁻ x, w x ∂‖T‖`. -/
theorem lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) {w : Ω → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤
      (K : ℝ≥0∞) * ∫⁻ x : Ω, w x ∂massMeasure T :=
  lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_aux hT hu ENNReal.coe_ne_top
    (fun _ hU => exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
      hT.comp_monoCLM (hu.mono hU)) hw

/-- **Sharp Lipschitz slicing inequality on a strip on an inner product space**:
`∫⁻ t in Ioo a b, mass ⟨T, u, t⟩ ≤ K * ‖T‖ {a < u < b}`. -/
theorem setLIntegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) (a b : ℝ) :
    ∫⁻ t in Ioo a b, mass (slice T u t) ≤ (K : ℝ≥0∞) * massMeasure T {x | u x ∈ Ioo a b} := by
  simpa only [one_mul] using
    setLIntegral_mass_slice_le_of_lipschitzOnWith_aux hu a b 1 fun _ hg => by
      simpa only [one_mul] using exists_measurable_mass_slice_le_of_innerProductSpace hT hg

end InnerProductSpace

end Distribution
