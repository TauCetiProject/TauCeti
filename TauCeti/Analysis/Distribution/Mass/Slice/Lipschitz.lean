/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Slice.Basic
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Slicing of currents by Lipschitz and locally Lipschitz functions

This file extends slicing of locally normal currents from smooth functions to Lipschitz and locally
Lipschitz functions, following Federer, *Geometric Measure Theory*, §§4.3.1–4.3.2, and Simon,
*Introduction to Geometric Measure Theory*, Chapter 6, §5.

Given `K`-Lipschitz `u : E → ℝ` on `Ω`, McShane extension (`LipschitzOnWith.extend_real`),
bump-convolution smoothing (`LipschitzWith.exists_contDiff_lipschitzWith_dist_lt`), and an upward
shift yield smooth `K`-Lipschitz `g_j` with `u < g_j` on `Ω` converging uniformly to `u`. Hence
`1_{g_j < t} → 1_{u < t}` everywhere on `Ω` for every `t`, so `⟨T, g_j, t⟩ → ⟨T, u, t⟩` weakly.

## Main declarations

* `Distribution.exists_contDiff_lipschitzWith_slice_tendsto`: shifted smooth `K`-Lipschitz
  approximants `g_j` whose slices converge pointwise on test forms at every level `t ∈ ℝ`.
* `Distribution.slice_eq_zero_of_lipschitzOnWith_zero`: a slice by a `0`-Lipschitz function on `Ω`
  is zero.
* `Distribution.lintegral_mass_slice_le_of_lipschitzOnWith`,
  `Distribution.lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace`: the slicing
  inequality for `K`-Lipschitz functions on `Ω` (sharp constant `K` on inner product spaces).
* `Distribution.lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith`,
  `Distribution.lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_of_innerProductSpace`:
  weighted mass-measure slicing inequalities for nonnegative Borel weights.
* `Distribution.ae_isNormal_slice_of_lipschitzOnWith`,
  `Distribution.ae_isNormal_massRestrict_lt_of_lipschitzOnWith`: for normal `T` and `u` Lipschitz
  on `Ω`, `⟨T, u, t⟩` and `T ⌞ {u < t}` are normal for Lebesgue-a.e. `t`.
* `Distribution.ae_isLocallyNormal_slice_of_locallyLipschitzOn`: for locally normal `T` and `u`
  locally Lipschitz on `Ω`, `⟨T, u, t⟩` is locally normal for Lebesgue-a.e. `t`.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {K : ℝ≥0} {u : E → ℝ}

/-! ### Smooth Lipschitz approximation of slices -/

/-- **Shifted smooth Lipschitz approximation for slices.** For `u` that is `K`-Lipschitz on `Ω`,
there exists a sequence of globally smooth `K`-Lipschitz functions `g_j : E → ℝ` converging to `u`
on `Ω` from strictly above (`u x < g_j x` on `Ω`) such that `⟨T, g_j, t⟩ φ → ⟨T, u, t⟩ φ` as
`j → ∞` for every current `T` on `Ω`, every `t ∈ ℝ`, and every test form `φ`. -/
theorem exists_contDiff_lipschitzWith_slice_tendsto (hu : LipschitzOnWith K u Ω) :
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
  have hg_lip (j : ℕ) : LipschitzWith K (g j) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa [g, add_sub_add_right_eq_sub] using (hw_lip j).dist_le_mul x y
  have hg_bounds (x : Ω) (j : ℕ) : u x < g j x ∧ g j x - u x < ((j : ℝ) + 1)⁻¹ := by
    have hdist : |w j x - u x| < ((j : ℝ) + 1)⁻¹ / 4 := by
      simpa [Real.dist_eq, hu_eq x.property] using hw_dist j x
    obtain ⟨hd1, hd2⟩ := abs_lt.1 hdist
    exact ⟨by dsimp [g]; linarith, by dsimp [g]; linarith⟩
  have hg_lim (x : Ω) : Tendsto (fun j => g j x) atTop (𝓝 (u x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_inv_atTop_zero.comp
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
  simp only [slice_apply _ hu_meas, slice_apply _ (hg_meas _)]
  exact (tendsto_massRestrict_of_eventually_iff
      (fun j => measurableSet_lt (hg_meas j) measurable_const)
      (measurableSet_lt hu_meas measurable_const) hiff (extDerivCLM φ)).sub
    (tendsto_massRestrict_of_eventually_iff
      (fun j => measurableSet_lt (hg_meas j) measurable_const)
      (measurableSet_lt hu_meas measurable_const) hiff φ)

/-! ### The slicing inequality for Lipschitz functions -/

private theorem exists_measurable_mass_slice_le_of_lipschitzOnWith_aux
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) (c : ℝ≥0∞)
    (hsmooth : ∀ g : E → ℝ, ContDiff ℝ ∞ g → ∃ m : ℝ → ℝ≥0∞, Measurable m ∧
      (∀ t, mass (slice T g t) ≤ m t) ∧
      ∫⁻ t, m t ≤ c * ∫⁻ x : Ω, ‖fderiv ℝ g x‖ₑ ∂massMeasure T) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice T u t) ≤ m t) ∧
      ∫⁻ t, m t ≤ c * (K : ℝ≥0∞) * mass T := by
  obtain ⟨g, hg_smooth, hg_lip, -, -, hg_slice⟩ := exists_contDiff_lipschitzWith_slice_tendsto hu
  choose mj hmj_meas hmj_le hmj_int using fun j => hsmooth (g j) (hg_smooth j)
  refine ⟨fun t => liminf (fun j => mj j t) atTop, Measurable.liminf hmj_meas,
    fun t => (mass_le_liminf (hg_slice T t)).trans
      (liminf_le_liminf (.of_forall fun j => hmj_le j t)),
    (lintegral_liminf_le hmj_meas).trans <| liminf_le_of_frequently_le' <| .of_forall fun j =>
      (hmj_int j).trans ?_⟩
  calc c * ∫⁻ x : Ω, ‖fderiv ℝ (g j) x‖ₑ ∂massMeasure T
      ≤ c * ∫⁻ _ : Ω, (K : ℝ≥0∞) ∂massMeasure T := by
        gcongr with x
        rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ (hg_lip j))
    _ = c * (K : ℝ≥0∞) * mass T := by
        rw [lintegral_const, massMeasure_univ hT.hasLocallyFiniteMass, mul_assoc]

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
  obtain ⟨m, -, hm_le, hm_int⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hT hu
  exact (lintegral_mono hm_le).trans hm_int

/-- **Local Lipschitz slicing inequality** on an open subset `U ≤ Ω` of a normed space. -/
theorem lintegral_localMass_slice_le_of_lipschitzOnWith {U : Opens E} (hU : U ≤ Ω)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u U) (huΩ : Measurable fun x : Ω => u x) :
    ∫⁻ t, localMass (slice T u t) U ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * localMass T U := by
  simp_rw [← mass_comp_monoCLM hU (f := T)]
  simpa only [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU huΩ] using
    lintegral_mass_slice_le_of_lipschitzOnWith hT.comp_monoCLM hu

/-! ### Almost-everywhere normality and local normality of slices -/

/-- For a locally normal current `T` of finite mass and `u` Lipschitz on `Ω`,
`mass ⟨T, u, t⟩ < ⊤` for Lebesgue-a.e. `t ∈ ℝ`. -/
theorem ae_mass_slice_lt_top_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hmass : mass T ≠ ⊤) (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ, mass (slice T u t) < ⊤ := by
  obtain ⟨m, hm_meas, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith hT hu
  filter_upwards [ae_lt_top hm_meas (ne_top_of_le_ne_top (by finiteness) hm_int)] with t ht
  exact (hm_le t).trans_lt ht

/-- **Slices of a normal current by a Lipschitz function are normal almost everywhere.** -/
theorem ae_isNormal_slice_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ, IsNormal (slice T u t) := by
  cases k with
  | zero =>
    filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT.mass_ne_top hu]
      with t ht
    exact isNormal_finZero_iff.2 ht.ne
  | succ k =>
    filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT.mass_ne_top hu,
      ae_mass_slice_lt_top_of_lipschitzOnWith hT.comp_extDerivCLM.isLocallyNormal
        (isNormal_succ_iff.1 hT).2 hu] with t ht1 ht2
    rw [isNormal_succ_iff, slice_comp_extDerivCLM T u t, FunLike.coe_neg, mass_neg]
    exact ⟨ht1.ne, ht2.ne⟩

/-- **Sublevel restrictions `T ⌞ {u < t}` of a normal current are normal almost everywhere.** -/
theorem ae_isNormal_massRestrict_lt_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ,
      IsNormal (massRestrict T (measurableSet_lt hu.continuousOn.domRestrict.measurable
        (measurable_const (a := t)))) := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  obtain ⟨hT1, hT2⟩ := isNormal_succ_iff.1 hT
  have hres_fin {m : ℕ} {Q : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] ℝ} (hQ : mass Q ≠ ⊤)
      {A : Set Ω} (hA : MeasurableSet A) : mass (massRestrict Q hA) ≠ ⊤ :=
    ne_top_of_le_ne_top hQ <| (mass_massRestrict_le hA).trans <|
      (measure_mono (subset_univ _)).trans_eq
        (massMeasure_univ (hasLocallyFiniteMass_of_mass_ne_top Q hQ))
  filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT1 hu] with t ht
  have hA : MeasurableSet {x : Ω | u x < t} :=
    measurableSet_lt hu_meas (measurable_const (a := t))
  have hbd : massRestrict T hA ∘L extDerivCLM =
      slice T u t + massRestrict (T ∘L extDerivCLM) hA := by
    ext φ; simp [slice_apply _ hu_meas]
  rw [massRestrict_congr_set (T := T)
    (measurableSet_lt hu.continuousOn.domRestrict.measurable (measurable_const (a := t)))
    hA (by ext x; rfl)]
  refine isNormal_succ_iff.2 ⟨hres_fin hT1 hA, ?_⟩
  rw [hbd, FunLike.coe_add]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ht.ne, hres_fin hT2 hA⟩) mass_add_le

/-- For a locally normal current `T` and `u` locally Lipschitz on `Ω`, the slice `⟨T, u, t⟩` has
locally finite mass for Lebesgue-a.e. `t ∈ ℝ`. -/
theorem ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ, HasLocallyFiniteMass (slice T u t) := by
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
  choose L hL using fun n =>
    (hu.mono (hC_sub n)).exists_lipschitzOnWith_of_compact (hC_cpt n)
  filter_upwards [ae_all_iff.2 fun n => ae_mass_slice_lt_top_of_lipschitzOnWith hT.comp_monoCLM
    (by rw [coe_comp, mass_comp_monoCLM (hW_le n)]
        exact ne_top_of_le_ne_top
          ((hasLocallyFiniteMass_iff_localMass_ne_top T).1 hT.hasLocallyFiniteMass
            (C n) (hC_cpt n) (hC_sub n)) (localMass_mono (hW_sub_C n)))
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
  | zero =>
    simpa only [isLocallyNormal_finZero_iff] using
      ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu
  | succ k =>
    have hbd : IsLocallyNormal (T ∘L extDerivCLM) := isLocallyNormal_succ_iff.2
      ⟨(isLocallyNormal_succ_iff.1 hT).2,
        by simp [comp_assoc, extDerivCLM_comp_extDerivCLM, hasLocallyFiniteMass_zero]⟩
    filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu,
      ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hbd hu] with t ht1 ht2
    rw [isLocallyNormal_succ_iff, slice_comp_extDerivCLM T u t]
    exact ⟨ht1, ht2.neg⟩

omit [FiniteDimensional ℝ E] in
/-- **A slice by a `0`-Lipschitz function on `Ω` is zero** for any locally normal current. -/
theorem slice_eq_zero_of_lipschitzOnWith_zero
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith 0 u Ω) (t : ℝ) :
    slice T u t = 0 := by
  by_cases hΩ : Nonempty Ω
  · obtain ⟨x₀⟩ := hΩ
    have h : EqOn u (fun _ => u x₀) Ω := fun x hx => by
      simpa using hu.dist_le_mul x hx (x₀ : E) x₀.property
    rw [slice_congr_of_eqOn T h, slice_const hT]
  · rw [not_nonempty_iff] at hΩ
    have h : EqOn u (fun _ => 0) Ω := fun x hx => (hΩ.false ⟨x, hx⟩).elim
    rw [slice_congr_of_eqOn T h, slice_const hT]

private theorem lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_aux
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) {c₀ : ℝ≥0∞} (hc₀top : c₀ ≠ ⊤)
    (hmaj : ∀ U : Opens E, U ≤ Ω →
      ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, localMass (slice T u t) U ≤ m t) ∧
        ∫⁻ t, m t ≤ c₀ * localMass T U)
    {w : Ω → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤
      c₀ * ∫⁻ x : Ω, w x ∂massMeasure T := by
  by_cases hc₀0 : c₀ = 0
  · subst hc₀0
    obtain ⟨m, hm_meas, hm_le, hm_int⟩ := hmaj Ω le_rfl
    have hm0 : ∀ᵐ t : ℝ, m t = 0 :=
      (lintegral_eq_zero_iff hm_meas).1 (nonpos_iff_eq_zero.1 (by simpa using hm_int))
    have hae : ∀ᵐ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) = 0 := by
      filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu.locallyLipschitzOn,
        hm0] with t ht hmt
      have hμ0 : massMeasure (slice T u t) = 0 := by
        rw [← Measure.measure_univ_eq_zero]
        have huniv : ((↑) ⁻¹' (Ω : Set E) : Set Ω) = univ :=
          eq_univ_of_forall fun x => x.property
        rw [← huniv, massMeasure_preimage_coe ht Ω.isOpen]
        exact nonpos_iff_eq_zero.1 ((hm_le t).trans_eq hmt)
      simp [hμ0]
    simp [lintegral_congr_ae hae]
  by_cases hwint : ∫⁻ x : Ω, w x ∂massMeasure T = ⊤
  · rw [hwint, ENNReal.mul_top hc₀0]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : 0 < (ε : ℝ≥0∞) / c₀ :=
    ENNReal.div_pos (ENNReal.coe_pos.2 hε).ne' hc₀top
  let d : ℕ → SimpleFunc Ω ℝ≥0 := SimpleFunc.eapproxDiff w
  let ι := Σ n : ℕ, {r : ℝ≥0 // r ∈ (d n).range.erase 0}
  let c (p : ι) : ℝ≥0∞ := (p.snd.val : ℝ≥0∞)
  let A (p : ι) : Set Ω := (d p.fst) ⁻¹' {p.snd.val}
  have hc_pos (p : ι) : c p ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Finset.mem_erase.1 p.snd.property).1
  have hA_meas (p : ι) : MeasurableSet (A p) :=
    (d p.fst).measurableSet_fiber p.snd.val
  have hw_eq (x : Ω) : w x = ∑' p : ι, c p * (A p).indicator 1 x := by
    rw [tsum_sigma', ← SimpleFunc.tsum_eapproxDiff w hw x]
    refine tsum_congr fun n => ?_
    have hsum : (d n x : ℝ≥0∞) =
        ∑ r ∈ (d n).range.erase 0, (r : ℝ≥0∞) * ((d n ⁻¹' {r}).indicator 1 x) := by
      by_cases h0 : d n x = 0
      · rw [h0, ENNReal.coe_zero, eq_comm]
        exact Finset.sum_eq_zero fun r hr => by
          simp [(Finset.ne_of_mem_erase hr).symm, h0]
      · have hmem : d n x ∈ (d n).range.erase 0 :=
          Finset.mem_erase.2 ⟨h0, SimpleFunc.mem_range_self (d n) x⟩
        rw [Finset.sum_eq_single_of_mem (d n x) hmem]
        · simp
        · intro r _ hne
          simp [Ne.symm hne]
    rw [hsum, ← Finset.tsum_subtype' ((d n).range.erase 0) fun r =>
      (r : ℝ≥0∞) * ((d n ⁻¹' {r}).indicator 1 x)]
    rfl
  have hw_int_eq : ∫⁻ x : Ω, w x ∂massMeasure T = ∑' p : ι, c p * massMeasure T (A p) := by
    rw [lintegral_congr hw_eq, lintegral_tsum fun p =>
      ((measurable_one.indicator (hA_meas p)).const_mul (c p)).aemeasurable]
    refine tsum_congr fun p => ?_
    rw [lintegral_const_mul _ (measurable_one.indicator (hA_meas p)),
      lintegral_indicator_one (hA_meas p)]
  have hA_fin (p : ι) : massMeasure T (A p) ≠ ⊤ := by
    have hle : c p * massMeasure T (A p) ≤ ∫⁻ x : Ω, w x ∂massMeasure T := by
      rw [hw_int_eq]
      exact le_tsum (fun p => c p * massMeasure T (A p)) p
    exact fun htop => hwint (top_le_iff.1 (by rw [← ENNReal.mul_top (hc_pos p), ← htop]; exact hle))
  let δ (p : ι) : ℝ≥0∞ :=
    ((ε : ℝ≥0∞) / c₀) / (c p * 2 ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞))
  have hδ_pos (p : ι) : δ p ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨hε'.ne', by finiteness⟩
  have hU_ex (p : ι) : ∃ U : Set Ω, A p ⊆ U ∧ IsOpen U ∧
      massMeasure T U < massMeasure T (A p) + δ p :=
    (A p).exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right (hA_fin p) (hδ_pos p))
  choose U hAU hUo hU_lt using hU_ex
  let V (p : ι) : Opens E := ⟨(↑) '' U p, Ω.isOpen.isOpenMap_subtypeVal _ (hUo p)⟩
  have hV_le (p : ι) : V p ≤ Ω := Subtype.coe_image_subset _ _
  have hV_pre (p : ι) : ((↑) ⁻¹' (V p : Set E) : Set Ω) = U p :=
    Subtype.val_injective.preimage_image (U p)
  choose m hm_meas hm_le hm_int using fun p : ι => hmaj (V p) (hV_le p)
  have hstep1 (t : ℝ) : ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤
      ∑' p : ι, c p * massMeasure (slice T u t) (U p) := by
    calc ∫⁻ x : Ω, w x ∂massMeasure (slice T u t)
        ≤ ∫⁻ x : Ω, ∑' p : ι, c p * (U p).indicator 1 x ∂massMeasure (slice T u t) := by
          refine lintegral_mono fun x => ?_
          rw [hw_eq]
          refine tsum_le_tsum fun p => ?_
          gcongr
          exact hAU p
      _ = ∑' p : ι, c p * massMeasure (slice T u t) (U p) := by
          rw [lintegral_tsum fun p =>
            ((measurable_one.indicator (hUo p).measurableSet).const_mul (c p)).aemeasurable]
          refine tsum_congr fun p => ?_
          rw [lintegral_const_mul _ (measurable_one.indicator (hUo p).measurableSet),
            lintegral_indicator_one (hUo p).measurableSet]
  have hae_slice : ∀ᵐ t : ℝ,
      ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤ ∑' p : ι, c p * m p t := by
    filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT
      hu.locallyLipschitzOn] with t ht
    refine (hstep1 t).trans (tsum_le_tsum fun p => ?_)
    gcongr
    rw [← hV_pre p, massMeasure_preimage_coe ht (V p).isOpen]
    exact hm_le p t
  calc ∫⁻ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t)
      ≤ ∫⁻ t : ℝ, ∑' p : ι, c p * m p t := lintegral_mono_ae hae_slice
    _ = ∑' p : ι, c p * ∫⁻ t : ℝ, m p t := by
        rw [lintegral_tsum fun p => ((hm_meas p).const_mul (c p)).aemeasurable]
        refine tsum_congr fun p => ?_
        rw [lintegral_const_mul _ (hm_meas p)]
    _ ≤ ∑' p : ι, c p * (c₀ * localMass T (V p)) :=
        tsum_le_tsum fun p => by gcongr; exact hm_int p
    _ = c₀ * ∑' p : ι, c p * massMeasure T (U p) := by
        simp_rw [← massMeasure_preimage_coe hT.hasLocallyFiniteMass (V _).isOpen, hV_pre,
          ← mul_assoc, mul_comm (c _) c₀, mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ c₀ * ∑' p : ι, c p * (massMeasure T (A p) + δ p) := by
        gcongr with p
        exact (hU_lt p).le
    _ = c₀ * (∫⁻ x : Ω, w x ∂massMeasure T + ∑' p : ι, c p * δ p) := by
        congr 1
        rw [tsum_congr fun p => mul_add (c p) _ _,
          Summable.tsum_add CompleteLattice.summable CompleteLattice.summable, hw_int_eq]
    _ ≤ c₀ * (∫⁻ x : Ω, w x ∂massMeasure T + (ε : ℝ≥0∞) / c₀) := by
        gcongr
        have hterm (p : ι) : c p * δ p = ((ε : ℝ≥0∞) / c₀) *
            ((2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹) := by
          calc c p * δ p
              = ((ε : ℝ≥0∞) / c₀) * ((c p * (c p)⁻¹) *
                  ((2 ^ (p.fst + 1) : ℝ≥0∞)⁻¹ * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹)) := by
                dsimp [δ]
                rw [div_eq_mul_inv,
                  ENNReal.mul_inv (Or.inl (mul_ne_zero (hc_pos p) (by positivity)))
                    (Or.inl (by finiteness)),
                  ENNReal.mul_inv (Or.inl (hc_pos p)) (Or.inl ENNReal.coe_ne_top)]
                ring
            _ = ((ε : ℝ≥0∞) / c₀) *
                  ((2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹) := by
                rw [ENNReal.mul_inv_cancel (hc_pos p) ENNReal.coe_ne_top, one_mul,
                  ENNReal.inv_pow]
        simp_rw [hterm, ENNReal.tsum_mul_left]
        calc ((ε : ℝ≥0∞) / c₀) *
                ∑' p : ι, (2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹
            ≤ ((ε : ℝ≥0∞) / c₀) * 1 := by
              gcongr
              rw [tsum_sigma']
              calc ∑' n : ℕ, ∑' _ : {r : ℝ≥0 // r ∈ (d n).range.erase 0},
                      (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹
                  = ∑' n : ℕ, ((d n).range.erase 0).card *
                      ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹) := by
                    refine tsum_congr fun n => ?_
                    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
                      nsmul_eq_mul]
                _ ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
                    refine tsum_le_tsum fun n => ?_
                    have hcard : (((d n).range.erase 0).card : ℝ≥0∞) ≤
                        ((d n).range.card + 1 : ℝ≥0∞) := by
                      exact_mod_cast (Finset.card_erase_le.trans (Nat.le_succ _))
                    calc (((d n).range.erase 0).card : ℝ≥0∞) *
                            ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹)
                        ≤ ((d n).range.card + 1 : ℝ≥0∞) *
                            ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹) := by
                          gcongr
                      _ = ((d n).range.card + 1 : ℝ≥0∞) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹ *
                            (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by ring
                      _ = (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
                          rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
                _ = 1 := by
                    simp_rw [pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
                    norm_num
                    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
          _ = (ε : ℝ≥0∞) / c₀ := mul_one _
    _ = c₀ * ∫⁻ x : Ω, w x ∂massMeasure T + (ε : ℝ≥0∞) := by
        rw [mul_add, ENNReal.mul_div_cancel hc₀0 hc₀top]

/-- **Weighted Lipschitz slicing inequality** on a general normed space: for a locally normal
`(k + 1)`-current `T`, `K`-Lipschitz `u` on `Ω`, and Borel measurable `w : Ω → ℝ≥0∞`,
`∫⁻ t, ∫⁻ x, w x ∂‖⟨T, u, t⟩‖ ≤ (k + 1) * K * ∫⁻ x, w x ∂‖T‖`. -/
theorem lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) {w : Ω → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ t : ℝ, ∫⁻ x : Ω, w x ∂massMeasure (slice T u t) ≤
      (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * ∫⁻ x : Ω, w x ∂massMeasure T := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  refine lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_aux hT hu (by finiteness)
    (fun U hU => ?_) hw
  obtain ⟨m, hm_meas, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith hT.comp_monoCLM (hu.mono hU)
  refine ⟨m, hm_meas, fun t => ?_, ?_⟩
  · simpa only [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU hu_meas t] using
      hm_le t
  · simpa only [← mass_comp_monoCLM hU, coe_comp] using hm_int

/-! ### Sharp constants on inner product spaces -/

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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
  obtain ⟨m, -, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hT hu
  exact (lintegral_mono hm_le).trans hm_int

/-- **Sharp local Lipschitz slicing inequality** on an open subset `U ≤ Ω` of an inner product
space: `∫⁻ t, localMass ⟨T, u, t⟩ U ≤ K * localMass T U`. -/
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
      (K : ℝ≥0∞) * ∫⁻ x : Ω, w x ∂massMeasure T := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  refine lintegral_lintegral_massMeasure_slice_le_of_lipschitzOnWith_aux hT hu ENNReal.coe_ne_top
    (fun U hU => ?_) hw
  obtain ⟨m, hm_meas, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
      hT.comp_monoCLM (hu.mono hU)
  refine ⟨m, hm_meas, fun t => ?_, ?_⟩
  · simpa only [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU hu_meas t] using
      hm_le t
  · simpa only [← mass_comp_monoCLM hU, coe_comp] using hm_int

end InnerProductSpace

end Distribution
