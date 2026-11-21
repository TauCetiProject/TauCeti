/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.Mass.Slice
public import TauCeti.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Slicing of currents by Lipschitz and locally Lipschitz functions

This file extends slicing of locally normal currents from smooth functions to Lipschitz and locally
Lipschitz functions, following Federer, *Geometric Measure Theory*, §§4.3.1–4.3.2, and Simon,
*Introduction to Geometric Measure Theory*, Chapter 6, §5.

Given `K`-Lipschitz `u : E → ℝ` on `Ω`, McShane extension (`LipschitzOnWith.extend_real`),
bump-convolution smoothing (`LipschitzWith.exists_contDiff_lipschitzWith_dist_lt`), and an upward
shift yield smooth `K`-Lipschitz `g_j` with `u < g_j` on `Ω` converging uniformly to `u`. Hence
`1_{g_j < t} → 1_{u < t}` everywhere on `Ω` for every `t`, so `⟨T, g_j, t⟩ → ⟨T, u, t⟩` weakly.

## Main results

* `Distribution.exists_contDiff_lipschitzWith_slice_tendsto`: shifted smooth `K`-Lipschitz
  approximants `g_j` whose slices converge pointwise on test forms at every level `t ∈ ℝ`.
* `Distribution.lintegral_mass_slice_le_of_lipschitzOnWith`,
  `Distribution.lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace`: the slicing
  inequality for `K`-Lipschitz functions on `Ω` (sharp constant `K` on inner product spaces).
* `Distribution.ae_isNormal_slice_of_lipschitzOnWith`,
  `Distribution.ae_isNormal_massRestrict_lt_of_lipschitzOnWith`: for normal `T` and `u` Lipschitz
  on `Ω`, `⟨T, u, t⟩` and `T ⌞ {u < t}` are normal for Lebesgue-a.e. `t`.
* `Distribution.ae_isLocallyNormal_slice_of_locallyLipschitzOn`: for locally normal `T` and `u`
  locally Lipschitz on `Ω`, `⟨T, u, t⟩` is locally normal for Lebesgue-a.e. `t`.
* `Distribution.lintegral_normalFlatMass_slice_sub_slice_le`: normal flat continuity of slices
  (`∫⁻ t, F(⟨T, v, t⟩ - ⟨T, u, t⟩) ≤ ∫ |v - u| d(‖T‖ + ‖∂T‖)`).
* `Distribution.lintegral_normalFlatMass_slice_le`,
  `Distribution.lintegral_normalFlatMass_slice_le_of_innerProductSpace`: the flat-norm slicing
  inequality `∫⁻ t, F(⟨N, u, t⟩) ≤ K · F(N)` on inner product spaces (factor `k + 2` generally).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology ContDiff symmDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {K : ℝ≥0} {u v : E → ℝ}

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

/-! ### Normal flat continuity and flat-mass slicing bounds -/

/-- **Normal flat continuity of slices with respect to the slicing function.**
For a real normal `(k + 1)`-current `T` and Lipschitz functions `u, v` on `Ω`,
`∫⁻ t, F(⟨T, v, t⟩ - ⟨T, u, t⟩) ≤ ∫⁻ x, edist (v x) (u x) ∂(‖T‖ + ‖∂T‖)`. -/
theorem lintegral_normalFlatMass_slice_sub_slice_le {K₁ K₂ : ℝ≥0}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K₁ u Ω) (hv : LipschitzOnWith K₂ v Ω) :
    ∫⁻ t : ℝ, (slice T v t - slice T u t).normalFlatMass ≤
      ∫⁻ x : Ω, edist (v x) (u x) ∂(massMeasure T + massMeasure (T ∘L extDerivCLM)) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  have hv_meas : Measurable fun x : Ω => v x := hv.continuousOn.domRestrict.measurable
  let Au (t : ℝ) : Set Ω := {x : Ω | u x < t}
  let Av (t : ℝ) : Set Ω := {x : Ω | v x < t}
  have hAu (t : ℝ) : MeasurableSet (Au t) := measurableSet_lt hu_meas (measurable_const (a := t))
  have hAv (t : ℝ) : MeasurableSet (Av t) := measurableSet_lt hv_meas (measurable_const (a := t))
  -- Step 1: bound the mass of the difference of sublevel restrictions by the symmetric difference.
  have hmass_diff {m : ℕ} (Q : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) (t : ℝ) :
      mass (massRestrict Q (hAv t) - massRestrict Q (hAu t)) ≤
        massMeasure Q (Av t ∆ Au t) := by
    have hsplit : massRestrict Q (hAv t) - massRestrict Q (hAu t) =
        massRestrict Q ((hAv t).diff (hAu t)) - massRestrict Q ((hAu t).diff (hAv t)) := by
      rw [massRestrict_congr_set (T := Q) (hAv t) (((hAv t).inter (hAu t)).union
          ((hAv t).diff (hAu t))) (inter_union_sdiff _ _).symm,
        massRestrict_congr_set (T := Q) (hAu t) (((hAv t).inter (hAu t)).union
          ((hAu t).diff (hAv t))) (by rw [inter_comm]; exact (inter_union_sdiff _ _).symm),
        massRestrict_union ((hAv t).inter (hAu t)) ((hAv t).diff (hAu t)) disjoint_inf_sdiff,
        massRestrict_union ((hAv t).inter (hAu t)) ((hAu t).diff (hAv t))
          (disjoint_sdiff_self_right.mono_left inter_subset_left),
        add_sub_add_left_eq_sub]
    rw [hsplit, Set.symmDiff_def,
      measure_union disjoint_sdiff_sdiff ((hAu t).diff (hAv t))]
    exact mass_sub_le.trans <| add_le_add (mass_massRestrict_le _) (mass_massRestrict_le _)
  -- Step 2: decompose `⟨T, v, t⟩ - ⟨T, u, t⟩ = Rt + ∂St` to bound its normal flat mass a.e.
  let μ : Measure Ω := massMeasure T + massMeasure (T ∘L extDerivCLM)
  have hae_bound : ∀ᵐ t : ℝ, (slice T v t - slice T u t).normalFlatMass ≤ μ (Av t ∆ Au t) := by
    filter_upwards [ae_isNormal_massRestrict_lt_of_lipschitzOnWith hT hu,
      ae_isNormal_massRestrict_lt_of_lipschitzOnWith hT hv,
      ae_isNormal_slice_of_lipschitzOnWith hT hu,
      ae_isNormal_slice_of_lipschitzOnWith hT hv] with t hNu_r hNv_r hNu_s hNv_s
    let St := massRestrict T (hAv t) - massRestrict T (hAu t)
    let Rt := -(massRestrict (T ∘L extDerivCLM) (hAv t) -
      massRestrict (T ∘L extDerivCLM) (hAu t))
    have hdecomp : slice T v t - slice T u t = Rt + St ∘L extDerivCLM := by
      ext φ; simp [St, Rt, slice_apply _ hu_meas, slice_apply _ hv_meas]; ring
    have hRt_normal : IsNormal Rt := by
      have hRt_eq : Rt = (slice T v t - slice T u t) - St ∘L extDerivCLM := by
        rw [hdecomp]; abel
      rw [hRt_eq]
      exact (hNv_s.sub hNu_s).sub (hNv_r.sub hNu_r).comp_extDerivCLM
    refine ((slice T v t - slice T u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM
      hRt_normal (hNv_r.sub hNu_r) hdecomp).trans ?_
    rw [FunLike.coe_neg, mass_neg, _root_.add_apply, add_comm]
    exact add_le_add (hmass_diff T t) (hmass_diff (T ∘L extDerivCLM) t)
  -- Step 3: integrate the a.e. bound and apply the superlevel symmetric-difference identity via
  -- negation (`v x < t ↔ -t < -v x`).
  refine (lintegral_mono_ae hae_bound).trans_eq ?_
  calc ∫⁻ t : ℝ, μ (Av t ∆ Au t)
      = ∫⁻ t : ℝ, μ ({x : Ω | -t < -v x} ∆ {x : Ω | -t < -u x}) := by
        refine lintegral_congr fun t => ?_
        simp only [Av, Au, neg_lt_neg_iff]
    _ = ∫⁻ s : ℝ, μ ({x : Ω | s < -v x} ∆ {x : Ω | s < -u x}) :=
        lintegral_neg_eq_self (fun s => μ ({x : Ω | s < -v x} ∆ {x : Ω | s < -u x}))
    _ = ∫⁻ x : Ω, ‖-v x - -u x‖ₑ ∂μ :=
        (Measure.lintegral_enorm_sub_eq_lintegral_measure_symmDiff_setOf_lt μ
          hv_meas.neg.aemeasurable hu_meas.neg.aemeasurable).symm
    _ = ∫⁻ x : Ω, edist (v x) (u x) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [neg_sub_neg, ← eDist_eq_eNorm_sub, edist_comm]

omit [FiniteDimensional ℝ E] in
private theorem slice_eq_zero_of_lipschitzOnWith_zero
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith 0 u Ω) (t : ℝ) :
    slice T u t = 0 := by
  obtain ⟨hT1, hT2⟩ := isLocallyNormal_succ_iff.1 hT
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hu_meas measurable_const
  ext φ
  rw [slice_apply _ hu_meas, zero_apply]
  by_cases hne : ∃ x : Ω, u x < t
  · obtain ⟨x₀, hx₀⟩ := hne
    have h : {x : Ω | u x < t} = univ := eq_univ_of_forall fun x => by
      have hux : u x = u x₀ := by
        simpa using hu.dist_le_mul (x : E) x.property (x₀ : E) x₀.property
      simpa only [mem_ofPred_eq, hux] using hx₀
    rw [massRestrict_congr_set (T := T) hA MeasurableSet.univ h,
      massRestrict_congr_set (T := T ∘L extDerivCLM) hA MeasurableSet.univ h,
      massRestrict_univ_apply hT1, massRestrict_univ_apply hT2, comp_apply, sub_self]
  · have h : {x : Ω | u x < t} = ∅ := eq_empty_of_forall_notMem fun x hx => hne ⟨x, hx⟩
    rw [massRestrict_congr_set (T := T) hA MeasurableSet.empty h,
      massRestrict_congr_set (T := T ∘L extDerivCLM) hA MeasurableSet.empty h,
      massRestrict_eq_zero MeasurableSet.empty (by simp),
      massRestrict_eq_zero MeasurableSet.empty (by simp)]
    simp

private theorem lintegral_normalFlatMass_slice_le_aux
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hu : LipschitzOnWith K u Ω)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hR_maj : ∀ R : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ, IsLocallyNormal R →
      ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice R u t) ≤ m t) ∧ ∫⁻ t, m t ≤ c * mass R)
    (hS_maj : ∀ S : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] ℝ) →L[ℝ] ℝ, IsLocallyNormal S →
      ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice S u t) ≤ m t) ∧ ∫⁻ t, m t ≤ c * mass S) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤ c * N.normalFlatMass := by
  rw [normalFlatMass_def]
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  let R := N - S ∘L extDerivCLM
  obtain ⟨mR, hmR_meas, hmR_le, hmR_int⟩ := hR_maj R hR.isLocallyNormal
  obtain ⟨mS, -, hmS_le, hmS_int⟩ := hS_maj S hS.isLocallyNormal
  have hae : ∀ᵐ t : ℝ, (slice N u t).normalFlatMass ≤ mR t + mS t := by
    filter_upwards [ae_isNormal_slice_of_lipschitzOnWith hR hu,
      ae_isNormal_slice_of_lipschitzOnWith hS hu] with t hNR hNS
    refine ((slice N u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM hNR hNS.neg (by
      rw [neg_comp, slice_comp_extDerivCLM S u t, neg_neg,
        ← slice_add hR.isLocallyNormal hS.comp_extDerivCLM.isLocallyNormal]
      simp)).trans ?_
    rw [FunLike.coe_neg, mass_neg]
    exact add_le_add (hmR_le t) (hmS_le t)
  calc ∫⁻ t : ℝ, (slice N u t).normalFlatMass
      ≤ ∫⁻ t : ℝ, (mR t + mS t) := lintegral_mono_ae hae
    _ = (∫⁻ t : ℝ, mR t) + ∫⁻ t : ℝ, mS t := lintegral_add_left hmR_meas _
    _ ≤ c * mass R + c * mass S := add_le_add hmR_int hmS_int
    _ = c * (mass R + mass S) := (mul_add _ _ _).symm

/-- **Flat-mass slicing inequality** on a general normed space:
for a real normal `(k + 1)`-current `N` and `u` that is `K`-Lipschitz on `Ω`,
`∫⁻ t, F(⟨N, u, t⟩) ≤ (k + 2) * K * F(N)`. -/
theorem lintegral_normalFlatMass_slice_le
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hN : IsNormal N)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤
      (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * N.normalFlatMass := by
  by_cases hK : K = 0
  · subst hK; simp [slice_eq_zero_of_lipschitzOnWith_zero hN.isLocallyNormal hu]
  refine lintegral_normalFlatMass_slice_le_aux hu (mul_ne_zero (by positivity) (by positivity))
    (by finiteness) (fun _ hR => ?_) fun _ hS => ?_
  · obtain ⟨m, hm1, hm2, hm3⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hR hu
    exact ⟨m, hm1, hm2, hm3.trans (by gcongr; norm_num)⟩
  · obtain ⟨m, hm1, hm2, hm3⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hS hu
    exact ⟨m, hm1, hm2, by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hm3⟩

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

/-- **Sharp flat-mass slicing inequality on an inner product space** (Federer 4.3.2(2)):
for a real normal `(k + 1)`-current `N` and `u` that is `K`-Lipschitz on `Ω`,
`∫⁻ t, F(⟨N, u, t⟩) ≤ K * F(N)`. -/
theorem lintegral_normalFlatMass_slice_le_of_innerProductSpace
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hN : IsNormal N)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤ (K : ℝ≥0∞) * N.normalFlatMass := by
  by_cases hK : K = 0
  · subst hK; simp [slice_eq_zero_of_lipschitzOnWith_zero hN.isLocallyNormal hu]
  exact lintegral_normalFlatMass_slice_le_aux hu (by positivity) ENNReal.coe_ne_top
    (fun _ hR => exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hR hu)
    (fun _ hS => exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hS hu)

end InnerProductSpace

end Distribution
