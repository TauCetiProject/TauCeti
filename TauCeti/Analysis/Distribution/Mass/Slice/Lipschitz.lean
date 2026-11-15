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

/-!
# Slicing of currents by Lipschitz and locally Lipschitz functions

This file extends the slicing theory of locally normal currents from smooth slicing functions to
Lipschitz and locally Lipschitz functions, following Federer, *Geometric Measure Theory*,
§§4.3.1–4.3.2, and Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5.

Given `u : E → ℝ` that is `K`-Lipschitz on `Ω`, McShane extension (`LipschitzOnWith.extend_real`)
followed by bump-convolution smoothing (`LipschitzWith.exists_contDiff_lipschitzWith_dist_lt`)
and an upward shift by half the approximation radius yields smooth `K`-Lipschitz functions `g_j`
with `u < g_j` on `Ω` converging uniformly on `Ω` to `u`. Because `u x < g_j x` everywhere on `Ω`,
the strict-sublevel indicators `1_{g_j < t}` converge pointwise everywhere on `Ω` to `1_{u < t}` for
every `t ∈ ℝ` (without exceptional levels), so `⟨T, g_j, t⟩ → ⟨T, u, t⟩` weakly for every `t`.

Combining weak lower semicontinuity of mass (`Distribution.mass_le_liminf`) with Fatou's lemma and
the smooth slicing inequality yields the Lipschitz slicing inequality, almost-everywhere normality
of slices of normal currents, almost-everywhere local normality of slices of locally normal currents
by locally Lipschitz functions, and the normal-flat continuity and flat-mass slicing bounds for
real-valued currents.

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
  with respect to the slicing function (`∫⁻ t, F(⟨T, v, t⟩ - ⟨T, u, t⟩) ≤ ∫ |v - u| d(‖T‖ + ‖∂T‖)`).
* `Distribution.lintegral_normalFlatMass_slice_le`,
  `Distribution.lintegral_normalFlatMass_slice_le_of_innerProductSpace`: the flat-norm slicing
  inequality `∫⁻ t, F(⟨N, u, t⟩) ≤ K · F(N)` on inner product spaces (and with factor `k + 2` on
  general normed spaces).

## References

* H. Federer, *Geometric Measure Theory*, §§4.3.1–4.3.2.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {K : ℝ≥0} {u v : E → ℝ}

/-! ### Smooth Lipschitz approximation of slices -/

private theorem massRestrict_congr_set {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (Q : 𝓓(Ω, G) →L[ℝ] ℝ) {A₁ A₂ : Set Ω} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) (h : A₁ = A₂) :
    massRestrict Q hA₁ = massRestrict Q hA₂ := by
  subst h
  rfl

/-- Pointwise convergence of sublevel restrictions `S ⌞ {g_j < t}` to `S ⌞ {u < t}` when
`u x < g_j x` for all `j` and `g_j x → u x` on `Ω`. -/
private theorem tendsto_massRestrict_lt_of_gt_tendsto {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {S : 𝓓(Ω, G) →L[ℝ] ℝ}
    {g : ℕ → E → ℝ} (hg_meas : ∀ j, Measurable fun x : Ω => g j x)
    (hu_meas : Measurable fun x : Ω => u x) (hgt : ∀ j (x : Ω), u x < g j x)
    (hlim : ∀ x : Ω, Tendsto (fun j => g j x) atTop (𝓝 (u x))) (t : ℝ) (η : 𝓓(Ω, G)) :
    Tendsto (fun j => massRestrict S (measurableSet_lt (hg_meas j) (measurable_const (a := t))) η)
      atTop (𝓝 (massRestrict S (measurableSet_lt hu_meas (measurable_const (a := t))) η)) := by
  let Aj (j : ℕ) : Set Ω := {x : Ω | g j x < t}
  have hAj (j : ℕ) : MeasurableSet (Aj j) :=
    measurableSet_lt (hg_meas j) (measurable_const (a := t))
  let A : Set Ω := {x : Ω | u x < t}
  have hA : MeasurableSet A := measurableSet_lt hu_meas (measurable_const (a := t))
  simp_rw [massRestrict_apply]
  refine Filter.Tendsto.comp ((extendL1 S).continuous.tendsto _) ?_
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  have heq (j : ℕ) :
      ‖TestFunction.indicatorToLp 1 (massMeasure S) (hAj j) η -
          TestFunction.indicatorToLp 1 (massMeasure S) hA η‖ₑ =
        ∫⁻ x : Ω, ‖(Aj j).indicator (fun y : Ω => η y) x -
          A.indicator (fun y : Ω => η y) x‖ₑ ∂massMeasure S := by
    rw [TestFunction.indicatorToLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub,
      Lp.eNorm_toLp, eLpNorm_one_eq_lintegral_eNorm
        ((((TestFunction.memLp_subtype (p := 1) η).indicator (hAj j).nullMeasurableSet).sub
          ((TestFunction.memLp_subtype (p := 1) η).indicator
            hA.nullMeasurableSet)).aestronglyMeasurable)]
    rfl
  simp_rw [heq]
  have hdom_int : ∫⁻ x : Ω, (2 : ℝ≥0∞) * ‖η x‖ₑ ∂massMeasure S ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ (by simp),
      ← eLpNorm_one_eq_lintegral_eNorm (TestFunction.memLp_subtype (p := 1) η).aestronglyMeasurable]
    exact ENNReal.mul_ne_top (by simp)
      (TestFunction.memLp_subtype (p := 1) (μ := massMeasure S) η).eLpNorm_lt_top.ne
  have hzero : ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂massMeasure S = 0 := by simp
  rw [← hzero]
  refine tendsto_lintegral_of_dominated_convergence' (fun x : Ω => (2 : ℝ≥0∞) * ‖η x‖ₑ)
    (fun j =>
      ((((η.continuous.comp continuous_subtype_val).aestronglyMeasurable.indicator (hAj j)).sub
        ((η.continuous.comp continuous_subtype_val).aestronglyMeasurable.indicator hA)).eNorm))
    (fun j => ae_of_all _ fun x => ?_) hdom_int (ae_of_all _ fun x => ?_)
  · refine eNorm_sub_le.trans ?_
    dsimp only
    rw [two_mul]
    refine add_le_add ?_ ?_
    · by_cases hx : x ∈ Aj j <;> simp [hx]
    · by_cases hx : x ∈ A <;> simp [hx]
  · by_cases hxu : u x < t
    · have hxA : x ∈ A := hxu
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_order.1 (hlim x)).2 t hxu] with j hj
      have hxAj : x ∈ Aj j := hj
      simp [hxAj, hxA]
    · have hxA : x ∉ A := hxu
      refine tendsto_const_nhds.congr' (.of_forall fun j => ?_)
      have hxAj : x ∉ Aj j := fun hj => hxu ((hgt j x).trans hj)
      simp [hxAj, hxA]

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
  have happrox : ∀ j : ℕ, ∃ w : E → ℝ, ContDiff ℝ ∞ w ∧ LipschitzWith K w ∧
      ∀ x, dist (w x) (u_ext x) < ((j : ℝ) + 1)⁻¹ / 4 := fun j =>
    hu_lip.exists_contDiff_lipschitzWith_dist_lt (by positivity)
  choose w hw_smooth hw_lip hw_dist using happrox
  let g : ℕ → E → ℝ := fun j x => w j x + ((j : ℝ) + 1)⁻¹ / 2
  have hg_smooth (j : ℕ) : ContDiff ℝ ∞ (g j) := (hw_smooth j).add contDiff_const
  have hg_lip (j : ℕ) : LipschitzWith K (g j) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa [g, add_sub_add_right_eq_sub] using (hw_lip j).dist_le_mul x y
  have hg_bounds (x : Ω) (j : ℕ) :
      u x < g j x ∧ g j x - u x < ((j : ℝ) + 1)⁻¹ := by
    have hd : |w j x - u x| < ((j : ℝ) + 1)⁻¹ / 4 := by
      simpa [Real.dist_eq, hu_eq x.2] using hw_dist j x
    obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
    dsimp only [g]
    constructor <;> linarith
  have hg_gt (x : Ω) (j : ℕ) : u x < g j x := (hg_bounds x j).1
  have hg_lim (x : Ω) : Tendsto (fun j => g j x) atTop (𝓝 (u x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))))
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 (hg_gt x j))]
    exact (hg_bounds x j).2.le
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  have hg_meas (j : ℕ) : Measurable fun x : Ω => g j x :=
    ((hg_smooth j).continuous.comp continuous_subtype_val).measurable
  refine ⟨g, hg_smooth, hg_lip, hg_gt, hg_lim, fun T t φ => ?_⟩
  simp only [slice_apply _ hu_meas, slice_apply _ (hg_meas _)]
  exact (tendsto_massRestrict_lt_of_gt_tendsto hg_meas hu_meas
    (fun j x => hg_gt x j) hg_lim t (extDerivCLM φ)).sub
    (tendsto_massRestrict_lt_of_gt_tendsto hg_meas hu_meas (fun j x => hg_gt x j) hg_lim t φ)

/-! ### The slicing inequality for Lipschitz functions -/

/-- **Measurable majorant for the mass of Lipschitz slices** on a general normed space:
if `T` is locally normal on `Ω` and `u` is `K`-Lipschitz on `Ω`, there exists a Borel
measurable `m : ℝ → ℝ≥0∞` dominating `t ↦ mass ⟨T, u, t⟩` with
`∫⁻ t, m t ≤ (k + 1) * K * mass T`. -/
theorem exists_measurable_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice T u t) ≤ m t) ∧
      ∫⁻ t, m t ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * mass T := by
  obtain ⟨g, hg_smooth, hg_lip, -, -, hg_slice⟩ := exists_contDiff_lipschitzWith_slice_tendsto hu
  choose mj hmj_meas hmj_le hmj_int using fun j =>
    exists_measurable_mass_slice_le hT (hg_smooth j)
  let m : ℝ → ℝ≥0∞ := fun t => liminf (fun j => mj j t) atTop
  have hm_meas : Measurable m := Measurable.liminf hmj_meas
  have hm_le (t : ℝ) : mass (slice T u t) ≤ m t :=
    (mass_le_liminf (fun φ => hg_slice T t φ)).trans
      (liminf_le_liminf (.of_forall fun j => hmj_le j t))
  have hmj_bound (j : ℕ) : ∫⁻ t, mj j t ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * mass T := by
    refine (hmj_int j).trans ?_
    have hpt (x : Ω) : ‖fderiv ℝ (g j) x‖ₑ ≤ (K : ℝ≥0∞) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ (hg_lip j))
    calc (k + 1 : ℝ≥0∞) * ∫⁻ x : Ω, ‖fderiv ℝ (g j) x‖ₑ ∂massMeasure T
        ≤ (k + 1 : ℝ≥0∞) * ∫⁻ _ : Ω, (K : ℝ≥0∞) ∂massMeasure T := by
          gcongr with x
          exact hpt x
      _ = (k + 1 : ℝ≥0∞) * ((K : ℝ≥0∞) * massMeasure T univ) := by rw [lintegral_const]
      _ = (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * mass T := by
        rw [massMeasure_univ hT.hasLocallyFiniteMass, mul_assoc]
  refine ⟨m, hm_meas, hm_le, (lintegral_liminf_le hmj_meas).trans ?_⟩
  exact liminf_le_of_frequently_le' (Frequently.of_forall hmj_bound)

/-- **The Lipschitz slicing inequality** on a general normed space:
`∫⁻ t, mass ⟨T, u, t⟩ ≤ (k + 1) * K * mass T`. -/
theorem lintegral_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t, mass (slice T u t) ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * mass T := by
  obtain ⟨m, -, hm_le, hm_int⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hT hu
  exact (lintegral_mono hm_le).trans hm_int

/-- **Sharp measurable majorant for the mass of Lipschitz slices on an inner product space**
(Federer 4.3.2(2)): `∫⁻ t, m t ≤ K * mass T`, with no dimension-dependent factor. -/
theorem exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice T u t) ≤ m t) ∧
      ∫⁻ t, m t ≤ (K : ℝ≥0∞) * mass T := by
  obtain ⟨g, hg_smooth, hg_lip, -, -, hg_slice⟩ := exists_contDiff_lipschitzWith_slice_tendsto hu
  choose mj hmj_meas hmj_le hmj_int using fun j =>
    exists_measurable_mass_slice_le_of_innerProductSpace hT (hg_smooth j)
  let m : ℝ → ℝ≥0∞ := fun t => liminf (fun j => mj j t) atTop
  have hm_meas : Measurable m := Measurable.liminf hmj_meas
  have hm_le (t : ℝ) : mass (slice T u t) ≤ m t :=
    (mass_le_liminf (fun φ => hg_slice T t φ)).trans
      (liminf_le_liminf (.of_forall fun j => hmj_le j t))
  have hmj_bound (j : ℕ) : ∫⁻ t, mj j t ≤ (K : ℝ≥0∞) * mass T := by
    refine (hmj_int j).trans ?_
    have hpt (x : Ω) : ‖fderiv ℝ (g j) x‖ₑ ≤ (K : ℝ≥0∞) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ (hg_lip j))
    calc ∫⁻ x : Ω, ‖fderiv ℝ (g j) x‖ₑ ∂massMeasure T
        ≤ ∫⁻ _ : Ω, (K : ℝ≥0∞) ∂massMeasure T := lintegral_mono hpt
      _ = (K : ℝ≥0∞) * massMeasure T univ := lintegral_const _
      _ = (K : ℝ≥0∞) * mass T := by rw [massMeasure_univ hT.hasLocallyFiniteMass]
  refine ⟨m, hm_meas, hm_le, (lintegral_liminf_le hmj_meas).trans ?_⟩
  exact liminf_le_of_frequently_le' (Frequently.of_forall hmj_bound)

/-- **The sharp Lipschitz slicing inequality on an inner product space** (Federer 4.3.2(2)):
`∫⁻ t, mass ⟨T, u, t⟩ ≤ K * mass T`. -/
theorem lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t, mass (slice T u t) ≤ (K : ℝ≥0∞) * mass T := by
  obtain ⟨m, -, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hT hu
  exact (lintegral_mono hm_le).trans hm_int

/-- **Local Lipschitz slicing inequality** on an open subset `U ≤ Ω` of a normed space. -/
theorem lintegral_localMass_slice_le_of_lipschitzOnWith {U : Opens E} (hU : U ≤ Ω)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u U) (huΩ : Measurable fun x : Ω => u x) :
    ∫⁻ t, localMass (slice T u t) U ≤ (k + 1 : ℝ≥0∞) * (K : ℝ≥0∞) * localMass T U := by
  have heq (t : ℝ) : localMass (slice T u t) U =
      mass (slice (T ∘L (monoCLM ℝ : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) u t) := by
    rw [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU huΩ t]
  simp_rw [heq, ← mass_comp_monoCLM hU (f := T)]
  exact lintegral_mass_slice_le_of_lipschitzOnWith hT.comp_monoCLM hu

/-- **Sharp local Lipschitz slicing inequality** on an open subset `U ≤ Ω` of an inner product
space: `∫⁻ t, localMass ⟨T, u, t⟩ U ≤ K * localMass T U`. -/
theorem lintegral_localMass_slice_le_of_lipschitzOnWith_of_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω U : Opens E} (hU : U ≤ Ω) {u : E → ℝ}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith K u U) (huΩ : Measurable fun x : Ω => u x) :
    ∫⁻ t : ℝ, localMass (slice T u t) U ≤ (K : ℝ≥0∞) * localMass T U := by
  have heq (t : ℝ) : localMass (slice T u t) U =
      mass (slice (T ∘L (monoCLM ℝ : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) u t) := by
    rw [← mass_comp_monoCLM hU, ← coe_comp, slice_comp_monoCLM hT hU huΩ t]
  simp_rw [heq, ← mass_comp_monoCLM hU (f := T)]
  exact lintegral_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hT.comp_monoCLM hu

/-! ### Almost-everywhere normality and local normality of slices -/

/-- For a locally normal current `T` of finite mass and `u` Lipschitz on `Ω`,
`mass ⟨T, u, t⟩ < ⊤` for Lebesgue-a.e. `t ∈ ℝ`. -/
theorem ae_mass_slice_lt_top_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hmass : mass T ≠ ⊤) (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ, mass (slice T u t) < ⊤ := by
  obtain ⟨m, hm_meas, hm_le, hm_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith hT hu
  have hfin : ∫⁻ t, m t ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hm_int
  filter_upwards [ae_lt_top hm_meas hfin] with t ht
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
    have hbd : mass (T ∘L extDerivCLM) ≠ ⊤ := (isNormal_succ_iff.1 hT).2
    filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT.mass_ne_top hu,
      ae_mass_slice_lt_top_of_lipschitzOnWith hT.comp_extDerivCLM.isLocallyNormal hbd hu]
      with t ht1 ht2
    rw [isNormal_succ_iff]
    refine ⟨ht1.ne, ?_⟩
    rw [slice_comp_extDerivCLM T u t, FunLike.coe_neg, mass_neg]
    exact ht2.ne

/-- **Sublevel restrictions `T ⌞ {u < t}` of a normal current are normal almost everywhere.** -/
theorem ae_isNormal_massRestrict_lt_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K u Ω) :
    ∀ᵐ t : ℝ,
      IsNormal (massRestrict T (measurableSet_lt hu.continuousOn.domRestrict.measurable
        (measurable_const (a := t)))) := by
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  obtain ⟨hT1, hT2⟩ := isNormal_succ_iff.1 hT
  filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT1 hu] with t ht
  let hA := measurableSet_lt hu_meas (measurable_const (a := t))
  rw [isNormal_succ_iff]
  have h1 : mass (massRestrict T hA) ≠ ⊤ :=
    ne_top_of_le_ne_top hT1
      ((mass_massRestrict_le hA).trans ((measure_mono (subset_univ _)).trans_eq
        (massMeasure_univ (hasLocallyFiniteMass_of_mass_ne_top T hT1))))
  have h2_rest : mass (massRestrict (T ∘L extDerivCLM) hA) ≠ ⊤ :=
    ne_top_of_le_ne_top hT2
      ((mass_massRestrict_le hA).trans ((measure_mono (subset_univ _)).trans_eq
        (massMeasure_univ (hasLocallyFiniteMass_of_mass_ne_top _ hT2))))
  have hdecomp : massRestrict T hA ∘L extDerivCLM =
      slice T u t + massRestrict (T ∘L extDerivCLM) hA := by
    ext φ
    simp [slice_apply _ hu_meas]
  refine ⟨h1, ?_⟩
  change mass (⇑(massRestrict T hA ∘L extDerivCLM)) ≠ ⊤
  rw [hdecomp, FunLike.coe_add]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ht.ne, h2_rest⟩) mass_add_le

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
  have hC_cpt (n : ℕ) : IsCompact (C n) := (Kex.isCompact (n + 1)).image continuous_subtype_val
  have hC_sub (n : ℕ) : C n ⊆ Ω := Subtype.coe_image_subset _ _
  let W (n : ℕ) : Opens E :=
    ⟨(↑) '' interior (Kex (n + 1)), Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior⟩
  have hW_sub_C (n : ℕ) : (W n : Set E) ⊆ C n := image_mono interior_subset
  have hW_le (n : ℕ) : W n ≤ Ω := (hW_sub_C n).trans (hC_sub n)
  have hLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzOnWith L u (W n) := by
    obtain ⟨L, hL⟩ := (hu.mono (hC_sub n)).exists_lipschitzOnWith_of_compact (hC_cpt n)
    exact ⟨L, hL.mono (hW_sub_C n)⟩
  choose L hL using hLip
  have hTW_mass (n : ℕ) :
      mass (T ∘L (monoCLM ℝ : 𝓓(W n, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) ≠ ⊤ := by
    rw [coe_comp, mass_comp_monoCLM (hW_le n)]
    exact ne_top_of_le_ne_top
      ((hasLocallyFiniteMass_iff_localMass_ne_top T).1 hT.hasLocallyFiniteMass
        (C n) (hC_cpt n) (hC_sub n))
      (localMass_mono (hW_sub_C n))
  have hae_all : ∀ᵐ t : ℝ, ∀ n : ℕ,
      mass (slice (T ∘L (monoCLM ℝ : 𝓓(W n, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) u t) < ⊤ :=
    ae_all_iff.2 fun n =>
      ae_mass_slice_lt_top_of_lipschitzOnWith hT.comp_monoCLM (hTW_mass n) (hL n)
  filter_upwards [hae_all] with t ht
  rw [hasLocallyFiniteMass_iff_localMass_ne_top]
  intro K₀ hK₀ hK₀Ω
  let K₀' : Set Ω := (↑) ⁻¹' K₀
  have hK₀'_cpt : IsCompact K₀' :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK₀
      (by rwa [Subtype.range_coe])
  obtain ⟨n, hn⟩ := Kex.exists_superset_of_isCompact hK₀'_cpt
  have hK₀_sub_W : K₀ ⊆ (W n : Set E) := fun x hx =>
    ⟨⟨x, hK₀Ω hx⟩, Kex.subset_interior_succ n (hn hx), rfl⟩
  refine ne_top_of_le_ne_top ?_ (localMass_mono hK₀_sub_W)
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
    have hbd : IsLocallyNormal (T ∘L extDerivCLM) := by
      rw [isLocallyNormal_succ_iff]
      exact ⟨(isLocallyNormal_succ_iff.1 hT).2,
        by simp [comp_assoc, extDerivCLM_comp_extDerivCLM, hasLocallyFiniteMass_zero]⟩
    filter_upwards [ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hT hu,
      ae_hasLocallyFiniteMass_slice_of_locallyLipschitzOn hbd hu] with t ht1 ht2
    rw [isLocallyNormal_succ_iff]
    refine ⟨ht1, ?_⟩
    rw [slice_comp_extDerivCLM T u t]
    exact ht2.neg

/-! ### Normal flat continuity and flat-mass slicing bounds -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem measurable_measure_sdiff_sublevel (μ : Measure Ω) [SigmaFinite μ]
    (hu : Measurable fun x : Ω => u x) (hv : Measurable fun x : Ω => v x) :
    Measurable (fun t : ℝ => μ ({x : Ω | v x < t} \ {x : Ω | u x < t})) := by
  let P : Set (ℝ × Ω) := {p | v p.2 < p.1 ∧ p.1 ≤ u p.2}
  have hP : MeasurableSet P :=
    (measurableSet_lt (hv.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst (hu.comp measurable_snd))
  have hsec : (fun t : ℝ => μ ({x : Ω | v x < t} \ {x : Ω | u x < t})) =
      fun t => ∫⁻ x : Ω, P.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x) ∂μ := by
    ext t
    have hset : {x : Ω | v x < t} \ {x : Ω | u x < t} = Prod.mk t ⁻¹' P := by
      ext x
      simp [P, not_lt]
    rw [hset, ← lintegral_indicator_one (hP.preimage (measurable_prodMk_left (x := t)))]
    refine lintegral_congr fun x => ?_
    by_cases hx : (t, x) ∈ P <;> simp [hx]
  rw [hsec]
  exact (measurable_const.indicator hP).lintegral_prod_right'

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Integrating `μ({v < t ≤ u}) + μ({u < t ≤ v})` over `t ∈ ℝ` equals `∫⁻ x, edist (v x) (u x) ∂μ`
for any σ-finite measure `μ` on `Ω`. -/
private theorem lintegral_measure_symmDiff_sublevel_eq (μ : Measure Ω) [SigmaFinite μ]
    (hu : Measurable fun x : Ω => u x) (hv : Measurable fun x : Ω => v x) :
    ∫⁻ t : ℝ, (μ ({x : Ω | v x < t} \ {x : Ω | u x < t}) +
        μ ({x : Ω | u x < t} \ {x : Ω | v x < t})) =
      ∫⁻ x : Ω, edist (v x) (u x) ∂μ := by
  let P₁ : Set (ℝ × Ω) := {p | v p.2 < p.1 ∧ p.1 ≤ u p.2}
  let P₂ : Set (ℝ × Ω) := {p | u p.2 < p.1 ∧ p.1 ≤ v p.2}
  have hP₁ : MeasurableSet P₁ :=
    (measurableSet_lt (hv.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst (hu.comp measurable_snd))
  have hP₂ : MeasurableSet P₂ :=
    (measurableSet_lt (hu.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst (hv.comp measurable_snd))
  have hsec₁ (t : ℝ) :
      μ ({x : Ω | v x < t} \ {x : Ω | u x < t}) =
        ∫⁻ x : Ω, P₁.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x) ∂μ := by
    have hset : {x : Ω | v x < t} \ {x : Ω | u x < t} = Prod.mk t ⁻¹' P₁ := by
      ext x
      simp [P₁, not_lt]
    rw [hset, ← lintegral_indicator_one (hP₁.preimage (measurable_prodMk_left (x := t)))]
    refine lintegral_congr fun x => ?_
    by_cases hx : (t, x) ∈ P₁ <;> simp [hx]
  have hsec₂ (t : ℝ) :
      μ ({x : Ω | u x < t} \ {x : Ω | v x < t}) =
        ∫⁻ x : Ω, P₂.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x) ∂μ := by
    have hset : {x : Ω | u x < t} \ {x : Ω | v x < t} = Prod.mk t ⁻¹' P₂ := by
      ext x
      simp [P₂, not_lt]
    rw [hset, ← lintegral_indicator_one (hP₂.preimage (measurable_prodMk_left (x := t)))]
    refine lintegral_congr fun x => ?_
    by_cases hx : (t, x) ∈ P₂ <;> simp [hx]
  have hx₁ (x : Ω) : (∫⁻ t : ℝ, P₁.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x)) =
      ENNReal.ofReal (u x - v x) := by
    have hset : (fun t : ℝ => P₁.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x)) =
        (Ioc (v x) (u x)).indicator 1 := by
      ext t
      by_cases ht : v x < t ∧ t ≤ u x <;> simp [P₁, ht]
    rw [hset, lintegral_indicator_one measurableSet_Ioc, Real.volume_Ioc]
  have hx₂ (x : Ω) : (∫⁻ t : ℝ, P₂.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x)) =
      ENNReal.ofReal (v x - u x) := by
    have hset : (fun t : ℝ => P₂.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x)) =
        (Ioc (u x) (v x)).indicator 1 := by
      ext t
      by_cases ht : u x < t ∧ t ≤ v x <;> simp [P₂, ht]
    rw [hset, lintegral_indicator_one measurableSet_Ioc, Real.volume_Ioc]
  rw [lintegral_add_left (measurable_measure_sdiff_sublevel μ hu hv)]
  simp_rw [hsec₁, hsec₂]
  rw [lintegral_lintegral_swap (f := fun t x => P₁.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x))
      (measurable_const.indicator hP₁).aemeasurable,
    lintegral_lintegral_swap (f := fun t x => P₂.indicator (1 : ℝ × Ω → ℝ≥0∞) (t, x))
      (measurable_const.indicator hP₂).aemeasurable]
  simp_rw [hx₁, hx₂]
  have hmeas_uv : Measurable fun y : Ω => ENNReal.ofReal (u y - v y) :=
    (hu.sub hv).ennreal_ofReal
  rw [← lintegral_add_left hmeas_uv]
  refine lintegral_congr fun x => ?_
  rw [edist_dist, Real.dist_eq]
  rcases le_total (v x) (u x) with hle | hle
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hle), add_zero,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hle), zero_add,
      abs_of_nonneg (sub_nonneg.2 hle)]

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
  have hmass_diff {m : ℕ} (Q : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) (t : ℝ) :
      mass (massRestrict Q (hAv t) - massRestrict Q (hAu t)) ≤
        massMeasure Q (Av t \ Au t) + massMeasure Q (Au t \ Av t) := by
    have hAv_eq : Av t = (Av t ∩ Au t) ∪ (Av t \ Au t) := (inter_union_sdiff _ _).symm
    have hAu_eq : Au t = (Av t ∩ Au t) ∪ (Au t \ Av t) := by
      rw [inter_comm]
      exact (inter_union_sdiff _ _).symm
    have h1 := massRestrict_union (T := Q) ((hAv t).inter (hAu t)) ((hAv t).diff (hAu t))
      disjoint_inf_sdiff
    have h2 := massRestrict_union (T := Q) ((hAv t).inter (hAu t)) ((hAu t).diff (hAv t))
      (disjoint_sdiff_self_right.mono_left inter_subset_left)
    have hdiff : massRestrict Q (hAv t) - massRestrict Q (hAu t) =
        massRestrict Q ((hAv t).diff (hAu t)) - massRestrict Q ((hAu t).diff (hAv t)) := by
      rw [massRestrict_congr_set Q (hAv t)
          (((hAv t).inter (hAu t)).union ((hAv t).diff (hAu t))) hAv_eq,
        massRestrict_congr_set Q (hAu t)
          (((hAv t).inter (hAu t)).union ((hAu t).diff (hAv t))) hAu_eq,
        h1, h2, add_sub_add_left_eq_sub]
    rw [hdiff]
    exact mass_sub_le.trans
      (add_le_add (mass_massRestrict_le ((hAv t).diff (hAu t)))
        (mass_massRestrict_le ((hAu t).diff (hAv t))))
  have hae_bound : ∀ᵐ t : ℝ, (slice T v t - slice T u t).normalFlatMass ≤
      (massMeasure (T ∘L extDerivCLM) (Av t \ Au t) +
        massMeasure (T ∘L extDerivCLM) (Au t \ Av t)) +
      (massMeasure T (Av t \ Au t) + massMeasure T (Au t \ Av t)) := by
    filter_upwards [ae_isNormal_massRestrict_lt_of_lipschitzOnWith hT hu,
      ae_isNormal_massRestrict_lt_of_lipschitzOnWith hT hv,
      ae_isNormal_slice_of_lipschitzOnWith hT hu,
      ae_isNormal_slice_of_lipschitzOnWith hT hv] with t hNu_r hNv_r hNu_s hNv_s
    let St := massRestrict T (hAv t) - massRestrict T (hAu t)
    let Rt := -(massRestrict (T ∘L extDerivCLM) (hAv t) - massRestrict (T ∘L extDerivCLM) (hAu t))
    have hSt : IsNormal St := hNv_r.sub hNu_r
    have hdecomp : slice T v t - slice T u t = Rt + St ∘L extDerivCLM := by
      ext φ
      simp [St, Rt, slice_apply _ hu_meas, slice_apply _ hv_meas]
      ring
    have hRt_eq : Rt = (slice T v t - slice T u t) - St ∘L extDerivCLM := by
      rw [hdecomp]
      abel
    have hRt : IsNormal Rt := hRt_eq ▸ (hNv_s.sub hNu_s).sub hSt.comp_extDerivCLM
    refine ((slice T v t - slice T u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM
      hRt hSt hdecomp).trans ?_
    rw [FunLike.coe_neg, mass_neg]
    exact add_le_add (hmass_diff (T ∘L extDerivCLM) t) (hmass_diff T t)
  refine (lintegral_mono_ae hae_bound).trans ?_
  have h1 := lintegral_measure_symmDiff_sublevel_eq (massMeasure (T ∘L extDerivCLM)) hu_meas hv_meas
  have h2 := lintegral_measure_symmDiff_sublevel_eq (massMeasure T) hu_meas hv_meas
  have hmeas_bd : Measurable (fun t : ℝ =>
      massMeasure (T ∘L extDerivCLM) (Av t \ Au t) +
        massMeasure (T ∘L extDerivCLM) (Au t \ Av t)) :=
    (measurable_measure_sdiff_sublevel (massMeasure (T ∘L extDerivCLM)) hu_meas hv_meas).add
      (measurable_measure_sdiff_sublevel (massMeasure (T ∘L extDerivCLM)) hv_meas hu_meas)
  rw [lintegral_add_left hmeas_bd, h1, h2, add_comm, ← lintegral_add_measure]

/-- Slicing by a `0`-Lipschitz function on `Ω` vanishes for every locally normal current. -/
private theorem slice_eq_zero_of_lipschitzOnWith_zero
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hu : LipschitzOnWith 0 u Ω) (t : ℝ) :
    slice T u t = 0 := by
  obtain ⟨hT1, hT2⟩ := isLocallyNormal_succ_iff.1 hT
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  let A : Set Ω := {x : Ω | u x < t}
  have hA : MeasurableSet A := measurableSet_lt hu_meas measurable_const
  cases isEmpty_or_nonempty Ω with
  | inl hE =>
    ext φ
    have hφ0 : φ = 0 := DFunLike.ext _ _ fun z => by
      by_cases hz : z ∈ Ω
      · exact (hE.false ⟨z, hz⟩).elim
      · simpa using image_eq_zero_of_notMem_tsupport (f := φ) fun h => hz (φ.tsupport_subset h)
    simp [hφ0]
  | inr hne =>
    let x₀ : Ω := hne.some
    have hconst (x : Ω) : u x = u x₀ := by
      have hd := hu.dist_le_mul x.1 x.2 x₀.1 x₀.2
      simp only [NNReal.coe_zero, zero_mul, dist_le_zero] at hd
      exact hd
    by_cases hlt : u x₀ < t
    · have hA_univ : A = univ := eq_univ_of_forall fun x => by simpa [A, hconst x] using hlt
      ext φ
      rw [slice_apply _ hu_meas, zero_apply]
      have h1 : massRestrict T hA (extDerivCLM φ) = T (extDerivCLM φ) := by
        rw [massRestrict_congr_set T hA MeasurableSet.univ hA_univ, massRestrict_univ_apply hT1]
      have h2 : massRestrict (T ∘L extDerivCLM) hA φ = T (extDerivCLM φ) := by
        rw [massRestrict_congr_set (T ∘L extDerivCLM) hA MeasurableSet.univ hA_univ,
          massRestrict_univ_apply hT2, comp_apply]
      rw [h1, h2, sub_self]
    · have hA_empty : A = ∅ := eq_empty_of_forall_notMem fun x hx =>
        hlt (by simpa [A, hconst x] using hx)
      ext φ
      rw [slice_apply _ hu_meas]
      have h1 : massRestrict T hA = 0 := by
        rw [massRestrict_congr_set T hA MeasurableSet.empty hA_empty]
        exact massRestrict_eq_zero MeasurableSet.empty (by simp)
      have h2 : massRestrict (T ∘L extDerivCLM) hA = 0 := by
        rw [massRestrict_congr_set (T ∘L extDerivCLM) hA MeasurableSet.empty hA_empty]
        exact massRestrict_eq_zero MeasurableSet.empty (by simp)
      simp [h1, h2]

/-- **Sharp flat-mass slicing inequality on an inner product space** (Federer 4.3.2(2)):
for a real normal `(k + 1)`-current `N` and `u` that is `K`-Lipschitz on `Ω`,
`∫⁻ t, F(⟨N, u, t⟩) ≤ K * F(N)`. -/
theorem lintegral_normalFlatMass_slice_le_of_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hN : IsNormal N)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤ (K : ℝ≥0∞) * N.normalFlatMass := by
  by_cases hK : K = 0
  · subst hK
    simp [slice_eq_zero_of_lipschitzOnWith_zero hN.isLocallyNormal hu]
  have hK' : (K : ℝ≥0∞) ≠ 0 := by positivity
  rw [normalFlatMass_def]
  simp_rw [ENNReal.mul_iInf_of_ne hK' ENNReal.coe_ne_top]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  let R := N - S ∘L extDerivCLM
  have hN_eq : N = R + S ∘L extDerivCLM := by simp [R]
  obtain ⟨mR, hmR_meas, hmR_le, hmR_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
      hR.isLocallyNormal hu
  obtain ⟨mS, -, hmS_le, hmS_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace
      hS.isLocallyNormal hu
  have hae : ∀ᵐ t : ℝ, (slice N u t).normalFlatMass ≤ mR t + mS t := by
    filter_upwards [ae_isNormal_slice_of_lipschitzOnWith hR hu,
      ae_isNormal_slice_of_lipschitzOnWith hS hu] with t hNR hNS
    have hslice_eq : slice N u t = slice R u t + (-slice S u t) ∘L extDerivCLM := by
      rw [neg_comp, slice_comp_extDerivCLM S u t, neg_neg,
        ← slice_add hR.isLocallyNormal hS.comp_extDerivCLM.isLocallyNormal, ← hN_eq]
    refine ((slice N u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM
      hNR hNS.neg hslice_eq).trans ?_
    rw [FunLike.coe_neg, mass_neg]
    exact add_le_add (hmR_le t) (hmS_le t)
  calc ∫⁻ t : ℝ, (slice N u t).normalFlatMass
      ≤ ∫⁻ t : ℝ, (mR t + mS t) := lintegral_mono_ae hae
    _ = (∫⁻ t : ℝ, mR t) + ∫⁻ t : ℝ, mS t := lintegral_add_left hmR_meas _
    _ ≤ (K : ℝ≥0∞) * mass R + (K : ℝ≥0∞) * mass S := add_le_add hmR_int hmS_int
    _ = (K : ℝ≥0∞) * (mass R + mass S) := (mul_add _ _ _).symm

/-- **Flat-mass slicing inequality** on a general normed space:
for a real normal `(k + 1)`-current `N` and `u` that is `K`-Lipschitz on `Ω`,
`∫⁻ t, F(⟨N, u, t⟩) ≤ (k + 2) * K * F(N)`. -/
theorem lintegral_normalFlatMass_slice_le
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hN : IsNormal N)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤
      (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * N.normalFlatMass := by
  by_cases hK : K = 0
  · subst hK
    simp [slice_eq_zero_of_lipschitzOnWith_zero hN.isLocallyNormal hu]
  have hc : (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) ≠ 0 :=
    mul_ne_zero (by positivity) (by positivity)
  have hctop : (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) ≠ ⊤ := by finiteness
  rw [normalFlatMass_def]
  simp_rw [ENNReal.mul_iInf_of_ne hc hctop]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  let R := N - S ∘L extDerivCLM
  have hN_eq : N = R + S ∘L extDerivCLM := by simp [R]
  obtain ⟨mR, hmR_meas, hmR_le, hmR_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith hR.isLocallyNormal hu
  obtain ⟨mS, -, hmS_le, hmS_int⟩ :=
    exists_measurable_mass_slice_le_of_lipschitzOnWith hS.isLocallyNormal hu
  have hae : ∀ᵐ t : ℝ, (slice N u t).normalFlatMass ≤ mR t + mS t := by
    filter_upwards [ae_isNormal_slice_of_lipschitzOnWith hR hu,
      ae_isNormal_slice_of_lipschitzOnWith hS hu] with t hNR hNS
    have hslice_eq : slice N u t = slice R u t + (-slice S u t) ∘L extDerivCLM := by
      rw [neg_comp, slice_comp_extDerivCLM S u t, neg_neg,
        ← slice_add hR.isLocallyNormal hS.comp_extDerivCLM.isLocallyNormal, ← hN_eq]
    refine ((slice N u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM
      hNR hNS.neg hslice_eq).trans ?_
    rw [FunLike.coe_neg, mass_neg]
    exact add_le_add (hmR_le t) (hmS_le t)
  have hk_le : (k + 1 : ℝ≥0∞) ≤ (k + 2 : ℝ≥0∞) := by
    gcongr
    norm_num
  have hmR_int' : ∫⁻ t : ℝ, mR t ≤ (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * mass R :=
    hmR_int.trans (by gcongr)
  have hmS_int' : ∫⁻ t : ℝ, mS t ≤ (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * mass S := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hmS_int
  calc ∫⁻ t : ℝ, (slice N u t).normalFlatMass
      ≤ ∫⁻ t : ℝ, (mR t + mS t) := lintegral_mono_ae hae
    _ = (∫⁻ t : ℝ, mR t) + ∫⁻ t : ℝ, mS t := lintegral_add_left hmR_meas _
    _ ≤ (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * mass R + (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * mass S :=
        add_le_add hmR_int' hmS_int'
    _ = (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * (mass R + mass S) := (mul_add _ _ _).symm

end Distribution
