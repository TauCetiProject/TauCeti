/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentCone
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Uniqueness of approximate tangent planes of rectifiable sets

A `k`-plane `P` is an approximate tangent plane of a set `E` at `x` if, for every `ε > 0`, the
part of `E ∩ closedBall x r` outside the cone `{z | infDist (z - x) P ≤ ε dist z x}` has
`k`-dimensional density zero at `x`, measured with the normalized Hausdorff measure `μHE[k]`
against the volume of a ball of `EuclideanSpace ℝ (Fin k)`. Such planes exist almost everywhere
on a countably `k`-rectifiable set
(`TauCeti.CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div`). This file
proves that they are almost everywhere unique.

At almost every point `x` of such a set `E`, the set has density one, and `x = f u₀` lies on a
bi-Lipschitz patch `f '' A` whose complement in `E` has density zero at `x`, with `f`
differentiable at `u₀` and the derivative range `D` of dimension `k`. If an approximate tangent
plane `P` differed from `D`, a vector `w` orthogonal to `P` but not to `D` would make the linear
form `ψ = ⟪w, f' u₀ ·⟫` nonzero. Points of the patch inside a narrow cone about `P` have parameters
in a thin cone `{v | |ψ v| ≤ t ‖v‖}` about the kernel of `ψ`, whose volume in the unit ball tends
to zero with `t`. Since `f` is Lipschitz and inverse-Lipschitz on `A`, the patch then carries
density less than one inside the cone, contradicting density one. Hence `P = D`.

## Main results

* `TauCeti.CountablyRectifiable.ae_eq_of_tendsto_measure_outside_cone_div`: approximate tangent
  `k`-planes of a null-measurable, countably `k`-rectifiable set with locally finite `μHE[k]`
  measure are unique at almost every point.

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 15.19.
* L. Simon, *Lectures on Geometric Measure Theory*, §11.
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal NNReal Topology RealInnerProductSpace Pointwise

namespace TauCeti

variable {k : ℕ}

/-- The cone of vectors of the closed unit ball on which a linear form is at most `t` times the
norm. -/
private noncomputable def unitFormCone (ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  closedBall 0 1 ∩ {v | |ψ v| ≤ t * ‖v‖}

/-- The thin cones about the kernel of a nonzero linear form have volume tending to zero. -/
private theorem tendsto_volume_unitFormCone {ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ} (hψ : ψ ≠ 0) :
    Tendsto (fun n : ℕ ↦ volume (unitFormCone ψ (1 / (n + 1)))) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : NullMeasurableSet (unitFormCone ψ (1 / (n + 1))) volume :=
    (isClosed_closedBall.inter (isClosed_le
      (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin k) ↦ |ψ v|)
      (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin k) ↦ 1 / ((n : ℝ) + 1) * ‖v‖)))
      |>.measurableSet.nullMeasurableSet
  have hanti : Antitone fun n : ℕ ↦ unitFormCone ψ (1 / (n + 1)) := by
    intro m n hmn
    change unitFormCone ψ _ ⊆ unitFormCone ψ _
    intro v hv
    simp only [unitFormCone, mem_inter_iff, mem_ofPred_eq] at hv ⊢
    refine ⟨hv.1, hv.2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))⟩
    gcongr
  have hfin : volume (unitFormCone ψ (1 / ((0 : ℕ) + 1))) ≠ ∞ :=
    (measure_mono (inter_subset_left : unitFormCone ψ (1 / (((0 : ℕ) : ℝ) + 1)) ⊆
      closedBall 0 1)).trans_lt measure_closedBall_lt_top |>.ne
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, hfin⟩
  set W := LinearMap.ker (ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ℝ)
  have hker : ⋂ n : ℕ, unitFormCone ψ (1 / (n + 1)) ⊆ (W : Set (EuclideanSpace ℝ (Fin k))) := by
    intro v hv
    simp only [mem_iInter] at hv
    simp only [SetLike.mem_coe, W, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) (abs_nonneg _))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp (hv n).1
    calc |ψ v| ≤ 1 / (n + 1) * ‖v‖ := (hv n).2
      _ ≤ 1 / (n + 1) * 1 := by gcongr
      _ ≤ 0 + δ := by linarith
  have hker0 : volume (W : Set (EuclideanSpace ℝ (Fin k))) = 0 := by
    refine Measure.addHaar_submodule _ _ fun htop ↦ hψ ?_
    ext v
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    simpa [W] using hv
  rwa [measure_mono_null hker hker0] at hlim

/-- Scaling the unit cone: the vectors of the closed ball of radius `R` on which `|ψ| ≤ t ‖·‖`
have volume `R ^ k` times that of the unit cone. -/
private theorem volume_formCone_closedBall (ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) (t : ℝ)
    {R : ℝ} (hR : 0 < R) :
    volume {v ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) R | |ψ v| ≤ t * ‖v‖} =
      ENNReal.ofReal (R ^ k) * volume (unitFormCone ψ t) := by
  have hset : {v ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) R | |ψ v| ≤ t * ‖v‖} =
      R • unitFormCone ψ t := by
    ext v
    rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne']
    simp only [unitFormCone, mem_inter_iff, mem_ofPred_eq, mem_closedBall_zero_iff, map_smul,
      smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hR]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [inv_mul_le_iff₀ hR]; linarith, ?_⟩
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hR.le)
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [inv_mul_le_iff₀ hR] at h1; linarith, ?_⟩
      rw [mul_left_comm] at h2
      exact le_of_mul_le_mul_left h2 (inv_pos.mpr hR)
  rw [hset, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hR k)]

/-- The vector `w` orthogonal to `P` bounds the pairing of `w` with `z` by the distance from `z`
to `P`. -/
private theorem abs_inner_le_norm_mul_infDist {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {P : Submodule ℝ V} {w : V} (hw : ∀ p ∈ P, ⟪w, p⟫ = 0) (z : V) :
    |⟪w, z⟫| ≤ ‖w‖ * infDist z (P : Set V) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [← div_le_iff₀' hpos]
  refine (le_infDist ⟨0, P.zero_mem⟩).mpr fun p hp ↦ ?_
  rw [div_le_iff₀' hpos, dist_eq_norm]
  calc |⟪w, z⟫| = |⟪w, z - p⟫| := by rw [inner_sub_right, hw p hp, sub_zero]
    _ ≤ ‖w‖ * ‖z - p‖ := abs_real_inner_le_norm w (z - p)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The approximate tangent plane on a patch.** Let `f` be Lipschitz, inverse-Lipschitz on `A`,
and differentiable at `u₀ ∈ A` with derivative range of dimension `k`. If a set `E` has density one
at `x = f u₀` and `E \ f '' A` has density zero there, then every approximate tangent `k`-plane of
`E` at `x` is the derivative range. -/
private theorem eq_range_fderiv_of_tendsto_measure_outside_cone_div
    {f : EuclideanSpace ℝ (Fin k) → V} {A : Set (EuclideanSpace ℝ (Fin k))} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hA : AntilipschitzWith L (A.domRestrict f))
    {u₀ : EuclideanSpace ℝ (Fin k)} (hu₀ : u₀ ∈ A) (hd : DifferentiableAt ℝ f u₀)
    (hrange : Module.finrank ℝ (fderiv ℝ f u₀).range = k) {E : Set V}
    (hE1 : Tendsto (fun r ↦ μHE[k] (E ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1))
    (hE0 : Tendsto (fun r ↦ μHE[k] ((E \ f '' A) ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
    {P : Submodule ℝ V} (hPk : Module.finrank ℝ P = k)
    (hP : ∀ ε > (0 : ℝ), Tendsto (fun r ↦
      μHE[k] {z ∈ E ∩ closedBall (f u₀) r | ε * dist z (f u₀) < infDist (z - f u₀) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    P = (fderiv ℝ f u₀).range := by
  set D := fderiv ℝ f u₀
  set x := f u₀
  by_contra hne
  -- A vector orthogonal to `P` but not to the derivative range.
  have hnle : ¬ (D.range ≤ P) := fun hle ↦
    hne (Submodule.eq_of_le_of_finrank_eq hle (hrange.trans hPk.symm)).symm
  obtain ⟨y, ⟨v₀, rfl⟩, hy⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  set w := D v₀ - P.starProjection (D v₀)
  have hwP : ∀ p ∈ P, ⟪w, p⟫ = 0 := fun p hp ↦ by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hp (P.sub_starProjection_mem_orthogonal _)
  have hw0 : w ≠ 0 := fun h ↦ by
    rw [sub_eq_zero] at h
    have hmem : D v₀ ∈ P := by rw [h]; exact P.starProjection_apply_mem _
    exact hy hmem
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := (innerSL ℝ w).comp D
  have hψ : ψ ≠ 0 := by
    intro h
    have h1 : ⟪w, D v₀⟫ = 0 := by
      simpa [ψ] using congrArg (fun φ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ ↦ φ v₀) h
    have h2 : ⟪w, D v₀⟫ = ⟪w, w⟫ := by
      have : D v₀ = w + P.starProjection (D v₀) := (sub_add_cancel _ _).symm
      rw [this, inner_add_right, hwP _ (P.starProjection_apply_mem _), add_zero]
    exact hw0 (inner_self_eq_zero.mp (h2 ▸ h1))
  -- The constant `a` with `μHE[k] (patch part) ≤ a r ^ k vol (cone)`.
  set a : ℝ≥0∞ := (K : ℝ≥0∞) ^ k * ENNReal.ofReal (((L : ℝ) + 1) ^ k) with ha
  have ha_top : a ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    ENNReal.ofReal_ne_top
  set B₁ := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)
  have hB₁0 : B₁ ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hB₁top : B₁ ≠ ∞ := measure_ball_lt_top.ne
  -- Choose the thickness `t` of the parameter cone so that its share is below one.
  have hlt : a * 0 < B₁ := by rw [mul_zero]; exact pos_iff_ne_zero.mpr hB₁0
  obtain ⟨n, hn⟩ := ((ENNReal.Tendsto.const_mul (tendsto_volume_unitFormCone hψ)
    (Or.inr ha_top)).eventually (gt_mem_nhds hlt)).exists
  set t : ℝ := 1 / (n + 1)
  have ht : 0 < t := by positivity
  set m : ℝ≥0∞ := a * volume (unitFormCone ψ t) / B₁
  have hm : m < 1 := (ENNReal.div_lt_iff (Or.inl hB₁0) (Or.inl hB₁top)).mpr (by simpa using hn)
  -- Choose the cone aperture `ε` and the differentiability error `η`.
  set ε : ℝ := t / (2 * ‖w‖ * ((K : ℝ) + 1))
  have hε : 0 < ε := by positivity
  set η : ℝ := t / (2 * ‖w‖)
  have hη : 0 < η := by positivity
  have hεη : ‖w‖ * (ε * K + η) ≤ t := by
    have hK : (K : ℝ) / ((K : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have : ‖w‖ * (ε * K + η) = t / 2 * ((K : ℝ) / ((K : ℝ) + 1)) + t / 2 := by
      simp only [ε, η]
      field_simp
    rw [this]
    nlinarith
  obtain ⟨ρ, hρ, hρd⟩ := Metric.eventually_nhds_iff.mp (hd.hasFDerivAt.isLittleO.def hη)
  -- For small radii, `E ∩ closedBall x r` is covered by three controlled pieces.
  set S : ℝ → Set (EuclideanSpace ℝ (Fin k)) := fun r ↦
    {v ∈ closedBall 0 (((L : ℝ) + 1) * r) | |ψ v| ≤ t * ‖v‖}
  have hcover : ∀ r, 0 < r → ((L : ℝ) + 1) * r < ρ →
      E ∩ closedBall x r ⊆ {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} ∪
        ((E \ f '' A) ∩ closedBall x r) ∪ f '' (A ∩ (fun u ↦ u - u₀) ⁻¹' S r) := by
    intro r hr hrρ z hz
    by_cases hout : ε * dist z x < infDist (z - x) (P : Set V)
    · exact Or.inl (Or.inl ⟨hz, hout⟩)
    by_cases hzA : z ∈ f '' A
    swap
    · exact Or.inl (Or.inr ⟨⟨hz.1, hzA⟩, hz.2⟩)
    obtain ⟨u, hu, rfl⟩ := hzA
    refine Or.inr ⟨u, ⟨hu, ?_⟩, rfl⟩
    have hdist : ‖u - u₀‖ ≤ ((L : ℝ) + 1) * r := by
      have h1 := hA.le_mul_dist ⟨u, hu⟩ ⟨u₀, hu₀⟩
      simp only [Subtype.dist_eq, domRestrict_apply] at h1
      rw [← dist_eq_norm]
      calc dist u u₀ ≤ L * dist (f u) x := h1
        _ ≤ L * r := by gcongr; exact mem_closedBall.mp hz.2
        _ ≤ ((L : ℝ) + 1) * r := by nlinarith
    refine ⟨mem_closedBall_zero_iff.mpr hdist, ?_⟩
    have hsmall : dist u u₀ < ρ := by rw [dist_eq_norm]; linarith
    have hlin : ‖f u - f u₀ - D (u - u₀)‖ ≤ η * ‖u - u₀‖ := hρd hsmall
    have hcone : |⟪w, f u - x⟫| ≤ ‖w‖ * (ε * dist (f u) x) :=
      (abs_inner_le_norm_mul_infDist hwP _).trans
        (mul_le_mul_of_nonneg_left (not_lt.mp hout) (norm_nonneg w))
    have hLip : dist (f u) x ≤ K * ‖u - u₀‖ := by
      rw [← dist_eq_norm]; exact hf.dist_le_mul u u₀
    have hψu : ψ (u - u₀) = ⟪w, f u - x⟫ - ⟪w, f u - f u₀ - D (u - u₀)⟫ := by
      simp only [ψ, ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sub_right, x]
      ring
    calc |ψ (u - u₀)| ≤ |⟪w, f u - x⟫| + |⟪w, f u - f u₀ - D (u - u₀)⟫| := by
          rw [hψu]; exact abs_sub _ _
      _ ≤ ‖w‖ * (ε * (K * ‖u - u₀‖)) + ‖w‖ * (η * ‖u - u₀‖) := by
          gcongr
          · exact hcone.trans (by gcongr)
          · exact (abs_real_inner_le_norm _ _).trans (by gcongr)
      _ = ‖w‖ * (ε * K + η) * ‖u - u₀‖ := by ring
      _ ≤ t * ‖u - u₀‖ := by gcongr
  -- The patch part has density at most `m`.
  have hpatch : ∀ r, 0 < r → μHE[k] (f '' (A ∩ (fun u ↦ u - u₀) ⁻¹' S r)) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤ m := by
    intro r hr
    have hR : 0 < ((L : ℝ) + 1) * r := by positivity
    have himage := (hf.lipschitzOnWith (s := A ∩ (fun u ↦ u - u₀) ⁻¹' S r)
      ).euclideanHausdorffMeasure_image_le k
    have hvol : μHE[k] (A ∩ (fun u ↦ u - u₀) ⁻¹' S r) ≤
        ENNReal.ofReal ((((L : ℝ) + 1) * r) ^ k) * volume (unitFormCone ψ t) := by
      have hμ : (μHE[k] : Measure (EuclideanSpace ℝ (Fin k))) = volume :=
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume k
      rw [hμ, ← volume_formCone_closedBall ψ t hR]
      refine (measure_mono inter_subset_right).trans_eq ?_
      simp only [sub_eq_add_neg]
      exact measure_preimage_add_right _ _ _
    rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin]
    calc μHE[k] (f '' (A ∩ (fun u ↦ u - u₀) ⁻¹' S r)) /
          (ENNReal.ofReal (r ^ k) * B₁)
        ≤ (K : ℝ≥0∞) ^ k * (ENNReal.ofReal ((((L : ℝ) + 1) * r) ^ k) *
            volume (unitFormCone ψ t)) / (ENNReal.ofReal (r ^ k) * B₁) := by
          gcongr
          exact himage.trans (by gcongr)
      _ = ENNReal.ofReal (r ^ k) * (a * volume (unitFormCone ψ t)) /
            (ENNReal.ofReal (r ^ k) * B₁) := by
          rw [mul_pow, ENNReal.ofReal_mul (by positivity), ha]
          congr 1
          ac_rfl
      _ = m := ENNReal.mul_div_mul_left _ _
            (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
  -- Passing to the limit gives `1 ≤ 0 + 0 + m`, contradicting `m < 1`.
  have hlim : (1 : ℝ≥0∞) ≤ 0 + 0 + m := by
    refine le_of_tendsto_of_tendsto hE1 (((hP ε hε).add hE0).add tendsto_const_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show (0 : ℝ) < ρ / ((L : ℝ) + 1) by positivity))] with r hr hrρ
    have hrρ' : ((L : ℝ) + 1) * r < ρ := by
      rwa [lt_div_iff₀' (by positivity)] at hrρ
    calc μHE[k] (E ∩ closedBall x r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
        ≤ (μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} +
            μHE[k] ((E \ f '' A) ∩ closedBall x r) +
            μHE[k] (f '' (A ∩ (fun u ↦ u - u₀) ⁻¹' S r))) /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
          gcongr
          exact (measure_mono (hcover r hr hrρ')).trans
            ((measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _))
      _ = μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
            μHE[k] ((E \ f '' A) ∩ closedBall x r) /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
            μHE[k] (f '' (A ∩ (fun u ↦ u - u₀) ⁻¹' S r)) /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
          rw [ENNReal.add_div, ENNReal.add_div]
      _ ≤ _ := by
          gcongr
          exact hpatch r hr
  simp only [zero_add] at hlim
  exact absurd hm (not_lt.mpr hlim)

/-- **Uniqueness of approximate tangent planes.** At almost every point of a null-measurable,
countably `k`-rectifiable set with locally finite `μHE[k]` measure, any two `k`-planes outside
every cone about which the set has density zero are equal. Together with
`CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div`, the set has a unique
approximate tangent plane almost everywhere. -/
theorem CountablyRectifiable.ae_eq_of_tendsto_measure_outside_cone_div {E : Set V}
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∀ P Q : Submodule ℝ V,
      Module.finrank ℝ P = k → Module.finrank ℝ Q = k →
      (∀ ε > (0 : ℝ), Tendsto (fun r ↦
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) →
      (∀ ε > (0 : ℝ), Tendsto (fun r ↦
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) →
      P = Q := by
  obtain ⟨A, f, hAm, hbi, hcover⟩ := hE.exists_bilipschitz_cover
  choose K L hLip hAnti using hbi
  have hgood (n : ℕ) := (hLip n).ae_exists_fderiv_range_forall_infDist_le (hAnti n)
  simp only [finrank_euclideanSpace_fin] at hgood
  have himm (n : ℕ) : MeasurableSet (f n '' A n) :=
    (hAm n).image_of_continuousOn_injOn (hLip n).continuous.continuousOn
      (injOn_iff_injective.mpr (hAnti n).injective)
  have hzero (n : ℕ) : ∀ᵐ x ∂μHE[k], x ∉ E \ f n '' A n → Tendsto (fun r ↦
      μHE[k] ((E \ f n '' A n) ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ f n '' A n)) := by
      rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict (himm n).compl]
      infer_instance
    exact ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure k
      (hEm.diff (himm n).nullMeasurableSet)
  filter_upwards [ae_le_set.mpr hcover, ae_all_iff.mpr hgood, ae_all_iff.mpr hzero,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm]
    with x hcov hgood hzero hone hxE P Q hP hQ hPc hQc
  obtain ⟨n, hxn⟩ := mem_iUnion.mp (hcov hxE)
  obtain ⟨u, hu, rfl, hrange, -⟩ := hgood n hxn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Submodule.finrank_eq_zero.mp hP, Submodule.finrank_eq_zero.mp hQ]
  have hd : DifferentiableAt ℝ (f n) u := by
    by_contra hnd
    have h0 : LinearMap.range (fderiv ℝ (f n) u : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] V) = ⊥ := by
      rw [fderiv_zero_of_not_differentiableAt hnd, ContinuousLinearMap.toLinearMap_zero,
        LinearMap.range_zero]
    have hbot : Module.finrank ℝ (⊥ : Submodule ℝ V) = k := h0 ▸ hrange
    rw [finrank_bot] at hbot
    omega
  have h0 := hzero n fun h ↦ h.2 hxn
  have hone' := hone hxE
  rw [eq_range_fderiv_of_tendsto_measure_outside_cone_div (hLip n) (hAnti n) hu hd hrange hone' h0
      hP hPc,
    eq_range_fderiv_of_tendsto_measure_outside_cone_div (hLip n) (hAnti n) hu hd hrange hone' h0
      hQ hQc]

end TauCeti
