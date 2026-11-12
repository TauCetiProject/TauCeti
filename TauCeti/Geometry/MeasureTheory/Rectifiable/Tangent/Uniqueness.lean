/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Cone
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Uniqueness of approximate tangent planes of rectifiable sets

A `k`-plane `P` is an approximate tangent plane of a set `E` at `x` if, for every `ε > 0`, the
part of `E ∩ closedBall x r` outside the cone `{z | infDist (z - x) P ≤ ε dist z x}` has
`k`-dimensional density zero at `x`, measured with the normalized Hausdorff measure `μHE[k]`
against the volume of a ball of `EuclideanSpace ℝ (Fin k)`. Let `E` be a countably
`k`-rectifiable set that is `μHE[k]`-null-measurable and whose restricted measure
`μHE[k].restrict E` is locally finite. Approximate tangent `k`-planes of such a set exist almost
everywhere on it
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

* `LipschitzWith.eq_range_fderiv_of_tendsto_measure_outside_cone_div`: on a bi-Lipschitz patch
  `f '' A`, at a point `f u₀` where `E` has density one and `E \ f '' A` has density zero, every
  approximate tangent `k`-plane of `E` is the range of the derivative of `f` at `u₀`.
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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Near `f u₀`, a set `E` is covered by its part outside a cone of aperture `ε` about `P`, its
part off the patch `f '' A`, and the image of the parameters `u ∈ A` with `u - u₀` in a thin cone
`|⟪w, f' u₀ (u - u₀)⟫| ≤ t ‖u - u₀‖`, where `w ⊥ P`. This holds at radii `r` whose parameter
radius `(L + 1) r` is within the radius `ρ` on which `f` is `η`-close to its linearization. -/
private theorem subset_union_image_of_forall_dist_lt
    {f : EuclideanSpace ℝ (Fin k) → V} {A : Set (EuclideanSpace ℝ (Fin k))} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hA : AntilipschitzWith L (A.domRestrict f))
    {u₀ : EuclideanSpace ℝ (Fin k)} (hu₀ : u₀ ∈ A) {P : Submodule ℝ V} {w : V} (hwP : w ∈ Pᗮ)
    {ε η t ρ : ℝ} (hε : 0 ≤ ε) (hεη : ‖w‖ * (ε * K + η) ≤ t)
    (hρ : ∀ ⦃u⦄, dist u u₀ < ρ → ‖f u - f u₀ - fderiv ℝ f u₀ (u - u₀)‖ ≤ η * ‖u - u₀‖)
    (E : Set V) {r : ℝ} (hrρ : ((L : ℝ) + 1) * r < ρ) :
    E ∩ closedBall (f u₀) r ⊆
      {z ∈ E ∩ closedBall (f u₀) r | ε * dist z (f u₀) < infDist (z - f u₀) (P : Set V)} ∪
        ((E \ f '' A) ∩ closedBall (f u₀) r) ∪
        f '' (A ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (((L : ℝ) + 1) * r) ∩
          {v | |(innerSL ℝ w).comp (fderiv ℝ f u₀) v| ≤ t * ‖v‖})) := by
  intro z hz
  by_cases hout : ε * dist z (f u₀) < infDist (z - f u₀) (P : Set V)
  · exact Or.inl (Or.inl ⟨hz, hout⟩)
  by_cases hzA : z ∈ f '' A
  swap
  · exact Or.inl (Or.inr ⟨⟨hz.1, hzA⟩, hz.2⟩)
  obtain ⟨u, hu, rfl⟩ := hzA
  refine Or.inr ⟨u, ⟨hu, ?_⟩, rfl⟩
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hz.2)
  have hdist : ‖u - u₀‖ ≤ ((L : ℝ) + 1) * r := by
    have h1 := hA.le_mul_dist ⟨u, hu⟩ ⟨u₀, hu₀⟩
    simp only [Subtype.dist_eq, domRestrict_apply] at h1
    rw [← dist_eq_norm]
    calc dist u u₀ ≤ L * dist (f u) (f u₀) := h1
      _ ≤ L * r := by gcongr; exact mem_closedBall.mp hz.2
      _ ≤ ((L : ℝ) + 1) * r := by nlinarith
  refine ⟨mem_closedBall_zero_iff.mpr hdist, ?_⟩
  have hsmall : dist u u₀ < ρ := by rw [dist_eq_norm]; linarith
  have hlin := hρ hsmall
  have hcone : |⟪w, f u - f u₀⟫| ≤ ‖w‖ * (ε * dist (f u) (f u₀)) :=
    (abs_inner_le_norm_mul_infDist hwP _).trans
      (mul_le_mul_of_nonneg_left (not_lt.mp hout) (norm_nonneg w))
  have hLip : dist (f u) (f u₀) ≤ K * ‖u - u₀‖ := by
    rw [← dist_eq_norm]; exact hf.dist_le_mul u u₀
  have hψu : (innerSL ℝ w).comp (fderiv ℝ f u₀) (u - u₀) =
      ⟪w, f u - f u₀⟫ - ⟪w, f u - f u₀ - fderiv ℝ f u₀ (u - u₀)⟫ := by
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sub_right]
    ring
  calc |(innerSL ℝ w).comp (fderiv ℝ f u₀) (u - u₀)|
      ≤ |⟪w, f u - f u₀⟫| + |⟪w, f u - f u₀ - fderiv ℝ f u₀ (u - u₀)⟫| := by
        rw [hψu]; exact abs_sub _ _
    _ ≤ ‖w‖ * (ε * (K * ‖u - u₀‖)) + ‖w‖ * (η * ‖u - u₀‖) := by
        gcongr
        · exact hcone.trans (by gcongr)
        · exact (abs_real_inner_le_norm _ _).trans (by gcongr)
    _ = ‖w‖ * (ε * K + η) * ‖u - u₀‖ := by ring
    _ ≤ t * ‖u - u₀‖ := by gcongr

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The image under a `K`-Lipschitz map of the parameters `u` with `u - u₀` in the part of a
cone `|ψ v| ≤ t ‖v‖` in the closed ball of radius `c r` has `k`-dimensional density at most
`K ^ k c ^ k` times the share of the cone in the unit ball. -/
private theorem euclideanHausdorffMeasure_image_inter_cone_div_le
    {f : EuclideanSpace ℝ (Fin k) → V} {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set (EuclideanSpace ℝ (Fin k))) (u₀ : EuclideanSpace ℝ (Fin k))
    (ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) (t : ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    μHE[k] (f '' (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤
      (K : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) /
        volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  have hcr : 0 < c * r := by positivity
  have himage := (hf.lipschitzOnWith (s := s ∩ (fun u ↦ u - u₀) ⁻¹'
    (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))).euclideanHausdorffMeasure_image_le k
  have hvol : μHE[k] (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖})) ≤
      ENNReal.ofReal ((c * r) ^ k) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
    have hμ : (μHE[k] : Measure (EuclideanSpace ℝ (Fin k))) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume k
    have hvolS := Measure.addHaar_closedBall_inter_setOf_abs_le_mul_norm volume ψ t hcr
    rw [finrank_euclideanSpace_fin] at hvolS
    rw [hμ, ← hvolS]
    refine (measure_mono inter_subset_right).trans_eq ?_
    simp only [sub_eq_add_neg]
    exact measure_preimage_add_right _ _ _
  rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin]
  calc μHE[k] (f '' (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))) /
        (ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1))
      ≤ (K : ℝ≥0∞) ^ k * (ENNReal.ofReal ((c * r) ^ k) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) /
          (ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) := by
        gcongr
        exact himage.trans (by gcongr)
    _ = ENNReal.ofReal (r ^ k) * ((K : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) /
          (ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity)]
        ac_rfl
    _ = _ := ENNReal.mul_div_mul_left _ _
          (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

/-- **The approximate tangent plane on a patch.** Let `f` be Lipschitz, inverse-Lipschitz on `A`,
and differentiable at `u₀ ∈ A` with derivative range of dimension `k`. If a set `E` has density one
at `x = f u₀` and `E \ f '' A` has density zero there, then every approximate tangent `k`-plane of
`E` at `x` is the derivative range. -/
theorem _root_.LipschitzWith.eq_range_fderiv_of_tendsto_measure_outside_cone_div
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
  -- A vector `w` orthogonal to `P` but not to the derivative range makes `ψ = ⟪w, D ·⟫` nonzero.
  obtain ⟨w, hwP, -, ⟨v₀, rfl⟩, hwv₀⟩ := exists_mem_orthogonal_inner_ne_zero_of_not_le
    (S := D.range) fun hle ↦
      hne (Submodule.eq_of_le_of_finrank_eq hle (hrange.trans hPk.symm)).symm
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr fun h ↦ hwv₀ (by simp [h])
  set ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := (innerSL ℝ w).comp D
  have hψ : ψ ≠ 0 := fun h ↦ hwv₀ (by simpa [ψ] using congr($h v₀))
  -- The constant `a` with `μHE[k] (patch part) ≤ a r ^ k vol (cone)`.
  set a : ℝ≥0∞ := (K : ℝ≥0∞) ^ k * ENNReal.ofReal (((L : ℝ) + 1) ^ k)
  have ha_top : a ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    ENNReal.ofReal_ne_top
  set B₁ := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)
  have hB₁0 : B₁ ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hB₁top : B₁ ≠ ∞ := measure_ball_lt_top.ne
  -- Choose the thickness `t` of the parameter cone so that its share is below one.
  set C : ℝ → Set (EuclideanSpace ℝ (Fin k)) := fun t ↦ closedBall 0 1 ∩ {v | |ψ v| ≤ t * ‖v‖}
  have hlt : a * 0 < B₁ := by rw [mul_zero]; exact pos_iff_ne_zero.mpr hB₁0
  obtain ⟨t, hn, ht⟩ := (((ENNReal.Tendsto.const_mul
    (Measure.tendsto_addHaar_closedBall_inter_setOf_abs_le_mul_norm volume hψ)
      (Or.inr ha_top)).eventually (gt_mem_nhds hlt)).and self_mem_nhdsWithin).exists
  replace ht : 0 < t := ht
  set m : ℝ≥0∞ := a * volume (C t) / B₁
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
  -- Passing to the limit in the three-piece cover gives `1 ≤ 0 + 0 + m`, contradicting `m < 1`.
  have hlim : (1 : ℝ≥0∞) ≤ 0 + 0 + m := by
    refine le_of_tendsto_of_tendsto hE1 (((hP ε hε).add hE0).add tendsto_const_nhds) ?_
    have hρL : 0 < ρ / ((L : ℝ) + 1) := by positivity
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds hρL)] with r hr hrρ
    have hrρ' : ((L : ℝ) + 1) * r < ρ := by
      rwa [lt_div_iff₀' (by positivity)] at hrρ
    set S := A ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (((L : ℝ) + 1) * r) ∩ {v | |ψ v| ≤ t * ‖v‖})
    calc μHE[k] (E ∩ closedBall x r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
        ≤ (μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} +
            μHE[k] ((E \ f '' A) ∩ closedBall x r) + μHE[k] (f '' S)) /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
          gcongr
          exact (measure_mono (subset_union_image_of_forall_dist_lt hf hA hu₀ hwP hε.le hεη hρd E
            hrρ')).trans ((measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _))
      _ = μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
            μHE[k] ((E \ f '' A) ∩ closedBall x r) /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
            μHE[k] (f '' S) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
          rw [ENNReal.add_div, ENNReal.add_div]
      _ ≤ _ := by
          gcongr
          exact euclideanHausdorffMeasure_image_inter_cone_div_le hf A u₀ ψ t
            (by positivity) hr
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
  obtain ⟨u, hu, rfl, hd, hrange, -⟩ := hgood n hxn
  have h0 := hzero n fun h ↦ h.2 hxn
  have hone' := hone hxE
  rw [(hLip n).eq_range_fderiv_of_tendsto_measure_outside_cone_div (hAnti n) hu hd hrange hone' h0
      hP hPc,
    (hLip n).eq_range_fderiv_of_tendsto_measure_outside_cone_div (hAnti n) hu hd hrange hone' h0
      hQ hQc]

end TauCeti
