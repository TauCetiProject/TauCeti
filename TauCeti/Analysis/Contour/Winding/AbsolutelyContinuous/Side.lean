/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.Deriv.TangentCone
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.TangentJump

/-!
# The side of a Jordan curve entered by a transverse curve

Near a point where a curve `γ` has derivative `v`, and which `γ` visits only once on a compact
parameter set, the trace of `γ` lies in arbitrarily thin double cones
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line
(`TauCeti.Contour.exists_pos_forall_abs_im_conj_mul_sub_le`).

For a simple closed absolutely continuous curve, this upgrades the normal identification of the
orientation sign `jordanSign γ a b` (normal rays at a regular point enter the inside or the
outside) to arbitrary curves `p` leaving `γ t₀` transversally: a short segment joins `p ε` to the
normal ray without meeting the trace. A curve leaving strictly to the left of the tangent, that is
with `0 < Im (conj v * w)` for its right derivative `w`, enters the bounded inside of a positively
oriented curve and the unbounded outside of a negatively oriented one.

## Main results

* `AbsolutelyContinuousOnInterval.eventually_mem_filledHull_sdiff_of_hasDerivAt`: a curve leaving
  a regular point on the side selected by `jordanSign γ a b` enters the bounded inside.
* `AbsolutelyContinuousOnInterval.eventually_notMem_filledHull_of_hasDerivAt`: a curve leaving a
  regular point on the other side enters the unbounded outside.
-/

public section

open Complex ComplexConjugate Filter Metric Set
open scoped Topology

namespace TauCeti.Contour

/-- **Lower bound across the tangent line along a segment.** Let `z` be the point at parameter
`l ∈ [0, 1]` of the segment from `ε • w + e` to `ε • (I * u)`, written relative to its base point.
If `w` and `I * u` both lie at least `κ` to the left of `u` (measured by `Im (conj u * ·)`), and
the error `e` is small enough, then `z` lies at least `3 / 4 * κ * ε` to the left of `u`. -/
private theorem le_im_conj_mul_smul_add_smul {u w e : ℂ} {κ η ε l : ℝ}
    (hκw : κ ≤ (conj u * w).im) (hκu : κ ≤ ‖u‖ ^ 2) (hηu : ‖u‖ * η ≤ κ / 4) (hε : 0 < ε)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (he : ‖e‖ ≤ η * ε) :
    3 / 4 * κ * ε ≤ (conj u * (ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e)).im := by
  have hn : (conj u * (I * u)).im = ‖u‖ ^ 2 := by
    rw [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, Complex.I_mul_im,
      Complex.ofReal_re]
  have him : (conj u * (ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e)).im =
      ε * ((1 - l) * (conj u * w).im + l * ‖u‖ ^ 2) + (1 - l) * (conj u * e).im := by
    rw [← hn]
    simp only [mul_add, mul_smul_comm, add_im, smul_im, smul_eq_mul]
  -- The error term moves the point by at most `κ / 4 * ε` across the tangent line.
  have hime : |(conj u * e).im| ≤ κ / 4 * ε := by
    refine ((abs_im_le_norm _).trans_eq (by rw [norm_mul, Complex.norm_conj])).trans ?_
    calc ‖u‖ * ‖e‖ ≤ ‖u‖ * (η * ε) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = ‖u‖ * η * ε := by ring
      _ ≤ κ / 4 * ε := mul_le_mul_of_nonneg_right hηu hε.le
  -- The main term is a convex combination of two quantities which are both at least `κ`.
  have h1 : κ ≤ (1 - l) * (conj u * w).im + l * ‖u‖ ^ 2 := by nlinarith
  have h2 := (abs_le.mp hime).1
  rw [him]
  nlinarith [mul_le_mul_of_nonneg_left h1 hε.le, abs_nonneg (conj u * e).im]

/-- **Upper bound on the norm along a segment.** The point at parameter `l ∈ [0, 1]` of the
segment from `ε • w + e` to `ε • (I * u)` has norm at most `(‖w‖ + ‖u‖ + 1) * ε` when
`‖e‖ ≤ η * ε` with `η ≤ 1`. -/
private theorem norm_smul_add_smul_le {u w e : ℂ} {η ε l : ℝ} (hη1 : η ≤ 1) (hε : 0 < ε)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (he : ‖e‖ ≤ η * ε) :
    ‖ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e‖ ≤ (‖w‖ + ‖u‖ + 1) * ε := by
  have hl1' : 0 ≤ 1 - l := sub_nonneg.mpr hl1
  calc ‖ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e‖
      ≤ ε * ((1 - l) * ‖w‖ + l * ‖u‖) + (1 - l) * (η * ε) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq ?_) hε.le
          simp only [norm_smul, norm_mul, norm_I, one_mul, Real.norm_eq_abs, abs_of_nonneg hl0,
            abs_of_nonneg hl1']
        · simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl1']
          exact mul_le_mul_of_nonneg_left he hl1'
    _ ≤ (‖w‖ + ‖u‖ + 1) * ε := by
        have hη0 : 0 ≤ η := nonneg_of_mul_nonneg_left ((norm_nonneg e).trans he) hε
        nlinarith [norm_nonneg w, norm_nonneg u, mul_nonneg hl0 hε.le, mul_nonneg hl1' hε.le,
          mul_nonneg (mul_nonneg hl0 hε.le) hη0]

/-- If the trace near `γ t₀` lies in thin double cones around the line `ℝ • u`, and a curve `p`
leaves `γ t₀` strictly to the left of `u`, then for small `ε > 0` the segment from `p ε` to the
point `γ t₀ + ε • (I * u)` of the left normal ray does not meet the trace. -/
private theorem eventually_segment_subset_compl {γ : ℝ → ℂ} {K : Set ℝ} {t₀ : ℝ} {u w : ℂ}
    (hcone : ∀ η > 0, ∃ ρ > 0, ∀ s ∈ K, ‖γ s - γ t₀‖ < ρ →
      |(conj u * (γ s - γ t₀)).im| ≤ η * ‖γ s - γ t₀‖)
    {p : ℝ → ℂ} (hp0 : p 0 = γ t₀) (hp : HasDerivWithinAt p w (Ici 0) 0)
    (hw : 0 < (conj u * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, segment ℝ (p ε) (γ t₀ + ε • (I * u)) ⊆ (γ '' K)ᶜ := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at hw
  -- `κ` bounds from below how far `w` and `I * u` lie to the left of `u`; the segment points stay
  -- in a ball of radius `M * ε`, and `η` is the relative error allowed for `p ε` around `ε • w`.
  set κ := min (conj u * w).im (‖u‖ ^ 2)
  have hκ : 0 < κ := lt_min hw (by positivity)
  set M := ‖w‖ + ‖u‖ + 1
  have hM : 0 < M := by positivity
  -- The cone of aperture `κ / (4 * M)` is too thin to contain points at distance `≤ M * ε` lying
  -- `3 / 4 * κ * ε` to the left of the tangent.
  obtain ⟨ρ, hρ, hc⟩ := hcone (κ / (4 * M)) (by positivity)
  set η := min 1 (κ / (4 * (‖u‖ + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hηu : ‖u‖ * η ≤ κ / 4 := by
    have h : η * (4 * (‖u‖ + 1)) ≤ κ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [norm_nonneg u]
  filter_upwards [nhdsWithin_mono _ Ioi_subset_Ici_self
      ((hasDerivWithinAt_iff_isLittleO.mp hp).def hη),
    nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < ρ / M by positivity)),
    self_mem_nhdsWithin] with ε hεo hερ (hε : 0 < ε)
  set e := p ε - p 0 - (ε - 0) • w
  have he : ‖e‖ ≤ η * ε := by simpa [Real.norm_eq_abs, abs_of_pos hε] using hεo
  rw [segment_eq_image']
  rintro _ ⟨l, ⟨hl0, hl1⟩, rfl⟩ ⟨s, hs, hsz⟩
  have hz : γ s - γ t₀ = ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e := by
    rw [hsz]
    simp only [e, hp0, sub_zero]
    module
  have hlow : 3 / 4 * κ * ε ≤ (conj u * (γ s - γ t₀)).im :=
    hz ▸ le_im_conj_mul_smul_add_smul (min_le_left _ _) (min_le_right _ _) hηu hε hl0 hl1 he
  have hnorm : ‖γ s - γ t₀‖ ≤ M * ε :=
    hz ▸ norm_smul_add_smul_le (min_le_left _ _) hε hl0 hl1 he
  -- The point `γ s` is close to `γ t₀`, so it lies in the thin cone, which contradicts `hlow`.
  have hρs : ‖γ s - γ t₀‖ < ρ :=
    hnorm.trans_lt (by rwa [lt_div_iff₀ hM, mul_comm] at hερ)
  have hup := (le_abs_self _).trans (hc s hs hρs)
  have h3 : κ / (4 * M) * ‖γ s - γ t₀‖ ≤ κ / 4 * ε := by
    calc κ / (4 * M) * ‖γ s - γ t₀‖ ≤ κ / (4 * M) * (M * ε) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = κ / 4 * ε := by field_simp
  nlinarith [mul_pos hκ hε]

end TauCeti.Contour

open TauCeti TauCeti.Contour

namespace AbsolutelyContinuousOnInterval

variable {γ : ℝ → ℂ} {a b t₀ : ℝ} {v w : ℂ} {p : ℝ → ℂ}

/-- A curve leaving a regular point strictly to the left of `u = ± v` avoids the trace on a segment
to the left normal ray of `u`. -/
private theorem eventually_segment_subset_compl_of_hasDerivAt {u : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hu : u = v ∨ u = -v) (hp0 : p 0 = γ t₀)
    (hp : HasDerivWithinAt p w (Ici 0) 0) (hw : 0 < (conj u * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, segment ℝ (p ε) (γ t₀ + ε • (I * u)) ⊆ (γ '' uIcc a b)ᶜ := by
  have huniq : ∀ t ∈ uIcc a b, γ t = γ t₀ → t = t₀ := fun t ht ↦
    hinj.eq_of_mem_Icc_of_mem_Ioo hclosed ht₀ (uIcc_of_le hab.le ▸ ht)
  refine eventually_segment_subset_compl (fun η hη ↦ ?_) hp0 hp hw
  obtain ⟨ρ, hρ, h⟩ := exists_pos_forall_abs_im_conj_mul_sub_le isCompact_uIcc hγ.continuousOn
    huniq hd.hasDerivWithinAt hη
  refine ⟨ρ, hρ, fun s hs hsρ ↦ ?_⟩
  rcases hu with rfl | rfl
  · exact h s hs hsρ
  · rw [map_neg, neg_mul, neg_im, abs_neg]
    exact h s hs hsρ

/-- **A transverse curve enters the inside on the side selected by the orientation.** Let `γ` be
a simple closed absolutely continuous curve on `[a, b]`, with derivative `v` at an interior
parameter `t₀`. A curve `p` with `p 0 = γ t₀` and right derivative `w` at `0` satisfying
`0 < jordanSign γ a b * Im (conj v * w)` lies in the bounded inside
`filledHull (γ '' uIcc a b) \ γ '' uIcc a b` at all small positive times. For a positively
oriented curve, this is the case of a curve leaving `γ t₀` strictly to the left of the tangent. -/
theorem eventually_mem_filledHull_sdiff_of_hasDerivAt (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p 0 = γ t₀)
    (hp : HasDerivWithinAt p w (Ici 0) 0)
    (hw : 0 < (jordanSign γ a b : ℝ) * (conj v * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, p ε ∈ filledHull (γ '' uIcc a b) \ γ '' uIcc a b := by
  have hv : v ≠ 0 := by
    rintro rfl
    simp at hw
  set σ : ℝ := ((jordanSign γ a b : ℤ) : ℝ)
  have hu : σ • v = v ∨ σ • v = -v := by
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> simp [σ, h]
  have hw' : 0 < (conj (σ • v) * w).im := by
    rwa [Complex.real_smul, map_mul, conj_ofReal, mul_assoc, im_ofReal_mul]
  have hC := hγ.isJordanCurve_image_uIcc hab hclosed hinj
  filter_upwards [hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt hab hclosed hinj
    ht₀ hd hv, eventually_segment_subset_compl_of_hasDerivAt hab hγ hclosed hinj ht₀ hd hu hp0 hp
    hw'] with ε hn hseg
  rw [mul_smul_comm] at hseg
  rw [hC.filledHull_sdiff_eq_connectedComponentIn hn.1]
  exact (convex_segment _ _).isPreconnected.subset_connectedComponentIn (right_mem_segment _ _ _)
    hseg (left_mem_segment _ _ _)

/-- **A transverse curve enters the outside on the side opposite to the orientation.** Let `γ` be
a simple closed absolutely continuous curve on `[a, b]`, with derivative `v` at an interior
parameter `t₀`. A curve `p` with `p 0 = γ t₀` and right derivative `w` at `0` satisfying
`jordanSign γ a b * Im (conj v * w) < 0` lies outside `filledHull (γ '' uIcc a b)` at all small
positive times. For a negatively oriented curve, this is the case of a curve leaving `γ t₀`
strictly to the left of the tangent. -/
theorem eventually_notMem_filledHull_of_hasDerivAt (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p 0 = γ t₀)
    (hp : HasDerivWithinAt p w (Ici 0) 0)
    (hw : (jordanSign γ a b : ℝ) * (conj v * w).im < 0) :
    ∀ᶠ ε in 𝓝[>] 0, p ε ∉ filledHull (γ '' uIcc a b) := by
  have hv : v ≠ 0 := by
    rintro rfl
    simp at hw
  set σ : ℝ := ((jordanSign γ a b : ℤ) : ℝ)
  have hu : -(σ • v) = v ∨ -(σ • v) = -v := by
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> simp [σ, h]
  have hw' : 0 < (conj (-(σ • v)) * w).im := by
    rwa [Complex.real_smul, map_neg, map_mul, conj_ofReal, neg_mul, mul_assoc, neg_im,
      im_ofReal_mul, neg_pos]
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have hbdd := (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isBounded
  filter_upwards [hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt hab hclosed hinj
    ht₀ hd hv, eventually_segment_subset_compl_of_hasDerivAt hab hγ hclosed hinj ht₀ hd hu hp0 hp
    hw'] with ε hn hseg
  rw [mul_neg, mul_smul_comm, smul_neg, ← sub_eq_add_neg] at hseg
  have hmem := (convex_segment _ _).isPreconnected.subset_connectedComponentIn
    (right_mem_segment _ _ _) hseg (left_mem_segment _ _ _)
  rwa [← compl_filledHull_eq_connectedComponentIn hrank hbdd hn.2] at hmem

end AbsolutelyContinuousOnInterval
