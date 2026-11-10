/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Topology.JordanCurve.Interval

/-!
# The side of a Jordan curve entered by a transverse curve

Near a point where a curve `γ` has derivative `v`, and which `γ` visits only once on a compact
parameter set, the trace of `γ` lies in arbitrarily thin double cones
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line: the derivative controls
the parameters close to `t₀`, and compactness keeps the others away from `γ t₀`.

For a simple closed absolutely continuous curve, this upgrades the normal identification of the
orientation sign `jordanSign γ a b` (normal rays at a regular point enter the inside or the
outside) to arbitrary curves `p` leaving `γ t₀` transversally: a short segment joins `p ε` to the
normal ray without meeting the trace. A curve leaving strictly to the left of the tangent, that is
with `0 < Im (conj v * w)` for its velocity `w`, enters the bounded inside of a positively oriented
curve and the unbounded outside of a negatively oriented one.

## Main results

* `TauCeti.Contour.exists_pos_forall_abs_im_conj_mul_sub_le`: the trace near a point visited once
  lies in thin double cones around the tangent line.
* `AbsolutelyContinuousOnInterval.eventually_mem_filledHull_sdiff_of_hasDerivAt`: a curve leaving
  a regular point on the side selected by `jordanSign γ a b` enters the bounded inside.
* `AbsolutelyContinuousOnInterval.eventually_notMem_filledHull_of_hasDerivAt`: a curve leaving a
  regular point on the other side enters the unbounded outside.
-/

public section

open Complex ComplexConjugate Filter Metric Set
open scoped Topology

namespace TauCeti.Contour

/-- **The trace near a point visited once lies in thin double cones around the tangent line.**
Let `γ` be continuous on a compact set `K` of parameters, with derivative `v` at `t₀` within `K`,
and assume that `γ` takes the value `γ t₀` on `K` only at `t₀`. Then for every `η > 0`, every point
of the trace `γ '' K` close enough to `γ t₀` lies in the double cone
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line. -/
theorem exists_pos_forall_abs_im_conj_mul_sub_le {γ : ℝ → ℂ} {K : Set ℝ} {t₀ : ℝ} {v : ℂ}
    (hK : IsCompact K) (hγ : ContinuousOn γ K) (huniq : ∀ t ∈ K, γ t = γ t₀ → t = t₀)
    (hd : HasDerivWithinAt γ v K t₀) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ s ∈ K, ‖γ s - γ t₀‖ < ρ →
      |(conj v * (γ s - γ t₀)).im| ≤ η * ‖γ s - γ t₀‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨1, one_pos, fun s _ _ ↦ by simpa using mul_nonneg hη.le (norm_nonneg (γ s - γ t₀))⟩
  set ε := min (‖v‖ / 2) (η / 2)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨σ, hσ, hloc⟩ : ∃ σ > 0, ∀ s ∈ K, |s - t₀| < σ →
      ‖γ s - γ t₀ - (s - t₀) • v‖ ≤ ε * |s - t₀| := by
    obtain ⟨σ, hσ, h⟩ := Metric.eventually_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp ((hasDerivWithinAt_iff_isLittleO.mp hd).def hε))
    exact ⟨σ, hσ, fun s hs hsσ ↦ by
      simpa [Real.norm_eq_abs] using h (by rwa [Real.dist_eq]) hs⟩
  set L := K ∩ {s | σ ≤ |s - t₀|}
  have hL : IsCompact L :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hγL : γ t₀ ∉ γ '' L := by
    rintro ⟨s, ⟨hs, hsσ⟩, hst⟩
    exact hσ.not_ge (by simpa [huniq s hs hst] using hsσ)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
    (hL.image_of_continuousOn (hγ.mono inter_subset_left)).isClosed.isOpen_compl _ hγL
  refine ⟨ρ, hρ, fun s hs hsρ ↦ ?_⟩
  have hsσ : |s - t₀| < σ := by
    by_contra h
    exact hball (mem_ball.mpr (by rwa [dist_eq_norm])) (mem_image_of_mem γ ⟨hs, not_lt.mp h⟩)
  have he := hloc s hs hsσ
  set e := γ s - γ t₀ - (s - t₀) • v
  have him : (conj v * (γ s - γ t₀)).im = (conj v * e).im := by
    have hreal : (conj v * ((s - t₀) • v)).im = 0 := by
      simp only [mul_smul_comm, smul_im, mul_im, conj_re, conj_im, smul_eq_mul]
      ring
    rw [show γ s - γ t₀ = (s - t₀) • v + e by simp [e], mul_add, add_im, hreal, zero_add]
  have hime : |(conj v * e).im| ≤ ‖v‖ * ‖e‖ :=
    (abs_im_le_norm _).trans_eq (by rw [norm_mul, Complex.norm_conj])
  have hlow : ‖v‖ / 2 * |s - t₀| ≤ ‖γ s - γ t₀‖ := by
    have h1 := norm_sub_le (γ s - γ t₀) e
    rw [show γ s - γ t₀ - e = (s - t₀) • v by simp [e], norm_smul, Real.norm_eq_abs] at h1
    have : ε ≤ ‖v‖ / 2 := min_le_left _ _
    nlinarith [abs_nonneg (s - t₀)]
  have hεη : ε ≤ η / 2 := min_le_right _ _
  rw [him]
  calc |(conj v * e).im| ≤ ‖v‖ * (ε * |s - t₀|) :=
        hime.trans (mul_le_mul_of_nonneg_left he hvpos.le)
    _ = 2 * ε * (‖v‖ / 2 * |s - t₀|) := by ring
    _ ≤ 2 * ε * ‖γ s - γ t₀‖ := mul_le_mul_of_nonneg_left hlow (by positivity)
    _ ≤ η * ‖γ s - γ t₀‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- If the trace near `γ t₀` lies in thin double cones around the line `ℝ • u`, and a curve `p`
leaves `γ t₀` strictly to the left of `u`, then for small `ε > 0` the segment from `p ε` to the
point `γ t₀ + ε • (I * u)` of the left normal ray does not meet the trace. -/
private theorem eventually_segment_subset_compl {γ : ℝ → ℂ} {K : Set ℝ} {t₀ : ℝ} {u w : ℂ}
    (hcone : ∀ η > 0, ∃ ρ > 0, ∀ s ∈ K, ‖γ s - γ t₀‖ < ρ →
      |(conj u * (γ s - γ t₀)).im| ≤ η * ‖γ s - γ t₀‖)
    {p : ℝ → ℂ} (hp0 : p 0 = γ t₀) (hp : HasDerivAt p w 0) (hw : 0 < (conj u * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, segment ℝ (p ε) (γ t₀ + ε • (I * u)) ⊆ (γ '' K)ᶜ := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at hw
  have hn : (conj u * (I * u)).im = ‖u‖ ^ 2 := by
    rw [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, Complex.I_mul_im,
      Complex.ofReal_re]
  set κ := min (conj u * w).im (‖u‖ ^ 2)
  have hκ : 0 < κ := lt_min hw (by positivity)
  set M := ‖w‖ + ‖u‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨ρ, hρ, hc⟩ := hcone (κ / (4 * M)) (by positivity)
  set η := min 1 (κ / (4 * (‖u‖ + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηu : ‖u‖ * η ≤ κ / 4 := by
    have h : η * (4 * (‖u‖ + 1)) ≤ κ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [norm_nonneg u]
  filter_upwards [nhdsWithin_le_nhds ((hasDerivAt_iff_isLittleO.mp hp).def hη),
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
  have him : (conj u * (γ s - γ t₀)).im =
      ε * ((1 - l) * (conj u * w).im + l * ‖u‖ ^ 2) + (1 - l) * (conj u * e).im := by
    rw [hz, ← hn]
    simp only [mul_add, mul_smul_comm, add_im, smul_im, smul_eq_mul]
  have hime : |(conj u * e).im| ≤ κ / 4 * ε := by
    refine ((abs_im_le_norm _).trans_eq (by rw [norm_mul, Complex.norm_conj])).trans ?_
    calc ‖u‖ * ‖e‖ ≤ ‖u‖ * (η * ε) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = ‖u‖ * η * ε := by ring
      _ ≤ κ / 4 * ε := mul_le_mul_of_nonneg_right hηu hε.le
  have hlow : 3 / 4 * κ * ε ≤ (conj u * (γ s - γ t₀)).im := by
    have hκw : κ ≤ (conj u * w).im := min_le_left _ _
    have hκu : κ ≤ ‖u‖ ^ 2 := min_le_right _ _
    have h1 : κ ≤ (1 - l) * (conj u * w).im + l * ‖u‖ ^ 2 := by nlinarith
    have h2 := (abs_le.mp hime).1
    rw [him]
    nlinarith [mul_le_mul_of_nonneg_left h1 hε.le, mul_pos hκ hε]
  have hnorm : ‖γ s - γ t₀‖ ≤ M * ε := by
    rw [hz]
    calc ‖ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e‖
        ≤ ε * ((1 - l) * ‖w‖ + l * ‖u‖) + (1 - l) * (η * ε) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq ?_) hε.le
            rw [norm_smul, norm_smul, norm_mul, norm_I, one_mul, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hl0]
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            exact mul_le_mul_of_nonneg_left he (by linarith)
      _ ≤ M * ε := by
          nlinarith [norm_nonneg w, norm_nonneg u, mul_nonneg hl0 hε.le,
            mul_nonneg (sub_nonneg.mpr hl1) hε.le, mul_nonneg (mul_nonneg hl0 hε.le) hη.le]
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
    (hp : HasDerivAt p w 0) (hw : 0 < (conj u * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, segment ℝ (p ε) (γ t₀ + ε • (I * u)) ⊆ (γ '' uIcc a b)ᶜ := by
  have huniq : ∀ t ∈ uIcc a b, γ t = γ t₀ → t = t₀ := by
    intro t ht hγt
    rw [uIcc_of_le hab.le] at ht
    rcases ht.2.eq_or_lt with rfl | htb
    · exact absurd (hinj ⟨le_rfl, hab⟩ (Ioo_subset_Ico_self ht₀) (hclosed.trans hγt)) ht₀.1.ne
    · exact hinj ⟨ht.1, htb⟩ (Ioo_subset_Ico_self ht₀) hγt
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
parameter `t₀`. A curve `p` with `p 0 = γ t₀` and velocity `w` at `0` satisfying
`0 < jordanSign γ a b * Im (conj v * w)` lies in the bounded inside
`filledHull (γ '' uIcc a b) \ γ '' uIcc a b` at all small positive times. For a positively
oriented curve, this is the case of a curve leaving `γ t₀` strictly to the left of the tangent. -/
theorem eventually_mem_filledHull_sdiff_of_hasDerivAt (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p 0 = γ t₀) (hp : HasDerivAt p w 0)
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
  have hC : IsJordanCurve (γ '' uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact isJordanCurve_image_Icc hab (uIcc_of_le hab.le ▸ hγ.continuousOn) hclosed hinj
  filter_upwards [hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt hab hclosed hinj
    ht₀ hd hv, eventually_segment_subset_compl_of_hasDerivAt hab hγ hclosed hinj ht₀ hd hu hp0 hp
    hw'] with ε hn hseg
  rw [mul_smul_comm] at hseg
  rw [hC.filledHull_sdiff_eq_connectedComponentIn hn.1]
  exact (convex_segment _ _).isPreconnected.subset_connectedComponentIn (right_mem_segment _ _ _)
    hseg (left_mem_segment _ _ _)

/-- **A transverse curve enters the outside on the side opposite to the orientation.** Let `γ` be
a simple closed absolutely continuous curve on `[a, b]`, with derivative `v` at an interior
parameter `t₀`. A curve `p` with `p 0 = γ t₀` and velocity `w` at `0` satisfying
`jordanSign γ a b * Im (conj v * w) < 0` lies outside `filledHull (γ '' uIcc a b)` at all small
positive times. For a negatively oriented curve, this is the case of a curve leaving `γ t₀`
strictly to the left of the tangent. -/
theorem eventually_notMem_filledHull_of_hasDerivAt (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p 0 = γ t₀) (hp : HasDerivAt p w 0)
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
