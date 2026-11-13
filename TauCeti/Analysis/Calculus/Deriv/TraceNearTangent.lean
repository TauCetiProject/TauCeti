/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Segment
public import TauCeti.Analysis.Complex.Basic

/-!
# Tangent-cone estimates and transverse segments avoiding a trace

Near a point where a curve `γ : ℝ → ℂ` has nonzero derivative `v`, and which `γ` visits only once
on a compact parameter set, the trace of `γ` lies in arbitrarily thin double cones
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line: the derivative controls
the parameters close to `t₀`, and compactness keeps the others away from `γ t₀`.
At `v = 0` the inequality is trivial. These estimates keep transverse curves and segments to
the normal ray disjoint from the trace near `γ t₀`, enabling side determination for Jordan curves.

## Main results

* `IsCompact.exists_pos_forall_abs_im_conj_mul_sub_le`: the trace near a point visited once
  satisfies the tangent-cone estimate.
* `HasDerivWithinAt.eventually_segment_subset_compl_of_abs_im_conj_mul_sub_le`: segments from a
  curve leaving strictly to the left of a direction to its left normal ray avoid a set satisfying
  the tangent-cone estimate.
* `HasDerivWithinAt.eventually_segment_subset_compl`: the corresponding result for a trace
  continuous on a compact parameter set `K` and differentiable within `K` at a uniquely visited
  base point `t₀`, with the other curve leaving strictly to the left of the tangent.
-/

public section

open Complex ComplexConjugate Filter Metric Set
open scoped Topology

/-- **Tangent-cone estimate for the trace near a point visited once.**
Let `γ` be continuous on a compact set `K` of parameters, with derivative `v` at `t₀` within `K`,
and assume that `γ` takes the value `γ t₀` on `K` only at `t₀`. Then for every `η > 0`, every point
of the trace `γ '' K` close enough to `γ t₀` satisfies
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖`. When `v ≠ 0` and `η` is small, this is a
thin double cone around the tangent line `γ t₀ + ℝ • v`; at `v = 0` the bound is trivial. -/
theorem IsCompact.exists_pos_forall_abs_im_conj_mul_sub_le {γ : ℝ → ℂ} {K : Set ℝ} {t₀ : ℝ} {v : ℂ}
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
    abs_im_conj_mul_le v e
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

/-- **Lower bound across the tangent line along a segment.** Let `z` be the point at parameter
`l ∈ [0, 1]` of the segment from `ε • w + e` to `ε • (I * u)`, written relative to its base point.
If `w` and `I * u` both lie at least `κ` to the left of `u` (measured by `Im (conj u * ·)`), and
the error `e` is small enough, then `z` lies at least `3 / 4 * κ * ε` to the left of `u`. -/
private theorem le_im_conj_mul_smul_add_smul {u w e : ℂ} {κ η ε l : ℝ}
    (hκw : κ ≤ (conj u * w).im) (hκu : κ ≤ ‖u‖ ^ 2) (hηu : ‖u‖ * η ≤ κ / 4) (hε : 0 < ε)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (he : ‖e‖ ≤ η * ε) :
    3 / 4 * κ * ε ≤ (conj u * (ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e)).im := by
  have hn : (conj u * (I * u)).im = ‖u‖ ^ 2 := by
    simp [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow]
  have him : (conj u * (ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e)).im =
      ε * ((1 - l) * (conj u * w).im + l * ‖u‖ ^ 2) + (1 - l) * (conj u * e).im := by
    rw [← hn]
    simp only [mul_add, mul_smul_comm, add_im, smul_im, smul_eq_mul]
  -- The error term moves the point by at most `κ / 4 * ε` across the tangent line.
  have hime : |(conj u * e).im| ≤ κ / 4 * ε := by
    refine (abs_im_conj_mul_le u e).trans ?_
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

/-- If a set `S` near `z₀` lies in thin double cones around the line `z₀ + ℝ • u`, and a curve
`p` with right derivative `w` at `0` leaves `z₀` strictly to the left of `u`
(`0 < Im (conj u * w)`), then for small `ε > 0` the segment from `p ε` to the point
`z₀ + ε • (I * u)` of the left normal ray does not meet `S`. -/
theorem HasDerivWithinAt.eventually_segment_subset_compl_of_abs_im_conj_mul_sub_le
    {S : Set ℂ} {z₀ u w : ℂ} {p : ℝ → ℂ}
    (hp : HasDerivWithinAt p w (Ici 0) 0)
    (hcone : ∀ η > 0, ∃ ρ > 0, ∀ z ∈ S, ‖z - z₀‖ < ρ →
      |(conj u * (z - z₀)).im| ≤ η * ‖z - z₀‖)
    (hp0 : p 0 = z₀)
    (hw : 0 < (conj u * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, segment ℝ (p ε) (z₀ + ε • (I * u)) ⊆ Sᶜ := by
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
  rintro z ⟨l, ⟨hl0, hl1⟩, hlz⟩ hzS
  have hz : z - z₀ = ε • ((1 - l) • w + l • (I * u)) + (1 - l) • e := by
    rw [← hlz]
    simp only [e, hp0, sub_zero]
    module
  have hlow : 3 / 4 * κ * ε ≤ (conj u * (z - z₀)).im :=
    hz ▸ le_im_conj_mul_smul_add_smul (min_le_left _ _) (min_le_right _ _) hηu hε hl0 hl1 he
  have hnorm : ‖z - z₀‖ ≤ M * ε :=
    hz ▸ norm_smul_add_smul_le (min_le_left _ _) hε hl0 hl1 he
  -- The point `z` is close to `z₀`, so it lies in the thin cone, which contradicts `hlow`.
  have hρs : ‖z - z₀‖ < ρ :=
    hnorm.trans_lt (by rwa [lt_div_iff₀ hM, mul_comm] at hερ)
  have hup := (le_abs_self _).trans (hc z hzS hρs)
  have h3 : κ / (4 * M) * ‖z - z₀‖ ≤ κ / 4 * ε := by
    calc κ / (4 * M) * ‖z - z₀‖ ≤ κ / (4 * M) * (M * ε) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = κ / 4 * ε := by field_simp
  nlinarith [mul_pos hκ hε]

/-- Let `γ` be continuous on a compact parameter set `K`, have derivative `v` within `K` at `t₀`,
and visit `γ t₀` only at `t₀` on `K`. If `p` has right derivative `w` at `0` and leaves `γ t₀`
strictly to the left of `v` (`0 < Im (conj v * w)`), then the segment from `p ε` to the left
normal ray avoids the trace at all small positive times. -/
theorem HasDerivWithinAt.eventually_segment_subset_compl
    {γ : ℝ → ℂ} {K : Set ℝ} {t₀ : ℝ} {v w : ℂ} (hd : HasDerivWithinAt γ v K t₀)
    (hK : IsCompact K) (hγ : ContinuousOn γ K) (huniq : ∀ t ∈ K, γ t = γ t₀ → t = t₀)
    {p : ℝ → ℂ} (hp0 : p 0 = γ t₀) (hp : HasDerivWithinAt p w (Ici 0) 0)
    (hw : 0 < (conj v * w).im) :
    ∀ᶠ ε in 𝓝[>] 0, segment ℝ (p ε) (γ t₀ + ε • (I * v)) ⊆ (γ '' K)ᶜ :=
  hp.eventually_segment_subset_compl_of_abs_im_conj_mul_sub_le
    (fun _ hη ↦ by
      obtain ⟨ρ, hρ, h⟩ := hK.exists_pos_forall_abs_im_conj_mul_sub_le hγ huniq hd hη
      exact ⟨ρ, hρ, forall_mem_image.2 h⟩) hp0 hw
