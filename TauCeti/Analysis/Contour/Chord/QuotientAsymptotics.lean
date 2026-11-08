/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Chord-quotient asymptotics at a transverse crossing

For a curve `γ : ℝ → ℂ` through a pole `s = γ t₀` with non-vanishing one-sided derivative `L`,
the chord quotient `(γ t - s) / (t - t₀)` tends to `L`, so on a small one-sided interval the
normalized chord `(γ t - s) / (L (t - t₀))` is close to `1`. Two consequences feed the
principal-value existence argument at the crossing:

* chord quotients `(γ b - s) / (γ a - s)` for `a, b` on a common side lie in
  `Complex.slitPlane` — the hypothesis under which the logarithmic fundamental theorem of
  calculus (`Contour.integral_inv_sub_mul_deriv_eq_log`) applies on the excised pieces;
* the arguments of the annular quotients converge as the excision endpoint tends to the
  crossing, which pins the angle contribution of each branch at the pole.

Where the two sides share a proof, the statement is parametrised over the within-set `u`
(`Ioi t₀` on the right, `Iio t₀` on the left).

## Main results

* `Contour.chord_quotient_tendsto` — `(γ t - s) / (t - t₀) → L` along `𝓝[u] t₀` for `t₀ ∉ u`.
* `Contour.exists_normalized_chord_bound_right` / `_left` — `‖(γ t - s)/(L(t - t₀)) - 1‖ ≤ ρ`
  on a fixed one-sided interval.
* `Contour.chord_quotient_mem_slitPlane` — `(γ b - s) / (γ a - s) ∈ slitPlane` when `a`, `b`
  lie on a common side of `t₀` and their normalized chords lie in the right half-plane.
* `Contour.exists_chord_quotient_mem_slitPlane_right` / `_left` — chord quotients on a small
  one-sided interval lie in the slit plane.
* `Contour.tendsto_arg_div_chord_right` / `Contour.tendsto_arg_chord_div_left` — convergence of
  the annular quotient arguments as the chord endpoint tends to the crossing from one side.
* `Contour.tendsto_arg_chord_div_tangent_nhdsGT` /
  `Contour.tendsto_arg_neg_tangent_div_chord_nhdsLT` — the boundary chord-to-tangent arguments
  converge to zero at the crossing.
* `Contour.exists_chord_div_tangent_mem_slitPlane_right` /
  `Contour.exists_neg_tangent_div_chord_mem_slitPlane_left` — a window radius on which the
  boundary quotients (chord over tangent on the right, negated tangent over chord on the left)
  lie in the slit plane, discharging the `h_slit` hypotheses of the annular limits.
* `Contour.exists_crossing_slitPlane_radius` — the per-crossing package: one radius carrying
  all four slit-plane properties, ready for a
  common minimum across the crossings of a pole.

## Provenance

Migrated from `chord_div_t_tendsto`, `normalized_chord_close`, `exists_normalized_chord_*`,
`div_mem_slitPlane_of_close_to_one`, `chord_quotient_mem_slitPlane`,
`exists_slitPlane_chord_quotient_*`, `tendsto_arg_of_pos_smul_tendsto`, and
`arg_*_annular_tendsto` of `CPVExistence.lean`, together with
`exists_chord_div_endpoint_slitPlane_right`/`_left` of `LocalCutoffs.lean`, in the AINTLIB
`LeanModularForms` development; the general argument limit `tendsto_arg_of_pos_smul_tendsto`
lives on as `Complex.tendsto_arg_of_tendsto_ofReal_mul`.
See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

variable {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}

/-- **Chord-to-tangent quotient limit.** Given `HasDerivWithinAt γ L u t₀` with `t₀ ∉ u` and
`γ t₀ = s`, the chord quotient `(γ t - s) / (t - t₀)` tends to `L` along `𝓝[u] t₀`.
Specialises to the one-sided limits at `u = Ioi t₀` (right) and `u = Iio t₀` (left). -/
theorem chord_quotient_tendsto {u : Set ℝ} (hu : t₀ ∉ u)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ ↦ (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[u] t₀) (𝓝 L) := by
  refine ((hasDerivWithinAt_iff_tendsto_slope' hu).mp h_deriv).congr fun t ↦ ?_
  rw [slope_def_module, h_at, Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

/-- **The normalized chord is eventually close to `1`**: for any `ρ > 0`, eventually along
`𝓝[u] t₀`, `‖(γ t - s) / (L (t - t₀)) - 1‖ ≤ ρ`. -/
private theorem eventually_normalized_chord_close {u : Set ℝ} (hu : t₀ ∉ u)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[u] t₀, ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_one : Tendsto (fun t : ℝ ↦ (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)))
      (𝓝[u] t₀) (𝓝 1) := by
    rw [← div_self hL]
    exact ((chord_quotient_tendsto hu h_deriv h_at).div_const L).congr fun t ↦ by
      rw [div_div, mul_comm]
  filter_upwards [h_one (Metric.closedBall_mem_nhds 1 hρ_pos)] with t ht
  rwa [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] at ht

/-- **Fixed-radius normalized chord bound (right side)**: a positive radius `r` on whose
right interval `(t₀, t₀ + r]` the normalized chord is uniformly `ρ`-close to `1`. -/
theorem exists_normalized_chord_bound_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ioc t₀ (t₀ + r),
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  obtain ⟨c, hc, h⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_normalized_chord_close self_notMem_Ioi h_deriv h_at hL hρ_pos)
  exact ⟨c - t₀, sub_pos.mpr hc, fun t ht ↦ h ⟨ht.1, by linarith [ht.2]⟩⟩

/-- **Fixed-radius normalized chord bound (left side)**: the counterpart of
`exists_normalized_chord_bound_right` on `[t₀ - r, t₀)`. -/
theorem exists_normalized_chord_bound_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ico (t₀ - r) t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  obtain ⟨c, hc, h⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp
    (eventually_normalized_chord_close self_notMem_Iio h_deriv h_at hL hρ_pos)
  exact ⟨t₀ - c, sub_pos.mpr hc, fun t ht ↦ h ⟨by linarith [ht.1], ht.2⟩⟩

/-- A complex number within `1/2` of `1` lies in the open right half-plane. -/
private theorem re_pos_of_norm_sub_one_le_half {q : ℂ} (hq : ‖q - 1‖ ≤ 1 / 2) : 0 < q.re := by
  have h := Complex.re_le_norm (1 - q)
  rw [norm_sub_rev, Complex.sub_re, Complex.one_re] at h
  linarith

/-- **Chord quotient in the slit plane (algebraic core).** If the normalized chords at `a` and
`b` lie in the open right half-plane and `a`, `b` lie on a common side of `t₀` — so that
`(b - t₀) / (a - t₀) > 0` — then `(γ b - s) / (γ a - s) ∈ Complex.slitPlane`. -/
theorem chord_quotient_mem_slitPlane {a b : ℝ}
    (ha : 0 < ((γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))).re)
    (hb : 0 < ((γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))).re) (hab : 0 < (b - t₀) / (a - t₀)) :
    (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  have hL : L ≠ 0 := by rintro rfl; simp at ha
  have hγa : γ a - s ≠ 0 := by intro h; simp [h] at ha
  have ha_ne : ((a - t₀ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; rintro h; simp [h] at hab
  have hb_ne : ((b - t₀ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; rintro h; simp [h] at hab
  have h_ratio : (γ b - s) / (γ a - s) = (((b - t₀) / (a - t₀) : ℝ) : ℂ) *
      ((γ b - s) / (L * ((b - t₀ : ℝ) : ℂ)) / ((γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)))) := by
    rw [Complex.ofReal_div]
    field_simp
  rw [h_ratio]
  exact ofReal_mul_mem_slitPlane hab (div_mem_slitPlane_of_re_pos ha hb)

/-- **Chord quotients on a small right interval lie in the slit plane**: there is `r > 0` such
that `(γ b - s) / (γ a - s) ∈ Complex.slitPlane` whenever `t₀ < a ≤ b ≤ t₀ + r`. -/
theorem exists_chord_quotient_mem_slitPlane_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_right h_deriv h_at hL (ρ := 1 / 2) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha hab hb ↦ ?_⟩
  exact chord_quotient_mem_slitPlane
    (re_pos_of_norm_sub_one_le_half (hr_close a ⟨ha, by linarith⟩))
    (re_pos_of_norm_sub_one_le_half (hr_close b ⟨by linarith, hb⟩))
    (div_pos (by linarith) (by linarith))

/-- **Chord quotients on a small left interval lie in the slit plane**: there is `r > 0` such
that `(γ b - s) / (γ a - s) ∈ Complex.slitPlane` whenever `t₀ - r ≤ a ≤ b < t₀`. Stated with
`a` the left endpoint — the form in which the argument-lift fundamental theorem of calculus
consumes it on the left excised piece. -/
theorem exists_chord_quotient_mem_slitPlane_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_left h_deriv h_at hL (ρ := 1 / 2) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha hab hb ↦ ?_⟩
  exact chord_quotient_mem_slitPlane
    (re_pos_of_norm_sub_one_le_half (hr_close a ⟨ha, by linarith⟩))
    (re_pos_of_norm_sub_one_le_half (hr_close b ⟨by linarith, hb⟩))
    (div_pos_of_neg_of_neg (by linarith) (by linarith))

/-- Along the incoming side of a crossing with left derivative `L`, the boundary argument
`arg (-L / (γ t - s))` tends to `0`. -/
theorem tendsto_arg_neg_tangent_div_chord_nhdsLT (h_at : γ t₀ = s)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    Tendsto (fun t ↦ ((-L) / (γ t - s)).arg) (𝓝[<] t₀) (𝓝 0) := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have hscaled : Tendsto (fun t ↦ (((t₀ - t : ℝ) : ℂ) * ((-L) / (γ t - s))))
      (𝓝[<] t₀) (𝓝 1) := by
    rw [← mul_inv_cancel₀ hL]
    refine (((chord_quotient_tendsto self_notMem_Iio h_deriv h_at).inv₀ hL).const_mul L).congr
      fun t ↦ ?_
    rw [inv_div]
    push_cast
    ring
  have hpos : ∀ᶠ t in 𝓝[<] t₀, 0 < t₀ - t :=
    eventually_nhdsWithin_of_forall fun t ht ↦ sub_pos.mpr ht
  simpa using Complex.tendsto_arg_of_tendsto_ofReal_mul (by simp) hpos hscaled

/-- Along the outgoing side of a crossing with right derivative `L`, the boundary argument
`arg ((γ t - s) / L)` tends to `0`. -/
theorem tendsto_arg_chord_div_tangent_nhdsGT (h_at : γ t₀ = s)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    Tendsto (fun t ↦ ((γ t - s) / L).arg) (𝓝[>] t₀) (𝓝 0) := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have hscaled : Tendsto (fun t ↦ ((((t - t₀)⁻¹ : ℝ) : ℂ) * ((γ t - s) / L)))
      (𝓝[>] t₀) (𝓝 1) := by
    rw [← div_self hL]
    refine ((chord_quotient_tendsto self_notMem_Ioi h_deriv h_at).div_const L).congr fun t ↦ ?_
    push_cast
    ring
  have hpos : ∀ᶠ t in 𝓝[>] t₀, 0 < (t - t₀)⁻¹ :=
    eventually_nhdsWithin_of_forall fun t ht ↦ inv_pos.mpr (sub_pos.mpr ht)
  simpa using Complex.tendsto_arg_of_tendsto_ofReal_mul (by simp) hpos hscaled

/-- **Argument of a quotient by a right chord**: if `τ x → t₀⁺` along `l` and
`w / L ∈ Complex.slitPlane`, then `arg (w / (γ (τ x) - s))` converges to `arg (w / L)`. With
`w = γ (t₀ + r) - s` and `τ` the right exit time of the circle of radius `ε` about `s`, this is
the convergence of the right annular quotient arguments as `ε → 0⁺`. -/
theorem tendsto_arg_div_chord_right {α : Type*} {l : Filter α} {τ : α → ℝ} {w : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s)
    (h_slit : w / L ∈ Complex.slitPlane) (hτ : Tendsto τ l (𝓝[>] t₀)) :
    Tendsto (fun x ↦ (w / (γ (τ x) - s)).arg) l (𝓝 (w / L).arg) := by
  have hL : L ≠ 0 := by rintro rfl; simp at h_slit
  refine Complex.tendsto_arg_of_tendsto_ofReal_mul h_slit
    ((hτ.eventually self_mem_nhdsWithin).mono fun x hx ↦ sub_pos.mpr hx) ?_
  rw [div_eq_mul_inv]
  refine ((((chord_quotient_tendsto self_notMem_Ioi h_deriv h_at).comp hτ).inv₀ hL).const_mul
    w).congr fun x ↦ ?_
  rw [Function.comp_apply, inv_div]
  ring

/-- **Argument of a left chord quotient**: if `τ x → t₀⁻` along `l` and
`-L / w ∈ Complex.slitPlane`, then `arg ((γ (τ x) - s) / w)` converges to `arg (-L / w)`. With
`w = γ (t₀ - r) - s` and `τ` the left exit time of the circle of radius `ε` about `s`, this is
the convergence of the left annular quotient arguments as `ε → 0⁺`. -/
theorem tendsto_arg_chord_div_left {α : Type*} {l : Filter α} {τ : α → ℝ} {w : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s)
    (h_slit : (-L) / w ∈ Complex.slitPlane) (hτ : Tendsto τ l (𝓝[<] t₀)) :
    Tendsto (fun x ↦ ((γ (τ x) - s) / w).arg) l (𝓝 ((-L) / w).arg) := by
  refine Complex.tendsto_arg_of_tendsto_ofReal_mul h_slit
    ((hτ.eventually self_mem_nhdsWithin).mono fun x hx ↦
      neg_pos.mpr (inv_neg''.mpr (sub_neg.mpr hx))) ?_
  refine ((((chord_quotient_tendsto self_notMem_Iio h_deriv h_at).comp hτ).neg).div_const
    w).congr fun x ↦ ?_
  rw [Function.comp_apply]
  push_cast
  ring

/-- **Boundary chord-to-tangent quotients in the slit plane (right)**: there is a window radius
`r > 0` such that `(γ (t₀ + r') - s) / L ∈ Complex.slitPlane` for every `0 < r' ≤ r` — the
`h_slit` input of `tendsto_arg_div_chord_right` at any admissible window radius. -/
theorem exists_chord_div_tangent_mem_slitPlane_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → (γ (t₀ + r') - s) / L ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_right h_deriv h_at hL (ρ := 1 / 2) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le ↦ ?_⟩
  have hq := re_pos_of_norm_sub_one_le_half (hr_close (t₀ + r') ⟨by linarith, by linarith⟩)
  have hr' : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_eq : (γ (t₀ + r') - s) / L =
      ((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((t₀ + r' - t₀ : ℝ) : ℂ))) := by
    rw [add_sub_cancel_left]
    field_simp
  rw [h_eq]
  exact ofReal_mul_mem_slitPlane hr'_pos (Or.inl hq)

/-- **Boundary chord-to-tangent quotients in the slit plane (left)**: there is a window radius
`r > 0` such that `(-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane` for every `0 < r' ≤ r` — the
`h_slit` input of `tendsto_arg_chord_div_left` at any admissible window radius. -/
theorem exists_neg_tangent_div_chord_mem_slitPlane_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_left h_deriv h_at hL (ρ := 1 / 2) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le ↦ ?_⟩
  have hq := re_pos_of_norm_sub_one_le_half (hr_close (t₀ - r') ⟨by linarith, by linarith⟩)
  have hr' : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_eq : (-L) / (γ (t₀ - r') - s) =
      1 / ((γ (t₀ - r') - s) / (L * ((t₀ - r' - t₀ : ℝ) : ℂ))) / ((r' : ℝ) : ℂ) := by
    rw [one_div, inv_div, sub_sub_cancel_left, Complex.ofReal_neg]
    field_simp
  rw [h_eq]
  exact div_ofReal_mem_slitPlane (div_mem_slitPlane_of_re_pos hq (by simp)) hr'_pos

/-- **The per-crossing slit-plane radius package**: at a transverse crossing with non-zero
one-sided derivatives, a single radius `r > 0` carries all four slit-plane properties — the
two-sided chord quotients and the two boundary tangent quotients at every admissible offset —
so a common minimum over the crossings of a pole inherits them all. -/
theorem exists_crossing_slitPlane_radius {γ : ℝ → ℂ} {t₀ : ℝ} {s L_R L_L : ℂ}
    (h_deriv_R : HasDerivWithinAt γ L_R (Ioi t₀) t₀)
    (h_deriv_L : HasDerivWithinAt γ L_L (Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0) :
    ∃ r > 0,
      (∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
        (γ b - s) / (γ a - s) ∈ Complex.slitPlane) ∧
      (∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
        (γ b - s) / (γ a - s) ∈ Complex.slitPlane) ∧
      (∀ r', 0 < r' → r' ≤ r → (γ (t₀ + r') - s) / L_R ∈ Complex.slitPlane) ∧
      (∀ r', 0 < r' → r' ≤ r → (-L_L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane) := by
  obtain ⟨r₁, hr₁_pos, h₁⟩ := exists_chord_quotient_mem_slitPlane_right h_deriv_R h_at hL_R
  obtain ⟨r₂, hr₂_pos, h₂⟩ := exists_chord_quotient_mem_slitPlane_left h_deriv_L h_at hL_L
  obtain ⟨r₃, hr₃_pos, h₃⟩ := exists_chord_div_tangent_mem_slitPlane_right h_deriv_R h_at hL_R
  obtain ⟨r₄, hr₄_pos, h₄⟩ :=
    exists_neg_tangent_div_chord_mem_slitPlane_left h_deriv_L h_at hL_L
  refine ⟨min (min r₁ r₂) (min r₃ r₄), lt_min (lt_min hr₁_pos hr₂_pos) (lt_min hr₃_pos hr₄_pos),
    fun a b ha hab hb ↦ h₁ a b ha hab (hb.trans (by simp)),
    fun a b ha hab hb ↦ h₂ a b ((sub_le_sub_left (by simp) t₀).trans ha) hab hb,
    fun r' hr' hle ↦ h₃ r' hr' (hle.trans (by simp)),
    fun r' hr' hle ↦ h₄ r' hr' (hle.trans (by simp))⟩

end TauCeti.Contour

end
