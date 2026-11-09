/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponential decay of the second derivatives of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. For a vortex on the whole plane with `|α| → 1` at
infinity, the function `ℓ = log |α|²` and its gradient decay exponentially at every rate
`c < 1 / 2` (`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`,
`TauCeti.Vortex.exists_eventually_norm_fderiv_log_normSq_le_mul_exp`). This file proves the same
decay for its second derivatives: outside a compact set,

`‖D² log |α|²‖ ≤ K exp (-c |z|)`.

In the winding end trivialization the connection of a vortex is `(1 / 2) ⋆ dℓ`, so this is the
decay of the first derivatives of the connection there.

The argument works with mixed second differences
`D (w) = ℓ (w + h + k) - ℓ (w + h) - ℓ (w + k) + ℓ (w)` outside a large disc, where `ℓ` solves
the scalar equation `Δ ℓ = (exp ℓ - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`). Writing the differences of `exp ℓ` as
divided differences (`dslope`), `4 Δ D = V D + F`, where the potential `V` is a divided difference
of `exp` at two values of `ℓ`, hence at least `4 c²` outside a large disc
(`Real.exp_min_le_dslope_exp`), and the forcing `F` is quadratic in first differences of `ℓ`
(`Real.abs_exp_sub_exp_sub_exp_add_exp_sub_dslope_mul_le`). For `|k| ≤ |h|` the decay of the
gradient bounds `|F| ≤ C |h| |k| exp (-2 c₁ |z|)`, and the comparison principle with forcing
(`TauCeti.le_mul_exp_of_mul_sub_le_laplacian`) bounds `|D|` by `C' |h| |k| exp (-c |z|)` for every
`c < c₁`. Letting `k → 0` bounds the differences `‖Dℓ (w + h) - Dℓ (w)‖ ≤ C' |h| exp (-c |z|)`,
and letting `h → 0` bounds the second derivative. Only `C²` regularity of the section is used: no
third derivative and no commutation of `Δ` with a derivative is needed.

## Main results

* `TauCeti.Vortex.exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp`: outside a compact
  set, `‖D² log |α|²‖ ≤ K exp (-c |z|)` for every `c < 1 / 2`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology InnerProductSpace Laplacian

/-! ### The linearized equation for mixed second differences -/

variable {ℓ : ℂ → ℝ}

/-- Where `Δ ℓ = (exp ℓ - 1) / 4` at the four corners, the Laplacian of the mixed second
difference of `ℓ` is the mixed second difference of `exp ℓ / 4`. -/
private theorem laplacian_mixedDifference {w h k : ℂ}
    (hcd : ∀ v ∈ ({0, h, k, h + k} : Set ℂ), ContDiffAt ℝ 2 ℓ (w + v))
    (hΔ : ∀ v ∈ ({0, h, k, h + k} : Set ℂ), Δ ℓ (w + v) = (Real.exp (ℓ (w + v)) - 1) / 4) :
    Δ (fun y ↦ ℓ (y + (h + k)) - ℓ (y + h) - ℓ (y + k) + ℓ y) w =
      (Real.exp (ℓ (w + (h + k))) - Real.exp (ℓ (w + h)) - Real.exp (ℓ (w + k)) +
        Real.exp (ℓ w)) / 4 := by
  have htr (v : ℂ) (hv : v ∈ ({0, h, k, h + k} : Set ℂ)) :
      ContDiffAt ℝ 2 (fun y ↦ ℓ (y + v)) w :=
    (hcd v hv).comp w (contDiffAt_id.add contDiffAt_const)
  have h0 : ContDiffAt ℝ 2 ℓ w := by simpa using hcd 0 (by simp)
  -- Split the Laplacian over the four translates of `ℓ`.
  have hfun : (fun y ↦ ℓ (y + (h + k)) - ℓ (y + h) - ℓ (y + k) + ℓ y) =
      (fun y ↦ ℓ (y + (h + k))) - (fun y ↦ ℓ (y + h)) - (fun y ↦ ℓ (y + k)) + ℓ := rfl
  rw [hfun, ContDiffAt.laplacian_add (f₁ := (fun y ↦ ℓ (y + (h + k))) - (fun y ↦ ℓ (y + h)) -
      (fun y ↦ ℓ (y + k))) (((htr _ (by simp)).sub (htr _ (by simp))).sub (htr _ (by simp))) h0,
    ContDiffAt.laplacian_sub (f₁ := (fun y ↦ ℓ (y + (h + k))) - (fun y ↦ ℓ (y + h)))
      ((htr _ (by simp)).sub (htr _ (by simp))) (htr _ (by simp)),
    (htr _ (by simp)).laplacian_sub (htr _ (by simp)),
    congrFun (laplacian_comp_add_right ℓ (h + k)) w, congrFun (laplacian_comp_add_right ℓ h) w,
    congrFun (laplacian_comp_add_right ℓ k) w, hΔ _ (by simp), hΔ _ (by simp), hΔ _ (by simp)]
  have := hΔ 0 (by simp)
  rw [add_zero] at this
  rw [this]
  ring

/-- **Exterior decay of mixed second differences.** Suppose that outside the disc of radius
`R - 2`, `ℓ` is `C²` with values in `[-1, 0]`, solves `Δ ℓ = (exp ℓ - 1) / 4` and has
`exp ℓ ≥ 4 c₁²`; that `ℓ → 0` at infinity; that its first differences are bounded by
`K |v| exp (-c₁ |y|)` near `|y| ≥ R`; and that its mixed second differences are bounded by
`L |h| |k|` on the circle `|z| = R`. Then for `0 < c < c₁`, `|k| ≤ |h| ≤ 1` and `|w| ≥ R`, the mixed
second difference at `w` is at most `(L + 3 K² / (4 (c₁² - c²))) |h| |k| exp (-c (|w| - R))`. -/
private theorem abs_mixedDifference_le_mul_exp {R c c₁ K L : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hcc₁ : c < c₁) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcd : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ContDiffAt ℝ 2 ℓ w)
    (hΔ : ∀ w : ℂ, R - 2 ≤ ‖w‖ → Δ ℓ w = (Real.exp (ℓ w) - 1) / 4)
    (hge : ∀ w : ℂ, R - 2 ≤ ‖w‖ → -1 ≤ ℓ w) (hle : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ℓ w ≤ 0)
    (hmass : ∀ w : ℂ, R - 2 ≤ ‖w‖ → 4 * c₁ ^ 2 ≤ Real.exp (ℓ w))
    (hlim : Tendsto ℓ (cocompact ℂ) (𝓝 0))
    (hdiff : ∀ y u v : ℂ, R ≤ ‖y‖ → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |ℓ (y + u + v) - ℓ (y + u)| ≤ K * ‖v‖ * Real.exp (-(c₁ * ‖y‖)))
    (hbdry : ∀ z h k : ℂ, ‖z‖ = R → ‖h‖ ≤ 1 → ‖k‖ ≤ 1 →
      |ℓ (z + (h + k)) - ℓ (z + h) - ℓ (z + k) + ℓ z| ≤ L * ‖h‖ * ‖k‖)
    {h k : ℂ} (hh : ‖h‖ ≤ 1) (hkh : ‖k‖ ≤ ‖h‖) {w : ℂ} (hw : R ≤ ‖w‖) :
    |ℓ (w + (h + k)) - ℓ (w + h) - ℓ (w + k) + ℓ w| ≤
      (L + 3 * K ^ 2 / (4 * (c₁ ^ 2 - c ^ 2))) * ‖h‖ * ‖k‖ * Real.exp (-(c * (‖w‖ - R))) := by
  set D : ℂ → ℝ := fun y ↦ ℓ (y + (h + k)) - ℓ (y + h) - ℓ (y + k) + ℓ y with hD
  set V : ℂ → ℝ := fun y ↦ dslope Real.exp (ℓ (y + h)) (ℓ (y + (h + k))) / 4 with hV
  set B := 3 * K ^ 2 / 4 * ‖h‖ * ‖k‖ with hB
  have hk : ‖k‖ ≤ 1 := hkh.trans hh
  have hcorner : ∀ y : ℂ, R ≤ ‖y‖ → ∀ v ∈ ({0, h, k, h + k} : Set ℂ), R - 2 ≤ ‖y + v‖ := by
    intro y hy v hv
    have hv2 : ‖v‖ ≤ 2 := by
      rcases hv with rfl | rfl | rfl | rfl
      · simp
      · linarith
      · linarith
      · exact (norm_add_le _ _).trans (by linarith)
    have := norm_sub_norm_le y (-v)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hDcd : ∀ y : ℂ, R ≤ ‖y‖ → ContDiffAt ℝ 2 D y := fun y hy ↦ by
    have htr (v : ℂ) (hv : v ∈ ({0, h, k, h + k} : Set ℂ)) :
        ContDiffAt ℝ 2 (fun y ↦ ℓ (y + v)) y :=
      (hcd _ (hcorner y hy v hv)).comp y (contDiffAt_id.add contDiffAt_const)
    have h0 : ContDiffAt ℝ 2 ℓ y := by simpa using hcd _ (hcorner y hy 0 (by simp))
    exact (((htr _ (by simp)).sub (htr _ (by simp))).sub (htr _ (by simp))).add h0
  -- `4 Δ D = 4 V D + F` with `|F| ≤ 4 B exp (-c (|y| - R))`.
  have hforce : ∀ y : ℂ, R ≤ ‖y‖ →
      |Δ D y - V y * D y| ≤ B * Real.exp (-(c * (‖y‖ - R))) := by
    intro y hy
    have hc' := hcorner y hy
    rw [hD, laplacian_mixedDifference (fun v hv ↦ hcd _ (hc' v hv))
      (fun v hv ↦ hΔ _ (hc' v hv))]
    have hab : ∀ u v : ℝ, -1 ≤ u → u ≤ 0 → -1 ≤ v → v ≤ 0 → |u - v| ≤ 1 := fun u v h₁ h₂ h₃ h₄ ↦
      abs_le.mpr ⟨by linarith, by linarith⟩
    have ha := hle y (by simpa using hc' 0 (by simp))
    have ha' := hge y (by simpa using hc' 0 (by simp))
    have hb := hle _ (hc' h (by simp))
    have hb' := hge _ (hc' h (by simp))
    have hc₀ := hle _ (hc' k (by simp))
    have hc₀' := hge _ (hc' k (by simp))
    have hd := hle _ (hc' (h + k) (by simp))
    have hd' := hge _ (hc' (h + k) (by simp))
    have hmain := Real.abs_exp_sub_exp_sub_exp_add_exp_sub_dslope_mul_le ha hb
      (hab _ _ hd' hd hb' hb) (hab _ _ hc₀' hc₀ ha' ha)
    -- The first differences, from `hdiff`.
    set E := Real.exp (-(c₁ * ‖y‖))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hca : |ℓ (y + k) - ℓ y| ≤ K * ‖k‖ * E := by
      simpa using hdiff y 0 k hy (by simp) hk
    have hba : |ℓ (y + h) - ℓ y| ≤ K * ‖h‖ * E := by
      simpa using hdiff y 0 h hy (by simp) hh
    have hdb : |ℓ (y + (h + k)) - ℓ (y + h)| ≤ K * ‖k‖ * E := by
      simpa [add_assoc] using hdiff y h k hy hh hk
    have hE2 : E ^ 2 ≤ Real.exp (-(c * (‖y‖ - R))) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      push_cast
      nlinarith [norm_nonneg y]
    have hsum : |ℓ (y + (h + k)) - ℓ (y + h)| + |ℓ (y + h) - ℓ y| + |ℓ (y + k) - ℓ y| ≤
        3 * K * ‖h‖ * E := by
      have : K * ‖k‖ * E ≤ K * ‖h‖ * E := by gcongr
      linarith
    have hF : |ℓ (y + k) - ℓ y| * (|ℓ (y + (h + k)) - ℓ (y + h)| + |ℓ (y + h) - ℓ y| +
        |ℓ (y + k) - ℓ y|) ≤ 4 * B * Real.exp (-(c * (‖y‖ - R))) :=
      calc _ ≤ (K * ‖k‖ * E) * (3 * K * ‖h‖ * E) :=
            mul_le_mul hca hsum (by positivity) (by positivity)
        _ = 4 * B * E ^ 2 := by rw [hB]; ring
        _ ≤ 4 * B * Real.exp (-(c * (‖y‖ - R))) :=
            mul_le_mul_of_nonneg_left hE2 (by positivity)
    simp only [hV]
    rw [show ∀ s g d : ℝ, s / 4 - g / 4 * d = (s - g * d) / 4 from fun s g d ↦ by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num)]
    linarith
  -- The potential is at least `c₁²`.
  have hVc : ∀ y : ℂ, R < ‖y‖ → c₁ ^ 2 ≤ V y := fun y hy ↦ by
    have hmin := Real.exp_min_le_dslope_exp (ℓ (y + h)) (ℓ (y + (h + k)))
    have h₁ := hmass _ (hcorner y hy.le h (by simp))
    have h₂ := hmass _ (hcorner y hy.le (h + k) (by simp))
    have : 4 * c₁ ^ 2 ≤ Real.exp (min (ℓ (y + h)) (ℓ (y + (h + k)))) := by
      rcases min_choice (ℓ (y + h)) (ℓ (y + (h + k))) with h' | h' <;> rw [h'] <;> assumption
    simp only [hV]
    linarith
  -- Both `D` and `-D` are forced subsolutions tending to zero and bounded on the circle.
  have hcont : ContinuousOn D {y | R ≤ ‖y‖} := fun y hy ↦
    (hDcd y hy).continuousAt.continuousWithinAt
  have hDlim : Tendsto D (cocompact ℂ) (𝓝 0) := by
    have htr (v : ℂ) : Tendsto (fun y ↦ ℓ (y + v)) (cocompact ℂ) (𝓝 0) :=
      hlim.comp (Homeomorph.addRight v).isClosedEmbedding.tendsto_cocompact
    simpa using (((htr (h + k)).sub (htr h)).sub (htr k)).add hlim
  have hM : 0 ≤ L * ‖h‖ * ‖k‖ := by positivity
  have hB₀ : 0 ≤ B := by positivity
  have hup := le_mul_exp_of_mul_sub_le_laplacian hR hc hcc₁ hM hB₀ hcont
    (fun y hy ↦ hDcd y hy.le) hVc
    (fun y hy ↦ by linarith [(abs_le.mp (hforce y hy.le)).1])
    (fun y hy ↦ (le_abs_self _).trans (hbdry y h k hy hh hk)) hDlim hw
  have hdown := le_mul_exp_of_mul_sub_le_laplacian (u := -D) hR hc hcc₁ hM hB₀ hcont.neg
    (fun y hy ↦ (hDcd y hy.le).neg) hVc
    (fun y hy ↦ by
      rw [laplacian_neg, Pi.neg_apply, Pi.neg_apply]
      linarith [(abs_le.mp (hforce y hy.le)).2])
    (fun y hy ↦ (neg_le_abs _).trans (hbdry y h k hy hh hk))
    (by have h := hDlim.neg; rwa [neg_zero] at h) hw
  have hgap : 0 < c₁ ^ 2 - c ^ 2 := by nlinarith
  have heq : (L * ‖h‖ * ‖k‖ + B / (c₁ ^ 2 - c ^ 2)) =
      (L + 3 * K ^ 2 / (4 * (c₁ ^ 2 - c ^ 2))) * ‖h‖ * ‖k‖ := by
    rw [hB]
    field_simp
  rw [heq] at hup hdown
  simp only [Pi.neg_apply] at hdown
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- Bounds `|ℓ (w + h + k) - ℓ (w + h) - ℓ (w + k) + ℓ w| ≤ C |h| |k|` for `|k| ≤ |h| ≤ 1` bound the
second derivative at `w` by `C`: letting `k → 0` bounds `‖Dℓ (w + h) - Dℓ w‖ ≤ C |h|`, and letting
`h → 0` bounds `‖D² ℓ (w)‖`. -/
private theorem norm_fderiv_fderiv_le_of_abs_mixedDifference_le {w : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ v : ℂ, ‖v‖ ≤ 1 → DifferentiableAt ℝ ℓ (w + v))
    (hd2 : DifferentiableAt ℝ (fderiv ℝ ℓ) w)
    (hmixed : ∀ h k : ℂ, ‖h‖ ≤ 1 → ‖k‖ ≤ ‖h‖ →
      |ℓ (w + (h + k)) - ℓ (w + h) - ℓ (w + k) + ℓ w| ≤ C * ‖h‖ * ‖k‖) :
    ‖fderiv ℝ (fderiv ℝ ℓ) w‖ ≤ C := by
  -- The gradient differences: `y ↦ ℓ (y + h) - ℓ y` is `C |h|`-Lipschitz on the ball of radius
  -- `|h|` about `w`.
  have hlip : ∀ h : ℂ, ‖h‖ ≤ 1 → ‖fderiv ℝ ℓ (w + h) - fderiv ℝ ℓ w‖ ≤ C * ‖h‖ := by
    intro h hh
    rcases eq_or_ne h 0 with rfl | hh₀
    · simp
    have hg : HasFDerivAt (fun y ↦ ℓ (y + h) - ℓ y) (fderiv ℝ ℓ (w + h) - fderiv ℝ ℓ w) w :=
      ((hasFDerivAt_comp_add_right h).mpr (hd h hh).hasFDerivAt).sub
        (by simpa using (hd 0 (by simp)).hasFDerivAt)
    refine hg.le_of_lip' (by positivity) ?_
    filter_upwards [ball_mem_nhds w (norm_pos_iff.mpr hh₀)] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h' := hmixed h (y - w) hh hy.le
    rw [show w + (h + (y - w)) = y + h by abel, show w + (y - w) = y by abel] at h'
    rw [Real.norm_eq_abs]
    calc |ℓ (y + h) - ℓ y - (ℓ (w + h) - ℓ w)| = |ℓ (y + h) - ℓ (w + h) - ℓ y + ℓ w| := by
          ring_nf
      _ ≤ C * ‖h‖ * ‖y - w‖ := h'
  -- The gradient is `C`-Lipschitz near `w`.
  refine hd2.hasFDerivAt.le_of_lip' hC ?_
  filter_upwards [closedBall_mem_nhds w one_pos] with y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  simpa using hlip (y - w) hy

/-- **First differences from the gradient.** If `ℓ` is `C²` outside the disc of radius `R - 2`
with `‖Dℓ (w)‖ ≤ K₀ exp (-c₁ |w|)` there, then near `|y| ≥ R` its first differences satisfy
`|ℓ (y + u + v) - ℓ (y + u)| ≤ K₀ exp (2 c₁) |v| exp (-c₁ |y|)` for `|u|, |v| ≤ 1`. -/
private theorem abs_sub_le_mul_exp_of_norm_fderiv_le {R c₁ K₀ : ℝ} (hc₁ : 0 ≤ c₁) (hK₀ : 0 ≤ K₀)
    (hcd : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ContDiffAt ℝ 2 ℓ w)
    (hgrad : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ‖fderiv ℝ ℓ w‖ ≤ K₀ * Real.exp (-(c₁ * ‖w‖)))
    {y u v : ℂ} (hy : R ≤ ‖y‖) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |ℓ (y + u + v) - ℓ (y + u)| ≤ K₀ * Real.exp (2 * c₁) * ‖v‖ * Real.exp (-(c₁ * ‖y‖)) := by
  -- Points of the unit ball about `y + u` lie within distance `2` of `y`.
  have hnear : ∀ p ∈ closedBall (y + u) 1, ‖y‖ - 2 ≤ ‖p‖ := fun p hp ↦ by
    rw [mem_closedBall, dist_eq_norm] at hp
    have h₁ : ‖p - y‖ ≤ 2 := by
      calc ‖p - y‖ = ‖(p - (y + u)) + u‖ := by congr 1; abel
        _ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    have h₂ := norm_sub_norm_le y p
    rw [norm_sub_rev] at h₂
    linarith
  have hbound : ∀ p ∈ closedBall (y + u) 1,
      ‖fderiv ℝ ℓ p‖ ≤ K₀ * Real.exp (2 * c₁) * Real.exp (-(c₁ * ‖y‖)) := fun p hp ↦ by
    have hpy := hnear p hp
    calc ‖fderiv ℝ ℓ p‖ ≤ K₀ * Real.exp (-(c₁ * ‖p‖)) := hgrad p (by linarith)
      _ ≤ K₀ * Real.exp (-(c₁ * (‖y‖ - 2))) := by gcongr
      _ = K₀ * Real.exp (2 * c₁) * Real.exp (-(c₁ * ‖y‖)) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf
  have h := (convex_closedBall (y + u) 1).norm_image_sub_le_of_norm_fderiv_le (f := ℓ)
    (fun p hp ↦ (hcd p (by linarith [hnear p hp])).differentiableAt (by norm_num)) hbound
    (mem_closedBall_self zero_le_one)
    (by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left] : y + u + v ∈ closedBall (y + u) 1)
  rw [add_sub_cancel_left, Real.norm_eq_abs] at h
  linarith

/-- **Mixed second differences on a circle.** If `ℓ` is `C²` outside the disc of radius `R - 2`,
its mixed second differences at points of the circle `|z| = R` are bounded by `L |h| |k|` for
`|h|, |k| ≤ 1`, where `L` bounds the second derivative on the annulus `R - 2 ≤ |w| ≤ R + 2`. -/
private theorem exists_abs_mixedDifference_le_of_norm_eq {R : ℝ}
    (hcd : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ContDiffAt ℝ 2 ℓ w) :
    ∃ L, 0 ≤ L ∧ ∀ z h k : ℂ, ‖z‖ = R → ‖h‖ ≤ 1 → ‖k‖ ≤ 1 →
      |ℓ (z + (h + k)) - ℓ (z + h) - ℓ (z + k) + ℓ z| ≤ L * ‖h‖ * ‖k‖ := by
  set A : Set ℂ := closedBall 0 (R + 2) ∩ {w | R - 2 ≤ ‖w‖}
  have hAc : IsCompact A := (isCompact_closedBall 0 (R + 2)).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hd2 : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ContDiffAt ℝ 1 (fderiv ℝ ℓ) w := fun w hw ↦
    (hcd w hw).fderiv_right (m := 1) (by norm_num)
  obtain ⟨L₀, hL₀⟩ := hAc.exists_bound_of_continuousOn (f := fun w ↦ fderiv ℝ (fderiv ℝ ℓ) w)
    fun w hw ↦ ((hd2 w hw.2).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  set L := max L₀ 0
  refine ⟨L, le_max_right _ _, fun z h k hz hh hk ↦ ?_⟩
  -- Points within distance `2` of the circle lie in the annulus.
  have hA : ∀ p, ‖p - z‖ ≤ 2 → p ∈ A := fun p hp ↦ by
    have := abs_norm_sub_norm_le p z
    rw [abs_le] at this
    exact ⟨mem_closedBall_zero_iff.mpr (by linarith), show R - 2 ≤ ‖p‖ by linarith⟩
  -- The gradient differences `Dℓ (y + h) - Dℓ y` are bounded by `L |h|` for `|y - z| ≤ 1`.
  have hg : ∀ y ∈ closedBall z 1, ‖fderiv ℝ ℓ (y + h) - fderiv ℝ ℓ y‖ ≤ L * ‖h‖ := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have hsub : closedBall y 1 ⊆ A := fun p hp ↦ by
      rw [mem_closedBall, dist_eq_norm] at hp
      refine hA p ?_
      calc ‖p - z‖ = ‖(p - y) + (y - z)‖ := by congr 1; abel
        _ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    have hmv := (convex_closedBall y 1).norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ ℓ)
      (C := L) (fun p hp ↦ (hd2 p (hsub hp).2).differentiableAt (by norm_num))
      (fun p hp ↦ (hL₀ p (hsub hp)).trans (le_max_left L₀ 0))
      (mem_closedBall_self zero_le_one)
      (by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left] : y + h ∈ closedBall y 1)
    rwa [add_sub_cancel_left] at hmv
  have hgd : ∀ y ∈ closedBall z 1, HasFDerivAt (fun y ↦ ℓ (y + h) - ℓ y)
      (fderiv ℝ ℓ (y + h) - fderiv ℝ ℓ y) y := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have hy₁ : R - 2 ≤ ‖y‖ := (hA y (by linarith)).2
    have hy₂ : R - 2 ≤ ‖y + h‖ := (hA (y + h) (by
      calc ‖y + h - z‖ = ‖(y - z) + h‖ := by congr 1; abel
        _ ≤ 2 := (norm_add_le _ _).trans (by linarith))).2
    exact ((hasFDerivAt_comp_add_right h).mpr
      ((hcd _ hy₂).differentiableAt (by norm_num)).hasFDerivAt).sub
      ((hcd y hy₁).differentiableAt (by norm_num)).hasFDerivAt
  -- The mean value inequality for `y ↦ ℓ (y + h) - ℓ y` along `[z, z + k]`.
  have hmv := (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le
    (f := fun y ↦ ℓ (y + h) - ℓ y)
    (fun y hy ↦ (hgd y hy).differentiableAt)
    (fun y hy ↦ (hgd y hy).fderiv ▸ hg y hy)
    (mem_closedBall_self zero_le_one)
    (by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left] : z + k ∈ closedBall z 1)
  rw [add_sub_cancel_left, Real.norm_eq_abs] at hmv
  rw [show z + (h + k) = z + k + h by abel]
  calc |ℓ (z + k + h) - ℓ (z + h) - ℓ (z + k) + ℓ z| =
        |ℓ (z + k + h) - ℓ (z + k) - (ℓ (z + h) - ℓ z)| := by ring_nf
    _ ≤ L * ‖h‖ * ‖k‖ := hmv

/-! ### Decay of the second derivatives of `log |α|²` -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The case `0 < c` of `exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp`. -/
private theorem exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp_of_pos
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc₀ : 0 < c) (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2) with hs
  set ℓ : ℂ → ℝ := fun z ↦ Real.log (s z) with hℓ
  have hscd : ContDiff ℝ 2 s := contDiff_normSq hp hq
  set c₁ := (c + 1 / 2) / 2 with hc₁
  have hcc₁ : c < c₁ := by linarith
  have hc₁' : c₁ < 1 / 2 := by linarith
  -- Beyond `R₁` the gradient of `ℓ` decays at the rate `c₁`; beyond `R₂`, `|α|²` is close to `1`.
  obtain ⟨K₀, hK₀⟩ := exists_eventually_norm_fderiv_log_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim
    hc₁'
  obtain ⟨R₁, -, hR₁⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hK₀)
  have hθ : max (4 * c₁ ^ 2) (Real.exp (-1)) < 1 :=
    max_lt (by nlinarith) (Real.exp_lt_one_iff.mpr (by norm_num))
  obtain ⟨R₂, -, hR₂⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hlim.eventually (lt_mem_nhds hθ))
  set R := max (max R₁ R₂) 0 + 3 with hR
  have hR₀ : 0 < R := by positivity
  have hRmax : ∀ w : ℂ, R - 2 ≤ ‖w‖ → max (max R₁ R₂) 0 ≤ ‖w‖ := fun w hw ↦ by linarith
  have hRR₁ : ∀ w : ℂ, R - 2 ≤ ‖w‖ → R₁ ≤ ‖w‖ := fun w hw ↦
    ((le_max_left R₁ R₂).trans (le_max_left _ 0)).trans (hRmax w hw)
  have hsR : ∀ w : ℂ, R - 2 ≤ ‖w‖ → max (4 * c₁ ^ 2) (Real.exp (-1)) < s w := fun w hw ↦
    hR₂ (((le_max_right R₁ R₂).trans (le_max_left _ 0)).trans (hRmax w hw))
  have hpos : ∀ w : ℂ, R - 2 ≤ ‖w‖ → 0 < s w := fun w hw ↦
    (lt_max_of_lt_right (Real.exp_pos _)).trans (hsR w hw)
  have hexp : ∀ w : ℂ, R - 2 ≤ ‖w‖ → Real.exp (ℓ w) = s w := fun w hw ↦
    Real.exp_log (hpos w hw)
  have hℓcd : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ContDiffAt ℝ 2 ℓ w := fun w hw ↦
    hscd.contDiffAt.log (hpos w hw).ne'
  have hΔ : ∀ w : ℂ, R - 2 ≤ ‖w‖ → Δ ℓ w = (Real.exp (ℓ w) - 1) / 4 := fun w hw ↦ by
    rw [hexp w hw]
    exact laplacian_log_normSq_of_equation_eq_zero (hb₁ w) (hb₂ w) hp.contDiffAt hq.contDiffAt
      (right_ne_zero_of_mul (hpos w hw).ne') (Eventually.of_forall hsol)
  have hge : ∀ w : ℂ, R - 2 ≤ ‖w‖ → -1 ≤ ℓ w := fun w hw ↦
    (Real.le_log_iff_exp_le (hpos w hw)).mpr ((le_max_right _ _).trans (hsR w hw).le)
  have hle : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ℓ w ≤ 0 := fun w hw ↦
    Real.log_nonpos (hpos w hw).le (normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim w)
  have hmass : ∀ w : ℂ, R - 2 ≤ ‖w‖ → 4 * c₁ ^ 2 ≤ Real.exp (ℓ w) := fun w hw ↦ by
    rw [hexp w hw]
    exact (le_max_left _ _).trans (hsR w hw).le
  have hℓlim : Tendsto ℓ (cocompact ℂ) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    rwa [Real.log_one] at h
  -- The first differences of `ℓ` decay, and its mixed second differences are bounded on the
  -- circle `|z| = R`.
  set K := max K₀ 0 * Real.exp (2 * c₁) with hK
  have hK₀' : 0 ≤ K := by positivity
  have hdiff : ∀ y u v : ℂ, R ≤ ‖y‖ → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |ℓ (y + u + v) - ℓ (y + u)| ≤ K * ‖v‖ * Real.exp (-(c₁ * ‖y‖)) := fun y u v hy hu hv ↦
    abs_sub_le_mul_exp_of_norm_fderiv_le (by linarith) (le_max_right _ _) hℓcd
      (fun w hw ↦ (hR₁ (hRR₁ w hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)) hy hu hv
  obtain ⟨L, hL, hbdry⟩ := exists_abs_mixedDifference_le_of_norm_eq hℓcd
  have hd2 : ∀ w : ℂ, R - 2 ≤ ‖w‖ → ContDiffAt ℝ 1 (fderiv ℝ ℓ) w := fun w hw ↦
    (hℓcd w hw).fderiv_right (m := 1) (by norm_num)
  -- Combine the mixed-difference decay with the two limiting arguments.
  set C := L + 3 * K ^ 2 / (4 * (c₁ ^ 2 - c ^ 2)) with hC
  have hgap : 0 < c₁ ^ 2 - c ^ 2 := by
    rw [sq_sub_sq]
    exact mul_pos (by linarith) (sub_pos.mpr hcc₁)
  have hC₀ : 0 ≤ C := by positivity
  refine ⟨C * Real.exp (c * R), ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop R] with w hw
  set E := Real.exp (-(c * (‖w‖ - R)))
  have hmixed := fun (h k : ℂ) (hh : ‖h‖ ≤ 1) (hkh : ‖k‖ ≤ ‖h‖) ↦
    abs_mixedDifference_le_mul_exp hR₀ hc₀ hcc₁ hK₀' hL hℓcd hΔ hge hle hmass
      hℓlim hdiff hbdry hh hkh hw
  have hdv : ∀ v : ℂ, ‖v‖ ≤ 1 → DifferentiableAt ℝ ℓ (w + v) := fun v hv ↦ by
    have := norm_sub_norm_le w (-v)
    rw [norm_neg, sub_neg_eq_add] at this
    exact (hℓcd _ (by linarith)).differentiableAt (by norm_num)
  have h2 := norm_fderiv_fderiv_le_of_abs_mixedDifference_le (C := C * E) (by positivity) hdv
    ((hd2 w (by linarith)).differentiableAt (by norm_num))
    (fun h k hh hkh ↦ (hmixed h k hh hkh).trans_eq (by ring))
  calc ‖fderiv ℝ (fderiv ℝ ℓ) w‖ ≤ C * E := h2
    _ = C * Real.exp (c * R) * Real.exp (-(c * ‖w‖)) := by
        rw [mul_assoc, ← exp_neg_mul_sub]

/-- **Exponential decay of the second derivatives of `log |α|²`.** Outside a compact set, a
vortex on the whole plane whose section satisfies `|α| → 1` at infinity has
`‖D² log |α|²‖ ≤ K exp (-c |z|)`, for every rate `c < 1 / 2`. -/
theorem exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp_of_pos hb₁ hb₂ hp
    hq hsol hlim (lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1 / 4))
    (max_lt hc (by norm_num))
  refine ⟨max K 0, hK.mono fun z hz ↦ hz.trans ?_⟩
  gcongr
  · exact le_max_left _ _
  · exact le_max_left _ _

end TauCeti.Vortex
