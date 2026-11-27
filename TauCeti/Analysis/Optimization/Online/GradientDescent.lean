/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Analysis.InnerProductSpace.Projection.MetricProj
public import TauCeti.Analysis.Optimization.Online.Regret
import TauCeti.Analysis.Real.SumInvSqrt

/-!
# Online gradient descent

Let `K` be a complete convex subset of a real inner product space `E`. Online gradient descent
with steps `η t`, driven by vectors `g t`, starts at `x₀` and moves from the iterate `x t`
against `g t` and back onto `K`:

`x 0 = x₀` and `x (t + 1) = metricProj K (x t - η t • g t)`.

The vector `g t` is meant to be a subgradient, at `x t`, of the loss `f t` revealed after `x t`
is played. Since `x t` depends only on `g s` for `s < t`, the losses may be chosen adaptively.
The start `x₀` need not lie in `K`; every later iterate does when `K` is nonempty.

The projection inequality gives the one-step inequality
`‖x (t + 1) - u‖ ^ 2 ≤ ‖x t - u‖ ^ 2 - 2 * η t * ⟪g t, x t - u⟫ + η t ^ 2 * ‖g t‖ ^ 2` for every
`u ∈ K`. With a constant step `η > 0` the squared distances telescope, and against every
`u ∈ K`

`regret f x T u ≤ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑_{t < T} ‖g t‖ ^ 2`.

If `‖g t‖ ≤ G` and `‖u - x₀‖ ≤ D`, the step `η = D / (G * √T)` balances the two terms and gives
regret at most `D * G * √T` after `T` rounds.

Non-increasing steps need no knowledge of the horizon `T`, at the price of a bounded domain: if
`D` bounds the distance from `u` to `x₀` and to every point of `K`, then

`regret f x T u ≤ D ^ 2 / (2 * η (T - 1)) + ∑_{t < T} η t / 2 * ‖g t‖ ^ 2`,

because the squared distances to `u` now telescope with the non-negative weights
`1 / (2 * η t) - 1 / (2 * η (t - 1))`. The steps `η t = D / (G * √(t + 1))` give regret at most
`3 / 2 * D * G * √T` for every `T`.

## Main definitions

* `TauCeti.OnlineConvexOptimization.ogd K η g x₀`: the iterates of online gradient descent.

## Main results

* `TauCeti.OnlineConvexOptimization.norm_ogd_succ_sub_sq_le`: the one-step inequality, for any
  steps.
* `TauCeti.OnlineConvexOptimization.sum_inner_ogd_sub_le`: the regret bound with a constant step
  on the linear losses `⟪g t, ·⟫`.
* `TauCeti.OnlineConvexOptimization.regret_ogd_le`: the regret bound with a constant step on
  convex losses with subgradients `g t`.
* `TauCeti.OnlineConvexOptimization.regret_ogd_le_mul_sqrt`: the regret bound `D * G * √T` with
  the step `D / (G * √T)`.
* `TauCeti.OnlineConvexOptimization.inner_ogd_sub_le`: the one-step inequality divided by the
  step.
* `TauCeti.OnlineConvexOptimization.regret_ogd_le_of_antitone`: the regret bound with
  non-increasing steps on a bounded domain, and its linear form
  `TauCeti.OnlineConvexOptimization.sum_inner_ogd_sub_le_of_antitone`.
* `TauCeti.OnlineConvexOptimization.regret_ogd_le_three_halves`: the regret bound
  `3 / 2 * D * G * √T` with the steps `D / (G * √(t + 1))`.

## References

* F. Orabona, *A modern introduction to online learning*, arXiv:1912.13213, Theorem 2.13 (both
  bounds) and equation (2.1), with Lemma 2.31 for subgradients.
* E. Hazan, *Introduction to online convex optimization*, 2nd ed., MIT Press, 2022, Chapter 3,
  Theorem 3.1 for the bound `3 / 2 * G * D * √T`.
* M. Zinkevich, *Online convex programming and generalized infinitesimal gradient ascent*,
  ICML 2003, Theorem 1 for the steps `1 / √(t + 1)`.
-/

public section

open Finset
open scoped RealInnerProductSpace

namespace TauCeti.OnlineConvexOptimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}

/-- The iterates of online gradient descent on `K` with steps `η`, driven by the vectors `g` and
started at `x₀`: `x 0 = x₀` and `x (t + 1) = metricProj K (x t - η t • g t)`. -/
noncomputable def ogd (K : Set E) (η : ℕ → ℝ) (g : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 => metricProj K (ogd K η g x₀ t - η t • g t)

@[simp]
theorem ogd_zero (K : Set E) (η : ℕ → ℝ) (g : ℕ → E) (x₀ : E) : ogd K η g x₀ 0 = x₀ :=
  (rfl)

@[simp]
theorem ogd_succ (K : Set E) (η : ℕ → ℝ) (g : ℕ → E) (x₀ : E) (t : ℕ) :
    ogd K η g x₀ (t + 1) = metricProj K (ogd K η g x₀ t - η t • g t) :=
  (rfl)

/-- Every iterate of online gradient descent after the start lies in `K`, when `K` is a
nonempty complete convex set. -/
theorem ogd_succ_mem (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (η : ℕ → ℝ)
    (g : ℕ → E) (x₀ : E) (t : ℕ) : ogd K η g x₀ (t + 1) ∈ K := by
  rw [ogd_succ]
  exact metricProj_mem hne hc hK _

/-- **The one-step inequality of online gradient descent.** If `K` is complete and convex and
`u ∈ K`, then for any steps `η`,
`‖x (t + 1) - u‖ ^ 2 ≤ ‖x t - u‖ ^ 2 - 2 * η t * ⟪g t, x t - u⟫ + η t ^ 2 * ‖g t‖ ^ 2`,
where `x = ogd K η g x₀`. -/
theorem norm_ogd_succ_sub_sq_le (hc : IsComplete K) (hK : Convex ℝ K) (η : ℕ → ℝ) (g : ℕ → E)
    (x₀ : E) (t : ℕ) {u : E} (hu : u ∈ K) :
    ‖ogd K η g x₀ (t + 1) - u‖ ^ 2 ≤
      ‖ogd K η g x₀ t - u‖ ^ 2 - 2 * η t * ⟪g t, ogd K η g x₀ t - u⟫ +
        η t ^ 2 * ‖g t‖ ^ 2 := by
  have hproj := norm_metricProj_sub_sq_add_norm_sub_metricProj_sq_le hc hK
    (ogd K η g x₀ t - η t • g t) hu
  have hexp : ‖ogd K η g x₀ t - η t • g t - u‖ ^ 2 =
      ‖ogd K η g x₀ t - u‖ ^ 2 - 2 * η t * ⟪g t, ogd K η g x₀ t - u⟫ +
        η t ^ 2 * ‖g t‖ ^ 2 := by
    rw [sub_right_comm, norm_sub_sq_real]
    simp only [real_inner_smul_left, real_inner_comm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [ogd_succ, ← hexp]
  linarith [sq_nonneg ‖ogd K η g x₀ t - η t • g t - metricProj K (ogd K η g x₀ t - η t • g t)‖]

/-- **The regret bound of online gradient descent with a constant step** on linear losses. If
`K` is complete and convex, `η > 0` and `u ∈ K`, then the iterates `x = ogd K (fun _ ↦ η) g x₀`
satisfy
`∑_{t < T} ⟪g t, x t - u⟫ ≤ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑_{t < T} ‖g t‖ ^ 2`. -/
theorem sum_inner_ogd_sub_le (hc : IsComplete K) (hK : Convex ℝ K) (x₀ : E) {η : ℝ}
    (hη : 0 < η) (g : ℕ → E) (T : ℕ) {u : E} (hu : u ∈ K) :
    ∑ t ∈ range T, ⟪g t, ogd K (fun _ ↦ η) g x₀ t - u⟫ ≤
      ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ‖g t‖ ^ 2 := by
  -- Summing the one-step inequality, the squared distances to `u` telescope.
  have htel : ∀ n, 2 * η * ∑ t ∈ range n, ⟪g t, ogd K (fun _ ↦ η) g x₀ t - u⟫ +
      ‖ogd K (fun _ ↦ η) g x₀ n - u‖ ^ 2 ≤ ‖x₀ - u‖ ^ 2 + η ^ 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := norm_ogd_succ_sub_sq_le hc hK (fun _ ↦ η) g x₀ n hu
      simp only [sum_range_succ]
      linarith
  have hrhs : ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ‖g t‖ ^ 2 =
      (‖x₀ - u‖ ^ 2 + η ^ 2 * ∑ t ∈ range T, ‖g t‖ ^ 2) / (2 * η) := by
    rw [norm_sub_rev]
    field_simp
  rw [hrhs, le_div_iff₀ (by positivity)]
  linarith [htel T, sq_nonneg ‖ogd K (fun _ ↦ η) g x₀ T - u‖]

/-- **The regret bound of online gradient descent with a constant step.** If `K` is complete and
convex, `η > 0`, and `u ∈ K` is a comparator at which each `g t` with `t < T` satisfies the
subgradient inequality `f t (x t) + ⟪g t, u - x t⟫ ≤ f t u` of the loss `f t` at the iterate
`x t` of `x = ogd K (fun _ ↦ η) g x₀`, then
`regret f x T u ≤ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑_{t < T} ‖g t‖ ^ 2`. This holds in particular
when each `g t` is a subgradient of `f t` at `x t` relative to `K`. -/
theorem regret_ogd_le (hc : IsComplete K) (hK : Convex ℝ K) (x₀ : E) {η : ℝ} (hη : 0 < η)
    (g : ℕ → E) (f : ℕ → E → ℝ) {T : ℕ} {u : E} (hu : u ∈ K)
    (hf : ∀ t < T, f t (ogd K (fun _ ↦ η) g x₀ t) + ⟪g t, u - ogd K (fun _ ↦ η) g x₀ t⟫ ≤
      f t u) :
    regret f (ogd K (fun _ ↦ η) g x₀) T u ≤
      ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ‖g t‖ ^ 2 :=
  (regret_le_sum_inner_sub f _ g hf).trans (sum_inner_ogd_sub_le hc hK x₀ hη g T hu)

/-- **The `D * G * √T` regret bound of online gradient descent.** If `K` is complete and convex,
`u ∈ K` with `‖u - x₀‖ ≤ D`, and `‖g t‖ ≤ G` for `t < T`, then with the constant step
`η = D / (G * √T)` the iterates `x = ogd K (fun _ ↦ η) g x₀` satisfy `regret f x T u ≤ D * G * √T`,
provided each `g t` with `t < T` satisfies the subgradient inequality
`f t (x t) + ⟪g t, u - x t⟫ ≤ f t u` of the loss `f t` at `x t`. -/
theorem regret_ogd_le_mul_sqrt (hc : IsComplete K) (hK : Convex ℝ K) (x₀ : E) (g : ℕ → E)
    (f : ℕ → E → ℝ) {D G : ℝ} {T : ℕ} (hg : ∀ t < T, ‖g t‖ ≤ G) {u : E} (hu : u ∈ K)
    (hD : ‖u - x₀‖ ≤ D)
    (hf : ∀ t < T, f t (ogd K (fun _ ↦ D / (G * √T)) g x₀ t) +
      ⟪g t, u - ogd K (fun _ ↦ D / (G * √T)) g x₀ t⟫ ≤ f t u) :
    regret f (ogd K (fun _ ↦ D / (G * √T)) g x₀) T u ≤ D * G * √T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hg 0 hT)
  rcases hD0.eq_or_lt with rfl | hDpos
  · -- With `D = 0` the comparator is the start and the step is `0`, so every iterate is `u`.
    obtain rfl : x₀ = u := (sub_eq_zero.1 (norm_le_zero_iff.1 hD)).symm
    have hx : ∀ t, ogd K (fun _ ↦ 0) g x₀ t = x₀ := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => simp [ih, hu]
    simp [regret_def, hx]
  rcases hG0.eq_or_lt with rfl | hGpos
  · -- With `G = 0` every `g t` vanishes, and so does the regret on the linear losses.
    refine (regret_le_sum_inner_sub f _ g hf).trans (le_of_eq ?_)
    rw [mul_zero, zero_mul]
    exact sum_eq_zero fun t ht ↦ by
      rw [norm_le_zero_iff.1 (hg t (mem_range.1 ht)), inner_zero_left]
  have hsqrt : 0 < √(T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hT)
  refine (regret_ogd_le hc hK x₀ (div_pos hDpos (mul_pos hGpos hsqrt)) g f hu hf).trans ?_
  have hsum : ∑ t ∈ range T, ‖g t‖ ^ 2 ≤ T * G ^ 2 := by
    calc ∑ t ∈ range T, ‖g t‖ ^ 2 ≤ ∑ _ ∈ range T, G ^ 2 :=
          sum_le_sum fun t ht ↦ pow_le_pow_left₀ (norm_nonneg _) (hg t (mem_range.1 ht)) 2
      _ = T * G ^ 2 := by simp
  have hsq : ‖u - x₀‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hT2 : √(T : ℝ) ^ 2 = T := Real.sq_sqrt (Nat.cast_nonneg T)
  calc ‖u - x₀‖ ^ 2 / (2 * (D / (G * √T))) + D / (G * √T) / 2 * ∑ t ∈ range T, ‖g t‖ ^ 2
      ≤ D ^ 2 / (2 * (D / (G * √T))) + D / (G * √T) / 2 * (T * G ^ 2) := by gcongr
    _ = D * G * √T := by
      field_simp
      linear_combination -hT2

/-- **The one-step inequality of online gradient descent**, divided by the step. If `K` is
complete and convex, `u ∈ K` and `η t > 0`, then the iterates `x = ogd K η g x₀` satisfy
`⟪g t, x t - u⟫ ≤ (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t) + η t / 2 * ‖g t‖ ^ 2`. -/
theorem inner_ogd_sub_le (hc : IsComplete K) (hK : Convex ℝ K) (η : ℕ → ℝ) (g : ℕ → E) (x₀ : E)
    (t : ℕ) (hη : 0 < η t) {u : E} (hu : u ∈ K) :
    ⟪g t, ogd K η g x₀ t - u⟫ ≤
      (‖ogd K η g x₀ t - u‖ ^ 2 - ‖ogd K η g x₀ (t + 1) - u‖ ^ 2) / (2 * η t) +
        η t / 2 * ‖g t‖ ^ 2 := by
  have hstep := norm_ogd_succ_sub_sq_le hc hK η g x₀ t hu
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

/-- **The regret bound of online gradient descent with non-increasing steps** on linear losses.
Let `K` be complete and convex, `u ∈ K`, and let `D` bound the distance from `u` to the start
`x₀` and to every point of `K`; this holds when `x₀ ∈ K` and `K` has diameter at most `D`. If the
steps `η` are non-increasing and `η (T - 1) > 0`, then the iterates `x = ogd K η g x₀` satisfy
`∑_{t < T} ⟪g t, x t - u⟫ ≤ D ^ 2 / (2 * η (T - 1)) + ∑_{t < T} η t / 2 * ‖g t‖ ^ 2`. -/
theorem sum_inner_ogd_sub_le_of_antitone (hc : IsComplete K) (hK : Convex ℝ K) (x₀ : E)
    {η : ℕ → ℝ} (hη : Antitone η) (g : ℕ → E) {T : ℕ} (hηT : 0 < η (T - 1)) {u : E}
    (hu : u ∈ K) {D : ℝ} (hx₀ : ‖u - x₀‖ ≤ D) (hD : ∀ y ∈ K, ‖u - y‖ ≤ D) :
    ∑ t ∈ range T, ⟪g t, ogd K η g x₀ t - u⟫ ≤
      D ^ 2 / (2 * η (T - 1)) + ∑ t ∈ range T, η t / 2 * ‖g t‖ ^ 2 := by
  -- Every iterate, including the start, lies within `D` of `u`.
  have hdist : ∀ t, ‖ogd K η g x₀ t - u‖ ^ 2 ≤ D ^ 2 := by
    rintro (_ | t)
    · rw [ogd_zero, norm_sub_rev]
      exact pow_le_pow_left₀ (norm_nonneg _) hx₀ 2
    · rw [norm_sub_rev]
      exact pow_le_pow_left₀ (norm_nonneg _) (hD _ (ogd_succ_mem ⟨u, hu⟩ hc hK η g x₀ t)) 2
  obtain _ | n := T
  · simp only [sum_range_zero]
    positivity
  -- Summing the one-step inequality, the distance terms telescope with the non-negative
  -- coefficients `1 / (2 * η (t + 1)) - 1 / (2 * η t)`, and each distance is at most `D`.
  have key : ∀ n, 0 < η n → ∑ t ∈ range (n + 1), ⟪g t, ogd K η g x₀ t - u⟫ +
      ‖ogd K η g x₀ (n + 1) - u‖ ^ 2 / (2 * η n) ≤
        D ^ 2 / (2 * η n) + ∑ t ∈ range (n + 1), η t / 2 * ‖g t‖ ^ 2 := by
    intro n hn
    induction n with
    | zero =>
      have h0 := inner_ogd_sub_le hc hK η g x₀ 0 hn hu
      simp only [zero_add, sum_range_one] at h0 ⊢
      have := div_le_div_of_nonneg_right (hdist 0) (by positivity : (0 : ℝ) ≤ 2 * η 0)
      rw [sub_div] at h0
      linarith
    | succ n ih =>
      have hn' : 0 < η n := hn.trans_le (hη n.le_succ)
      have h1 := inner_ogd_sub_le hc hK η g x₀ (n + 1) hn hu
      rw [sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
      have hcoef : 1 / (2 * η n) ≤ 1 / (2 * η (n + 1)) := by
        gcongr
        exact hη n.le_succ
      have hmul : ‖ogd K η g x₀ (n + 1) - u‖ ^ 2 / (2 * η (n + 1)) -
          ‖ogd K η g x₀ (n + 1) - u‖ ^ 2 / (2 * η n) ≤
            D ^ 2 / (2 * η (n + 1)) - D ^ 2 / (2 * η n) := by
        have := mul_le_mul_of_nonneg_right (hdist (n + 1)) (sub_nonneg.2 hcoef)
        calc _ = ‖ogd K η g x₀ (n + 1) - u‖ ^ 2 * (1 / (2 * η (n + 1)) - 1 / (2 * η n)) := by ring
          _ ≤ D ^ 2 * (1 / (2 * η (n + 1)) - 1 / (2 * η n)) := this
          _ = _ := by ring
      rw [sub_div] at h1
      linarith [ih hn']
  have := key n hηT
  have : 0 ≤ ‖ogd K η g x₀ (n + 1) - u‖ ^ 2 / (2 * η n) :=
    div_nonneg (sq_nonneg _) (by simp only [add_tsub_cancel_right] at hηT; linarith)
  simp only [add_tsub_cancel_right]
  linarith

/-- **The regret bound of online gradient descent with non-increasing steps.** Let `K` be
complete and convex, `u ∈ K`, and let `D` bound the distance from `u` to the start `x₀` and to
every point of `K`; this holds when `x₀ ∈ K` and `K` has diameter at most `D`. If the steps `η`
are non-increasing, `η (T - 1) > 0`, and each `g t` with `t < T` satisfies the subgradient
inequality `f t (x t) + ⟪g t, u - x t⟫ ≤ f t u` of the loss `f t` at the iterate `x t` of
`x = ogd K η g x₀`, then
`regret f x T u ≤ D ^ 2 / (2 * η (T - 1)) + ∑_{t < T} η t / 2 * ‖g t‖ ^ 2`. -/
theorem regret_ogd_le_of_antitone (hc : IsComplete K) (hK : Convex ℝ K) (x₀ : E) {η : ℕ → ℝ}
    (hη : Antitone η) (g : ℕ → E) (f : ℕ → E → ℝ) {T : ℕ} (hηT : 0 < η (T - 1)) {u : E}
    (hu : u ∈ K) {D : ℝ} (hx₀ : ‖u - x₀‖ ≤ D) (hD : ∀ y ∈ K, ‖u - y‖ ≤ D)
    (hf : ∀ t < T, f t (ogd K η g x₀ t) + ⟪g t, u - ogd K η g x₀ t⟫ ≤ f t u) :
    regret f (ogd K η g x₀) T u ≤
      D ^ 2 / (2 * η (T - 1)) + ∑ t ∈ range T, η t / 2 * ‖g t‖ ^ 2 :=
  (regret_le_sum_inner_sub f _ g hf).trans
    (sum_inner_ogd_sub_le_of_antitone hc hK x₀ hη g hηT hu hx₀ hD)

/-- **The `(3 / 2) * D * G * √T` regret bound of online gradient descent** with the steps
`η t = D / (G * √(t + 1))`, which need no knowledge of the horizon `T`. Let `K` be complete and
convex, `u ∈ K`, and let `D` bound the distance from `u` to the start `x₀` and to every point
of `K`; this holds when `x₀ ∈ K` and `K` has diameter at most `D`. If `‖g t‖ ≤ G` and `g t`
satisfies the subgradient inequality `f t (x t) + ⟪g t, u - x t⟫ ≤ f t u` of the loss `f t` at the
iterate `x t` for every `t < T`, then `regret f x T u ≤ 3 / 2 * D * G * √T`. -/
theorem regret_ogd_le_three_halves (hc : IsComplete K) (hK : Convex ℝ K) (x₀ : E) (g : ℕ → E)
    (f : ℕ → E → ℝ) {D G : ℝ} {T : ℕ} (hg : ∀ t < T, ‖g t‖ ≤ G) {u : E} (hu : u ∈ K)
    (hx₀ : ‖u - x₀‖ ≤ D) (hD : ∀ y ∈ K, ‖u - y‖ ≤ D)
    (hf : ∀ t < T, f t (ogd K (fun t ↦ D / (G * √(t + 1))) g x₀ t) +
      ⟪g t, u - ogd K (fun t ↦ D / (G * √(t + 1))) g x₀ t⟫ ≤ f t u) :
    regret f (ogd K (fun t ↦ D / (G * √(t + 1))) g x₀) T u ≤ 3 / 2 * D * G * √T := by
  obtain _ | n := T
  · simp
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hx₀
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hg 0 n.succ_pos)
  rcases hD0.eq_or_lt with rfl | hDpos
  · -- With `D = 0` the set `K` is `{u}` and the start is `u`, so every iterate is `u`.
    have hx : ∀ t, ogd K (fun t ↦ 0 / (G * √(t + 1))) g x₀ t = u := by
      rintro (_ | t)
      · exact (sub_eq_zero.1 (norm_le_zero_iff.1 hx₀)).symm
      · exact (sub_eq_zero.1 (norm_le_zero_iff.1
          (hD _ (ogd_succ_mem ⟨u, hu⟩ hc hK _ g x₀ t)))).symm
    refine (regret_le_sum_inner_sub f _ g hf).trans (le_of_eq ?_)
    simp only [hx, sub_self, inner_zero_right, sum_const_zero, mul_zero, zero_mul]
  rcases hG0.eq_or_lt with rfl | hGpos
  · -- With `G = 0` every `g t` vanishes, and so does the regret on the linear losses.
    refine (regret_le_sum_inner_sub f _ g hf).trans (le_of_eq ?_)
    rw [mul_zero, zero_mul]
    exact sum_eq_zero fun t ht ↦ by
      rw [norm_le_zero_iff.1 (hg t (mem_range.1 ht)), inner_zero_left]
  have hanti : Antitone fun t : ℕ ↦ D / (G * √(t + 1)) := fun a b hab ↦ by
    dsimp only
    gcongr
  have hpos : 0 < D / (G * √((n : ℝ) + 1)) := by positivity
  refine (regret_ogd_le_of_antitone hc hK x₀ hanti g f (by simpa using hpos) hu hx₀ hD
    hf).trans ?_
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
  have hsum : ∑ t ∈ range (n + 1), D / (G * √((t : ℝ) + 1)) / 2 * ‖g t‖ ^ 2 ≤
      D * G * √((n : ℝ) + 1) := by
    calc ∑ t ∈ range (n + 1), D / (G * √((t : ℝ) + 1)) / 2 * ‖g t‖ ^ 2
        ≤ ∑ t ∈ range (n + 1), D * G / 2 * (√((t : ℝ) + 1))⁻¹ := by
          refine sum_le_sum fun t ht ↦ ?_
          calc D / (G * √((t : ℝ) + 1)) / 2 * ‖g t‖ ^ 2
              ≤ D / (G * √((t : ℝ) + 1)) / 2 * G ^ 2 := by
                gcongr
                exact hg t (mem_range.1 ht)
            _ = D * G / 2 * (√((t : ℝ) + 1))⁻¹ := by
                field_simp
      _ = D * G / 2 * ∑ t ∈ range (n + 1), (√((t : ℝ) + 1))⁻¹ := by rw [mul_sum]
      _ ≤ D * G / 2 * (2 * √((n : ℝ) + 1)) := by
          gcongr
          simpa using Real.sum_range_inv_sqrt_succ_le (n + 1)
      _ = D * G * √((n : ℝ) + 1) := by ring
  have hfirst : D ^ 2 / (2 * (D / (G * √((n : ℝ) + 1)))) = D * G * √((n : ℝ) + 1) / 2 := by
    field_simp
  rw [hfirst]
  linarith

end TauCeti.OnlineConvexOptimization
