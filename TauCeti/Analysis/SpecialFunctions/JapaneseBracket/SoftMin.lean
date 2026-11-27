/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp

/-!
# A smooth distance to a finite set

For `b > 0` and a finite set `s` in a real inner product space, the soft minimum

`Φ(z) = -log ∑_{a ∈ s} exp (-√(b + ‖z - a‖²))`

(`TauCeti.softMinDist`) of the regularized distances `√(b + ‖z - a‖²)` is a smooth function
within a constant of the distance from `z` to `s`:

`infDist z s - log (card s) ≤ Φ(z) ≤ infDist z s + √b`

(`TauCeti.infDist_sub_log_card_le_softMinDist`, `TauCeti.softMinDist_le_infDist_add_sqrt`,
`TauCeti.abs_softMinDist_sub_infDist_le`).
Its gradient is a convex combination of the gradients of the regularized distances
(`TauCeti.hasFDerivAt_softMinDist`), so it has norm at most one
(`TauCeti.norm_fderiv_softMinDist_le_one`), like the distance function itself.

Unlike the distance function it is nearly flat near `s` once `b` is large: where
`Φ(z) ≤ √b + L`, the gradient has norm at most `card s · exp L / √(√b)`
(`TauCeti.norm_fderiv_softMinDist_le_of_le`). Each center `a` contributes the gradient of
`√(b + ‖z - a‖²)`, of norm `‖z - a‖ / √(b + ‖z - a‖²) < 1`, with the weight
`exp (Φ(z) - √(b + ‖z - a‖²))`; these weights sum to one
(`TauCeti.sum_exp_softMinDist_sub_sqrt`). A center far from `z` therefore contributes an
exponentially small amount, while a center near `z` contributes a small gradient because
`√(b + t²)` is flat for `t` small compared with `√b`.

So `exp (c Φ)` is a smooth weight comparable to `exp (c · infDist z s)`, with logarithmic gradient
at most `|c|` everywhere (`TauCeti.norm_fderiv_exp_mul_softMinDist_le`) and arbitrarily small near
`s`, uniformly over sets of at most `m` points once `b` is large
(`TauCeti.exists_pos_forall_norm_fderiv_softMinDist_le`). Such weights measure exponential decay
away from a finite configuration of points that may spread apart, for instance away from the
zeros of a plane vortex uniformly over its moduli space.
-/

public section

noncomputable section

namespace TauCeti

open Metric

variable {E : Type*} [NormedAddCommGroup E] {b L : ℝ} {s : Finset E} {z a : E}

/-- The **soft minimum of the regularized distances** from `z` to the points of a finite set `s`,
`-log ∑_{a ∈ s} exp (-√(b + ‖z - a‖²))`. For `b > 0` it is a smooth function within a constant
of the distance from `z` to `s`. It is `0` for the empty set. -/
def softMinDist (b : ℝ) (s : Finset E) (z : E) : ℝ :=
  -Real.log (∑ a ∈ s, Real.exp (-√(b + ‖z - a‖ ^ 2)))

theorem softMinDist_def (b : ℝ) (s : Finset E) (z : E) :
    softMinDist b s z = -Real.log (∑ a ∈ s, Real.exp (-√(b + ‖z - a‖ ^ 2))) :=
  (rfl)

@[simp]
theorem softMinDist_empty (b : ℝ) (z : E) : softMinDist b (∅ : Finset E) z = 0 := by
  simp [softMinDist_def]

/-- The soft minimum over a single point is the regularized distance to it. -/
@[simp]
theorem softMinDist_singleton (b : ℝ) (a z : E) : softMinDist b {a} z = √(b + ‖z - a‖ ^ 2) := by
  simp [softMinDist_def]

/-- The sum of exponentials inside `softMinDist` is positive for a nonempty set. -/
private theorem sum_exp_pos (hs : s.Nonempty) :
    0 < ∑ a ∈ s, Real.exp (-√(b + ‖z - a‖ ^ 2)) :=
  Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) hs

/-- The weight `exp (Φ(z) - √(b + ‖z - a‖²))` of a center `a` is its exponential
`exp (-√(b + ‖z - a‖²))` divided by the sum inside `softMinDist`. -/
private theorem exp_softMinDist_sub_sqrt (hs : s.Nonempty) (a : E) :
    Real.exp (softMinDist b s z - √(b + ‖z - a‖ ^ 2)) =
      (∑ a' ∈ s, Real.exp (-√(b + ‖z - a'‖ ^ 2)))⁻¹ * Real.exp (-√(b + ‖z - a‖ ^ 2)) := by
  rw [sub_eq_add_neg, Real.exp_add, softMinDist_def, Real.exp_neg, Real.exp_log (sum_exp_pos hs)]

/-- The weights `exp (Φ(z) - √(b + ‖z - a‖²))` of the centers of a nonempty set sum to one. -/
theorem sum_exp_softMinDist_sub_sqrt (hs : s.Nonempty) (b : ℝ) (z : E) :
    ∑ a ∈ s, Real.exp (softMinDist b s z - √(b + ‖z - a‖ ^ 2)) = 1 := by
  simp_rw [exp_softMinDist_sub_sqrt hs, ← Finset.mul_sum]
  exact inv_mul_cancel₀ (sum_exp_pos hs).ne'

/-- The soft minimum is at most each regularized distance. -/
theorem softMinDist_le_sqrt (ha : a ∈ s) : softMinDist b s z ≤ √(b + ‖z - a‖ ^ 2) := by
  have hle : Real.exp (-√(b + ‖z - a‖ ^ 2)) ≤ ∑ a ∈ s, Real.exp (-√(b + ‖z - a‖ ^ 2)) :=
    Finset.single_le_sum (f := fun a ↦ Real.exp (-√(b + ‖z - a‖ ^ 2)))
      (fun _ _ ↦ (Real.exp_pos _).le) ha
  have := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp] at this
  rw [softMinDist_def]
  linarith

/-- The soft minimum exceeds every lower bound `r` of the regularized distances by at least
`-log (card s)`. -/
theorem sub_log_card_le_softMinDist {r : ℝ} (hs : s.Nonempty)
    (hr : ∀ a ∈ s, r ≤ √(b + ‖z - a‖ ^ 2)) : r - Real.log s.card ≤ softMinDist b s z := by
  have hle : ∑ a ∈ s, Real.exp (-√(b + ‖z - a‖ ^ 2)) ≤ s.card * Real.exp (-r) := by
    simpa using Finset.sum_le_card_nsmul s _ _ fun a ha ↦ Real.exp_le_exp.2 (neg_le_neg (hr a ha))
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have := Real.log_le_log (sum_exp_pos hs) hle
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  rw [softMinDist_def]
  linarith

/-- Every regularized distance is at least `√b`, so the soft minimum is at least
`√b - log (card s)`. -/
theorem sqrt_sub_log_card_le_softMinDist (hs : s.Nonempty) :
    √b - Real.log s.card ≤ softMinDist b s z :=
  sub_log_card_le_softMinDist hs fun _ _ ↦
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

/-- The soft minimum is at least the distance to `s` minus `log (card s)`. -/
theorem infDist_sub_log_card_le_softMinDist (hb : 0 ≤ b) :
    infDist z (s : Set E) - Real.log s.card ≤ softMinDist b s z := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  exact sub_log_card_le_softMinDist hs fun a ha ↦ by
    refine (infDist_le_dist_of_mem (Finset.mem_coe.2 ha)).trans ?_
    rw [dist_eq_norm]
    exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left hb)

/-- The soft minimum is at most the distance to `s` plus `√b`. -/
theorem softMinDist_le_infDist_add_sqrt :
    softMinDist b s z ≤ infDist z (s : Set E) + √b := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [Real.sqrt_nonneg]
  obtain ⟨a, ha, hd⟩ := (s.finite_toSet.isCompact).exists_infDist_eq_dist
    (Finset.coe_nonempty.2 hs) z
  refine (softMinDist_le_sqrt (Finset.mem_coe.1 ha)).trans ?_
  rw [hd, dist_eq_norm]
  calc √(b + ‖z - a‖ ^ 2) ≤ √b + √(‖z - a‖ ^ 2) := Real.sqrt_add_le_add_sqrt b _
    _ = ‖z - a‖ + √b := by rw [Real.sqrt_sq (norm_nonneg _), add_comm]

/-- The soft minimum of the regularized distances to a set of at most `m` points is within
`√b + log m` of the distance to the set. -/
theorem abs_softMinDist_sub_infDist_le (hb : 0 ≤ b) {m : ℕ} (hs : s.card ≤ m) (z : E) :
    |softMinDist b s z - infDist z (s : Set E)| ≤ √b + Real.log m := by
  have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [softMinDist_empty, Finset.coe_empty, infDist_empty, sub_zero, abs_zero]
    positivity
  have hk : (1 : ℝ) ≤ s.card := by exact_mod_cast hne.card_pos
  have hlk : Real.log s.card ≤ Real.log m :=
    Real.log_le_log (by linarith) (by exact_mod_cast hs)
  have h₁ := infDist_sub_log_card_le_softMinDist (s := s) (z := z) hb
  have h₂ := softMinDist_le_infDist_add_sqrt (b := b) (s := s) (z := z)
  have : 0 ≤ Real.log s.card := Real.log_nonneg hk
  rw [abs_le]
  constructor <;> linarith [Real.sqrt_nonneg b]

/-- Where the soft minimum is at least `√b + r`, every point of `s` is at distance at least `r`. -/
theorem le_norm_sub_of_sqrt_add_le_softMinDist {r : ℝ} (h : √b + r ≤ softMinDist b s z)
    (ha : a ∈ s) : r ≤ ‖z - a‖ := by
  have h₁ := h.trans softMinDist_le_infDist_add_sqrt
  have h₂ := infDist_le_dist_of_mem (x := z) (Finset.mem_coe.2 ha)
  rw [dist_eq_norm] at h₂
  linarith

/-! ### The derivative -/

variable [InnerProductSpace ℝ E]

/-- The derivative of the sum of exponentials inside `softMinDist`. -/
private theorem hasFDerivAt_sum_exp (hb : 0 < b) (s : Finset E) (z : E) :
    HasFDerivAt (fun t ↦ ∑ a ∈ s, Real.exp (-√(b + ‖t - a‖ ^ 2)))
      (∑ a ∈ s, Real.exp (-√(b + ‖z - a‖ ^ 2)) •
        -((√(b + ‖z - a‖ ^ 2))⁻¹ • innerSL ℝ (z - a))) z :=
  HasFDerivAt.fun_sum fun a _ ↦
    (hasFDerivAt_sqrt_add_norm_sub_sq (x₀ := a) (x := z) (by positivity)).fun_neg.exp

/-- The soft minimum is smooth. -/
theorem contDiff_softMinDist (hb : 0 < b) (s : Finset E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (softMinDist b s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa [funext fun z : E ↦ softMinDist_empty b z] using contDiff_const (c := (0 : ℝ))
  have hS : ContDiff ℝ n fun t : E ↦ ∑ a ∈ s, Real.exp (-√(b + ‖t - a‖ ^ 2)) :=
    ContDiff.sum fun a _ ↦ ((contDiff_const.add
      ((contDiff_id.sub contDiff_const).norm_sq ℝ)).sqrt fun t ↦ by positivity).neg.exp
  exact (hS.log fun t ↦ (sum_exp_pos hs).ne').neg

/-- **The derivative of the soft minimum.** It is the convex combination of the derivatives
`(√(b + ‖z - a‖²))⁻¹ • ⟪z - a, ·⟫` of the regularized distances, with the weights
`exp (Φ(z) - √(b + ‖z - a‖²))`, which sum to one when `s` is nonempty
(`sum_exp_softMinDist_sub_sqrt`). -/
theorem hasFDerivAt_softMinDist (hb : 0 < b) (s : Finset E) (z : E) :
    HasFDerivAt (softMinDist b s)
      (∑ a ∈ s, Real.exp (softMinDist b s z - √(b + ‖z - a‖ ^ 2)) •
        ((√(b + ‖z - a‖ ^ 2))⁻¹ • innerSL ℝ (z - a))) z := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa [funext fun z : E ↦ softMinDist_empty b z] using hasFDerivAt_const (0 : ℝ) z
  refine ((hasFDerivAt_sum_exp hb s z).log (sum_exp_pos hs).ne').fun_neg.congr_fderiv ?_
  simp_rw [exp_softMinDist_sub_sqrt hs, Finset.smul_sum, smul_neg, Finset.sum_neg_distrib, neg_neg,
    smul_smul, mul_assoc]

/-- **The gradient of the soft minimum as a convex combination.** Its norm is at most the sum over
the centers `a` of `exp (Φ(z) - √(b + ‖z - a‖²))` times the norm `‖z - a‖ / √(b + ‖z - a‖²)` of
the gradient of the regularized distance; these weights sum to one. -/
theorem norm_fderiv_softMinDist_le_sum (hb : 0 < b) (s : Finset E) (z : E) :
    ‖fderiv ℝ (softMinDist b s) z‖ ≤
      ∑ a ∈ s, Real.exp (softMinDist b s z - √(b + ‖z - a‖ ^ 2)) *
        (‖z - a‖ / √(b + ‖z - a‖ ^ 2)) := by
  rw [(hasFDerivAt_softMinDist hb s z).fderiv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  have h : b + ‖z - a‖ ^ 2 ≠ 0 := by positivity
  rw [norm_smul, ← (hasFDerivAt_sqrt_add_norm_sub_sq h).fderiv, norm_fderiv_sqrt_add_norm_sub_sq h,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The gradient of the soft minimum has norm at most one. -/
theorem norm_fderiv_softMinDist_le_one (hb : 0 < b) (s : Finset E) (z : E) :
    ‖fderiv ℝ (softMinDist b s) z‖ ≤ 1 := by
  refine (norm_fderiv_softMinDist_le_sum hb s z).trans ?_
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  calc ∑ a ∈ s, Real.exp (softMinDist b s z - √(b + ‖z - a‖ ^ 2)) *
          (‖z - a‖ / √(b + ‖z - a‖ ^ 2))
      ≤ ∑ a ∈ s, Real.exp (softMinDist b s z - √(b + ‖z - a‖ ^ 2)) :=
        Finset.sum_le_sum fun a _ ↦ mul_le_of_le_one_right (Real.exp_pos _).le
          (by simpa using norm_div_sqrt_add_norm_sq_le_one hb.le (z - a))
    _ = 1 := sum_exp_softMinDist_sub_sqrt hs b z

/-- One term of the gradient of the soft minimum is small where the soft minimum is at most
`√b + L`: the center contributes `exp (Φ - y) √(y² - b) / y`, `y = √(b + t²)`, which is at most
`exp L / √(√b)`. -/
private theorem exp_sub_mul_div_le {Φ t : ℝ} (hb : 0 < b) (hΦ : Φ ≤ √b + L) (ht : 0 ≤ t) :
    Real.exp (Φ - √(b + t ^ 2)) * (t / √(b + t ^ 2)) ≤ Real.exp L / √(√b) := by
  set y := √(b + t ^ 2)
  have hsb : 0 < √b := Real.sqrt_pos.2 hb
  have hy : √b ≤ y := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg t))
  have hy2 : y ^ 2 = b + t ^ 2 := Real.sq_sqrt (by positivity)
  have hb2 : √b ^ 2 = b := Real.sq_sqrt hb.le
  set u := y - √b
  -- `t² = u (y + √b) ≤ 2 u y`, so `t² / y² ≤ 2 u / √b`.
  have ht2 : t ^ 2 ≤ 2 * u * y := by nlinarith
  have hratio : (t / y) ^ 2 ≤ 2 * u / √b := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hsb]
    nlinarith
  -- `exp (2 (Φ - y)) ≤ exp (2 L) exp (-2 u)` and `2 u exp (-2 u) ≤ 1`.
  have hexp : Real.exp (Φ - y) ^ 2 ≤ Real.exp L ^ 2 * Real.exp (-(2 * u)) := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have hue : 2 * u * Real.exp (-(2 * u)) ≤ 1 := by
    have := Real.add_one_le_exp (2 * u)
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  have hsq : (Real.exp (Φ - y) * (t / y)) ^ 2 ≤ (Real.exp L / √(√b)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hsb.le, mul_pow]
    calc Real.exp (Φ - y) ^ 2 * (t / y) ^ 2
        ≤ Real.exp L ^ 2 * Real.exp (-(2 * u)) * (2 * u / √b) :=
          mul_le_mul hexp hratio (sq_nonneg _) (by positivity)
      _ = Real.exp L ^ 2 * (2 * u * Real.exp (-(2 * u))) / √b := by ring
      _ ≤ Real.exp L ^ 2 * 1 / √b := by gcongr
      _ = Real.exp L ^ 2 / √b := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- **The soft minimum is nearly flat near `s`.** Where `Φ(z) ≤ √b + L`, the gradient of the
soft minimum has norm at most `card s · exp L / √(√b)`, which is small once `b` is large compared
with `exp (4 L) (card s)⁴`. -/
theorem norm_fderiv_softMinDist_le_of_le (hb : 0 < b) (hz : softMinDist b s z ≤ √b + L) :
    ‖fderiv ℝ (softMinDist b s) z‖ ≤ s.card * (Real.exp L / √(√b)) := by
  refine (norm_fderiv_softMinDist_le_sum hb s z).trans ?_
  simpa using Finset.sum_le_card_nsmul s _ _ fun a _ ↦
    exp_sub_mul_div_le hb hz (norm_nonneg (z - a))

/-- **The soft minimum is uniformly flat near `s` for `b` large.** For `ε > 0`, `m` and `L` there
is `b > 0` such that, for every set `s` of at most `m` points, the gradient of the soft minimum has
norm at most `ε` wherever `Φ(z) ≤ √b + L`. -/
theorem exists_pos_forall_norm_fderiv_softMinDist_le (m : ℕ) (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b > 0, ∀ s : Finset E, s.card ≤ m → ∀ z, softMinDist b s z ≤ √b + L →
      ‖fderiv ℝ (softMinDist b s) z‖ ≤ ε := by
  set β : ℝ := m * Real.exp L / ε + 1
  have hβ : 0 < β := by positivity
  have hb : 0 < β ^ 4 := by positivity
  have hssb : √(√(β ^ 4)) = β := by
    rw [show β ^ 4 = (β ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.sqrt_sq hβ.le]
  refine ⟨β ^ 4, hb, fun s hs z hz ↦ (norm_fderiv_softMinDist_le_of_le hb hz).trans ?_⟩
  have hk : (s.card : ℝ) ≤ m := by exact_mod_cast hs
  rw [hssb, mul_div_assoc', div_le_iff₀ hβ]
  calc (s.card : ℝ) * Real.exp L ≤ m * Real.exp L := by gcongr
    _ ≤ ε * β := by
      rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
      linarith

/-- The logarithmic gradient of the weight `exp (c Φ)` is `c` times the gradient of the soft
minimum `Φ`. -/
theorem norm_fderiv_exp_mul_softMinDist (hb : 0 < b) (s : Finset E) (c : ℝ) (z : E) :
    ‖fderiv ℝ (fun t ↦ Real.exp (c * softMinDist b s t)) z‖ =
      |c| * ‖fderiv ℝ (softMinDist b s) z‖ * Real.exp (c * softMinDist b s z) := by
  have hΦ := (contDiff_softMinDist hb s (n := 1)).differentiable (by simp)
  have hd := ((hΦ z).hasFDerivAt.const_mul c).exp
  rw [hd.fderiv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

/-- The weight `exp (c Φ)` has logarithmic gradient at most `|c|`. -/
theorem norm_fderiv_exp_mul_softMinDist_le (hb : 0 < b) (s : Finset E) (c : ℝ) (z : E) :
    ‖fderiv ℝ (fun t ↦ Real.exp (c * softMinDist b s t)) z‖ ≤
      |c| * Real.exp (c * softMinDist b s z) := by
  rw [norm_fderiv_exp_mul_softMinDist hb s c z]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg c) (norm_fderiv_softMinDist_le_one hb s z))
    (Real.exp_pos _).le

/-- The squared form of `norm_fderiv_exp_mul_softMinDist_le`, the bound
`‖d exp (c Φ)‖² ≤ c² exp (c Φ)²` that enters weighted `L²` estimates. -/
theorem norm_fderiv_exp_mul_softMinDist_sq_le (hb : 0 < b) (s : Finset E) (c : ℝ) (z : E) :
    ‖fderiv ℝ (fun t ↦ Real.exp (c * softMinDist b s t)) z‖ ^ 2 ≤
      c ^ 2 * Real.exp (c * softMinDist b s z) ^ 2 := by
  simpa only [mul_pow, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_exp_mul_softMinDist_le hb s c z) 2

end TauCeti
