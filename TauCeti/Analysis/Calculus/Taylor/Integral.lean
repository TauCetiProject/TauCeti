/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.Taylor.Basic

/-!
# Iterated derivatives along a line and multivariate Taylor remainders

Mathlib's `DifferentiableAt.deriv_comp_add_smul` computes the derivative of the restriction
`s ↦ f (x + s • y)` of a function to a line, and `map_add_eq_sum_add_integral_iteratedFDeriv`
expresses the Taylor remainder in integral form when the target space is complete.

This file records the higher derivatives of `s ↦ f (x + s • y)` for functions over any
nontrivially normed field, and deduces a norm bound on the multivariate Taylor remainder of any
order over `ℝ` without assuming completeness of the target space, by pairing the remainder with a
unit continuous linear functional via Hahn–Banach and applying the one-dimensional Lagrange
remainder bound `TauCeti.abs_sub_taylorWithinEval_le` along the segment `[0, 1]`.

## Main results

* `DifferentiableAt.hasDerivAt_deriv_comp_add_smul`: if `f` is differentiable near `x + t • y`
  and `fderiv 𝕜 f` is differentiable at `x + t • y`, then the derivative of
  `s ↦ f (x + s • y)` has derivative `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`.
* `ContDiffAt.deriv_deriv_comp_add_smul` and `ContDiffAt.deriv_deriv_deriv_comp_add_smul`: the
  second and third derivatives of `s ↦ f (x + s • y)` at `t` in curried `fderiv` form.
* `ContDiffAt.iteratedDeriv_comp_add_smul`: the `n`-th derivative of `s ↦ f (x + s • y)` at `t`
  is `iteratedFDeriv 𝕜 n f (x + t • y) (fun _ ↦ y)`.
* `TauCeti.norm_map_add_sub_sum_iteratedFDeriv_le`: Taylor's remainder bound of order `n` along a
  segment `[x, x + y]` between arbitrary real normed spaces.
* `ContDiffAt.isBigO_sub_sum_iteratedFDeriv` and `ContDiffAt.isBigO_sub_taylor_three`: asymptotic
  `O(‖x' - x‖ ^ (n + 1))` and third-order `O(‖x' - x‖ ^ 4)` Taylor expansions at a point.
-/

public section

open scoped ContDiff Nat Topology

section LineDerivatives

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x y : E} {t : 𝕜}

/-- If `f` is differentiable near `x + t • y` and `fderiv 𝕜 f` is differentiable at
`x + t • y`, then the derivative of the restriction `s ↦ f (x + s • y)` of `f` to a line has
derivative the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`. -/
theorem DifferentiableAt.hasDerivAt_deriv_comp_add_smul
    (hf' : DifferentiableAt 𝕜 (fderiv 𝕜 f) (x + t • y))
    (hf : ∀ᶠ z in 𝓝 (x + t • y), DifferentiableAt 𝕜 f z) :
    HasDerivAt (deriv fun s : 𝕜 => f (x + s • y)) (fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y) t := by
  have hline : HasDerivAt (fun s : 𝕜 => x + s • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x
  have hev : (fun s => fderiv 𝕜 f (x + s • y) y) =ᶠ[𝓝 t] deriv fun s : 𝕜 => f (x + s • y) := by
    filter_upwards [hline.continuousAt.tendsto.eventually hf] with s hs
    exact hs.deriv_comp_add_smul.symm
  simpa using ((hf'.hasFDerivAt.comp_hasDerivAt t hline).clm_apply
    (hasDerivAt_const t y)).congr_of_eventuallyEq hev.symm

/-- The second derivative of the restriction `s ↦ f (x + s • y)` of a `C²` function to a line is
the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`. -/
theorem ContDiffAt.deriv_deriv_comp_add_smul (hf : ContDiffAt 𝕜 2 f (x + t • y)) :
    deriv (deriv fun s : 𝕜 => f (x + s • y)) t = fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y :=
  ((hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasDerivAt_deriv_comp_add_smul
    (hf.eventually (by simp) |>.mono fun _ hz => hz.differentiableAt two_ne_zero) |>.deriv

/-- The `n`-th derivative of the restriction `s ↦ f (x + s • y)` of a `C^n` function to a line is
the `n`-th iterated derivative evaluated on the constant tuple `y`. -/
theorem ContDiffAt.iteratedDeriv_comp_add_smul {n : ℕ} (hf : ContDiffAt 𝕜 n f (x + t • y)) :
    iteratedDeriv n (fun s : 𝕜 => f (x + s • y)) t =
      iteratedFDeriv 𝕜 n f (x + t • y) (fun _ => y) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hline : ContinuousAt (fun s : 𝕜 => x + s • y) t :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have hev : (iteratedDeriv n fun s : 𝕜 => f (x + s • y)) =ᶠ[𝓝 t]
        fun s => iteratedFDeriv 𝕜 n f (x + s • y) (fun _ => y) :=
      (hline.eventually (hf.eventually (by simp))).mono fun s hs =>
        ih (hs.of_le (mod_cast n.le_succ))
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact ContDiffAt.deriv_fderiv_add_smul (by simpa [Nat.cast_succ] using hf)

/-- The third derivative of the restriction `s ↦ f (x + s • y)` of a `C³` function to a line is
`fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 f)) (x + t • y) y y y`. -/
theorem ContDiffAt.deriv_deriv_deriv_comp_add_smul (hf : ContDiffAt 𝕜 3 f (x + t • y)) :
    deriv (deriv (deriv fun s : 𝕜 => f (x + s • y))) t =
      fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 f)) (x + t • y) y y y := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, TauCeti.iteratedFDeriv_three_apply] using
    hf.iteratedDeriv_comp_add_smul (n := 3)

end LineDerivatives

section RemainderBound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Multivariate Taylor remainder bound without completeness.** If `f` is `C^(n + 1)` at each
point of the segment from `x` to `x + y` and `‖D^(n + 1) f‖ ≤ M` on the open segment, then the
order-`n` Taylor polynomial of `f` at `x` approximates `f (x + y)` with error at most
`M * ‖y‖ ^ (n + 1) / (n + 1)!`. -/
theorem TauCeti.norm_map_add_sub_sum_iteratedFDeriv_le {f : E → F} {x y : E} {n : ℕ} {M : ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • y))
    (hM : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ ≤ M) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1),
        (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖ ≤
      M * ‖y‖ ^ (n + 1) / (n + 1)! := by
  set rem := f (x + y) - ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)
  obtain ⟨g, hg_norm, hg_rem⟩ := exists_dual_vector'' ℝ rem
  replace hg_rem : g rem = ‖rem‖ := by simpa using hg_rem
  let line : ℝ → F := fun s => f (x + s • y)
  have hline {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ContDiffAt ℝ (n + 1) line t :=
    (hf t ht).comp t (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hφ_deriv {k : ℕ} (hk : k ≤ n + 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDeriv k (g ∘ line) t = g (iteratedFDeriv ℝ k f (x + t • y) (fun _ => y)) := by
    have hk' : (k : ℕ∞ω) ≤ (n + 1 : ℕ) := mod_cast hk
    rw [g.iteratedDeriv_comp_left (hline ht) (by simpa [Nat.cast_succ] using hk'),
      ((hf t ht).of_le (by simpa [Nat.cast_succ] using hk')).iteratedDeriv_comp_add_smul]
  have htaylor : (g ∘ line) 1 - taylorWithinEval (g ∘ line) n Set.univ 0 1 = ‖rem‖ := by
    rw [← hg_rem]
    simp only [rem, Function.comp_apply, line, one_smul, map_sub, map_sum, map_smul,
      taylor_within_apply, sub_zero, one_pow, mul_one, iteratedDerivWithin_univ]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hφ_deriv (Finset.mem_range.mp hk).le (Set.left_mem_Icc.mpr zero_le_one)]
    simp [smul_eq_mul]
  have hbound := TauCeti.abs_sub_taylorWithinEval_le (f := g ∘ line) (n := n)
    (M := M * ‖y‖ ^ (n + 1)) (x₀ := 0) (x := 1)
    (fun t ht => g.contDiff.contDiffAt.comp t
      (hline (by rwa [Set.uIcc_of_le zero_le_one] at ht)))
    fun t ht => by
      rw [Set.uIoo_of_lt zero_lt_one] at ht
      rw [hφ_deriv le_rfl (Set.Ioo_subset_Icc_self ht), ← Real.norm_eq_abs]
      calc ‖g (iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y))‖
          ≤ ‖g‖ * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ := g.le_opNorm _
        _ ≤ 1 * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ := by gcongr
        _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ‖y‖ ^ (n + 1) := by
            simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
              (iteratedFDeriv ℝ (n + 1) f (x + t • y)).le_opNorm (fun _ => y)
        _ ≤ M * ‖y‖ ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (hM t ht) (pow_nonneg (norm_nonneg y) _)
  rw [htaylor, abs_of_nonneg (norm_nonneg rem)] at hbound
  simpa using hbound

/-- **Taylor's theorem of order `n` with `O(‖x' - x‖ ^ (n + 1))` remainder.** If `f` is `C^(n + 1)`
at `x`, then `f x' - ∑ k ≤ n, (k!)⁻¹ • D^k f(x)(x' - x, …, x' - x) = O(‖x' - x‖ ^ (n + 1))` as
`x' → x`, without any completeness assumption on the target space. -/
theorem ContDiffAt.isBigO_sub_sum_iteratedFDeriv {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ (n + 1) f x) :
    (fun x' => f x' - ∑ k ∈ Finset.range (n + 1),
        (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => x' - x))
      =O[𝓝 x] fun x' => ‖x' - x‖ ^ (n + 1) := by
  let M := ‖iteratedFDeriv ℝ (n + 1) f x‖ + 1
  have hcont : ContinuousAt (iteratedFDeriv ℝ (n + 1) f) x :=
    (hf.iteratedFDeriv_right (i := n + 1) (m := 0) (by simp)).continuousAt
  have hnear : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ (n + 1) f z ∧ ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ M := by
    filter_upwards [hf.eventually (by simp),
      hcont.eventually (Metric.ball_mem_nhds _ zero_lt_one)] with z hz hznorm
    refine ⟨hz, ?_⟩
    have hdist : ‖iteratedFDeriv ℝ (n + 1) f z - iteratedFDeriv ℝ (n + 1) f x‖ < 1 := by
      simpa [dist_eq_norm] using hznorm
    linarith [norm_sub_norm_le (iteratedFDeriv ℝ (n + 1) f z) (iteratedFDeriv ℝ (n + 1) f x)]
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  refine Asymptotics.isBigO_iff.mpr ⟨M / (n + 1)!, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x hr] with x' hx'
  have hseg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (x' - x) ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (by simpa [dist_eq_norm] using hx')
  have hb := TauCeti.norm_map_add_sub_sum_iteratedFDeriv_le (f := f) (x := x) (y := x' - x)
    (n := n) (M := M) (fun t ht => (hball _ (hseg ht)).1)
    (fun t ht => (hball _ (hseg (Set.Ioo_subset_Icc_self ht))).2)
  rw [add_sub_cancel] at hb
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact hb.trans_eq (div_mul_eq_mul_div _ _ _).symm

/-- **The third-order Taylor expansion of a `C⁴` map.** If `f` is `C⁴` at `x`, then
`f x' = f x + Df(x)(x' - x) + ½ D²f(x)(x' - x)² + ⅙ D³f(x)(x' - x)³ + O(‖x' - x‖ ^ 4)`,
without any completeness assumption on the target space. -/
theorem ContDiffAt.isBigO_sub_taylor_three {f : E → F} {x : E} (hf : ContDiffAt ℝ 4 f x) :
    (fun x' => f x' - f x - fderiv ℝ f x (x' - x) -
        (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ f) x (x' - x) (x' - x) -
        (6⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x (x' - x) (x' - x) (x' - x))
      =O[𝓝 x] fun x' => ‖x' - x‖ ^ 4 := by
  refine (hf.isBigO_sub_sum_iteratedFDeriv (n := 3)).congr_left fun x' => ?_
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, Nat.cast_mul, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply,
    TauCeti.iteratedFDeriv_three_apply]
  module

end RemainderBound
