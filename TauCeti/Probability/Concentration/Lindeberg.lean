/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lindeberg replacement

Finite-dimensional Lindeberg replacement: swapping the independent coordinates of a product of
probability measures on `ℝ` one at a time, for a test function that is `C^(r+1)` in each
coordinate, when the first `r` moments agree.

## Main results

* `TauCeti.Probability.abs_sub_taylorPoly_le`: if `g` is `C^(r+1)` and its `(r+1)`st derivative is
  bounded by `M`, then `g x` differs from its degree-`r` Taylor polynomial at `0` by at most
  `M * |x| ^ (r + 1) / (r + 1)!`.
* `TauCeti.Probability.abs_integral_sub_integral_le`: the one-variable replacement bound.
* `TauCeti.Probability.integral_pi_succ`: splitting off the first coordinate of a product measure.
* `TauCeti.Probability.abs_integral_pi_sub_integral_pi_le`: the replacement inequality for product
  measures on `Fin n → ℝ`.
-/

@[expose] public section

open Finset Nat

namespace TauCeti.Probability

/-- The degree-`r` Taylor polynomial of `g` at `0`, evaluated at `x`. -/
noncomputable def taylorPoly (g : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (r + 1), iteratedDeriv k g 0 * x ^ k / k !

/-- Lagrange bound on the degree-`r` Taylor remainder at `0` of a `C^(r+1)` function. -/
theorem abs_sub_taylorPoly_le {g : ℝ → ℝ} {r : ℕ} (hg : ContDiff ℝ (r + 1) g) {M : ℝ}
    (hM : ∀ t, |iteratedDeriv (r + 1) g t| ≤ M) (x : ℝ) :
    |g x - taylorPoly g r x| ≤ M * |x| ^ (r + 1) / (r + 1)! := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [taylorPoly, Finset.sum_range_succ']
  obtain ⟨y, -, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := x) (n := r)
    hx.symm (hg.contDiffOn)
  have htay : taylorWithinEval g r (Set.uIcc 0 x) 0 x = taylorPoly g r x := by
    simp only [taylor_within_apply, taylorPoly]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
      ((hg.of_le (by norm_cast; simp at hk; omega)).contDiffAt) Set.left_mem_uIcc]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [htay] at hy
  rw [hy, abs_div, abs_mul, abs_pow, sub_zero, Nat.abs_cast]
  gcongr
  exact hM y

open MeasureTheory

/-- A finite measure's `k`th moment is integrable once its `m`th absolute moment is, for `k ≤ m`. -/
theorem integrable_pow_of_integrable_abs_pow {μ : Measure ℝ} {m : ℕ}
    (h : Integrable (fun t : ℝ ↦ |t| ^ m) μ) [IsFiniteMeasure μ] {k : ℕ} (hk : k ≤ m) :
    Integrable (fun t : ℝ ↦ t ^ k) μ := by
  refine Integrable.mono' (h.add (integrable_const 1))
    (by fun_prop : Continuous fun t : ℝ ↦ t ^ k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow]
  rcases le_total |t| 1 with ht | ht
  · have := pow_le_one₀ (abs_nonneg t) ht (n := k)
    have := pow_nonneg (abs_nonneg t) m
    simp only [Pi.add_apply]
    linarith
  · have := pow_le_pow_right₀ ht hk
    simp only [Pi.add_apply]
    linarith

/-- Two probability measures on `ℝ` with the same moments up to order `r` and a finite absolute
moment of order `r + 1` give expectations of a `C^(r+1)` function that differ by at most the
`(r+1)`st derivative bound times the two absolute moments over `(r+1)!`. -/
theorem abs_integral_sub_integral_le {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : ℝ → ℝ} {r : ℕ} (hg : ContDiff ℝ (r + 1) g) {M : ℝ}
    (hM : ∀ t, |iteratedDeriv (r + 1) g t| ≤ M)
    (hμ : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) μ) (hν : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ν)
    (hmom : ∀ k ≤ r, ∫ t, t ^ k ∂μ = ∫ t, t ^ k ∂ν) :
    |∫ t, g t ∂μ - ∫ t, g t ∂ν| ≤
      M / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ + ∫ t, |t| ^ (r + 1) ∂ν) := by
  have hPc : Continuous (taylorPoly g r) := by unfold taylorPoly; fun_prop
  have hRc : Continuous fun t ↦ g t - taylorPoly g r t := hg.continuous.sub hPc
  have hRb : ∀ t, ‖g t - taylorPoly g r t‖ ≤ M / (r + 1)! * |t| ^ (r + 1) := fun t ↦ by
    rw [Real.norm_eq_abs, div_mul_eq_mul_div]
    exact abs_sub_taylorPoly_le hg hM t
  have hPint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ → Integrable (taylorPoly g r) ρ := by
    intro ρ _ h
    refine integrable_finsetSum _ fun k hk ↦ ?_
    have := integrable_pow_of_integrable_abs_pow h (k := k) (by simp at hk; omega)
    exact (this.const_mul _).div_const _
  have hRint : ∀ (ρ : Measure ℝ), Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ →
      Integrable (fun t ↦ g t - taylorPoly g r t) ρ := fun ρ h ↦
    Integrable.mono' (h.const_mul _) hRc.aestronglyMeasurable (Filter.Eventually.of_forall hRb)
  have hPeq : ∫ t, taylorPoly g r t ∂μ = ∫ t, taylorPoly g r t ∂ν := by
    have key : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ →
        ∀ k ∈ range (r + 1), Integrable (fun t : ℝ ↦ iteratedDeriv k g 0 * t ^ k / k !) ρ :=
      fun ρ _ h k hk ↦
        ((integrable_pow_of_integrable_abs_pow h (k := k) (by simp at hk; omega)).const_mul
          _).div_const _
    unfold taylorPoly
    rw [integral_finsetSum _ (key μ hμ), integral_finsetSum _ (key ν hν)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [integral_div, integral_const_mul, integral_div, integral_const_mul,
      hmom k (by simp at hk; omega)]
  have hgμ : Integrable g μ :=
    ((hRint μ hμ).add (hPint μ hμ)).congr (Filter.Eventually.of_forall fun t ↦ by simp)
  have hgν : Integrable g ν :=
    ((hRint ν hν).add (hPint ν hν)).congr (Filter.Eventually.of_forall fun t ↦ by simp)
  have hsplit : ∫ t, g t ∂μ - ∫ t, g t ∂ν =
      (∫ t, (g t - taylorPoly g r t) ∂μ) - ∫ t, (g t - taylorPoly g r t) ∂ν := by
    rw [integral_sub hgμ (hPint μ hμ), integral_sub hgν (hPint ν hν), hPeq]
    ring
  have hb : ∀ (ρ : Measure ℝ) (h : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ),
      |∫ t, (g t - taylorPoly g r t) ∂ρ| ≤ M / (r + 1)! * ∫ t, |t| ^ (r + 1) ∂ρ :=
    fun ρ h ↦ by
      have := norm_integral_le_of_norm_le (h.const_mul (M / (r + 1)!))
        (Filter.Eventually.of_forall hRb)
      rwa [integral_const_mul, Real.norm_eq_abs] at this
  rw [hsplit]
  calc _ ≤ |∫ t, (g t - taylorPoly g r t) ∂μ| + |∫ t, (g t - taylorPoly g r t) ∂ν| :=
        abs_sub _ _
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hb μ hμ) (hb ν hν)

/-- Integrating over a product measure on `Fin (n + 1) → ℝ` splits off the first coordinate. -/
theorem integral_pi_succ {n : ℕ} (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ x, f x ∂Measure.pi μ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
      ∂((μ 0).prod (Measure.pi fun i ↦ μ i.succ)) := by
  rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Equiv.coe_fn_mk]
  rfl

/-- **Lindeberg replacement.** Let `μ i` and `ν i` be probability measures on `ℝ` with finite
absolute moments of order `r + 1` and the same moments up to order `r`. If `f` is bounded,
continuous and `C^(r+1)` in each coordinate, with `(r+1)`st derivative in coordinate `i` bounded
by `M i`, then replacing the product measure `∏ μ i` by `∏ ν i` changes the expectation of `f` by
at most `∑ i, M i / (r + 1)! * (E |X_i| ^ (r + 1) + E |Y_i| ^ (r + 1))`. -/
theorem abs_integral_pi_sub_integral_pi_le {r n : ℕ} (μ ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (μ i))
    (hν : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (ν i))
    (hmom : ∀ i, ∀ k ≤ r, ∫ t, t ^ k ∂μ i = ∫ t, t ^ k ∂ν i)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) {C : ℝ} (hfb : ∀ z, |f z| ≤ C)
    {M : Fin n → ℝ}
    (hsm : ∀ z i, ContDiff ℝ (r + 1) fun t ↦ f (Function.update z i t))
    (hM : ∀ z i t, |iteratedDeriv (r + 1) (fun s ↦ f (Function.update z i s)) t| ≤ M i) :
    |∫ z, f z ∂Measure.pi μ - ∫ z, f z ∂Measure.pi ν| ≤
      ∑ i, M i / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ i + ∫ t, |t| ^ (r + 1) ∂ν i) := by
  induction n with
  | zero => rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]; simp
  | succ n ih =>
    have hc : Continuous fun p : ℝ × (Fin n → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) :=
      continuous_pi fun i ↦ by
        induction i using Fin.cases with
        | zero => simp only [Fin.cons_zero]; fun_prop
        | succ j => simp only [Fin.cons_succ]; fun_prop
    have hFc : Continuous fun p : ℝ × (Fin n → ℝ) ↦ f (Fin.cons p.1 p.2) := hf.comp hc
    have hFi : ∀ (ρ : Measure (ℝ × (Fin n → ℝ))) [IsFiniteMeasure ρ],
        Integrable (fun p : ℝ × (Fin n → ℝ) ↦ f (Fin.cons p.1 p.2)) ρ := fun ρ _ ↦
      Integrable.of_bound hFc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p ↦ by
        simpa using hfb _)
    rw [integral_pi_succ μ, integral_pi_succ ν]
    set μ' : Fin n → Measure ℝ := fun i ↦ μ i.succ with hμ'
    set ν' : Fin n → Measure ℝ := fun i ↦ ν i.succ with hν'
    have h1 : |∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂((μ 0).prod (Measure.pi μ')) -
        ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂((ν 0).prod (Measure.pi μ'))| ≤
        M 0 / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ 0 + ∫ t, |t| ^ (r + 1) ∂ν 0) := by
      rw [integral_prod_symm _ (hFi _), integral_prod_symm _ (hFi _),
        ← integral_sub ((hFi _).integral_prod_right) ((hFi _).integral_prod_right)]
      rw [← Real.norm_eq_abs]
      refine le_trans (norm_integral_le_of_norm_le_const
        (C := M 0 / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ 0 + ∫ t, |t| ^ (r + 1) ∂ν 0))
        (Filter.Eventually.of_forall fun w ↦ ?_)) (by simp)
      have := abs_integral_sub_integral_le (μ := μ 0) (ν := ν 0)
        (g := fun t ↦ f (Fin.cons t w)) (M := M 0) (r := r) ?_ ?_ (hμ 0) (hν 0) (hmom 0)
      · exact this
      · simpa [Fin.update_cons_zero] using hsm (Fin.cons 0 w) 0
      · intro t
        simpa [Fin.update_cons_zero] using hM (Fin.cons 0 w) 0 t
    have h2 : |∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂((ν 0).prod (Measure.pi μ')) -
        ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂((ν 0).prod (Measure.pi ν'))| ≤
        ∑ i : Fin n, M i.succ / (r + 1)! *
          (∫ t, |t| ^ (r + 1) ∂μ i.succ + ∫ t, |t| ^ (r + 1) ∂ν i.succ) := by
      rw [integral_prod _ (hFi _), integral_prod _ (hFi _),
        ← integral_sub ((hFi _).integral_prod_left) ((hFi _).integral_prod_left)]
      rw [← Real.norm_eq_abs]
      refine le_trans (norm_integral_le_of_norm_le_const
        (C := ∑ i : Fin n, M i.succ / (r + 1)! *
          (∫ t, |t| ^ (r + 1) ∂μ i.succ + ∫ t, |t| ^ (r + 1) ∂ν i.succ))
        (Filter.Eventually.of_forall fun t ↦ ?_)) (by simp)
      refine ih μ' ν' (fun i ↦ hμ i.succ) (fun i ↦ hν i.succ) (fun i ↦ hmom i.succ)
        (f := fun w ↦ f (Fin.cons t w)) (hf.comp (by fun_prop))
        (fun z ↦ hfb _) (M := fun i ↦ M i.succ) (fun z i ↦ ?_) (fun z i s ↦ ?_)
      · simpa [Fin.cons_update] using hsm (Fin.cons t z) i.succ
      · simpa [Fin.cons_update] using hM (Fin.cons t z) i.succ s
    rw [Fin.sum_univ_succ]
    calc _ ≤ _ := abs_sub_le _ (∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂((ν 0).prod (Measure.pi μ'))) _
      _ ≤ _ := add_le_add h1 h2

end TauCeti.Probability

