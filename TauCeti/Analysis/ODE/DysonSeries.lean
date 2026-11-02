/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Analysis.ODE.Caratheodory
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Dyson series of a continuous path in a Banach algebra

For a continuous path `p : ℝ → B` in a real Banach algebra, the time-ordered exponential
`Γ t` is the solution of the linear equation `Γ' t = Γ t * p t` with `Γ 0 = 1`. It is given by
the norm-convergent Dyson series of iterated integrals

`Γ t = 1 + ∫₀ᵗ p s₁ ds₁ + ∫₀ᵗ ∫₀^{s₂} p s₁ * p s₂ ds₁ ds₂ + ⋯`,

whose `n`-th term is bounded by `‖1‖ (C |t|)ⁿ / n!` whenever `‖p s‖ ≤ C` for `|s| ≤ |t|`.
The coefficient `p` need not be bounded on the whole line.

Existence on the whole line cannot be taken from `TauCeti.timeDependentFlow`, whose suspended
field must be globally Lipschitz, nor from the Carathéodory solutions of
`TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard`, which live on one compact interval;
the series also supplies the explicit expansion. Uniqueness is
`Continuous.eq_of_hasDerivAt_clm_apply`.

If `p` takes skew-adjoint values in a star algebra, then `Γ t` is unitary. This is the
mechanism producing the unitary cocycles which implement bounded perturbations of
one-parameter automorphism groups of C⋆-algebras.

## Main declarations

* `TauCeti.dysonTerm`: the `n`-fold iterated integral of the path.
* `TauCeti.norm_dysonTerm_le`: the factorial bound on the iterated integrals.
* `TauCeti.dysonSeries`: the sum of the iterated integrals.
* `TauCeti.hasDerivAt_dysonSeries`: the series solves `Γ' t = Γ t * p t`.
* `TauCeti.eq_mul_dysonSeries`: every solution of this equation is `f 0 * Γ t`.
* `TauCeti.dysonSeries_mem_unitary`: for skew-adjoint `p` the series is unitary.

## References

* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
  Theorem 3.1.33, for bounded perturbations and their Dyson expansions.
* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
  Section 5.4.1, for the unitary cocycles of perturbed C⋆-dynamics.
-/

public section

noncomputable section

open Set intervalIntegral
open scoped Nat Interval

namespace TauCeti

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] {p : ℝ → B}

/-- The `n`-th term of the Dyson series of `p`: `dysonTerm p 0 t = 1` and
`dysonTerm p (n + 1) t = ∫ s in 0..t, dysonTerm p n s * p s`. It is the iterated integral of
`p s₁ * ⋯ * p sₙ` over the simplex `0 ≤ s₁ ≤ ⋯ ≤ sₙ ≤ t` when `t ≥ 0`; when `t < 0` it is
`(-1)ⁿ` times the integral over the reversed simplex `t ≤ sₙ ≤ ⋯ ≤ s₁ ≤ 0`. -/
def dysonTerm (p : ℝ → B) : ℕ → ℝ → B
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ s in 0..t, dysonTerm p n s * p s

@[simp]
theorem dysonTerm_zero (p : ℝ → B) (t : ℝ) : dysonTerm p 0 t = 1 := by
  simp [dysonTerm]

/-- The recursion defining the iterated integrals. -/
theorem dysonTerm_succ (p : ℝ → B) (n : ℕ) (t : ℝ) :
    dysonTerm p (n + 1) t = ∫ s in 0..t, dysonTerm p n s * p s := by
  simp [dysonTerm]

@[simp]
theorem dysonTerm_succ_zero (p : ℝ → B) (n : ℕ) : dysonTerm p (n + 1) 0 = 0 := by
  simp [dysonTerm_succ]

/-- The iterated integrals of a continuous path are continuous. -/
theorem continuous_dysonTerm (hp : Continuous p) (n : ℕ) : Continuous (dysonTerm p n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    rw [funext (dysonTerm_succ p n)]
    exact continuous_primitive (fun _ _ => (ih.mul hp).intervalIntegrable _ _) 0

/-- The factorial bound on the iterated integrals: if `‖p s‖ ≤ C` for `|s| ≤ R`, then
`‖dysonTerm p n t‖ ≤ ‖1‖ * (C * |t|) ^ n / n!` for `|t| ≤ R`. -/
theorem norm_dysonTerm_le {R C : ℝ} (hC : ∀ s, |s| ≤ R → ‖p s‖ ≤ C)
    (n : ℕ) {t : ℝ} (ht : |t| ≤ R) :
    ‖dysonTerm p n t‖ ≤ ‖(1 : B)‖ * (C * |t|) ^ n / n ! := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simpa using (abs_nonneg t).trans ht))
    set K := ‖(1 : B)‖ * C ^ (n + 1) / (n ! : ℝ)
    have hbound : ∀ s ∈ Ι (0 : ℝ) t, ‖dysonTerm p n s * p s‖ ≤ K * |s| ^ n := by
      intro s hs
      have hst : |s| ≤ |t| := by
        rcases Set.mem_uIcc.1 (Set.uIoc_subset_uIcc hs) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
          exact abs_le.2 ⟨by linarith [neg_abs_le t, abs_nonneg t],
            by linarith [le_abs_self t, abs_nonneg t]⟩
      calc ‖dysonTerm p n s * p s‖ ≤ ‖dysonTerm p n s‖ * ‖p s‖ := norm_mul_le _ _
        _ ≤ (‖(1 : B)‖ * (C * |s|) ^ n / n !) * C :=
          mul_le_mul (ih (hst.trans ht)) (hC s (hst.trans ht)) (norm_nonneg _)
            (by positivity)
        _ = K * |s| ^ n := by simp only [K]; ring
    rw [dysonTerm_succ]
    refine (norm_integral_le_abs_of_norm_le
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hbound)
      ((by fun_prop : Continuous fun s : ℝ => K * |s| ^ n).intervalIntegrable _ _)).trans_eq ?_
    have hint : |∫ s in 0..t, |s| ^ n| = |t| ^ (n + 1) / (n + 1) := by
      have h := integral_pow_abs_sub_uIoc (a := 0) (b := t) (n := n)
      simp only [sub_zero] at h
      rw [abs_intervalIntegral_eq, h, abs_of_nonneg (by positivity)]
    rw [integral_const_mul, abs_mul, hint, abs_of_nonneg (by positivity),
      Nat.factorial_succ]
    simp only [K]
    push_cast
    field_simp
    ring

/-- Uniqueness for the linear equation solved by the Dyson series: a solution of
`f' t = f t * p t` is determined by its value at one time. -/
theorem eq_of_hasDerivAt_mul (hp : Continuous p) {f g : ℝ → B}
    (hf : ∀ t, HasDerivAt f (f t * p t) t) (hg : ∀ t, HasDerivAt g (g t * p t) t) {t₀ : ℝ}
    (h : f t₀ = g t₀) : f = g :=
  ((ContinuousLinearMap.mul ℝ B).flip.continuous.comp hp).eq_of_hasDerivAt_clm_apply
    (by simpa using hf) (by simpa using hg) h

/-- The Dyson series, or time-ordered exponential, of `p`: the sum of the iterated integrals
`dysonTerm p n t`. For continuous `p` it is the solution of `Γ' t = Γ t * p t` with `Γ 0 = 1`
(`hasDerivAt_dysonSeries`, `eq_mul_dysonSeries`). -/
def dysonSeries (p : ℝ → B) (t : ℝ) : B :=
  ∑' n, dysonTerm p n t

@[simp]
theorem dysonSeries_zero (p : ℝ → B) : dysonSeries p 0 = 1 := by
  rw [dysonSeries, tsum_eq_single 0 fun n hn => ?_]
  · simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact dysonTerm_succ_zero p n

variable [CompleteSpace B]

/-- Each iterated integral is the primitive of the previous one multiplied by `p`. -/
theorem hasDerivAt_dysonTerm_succ (hp : Continuous p) (n : ℕ) (t : ℝ) :
    HasDerivAt (dysonTerm p (n + 1)) (dysonTerm p n t * p t) t := by
  rw [funext (dysonTerm_succ p n)]
  exact ((continuous_dysonTerm hp n).mul hp).integral_hasStrictDerivAt 0 t |>.hasDerivAt

/-- The iterated integrals are summable at every time. -/
theorem summable_dysonTerm (hp : Continuous p) (t : ℝ) : Summable fun n => dysonTerm p n t := by
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hp.continuousOn (s := Icc (-|t|) |t|))
  refine .of_norm_bounded ((Real.summable_pow_div_factorial (C * |t|)).mul_left ‖(1 : B)‖)
    fun n => (norm_dysonTerm_le (fun s hs => hC s (abs_le.1 hs)) n le_rfl).trans_eq ?_
  ring

/-- The Dyson series converges in norm at every time. -/
theorem hasSum_dysonSeries (hp : Continuous p) (t : ℝ) :
    HasSum (fun n => dysonTerm p n t) (dysonSeries p t) :=
  (summable_dysonTerm hp t).hasSum

/-- The Dyson series solves the linear equation `Γ' t = Γ t * p t`. -/
theorem hasDerivAt_dysonSeries (hp : Continuous p) (t : ℝ) :
    HasDerivAt (dysonSeries p) (dysonSeries p t * p t) t := by
  -- Split off the constant term and differentiate the tail termwise on the ball `|s| < R`,
  -- where `‖p‖ ≤ C`.
  have hsplit : dysonSeries p = fun s => 1 + ∑' n, dysonTerm p (n + 1) s :=
    funext fun s => by rw [dysonSeries, (summable_dysonTerm hp s).tsum_eq_zero_add, dysonTerm_zero]
  set R := |t| + 1
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hp.continuousOn (s := Icc (-R) R))
  have hC' : ∀ s, |s| ≤ R → ‖p s‖ ≤ C := fun s hs => hC s (abs_le.1 hs)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0 (by simp only [abs_zero, R]; positivity))
  have hbound : ∀ n s, s ∈ Metric.ball (0 : ℝ) R →
      ‖dysonTerm p n s * p s‖ ≤ ‖(1 : B)‖ * (C * R) ^ n / n ! * C := by
    intro n s hs
    have hs : |s| ≤ R := by simpa [Real.dist_eq] using (Metric.mem_ball.1 hs).le
    calc ‖dysonTerm p n s * p s‖ ≤ ‖dysonTerm p n s‖ * ‖p s‖ := norm_mul_le _ _
      _ ≤ ‖(1 : B)‖ * (C * |s|) ^ n / n ! * C :=
        mul_le_mul (norm_dysonTerm_le hC' n hs) (hC' s hs) (norm_nonneg _) (by positivity)
      _ ≤ ‖(1 : B)‖ * (C * R) ^ n / n ! * C := by gcongr
  have ht : t ∈ Metric.ball (0 : ℝ) R := by simp [R]
  have h := hasDerivAt_tsum_of_isPreconnected
    (((Real.summable_pow_div_factorial (C * R)).mul_left ‖(1 : B)‖).mul_right C |>.congr
      fun n => by ring)
    Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected
    (fun n s _ => hasDerivAt_dysonTerm_succ hp n s) hbound ht
    ((summable_nat_add_iff 1).2 (summable_dysonTerm hp t)) ht
  rw [dysonSeries, ← (summable_dysonTerm hp t).tsum_mul_right, hsplit]
  exact h.const_add 1

/-- The Dyson series of a continuous path is continuous. -/
theorem continuous_dysonSeries (hp : Continuous p) : Continuous (dysonSeries p) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_dysonSeries hp t).continuousAt

/-- Every solution of `f' t = f t * p t` is `f 0 * dysonSeries p t`. -/
theorem eq_mul_dysonSeries (hp : Continuous p) {f : ℝ → B}
    (hf : ∀ t, HasDerivAt f (f t * p t) t) (t : ℝ) : f t = f 0 * dysonSeries p t := by
  refine congrFun (eq_of_hasDerivAt_mul hp hf (g := fun t => f 0 * dysonSeries p t)
    (fun t => ?_) (t₀ := 0) (by simp)) t
  rw [mul_assoc]
  exact (hasDerivAt_dysonSeries hp t).const_mul (f 0)

section Star

variable [StarRing B] [StarModule ℝ B] [ContinuousStar B]

/-- The Dyson series of a skew-adjoint path is unitary. -/
theorem dysonSeries_mem_unitary (hp : Continuous p) (hskew : ∀ t, star (p t) = -p t) (t : ℝ) :
    dysonSeries p t ∈ unitary B := by
  have hΓ := hasDerivAt_dysonSeries hp
  have hΓstar (t : ℝ) :
      HasDerivAt (fun s => star (dysonSeries p s)) (-(p t * star (dysonSeries p t))) t :=
    (hΓ t).star.congr_deriv (by simp [star_mul, hskew])
  -- `Γ t * star (Γ t)` has derivative `Γ p Γ⋆ - Γ p Γ⋆ = 0`.
  have hright : ∀ t, dysonSeries p t * star (dysonSeries p t) = 1 := by
    have hd (s : ℝ) : HasDerivAt (fun s => dysonSeries p s * star (dysonSeries p s)) 0 s :=
      ((hΓ s).mul (hΓstar s)).congr_deriv (by noncomm_ring)
    have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      fun s => (hd s).deriv
    exact fun t => (hconst t 0).trans (by simp)
  -- `star (Γ t) * Γ t` solves `X' = X p - p X`, as does the constant `1`.
  have hleft : (fun s => star (dysonSeries p s) * dysonSeries p s) = fun _ => 1 := by
    let L : ℝ → B →L[ℝ] B := fun s =>
      (ContinuousLinearMap.mul ℝ B).flip (p s) - ContinuousLinearMap.mul ℝ B (p s)
    have hL : Continuous L :=
      ((ContinuousLinearMap.mul ℝ B).flip.continuous.comp hp).sub
        ((ContinuousLinearMap.mul ℝ B).continuous.comp hp)
    refine hL.eq_of_hasDerivAt_clm_apply (fun s => ?_) (fun s => ?_) (t₀ := 0) (by simp)
    · exact ((hΓstar s).mul (hΓ s)).congr_deriv (by
        simp only [L, sub_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.mul_apply']
        noncomm_ring)
    · exact (hasDerivAt_const s (1 : B)).congr_deriv (by simp [L])
  exact Unitary.mem_iff.2 ⟨congrFun hleft t, hright t⟩

end Star

end TauCeti
