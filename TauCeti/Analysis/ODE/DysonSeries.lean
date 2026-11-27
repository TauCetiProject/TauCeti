/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.Normed.Operator.CompactFamily
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Topology.Algebra.Module.ComplexSmulI
import TauCeti.Topology.Algebra.Star.RealModule

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
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard`, which live on one compact interval;
the series also supplies the explicit expansion. Uniqueness is
`Continuous.eq_of_hasDerivAt_clm_apply`.

Applied in the opposite algebra, the same series solves the left equation `Γ' t = p t * Γ t`.
For a path of bounded operators `M` on a Banach space this left series is the propagator of the
time-dependent linear equation `w' t = M t (w t)`: every solution is `w t = Γ t (w 0)`.

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
* `TauCeti.continuous_parametric_dysonSeries`: the series of a jointly continuous family of paths
  depends continuously on the parameter, jointly with the time.
* `TauCeti.dysonSeriesLeft`: the Dyson series in the opposite algebra, solving
  `Γ' t = p t * Γ t` (`TauCeti.hasDerivAt_dysonSeriesLeft`), and factoring as
  `Γ (t + d) = Γ t * Γ d` for a path of period `d` (`TauCeti.dysonSeriesLeft_add_of_periodic`),
  hence `Γ (n d) = Γ d ^ n` (`TauCeti.dysonSeriesLeft_natCast_mul_of_periodic`).
* `TauCeti.exists_isInvertible_hasDerivAt_clm_Icc`: an invertible fundamental solution on a
  closed interval, initialized at any included time.
* `TauCeti.dysonSeriesLeft_mul_sub_mul_mul_eq`: rotating the left equation by a path `J` of
  square roots of `-1` conjugates its series by `J`. For a loop `J` of bounded operators, the
  rotated return map then has the same `det (1 - ·)`
  (`TauCeti.det_one_sub_dysonSeriesLeft_mul_sub_mul_mul`).
* `TauCeti.eq_dysonSeriesLeft_apply`: for a path of bounded operators, every solution of the
  time-dependent linear equation `w' t = M t (w t)` is `w t = dysonSeriesLeft M t (w 0)`.
* `TauCeti.periodic_dysonSeriesLeft_apply_iff`: for a periodic path of bounded operators, such a
  solution is periodic exactly when its initial value is fixed by the propagator over one period.
* `TauCeti.dysonSeriesLeft_add_natCast_mul_apply_of_eq_smul`: more generally, if the initial
  value lies in the `ε`-eigenspace of `Γ d ^ n`, the solution is twisted by `ε` along `n d`.
* `TauCeti.apply_dysonSeriesLeft_apply_dysonSeriesLeft`: the propagator of a continuous path
  that is skew for a continuous bilinear map `B` preserves `B`.
* `TauCeti.apply_dysonSeries_neg_apply`: the inverse of such a propagator is its adjoint for
  `B`.
* `TauCeti.contDiff_dysonSeriesLeft`: the left series of a `Cⁿ` path is `Cⁿ⁺¹`.
* `TauCeti.dysonSeriesLeft_const`: the left series of a constant path `a` is `t ↦ exp (t • a)`.
* `TauCeti.dysonSeriesLeft_add`: `Γ (a + t) = Γₐ t * Γ a` for the left series `Γₐ` of the
  translated path `s ↦ p (a + s)`.
* `TauCeti.dysonSeriesLeft_comp_const_add`: `Γₐ t = Γ (a + t) * Γ(a)⁻¹`, with the inverse given
  by the Dyson series of `-p`.
* `TauCeti.star_dysonSeriesLeft`, `TauCeti.dysonSeriesLeft_mem_unitary`: the adjoint of the left
  series of `p` is the series of `s ↦ star (p s)`, and the left series of a skew-adjoint path is
  unitary.
* `TauCeti.norm_dysonSeriesLeft_sub_le`: in a C⋆-ring, the left series of two skew-adjoint paths
  differ at time `t` by at most `|∫₀ᵗ ‖p - q‖|`.
* `TauCeti.dysonSeries_neg_mul_dysonSeriesLeft`, `TauCeti.dysonSeriesLeft_mul_dysonSeries_neg`:
  the Dyson series of `-p` is the inverse of the left Dyson series of `p`.
* `TauCeti.commute_dysonSeries`, `TauCeti.commute_dysonSeriesLeft`: an element commuting with
  every value of `p` commutes with both Dyson series of `p`.
* `TauCeti.dysonSeriesLeft_apply_I_smul`, `TauCeti.dysonSeries_neg_apply_I_smul`: the propagator
  of a path of complex-linear maps and its inverse are complex linear.
* `TauCeti.eq_dysonSeriesLeft_apply_add_integral`: variation of constants, every solution of
  `w' t = M t (w t) + f t` is `w t = Γ t (w 0 + ∫₀ᵗ Γ(s)⁻¹ (f s) ds)`.
* `TauCeti.exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm`,
  `TauCeti.exists_forall_norm_le_mul_norm_add_integral_norm`: on `[0, d]` such a solution stays
  within `C ∫₀ᵈ ‖f‖` of `t ↦ Γ t (w 0)`, hence `‖w t‖ ≤ C (‖w 0‖ + ∫₀ᵈ ‖f‖)`.
* `TauCeti.exists_forall_norm_le_mul_integral_norm_of_norm_le`: if `w 0` is bounded by the
  deviation `w d - Γ d (w 0)`, then `‖w t‖ ≤ C ∫₀ᵈ ‖f‖` on `[0, d]`; boundary value problems and
  twisted periodic problems both reduce to this.

## References

* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
  Theorem 3.1.33, for bounded perturbations and their Dyson expansions.
* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
  Section 5.4.1, for the unitary cocycles of perturbed C⋆-dynamics.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public section

noncomputable section

open Set intervalIntegral
open scoped Nat Interval Topology

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

/-- The iterated integrals of a jointly continuous family of paths are jointly continuous in the
parameter and the time. -/
theorem continuous_parametric_dysonTerm {X : Type*} [TopologicalSpace X] {p : X → ℝ → B}
    (hp : Continuous (Function.uncurry p)) (n : ℕ) :
    Continuous fun q : X × ℝ => dysonTerm (p q.1) n q.2 := by
  induction n with
  | zero => simpa using continuous_const
  | succ n ih =>
    simp_rw [dysonTerm_succ]
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun x s => dysonTerm (p x) n s * p x s) (ih.mul hp)

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

/-- The Dyson series of `p` for the left equation `Γ' t = p t * Γ t`: the Dyson series of `p` in
the opposite algebra. For a path of bounded operators it is the propagator of the time-dependent
linear equation `w' t = p t (w t)` (`eq_dysonSeriesLeft_apply`). -/
def dysonSeriesLeft (p : ℝ → B) (t : ℝ) : B :=
  MulOpposite.unop (dysonSeries (fun s => MulOpposite.op (p s)) t)

/-- The left Dyson series of `p` is the Dyson series of `p` in the opposite algebra. This
transfers the facts about `dysonSeries` to `dysonSeriesLeft`. -/
theorem op_dysonSeriesLeft (p : ℝ → B) (t : ℝ) :
    MulOpposite.op (dysonSeriesLeft p t) = dysonSeries (fun s => MulOpposite.op (p s)) t := by
  rw [dysonSeriesLeft, MulOpposite.op_unop]

@[simp]
theorem dysonSeriesLeft_zero (p : ℝ → B) : dysonSeriesLeft p 0 = 1 := by
  simp [dysonSeriesLeft]

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

/-- **Continuous dependence on parameters.** The Dyson series of a jointly continuous family of
paths is jointly continuous in the parameter and the time. -/
theorem continuous_parametric_dysonSeries {X : Type*} [TopologicalSpace X] {p : X → ℝ → B}
    (hp : Continuous (Function.uncurry p)) :
    Continuous fun q : X × ℝ => dysonSeries (p q.1) q.2 := by
  -- Near `(x₀, t₀)` the paths are bounded uniformly in the parameter on a compact time
  -- interval, so the factorial bound makes the series converge uniformly there.
  refine continuous_iff_continuousAt.2 fun ⟨x₀, t₀⟩ => ?_
  set R := |t₀| + 1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hp.comp (Continuous.prodMk_right x₀)).continuousOn (s := Icc (-R) R))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by simp only [R]; linarith [abs_nonneg t₀],
    by simp only [R]; linarith [abs_nonneg t₀]⟩)
  -- By the tube lemma, the bound `C + 1` holds for all parameters near `x₀`.
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ s ∈ Icc (-R) R, ‖p x s‖ ≤ C + 1 :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun s hs =>
      ((hp.norm.tendsto (x₀, s)).eventually (eventually_lt_nhds (lt_add_one _))).mono
        fun z hz => hz.le.trans (by simpa using hC s hs)
  have hN : {x | ∀ s ∈ Icc (-R) R, ‖p x s‖ ≤ C + 1} ×ˢ {t : ℝ | |t| < R} ∈ 𝓝 (x₀, t₀) :=
    prod_mem_nhds hev ((isOpen_lt continuous_abs continuous_const).mem_nhds (by simp [R]))
  have hu := (Real.summable_pow_div_factorial ((C + 1) * R)).mul_left ‖(1 : B)‖
  refine (continuousOn_tsum (fun n => (continuous_parametric_dysonTerm hp n).continuousOn) hu
    (fun n q hq => ?_)).continuousAt hN
  have hbound : ∀ s, |s| ≤ R → ‖p q.1 s‖ ≤ C + 1 := fun s hs => hq.1 s (abs_le.1 hs)
  have hq₂ : |q.2| ≤ R := le_of_lt hq.2
  calc ‖dysonTerm (p q.1) n q.2‖ ≤ ‖(1 : B)‖ * ((C + 1) * |q.2|) ^ n / n ! :=
        norm_dysonTerm_le hbound n hq₂
    _ ≤ ‖(1 : B)‖ * ((C + 1) * R) ^ n / n ! := by gcongr
    _ = ‖(1 : B)‖ * (((C + 1) * R) ^ n / n !) := mul_div_assoc _ _ _

/-- Every solution of `f' t = f t * p t` is `f 0 * dysonSeries p t`. -/
theorem eq_mul_dysonSeries (hp : Continuous p) {f : ℝ → B}
    (hf : ∀ t, HasDerivAt f (f t * p t) t) (t : ℝ) : f t = f 0 * dysonSeries p t := by
  refine congrFun (eq_of_hasDerivAt_mul hp hf (g := fun t => f 0 * dysonSeries p t)
    (fun t => ?_) (t₀ := 0) (by simp)) t
  rw [mul_assoc]
  exact (hasDerivAt_dysonSeries hp t).const_mul (f 0)

/-- An element commuting with every value of a continuous path `p` commutes with its Dyson
series: `a Γ` and `Γ a` both solve `X' = X p` with initial value `a`. -/
theorem commute_dysonSeries (hp : Continuous p) {a : B} (ha : ∀ s, Commute a (p s)) (t : ℝ) :
    Commute a (dysonSeries p t) :=
  congrFun (eq_of_hasDerivAt_mul hp (f := fun s => a * dysonSeries p s)
    (g := fun s => dysonSeries p s * a)
    (fun s => by simpa only [mul_assoc] using (hasDerivAt_dysonSeries hp s).const_mul a)
    (fun s => ((hasDerivAt_dysonSeries hp s).mul_const a).congr_deriv (by
      rw [mul_assoc, mul_assoc, (ha s).eq])) (t₀ := 0) (by simp)) t

section Star

variable [StarRing B] [ContinuousStar B]

/-- The Dyson series of a skew-adjoint path is unitary. -/
theorem dysonSeries_mem_unitary (hp : Continuous p) (hskew : ∀ t, star (p t) = -p t) (t : ℝ) :
    dysonSeries p t ∈ unitary B := by
  -- Continuity of `star` makes it commute with real scalars.
  have : StarModule ℝ B := ContinuousStar.starModule_real
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

/-! ### The left equation and the propagator of a linear equation -/

section Left

/-- The left Dyson series solves the linear equation `Γ' t = p t * Γ t`. -/
theorem hasDerivAt_dysonSeriesLeft (hp : Continuous p) (t : ℝ) :
    HasDerivAt (dysonSeriesLeft p) (p t * dysonSeriesLeft p t) t := by
  have h := hasDerivAt_dysonSeries (MulOpposite.continuous_op.comp hp) t
  exact (MulOpposite.opContinuousLinearEquiv ℝ).symm.hasFDerivAt.comp_hasDerivAt t h

/-- The left Dyson series of a continuous path is continuous. -/
theorem continuous_dysonSeriesLeft (hp : Continuous p) : Continuous (dysonSeriesLeft p) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_dysonSeriesLeft hp t).continuousAt

/-- The left Dyson series of a jointly continuous family of paths is jointly continuous in the
parameter and the time. -/
theorem continuous_parametric_dysonSeriesLeft {X : Type*} [TopologicalSpace X] {p : X → ℝ → B}
    (hp : Continuous (Function.uncurry p)) :
    Continuous fun q : X × ℝ => dysonSeriesLeft (p q.1) q.2 :=
  MulOpposite.continuous_unop.comp <| continuous_parametric_dysonSeries
    (p := fun x s => MulOpposite.op (p x s)) (MulOpposite.continuous_op.comp hp)

/-- Every solution of `f' t = p t * f t` is `dysonSeriesLeft p t * f 0`. -/
theorem eq_dysonSeriesLeft_mul (hp : Continuous p) {f : ℝ → B}
    (hf : ∀ t, HasDerivAt f (p t * f t) t) (t : ℝ) : f t = dysonSeriesLeft p t * f 0 := by
  refine congrFun (((ContinuousLinearMap.mul ℝ B).continuous.comp hp).eq_of_hasDerivAt_clm_apply
    (w := fun t => dysonSeriesLeft p t * f 0) (fun t => by simpa using hf t) (fun t => ?_)
    (t₀ := 0) (by simp)) t
  simpa [mul_assoc] using (hasDerivAt_dysonSeriesLeft hp t).mul_const (f 0)

/-- **The Dyson series of a constant path is the exponential.** For the constant path `a`, the
solution of `Γ' t = a * Γ t` with `Γ 0 = 1` is `Γ t = exp (t • a)`. -/
@[simp]
theorem dysonSeriesLeft_const (a : B) (t : ℝ) :
    dysonSeriesLeft (fun _ ↦ a) t = NormedSpace.exp (t • a) := by
  simpa using (eq_dysonSeriesLeft_mul continuous_const
    (fun t ↦ hasDerivAt_exp_smul_const' (𝕂 := ℝ) a t) t).symm

/-- The left Dyson series over `[0, a + t]` factors through the left Dyson series of the
translated path `s ↦ p (a + s)`: `Γ (a + t) = Γₐ t * Γ a`. -/
theorem dysonSeriesLeft_add (hp : Continuous p) (a t : ℝ) :
    dysonSeriesLeft p (a + t) = dysonSeriesLeft (fun s => p (a + s)) t * dysonSeriesLeft p a := by
  simpa using eq_dysonSeriesLeft_mul (p := fun s => p (a + s)) (hp.comp (continuous_const_add a))
    (f := fun t => dysonSeriesLeft p (a + t))
    (fun t => (hasDerivAt_dysonSeriesLeft hp (a + t)).comp_const_add a t) t

/-- For a periodic path, the left Dyson series over a translated period factors through the
left Dyson series over one period: `Γ (t + d) = Γ t * Γ d`. -/
theorem dysonSeriesLeft_add_of_periodic (hp : Continuous p) {d : ℝ}
    (hper : Function.Periodic p d) (t : ℝ) :
    dysonSeriesLeft p (t + d) = dysonSeriesLeft p t * dysonSeriesLeft p d := by
  rw [add_comm, dysonSeriesLeft_add hp]
  simp_rw [add_comm d, hper.funext]

/-- For a periodic path, the left Dyson series over `n` periods is the `n`-th power of the left
Dyson series over one period: `Γ (n d) = Γ d ^ n`. For a propagator this says that the return
map of the `n`-fold iterated loop is the `n`-th power of the return map. -/
theorem dysonSeriesLeft_natCast_mul_of_periodic (hp : Continuous p) {d : ℝ}
    (hper : Function.Periodic p d) (n : ℕ) :
    dysonSeriesLeft p (n * d) = dysonSeriesLeft p d ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, add_one_mul, dysonSeriesLeft_add_of_periodic hp hper, ih,
      pow_succ]

/-- The Dyson series of `-p` is a left inverse of the left Dyson series of `p`:
`dysonSeries (-p) t * dysonSeriesLeft p t = 1`. -/
theorem dysonSeries_neg_mul_dysonSeriesLeft (hp : Continuous p) (t : ℝ) :
    dysonSeries (-p) t * dysonSeriesLeft p t = 1 := by
  -- The product has derivative `Φ (-p) Ψ + Φ p Ψ = 0`.
  have hd (s : ℝ) : HasDerivAt (fun s => dysonSeries (-p) s * dysonSeriesLeft p s) 0 s :=
    ((hasDerivAt_dysonSeries hp.neg s).mul (hasDerivAt_dysonSeriesLeft hp s)).congr_deriv (by
      simp only [Pi.neg_apply, mul_neg, neg_mul, mul_assoc, neg_add_cancel])
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    fun s => (hd s).deriv
  exact (hconst t 0).trans (by simp)

/-- The Dyson series of `-p` is a right inverse of the left Dyson series of `p`:
`dysonSeriesLeft p t * dysonSeries (-p) t = 1`. -/
theorem dysonSeriesLeft_mul_dysonSeries_neg (hp : Continuous p) (t : ℝ) :
    dysonSeriesLeft p t * dysonSeries (-p) t = 1 := by
  -- The product solves `X' = p X - X p`, as does the constant `1`.
  let L : ℝ → B →L[ℝ] B := fun s =>
    ContinuousLinearMap.mul ℝ B (p s) - (ContinuousLinearMap.mul ℝ B).flip (p s)
  have hL : Continuous L :=
    ((ContinuousLinearMap.mul ℝ B).continuous.comp hp).sub
      ((ContinuousLinearMap.mul ℝ B).flip.continuous.comp hp)
  have h : (fun s => dysonSeriesLeft p s * dysonSeries (-p) s) = fun _ => 1 := by
    refine hL.eq_of_hasDerivAt_clm_apply (fun s => ?_) (fun s => ?_) (t₀ := 0) (by simp)
    · exact ((hasDerivAt_dysonSeriesLeft hp s).mul (hasDerivAt_dysonSeries hp.neg s)).congr_deriv
        (by simp only [L, sub_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.mul_apply', Pi.neg_apply, mul_neg]; noncomm_ring)
    · exact (hasDerivAt_const s (1 : B)).congr_deriv (by simp [L])
  exact congrFun h t

/-- The left Dyson series of a continuous path takes invertible values, with inverse the Dyson
series of `-p`. -/
theorem isUnit_dysonSeriesLeft (hp : Continuous p) (t : ℝ) : IsUnit (dysonSeriesLeft p t) :=
  ⟨⟨_, _, dysonSeriesLeft_mul_dysonSeries_neg hp t, dysonSeries_neg_mul_dysonSeriesLeft hp t⟩,
    rfl⟩

/-- The left Dyson series of the translated path `s ↦ p (a + s)` is `Γ (a + t) * Γ(a)⁻¹`, where
the inverse `Γ(a)⁻¹` is the Dyson series of `-p` at time `a`. -/
theorem dysonSeriesLeft_comp_const_add (hp : Continuous p) (a t : ℝ) :
    dysonSeriesLeft (fun s => p (a + s)) t = dysonSeriesLeft p (a + t) * dysonSeries (-p) a := by
  rw [dysonSeriesLeft_add hp, mul_assoc, dysonSeriesLeft_mul_dysonSeries_neg hp, mul_one]

section Star

variable [StarRing B] [ContinuousStar B]

/-- The adjoint of the left Dyson series of `p` is the Dyson series of the adjoint path
`s ↦ star (p s)`. -/
theorem star_dysonSeriesLeft (hp : Continuous p) (t : ℝ) :
    star (dysonSeriesLeft p t) = dysonSeries (fun s => star (p s)) t := by
  -- Continuity of `star` makes it commute with real scalars.
  have : StarModule ℝ B := ContinuousStar.starModule_real
  -- `star Γ` solves `X' = X (star p)` with `X 0 = 1`.
  simpa using eq_mul_dysonSeries (p := fun s => star (p s)) hp.star
    (f := fun s => star (dysonSeriesLeft p s))
    (fun s => (hasDerivAt_dysonSeriesLeft hp s).star.congr_deriv (by simp [star_mul])) t

/-- The left Dyson series of a skew-adjoint path is unitary. -/
theorem dysonSeriesLeft_mem_unitary (hp : Continuous p) (hskew : ∀ t, star (p t) = -p t)
    (t : ℝ) : dysonSeriesLeft p t ∈ unitary B := by
  -- For a skew-adjoint path the adjoint path is `-p`, whose series inverts the left series.
  rw [Unitary.mem_iff, star_dysonSeriesLeft hp, show (fun s => star (p s)) = -p from funext hskew]
  exact ⟨dysonSeries_neg_mul_dysonSeriesLeft hp t, dysonSeriesLeft_mul_dysonSeries_neg hp t⟩

/-- **Comparison of unitary propagators.** In a C⋆-ring, the left Dyson series of two continuous
skew-adjoint paths `p` and `q` differ at time `t` by at most `|∫₀ᵗ ‖p - q‖|`. -/
theorem norm_dysonSeriesLeft_sub_le [CStarRing B] {q : ℝ → B} (hp : Continuous p)
    (hq : Continuous q) (hpskew : ∀ t, star (p t) = -p t) (hqskew : ∀ t, star (q t) = -q t)
    (t : ℝ) :
    ‖dysonSeriesLeft p t - dysonSeriesLeft q t‖ ≤ |∫ s in 0..t, ‖p s - q s‖| := by
  have : StarModule ℝ B := ContinuousStar.starModule_real
  have hpu := dysonSeriesLeft_mem_unitary hp hpskew
  have hqu := dysonSeriesLeft_mem_unitary hq hqskew
  -- `W = Γ_p⋆ Γ_q` has derivative `Γ_p⋆ (q - p) Γ_q`, whose norm is `‖p - q‖`, and `W 0 = 1`.
  have hW (s : ℝ) : HasDerivAt (fun s => star (dysonSeriesLeft p s) * dysonSeriesLeft q s)
      (star (dysonSeriesLeft p s) * (q s - p s) * dysonSeriesLeft q s) s :=
    ((hasDerivAt_dysonSeriesLeft hp s).star.mul (hasDerivAt_dysonSeriesLeft hq s)).congr_deriv
      (by simp only [star_mul, hpskew]; noncomm_ring)
  have hnorm (s : ℝ) :
      ‖star (dysonSeriesLeft p s) * (q s - p s) * dysonSeriesLeft q s‖ = ‖p s - q s‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ (hqu s),
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (hpu s)), norm_sub_rev]
  have hint := integral_eq_sub_of_hasDerivAt (fun s _ => hW s)
    ((((continuous_dysonSeriesLeft hp).star.mul (hq.sub hp)).mul
      (continuous_dysonSeriesLeft hq)).intervalIntegrable 0 t)
  -- `‖Γ_p - Γ_q‖ = ‖Γ_p⋆ (Γ_p - Γ_q)‖ = ‖W - 1‖`.
  calc ‖dysonSeriesLeft p t - dysonSeriesLeft q t‖
      = ‖star (dysonSeriesLeft p t) * dysonSeriesLeft q t - 1‖ := by
        rw [norm_sub_rev, ← CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (hpu t)), mul_sub,
          Unitary.star_mul_self_of_mem (hpu t)]
    _ = ‖∫ s in 0..t, star (dysonSeriesLeft p s) * (q s - p s) * dysonSeriesLeft q s‖ := by
        rw [hint, dysonSeriesLeft_zero, dysonSeriesLeft_zero, star_one, one_mul]
    _ ≤ |∫ s in 0..t, ‖star (dysonSeriesLeft p s) * (q s - p s) * dysonSeriesLeft q s‖| :=
        norm_integral_le_abs_integral_norm
    _ = |∫ s in 0..t, ‖p s - q s‖| := by simp_rw [hnorm]

end Star

/-- An element commuting with every value of a continuous path `p` commutes with its left Dyson
series. This is `TauCeti.commute_dysonSeries` in the opposite algebra. -/
theorem commute_dysonSeriesLeft (hp : Continuous p) {a : B} (ha : ∀ s, Commute a (p s))
    (t : ℝ) : Commute a (dysonSeriesLeft p t) := by
  have h := commute_dysonSeries (p := fun s => MulOpposite.op (p s))
    (MulOpposite.continuous_op.comp hp) (a := MulOpposite.op a) (fun s => (ha s).op) t
  rw [← op_dysonSeriesLeft] at h
  exact h.unop

/-- The left Dyson series of a `Cⁿ` path is `Cⁿ⁺¹`. -/
theorem contDiff_dysonSeriesLeft {n : ℕ} (hp : ContDiff ℝ n p) :
    ContDiff ℝ (n + 1) (dysonSeriesLeft p) := by
  have hderiv : deriv (dysonSeriesLeft p) = fun t => p t * dysonSeriesLeft p t :=
    funext fun t => (hasDerivAt_dysonSeriesLeft hp.continuous t).deriv
  induction n with
  | zero =>
    refine contDiff_succ_iff_deriv.2
      ⟨fun t => (hasDerivAt_dysonSeriesLeft hp.continuous t).differentiableAt, by simp, ?_⟩
    rw [hderiv]
    exact contDiff_zero.2 (hp.continuous.mul (continuous_dysonSeriesLeft hp.continuous))
  | succ n ih =>
    have hU := ih (hp.of_le (by exact_mod_cast Nat.le_succ n))
    refine contDiff_succ_iff_deriv.2
      ⟨fun t => (hasDerivAt_dysonSeriesLeft hp.continuous t).differentiableAt, by simp, ?_⟩
    rw [hderiv]
    exact_mod_cast hp.mul hU

/-- **Rotating the left equation by a path of complex structures.** Let `J` be a differentiable
path with `J t * J t = -1` and derivative `D`, and let `p` be continuous. Then the left Dyson
series of the rotated path `J D - J p J` is `-J(t) Γ(t) J(0)` for the left Dyson series `Γ` of
`p`: left multiplication by `J` carries solutions of `ξ' = p ξ` to solutions of the rotated
equation. -/
theorem dysonSeriesLeft_mul_sub_mul_mul_eq {J D : ℝ → B} (hJ : ∀ t, HasDerivAt J (D t) t)
    (hJJ : ∀ t, J t * J t = -1) (hD : Continuous D) (hp : Continuous p) (t : ℝ) :
    dysonSeriesLeft (fun t ↦ J t * D t - J t * p t * J t) t =
      -(J t * dysonSeriesLeft p t * J 0) := by
  have hJc : Continuous J := continuous_iff_continuousAt.2 fun t ↦ (hJ t).continuousAt
  -- Differentiating `J * J = -1` gives `D J = -J D`.
  have hDJ (t : ℝ) : D t * J t = -(J t * D t) := eq_neg_of_add_eq_zero_left <| by
    simpa using (ContinuousLinearMap.mul ℝ B).apply_add_apply_eq_zero_of_const (hJ t) (hJ t) hJJ
  have hf (t : ℝ) : HasDerivAt (fun t ↦ -(J t * dysonSeriesLeft p t * J 0))
      ((J t * D t - J t * p t * J t) * -(J t * dysonSeriesLeft p t * J 0)) t := by
    have h := (((hJ t).mul (hasDerivAt_dysonSeriesLeft hp t)).mul_const (J 0)).neg
    convert h using 1
    have h₁ : J t * D t * J t = D t := by
      rw [mul_assoc, hDJ, mul_neg, ← mul_assoc, hJJ, neg_mul, one_mul, neg_neg]
    have h₂ : J t * p t * J t * J t = -(J t * p t) := by
      rw [mul_assoc _ (J t), hJJ, mul_neg, mul_one]
    calc (J t * D t - J t * p t * J t) * -(J t * dysonSeriesLeft p t * J 0)
        = -((J t * D t * J t) * dysonSeriesLeft p t * J 0) +
            (J t * p t * J t * J t) * dysonSeriesLeft p t * J 0 := by noncomm_ring
      _ = _ := by rw [h₁, h₂]; noncomm_ring
  have h0 : -(J 0 * dysonSeriesLeft p 0 * J 0) = 1 := by
    rw [dysonSeriesLeft_zero, mul_one, hJJ, neg_neg]
  have h := eq_dysonSeriesLeft_mul (p := fun t ↦ J t * D t - J t * p t * J t)
    ((hJc.mul hD).sub ((hJc.mul hp).mul hJc)) hf t
  rw [h0, mul_one] at h
  exact h.symm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A continuous linear equation on a closed interval admits an everywhere invertible
fundamental solution starting at any included time. The original coefficient equation holds
at every time of the interval, including its endpoints. -/
theorem exists_isInvertible_hasDerivAt_clm_Icc {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (A : ℝ → X →L[ℝ] X) (hA : ContinuousOn A (Icc a b)) :
    ∃ P : ℝ → X →L[ℝ] X,
      P t₀ = 1 ∧ (∀ t ∈ Icc a b, HasDerivAt P (A t * P t) t) ∧
        ∀ t, (P t).IsInvertible := by
  let B : ℝ → X →L[ℝ] X := fun t ↦ A (projIcc a b (ht₀.1.trans ht₀.2) (t + t₀))
  have hB : Continuous B :=
    (hA.comp_continuous (continuous_subtypeVal.comp continuous_projIcc)
      (fun _ ↦ (projIcc a b (ht₀.1.trans ht₀.2) _).property)).comp
        (continuous_id.add continuous_const)
  refine ⟨fun t ↦ dysonSeriesLeft B (t - t₀), by simp, ?_, ?_⟩
  · intro t ht
    simpa only [Function.comp_def, id_eq, B, sub_add_cancel, projIcc_of_mem _ ht, one_smul] using
      (hasDerivAt_dysonSeriesLeft hB (t - t₀)).scomp t ((hasDerivAt_id t).sub_const t₀)
  · intro t
    exact ContinuousLinearMap.IsInvertible.of_inverse
      (dysonSeriesLeft_mul_dysonSeries_neg hB (t - t₀))
      (dysonSeries_neg_mul_dysonSeriesLeft hB (t - t₀))

/-- **The propagator of a time-dependent linear equation.** Every solution of `w' t = M t (w t)`
for a continuous path `M` of bounded operators is `w t = dysonSeriesLeft M t (w 0)`. -/
theorem eq_dysonSeriesLeft_apply {M : ℝ → X →L[ℝ] X} (hM : Continuous M) {w : ℝ → X}
    (hw : ∀ t, HasDerivAt w (M t (w t)) t) (t : ℝ) : w t = dysonSeriesLeft M t (w 0) := by
  refine congrFun (hM.eq_of_hasDerivAt_clm_apply hw (w := fun t => dysonSeriesLeft M t (w 0))
    (fun t => ?_) (t₀ := 0) (by simp)) t
  simpa using (hasDerivAt_dysonSeriesLeft hM t).clm_apply (hasDerivAt_const t (w 0))

/-- The propagator applied to a fixed vector solves `w' t = M t (w t)`. -/
theorem hasDerivAt_dysonSeriesLeft_apply {M : ℝ → X →L[ℝ] X} (hM : Continuous M) (x : X)
    (t : ℝ) :
    HasDerivAt (fun t => dysonSeriesLeft M t x) (M t (dysonSeriesLeft M t x)) t := by
  simpa using (hasDerivAt_dysonSeriesLeft hM t).clm_apply (hasDerivAt_const t x)

/-- **The return twist of the propagator.** For a continuous path `M` of period `d`, if `x` lies
in the `ε`-eigenspace of `Ψ(d) ^ n`, where `Ψ = dysonSeriesLeft M`, then the solution
`t ↦ Ψ t x` of `w' t = M t (w t)` satisfies `Ψ (t + n d) x = ε • Ψ t x`. -/
theorem dysonSeriesLeft_add_natCast_mul_apply_of_eq_smul {M : ℝ → X →L[ℝ] X} (hM : Continuous M)
    {d : ℝ} (hper : Function.Periodic M d) {n : ℕ} {ε : ℝ} {x : X}
    (hx : (dysonSeriesLeft M d ^ n) x = ε • x) (t : ℝ) :
    dysonSeriesLeft M (t + n * d) x = ε • dysonSeriesLeft M t x := by
  rw [dysonSeriesLeft_add_of_periodic hM (hper.nat_mul n),
    dysonSeriesLeft_natCast_mul_of_periodic hM hper, mul_apply_eq_comp, hx, map_smul]

/-- For a continuous path `M` of period `d`, the solution `t ↦ dysonSeriesLeft M t x` of
`w' t = M t (w t)` has period `d` exactly when `x` is fixed by the propagator over one period. -/
theorem periodic_dysonSeriesLeft_apply_iff {M : ℝ → X →L[ℝ] X} (hM : Continuous M) {d : ℝ}
    (hper : Function.Periodic M d) (x : X) :
    Function.Periodic (fun t => dysonSeriesLeft M t x) d ↔ dysonSeriesLeft M d x = x := by
  refine ⟨fun h => by simpa [dysonSeriesLeft_zero] using h 0, fun h t => ?_⟩
  simpa using dysonSeriesLeft_add_natCast_mul_apply_of_eq_smul hM hper (n := 1) (ε := 1)
    (by simpa using h) t

/-- **The propagator of a skew path preserves the bilinear form.** If `M` is a continuous path of
bounded operators with `B (M r u) w + B u (M r w) = 0`, then the propagator of
`w' t = M t (w t)` preserves `B`. -/
theorem apply_dysonSeriesLeft_apply_dysonSeriesLeft {M : ℝ → X →L[ℝ] X} (hM : Continuous M)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (B : X →L[ℝ] X →L[ℝ] W)
    (hskew : ∀ r u w, B (M r u) w + B u (M r w) = 0) (t : ℝ) (u w : X) :
    B (dysonSeriesLeft M t u) (dysonSeriesLeft M t w) = B u w := by
  have hd (r : ℝ) : HasDerivAt (fun q => B (dysonSeriesLeft M q u) (dysonSeriesLeft M q w)) 0 r :=
    (B.hasDerivAt_of_bilinear (fun _ => hasDerivAt_dysonSeriesLeft_apply hM u r)
      (fun _ => hasDerivAt_dysonSeriesLeft_apply hM w r)).congr_deriv (by rw [add_comm, hskew])
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa [dysonSeriesLeft_zero] using hc

/-- **The inverse propagator is the adjoint for a preserved form.** If the continuous path `M` of
bounded operators is skew for a bilinear map `B`, so that the propagator `Ψ = dysonSeriesLeft M`
preserves `B` (`TauCeti.apply_dysonSeriesLeft_apply_dysonSeriesLeft`), then its inverse
`Ψ(t)⁻¹ = dysonSeries (-M) t` satisfies `B u (Ψ(t)⁻¹ w) = B (Ψ(t) u) w`. -/
theorem apply_dysonSeries_neg_apply {M : ℝ → X →L[ℝ] X} (hM : Continuous M)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (B : X →L[ℝ] X →L[ℝ] W)
    (hskew : ∀ r u w, B (M r u) w + B u (M r w) = 0) (t : ℝ) (u w : X) :
    B u (dysonSeries (-M) t w) = B (dysonSeriesLeft M t u) w := by
  rw [← apply_dysonSeriesLeft_apply_dysonSeriesLeft hM B hskew t u, ← mul_apply_eq_comp,
    dysonSeriesLeft_mul_dysonSeries_neg hM, one_apply_eq_self]

/-- **Variation of constants.** For continuous `M` and `f`, the map
`w t = Ψ t (x + ∫₀ᵗ Ψ(s)⁻¹ (f s) ds)`, where `Ψ = dysonSeriesLeft M` and
`Ψ(s)⁻¹ = dysonSeries (-M) s`, solves the inhomogeneous equation `w' t = M t (w t) + f t`. -/
theorem hasDerivAt_dysonSeriesLeft_apply_add_integral {M : ℝ → X →L[ℝ] X} (hM : Continuous M)
    {f : ℝ → X} (hf : Continuous f) (x : X) (t : ℝ) :
    HasDerivAt (fun t => dysonSeriesLeft M t (x + ∫ s in 0..t, dysonSeries (-M) s (f s)))
      (M t (dysonSeriesLeft M t (x + ∫ s in 0..t, dysonSeries (-M) s (f s))) + f t) t := by
  have hy : HasDerivAt (fun t => x + ∫ s in 0..t, dysonSeries (-M) s (f s))
      (dysonSeries (-M) t (f t)) t :=
    (((continuous_dysonSeries hM.neg).clm_apply hf).integral_hasStrictDerivAt 0 t).hasDerivAt
      |>.const_add x
  refine ((hasDerivAt_dysonSeriesLeft hM t).clm_apply hy).congr_deriv ?_
  rw [← mul_apply_eq_comp, dysonSeriesLeft_mul_dysonSeries_neg hM, one_apply_eq_self,
    mul_apply_eq_comp]

/-- **Variation of constants.** Every solution of `w' t = M t (w t) + f t`, for continuous `M`
and `f`, is `w t = Ψ t (w 0 + ∫₀ᵗ Ψ(s)⁻¹ (f s) ds)`, where `Ψ = dysonSeriesLeft M` and
`Ψ(s)⁻¹ = dysonSeries (-M) s`. -/
theorem eq_dysonSeriesLeft_apply_add_integral {M : ℝ → X →L[ℝ] X} (hM : Continuous M)
    {f : ℝ → X} (hf : Continuous f) {w : ℝ → X} (hw : ∀ t, HasDerivAt w (M t (w t) + f t) t)
    (t : ℝ) : w t = dysonSeriesLeft M t (w 0 + ∫ s in 0..t, dysonSeries (-M) s (f s)) := by
  set v : ℝ → X := fun t => dysonSeriesLeft M t (w 0 + ∫ s in 0..t, dysonSeries (-M) s (f s))
  -- The difference of two solutions solves the homogeneous equation and vanishes at `0`.
  have hd (t : ℝ) : HasDerivAt (fun t => w t - v t) (M t (w t - v t)) t :=
    ((hw t).sub (hasDerivAt_dysonSeriesLeft_apply_add_integral hM hf (w 0) t)).congr_deriv
      (by rw [map_sub]; abel)
  have h0 := eq_dysonSeriesLeft_apply hM hd t
  simp only [v, dysonSeriesLeft_zero, intervalIntegral.integral_same, add_zero,
    one_apply_eq_self, sub_self, map_zero] at h0
  exact sub_eq_zero.1 h0

/-- **The rotated return map.** For a loop `J` of complex structures, `J t * J t = -1` and
`J 1 = J 0`, the return map of the rotated equation `ξ' = (J D - J M J) ξ` of
`dysonSeriesLeft_mul_sub_mul_mul_eq` is conjugate by `J 0` to that of `ξ' = M ξ`, so `1` minus
either has the same determinant. -/
theorem det_one_sub_dysonSeriesLeft_mul_sub_mul_mul {J D M : ℝ → X →L[ℝ] X}
    (hJ : ∀ t, HasDerivAt J (D t) t) (hJJ : ∀ t, J t * J t = -1) (hD : Continuous D)
    (hM : Continuous M) (hJ1 : J 1 = J 0) :
    LinearMap.det ((1 - dysonSeriesLeft (fun t ↦ J t * D t - J t * M t * J t) 1 :
      X →L[ℝ] X) : X →ₗ[ℝ] X) =
      LinearMap.det ((1 - dysonSeriesLeft M 1 : X →L[ℝ] X) : X →ₗ[ℝ] X) := by
  rw [dysonSeriesLeft_mul_sub_mul_mul_eq hJ hJJ hD hM, hJ1]
  set j := J 0
  set Ψ := dysonSeriesLeft M 1
  have h : (1 - -(j * Ψ * j) : X →L[ℝ] X) = -j * (1 - Ψ) * j := by
    calc (1 - -(j * Ψ * j) : X →L[ℝ] X) = -(j * j) * 1 + j * Ψ * j := by
          rw [hJJ, neg_neg, mul_one, sub_neg_eq_add]
      _ = -j * (1 - Ψ) * j := by noncomm_ring
  have hj : ((-j : X →L[ℝ] X) : X →ₗ[ℝ] X) * (j : X →ₗ[ℝ] X) = 1 := by
    rw [← ContinuousLinearMap.toLinearMap_mul, neg_mul, hJJ, neg_neg,
      ContinuousLinearMap.toLinearMap_one]
  rw [h, ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul, map_mul, map_mul,
    mul_right_comm, ← map_mul, hj, map_one, one_mul]

/-- **The deviation from the homogeneous solution.** For `d ≥ 0` there is a constant `C ≥ 0`
such that every solution of `w' = M w + f` with `f` continuous stays within `C ∫₀ᵈ ‖f‖` of the
solution `t ↦ Ψ(t) (w 0)` of `w' = M w` on `[0, d]`, where `Ψ = dysonSeriesLeft M`. -/
theorem exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm {M : ℝ → X →L[ℝ] X}
    (hM : Continuous M) (d : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      ∀ t ∈ Icc 0 d, ‖w t - dysonSeriesLeft M t (w 0)‖ ≤ C * ∫ s in 0..d, ‖f s‖ := by
  obtain ⟨A, hA0, hA⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := d)).exists_forall_norm_apply_le_mul_norm
      (continuous_dysonSeriesLeft hM).continuousOn
  obtain ⟨B, hB0, hB⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := d)).exists_forall_norm_apply_le_mul_norm
      (continuous_dysonSeries hM.neg).continuousOn
  refine ⟨A * B, mul_nonneg hA0 hB0, fun w f hf hw t ht ↦ ?_⟩
  -- By variation of constants, `w t - Ψ(t) (w 0) = Ψ(t) (∫₀ᵗ Ψ(s)⁻¹ (f s) ds)`.
  rw [eq_dysonSeriesLeft_apply_add_integral hM hf hw t, map_add, add_sub_cancel_left]
  calc _ ≤ A * ‖∫ s in 0..t, dysonSeries (-M) s (f s)‖ := hA t ht _
    _ ≤ A * ∫ s in 0..t, B * ‖f s‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le ht.1
          (Filter.Eventually.of_forall fun s hs ↦ hB s ⟨hs.1.le, hs.2.trans ht.2⟩ _)
          ((continuous_const.mul hf.norm).intervalIntegrable _ _)) hA0
    _ = A * B * ∫ s in 0..t, ‖f s‖ := by rw [integral_const_mul]; ring
    _ ≤ A * B * ∫ s in 0..d, ‖f s‖ := mul_le_mul_of_nonneg_left (integral_mono_interval
        le_rfl ht.1 ht.2 (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        (hf.norm.intervalIntegrable _ _)) (mul_nonneg hA0 hB0)

/-- **A bound by the initial value and the forcing.** For `d ≥ 0` there is a constant `C ≥ 0`
such that every solution of `w' = M w + f` with `f` continuous satisfies
`‖w t‖ ≤ C (‖w 0‖ + ∫₀ᵈ ‖f‖)` on `[0, d]`. -/
theorem exists_forall_norm_le_mul_norm_add_integral_norm {M : ℝ → X →L[ℝ] X} (hM : Continuous M)
    (d : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      ∀ t ∈ Icc 0 d, ‖w t‖ ≤ C * (‖w 0‖ + ∫ s in 0..d, ‖f s‖) := by
  obtain ⟨A, hA0, hA⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := d)).exists_forall_norm_apply_le_mul_norm
      (continuous_dysonSeriesLeft hM).continuousOn
  obtain ⟨C, -, hdev⟩ := exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm hM d
  refine ⟨max A C, le_max_of_le_left hA0, fun w f hf hw t ht ↦ ?_⟩
  have hI : 0 ≤ ∫ s in 0..d, ‖f s‖ :=
    intervalIntegral.integral_nonneg (le_trans ht.1 ht.2) fun _ _ ↦ norm_nonneg _
  calc ‖w t‖ ≤ ‖dysonSeriesLeft M t (w 0)‖ + ‖w t - dysonSeriesLeft M t (w 0)‖ :=
        norm_le_insert' _ _
    _ ≤ max A C * ‖w 0‖ + max A C * ∫ s in 0..d, ‖f s‖ :=
        add_le_add ((hA t ht (w 0)).trans (by gcongr; exact le_max_left _ _))
          ((hdev hf hw t ht).trans (by gcongr; exact le_max_right _ _))
    _ = max A C * (‖w 0‖ + ∫ s in 0..d, ‖f s‖) := by ring

/-- **An a priori estimate from a bound on the initial value.** Let `Ψ = dysonSeriesLeft M`,
`d ≥ 0` and `K ≥ 0`. There is a constant `C ≥ 0` such that every solution of `w' = M w + f`, with
`f` continuous and `‖w 0‖ ≤ K ‖w d - Ψ(d) (w 0)‖`, satisfies `‖w t‖ ≤ C ∫₀ᵈ ‖f‖` on `[0, d]`.
A boundary condition which determines `w 0` from the deviation `w d - Ψ(d) (w 0)` thus gives an
a priori estimate. -/
theorem exists_forall_norm_le_mul_integral_norm_of_norm_le {M : ℝ → X →L[ℝ] X}
    (hM : Continuous M) {d : ℝ} (hd : 0 ≤ d) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      ‖w 0‖ ≤ K * ‖w d - dysonSeriesLeft M d (w 0)‖ →
        ∀ t ∈ Icc 0 d, ‖w t‖ ≤ C * ∫ s in 0..d, ‖f s‖ := by
  obtain ⟨C, hC, hdev⟩ := exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm hM d
  obtain ⟨B, hB, hle⟩ := exists_forall_norm_le_mul_norm_add_integral_norm hM d
  refine ⟨B * (K * C + 1), mul_nonneg hB (add_nonneg (mul_nonneg hK hC) zero_le_one),
    fun w f hf hw h0 t ht ↦ ?_⟩
  have h0' : ‖w 0‖ ≤ K * (C * ∫ s in 0..d, ‖f s‖) :=
    h0.trans (mul_le_mul_of_nonneg_left (hdev hf hw d ⟨hd, le_rfl⟩) hK)
  calc ‖w t‖ ≤ B * (‖w 0‖ + ∫ s in 0..d, ‖f s‖) := hle hf hw t ht
    _ ≤ B * (K * (C * ∫ s in 0..d, ‖f s‖) + ∫ s in 0..d, ‖f s‖) := by gcongr
    _ = B * (K * C + 1) * ∫ s in 0..d, ‖f s‖ := by ring

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {M : ℝ → E →L[ℝ] E}

open Complex (I)

variable [CompleteSpace E]

/-- The propagator of a continuous path of complex-linear maps is complex linear. -/
theorem dysonSeriesLeft_apply_I_smul (hM : Continuous M) (hMI : ∀ s v, M s (I • v) = I • M s v)
    (t : ℝ) (v : E) : dysonSeriesLeft M t (I • v) = I • dysonSeriesLeft M t v :=
  ContinuousLinearMap.commute_I_smul_one_iff.1
    (commute_dysonSeriesLeft hM (ContinuousLinearMap.commute_I_smul_one_iff.2 <| hMI ·) t) v

/-- The inverse `dysonSeries (-M)` of the propagator of a continuous path of complex-linear maps
is complex linear. -/
theorem dysonSeries_neg_apply_I_smul (hM : Continuous M) (hMI : ∀ s v, M s (I • v) = I • M s v)
    (t : ℝ) (v : E) : dysonSeries (-M) t (I • v) = I • dysonSeries (-M) t v :=
  ContinuousLinearMap.commute_I_smul_one_iff.1 (commute_dysonSeries hM.neg
    (fun s ↦ (ContinuousLinearMap.commute_I_smul_one_iff.2 (hMI s)).neg_right) t) v

end Complex

end Left

end TauCeti
