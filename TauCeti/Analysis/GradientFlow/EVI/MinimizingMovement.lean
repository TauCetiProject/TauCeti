/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.GradientFlow.MinimizingMovement
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.Topology.MetricSpace.Pseudo.Basic
import TauCeti.Topology.UniformSpace.UniformConvergence.Complete

/-!
# Convergence of minimizing movements to `EVI_λ` gradient flows

Let `φ : X → EReal` be lower semicontinuous on a complete pseudometric space, coercive
(`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0`, `x₁`), and `PenalizedConvex lam τ φ` for small `τ > 0`
(Ambrosio–Gigli–Savaré, Assumption 4.0.1). From every `x₀` with `φ x₀ ≠ ⊤`, minimizing movements
exist (`TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`) and
`t ↦ J ⌈t / τ⌉₊` converges uniformly on `[0, T]` as `τ → 0` to an `EVI_λ` solution starting at `x₀`
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`).

Since `TauCeti.eviDomain lam φ` is closed on a complete space (`TauCeti.isClosed_eviDomain`),
existence on `{x | φ x ≠ ⊤}` extends to every `x₀ ∈ closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_subset`,
`TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex`), giving
`TauCeti.eviDomain lam φ = closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_penalizedConvex`). On a complete CAT(0) pseudometric space,
`λ`-geodesically convex lower semicontinuous energies that never take the value `⊥` satisfy both
hypotheses automatically whenever the effective domain is nonempty.

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`: existence of the `EVI_λ`
  solution and uniform convergence on compact time intervals of minimizing movement interpolants
  as `τ → 0` (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex` and
  `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: existence on `closure {x | φ x ≠ ⊤}` and
  `TauCeti.eviDomain lam φ = closure {x | φ x ≠ ⊤}` under penalized convexity
  (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn`,
  `TauCeti.GeodesicallyConvex.exists_isEVISolution_of_mem_closure`, and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`: CAT(0) corollaries (Jost; Mayer, Theorem 1.13).

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4, Theorems 4.0.4 and 4.1.2, Section 4.2.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, in *Modelling and Optimisation of
  Flows on Networks*, Lecture Notes in Math. 2062, Springer 2013, Theorem 3.25.
* M. G. Crandall, T. M. Liggett, *Generation of semi-groups of nonlinear transformations on general
  Banach spaces*, Amer. J. Math. 93 (1971), 265--298, Lemma 1.2.
* Y. Kobayashi, *Difference approximation of Cauchy problems for quasi-dissipative operators and
  generation of nonlinear semigroups*, J. Math. Soc. Japan 27 (1975), 640--665, Lemma 2.1.
* J. Jost, *Convex functionals and generalized harmonic maps into spaces of nonpositive curvature*,
  Comment. Math. Helv. 70 (1995), 659--673.
* U. F. Mayer, *Gradient flows on nonpositively curved metric spaces and harmonic maps*, Comm.
  Anal. Geom. 6 (1998), 199--253, Section 1 and Theorem 1.13.
-/

public section

noncomputable section

open Filter Finset Set Topology Real
open scoped NNReal ENNReal

namespace TauCeti

section DiscreteComparison

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {φ : X → EReal}

private def barrierC (m T : ℝ) (τ' : ℝ≥0) : ℝ := (2 * |m| * (T + τ') + 5 / 4) / (3 / 2)

private def gridBarrier (τ σ : ℝ≥0) (C : ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ) * τ - (j : ℝ) * σ) ^ 2 + C * (τ + σ) * ((i : ℝ) * τ + (j : ℝ) * σ)

private def cauchyL (T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  A - (E - A) * Real.exp (8 * (T + τ') / τ')

private def cauchyM (m T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  2 * (E - cauchyL T τ' A E) * Real.exp (|m| * (T + τ'))

private def cauchyK (m T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  Real.exp (4 * |m| * (T + τ')) * cauchyM m T τ' A E *
    Real.sqrt (2 * τ' + 2 * barrierC m T τ' * (T + τ'))

private lemma barrierC_nonneg (m : ℝ) {T : ℝ} {τ' : ℝ≥0} (hTτ' : 0 ≤ T + τ') :
    0 ≤ barrierC m T τ' := by
  unfold barrierC; positivity

private lemma cauchyL_le {T : ℝ} {τ' : ℝ≥0} {A E : ℝ} (hAE : A ≤ E) :
    cauchyL T τ' A E ≤ E := by
  have : 0 ≤ (E - A) * Real.exp (8 * (T + τ') / τ') :=
    mul_nonneg (sub_nonneg.2 hAE) (Real.exp_pos _).le
  unfold cauchyL; linarith

private lemma cauchyM_nonneg (m : ℝ) {T : ℝ} {τ' : ℝ≥0} {A E : ℝ} (hAE : A ≤ E) :
    0 ≤ cauchyM m T τ' A E :=
  mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 (cauchyL_le hAE))) (Real.exp_pos _).le

private lemma gridBarrier_ceil_le {τ σ τ' : ℝ≥0} {C T t : ℝ}
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hC : 0 ≤ C) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    gridBarrier τ σ C ⌈t / τ⌉₊ ⌈t / σ⌉₊ ≤ (2 * τ' + 2 * C * (T + τ')) * (τ + σ) := by
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hσr : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hn_lo : t ≤ (⌈t / τ⌉₊ : ℝ) * τ := le_ceil_div_mul hτr
  have hn_hi : (⌈t / τ⌉₊ : ℝ) * τ < t + τ := ceil_div_mul_lt_add ht0 hτr
  have hk_lo : t ≤ (⌈t / σ⌉₊ : ℝ) * σ := le_ceil_div_mul hσr
  have hk_hi : (⌈t / σ⌉₊ : ℝ) * σ < t + σ := ceil_div_mul_lt_add ht0 hσr
  have hdiff_sq : ((⌈t / τ⌉₊ : ℝ) * τ - (⌈t / σ⌉₊ : ℝ) * σ) ^ 2 ≤ (τ + σ) ^ 2 :=
    sq_le_sq.2 (by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ + σ)]
      exact abs_le.2 ⟨by linarith, by linarith⟩)
  have hsum_le : (⌈t / τ⌉₊ : ℝ) * τ + (⌈t / σ⌉₊ : ℝ) * σ ≤ 2 * (T + τ') := by linarith
  have hτσ_sq : ((τ : ℝ) + σ) ^ 2 ≤ 2 * τ' * (τ + σ) := by nlinarith
  unfold gridBarrier
  calc ((⌈t / τ⌉₊ : ℝ) * τ - (⌈t / σ⌉₊ : ℝ) * σ) ^ 2 +
          C * (τ + σ) * ((⌈t / τ⌉₊ : ℝ) * τ + (⌈t / σ⌉₊ : ℝ) * σ)
      ≤ 2 * τ' * (τ + σ) + C * (τ + σ) * (2 * (T + τ')) := by
        gcongr; exact hdiff_sq.trans hτσ_sq
    _ = (2 * τ' + 2 * C * (T + τ')) * (τ + σ) := by ring

/-- **Discrete comparison step** between two minimizing movement sequences `U` (step `τ`) and `V`
(step `σ`) (Kobayashi, Lemma 2.1; Mayer, Section 1; Ambrosio–Gigli–Savaré, Theorem 4.1.2):
cross-testing the one-step variational inequalities eliminates the energies and yields
`((1 + m τ) σ + (1 + m σ) τ) d(U (n + 1), V (k + 1))² ≤
  σ d(U n, V (k + 1))² + τ d(U (n + 1), V k)²`. -/
private theorem discrete_comparison_step {τ σ : ℝ≥0}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    (hUtop : ∀ n, φ (U n) ≠ ⊤) (hUbot : ∀ n, φ (U n) ≠ ⊥)
    (hVtop : ∀ k, φ (V k) ≠ ⊤) (hVbot : ∀ k, φ (V k) ≠ ⊥) (n k : ℕ) :
    ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ)) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
      σ * dist (U n) (V (k + 1)) ^ 2 + τ * dist (U (n + 1)) (V k) ^ 2 := by
  have h1 := hPenτ.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU n) (hVtop (k + 1))
  have h2 := hPenσ.apply_add_le_of_mem_moreauYosidaResolvent hσ (hV k) (hUtop (n + 1))
  have ha : φ (U (n + 1)) = (φ (U (n + 1))).toReal :=
    (EReal.coe_toReal (hUtop (n + 1)) (hUbot (n + 1))).symm
  have hb : φ (V (k + 1)) = (φ (V (k + 1))).toReal :=
    (EReal.coe_toReal (hVtop (k + 1)) (hVbot (k + 1))).symm
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
  have h1m := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (τ : ℝ) * σ)
  have h2m := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * (τ : ℝ) * σ)
  field_simp at h1m h2m
  rw [dist_comm (V (k + 1)) (U (n + 1)), dist_comm (V k) (U (n + 1))] at h2m
  nlinarith [NNReal.coe_nonneg σ, NNReal.coe_nonneg τ,
    mul_nonneg (NNReal.coe_nonneg σ) (sq_nonneg (dist (U n) (U (n + 1)))),
    mul_nonneg (NNReal.coe_nonneg τ) (sq_nonneg (dist (V k) (V (k + 1))))]

/-- Weighted comparison inequality (Crandall–Liggett, Lemma 1.2): setting
`a n k = (1 + m τ) ^ n (1 + m σ) ^ k d(U n, V k)²` with weights `p + q = 1`, we have
`a (n + 1) (k + 1) ≤ p * a n (k + 1) + q * a (n + 1) k`. -/
private theorem weighted_comparison_step {τ σ : ℝ≥0}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hmτ : 0 < 1 + m * τ) (hmσ : 0 < 1 + m * σ)
    {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    (hUtop : ∀ n, φ (U n) ≠ ⊤) (hUbot : ∀ n, φ (U n) ≠ ⊥)
    (hVtop : ∀ k, φ (V k) ≠ ⊤) (hVbot : ∀ k, φ (V k) ≠ ⊥) (n k : ℕ) :
    (1 + m * τ) ^ (n + 1) * (1 + m * σ) ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
      ((σ : ℝ) * (1 + m * τ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        ((1 + m * τ) ^ n * (1 + m * σ) ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
      ((τ : ℝ) * (1 + m * σ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        ((1 + m * τ) ^ (n + 1) * (1 + m * σ) ^ k * dist (U (n + 1)) (V k) ^ 2) := by
  have hstep := discrete_comparison_step hPenτ hPenσ hτ hσ hU hV hUtop hUbot hVtop hVbot n k
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  set γ : ℝ := (σ : ℝ) * r₁ + τ * r₂
  have hγ : 0 < γ :=
    add_pos (mul_pos (NNReal.coe_pos.2 hσ) hmτ) (mul_pos (NNReal.coe_pos.2 hτ) hmσ)
  have hmul := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep
      (mul_nonneg (pow_nonneg hmτ.le (n + 1)) (pow_nonneg hmσ.le (k + 1)))) hγ.le
  refine (le_of_eq ?_).trans (hmul.trans_eq ?_)
  · field_simp [hγ.ne']
  · rw [pow_succ r₁ n, pow_succ r₂ k]
    field_simp [hγ.ne']

/-- The discrete heat-equation barrier `gridBarrier` is a supersolution of the `(p, q)` random walk
on the grid `(n + 1) τ ≤ T + τ'`, `(k + 1) σ ≤ T + τ'` (Crandall–Liggett, Lemma 1.2;
Kobayashi, Lemma 2.1). -/
private theorem barrier_superharmonic {τ σ τ' : ℝ≥0} {T : ℝ}
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4) {n k : ℕ}
    (hn : ((n + 1 : ℕ) : ℝ) * τ ≤ T + τ') (hk : ((k + 1 : ℕ) : ℝ) * σ ≤ T + τ') :
    ((σ : ℝ) * (1 + m * τ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        gridBarrier τ σ (barrierC m T τ') n (k + 1) +
      ((τ : ℝ) * (1 + m * σ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        gridBarrier τ σ (barrierC m T τ') (n + 1) k ≤
      gridBarrier τ σ (barrierC m T τ') (n + 1) (k + 1) := by
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  set γ : ℝ := (σ : ℝ) * r₁ + τ * r₂
  set C : ℝ := barrierC m T τ'
  have hτ0 : (0 : ℝ) ≤ τ := NNReal.coe_nonneg τ
  have hσ0 : (0 : ℝ) ≤ σ := NNReal.coe_nonneg σ
  have hr₁_lo : 3 / 4 ≤ r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  have hr₁_hi : r₁ ≤ 5 / 4 := by dsimp [r₁]; nlinarith [le_abs_self m]
  have hr₂_lo : 3 / 4 ≤ r₂ := by dsimp [r₂]; nlinarith [neg_abs_le m]
  have hr₂_hi : r₂ ≤ 5 / 4 := by dsimp [r₂]; nlinarith [le_abs_self m]
  have hr₁0 : 0 ≤ r₁ := by linarith
  have hr₂0 : 0 ≤ r₂ := by linarith
  have hTτ' : 0 ≤ T + τ' := le_trans (mul_nonneg (Nat.cast_nonneg _) hτ0) hn
  -- Bound the drift and variance terms against the linear drift `C (τ + σ) (r₁ + r₂)`.
  set x : ℝ := ((n + 1 : ℕ) : ℝ) * τ - ((k + 1 : ℕ) : ℝ) * σ
  have hx : |x| ≤ T + τ' := abs_le.2 ⟨by linarith [mul_nonneg (Nat.cast_nonneg (n + 1)) hτ0],
    by linarith [mul_nonneg (Nat.cast_nonneg (k + 1)) hσ0]⟩
  have hστ : |((σ : ℝ) - τ)| ≤ τ + σ :=
    (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hσ0, abs_of_nonneg hτ0]; ring)
  have hcross : 2 * x * m * ((σ : ℝ) - τ) ≤ 2 * |m| * (T + τ') * (τ + σ) := by
    calc 2 * x * m * ((σ : ℝ) - τ) ≤ |2 * x * m * ((σ : ℝ) - τ)| := le_abs_self _
      _ = 2 * |x| * |m| * |((σ : ℝ) - τ)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg two_pos.le]
      _ ≤ 2 * (T + τ') * |m| * (τ + σ) := by gcongr
      _ = 2 * |m| * (T + τ') * (τ + σ) := by ring
  have hconst : r₁ * τ + r₂ * σ ≤ 5 / 4 * (τ + σ) := by nlinarith
  have hC : (2 * |m| * (T + τ') + 5 / 4) * (τ + σ) ≤ C * (τ + σ) * (r₁ + r₂) := by
    have hC0 : 0 ≤ C * (τ + σ) := mul_nonneg (barrierC_nonneg m hTτ') (by positivity)
    calc (2 * |m| * (T + τ') + 5 / 4) * (τ + σ)
        = C * (τ + σ) * (3 / 2) := by unfold C barrierC; field_simp
      _ ≤ C * (τ + σ) * (r₁ + r₂) := by gcongr; linarith
  set rhs : ℝ := 2 * x * m * ((σ : ℝ) - τ) + r₁ * τ + r₂ * σ - C * (τ + σ) * (r₁ + r₂)
  have hmain : rhs ≤ 0 := by dsimp [rhs]; linarith
  -- Clear the positive denominator `γ` (treating the degenerate `τ = σ = 0` case separately).
  rcases eq_or_lt_of_le (show 0 ≤ γ by positivity) with hγ0 | hγpos
  · have hστ0 : (τ : ℝ) = 0 ∧ (σ : ℝ) = 0 :=
      ⟨by nlinarith [mul_nonneg hσ0 hr₁0], by nlinarith [mul_nonneg hτ0 hr₂0]⟩
    unfold gridBarrier
    rw [hστ0.1, hστ0.2]
    norm_num
  have hid : γ * (((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
      ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k -
      gridBarrier τ σ C (n + 1) (k + 1)) = (τ : ℝ) * σ * rhs := by
    unfold gridBarrier
    field_simp [hγpos.ne']
    dsimp [rhs, γ, r₁, r₂, x]
    push_cast
    ring
  have hneg : γ * (((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
      ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k -
      gridBarrier τ σ C (n + 1) (k + 1)) ≤ 0 :=
    hid ▸ mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hτ0 hσ0) hmain
  nlinarith

/-- Every iterate of a minimizing movement sequence started at a finite-energy point `x₀` under a
coercive energy `φ_{τ'}(x₀) = A` has finite energy (`≠ ⊤` and `≠ ⊥`). -/
private lemma apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent
    {δ τ' : ℝ≥0} {x₀ : X} {A E : ℝ} (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    {W : ℕ → X} (hW0 : W 0 = x₀)
    (hW : ∀ n, W (n + 1) ∈ moreauYosidaResolvent φ δ (W n)) :
    (∀ n, φ (W n) ≠ ⊤) ∧ (∀ n, φ (W n) ≠ ⊥) := by
  refine ⟨fun n ↦ ?_, fun n ↦ apply_ne_bot_of_moreauYosida_ne_bot
    (hA ▸ EReal.coe_ne_bot A) (edist_ne_top x₀ (W n))⟩
  have hle := antitone_comp_of_forall_mem_moreauYosidaResolvent hW (Nat.zero_le n)
  simp only [Function.comp_apply, hW0, hE] at hle
  exact ne_top_of_le_ne_top (EReal.coe_ne_top E) hle

/-- Boundary estimate at `k = 0`: for `n ≤ ⌈T / τ⌉₊`,
`(1 + m τ) ^ n * d(U n, x₀)² ≤ cauchyM * √(gridBarrier τ σ C n 0)`. -/
private theorem boundary_comparison_left {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ') (hmτ : |m| * τ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U : ℕ → X} (hU0 : U 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {n : ℕ} (hn : n ≤ ⌈T / τ⌉₊) :
    (1 + m * τ) ^ n * dist (U n) x₀ ^ 2 ≤
      cauchyM m T τ' A E * Real.sqrt (gridBarrier τ σ (barrierC m T τ') n 0) := by
  set r₁ : ℝ := 1 + m * τ
  set L : ℝ := cauchyL T τ' A E
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have hτ_le_τ' : (τ : ℝ) ≤ τ' := by linarith
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := cauchyM_nonneg m hAE
  have hC0 : 0 ≤ C := barrierC_nonneg m (add_nonneg hT (NNReal.coe_nonneg τ'))
  have hr₁0 : 0 ≤ r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  -- Combine the uniform energy lower bound `L ≤ φ (U n)` with the multi-step dissipation bound.
  have hlow_n : (L : EReal) ≤ φ (U n) :=
    (le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hU hτ hττ'
      (hU0 ▸ hA).ge (hU0 ▸ hE).le hT hn).1
  obtain ⟨htop_U, hbot_U⟩ :=
    apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent hA hE hU0 hU
  set en : ℝ := (φ (U n)).toReal
  have hen : φ (U n) = en := (EReal.coe_toReal (htop_U n) (hbot_U n)).symm
  have hL_en : L ≤ en := by exact_mod_cast hen ▸ hlow_n
  have hdist : dist (U n) x₀ ^ 2 ≤ 2 * (E - L) * ((n : ℝ) * τ) := by
    have hstep :=
      toReal_edist_sq_le_mul_sub_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le n) (hU0 ▸ hE)
        hen
    rw [Nat.sub_zero, hU0, ← dist_edist, dist_comm] at hstep
    calc dist (U n) x₀ ^ 2 ≤ 2 * ((n : ℝ) * τ) * (E - en) := hstep
      _ ≤ 2 * ((n : ℝ) * τ) * (E - L) := by gcongr
      _ = 2 * (E - L) * ((n : ℝ) * τ) := by ring
  have hr₁_exp : r₁ ^ n ≤ Real.exp (|m| * (T + τ')) := by
    have hr₁_le : r₁ ≤ 1 + |m| * τ := by dsimp [r₁]; nlinarith [le_abs_self m]
    calc r₁ ^ n ≤ (1 + |m| * τ) ^ n := pow_le_pow_left₀ hr₁0 hr₁_le n
      _ ≤ (1 + |m| * τ) ^ ⌈T / τ⌉₊ :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn
      _ ≤ Real.exp (|m| * (T + τ)) :=
          one_add_mul_pow_ceil_div_le_exp (abs_nonneg m) (add_nonneg hT hτr.le)
      _ ≤ Real.exp (|m| * (T + τ')) := Real.exp_le_exp.2 (by gcongr)
  have hnτ_sqrt : (n : ℝ) * τ ≤ Real.sqrt (gridBarrier τ σ C n 0) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : 0 ≤ C * ((τ : ℝ) + σ) * ((n : ℝ) * τ + 0) :=
      mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity)
    unfold gridBarrier
    simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero]
    linarith
  calc r₁ ^ n * dist (U n) x₀ ^ 2
      ≤ Real.exp (|m| * (T + τ')) * (2 * (E - L) * ((n : ℝ) * τ)) :=
        mul_le_mul hr₁_exp hdist (sq_nonneg _) (by positivity)
    _ = M * ((n : ℝ) * τ) := by unfold M cauchyM L; ring
    _ ≤ M * Real.sqrt (gridBarrier τ σ C n 0) := mul_le_mul_of_nonneg_left hnτ_sqrt hM0

/-- Inductive lattice barrier comparison (Crandall–Liggett, Lemma 1.2; Kobayashi, Lemma 2.1):
on the grid `n ≤ ⌈T / τ⌉₊`, `k ≤ ⌈T / σ⌉₊`, the weighted squared distance
`(1 + m τ) ^ n (1 + m σ) ^ k d(U n, V k)²` is bounded by `cauchyM * √(gridBarrier n k)`. -/
private theorem grid_comparison {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {n k : ℕ} (hn : n ≤ ⌈T / τ⌉₊) (hk : k ≤ ⌈T / σ⌉₊) :
    (1 + m * τ) ^ n * (1 + m * σ) ^ k * dist (U n) (V k) ^ 2 ≤
      cauchyM m T τ' A E * Real.sqrt (gridBarrier τ σ (barrierC m T τ') n k) := by
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  set Φ : ℕ → ℕ → ℝ := gridBarrier τ σ C
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hσr : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  have hr₁_pos : 0 < r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  have hr₂_pos : 0 < r₂ := by dsimp [r₂]; nlinarith [neg_abs_le m]
  obtain ⟨hUtop, hUbot⟩ := apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent hA hE hU0 hU
  obtain ⟨hVtop, hVbot⟩ := apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent hA hE hV0 hV
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := cauchyM_nonneg m hAE
  have hC0 : 0 ≤ C := barrierC_nonneg m (add_nonneg hT (NNReal.coe_nonneg τ'))
  have hΦ0 : ∀ i j : ℕ, 0 ≤ Φ i j := fun i j ↦ by
    unfold Φ gridBarrier
    exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity))
  -- Induct on `(n, k)`: the axes `n = 0` and `k = 0` use `boundary_comparison_left`; interior
  -- steps combine `weighted_comparison_step`, `Real.sqrt` concavity, and `barrier_superharmonic`.
  induction n generalizing k with
  | zero =>
    have hs := boundary_comparison_left (φ := φ) (x₀ := x₀) (m := m) (τ := σ) (σ := τ)
      hσ hστ' hmσ hA hE hT hV0 hV hk
    have hsymm : gridBarrier σ τ C k 0 = Φ 0 k := by
      unfold Φ gridBarrier
      simp only [Nat.cast_zero]
      ring
    rw [hU0, pow_zero, one_mul, dist_comm, ← hsymm]
    exact hs
  | succ n ihn =>
    induction k with
    | zero =>
      rw [hV0, pow_zero, mul_one]
      exact boundary_comparison_left (φ := φ) (x₀ := x₀) (m := m) (τ := τ) (σ := σ)
        hτ hττ' hmτ hA hE hT hU0 hU hn
    | succ k ihk =>
      have hn_lt : ((n + 1 : ℕ) : ℝ) * τ ≤ T + τ' :=
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hn) hτr.le).trans
          (ceil_div_mul_lt_add hT hτr).le).trans (by linarith)
      have hk_lt : ((k + 1 : ℕ) : ℝ) * σ ≤ T + τ' :=
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hσr.le).trans
          (ceil_div_mul_lt_add hT hσr).le).trans (by linarith)
      set γ : ℝ := σ * r₁ + τ * r₂
      set p : ℝ := σ * r₁ / γ
      set q : ℝ := τ * r₂ / γ
      have hγ : 0 < γ := add_pos (mul_pos hσr hr₁_pos) (mul_pos hτr hr₂_pos)
      have hp0 : 0 ≤ p := div_nonneg (mul_nonneg hσr.le hr₁_pos.le) hγ.le
      have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hτr.le hr₂_pos.le) hγ.le
      have hpq : p + q = 1 := by dsimp [p, q, γ]; field_simp
      have hstep := weighted_comparison_step hPenτ hPenσ hτ hσ hr₁_pos hr₂_pos hU hV
        hUtop hUbot hVtop hVbot n k
      have h1 := ihn (Nat.le_of_succ_le hn) hk
      have h2 := ihk (Nat.le_of_succ_le hk)
      have hbar := barrier_superharmonic (τ := τ) (σ := σ) (τ' := τ') (T := T)
        hmτ hmσ hn_lt hk_lt
      have hsqrt : p * Real.sqrt (Φ n (k + 1)) + q * Real.sqrt (Φ (n + 1) k) ≤
          Real.sqrt (Φ (n + 1) (k + 1)) :=
        (Real.strictConcaveOn_sqrt.concaveOn.2 (hΦ0 n (k + 1)) (hΦ0 (n + 1) k)
          hp0 hq0 hpq).trans (Real.sqrt_le_sqrt hbar)
      calc r₁ ^ (n + 1) * r₂ ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2
          ≤ p * (r₁ ^ n * r₂ ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
              q * (r₁ ^ (n + 1) * r₂ ^ k * dist (U (n + 1)) (V k) ^ 2) := hstep
        _ ≤ p * (M * Real.sqrt (Φ n (k + 1))) + q * (M * Real.sqrt (Φ (n + 1) k)) := by gcongr
        _ = M * (p * Real.sqrt (Φ n (k + 1)) + q * Real.sqrt (Φ (n + 1) k)) := by ring
        _ ≤ M * Real.sqrt (Φ (n + 1) (k + 1)) := by gcongr

/-- **Uniform Cauchy comparison between minimizing movement interpolants**
(Crandall–Liggett, Lemma 1.2; Kobayashi, Lemma 2.1; Mayer, Section 1;
Ambrosio–Gigli–Savaré, Section 4.2). For minimizing movement sequences `U`, `V`
started at `x₀` with `φ x₀ = E` and `φ_{τ'}(x₀) = A`, when `4 τ ≤ τ'`, `4 σ ≤ τ'`,
`|m| τ ≤ 1 / 4`, `|m| σ ≤ 1 / 4`, and `t ∈ [0, T]`, we have
`dist (U ⌈t / τ⌉₊) (V ⌈t / σ⌉₊) ^ 2 ≤ cauchyK m T τ' A E * √(τ + σ)`. -/
private theorem dist_ceil_sq_le_of_penalizedConvex {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    dist (U ⌈t / τ⌉₊) (V ⌈t / σ⌉₊) ^ 2 ≤
      cauchyK m T τ' A E * Real.sqrt (τ + σ) := by
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  set Φ : ℕ → ℕ → ℝ := gridBarrier τ σ C
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hσr : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hτ_le_τ' : (τ : ℝ) ≤ τ' := by linarith
  have hσ_le_τ' : (σ : ℝ) ≤ τ' := by linarith
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  have hr₁_lo : 1 / 2 ≤ r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  have hr₂_lo : 1 / 2 ≤ r₂ := by dsimp [r₂]; nlinarith [neg_abs_le m]
  have hr₁_pos : 0 < r₁ := by linarith
  have hr₂_pos : 0 < r₂ := by linarith
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := cauchyM_nonneg m hAE
  have hC0 : 0 ≤ C := barrierC_nonneg m (add_nonneg hT (NNReal.coe_nonneg τ'))
  -- Evaluate `grid_comparison` along the near-diagonal indices `n = ⌈t / τ⌉₊`, `k = ⌈t / σ⌉₊`.
  set n := ⌈t / τ⌉₊
  set k := ⌈t / σ⌉₊
  have hnT : n ≤ ⌈T / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right htT hτr.le)
  have hkT : k ≤ ⌈T / σ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right htT hσr.le)
  have hsqrt_le : Real.sqrt (Φ n k) ≤
      Real.sqrt (2 * τ' + 2 * C * (T + τ')) * Real.sqrt (τ + σ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (gridBarrier_ceil_le hτ hσ hττ' hστ' hC0 ht0 htT)
  -- Unwind the weights `r₁ ^ n * r₂ ^ k` via `inv_one_add_mul_pow_ceil_div_le_exp`.
  have hinv_r₁ : r₁⁻¹ ^ n ≤ Real.exp (2 * |m| * (T + τ')) :=
    (inv_one_add_mul_pow_ceil_div_le_exp (by norm_num : (0 : ℝ) < 1 / 2) hr₁_lo
      (by linarith)).trans (Real.exp_le_exp.2 (by
        rw [div_div_eq_mul_div, div_one, mul_comm |m|]; gcongr))
  have hinv_r₂ : r₂⁻¹ ^ k ≤ Real.exp (2 * |m| * (T + τ')) :=
    (inv_one_add_mul_pow_ceil_div_le_exp (by norm_num : (0 : ℝ) < 1 / 2) hr₂_lo
      (by linarith)).trans (Real.exp_le_exp.2 (by
        rw [div_div_eq_mul_div, div_one, mul_comm |m|]; gcongr))
  have hinv_prod : r₁⁻¹ ^ n * r₂⁻¹ ^ k ≤ Real.exp (4 * |m| * (T + τ')) := by
    calc r₁⁻¹ ^ n * r₂⁻¹ ^ k
        ≤ Real.exp (2 * |m| * (T + τ')) * Real.exp (2 * |m| * (T + τ')) :=
          mul_le_mul hinv_r₁ hinv_r₂ (by positivity) (by positivity)
      _ = Real.exp (4 * |m| * (T + τ')) := by rw [← Real.exp_add]; ring_nf
  have hdist_eq : dist (U n) (V k) ^ 2 =
      (r₁⁻¹ ^ n * r₂⁻¹ ^ k) * (r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2) := by
    have hr₁_ne : r₁ ^ n ≠ 0 := pow_ne_zero n hr₁_pos.ne'
    have hr₂_ne : r₂ ^ k ≠ 0 := pow_ne_zero k hr₂_pos.ne'
    simp only [inv_pow]
    field_simp
  rw [hdist_eq]
  calc (r₁⁻¹ ^ n * r₂⁻¹ ^ k) * (r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2)
      ≤ Real.exp (4 * |m| * (T + τ')) * (M * Real.sqrt (Φ n k)) :=
        mul_le_mul hinv_prod
          (grid_comparison hPenτ hPenσ hτ hσ hττ' hστ' hmτ hmσ hA hE hT hU0 hV0 hU hV hnT hkT)
          (mul_nonneg (mul_nonneg (pow_nonneg hr₁_pos.le n) (pow_nonneg hr₂_pos.le k))
            (sq_nonneg _)) (by positivity)
    _ ≤ Real.exp (4 * |m| * (T + τ')) *
          (M * (Real.sqrt (2 * τ' + 2 * C * (T + τ')) * Real.sqrt (τ + σ))) := by gcongr
    _ = cauchyK m T τ' A E * Real.sqrt (τ + σ) := by unfold cauchyK; ring

end DiscreteComparison

section Existence

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}

/-- Passing the discrete multi-step `PenalizedConvex.apply_le` inequality along ceiling indices to
a pointwise limit curve gives the continuous endpoint energy regularization estimate. -/
private lemma apply_le_of_tendsto_ceil
    (hφ : LowerSemicontinuous φ) {τ₁ : ℝ≥0}
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    (hbot : ∀ z, φ z ≠ ⊥)
    {τc : ℕ → ℝ≥0} {Jc : ℕ → ℕ → X} (hτc : ∀ j, 0 < τc j) (hτcτ₁ : ∀ j, τc j < τ₁)
    (hτc0 : Tendsto τc atTop (𝓝 0)) (hlamτc : ∀ j, 0 < 1 + lam * (τc j : ℝ))
    (hJc : ∀ j k, Jc j (k + 1) ∈ moreauYosidaResolvent φ (τc j) (Jc j k))
    {u : ℝ → X} (hu_lim : ∀ t ≥ 0, Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 (u t)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - Real.exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in (0 : ℝ)..(t - s), Real.exp (lam * r)) : ℝ) : EReal) := by
  set n : ℕ → ℕ := fun j ↦ ⌈s / (τc j : ℝ)⌉₊
  set m : ℕ → ℕ := fun j ↦ ⌈t / (τc j : ℝ)⌉₊
  have hτc_real : Tendsto (fun j ↦ (τc j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτc0
  have hτc_pos : ∀ᶠ j in atTop, (0 : ℝ) < τc j :=
    Eventually.of_forall fun j ↦ NNReal.coe_pos.2 (hτc j)
  have hev_lt : ∀ᶠ j in atTop, n j < m j :=
    eventually_ceil_div_lt_ceil_div (hs.trans_lt hst) hst hτc_pos hτc_real
  have hN_lim : Tendsto (fun j ↦ ((m j - n j : ℕ) : ℝ) * τc j) atTop (𝓝 (t - s)) :=
    tendsto_ceil_div_sub_ceil_div_mul hs hst.le hτc_pos hτc_real
  have hrhs_lim : Tendsto (fun j ↦ φ y +
      (((dist (Jc j (n j)) y ^ 2 - (1 + lam * (τc j : ℝ)) ^ (m j - n j) *
          dist (Jc j (m j)) y ^ 2) /
        (2 * (τc j : ℝ) *
          ∑ k ∈ range (m j - n j), (1 + lam * (τc j : ℝ)) ^ k) : ℝ) : EReal))
      atTop (𝓝 (φ y + (((dist (u s) y ^ 2 - Real.exp (lam * (t - s)) * dist (u t) y ^ 2) /
        (2 * ∫ r in (0 : ℝ)..(t - s), Real.exp (lam * r)) : ℝ) : EReal))) := by
    have hnum : Tendsto (fun j ↦ dist (Jc j (n j)) y ^ 2 -
        (1 + lam * (τc j : ℝ)) ^ (m j - n j) * dist (Jc j (m j)) y ^ 2) atTop
        (𝓝 (dist (u s) y ^ 2 - Real.exp (lam * (t - s)) * dist (u t) y ^ 2)) :=
      (((hu_lim s hs).dist tendsto_const_nhds).pow 2).sub
        ((tendsto_one_add_mul_pow hτc_real hN_lim).mul
          (((hu_lim t (hs.trans hst.le)).dist tendsto_const_nhds).pow 2))
    have hden : Tendsto (fun j ↦ 2 * (τc j : ℝ) *
        ∑ k ∈ range (m j - n j), (1 + lam * (τc j : ℝ)) ^ k) atTop
        (𝓝 (2 * ∫ r in (0 : ℝ)..(t - s), Real.exp (lam * r))) := by
      simpa only [mul_assoc] using (tendsto_mul_sum_one_add_mul_pow hτc_real hN_lim).const_mul 2
    have hfrac :=
      hnum.div hden (mul_ne_zero two_ne_zero (integral_exp_mul_pos lam (sub_pos.2 hst)).ne')
    lift φ y to ℝ using ⟨hy, hbot y⟩ with py
    exact ((continuous_coe_real_ereal.tendsto _).comp (hfrac.const_add py)).congr
      fun _ ↦ by simp
  have hdisc : ∀ᶠ j in atTop, φ (Jc j (m j)) ≤ φ y +
      (((dist (Jc j (n j)) y ^ 2 - (1 + lam * (τc j : ℝ)) ^ (m j - n j) *
          dist (Jc j (m j)) y ^ 2) /
        (2 * (τc j : ℝ) *
          ∑ k ∈ range (m j - n j), (1 + lam * (τc j : ℝ)) ^ k) : ℝ) : EReal) := by
    filter_upwards [hev_lt] with j hj
    have hshift := (hconv (τc j) (hτc j) (hτcτ₁ j)).apply_le
      (hτc j) (hlamτc j).le (U := fun k ↦ Jc j (n j + k)) (fun k ↦ hJc j (n j + k))
      hy (Nat.sub_pos_of_lt hj)
    rwa [Nat.add_zero, Nat.add_sub_cancel' hj.le] at hshift
  exact ((hφ.le_liminf (u t)).trans (hu_lim t (hs.trans hst.le)).liminf_le_liminf_comp).trans
    ((liminf_le_liminf hdisc).trans_eq hrhs_lim.liminf_eq)

/-- Passing the discrete multi-step `PenalizedConvex` variational inequality and the minimizing
movement absolute continuity estimate to a pointwise limit curve yields an `IsEVISolution`. -/
private lemma isEVISolution_of_tendsto_ceil
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤)
    {τc : ℕ → ℝ≥0} {Jc : ℕ → ℕ → X} (hτc : ∀ j, 0 < τc j) (hτcτ₁ : ∀ j, τc j < τ₁)
    (hτc0 : Tendsto τc atTop (𝓝 0)) (hlamτc : ∀ j, 0 < 1 + lam * (τc j : ℝ))
    (hJc0 : ∀ j, Jc j 0 = x₀)
    (hJc : ∀ j k, Jc j (k + 1) ∈ moreauYosidaResolvent φ (τc j) (Jc j k))
    {u : ℝ → X} (hu_lim : ∀ t ≥ 0, Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 (u t))) :
    IsEVISolution lam φ u := by
  have hbot : ∀ z, φ z ≠ ⊥ := fun z ↦
    apply_ne_bot_of_moreauYosida_ne_bot h₀ (edist_ne_top x₁ z)
  have hu_cont : ContinuousOn u (Ici 0) := continuousOn_Ici_of_forall_Icc fun T hT ↦ by
    have hS : ∀ j, φ (Jc j 0) ≤ (φ x₀).toReal := fun j ↦ by
      rw [hJc0 j, EReal.coe_toReal hx₀ (hbot x₀)]
    have hAC := absolutelyContinuousOnInterval_of_forall_mem_moreauYosidaResolvent
      (l := 𝓝) (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge) hτ₀ h₀ hτc hτc0 hJc
      (by simpa only [hJc0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x₀) atTop (𝓝 x₀)))
      hS (fun t ht ↦ hu_lim t ht.1) hT
    exact uIcc_of_le hT ▸ hAC.continuousOn'
  exact isEVISolution_of_apply_le hφ hu_cont
    (fun t ht ↦ ne_top_of_le_ne_top (EReal.add_ne_top hx₀ (EReal.coe_ne_top _))
      (apply_le_of_tendsto_ceil hφ hconv hbot hτc hτcτ₁ hτc0 hlamτc hJc hu_lim hx₀
        (le_refl (0 : ℝ)) ht))
    (fun t _ ↦ hbot (u t))
    (fun _ hy _ _ hs hst ↦
      apply_le_of_tendsto_ceil hφ hconv hbot hτc hτcτ₁ hτc0 hlamτc hJc hu_lim hy hs hst)

/-- **Existence of `EVI_λ` flows and uniform convergence of minimizing movements**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4; Ambrosio–Gigli, Theorem 3.25). Let `φ : X → EReal`
be lower semicontinuous on a complete pseudometric space, coercive (`φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0`), and `lam`-penalized convex for all sufficiently small `τ > 0`. Then from every
point `x₀` of finite energy starts an `EVI_λ` solution `u` with `u 0 = x₀`, and the piecewise
constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of every minimizing movement scheme eventually starting
at `x₀` with positive time steps `τ j → 0` converge to `u` uniformly on `[0, T]` for every `T : ℝ`.
-/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ᶠ j in atTop, J j 0 = x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  -- Step 1: Choose a common reference scale `τ'` where `φ_{τ'}(x₀)` is finite and `|lam| τ' ≤ 1/4`.
  set r₀ : ℝ := (4 * (|lam| + 1))⁻¹
  have hr₀ : 0 < r₀ := by positivity
  set τ' : ℝ≥0 := min (τ₀ / 2) (min (τ₁ / 2) r₀.toNNReal)
  have hτ' : 0 < τ' :=
    lt_min (half_pos hτ₀) (lt_min (half_pos hτ₁) (Real.toNNReal_pos.2 hr₀))
  have hτ'τ₀ : τ' < τ₀ := (min_le_left _ _).trans_lt (half_lt_self hτ₀)
  have hτ'τ₁ : τ' < τ₁ :=
    (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hτ₁))
  have hlamτ' : |lam| * (τ' : ℝ) ≤ 1 / 4 := by
    have hτ'le : (τ' : ℝ) ≤ r₀ :=
      (NNReal.coe_le_coe.2 ((min_le_right _ _).trans (min_le_right _ _))).trans_eq
        (Real.coe_toNNReal r₀ hr₀.le)
    calc |lam| * (τ' : ℝ) ≤ (|lam| + 1) * r₀ :=
          mul_le_mul (by linarith) hτ'le (NNReal.coe_nonneg _) (by positivity)
      _ = 1 / 4 := by dsimp [r₀]; field_simp
  have hAbot : moreauYosida φ τ' x₀ ≠ ⊥ :=
    moreauYosida_ne_bot_of_lt hτ'τ₀ (edist_ne_top x₀ x₁) h₀
  have hAtop : moreauYosida φ τ' x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀)
  set A : ℝ := (moreauYosida φ τ' x₀).toReal
  set E : ℝ := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A := (EReal.coe_toReal hAtop hAbot).symm
  have hE : φ x₀ = E :=
    (EReal.coe_toReal hx₀ (apply_ne_bot_of_moreauYosida_ne_bot h₀ (edist_ne_top x₁ x₀))).symm
  have hpair : ∀ {τ σ : ℝ≥0} {U V : ℕ → X} {T : ℝ}, 0 ≤ T →
      0 < τ → 0 < σ → 4 * τ ≤ τ' → 4 * σ ≤ τ' → U 0 = x₀ → V 0 = x₀ →
      (∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) →
      (∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k)) →
      ∀ t ∈ Icc 0 T,
        dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
          cauchyK lam T τ' A E * Real.sqrt ((τ : ℝ) + σ) := by
    intro τ σ U V T hT hτ hσ hττ' hστ' hU0 hV0 hU hV t ht
    have h4_le : ∀ {δ : ℝ≥0}, 4 * δ ≤ τ' → (δ : ℝ) ≤ τ' := fun {δ} h4 ↦ by
      have : (4 : ℝ) * δ ≤ τ' := by exact_mod_cast h4
      linarith [NNReal.coe_nonneg δ]
    have hττ₁ : τ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hττ')).trans_lt hτ'τ₁
    have hστ₁ : σ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hστ')).trans_lt hτ'τ₁
    have hmτ := (mul_le_mul_of_nonneg_left (h4_le hττ') (abs_nonneg _)).trans hlamτ'
    have hmσ := (mul_le_mul_of_nonneg_left (h4_le hστ') (abs_nonneg _)).trans hlamτ'
    exact dist_ceil_sq_le_of_penalizedConvex (hconv τ hτ hττ₁) (hconv σ hσ hστ₁)
      hτ hσ hττ' hστ' hmτ hmσ hA hE hT hU0 hV0 hU hV ht.1 ht.2
  -- Step 2: Construct a reference minimizing movement family `Jc` at step sizes `τ' / 4 / (j + 1)`
  -- and pass to its uniform limit `u` by completeness.
  set τc : ℕ → ℝ≥0 := fun j ↦ τ' / 4 / ↑(j + 1)
  have hτc : ∀ j, 0 < τc j := fun j ↦ div_pos (div_pos hτ' four_pos) (Nat.cast_pos.2 j.succ_pos)
  have hτcτ' : ∀ j, 4 * τc j ≤ τ' := fun j ↦
    (mul_le_mul_of_nonneg_left
      (div_le_self zero_le (Nat.one_le_cast.2 j.succ_pos)) zero_le).trans_eq
      (mul_div_cancel₀ τ' four_ne_zero)
  have hτc_le : ∀ j, τc j ≤ τ' := fun j ↦ by
    have h4 : (4 : ℝ) * τc j ≤ τ' := by exact_mod_cast hτcτ' j
    exact NNReal.coe_le_coe.1 (by linarith [NNReal.coe_nonneg (τc j)])
  have hτc0 : Tendsto τc atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (τ' / 4))
  have hlamτc : ∀ j, 0 < 1 + lam * (τc j : ℝ) := fun j ↦ by
    have habs : |lam| * (τc j : ℝ) ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (hτc_le j)) (abs_nonneg _)).trans hlamτ'
    nlinarith [neg_abs_le lam, NNReal.coe_nonneg (τc j)]
  choose Jc hJc0 hJc using fun j ↦
    PenalizedConvex.exists_forall_mem_moreauYosidaResolvent
      hφ (hconv (τc j) (hτc j) ((hτc_le j).trans_lt hτ'τ₁)) (hτc j) (hlamτc j)
      ((hτc_le j).trans_lt hτ'τ₀) h₀ x₀
  let Fc : ℕ → ℝ → X := fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊
  have huc : ∀ T ≥ (0 : ℝ), UniformCauchySeqOn Fc atTop (Icc 0 T) := fun T hT ↦ by
    set K : ℝ := cauchyK lam T τ' A E
    have herr : Tendsto (fun p : ℕ × ℕ ↦ Real.sqrt (K * Real.sqrt ((τc p.1 : ℝ) + τc p.2)))
        (atTop ×ˢ atTop) (𝓝 0) := by
      have hsum : Tendsto (fun p : ℕ × ℕ ↦ (τc p.1 : ℝ) + τc p.2) (atTop ×ˢ atTop) (𝓝 0) := by
        simpa using ((NNReal.tendsto_coe.2 hτc0).comp tendsto_fst).add
          ((NNReal.tendsto_coe.2 hτc0).comp tendsto_snd)
      have h0 : Tendsto (fun p : ℕ × ℕ ↦ K * Real.sqrt ((τc p.1 : ℝ) + τc p.2))
          (atTop ×ˢ atTop) (𝓝 0) :=
        (((Real.continuous_sqrt.tendsto 0).comp hsum).const_mul K).trans_eq (by simp)
      exact ((Real.continuous_sqrt.tendsto 0).comp h0).trans_eq (by simp)
    exact uniformCauchySeqOn_of_dist_le herr <| .of_forall fun p t ht ↦ Real.le_sqrt_of_sq_le <|
      hpair hT (hτc p.1) (hτc p.2) (hτcτ' p.1) (hτcτ' p.2) (hJc0 p.1) (hJc0 p.2)
        (hJc p.1) (hJc p.2) t ht
  obtain ⟨u₀, hu₀⟩ := exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn
    (𝔖 := {s | ∃ T ≥ (0 : ℝ), s = Icc 0 T}) (by rintro _ ⟨T, hT, rfl⟩; exact huc T hT)
  classical
  let u : ℝ → X := Function.update u₀ 0 x₀
  have hu0 : u 0 = x₀ := Function.update_self 0 x₀ u₀
  have hu_unif : ∀ T ≥ (0 : ℝ), TendstoUniformlyOn Fc u atTop (Icc 0 T) := fun T hT ↦
    (hu₀ _ ⟨T, hT, rfl⟩).congr_inseparable_right fun t ht ↦ by
      by_cases h0 : t = 0
      · subst h0
        simpa only [u, Function.update_self] using
          tendsto_nhds_unique_inseparable ((hu₀ _ ⟨T, hT, rfl⟩).tendsto_at ht)
            (by simpa only [Fc, zero_div, Nat.ceil_zero, hJc0] using tendsto_const_nhds)
      · simp only [u, Function.update_of_ne h0]; rfl
  have hu_lim : ∀ t ≥ 0, Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 (u t)) := fun t ht ↦
    (hu_unif t ht).tendsto_at ⟨ht, le_rfl⟩
  have hu_evi : IsEVISolution lam φ u :=
    isEVISolution_of_tendsto_ceil hφ hτ₀ hconv h₀ hx₀ hτc
      (fun j ↦ (hτc_le j).trans_lt hτ'τ₁) hτc0 hlamτc hJc0 hJc hu_lim
  -- Step 3: Compare any minimizing movement scheme `(τ, J)` against `(τc, Jc)`.
  refine ⟨u, hu0, hu_evi, fun τ J hτ hτ0 hJ0 hJ T ↦ ?_⟩
  set T' : ℝ := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  suffices h :
      TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T') from
    h.mono (fun t ht ↦ ⟨ht.1, ht.2.trans (le_max_left _ _)⟩)
  set K : ℝ := cauchyK lam T' τ' A E
  have herr0 :
      Tendsto (fun j ↦ Real.sqrt (K * Real.sqrt ((τc j : ℝ) + τ j))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun j ↦ (τc j : ℝ) + τ j) atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_coe.2 hτc0).add (NNReal.tendsto_coe.2 hτ0)
    have h0 : Tendsto (fun j ↦ K * Real.sqrt ((τc j : ℝ) + τ j)) atTop (𝓝 0) :=
      (((Real.continuous_sqrt.tendsto 0).comp hsum).const_mul K).trans_eq (by simp)
    exact ((Real.continuous_sqrt.tendsto 0).comp h0).trans_eq (by simp)
  refine (hu_unif T' hT').congr_dist_le herr0 ?_
  filter_upwards [hτ, hJ0, hJ,
    hτ0.eventually (ge_mem_nhds (by positivity : (0 : ℝ≥0) < τ' / 4))] with j hjτ hj0 hjJ hj4 t ht
  have h4 : 4 * τ j ≤ τ' :=
    (mul_le_mul_of_nonneg_left hj4 (by positivity)).trans_eq (mul_div_cancel₀ _ four_ne_zero)
  exact Real.le_sqrt_of_sq_le
    (hpair hT' (hτc j) hjτ (hτcτ' j) h4 (hJc0 j) hj0 (hJc j) hjJ t ht)

/-- **Characterization of the `EVI_λ` domain** (Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under
the hypotheses of `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, the set
of initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) :
    eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ :=
      exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ hx
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- **Existence of `EVI_λ` flows on the closure of the effective domain**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, every point `x₀` in
`closure {x | φ x ≠ ⊤}` is the initial point of an `EVI_λ` solution. -/
theorem exists_isEVISolution_of_mem_closure_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X}
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (eviDomain_eq_closure_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ ▸ hx₀)

end Existence

section GeodesicallyConvex

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X]
  {lam : ℝ} {φ : X → EReal}

/-- **Existence and uniform convergence of minimizing movements for geodesically convex energies
on CAT(0) spaces** (Jost; Mayer, Theorem 1.13). Let `φ : X → EReal` be lower semicontinuous and
`lam`-geodesically convex on a complete CAT(0) pseudometric space, and let `x₀` be a point of
finite energy (`φ x₀ ≠ ⊤` and `φ x₀ ≠ ⊥`). Then there starts from `x₀` an `EVI_λ` solution `u`
with `u 0 = x₀`, and all minimizing movement interpolants eventually starting at `x₀` converge
uniformly to `u` on compact time intervals `[0, T]` as `τ → 0`. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ᶠ j in atTop, J j 0 = x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, h₀⟩ :=
    hconv.exists_moreauYosida_ne_bot (hφ.lowerSemicontinuousAt x₀) hx₀ hx₀bot x₀
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ one_pos
    (fun _ _ _ ↦ hconv.penalizedConvex) h₀ hx₀

/-- **Characterization of the `EVI_λ` domain for geodesically convex energies on CAT(0) spaces**
(Jost; Mayer, Theorem 1.13). If `φ` is lower semicontinuous, `lam`-geodesically convex, and never
equal to `⊥` on a complete CAT(0) pseudometric space, then the set `TauCeti.eviDomain lam φ` of
initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem GeodesicallyConvex.eviDomain_eq_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) : eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ := hconv.exists_isEVISolution_tendstoUniformlyOn hφ hx (hbot _)
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- **Existence of `EVI_λ` flows on `closure {x | φ x ≠ ⊤}` for geodesically convex energies on
CAT(0) spaces** (Jost; Mayer, Theorem 1.13). If `φ` is lower semicontinuous, `lam`-geodesically
convex, and never equal to `⊥` on a complete CAT(0) pseudometric space, then every point
`x₀ ∈ closure {x | φ x ≠ ⊤}` is the initial point of an `EVI_λ` solution. -/
theorem GeodesicallyConvex.exists_isEVISolution_of_mem_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (hconv.eviDomain_eq_closure hφ hbot ▸ hx₀)

end GeodesicallyConvex

end TauCeti
