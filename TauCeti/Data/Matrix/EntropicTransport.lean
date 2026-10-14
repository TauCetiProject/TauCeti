/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Data.Matrix.Scaling
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# The envelope formula for finite entropic optimal transport

Let `ι` and `κ` be finite types, let `a : ι → ℝ` and `b : κ → ℝ` be strictly positive marginals of
equal total mass, and let `ε > 0` be a temperature. For a real cost matrix `C : Matrix ι κ ℝ`, the
entropically regularised transport problem minimises

`∑ i, ∑ j, C i j * P i j + ε * relEntropy P (vecMulVec a b)`

over the transport polytope of the nonnegative matrices `P` with row sums `a` and column sums `b`,
where the relative entropy is taken against the product `a ⊗ b` of the marginals. For probability
vectors `a` and `b` this is the Kullback–Leibler divergence of the plan from `a ⊗ b`; for other
masses it differs from the finite-measure divergence by a constant independent of `P` and `C`. Its
value
`Matrix.entropicTransportValue C ε a b` is a function of the cost, and this file proves that it is
differentiable, with the optimal plan as its gradient:

`D_C OT_ε(C)[H] = ∑ i, ∑ j, P i j * H i j`,

where `P` is the optimal plan for the cost `C`. This is a genuine derivative and not only a
one-sided one, because the regularised problem has a unique optimal plan.

The regularised objective is `ε` times the relative entropy against the Gibbs kernel
`a i * b j * exp (-C i j / ε)`, so its minimiser is the entropy minimiser of
`TauCeti/Data/Matrix/Scaling.lean`, which exists and has strictly positive entries. The proof of
the derivative is quantitative. At a positive minimiser `P` for the cost `C`, the first-order
condition says that `C + ε log P` integrates to `0` against every matrix with zero row and column
sums. Comparing the conditions at the minimisers `P` and `Q` for two costs `C` and `C'` gives

`ε * ∑ i, ∑ j, (P i j - Q i j) * (log (P i j) - log (Q i j)) = ⟪P - Q, C' - C⟫`.

Since the entries are at most the total mass `m = ∑ i, a i`, strong monotonicity of the logarithm
on `(0, m]` bounds the left side below by `ε / m * ‖P - Q‖ ^ 2`, in the Frobenius norm. So the
optimal plan is an `m / ε`-Lipschitz function of the cost. The value is the minimum of functions
that are affine in the cost, which squeezes its first-order remainder between `0` and
`⟪Q - P, C' - C⟫`, hence `|OT_ε(C') - OT_ε(C) - ⟪P, C' - C⟫| ≤ m / ε * ‖C' - C‖ ^ 2`.

The norm and inner product on matrices are the Frobenius ones of
`open scoped Matrix.Norms.Frobenius`, with `⟪A, B⟫ = ∑ i, ∑ j, A i j * B i j`. Any norm on the
finite-dimensional space of matrices gives the same derivative, and in the Frobenius norm the
Lipschitz constant `m / ε` of the plan does not depend on the sizes of `ι` and `κ`.

## Main definitions

* `Matrix.transportPolytope a b`: the nonnegative matrices with row sums `a` and column sums `b`.
* `Matrix.entropicTransportObjective C ε a b P`: the regularised transport objective of a plan.
* `Matrix.entropicTransportValue C ε a b`: its infimum over the transport polytope.

## Main results

* `Matrix.entropicTransportObjective_eq_mul_relEntropy`: the objective is `ε` times the relative
  entropy against the Gibbs kernel `a i * b j * exp (-C i j / ε)`.
* `Matrix.exists_isMinOn_entropicTransportObjective`: an optimal plan exists whenever the
  transport polytope is nonempty, and `Matrix.pos_of_isMinOn_entropicTransportObjective`: for a
  positive temperature and strictly positive marginals, every optimal plan has strictly positive
  entries.
* `Matrix.norm_sub_le_of_isMinOn_entropicTransportObjective`: the optimal plan is a
  `(∑ i, a i) / ε`-Lipschitz function of the cost, and
  `Matrix.eq_of_isMinOn_entropicTransportObjective`: it is unique.
* `Matrix.abs_entropicTransportValue_sub_sub_inner_le`: the second-order bound on the first-order
  remainder of the value.
* `Matrix.hasGradientAt_entropicTransportValue`: **the envelope formula**, the gradient of the
  value with respect to the cost is the optimal plan.

## References

* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Section 4.1 and Proposition 4.3, for the regularised problem with reference `a ⊗ b`, its Gibbs
  kernel and its unique minimiser, and Section 9.1 for the derivatives of the regularised value
  through Danskin's theorem.
* J. M. Danskin, *The theory of max-min, with applications*, SIAM J. Appl. Math. 14 (1966),
  641--664, for the differentiation of an optimal value through its optimal solution.
-/

public section

noncomputable section

open Filter Topology Real
open scoped Matrix.Norms.Frobenius RealInnerProductSpace

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {a : ι → ℝ} {b : κ → ℝ} {ε : ℝ} {C C' P Q : Matrix ι κ ℝ}

/-! ### The transport polytope and the regularised problem -/

/-- The transport polytope of the marginals `a` and `b`: the nonnegative matrices with row sums
`a` and column sums `b`. The marginals are arbitrary real vectors, as for the diagonal scalings of
`Matrix.HasMarginals`; `TauCeti.RealPlans μ ν` is the same set for probability marginals, with
plans written as functions on `ι × κ`. -/
def transportPolytope (a : ι → ℝ) (b : κ → ℝ) : Set (Matrix ι κ ℝ) :=
  {P | (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b}

@[simp] theorem mem_transportPolytope :
    P ∈ transportPolytope a b ↔ (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b :=
  Iff.rfl

/-- The entropically regularised transport objective of a plan `P` for the cost `C` at temperature
`ε`: the transport cost `∑ i, ∑ j, C i j * P i j` plus `ε` times the relative entropy of `P`
against the product `a ⊗ b` of the marginals. -/
def entropicTransportObjective (C : Matrix ι κ ℝ) (ε : ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (P : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, C i j * P i j + ε * relEntropy P (vecMulVec a b)

theorem entropicTransportObjective_def (C : Matrix ι κ ℝ) (ε : ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (P : Matrix ι κ ℝ) :
    C.entropicTransportObjective ε a b P =
      ∑ i, ∑ j, C i j * P i j + ε * relEntropy P (vecMulVec a b) :=
  (rfl)

/-- The value of the entropically regularised transport problem: the infimum of
`Matrix.entropicTransportObjective C ε a b` over the transport polytope of `a` and `b`. -/
def entropicTransportValue (C : Matrix ι κ ℝ) (ε : ℝ) (a : ι → ℝ) (b : κ → ℝ) : ℝ :=
  sInf (C.entropicTransportObjective ε a b '' transportPolytope a b)

theorem entropicTransportValue_def (C : Matrix ι κ ℝ) (ε : ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    C.entropicTransportValue ε a b =
      sInf (C.entropicTransportObjective ε a b '' transportPolytope a b) :=
  (rfl)

/-- The value is the objective of an optimal plan. -/
theorem entropicTransportValue_eq_of_isMinOn
    (hP : P ∈ transportPolytope a b)
    (hmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P) :
    C.entropicTransportValue ε a b = C.entropicTransportObjective ε a b P :=
  IsLeast.csInf_eq ⟨⟨P, hP, rfl⟩, by
    rintro _ ⟨Q, hQ, rfl⟩
    exact isMinOn_iff.1 hmin Q hQ⟩

/-- The objective is affine in the cost: changing the cost by `H` changes the objective of `P` by
`⟪H, P⟫`. -/
theorem entropicTransportObjective_add (C H : Matrix ι κ ℝ) (ε : ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (P : Matrix ι κ ℝ) :
    (C + H).entropicTransportObjective ε a b P = C.entropicTransportObjective ε a b P + ⟪H, P⟫ := by
  simp only [entropicTransportObjective_def, frobenius_inner_def, add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

/-- **The Gibbs reformulation.** For nonzero marginals and a nonzero temperature, the regularised
objective is `ε` times the relative entropy against the Gibbs kernel
`a i * b j * exp (-C i j / ε)`. -/
theorem entropicTransportObjective_eq_mul_relEntropy (C : Matrix ι κ ℝ) (hε : ε ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (P : Matrix ι κ ℝ) :
    C.entropicTransportObjective ε a b P =
      ε * relEntropy P (of fun i j ↦ a i * b j * exp (-C i j / ε)) := by
  have hlog (i : ι) (j : κ) :
      log (a i * b j * exp (-C i j / ε)) = log (vecMulVec a b i j) - C i j / ε := by
    rw [log_mul (mul_ne_zero (ha i) (hb j)) (exp_ne_zero _), log_exp, vecMulVec_apply]
    ring
  simp only [entropicTransportObjective_def, relEntropy_def, of_apply, hlog, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  field_simp
  ring

/-! ### Optimal plans -/

/-- For a positive temperature, a minimiser of the regularised objective over the transport
polytope minimises the relative entropy against the Gibbs kernel, in the form used by
`TauCeti/Data/Matrix/Scaling.lean`. -/
private theorem relEntropy_le_of_isMinOn (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P) :
    ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P (of fun i j ↦ a i * b j * exp (-C i j / ε)) ≤
        relEntropy Q (of fun i j ↦ a i * b j * exp (-C i j / ε)) := by
  intro Q hQ0 hQ
  have h := isMinOn_iff.1 hmin Q ⟨hQ0, hQ⟩
  simp only [entropicTransportObjective_eq_mul_relEntropy C hε.ne'
    (fun i ↦ (ha i).ne') (fun j ↦ (hb j).ne')] at h
  exact le_of_mul_le_mul_left h hε

/-- The regularised transport problem has an optimal plan for every cost and every temperature, as
soon as the transport polytope is nonempty: the polytope is compact and the objective is
continuous. -/
theorem exists_isMinOn_entropicTransportObjective (C : Matrix ι κ ℝ) (ε : ℝ)
    (h : (transportPolytope a b).Nonempty) :
    ∃ P ∈ transportPolytope a b,
      IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P := by
  have hK := continuous_relEntropy (vecMulVec a b)
  have hcont : Continuous (C.entropicTransportObjective ε a b) := by
    rw [funext (entropicTransportObjective_def C ε a b)]
    fun_prop
  exact (isCompact_setOf_nonneg_hasMarginals a b).exists_isMinOn h hcont.continuousOn

/-- For a positive temperature and strictly positive marginals, every optimal plan of the
regularised transport problem has strictly positive entries. -/
theorem pos_of_isMinOn_entropicTransportObjective (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P) :
    ∀ i j, 0 < P i j :=
  pos_of_relEntropy_minOn _ a b ha hb hP.1 hP.2 (relEntropy_le_of_isMinOn hε ha hb hmin)

/-- The first-order condition at an optimal plan `P`: the function `C + ε log P` integrates to `0`
against every matrix `D` with zero row and column sums. -/
private theorem sum_sum_mul_add_mul_log_eq_zero (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P)
    {D : Matrix ι κ ℝ} (hD : HasMarginals D 0 0) :
    ∑ i, ∑ j, D i j * (C i j + ε * log (P i j)) = 0 := by
  have h := sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn _
    (pos_of_isMinOn_entropicTransportObjective hε ha hb hP hmin) hP.2
    (relEntropy_le_of_isMinOn hε ha hb hmin) hD
  -- The logarithm of the Gibbs kernel splits into a row term, a column term and `-C / ε`, and the
  -- row and column terms integrate to `0` against `D`.
  have hlog (i : ι) (j : κ) : log (P i j) - log (of (fun i j ↦ a i * b j * exp (-C i j / ε)) i j) =
      (C i j + ε * log (P i j)) / ε + (-log (a i) + -log (b j)) := by
    rw [of_apply, log_mul (mul_pos (ha i) (hb j)).ne' (exp_pos _).ne', log_exp,
      log_mul (ha i).ne' (hb j).ne']
    field_simp
    ring
  have hsplit : ∑ i, ∑ j, D i j *
      (log (P i j) - log (of (fun i j ↦ a i * b j * exp (-C i j / ε)) i j)) =
      (∑ i, ∑ j, D i j * (C i j + ε * log (P i j))) / ε +
        ∑ i, ∑ j, D i j * (-log (a i) + -log (b j)) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hlog]
    ring
  rw [hsplit, hD.sum_sum_mul_add] at h
  simpa [hε.ne'] using h

/-- Comparison of the optimal plans `P` and `Q` for the costs `C` and `C'`:
`ε * ∑ i, ∑ j, (P i j - Q i j) * (log (P i j) - log (Q i j)) = ⟪P - Q, C' - C⟫`. -/
private theorem mul_sum_sum_sub_mul_log_sub_log_eq (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P)
    (hQ : Q ∈ transportPolytope a b)
    (hQmin : IsMinOn (C'.entropicTransportObjective ε a b) (transportPolytope a b) Q) :
    ε * ∑ i, ∑ j, (P i j - Q i j) * (log (P i j) - log (Q i j)) = ⟪P - Q, C' - C⟫ := by
  obtain ⟨hPa, hPb⟩ := (hasMarginals_def P a b).1 hP.2
  obtain ⟨hQa, hQb⟩ := (hasMarginals_def Q a b).1 hQ.2
  have hD : HasMarginals (P - Q) 0 0 :=
    (hasMarginals_def _ _ _).2 ⟨fun i ↦ by simp [Finset.sum_sub_distrib, hPa i, hQa i],
      fun j ↦ by simp [Finset.sum_sub_distrib, hPb j, hQb j]⟩
  have hPfoc := sum_sum_mul_add_mul_log_eq_zero hε ha hb hP hPmin hD
  have hQfoc := sum_sum_mul_add_mul_log_eq_zero hε ha hb hQ hQmin hD
  have key : ε * ∑ i, ∑ j, (P i j - Q i j) * (log (P i j) - log (Q i j)) -
      ∑ i, ∑ j, (P - Q) i j * (C' - C) i j =
      ∑ i, ∑ j, (P - Q) i j * (C i j + ε * log (P i j)) -
        ∑ i, ∑ j, (P - Q) i j * (C' i j + ε * log (Q i j)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [sub_apply]
    ring
  rw [frobenius_inner_def]
  linarith

/-- **The optimal plan is a Lipschitz function of the cost.** For a positive temperature and
strictly positive marginals, the optimal plans `P` and `Q` of the regularised problems for the costs
`C` and `C'` satisfy `‖P - Q‖ ≤ (∑ i, a i) / ε * ‖C - C'‖` in the Frobenius norm. -/
theorem norm_sub_le_of_isMinOn_entropicTransportObjective (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P)
    (hQ : Q ∈ transportPolytope a b)
    (hQmin : IsMinOn (C'.entropicTransportObjective ε a b) (transportPolytope a b) Q) :
    ‖P - Q‖ ≤ (∑ i, a i) / ε * ‖C - C'‖ := by
  set m := ∑ i, a i
  have hPpos := pos_of_isMinOn_entropicTransportObjective hε ha hb hP hPmin
  have hQpos := pos_of_isMinOn_entropicTransportObjective hε ha hb hQ hQmin
  -- Every entry of a plan is at most its row sum, hence at most the total mass.
  have hle {R : Matrix ι κ ℝ} (hR : R ∈ transportPolytope a b) (i : ι) (j : κ) : R i j ≤ m :=
    calc R i j ≤ ∑ j', R i j' :=
          Finset.single_le_sum (fun j' _ ↦ hR.1 i j') (Finset.mem_univ j)
      _ = a i := ((hasMarginals_def R a b).1 hR.2).1 i
      _ ≤ m := Finset.single_le_sum (fun i' _ ↦ (ha i').le) (Finset.mem_univ i)
  -- Strong monotonicity of the logarithm on `(0, m]`, summed over the entries.
  have hsq : ‖P - Q‖ ^ 2 ≤ m * ∑ i, ∑ j, (P i j - Q i j) * (log (P i j) - log (Q i j)) := by
    rw [← real_inner_self_eq_norm_sq, frobenius_inner_def, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    simpa [sub_apply, sq] using Real.sq_sub_le_mul_sub_mul_log_sub_log (hPpos i j) (hQpos i j)
      (hle hP i j) (hle hQ i j)
  have hinner : ε * ‖P - Q‖ ^ 2 ≤ m * (‖P - Q‖ * ‖C - C'‖) := by
    calc ε * ‖P - Q‖ ^ 2
        ≤ ε * (m * ∑ i, ∑ j, (P i j - Q i j) * (log (P i j) - log (Q i j))) :=
          mul_le_mul_of_nonneg_left hsq hε.le
      _ = m * ⟪P - Q, C' - C⟫ := by
          rw [mul_left_comm, mul_sum_sum_sub_mul_log_sub_log_eq hε ha hb hP hPmin hQ hQmin]
      _ ≤ m * (‖P - Q‖ * ‖C - C'‖) := by
          rw [norm_sub_rev C C']
          exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _)
            (Finset.sum_nonneg fun i _ ↦ (ha i).le)
  rcases (norm_nonneg (P - Q)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (div_nonneg (Finset.sum_nonneg fun i _ ↦ (ha i).le) hε.le) (norm_nonneg _)
  · rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith

/-- For a positive temperature and strictly positive marginals, the regularised transport problem
has at most one optimal plan. -/
theorem eq_of_isMinOn_entropicTransportObjective (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P)
    (hQ : Q ∈ transportPolytope a b)
    (hQmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) Q) :
    P = Q := by
  have h := norm_sub_le_of_isMinOn_entropicTransportObjective hε ha hb hP hPmin hQ hQmin
  rw [sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-! ### The envelope formula -/

/-- **The second-order bound on the value.** If `P` is the optimal plan for the cost `C`, then for
every cost `C'`,
`|OT_ε(C') - OT_ε(C) - ⟪P, C' - C⟫| ≤ (∑ i, a i) / ε * ‖C' - C‖ ^ 2`. -/
theorem abs_entropicTransportValue_sub_sub_inner_le (C' : Matrix ι κ ℝ) (hε : 0 < ε)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P) :
    |C'.entropicTransportValue ε a b - C.entropicTransportValue ε a b - ⟪P, C' - C⟫| ≤
      (∑ i, a i) / ε * ‖C' - C‖ ^ 2 := by
  obtain ⟨Q, hQ, hQmin⟩ := exists_isMinOn_entropicTransportObjective C' ε ⟨P, hP⟩
  have hlip := norm_sub_le_of_isMinOn_entropicTransportObjective hε ha hb hQ hQmin hP hmin
  rw [entropicTransportValue_eq_of_isMinOn hP hmin, entropicTransportValue_eq_of_isMinOn hQ hQmin]
  -- The value is a minimum of functions that are affine in the cost: testing the problem for `C'`
  -- against `P`, and the problem for `C` against `Q`, squeezes the remainder between
  -- `⟪Q - P, C' - C⟫` and `0`.
  have hC' : C' = C + (C' - C) := by abel
  have hup : C'.entropicTransportObjective ε a b Q ≤
      C.entropicTransportObjective ε a b P + ⟪C' - C, P⟫ := by
    rw [← entropicTransportObjective_add, ← hC']
    exact isMinOn_iff.1 hQmin P hP
  have hlow : C.entropicTransportObjective ε a b P + ⟪C' - C, Q⟫ ≤
      C'.entropicTransportObjective ε a b Q := by
    conv_rhs => rw [hC', entropicTransportObjective_add]
    exact add_le_add_left (isMinOn_iff.1 hmin Q hQ) _
  have hQP : |⟪C' - C, Q - P⟫| ≤ (∑ i, a i) / ε * ‖C' - C‖ ^ 2 := by
    calc |⟪C' - C, Q - P⟫| ≤ ‖C' - C‖ * ‖Q - P‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖C' - C‖ * ((∑ i, a i) / ε * ‖C' - C‖) :=
          mul_le_mul_of_nonneg_left hlip (norm_nonneg _)
      _ = (∑ i, a i) / ε * ‖C' - C‖ ^ 2 := by ring
  rw [inner_sub_right, abs_le] at hQP
  rw [← real_inner_comm P (C' - C), abs_le]
  constructor <;> linarith [hQP.1, hQP.2]

/-- **The envelope formula.** For a positive temperature and strictly positive marginals, the
value of the regularised transport problem is differentiable in the cost, and its gradient at `C`,
for the Frobenius inner product, is the optimal plan `P` for `C`:
`D_C OT_ε(C)[H] = ∑ i, ∑ j, P i j * H i j`. -/
theorem hasGradientAt_entropicTransportValue (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hmin : IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P) :
    HasGradientAt (fun D ↦ D.entropicTransportValue ε a b) P C := by
  rw [hasGradientAt_iff_isLittleO]
  have hsq : (fun C' : Matrix ι κ ℝ ↦ ‖C' - C‖ ^ 2) =o[𝓝 C] fun C' ↦ C' - C :=
    (Asymptotics.isLittleO_norm_pow_id one_lt_two).comp_tendsto
      (tendsto_sub_nhds_zero_iff.2 tendsto_id)
  refine (Asymptotics.IsBigO.of_bound ((∑ i, a i) / ε)
    (Eventually.of_forall fun C' ↦ ?_)).trans_isLittleO hsq
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  exact abs_entropicTransportValue_sub_sub_inner_le C' hε ha hb hP hmin

end Matrix
