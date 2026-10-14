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
# Duality and the envelope formulas for finite entropic optimal transport

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

The value is also differentiable in the marginals, with the dual potentials as its gradient. Any
potentials `f : ι → ℝ` and `g : κ → ℝ` bound the objective of every plan below (weak duality),

`∑ i, a i * f i + ∑ j, b j * g j + ε * (∑ i, a i - ∑ i, ∑ j, a i * b j * E i j) ≤ OT_ε(a, b)`,
where `E i j = exp ((f i + g j - C i j) / ε)`,

by the supporting line of `u ↦ u * log u` at the Gibbs density `a i * b j * E i j`. A plan of the
Gibbs form `P i j = a i * b j * E i j` with marginals `a` and `b` makes this an equality, so it is
optimal and `OT_ε(a, b) = ∑ i, a i * f i + ∑ j, b j * g j` (strong duality). Conversely the optimal
plan is a diagonal scaling of the Gibbs kernel, so it has this form: the potentials `f` and `g`,
the Schrödinger potentials of the problem, exist for strictly positive marginals and are the
logarithms of the scaling factors, times `ε`.

The potentials of `P` at `(a, b)` then give the expansion of the value at nearby marginals
`(a', b')` of equal total mass. Weak duality at `(a', b')` with the same potentials bounds the
value below by its first-order approximation, up to the bilinear remainder
`-ε * ∑ i, ∑ j, (a' i - a i) * (b' j - b j) * E i j`. Above, a matrix `D` with marginals
`a' - a` and `b' - b` moves `P` to a plan of `(a', b')`, whose objective exceeds the first-order
approximation by at most `ε * ∑ i, ∑ j, D i j ^ 2 / P i j`, from the quadratic upper bound on
`u ↦ u * log u` at `P i j`. Since `P` is strictly positive, both remainders are
`O(‖(a', b') - (a, b)‖ ^ 2)`, and on the perturbations `(h, k)` of fixed total masses

`D_{a,b} OT_ε[(h, k)] = ∑ i, f i * h i + ∑ j, g j * k j`.

The reference measure `a ⊗ b` moves with the marginals, so along a change of total mass the
derivative acquires the term `-ε * ∑ j, k j`.

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
* `Matrix.le_entropicTransportObjective` and `Matrix.le_entropicTransportValue`: weak duality.
* `Matrix.isMinOn_entropicTransportObjective_iff`: a plan is optimal exactly when it has the Gibbs
  form `a i * b j * exp ((f i + g j - C i j) / ε)`, and
  `Matrix.entropicTransportValue_eq_of_eq_mul_exp`: strong duality for its potentials.
* `Matrix.isBigO_entropicTransportValue_sub_sub`: the quadratic remainder of the first-order
  expansion of the value in the marginals.
* `Matrix.hasFDerivWithinAt_entropicTransportValue_marginals` and
  `Matrix.hasFDerivWithinAt_entropicTransportValue_marginals_fixedMass`: **the envelope formula in
  the marginals**, along marginals of equal total mass and along fixed total masses.

## References

* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Section 4.1 and Proposition 4.3, for the regularised problem with reference `a ⊗ b`, its Gibbs
  kernel and its unique minimiser, Chapter 4 for its dual problem and the scaling form of its
  potentials, and Section 9.1 for the derivatives of the regularised value through Danskin's
  theorem.
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

/-- Every entry of a plan in the transport polytope is at most its row sum and its column sum. -/
private theorem apply_le_of_mem_transportPolytope (hP : P ∈ transportPolytope a b) (i : ι)
    (j : κ) : P i j ≤ a i ∧ P i j ≤ b j := by
  obtain ⟨hPa, hPb⟩ := (hasMarginals_def P a b).1 hP.2
  exact ⟨hPa i ▸ Finset.single_le_sum (fun j' _ ↦ hP.1 i j') (Finset.mem_univ j),
    hPb j ▸ Finset.single_le_sum (fun i' _ ↦ hP.1 i' j) (Finset.mem_univ i)⟩

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

/-! ### Entropic duality -/

/-- The value is at most the objective of every plan in the transport polytope. -/
theorem entropicTransportValue_le_entropicTransportObjective (hQ : Q ∈ transportPolytope a b) :
    C.entropicTransportValue ε a b ≤ C.entropicTransportObjective ε a b Q := by
  obtain ⟨P, hP, hmin⟩ := exists_isMinOn_entropicTransportObjective C ε ⟨Q, hQ⟩
  rw [entropicTransportValue_eq_of_isMinOn hP hmin]
  exact isMinOn_iff.1 hmin Q hQ

/-- **Weak duality** for the regularised problem. For a positive temperature, any potentials `f`
and `g` give the lower bound
`∑ i, a i * f i + ∑ j, b j * g j + ε * (∑ i, a i - ∑ i, ∑ j, a i * b j * E i j)`, where
`E i j = exp ((f i + g j - C i j) / ε)`, on the objective of every plan with marginals `a` and
`b`. -/
theorem le_entropicTransportObjective (hε : 0 < ε) (hQ : Q ∈ transportPolytope a b)
    (f : ι → ℝ) (g : κ → ℝ) :
    ∑ i, a i * f i + ∑ j, b j * g j +
        ε * (∑ i, a i - ∑ i, ∑ j, a i * b j * exp ((f i + g j - C i j) / ε)) ≤
      C.entropicTransportObjective ε a b Q := by
  have hrow (i : ι) (j : κ) : Q i j ≤ a i := (apply_le_of_mem_transportPolytope hQ i j).1
  have hcol (i : ι) (j : κ) : Q i j ≤ b j := (apply_le_of_mem_transportPolytope hQ i j).2
  obtain ⟨hQ0, hQm⟩ := hQ
  obtain ⟨hQa, hQb⟩ := (hasMarginals_def Q a b).1 hQm
  -- Cell by cell, this is the supporting line of `u ↦ u * log u` at the Gibbs density
  -- `a i * b j * exp ((f i + g j - C i j) / ε)`, evaluated at `Q i j`.
  have hcell (i : ι) (j : κ) :
      Q i j * (f i + g j) + ε * (Q i j - a i * b j * exp ((f i + g j - C i j) / ε)) ≤
        C i j * Q i j + ε * (Q i j * log (Q i j) - Q i j * log (vecMulVec a b i j)) := by
    set t := (f i + g j - C i j) / ε
    have ht : ε * t = f i + g j - C i j := mul_div_cancel₀ _ hε.ne'
    rcases (hQ0 i j).eq_or_lt with h0 | hpos
    · have hR : 0 ≤ a i * b j * exp t := mul_nonneg
        (mul_nonneg ((hQ0 i j).trans (hrow i j)) ((hQ0 i j).trans (hcol i j))) (exp_pos t).le
      rw [← h0]
      simp only [zero_mul, mul_zero, zero_sub, zero_add, sub_self]
      nlinarith
    · have hab : 0 < a i * b j := mul_pos (hpos.trans_le (hrow i j)) (hpos.trans_le (hcol i j))
      have h := mul_log_sub_mul_log_ge _ _ (mul_pos hab (exp_pos t)) hpos.le
      rw [log_mul hab.ne' (exp_pos t).ne', log_exp] at h
      rw [vecMulVec_apply]
      nlinarith [mul_le_mul_of_nonneg_left h hε.le]
  have hmass : ∑ i, ∑ j, Q i j = ∑ i, a i := Finset.sum_congr rfl fun i _ ↦ hQa i
  calc ∑ i, a i * f i + ∑ j, b j * g j +
        ε * (∑ i, a i - ∑ i, ∑ j, a i * b j * exp ((f i + g j - C i j) / ε))
      = ∑ i, ∑ j, (Q i j * (f i + g j) +
          ε * (Q i j - a i * b j * exp ((f i + g j - C i j) / ε))) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
          hQm.sum_sum_mul_add, hmass]
    _ ≤ ∑ i, ∑ j, (C i j * Q i j +
          ε * (Q i j * log (Q i j) - Q i j * log (vecMulVec a b i j))) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hcell i j
    _ = C.entropicTransportObjective ε a b Q := by
        simp only [entropicTransportObjective_def, relEntropy_def, Finset.mul_sum,
          Finset.sum_add_distrib]

/-- **Weak duality** for the value of the regularised problem: for a positive temperature and
a nonempty transport polytope, every pair of potentials gives a lower bound on the value. -/
theorem le_entropicTransportValue (hε : 0 < ε) (h : (transportPolytope a b).Nonempty)
    (f : ι → ℝ) (g : κ → ℝ) :
    ∑ i, a i * f i + ∑ j, b j * g j +
        ε * (∑ i, a i - ∑ i, ∑ j, a i * b j * exp ((f i + g j - C i j) / ε)) ≤
      C.entropicTransportValue ε a b :=
  le_csInf (h.image _) (by
    rintro _ ⟨Q, hQ, rfl⟩
    exact le_entropicTransportObjective hε hQ f g)

/-- The objective of a plan of the Gibbs form `a i * b j * exp ((f i + g j - C i j) / ε)` is
`∑ i, a i * f i + ∑ j, b j * g j`. -/
private theorem entropicTransportObjective_eq_of_eq_mul_exp {f : ι → ℝ} {g : κ → ℝ}
    (hε : ε ≠ 0) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) :
    C.entropicTransportObjective ε a b P = ∑ i, a i * f i + ∑ j, b j * g j := by
  have hcell (i : ι) (j : κ) :
      C i j * P i j + ε * (P i j * log (P i j) - P i j * log (vecMulVec a b i j)) =
        P i j * (f i + g j) := by
    by_cases h0 : P i j = 0
    · simp [h0]
    have hab : a i * b j ≠ 0 := fun h ↦ h0 (by rw [hPfg, h, zero_mul])
    have hlog : log (P i j) = log (vecMulVec a b i j) + (f i + g j - C i j) / ε := by
      rw [hPfg, log_mul hab (exp_pos _).ne', log_exp, vecMulVec_apply]
    rw [hlog]
    field_simp
    ring
  rw [← hP.2.sum_sum_mul_add, entropicTransportObjective_def, relEntropy_def, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, hcell]

/-- A plan of the Gibbs form `P i j = a i * b j * exp ((f i + g j - C i j) / ε)` is optimal: the
potentials `f` and `g` certify it, since weak duality is an equality for them. -/
theorem isMinOn_entropicTransportObjective_of_eq_mul_exp {f : ι → ℝ} {g : κ → ℝ}
    (hε : 0 < ε) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) :
    IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P := by
  have hmass : ∑ i, ∑ j, a i * b j * exp ((f i + g j - C i j) / ε) = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ by
      simp_rw [← hPfg]
      exact ((hasMarginals_def P a b).1 hP.2).1 i
  refine isMinOn_iff.2 fun Q hQ ↦ ?_
  have h := le_entropicTransportObjective (C := C) hε hQ f g
  rwa [hmass, sub_self, mul_zero, add_zero,
    ← entropicTransportObjective_eq_of_eq_mul_exp hε.ne' hP hPfg] at h

/-- **Strong duality** at a plan of Gibbs form: if
`P i j = a i * b j * exp ((f i + g j - C i j) / ε)` lies in the transport polytope, the value of
the regularised problem is `∑ i, a i * f i + ∑ j, b j * g j`, the dual value of the potentials
`f` and `g`. -/
theorem entropicTransportValue_eq_of_eq_mul_exp {f : ι → ℝ} {g : κ → ℝ} (hε : 0 < ε)
    (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) :
    C.entropicTransportValue ε a b = ∑ i, a i * f i + ∑ j, b j * g j :=
  (entropicTransportValue_eq_of_isMinOn hP
    (isMinOn_entropicTransportObjective_of_eq_mul_exp hε hP hPfg)).trans
    (entropicTransportObjective_eq_of_eq_mul_exp hε.ne' hP hPfg)

/-- **The Schrödinger potentials.** For a positive temperature and strictly positive marginals, a
plan in the transport polytope is optimal for the regularised problem exactly when it has the
Gibbs form `P i j = a i * b j * exp ((f i + g j - C i j) / ε)` for some potentials `f` and `g`. -/
theorem isMinOn_entropicTransportObjective_iff (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b) :
    IsMinOn (C.entropicTransportObjective ε a b) (transportPolytope a b) P ↔
      ∃ (f : ι → ℝ) (g : κ → ℝ), ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε) := by
  refine ⟨fun hmin ↦ ?_, fun ⟨f, g, hPfg⟩ ↦
    isMinOn_entropicTransportObjective_of_eq_mul_exp hε hP hPfg⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_isDiagonalScaling_of_relEntropy_minOn
    (fun i j ↦ mul_pos (mul_pos (ha i) (hb j)) (exp_pos _)) ha hb hP.1 hP.2
    (relEntropy_le_of_isMinOn hε ha hb hmin)
  refine ⟨fun i ↦ ε * log (u i), fun j ↦ ε * log (v j), fun i j ↦ ?_⟩
  have hexp : (ε * log (u i) + ε * log (v j) - C i j) / ε = log (u i) + log (v j) + -C i j / ε := by
    field_simp
    ring
  rw [(isDiagonalScaling_def _ _ _ _).1 huv i j]
  beta_reduce
  rw [hexp, exp_add, exp_add, exp_log (hu i), exp_log (hv j)]
  ring

/-! ### The derivative of the value in the marginals -/

/-- On the transport polytope, the regularised objective is
`∑ i, ∑ j, (C i j * Q i j + ε * (Q i j * log (Q i j)))` minus `ε` times the sum of the two
marginal terms `∑ i, a i * log (a i)` and `∑ j, b j * log (b j)`. -/
private theorem entropicTransportObjective_eq_sum_sub (hQ : Q ∈ transportPolytope a b) :
    C.entropicTransportObjective ε a b Q =
      ∑ i, ∑ j, (C i j * Q i j + ε * (Q i j * log (Q i j))) -
        ε * (∑ i, a i * log (a i) + ∑ j, b j * log (b j)) := by
  -- The logarithm of `a i * b j` splits on every cell that carries mass.
  have hcell (i : ι) (j : κ) :
      Q i j * log (vecMulVec a b i j) = Q i j * (log (a i) + log (b j)) := by
    rcases (hQ.1 i j).eq_or_lt with h0 | hpos
    · simp [← h0]
    have hai := hpos.trans_le (apply_le_of_mem_transportPolytope hQ i j).1
    have hbj := hpos.trans_le (apply_le_of_mem_transportPolytope hQ i j).2
    rw [vecMulVec_apply, log_mul hai.ne' hbj.ne']
  have hlog := hQ.2.sum_sum_mul_add (fun i ↦ log (a i)) fun j ↦ log (b j)
  rw [entropicTransportObjective_def, relEntropy_def]
  simp only [hcell]
  simp only [Finset.sum_sub_distrib]
  rw [hlog]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The upper half of the expansion of the value in the marginals: moving the optimal plan `P` of
Gibbs form by a matrix `D` with marginals `a' - a` and `b' - b` that keeps it nonnegative, the
value at `a'` and `b'` exceeds its first-order approximation at `a` and `b` by at most
`ε * ∑ i, ∑ j, D i j ^ 2 / P i j`. -/
private theorem entropicTransportValue_sub_sub_le {f : ι → ℝ} {g : κ → ℝ} (hε : 0 < ε)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) {a' : ι → ℝ} {b' : κ → ℝ}
    {D : Matrix ι κ ℝ} (hD : HasMarginals D (a' - a) (b' - b)) (hPD : ∀ i j, 0 ≤ P i j + D i j) :
    C.entropicTransportValue ε a' b' - C.entropicTransportValue ε a b -
        (∑ i, f i * (a' i - a i) + ∑ j, (g j - ε) * (b' j - b j)) ≤
      ε * ∑ i, ∑ j, D i j ^ 2 / P i j := by
  have hPpos (i : ι) (j : κ) : 0 < P i j := by
    rw [hPfg]
    exact mul_pos (mul_pos (ha i) (hb j)) (exp_pos _)
  have hQ : P + D ∈ transportPolytope a' b' := by
    refine ⟨fun i j ↦ hPD i j, ?_⟩
    simpa using hP.2.add hD
  obtain ⟨hQa, hQb⟩ := (hasMarginals_def _ a' b').1 hQ.2
  have ha' (i : ι) : 0 ≤ a' i := hQa i ▸ Finset.sum_nonneg fun j _ ↦ hQ.1 i j
  have hb' (j : κ) : 0 ≤ b' j := hQb j ▸ Finset.sum_nonneg fun i _ ↦ hQ.1 i j
  rw [entropicTransportValue_eq_of_isMinOn hP
    (isMinOn_entropicTransportObjective_of_eq_mul_exp hε hP hPfg)]
  refine (sub_le_sub_right (sub_le_sub_right
    (entropicTransportValue_le_entropicTransportObjective hQ) _) _).trans ?_
  rw [entropicTransportObjective_eq_sum_sub hQ, entropicTransportObjective_eq_sum_sub hP]
  -- The objective of `P + D`, cell by cell, by the quadratic bound on `u ↦ u * log u` at `P i j`.
  have hcell (i : ι) (j : κ) :
      C i j * (P + D) i j + ε * ((P + D) i j * log ((P + D) i j)) ≤
        C i j * P i j + ε * (P i j * log (P i j)) +
          D i j * (C i j + ε * log (P i j) + ε) + ε * (D i j ^ 2 / P i j) := by
    have h := TauCeti.mul_log_sub_mul_log_sub_le_sq_div (hPpos i j) (hPD i j)
    simp only [add_apply, add_sub_cancel_left] at h ⊢
    nlinarith [mul_le_mul_of_nonneg_left h hε.le]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hcell i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- The marginal terms, by the supporting line of `u ↦ u * log u` at `a i` and at `b j`.
  have hrow : ∑ i, (a i * log (a i) + (a' i - a i) * (log (a i) + 1)) ≤
      ∑ i, a' i * log (a' i) :=
    Finset.sum_le_sum fun i _ ↦ by linarith [mul_log_sub_mul_log_ge _ _ (ha i) (ha' i)]
  have hcol : ∑ j, (b j * log (b j) + (b' j - b j) * (log (b j) + 1)) ≤
      ∑ j, b' j * log (b' j) :=
    Finset.sum_le_sum fun j _ ↦ by linarith [mul_log_sub_mul_log_ge _ _ (hb j) (hb' j)]
  simp only [Finset.sum_add_distrib] at hrow hcol
  -- The first-order term: `C + ε * log P` is a row term plus a column term on the support.
  have hlin : ∑ i, ∑ j, D i j * (C i j + ε * log (P i j) + ε) =
      ∑ i, (a' i - a i) * (f i + ε * log (a i) + ε) +
        ∑ j, (b' j - b j) * (g j + ε * log (b j)) := by
    have hlog (i : ι) (j : κ) : C i j + ε * log (P i j) + ε =
        (f i + ε * log (a i) + ε) + (g j + ε * log (b j)) := by
      rw [hPfg, log_mul (mul_pos (ha i) (hb j)).ne' (exp_pos _).ne', log_exp,
        log_mul (ha i).ne' (hb j).ne']
      field_simp
      ring
    simp only [hlog]
    simpa using hD.sum_sum_mul_add (fun i ↦ f i + ε * log (a i) + ε) fun j ↦ g j + ε * log (b j)
  have hrow' : ∑ i, (a' i - a i) * (f i + ε * log (a i) + ε) -
      ε * ∑ i, (a' i - a i) * (log (a i) + 1) = ∑ i, f i * (a' i - a i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hcol' : ∑ j, (b' j - b j) * (g j + ε * log (b j)) -
      ε * ∑ j, (b' j - b j) * (log (b j) + 1) = ∑ j, (g j - ε) * (b' j - b j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [mul_le_mul_of_nonneg_left hrow hε.le, mul_le_mul_of_nonneg_left hcol hε.le]

/-- The lower half of the expansion of the value in the marginals, by weak duality with the
potentials `f` and `g` of the optimal plan at `a` and `b`. -/
private theorem le_entropicTransportValue_sub_sub {f : ι → ℝ} {g : κ → ℝ} (hε : 0 < ε)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) {a' : ι → ℝ} {b' : κ → ℝ}
    (h' : (transportPolytope a' b').Nonempty) :
    -(ε * ∑ i, ∑ j, (a' i - a i) * (b' j - b j) * exp ((f i + g j - C i j) / ε)) ≤
      C.entropicTransportValue ε a' b' - C.entropicTransportValue ε a b -
        (∑ i, f i * (a' i - a i) + ∑ j, (g j - ε) * (b' j - b j)) := by
  obtain ⟨hPa, hPb⟩ := (hasMarginals_def P a b).1 hP.2
  set E : ι → κ → ℝ := fun i j ↦ exp ((f i + g j - C i j) / ε)
  -- The rows and columns of the Gibbs density, weighted by the other marginal, have sum `1`.
  have hrow (i : ι) : ∑ j, b j * E i j = 1 := by
    have h := hPa i
    simp only [hPfg, mul_assoc, ← Finset.mul_sum] at h
    exact (mul_eq_left₀ (ha i).ne').1 h
  have hcol (j : κ) : ∑ i, a i * E i j = 1 := by
    have h := hPb j
    simp only [hPfg, mul_comm (a _) (b j), mul_assoc, ← Finset.mul_sum] at h
    exact (mul_eq_left₀ (hb j).ne').1 h
  have hmass : ∑ i, ∑ j, a i * b j * E i j = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ by simp only [E, ← hPfg]; exact hPa i
  have hsplit : ∑ i, ∑ j, a' i * b' j * E i j = ∑ i, a i + ∑ i, (a' i - a i) +
      ∑ j, (b' j - b j) + ∑ i, ∑ j, (a' i - a i) * (b' j - b j) * E i j := by
    have hcell (i : ι) (j : κ) : a' i * b' j * E i j = a i * b j * E i j +
        (a' i - a i) * (b j * E i j) + (b' j - b j) * (a i * E i j) +
        (a' i - a i) * (b' j - b j) * E i j := by ring
    simp only [hcell, Finset.sum_add_distrib, hmass, ← Finset.mul_sum, hrow, mul_one]
    rw [Finset.sum_comm (f := fun i j ↦ (b' j - b j) * (a i * E i j))]
    simp only [← Finset.mul_sum, hcol, mul_one]
  have hw := le_entropicTransportValue (C := C) hε h' f g
  rw [entropicTransportValue_eq_of_eq_mul_exp hε hP hPfg]
  simp only [E] at hsplit
  rw [hsplit] at hw
  have e1 : ∑ i, a' i * f i = ∑ i, a i * f i + ∑ i, f i * (a' i - a i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ j, b' j * g j = ∑ j, b j * g j + ∑ j, (g j - ε) * (b' j - b j) +
      ε * ∑ j, (b' j - b j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have e3 : ∑ i, a' i = ∑ i, a i + ∑ i, (a' i - a i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e1, e2, e3] at hw
  linarith

/-- The quantitative expansion of the value in the marginals: for marginals `(a', b')` of equal
total mass, within a third of the smallest entry of the optimal plan `P` of Gibbs form from
`(a, b)` in the sup norm, the first-order remainder is at most
`ε * ∑ i, ∑ j, (exp ((f i + g j - C i j) / ε) + 9 / P i j)` times the squared distance. -/
private theorem abs_entropicTransportValue_sub_sub_le {f : ι → ℝ} {g : κ → ℝ} (hε : 0 < ε)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε))
    {p : (ι → ℝ) × (κ → ℝ)} (hpS : ∑ i, p.1 i = ∑ j, p.2 j)
    (hpP : ∀ i j, 3 * ‖p - (a, b)‖ ≤ P i j) :
    |C.entropicTransportValue ε p.1 p.2 - C.entropicTransportValue ε a b -
        (∑ i, f i * (p.1 i - a i) + ∑ j, (g j - ε) * (p.2 j - b j))| ≤
      ε * (∑ i, ∑ j, (exp ((f i + g j - C i j) / ε) + 9 / P i j)) * ‖p - (a, b)‖ ^ 2 := by
  obtain ⟨hPa, hPb⟩ := (hasMarginals_def P a b).1 hP.2
  have hPpos (i : ι) (j : κ) : 0 < P i j := by
    rw [hPfg]
    exact mul_pos (mul_pos (ha i) (hb j)) (exp_pos _)
  set δ := ‖p - (a, b)‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hh (i : ι) : |p.1 i - a i| ≤ δ :=
    (norm_le_pi_norm (p - (a, b)).1 i).trans (norm_fst_le (p - (a, b)))
  have hk (j : κ) : |p.2 j - b j| ≤ δ :=
    (norm_le_pi_norm (p - (a, b)).2 j).trans (norm_snd_le (p - (a, b)))
  -- Both index types are empty, or both are nonempty.
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have : IsEmpty ι := ⟨fun i ↦ (ha i).ne' (by simp [← hPa i])⟩
    have hp : p = (a, b) := Subsingleton.elim _ _
    simp [hp]
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨j⟩ := hκ
    exact (hb j).ne' (by simp [← hPb j])
  -- Follow the perturbation of the marginals by a perturbation `D` of `P`.
  obtain ⟨D, hD, hDle⟩ := exists_hasMarginals_abs_le (h := p.1 - a) (k := p.2 - b)
    (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, hpS, hP.2.sum_eq]) hh hk
  have hPD (i : ι) (j : κ) : 0 ≤ P i j + D i j := by
    linarith [neg_abs_le (D i j), hDle i j, hpP i j]
  have hup := entropicTransportValue_sub_sub_le hε ha hb hP hPfg hD hPD
  have hlow := le_entropicTransportValue_sub_sub (C := C) hε ha hb hP hPfg
    ⟨P + D, hPD, by simpa using hP.2.add hD⟩
  -- Both remainders are bounded cell by cell.
  have hcellE (i : ι) (j : κ) : (p.1 i - a i) * (p.2 j - b j) * exp ((f i + g j - C i j) / ε) ≤
      (exp ((f i + g j - C i j) / ε) + 9 / P i j) * δ ^ 2 := by
    have hE := exp_pos ((f i + g j - C i j) / ε)
    have hhk : (p.1 i - a i) * (p.2 j - b j) ≤ δ ^ 2 := by
      calc (p.1 i - a i) * (p.2 j - b j) ≤ |(p.1 i - a i) * (p.2 j - b j)| := le_abs_self _
        _ = |p.1 i - a i| * |p.2 j - b j| := abs_mul _ _
        _ ≤ δ * δ := mul_le_mul (hh i) (hk j) (abs_nonneg _) hδ
        _ = δ ^ 2 := (sq δ).symm
    have h9 : 0 ≤ 9 / P i j * δ ^ 2 := by have := hPpos i j; positivity
    nlinarith [mul_le_mul_of_nonneg_right hhk hE.le]
  have hcellD (i : ι) (j : κ) : D i j ^ 2 / P i j ≤
      (exp ((f i + g j - C i j) / ε) + 9 / P i j) * δ ^ 2 := by
    have hD2 : D i j ^ 2 ≤ 9 * δ ^ 2 := by
      nlinarith [sq_abs (D i j), abs_nonneg (D i j), hDle i j]
    have hE := exp_pos ((f i + g j - C i j) / ε)
    calc D i j ^ 2 / P i j ≤ 9 * δ ^ 2 / P i j := by gcongr; exact (hPpos i j).le
      _ = 9 / P i j * δ ^ 2 := by ring
      _ ≤ (exp ((f i + g j - C i j) / ε) + 9 / P i j) * δ ^ 2 := by
        nlinarith [mul_nonneg hE.le (sq_nonneg δ)]
  have hK : ε * (∑ i, ∑ j, (exp ((f i + g j - C i j) / ε) + 9 / P i j)) * δ ^ 2 =
      ε * ∑ i, ∑ j, (exp ((f i + g j - C i j) / ε) + 9 / P i j) * δ ^ 2 := by
    simp only [mul_assoc, Finset.sum_mul]
  have hE' := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hcellE i j) hε.le
  have hD' := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hcellD i j) hε.le
  rw [abs_le]
  constructor <;> linarith

/-- **The quadratic expansion of the value in the marginals.** Let `P` be a plan of Gibbs form
`P i j = a i * b j * exp ((f i + g j - C i j) / ε)` for strictly positive marginals `a` and `b`
and a positive temperature, so that `P` is optimal and `f`, `g` are its Schrödinger potentials.
Along pairs of marginals `(a', b')` of equal total mass, the value at `(a', b')` differs from its
first-order approximation
`OT_ε(a, b) + ∑ i, f i * (a' i - a i) + ∑ j, (g j - ε) * (b' j - b j)` by
`O(‖(a', b') - (a, b)‖ ^ 2)`. -/
theorem isBigO_entropicTransportValue_sub_sub {f : ι → ℝ} {g : κ → ℝ} (hε : 0 < ε)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) :
    (fun p : (ι → ℝ) × (κ → ℝ) ↦ C.entropicTransportValue ε p.1 p.2 -
        C.entropicTransportValue ε a b -
          (∑ i, f i * (p.1 i - a i) + ∑ j, (g j - ε) * (p.2 j - b j))) =O[
        𝓝[{p | ∑ i, p.1 i = ∑ j, p.2 j}] (a, b)] fun p ↦ ‖p - (a, b)‖ ^ 2 := by
  have hPpos (i : ι) (j : κ) : 0 < P i j := by
    rw [hPfg]
    exact mul_pos (mul_pos (ha i) (hb j)) (exp_pos _)
  -- Near `(a, b)`, every entry of `P` exceeds three times the size of the perturbation.
  have hev : ∀ᶠ p in 𝓝[{p | ∑ i, p.1 i = ∑ j, p.2 j}] (a, b),
      (∑ i, p.1 i = ∑ j, p.2 j) ∧ ∀ i j, 3 * ‖p - (a, b)‖ ≤ P i j := by
    refine eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds ?_)
    refine eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ ?_
    filter_upwards [tendsto_norm_sub_self (a, b) |>.eventually
      (gt_mem_nhds (div_pos (hPpos i j) three_pos))] with p hp
    linarith
  refine Asymptotics.IsBigO.of_bound
    (ε * ∑ i, ∑ j, (exp ((f i + g j - C i j) / ε) + 9 / P i j)) ?_
  filter_upwards [hev] with p ⟨hpS, hpP⟩
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  exact abs_entropicTransportValue_sub_sub_le hε ha hb hP hPfg hpS hpP

/-- **The envelope formula in the marginals.** Let `P` be a plan of Gibbs form
`P i j = a i * b j * exp ((f i + g j - C i j) / ε)` for strictly positive marginals `a` and `b`
and a positive temperature, so that `P` is optimal and `f`, `g` are its Schrödinger potentials.
Within the pairs of marginals of equal total mass, the value is differentiable at `(a, b)` with
derivative `(h, k) ↦ ∑ i, f i * h i + ∑ j, (g j - ε) * k j`.

The term `-ε * ∑ j, k j` comes from the reference measure `a ⊗ b`, which moves with the
marginals; it vanishes on the perturbations that keep both total masses fixed, where
`Matrix.hasFDerivWithinAt_entropicTransportValue_marginals_fixedMass` gives the derivative
`(h, k) ↦ ∑ i, f i * h i + ∑ j, g j * k j`. Replacing `f` and `g` by `f + c` and `g - c` keeps
the Gibbs form and changes the derivative only off the equal-mass directions. -/
theorem hasFDerivWithinAt_entropicTransportValue_marginals {f : ι → ℝ} {g : κ → ℝ} (hε : 0 < ε)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) :
    HasFDerivWithinAt (fun p : (ι → ℝ) × (κ → ℝ) ↦ C.entropicTransportValue ε p.1 p.2)
      ((∑ i, f i • ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ)) +
        (∑ j, (g j - ε) • ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))
      {p | ∑ i, p.1 i = ∑ j, p.2 j} (a, b) := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  have hsq : (fun p : (ι → ℝ) × (κ → ℝ) ↦ ‖p - (a, b)‖ ^ 2) =o[
      𝓝[{p | ∑ i, p.1 i = ∑ j, p.2 j}] (a, b)] fun p ↦ p - (a, b) :=
    ((Asymptotics.isLittleO_norm_pow_id one_lt_two).comp_tendsto
      (tendsto_sub_nhds_zero_iff.2 tendsto_id)).mono nhdsWithin_le_nhds
  refine ((isBigO_entropicTransportValue_sub_sub hε ha hb hP hPfg).trans_isLittleO hsq).congr_left
    fun p ↦ ?_
  simp [smul_eq_mul]

/-- **The envelope formula along fixed total masses.** Let `P` be a plan of Gibbs form
`P i j = a i * b j * exp ((f i + g j - C i j) / ε)` for strictly positive marginals `a` and `b`
and a positive temperature. Within the pairs of marginals with the total masses of `a` and `b`,
the value is differentiable at `(a, b)` with derivative
`(h, k) ↦ ∑ i, f i * h i + ∑ j, g j * k j`: the gradient of the value in the marginals is the pair
of Schrödinger potentials. -/
theorem hasFDerivWithinAt_entropicTransportValue_marginals_fixedMass {f : ι → ℝ} {g : κ → ℝ}
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hP : P ∈ transportPolytope a b)
    (hPfg : ∀ i j, P i j = a i * b j * exp ((f i + g j - C i j) / ε)) :
    HasFDerivWithinAt (fun p : (ι → ℝ) × (κ → ℝ) ↦ C.entropicTransportValue ε p.1 p.2)
      ((∑ i, f i • ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ)) +
        (∑ j, g j • ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))
      {p | ∑ i, p.1 i = ∑ i, a i ∧ ∑ j, p.2 j = ∑ j, b j} (a, b) := by
  have hTS : {p : (ι → ℝ) × (κ → ℝ) | ∑ i, p.1 i = ∑ i, a i ∧ ∑ j, p.2 j = ∑ j, b j} ⊆
      {p | ∑ i, p.1 i = ∑ j, p.2 j} := fun p hp ↦ by
    rw [Set.mem_ofPred_eq] at hp ⊢
    rw [hp.1, hp.2, hP.2.sum_eq]
  have H := (hasFDerivWithinAt_entropicTransportValue_marginals hε ha hb hP hPfg).mono hTS
  rw [hasFDerivWithinAt_iff_isLittleO] at H ⊢
  refine H.congr' (eventually_mem_nhdsWithin.mono fun p hp ↦ ?_) EventuallyEq.rfl
  rw [Set.mem_ofPred_eq] at hp
  -- The mass term `-ε * ∑ j, k j` vanishes when the total mass of the column marginal is fixed.
  have hk : ∑ j, (p.2 j - b j) = 0 := by rw [Finset.sum_sub_distrib, hp.2, sub_self]
  have hsum : ∑ j, (g j - ε) * (p.2 j - b j) = ∑ j, g j * (p.2 j - b j) := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hk, mul_zero, sub_zero]
  simp [smul_eq_mul, hsum]

end Matrix
