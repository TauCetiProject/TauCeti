/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# The formal adjoint of homogeneous symbol expansions

The adjoint symbol `a*` of a symbol `a` with values in operators between complex Hilbert spaces
has the expansion `a* ∼ ∑ₖ ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`, so for a classical symbol
`a ∼ ∑ᵢ a_{m-i}` its homogeneous term of degree `m - j` collects
`((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a_{m-j+k})†` over `k ≤ j`. This file sets up this formal
adjoint of expansions.

* `TauCeti.HomogeneousSymbol.adjointTerm k a`: the homogeneous symbol
  `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of degree `m - k`
  (`TauCeti.HomogeneousSymbol.coefficient_adjointTerm`), defined by the recursion of
  `TauCeti.Symbol.adjointTerm`.
* `TauCeti.ClassicalSymbol.adjointTerms`: the homogeneous terms
  `cⱼ = ∑_{k ≤ j} adjointTerm k q_{j-k}` of the formal adjoint of an expansion `∑ᵢ qᵢ`. Its
  leading term is the pointwise adjoint `q₀†` (`ClassicalSymbol.coefficient_adjointTerms_zero`)
  and the next one is `q₁† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} q₀)†`
  (`ClassicalSymbol.coefficient_adjointTerms_one`).

Everything here is a statement about homogeneous terms. That `adjointTerms` gives the expansion of
the adjoint symbol is the adjoint theorem of the symbol calculus: for a classical symbol `a` of
compact spatial support, the adjoint symbol `TauCeti.ClassicalSymbol.adjoint`, whose quantization
is the formal adjoint of `Op(a)`, is classical with the terms `adjointTerms a.term`
(`TauCeti.ClassicalSymbol.term_adjoint`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### The terms of the adjoint expansion of a homogeneous symbol -/

namespace HomogeneousSymbol

/-- The homogeneous symbol `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of degree `m - k`, the
term of the formal adjoint of `a` with `k` position and `k` frequency derivatives. It is defined by
the recursion of `TauCeti.Symbol.adjointTerm`: `adjointTerm 0 a = a†` and
`adjointTerm (k + 1) a = (-i / (k + 1)) ∑ⱼ adjointTerm k (∂_{xⱼ} ∂_{ξⱼ} a)`; the closed form is
`TauCeti.HomogeneousSymbol.coefficient_adjointTerm`. -/
def adjointTerm : (k : ℕ) → {m : ℝ} →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (m - k)
  | 0, _, a => a.adjoint.castDegree (by simp)
  | k + 1, _, a => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (adjointTerm k ((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (EuclideanSpace.single j 1))).castDegree (by push_cast; ring)

variable {m : ℝ} (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

theorem adjointTerm_zero : adjointTerm 0 a = a.adjoint.castDegree (by simp) :=
  (rfl)

theorem adjointTerm_succ (k : ℕ) :
    adjointTerm (k + 1) a = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (adjointTerm k ((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (EuclideanSpace.single j 1))).castDegree (by push_cast; ring) :=
  (rfl)

@[simp]
theorem coefficient_adjointTerm_zero (p : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerm 0 a).coefficient p = ContinuousLinearMap.adjoint (a.coefficient p) := by
  simp [adjointTerm_zero]

/-- Transporting the degree of `a` transports the degree of every term of its formal adjoint. -/
@[simp]
theorem adjointTerm_castDegree {m' : ℝ} (h : m = m') (k : ℕ) :
    adjointTerm k (a.castDegree h) = (adjointTerm k a).castDegree (by rw [h]) := by
  subst h
  rw [castDegree_rfl, castDegree_rfl]

/-- **Closed form of the adjoint terms.** At a nonzero frequency, `adjointTerm k a` is
`((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`, the sum over the words `w` of length `k` in the
coordinate directions. -/
theorem coefficient_adjointTerm (k : ℕ) (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) :
    (adjointTerm k a).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial : ℂ) •
      ∑ w : Fin k → Fin n,
        ContinuousLinearMap.adjoint (mixedDeriv (List.ofFn w) (List.ofFn w) a.coefficient x ξ) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [adjointTerm_succ, coefficient_smul, Pi.smul_apply, coefficient_sum, Finset.sum_apply,
      ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp, Fintype.sum_prod_type]
    simp only [coefficient_castDegree, ih, mixedDeriv_spatialDeriv_frequencyDeriv _ _ _ _ _ _ hξ,
      Finset.smul_sum, smul_smul, Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc,
      Fin.snoc_last, List.concat_eq_append]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end HomogeneousSymbol

namespace ClassicalSymbol

open HomogeneousSymbol

/-! ### The formal adjoint of an expansion -/

section AdjointTerms

variable {m : ℝ}

/-- The homogeneous terms `cⱼ = ∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w q_{j-k})†` of the
formal adjoint of an expansion `∑ᵢ qᵢ` with terms `qᵢ` of degree `m - i`. The term `cⱼ` has
degree `m - j`. -/
def adjointTerms
    (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - i))
    (j : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (m - j) :=
  ∑ k ∈ range (j + 1),
    if h : k ≤ j then
      (adjointTerm k (q (j - k))).castDegree (by rw [Nat.cast_sub h]; ring)
    else 0

variable (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - i))

/-- The coefficient of `cⱼ` is `∑_{k ≤ j} adjointTerm k q_{j-k}`. -/
theorem coefficient_adjointTerms (j : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerms q j).coefficient z =
      ∑ k ∈ range (j + 1), (adjointTerm k (q (j - k))).coefficient z := by
  simp only [adjointTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp [Nat.lt_succ_iff.1 (mem_range.1 hk)]

/-- The leading term of the formal adjoint is the pointwise adjoint of the leading term. -/
@[simp]
theorem coefficient_adjointTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerms q 0).coefficient z = ContinuousLinearMap.adjoint ((q 0).coefficient z) := by
  simp [coefficient_adjointTerms]

/-- The term `c₁ = q₁† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} q₀)†` of the formal adjoint. -/
theorem coefficient_adjointTerms_one (z : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerms q 1).coefficient z =
      ContinuousLinearMap.adjoint ((q 1).coefficient z) -
        Complex.I • ∑ j, ContinuousLinearMap.adjoint
          ((((q 0).frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  simp [coefficient_adjointTerms, Finset.sum_range_succ, adjointTerm_succ, sub_eq_add_neg]

end AdjointTerms

end ClassicalSymbol

end TauCeti
