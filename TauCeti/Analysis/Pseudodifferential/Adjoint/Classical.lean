/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion

/-!
# The adjoint of a classical symbol

Let `a` be a classical symbol of order `m` with values in operators between complex Hilbert spaces
that vanishes for positions outside a compact set. This file shows that its adjoint symbol `a*`
(`TauCeti.Symbol.adjoint`), whose quantization is the formal adjoint of the quantization of `a`,
is again classical, of order `m`, and computes its homogeneous terms.

Each term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of the adjoint expansion
(`TauCeti.Symbol.adjointTerm`) is a classical symbol of order `m - k`
(`TauCeti.ClassicalSymbol.adjointTerm`), built from the pointwise adjoint
`a† = a.map adjointRealCLM` and the derivatives of classical symbols by the recursion
`adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{xⱼ} ∂_{ξⱼ} a) k`. Its homogeneous term
of degree `m - k - l` is `TauCeti.HomogeneousSymbol.adjointTerm k a_{m-l}`, given by the same
recursion applied to the homogeneous term `a_{m-l}` of `a`. Collecting the homogeneous terms of the
same degree, the term of degree `m - j` of `a*` is

`(a*)_{m-j} = ∑_{k + l = j} HomogeneousSymbol.adjointTerm k a_{m-l}`

(`TauCeti.ClassicalSymbol.adjointTerms`). In particular the principal symbol of `a*` is the
pointwise adjoint `a_m†`, and its next term is `a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`.

## Main results

* `TauCeti.ClassicalSymbol.adjoint`: **the adjoint of a classical symbol is classical**, with the
  terms `adjointTerms a.term` (`TauCeti.ClassicalSymbol.term_adjoint`).
* `TauCeti.ClassicalSymbol.principal_adjoint`: the principal symbol of `a*` is the pointwise
  adjoint of the principal symbol of `a`.
* `TauCeti.ClassicalSymbol.isElliptic_adjoint_iff`: `a*` is elliptic exactly when `a` is.
* `TauCeti.ClassicalSymbol.exists_inclusion_eq_adjoint_sub_map`: `a* - a†` is a classical symbol
  of order `m - 1`, with principal symbol `-i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open Finset
open ContinuousLinearMap (adjointRealCLM)

namespace TauCeti

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### The terms of the adjoint expansion of a homogeneous symbol -/

namespace HomogeneousSymbol

/-- The term with `k` derivatives of the adjoint expansion of a homogeneous symbol `a` of degree
`m`, a homogeneous symbol of degree `m - k`. It is defined by the recursion `adjointTerm 0 a = a†`
and `adjointTerm (k + 1) a = (-i / (k + 1)) ∑ⱼ adjointTerm k (∂_{xⱼ} ∂_{ξⱼ} a)`, the recursion that
defines the term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of the adjoint expansion of a full
symbol (`TauCeti.Symbol.adjointTerm`, `TauCeti.Symbol.coefficient_adjointTerm`). -/
def adjointTerm : (k : ℕ) → {m : ℝ} →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (m - k)
  | 0, _, a => a.adjoint.castDegree (by simp)
  | k + 1, _, a => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (adjointTerm k ((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (EuclideanSpace.single j 1))).castDegree (by push_cast; ring)

variable (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

theorem adjointTerm_zero : adjointTerm 0 a = a.adjoint.castDegree (by simp) :=
  (rfl)

theorem adjointTerm_succ (k : ℕ) :
    adjointTerm (k + 1) a = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (adjointTerm k ((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (EuclideanSpace.single j 1))).castDegree (by push_cast; ring) :=
  (rfl)

/-- Transporting the degree of a homogeneous symbol transports the degree of every term of its
adjoint expansion. -/
@[simp]
theorem adjointTerm_castDegree {m' : ℝ} (h : m = m') (k : ℕ) :
    adjointTerm k (a.castDegree h) = (adjointTerm k a).castDegree (by rw [h]) := by
  subst h
  rw [castDegree_rfl, castDegree_rfl]

@[simp]
theorem coefficient_adjointTerm_zero (p : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerm 0 a).coefficient p = ContinuousLinearMap.adjoint (a.coefficient p) := by
  simp [adjointTerm_zero]

end HomogeneousSymbol

namespace ClassicalSymbol

open HomogeneousSymbol

/-! ### The homogeneous terms of the adjoint expansion -/

section AdjointTerms

/-- The homogeneous terms `cⱼ = ∑_{k + l = j} HomogeneousSymbol.adjointTerm k pₗ` of the formal
adjoint of an expansion `∑ₗ pₗ`, with the term `pₗ` of degree `m - l`. The term `cⱼ` has degree
`m - j`. -/
def adjointTerms
    (p : (l : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - l))
    (j : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (m - j) :=
  ∑ k ∈ range (j + 1),
    if h : k ≤ j then (adjointTerm k (p (j - k))).castDegree (by rw [Nat.cast_sub h]; ring)
    else 0

variable (p : (l : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - l))

/-- The coefficient of `cⱼ` is `∑_{k ≤ j} adjointTerm k p_{j-k}`. -/
theorem coefficient_adjointTerms (j : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerms p j).coefficient z =
      ∑ k ∈ range (j + 1), (adjointTerm k (p (j - k))).coefficient z := by
  rw [adjointTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [Nat.le_of_lt_succ (Finset.mem_range.1 hk)]

/-- The leading term of the formal adjoint is the pointwise adjoint of the leading term. -/
@[simp]
theorem coefficient_adjointTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerms p 0).coefficient z = ContinuousLinearMap.adjoint ((p 0).coefficient z) := by
  simp [coefficient_adjointTerms]

/-- The term `c₁ = p₁† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} p₀)†` of the formal adjoint. -/
theorem coefficient_adjointTerms_one (z : CoordinateSpace n × CoordinateSpace n) :
    (adjointTerms p 1).coefficient z =
      ContinuousLinearMap.adjoint ((p 1).coefficient z) -
        Complex.I • ∑ j, ContinuousLinearMap.adjoint
          ((((p 0).frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  simp [coefficient_adjointTerms, Finset.sum_range_succ, adjointTerm_succ, sub_eq_add_neg]

end AdjointTerms

/-! ### The terms of the adjoint expansion of a classical symbol -/

section Term

/-- The term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of the adjoint expansion, as a classical
symbol of order `m - k`. It is defined by the recursion of `TauCeti.Symbol.adjointTerm`, whose full
symbol it has (`TauCeti.ClassicalSymbol.toSymbol_adjointTerm`):
`adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{xⱼ} ∂_{ξⱼ} a) k`, starting from the
pointwise adjoint `adjointTerm a 0 = a†`. -/
def adjointTerm : {m : ℝ} → ClassicalSymbol n V W m → (k : ℕ) → ClassicalSymbol n W V (m - k)
  | _, a, 0 => inclusion 0 (by simp) (a.map adjointRealCLM)
  | _, a, k + 1 => inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, adjointTerm (spatialDeriv j (frequencyDeriv j a)) k)

theorem adjointTerm_zero (a : ClassicalSymbol n V W m) :
    a.adjointTerm 0 = inclusion 0 (by simp) (a.map adjointRealCLM) := by
  rw [adjointTerm]

theorem adjointTerm_succ (a : ClassicalSymbol n V W m) (k : ℕ) :
    a.adjointTerm (k + 1) = inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, (spatialDeriv j (frequencyDeriv j a)).adjointTerm k) := by
  rw [adjointTerm]

/-- The full symbol of the classical term `adjointTerm a k` is the term `Symbol.adjointTerm` of
the adjoint expansion of the full symbol. -/
@[simp]
theorem toSymbol_adjointTerm (a : ClassicalSymbol n V W m) (k : ℕ) :
    (a.adjointTerm k).toSymbol = a.toSymbol.adjointTerm k := by
  induction k generalizing m with
  | zero =>
    rw [adjointTerm_zero, Symbol.adjointTerm_zero]
    ext1
    simp
  | succ k ih =>
    rw [adjointTerm_succ, Symbol.adjointTerm_succ]
    ext1
    simp [ih]

/-- The homogeneous term of degree `m - k - l` of `adjointTerm a k` is the term
`HomogeneousSymbol.adjointTerm k a_{m-l}` of the adjoint expansion of the homogeneous term
`a_{m-l}`. -/
theorem coefficient_term_adjointTerm (a : ClassicalSymbol n V W m) (k l : ℕ) :
    ((a.adjointTerm k).term l).coefficient =
      (HomogeneousSymbol.adjointTerm k (a.term l)).coefficient := by
  induction k generalizing m with
  | zero =>
    rw [adjointTerm_zero, term_inclusion_zero, coefficient_castDegree, term_map]
    funext z
    simp [ContinuousLinearMap.adjointRealCLM_apply]
  | succ k ih =>
    rw [adjointTerm_succ, term_inclusion_zero, coefficient_castDegree, term_smul, term_sum]
    funext z
    simp only [HomogeneousSymbol.coefficient_smul, HomogeneousSymbol.coefficient_sum,
      Pi.smul_apply, Finset.sum_apply, ih, HomogeneousSymbol.adjointTerm_succ, term_spatialDeriv,
      term_frequencyDeriv, spatialDeriv_castDegree, adjointTerm_castDegree, coefficient_castDegree]

end Term

/-! ### The adjoint of a classical symbol -/

section Adjoint

/-- The remainder of the adjoint symbol of a classical symbol after `N` terms has order `m - N`: it
is the remainder of the adjoint expansion after `N` terms, plus the remainder after `N - k`
homogeneous terms of each term `adjointTerm a k`, `k < N`. -/
private theorem exists_remainder_adjoint (a : ClassicalSymbol n V W m)
    (ha : a.toSymbol.HasCompactSpatialSupport) (χ : FrequencyCutoff (CoordinateSpace n))
    (N : ℕ) :
    ∃ r : Symbol n W V (m - N), ∀ p, r.coefficient p =
      (a.toSymbol.adjoint ha).coefficient p -
        ∑ j ∈ range N, χ p.2 • (adjointTerms a.term j).coefficient p := by
  -- The remainder of `adjointTerm a k` after `N - k` terms has order `m - N` for `k ≤ N`.
  have hord (k : ℕ) : m - k - ((N - k : ℕ) : ℝ) ≤ m - N := by
    have : (N : ℝ) ≤ k + ((N - k : ℕ) : ℝ) := by exact_mod_cast le_add_tsub
    linarith
  refine ⟨a.toSymbol.adjointRemainder ha N +
    ∑ k ∈ range N, Symbol.inclusion (hord k) ((a.adjointTerm k).remainder χ (N - k)),
    fun p => ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Symbol.coefficient_inclusion,
    Symbol.coefficient_adjointRemainder, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    coefficient_remainder, toSymbol_adjointTerm, coefficient_term_adjointTerm,
    coefficient_adjointTerms, Finset.smul_sum, Finset.sum_sub_distrib]
  -- Reindex the double sum over `k + l = j < N` by `k < N`, `l < N - k`.
  rw [Finset.sum_range_diag_flip N
    fun k l => χ p.2 • (HomogeneousSymbol.adjointTerm k (a.term l)).coefficient p]
  abel

/-- **The adjoint of a classical symbol is classical.** For a classical symbol `a` of order `m`
with compact spatial support, the adjoint symbol `a*`, whose quantization is the formal adjoint of
the quantization of `a`, is a classical symbol of order `m`. Its homogeneous terms are the formal
adjoint `adjointTerms a.term` of the expansion of `a`; the term of degree `m - j` is
`∑_{k + l = j} HomogeneousSymbol.adjointTerm k a_{m-l}`. -/
def adjoint (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport) :
    ClassicalSymbol n W V m where
  toSymbol := a.toSymbol.adjoint ha
  term := adjointTerms a.term
  exists_remainder' := ⟨default, exists_remainder_adjoint a ha default⟩

variable (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport)

@[simp]
theorem toSymbol_adjoint : (a.adjoint ha).toSymbol = a.toSymbol.adjoint ha :=
  (rfl)

@[simp]
theorem term_adjoint (j : ℕ) : (a.adjoint ha).term j = adjointTerms a.term j :=
  (rfl)

/-- **The principal symbol of the adjoint** is the pointwise adjoint of the principal symbol. -/
@[simp]
theorem principal_adjoint : (a.adjoint ha).principal = a.principal.adjoint := by
  ext1
  funext z
  simp

/-- The term of degree `m - 1` of the adjoint `a*` of a classical symbol is
`a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`. -/
theorem coefficient_term_one_adjoint (z : CoordinateSpace n × CoordinateSpace n) :
    ((a.adjoint ha).term 1).coefficient z =
      ContinuousLinearMap.adjoint ((a.term 1).coefficient z) -
        Complex.I • ∑ j, ContinuousLinearMap.adjoint
          (((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  rw [term_adjoint, coefficient_adjointTerms_one, principal_def]
  simp

/-- The adjoint of a classical symbol is elliptic exactly when the symbol is. -/
@[simp]
theorem isElliptic_adjoint_iff : (a.adjoint ha).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, isElliptic_def, principal_adjoint, HomogeneousSymbol.isElliptic_adjoint_iff]

/-- **The adjoint modulo lower order.** For a classical symbol `a` of order `m` with compact
spatial support, the difference `a* - a†` between the adjoint symbol and the pointwise adjoint is
a classical symbol of order `m - 1`, with principal symbol `-i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`. -/
theorem exists_inclusion_eq_adjoint_sub_map :
    ∃ c : ClassicalSymbol n W V (m - 1),
      inclusion 1 (by simp) c = a.adjoint ha - a.map adjointRealCLM ∧
      ∀ z, c.principal.coefficient z =
        -Complex.I • ∑ j, ContinuousLinearMap.adjoint
          (((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  have h0 : (a.adjoint ha - a.map adjointRealCLM).principal = 0 := by
    ext1
    funext z
    simp [ContinuousLinearMap.adjointRealCLM_apply]
  obtain ⟨c, hc⟩ := (principal_eq_zero_iff_exists_inclusion _).1 h0
  refine ⟨c, hc, fun z => ?_⟩
  -- The principal symbol of `c` is the term of index `1` of the difference.
  have hterm := congrArg (fun d : ClassicalSymbol n W V m => (d.term (1 + 0)).coefficient z) hc
  simp only [term_inclusion_add, coefficient_castDegree] at hterm
  rw [coefficient_principal, hterm, term_sub, HomogeneousSymbol.coefficient_sub, Pi.sub_apply,
    coefficient_term_one_adjoint, term_map, HomogeneousSymbol.coefficient_map,
    ContinuousLinearMap.adjointRealCLM_apply, sub_sub_cancel_left, neg_smul]

end Adjoint

end ClassicalSymbol

end TauCeti
