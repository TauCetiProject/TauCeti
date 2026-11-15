/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# The adjoint of a classical symbol

Let `a` be a classical symbol of order `m` with values in operators between complex Hilbert
spaces, `a ∼ ∑ⱼ a_{m-j}` with homogeneous terms `a_{m-j}`, and suppose that `a` vanishes for
positions outside a compact set. Its adjoint symbol `a*` (`TauCeti.Symbol.adjoint`), whose
quantization is the formal adjoint of the quantization of `a`, has the asymptotic expansion
`a* ∼ ∑ₖ ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`
(`TauCeti.Symbol.adjoint_eq_sum_adjointTerm_add_adjointRemainder`). This file shows that `a*` is
again a classical symbol of order `m`, and computes its homogeneous terms. Expanding each term of
the adjoint expansion into the homogeneous terms of `a`, the term of degree `m - j` of `a*` is

`(a*)_{m-j} = ∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a_{m-j+k})†`.

In particular the principal symbol of `a*` is the pointwise adjoint `a_m†` of the principal symbol
of `a`, so `a*` is elliptic exactly when `a` is, and its next term is

`(a*)_{m-1} = a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`.

The second summand cannot be dropped: in one dimension, for `a(x, ξ) = φ(x) ξ` with `φ` compactly
supported and `ψ = conj ∘ φ`, `a* = ψ(x) ξ - i ψ'(x)`, which is the symbol of `u ↦ D(ψ u)` for
`D = -i ∂`.

## Main declarations

* `TauCeti.HomogeneousSymbol.adjointTerm k a`: the homogeneous symbol
  `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of degree `m - k`
  (`TauCeti.HomogeneousSymbol.coefficient_adjointTerm`), defined by the recursion of
  `TauCeti.Symbol.adjointTerm`.
* `TauCeti.ClassicalSymbol.adjointTerms`: the homogeneous terms
  `cⱼ = ∑_{k ≤ j} adjointTerm k q_{j-k}` of the formal adjoint of an expansion `∑ᵢ qᵢ`.
* `TauCeti.ClassicalSymbol.adjointTerm a k`: the term of order `m - k` of the adjoint expansion of
  a classical symbol `a`, again classical, with full symbol `TauCeti.Symbol.adjointTerm`
  (`TauCeti.ClassicalSymbol.toSymbol_adjointTerm`).
* `TauCeti.ClassicalSymbol.adjoint`: **the adjoint of a classical symbol is classical**, with full
  symbol the adjoint symbol (`TauCeti.ClassicalSymbol.toSymbol_adjoint`) and homogeneous terms
  `adjointTerms a.term` (`TauCeti.ClassicalSymbol.term_adjoint`).
* `TauCeti.ClassicalSymbol.principal_adjoint`: the principal symbol of `a*` is `a_m†`.
* `TauCeti.ClassicalSymbol.coefficient_term_one_adjoint`: the term of degree `m - 1` of `a*`.
* `TauCeti.ClassicalSymbol.isElliptic_adjoint_iff`: `a*` is elliptic exactly when `a` is.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7 and
  Definition 18.1.5.
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

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
    simp only [coefficient_castDegree, ih, mixedDeriv_spatialDeriv_frequencyDeriv _ _ _ _ _ hξ,
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

/-! ### The terms of the adjoint expansion of a classical symbol -/

section AdjointTerm

/-- The remainder of the term `adjointTerm a k` of the adjoint expansion of a classical symbol
after `N` homogeneous terms has order `m - k - N`. -/
private theorem exists_remainder_adjointTerm (χ : FrequencyCutoff (CoordinateSpace n)) (k : ℕ) :
    ∀ {m : ℝ} (a : ClassicalSymbol n V W m) (N : ℕ), ∃ r : Symbol n W V (m - k - N), ∀ p,
      r.coefficient p = (a.toSymbol.adjointTerm k).coefficient p -
        ∑ j ∈ range N, χ p.2 • (adjointTerm k (a.term j)).coefficient p := by
  induction k with
  | zero =>
    -- The pointwise adjoint of the remainder of `a`.
    intro m a N
    refine ⟨Symbol.inclusion (le_of_eq (by simp)) ((a.remainder χ N).map adjointRealCLM),
      fun p ↦ ?_⟩
    simp only [Symbol.coefficient_inclusion, Symbol.coefficient_map, coefficient_remainder,
      map_sub, map_sum, map_smul, adjointRealCLM_apply, Symbol.coefficient_adjointTerm_zero,
      coefficient_adjointTerm_zero]
  | succ k ih =>
    -- The recursion of the terms, applied to the remainders of `∂_{xⱼ} ∂_{ξⱼ} a`.
    intro m a N
    choose r hr using fun l : Fin n ↦ ih (spatialDeriv l (frequencyDeriv l a)) N
    refine ⟨Symbol.inclusion (le_of_eq (by push_cast; ring))
      ((-Complex.I / (k + 1)) • ∑ l, r l), fun p ↦ ?_⟩
    simp only [Symbol.coefficient_inclusion, Symbol.coefficient_smul, Symbol.coefficient_sum,
      Pi.smul_apply, Finset.sum_apply, hr, toSymbol_spatialDeriv, toSymbol_frequencyDeriv,
      term_spatialDeriv, term_frequencyDeriv, spatialDeriv_castDegree, adjointTerm_castDegree,
      coefficient_castDegree, Symbol.coefficient_adjointTerm_succ, adjointTerm_succ,
      HomogeneousSymbol.coefficient_smul, HomogeneousSymbol.coefficient_sum, Finset.sum_sub_distrib,
      smul_sub, Finset.smul_sum]
    rw [Finset.sum_comm (s := range N)]
    simp only [smul_comm (χ p.2)]

variable {m : ℝ}

/-- The term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of order `m - k` of the adjoint
expansion of a classical symbol `a` of order `m`, as a classical symbol: its full symbol is
`TauCeti.Symbol.adjointTerm` (`TauCeti.ClassicalSymbol.toSymbol_adjointTerm`) and its homogeneous
terms are the terms `adjointTerm k a_{m-j}` of the homogeneous terms of `a`
(`TauCeti.ClassicalSymbol.term_adjointTerm`). -/
def adjointTerm (a : ClassicalSymbol n V W m) (k : ℕ) : ClassicalSymbol n W V (m - k) where
  toSymbol := a.toSymbol.adjointTerm k
  term j := (HomogeneousSymbol.adjointTerm k (a.term j)).castDegree (by ring)
  exists_remainder' := ⟨default, fun N ↦ by simpa using exists_remainder_adjointTerm default k a N⟩

variable (a : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_adjointTerm (k : ℕ) : (a.adjointTerm k).toSymbol = a.toSymbol.adjointTerm k :=
  (rfl)

@[simp]
theorem term_adjointTerm (k j : ℕ) :
    (a.adjointTerm k).term j =
      (HomogeneousSymbol.adjointTerm k (a.term j)).castDegree (by ring) :=
  (rfl)

end AdjointTerm

/-! ### The adjoint of a classical symbol -/

section Adjoint

variable {m : ℝ}

/-- The remainder of the adjoint symbol of a classical symbol after `N` terms has order `m - N`:
it is the remainder of the adjoint expansion after `N` terms, plus the remainder after `N - k`
homogeneous terms of each term `adjointTerm a k`, `k < N`. -/
private theorem exists_remainder_adjoint (a : ClassicalSymbol n V W m)
    (ha : a.toSymbol.HasCompactSpatialSupport) (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n W V (m - N), ∀ p, r.coefficient p =
      (a.toSymbol.adjoint ha).coefficient p -
        ∑ j ∈ range N, χ p.2 • (adjointTerms a.term j).coefficient p := by
  -- The remainder of `adjointTerm a k` after `N - k` terms has order `m - N` for `k ≤ N`.
  have hord (k : ℕ) : m - k - ((N - k : ℕ) : ℝ) ≤ m - N := by
    have : (N : ℝ) ≤ k + ((N - k : ℕ) : ℝ) := by exact_mod_cast le_add_tsub
    linarith
  refine ⟨a.toSymbol.adjointRemainder ha N +
    ∑ k ∈ range N, Symbol.inclusion (hord k) ((a.adjointTerm k).remainder χ (N - k)),
    fun p ↦ ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Symbol.coefficient_inclusion,
    Symbol.coefficient_adjointRemainder, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    coefficient_remainder, toSymbol_adjointTerm, term_adjointTerm, coefficient_castDegree,
    coefficient_adjointTerms, Finset.smul_sum, Finset.sum_sub_distrib]
  -- Reindex the double sum over `k + i = j < N` by `k < N`, `i < N - k`.
  rw [Finset.sum_range_diag_flip N
    fun k i ↦ χ p.2 • (HomogeneousSymbol.adjointTerm k (a.term i)).coefficient p]
  abel

/-- **The adjoint of a classical symbol is classical.** For a classical symbol `a` of order `m`
between complex Hilbert spaces, with compact spatial support, the adjoint symbol `a*`, whose
quantization is the formal adjoint of the quantization of `a`, is a classical symbol of order `m`.
Its homogeneous terms are the formal adjoint `adjointTerms a.term` of the expansion of `a`: the
term of degree `m - j` is `∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a_{m-j+k})†`. -/
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

/-- **The principal symbol of the adjoint** is the pointwise adjoint `a_m†` of the principal
symbol. -/
@[simp]
theorem principal_adjoint : (a.adjoint ha).principal = a.principal.adjoint := by
  ext1
  funext z
  simp

/-- The term of degree `m - 1` of the adjoint symbol is `a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`. -/
theorem coefficient_term_one_adjoint (z : CoordinateSpace n × CoordinateSpace n) :
    ((a.adjoint ha).term 1).coefficient z =
      ContinuousLinearMap.adjoint ((a.term 1).coefficient z) -
        Complex.I • ∑ j, ContinuousLinearMap.adjoint
          (((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  rw [term_adjoint, coefficient_adjointTerms_one, principal_def]
  simp

/-- **The adjoint of an elliptic symbol is elliptic**, and conversely: the principal symbol of
`a*` is invertible exactly where that of `a` is. -/
@[simp]
theorem isElliptic_adjoint_iff : (a.adjoint ha).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, isElliptic_def, principal_adjoint, HomogeneousSymbol.isElliptic_adjoint_iff]

end Adjoint

end ClassicalSymbol

end TauCeti
