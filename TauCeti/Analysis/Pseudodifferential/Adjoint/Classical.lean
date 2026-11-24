/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.FormalAdjoint

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

The homogeneous symbols `TauCeti.HomogeneousSymbol.adjointTerm k a` and the formal adjoint
`TauCeti.ClassicalSymbol.adjointTerms` of an expansion are set up in
`TauCeti.Analysis.Pseudodifferential.Symbol.FormalAdjoint`.

* `TauCeti.ClassicalSymbol.adjointTerm a k`: the term of order `m - k` of the adjoint expansion of
  a classical symbol `a`, again classical, with full symbol `TauCeti.Symbol.adjointTerm`
  (`TauCeti.ClassicalSymbol.toSymbol_adjointTerm`).
* `TauCeti.ClassicalSymbol.exists_remainder_adjointTerms_of_isAsymptoticSum`: a symbol that is an
  asymptotic sum of the terms `adjointTerm a k` has remainders of order `m - N` after the first `N`
  homogeneous terms `adjointTerms a.term`.
* `TauCeti.ClassicalSymbol.adjoint`: **the adjoint of a classical symbol is classical**, with full
  symbol the adjoint symbol (`TauCeti.ClassicalSymbol.toSymbol_adjoint`) and homogeneous terms
  `adjointTerms a.term` (`TauCeti.ClassicalSymbol.term_adjoint`).
* `TauCeti.ClassicalSymbol.principal_adjoint`: the principal symbol of `a*` is `a_m†`.
* `TauCeti.ClassicalSymbol.coefficient_term_one_adjoint`: the term of degree `m - 1` of `a*`.
* `TauCeti.ClassicalSymbol.isElliptic_adjoint_iff`: `a*` is elliptic exactly when `a` is.
* `TauCeti.ClassicalSymbol.exists_inclusion_eq_adjoint_sub_pointwiseAdjoint`: `a* - a†` is a
  classical symbol of order `m - 1` with principal symbol `-i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`, where `a†`
  is the pointwise adjoint `TauCeti.ClassicalSymbol.pointwiseAdjoint`.
* `TauCeti.ClassicalSymbol.eq_adjoint_of_forall_integral_inner_eq`: if the quantization of `b` is
  the formal adjoint of that of `a` on compactly supported Schwartz functions, then `b = a*`, and
  `TauCeti.ClassicalSymbol.adjoint_principal_eq_of_forall_integral_inner_eq`: the principal symbol
  of `b` is `a_m†`. For `b = a`, a formally self-adjoint quantization has `a* = a` and a pointwise
  self-adjoint principal symbol.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7 and
  Definition 18.1.5.
-/

public section

noncomputable section

open Finset
open scoped SchwartzMap

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

namespace ClassicalSymbol

open HomogeneousSymbol

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

/-- **Classical remainders of the adjoint expansion.** If a symbol `c` of order `m` is an
asymptotic sum `c ∼ ∑ₖ adjointTerm a k` of the terms of the adjoint expansion of a classical symbol
`a`, then its remainder after the first `N` homogeneous terms `adjointTerms a.term` has order
`m - N`: it is the remainder of the asymptotic sum after `N` terms, plus the remainder after
`N - k` homogeneous terms of each term `adjointTerm a k`, `k < N`. -/
theorem exists_remainder_adjointTerms_of_isAsymptoticSum (a : ClassicalSymbol n V W m)
    {c : Symbol n W V m}
    (hc : (Symbol.inclusion (by simp) c : Symbol n W V (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum
      a.toSymbol.adjointTerm)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n W V (m - N), ∀ p, r.coefficient p =
      c.coefficient p - ∑ j ∈ range N, χ p.2 • (adjointTerms a.term j).coefficient p := by
  obtain ⟨r, hr⟩ := exists_remainder_of_isAsymptoticSum (fun k ↦ a.adjointTerm k) hc χ N
  exact ⟨r, fun p ↦ by simp [hr p, coefficient_adjointTerms]⟩

/-- **The adjoint of a classical symbol is classical.** For a classical symbol `a` of order `m`
between complex Hilbert spaces, with compact spatial support, the adjoint symbol `a*`, whose
quantization is the formal adjoint of the quantization of `a`, is a classical symbol of order `m`.
Its homogeneous terms are the formal adjoint `adjointTerms a.term` of the expansion of `a`: the
term of degree `m - j` is `∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a_{m-j+k})†`. -/
def adjoint (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport) :
    ClassicalSymbol n W V m where
  toSymbol := a.toSymbol.adjoint ha
  term := adjointTerms a.term
  exists_remainder' := ⟨default,
    exists_remainder_adjointTerms_of_isAsymptoticSum a (Symbol.isAsymptoticSum_adjoint ha) default⟩

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

/-- **The adjoint up to order `m - 1`.** The adjoint symbol `a*` differs from the pointwise adjoint
`a†` by a classical symbol of order `m - 1`, whose principal symbol is
`-i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`. -/
theorem exists_inclusion_eq_adjoint_sub_pointwiseAdjoint :
    ∃ c : ClassicalSymbol n W V (m - 1),
      inclusion 1 (by simp) c = a.adjoint ha - a.pointwiseAdjoint ∧
      ∀ z, c.principal.coefficient z =
        -Complex.I • ∑ j, ContinuousLinearMap.adjoint
          (((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  have h0 : (a.adjoint ha - a.pointwiseAdjoint).principal = 0 := by
    simp [principal_sub]
  obtain ⟨c, hc⟩ := (principal_eq_zero_iff_exists_inclusion _).1 h0
  refine ⟨c, hc, fun z => ?_⟩
  rw [coefficient_principal_of_inclusion_eq hc, term_sub, HomogeneousSymbol.coefficient_sub,
    Pi.sub_apply, coefficient_term_one_adjoint, term_pointwiseAdjoint, coefficient_adjoint,
    neg_smul]
  abel

end Adjoint

/-! ### Uniqueness of the adjoint -/

section FormalAdjoint

variable {m : ℝ} (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport)

/-- **Uniqueness of the adjoint.** Let `a` be a classical symbol with compact spatial support. If
the quantization of a classical symbol `b` is the formal adjoint of that of `a` on compactly
supported Schwartz functions, `∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(b) v⟫`, then `b` is the adjoint symbol
`a*`. For `b = a` this says that a formally self-adjoint quantization has `a* = a`. -/
theorem eq_adjoint_of_forall_integral_inner_eq {b : ClassicalSymbol n W V m}
    (h : ∀ (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)), HasCompactSupport u →
      HasCompactSupport v →
        ∫ x, inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient u x) (v x) =
          ∫ x, inner ℂ (u x) (quantizeSchwartzValue b.toSymbol.coefficient v x)) :
    b = a.adjoint ha := by
  ext1
  rw [toSymbol_adjoint]
  exact Symbol.ext (Symbol.coefficient_eq_adjoint_of_forall_integral_inner_eq ha h)

include ha in
/-- **The principal symbol of a formal adjoint.** Let `a` be a classical symbol with compact
spatial support. If the quantization of a classical symbol `b` is the formal adjoint of that of
`a` on compactly supported Schwartz functions, then the principal symbol of `b` is the pointwise
adjoint `a_m(x, ξ)†` of that of `a`. For `b = a`: the principal symbol of a formally self-adjoint
quantization is a self-adjoint operator at every position and frequency. -/
theorem adjoint_principal_eq_of_forall_integral_inner_eq {b : ClassicalSymbol n W V m}
    (h : ∀ (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)), HasCompactSupport u →
      HasCompactSupport v →
        ∫ x, inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient u x) (v x) =
          ∫ x, inner ℂ (u x) (quantizeSchwartzValue b.toSymbol.coefficient v x)) :
    a.principal.adjoint = b.principal := by
  rw [← principal_adjoint a ha, eq_adjoint_of_forall_integral_inner_eq a ha h]

end FormalAdjoint

end ClassicalSymbol

end TauCeti
