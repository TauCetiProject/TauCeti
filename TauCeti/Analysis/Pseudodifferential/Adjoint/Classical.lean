/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# Adjoints of classical symbols

Let `a` be a classical symbol of order `m` with values in operators between complex Hilbert spaces
`V` and `W`, that vanishes for positions outside a compact set. This file shows that its adjoint
symbol `a*` (`TauCeti.Symbol.adjoint`), whose quantization is the formal adjoint of `Op(a)`, is
again classical of order `m`, and computes its homogeneous terms. In particular the principal
symbol of `a*` is the pointwise adjoint `a_m†` of the principal symbol of `a`, and its next term is

`a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`.

The pointwise adjoint `(x, ξ) ↦ a(x, ξ)†` of a classical symbol is classical
(`TauCeti.ClassicalSymbol.pointwiseAdjoint`), with the pointwise adjoints of the homogeneous terms
of `a` as its terms. Each term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of the adjoint
expansion is then a classical symbol of order `m - k` (`TauCeti.ClassicalSymbol.adjointTerm`),
built from the pointwise adjoint and the derivatives of classical symbols. The adjoint symbol `a*`
is their asymptotic sum (`TauCeti.Symbol.isAsymptoticSum_adjoint`), hence classical
(`TauCeti.ClassicalSymbol.ofAsymptoticSum`): its term of degree `m - j` is the sum over `k ≤ j`
of the homogeneous term of index `j - k` of `adjointTerm a k`
(`TauCeti.ClassicalSymbol.asymptoticSumTerms`).

## Main results

* `TauCeti.ClassicalSymbol.adjoint`: **the adjoint of a classical symbol is classical**, with the
  terms `TauCeti.ClassicalSymbol.asymptoticSumTerms`.
* `TauCeti.ClassicalSymbol.principal_adjoint`: the principal symbol of `a*` is `a_m†`; in
  particular `a*` is elliptic exactly when `a` is
  (`TauCeti.ClassicalSymbol.isElliptic_adjoint_iff`).
* `TauCeti.ClassicalSymbol.coefficient_term_one_adjoint`: the term of degree `m - 1` of `a*`.
* `TauCeti.ClassicalSymbol.exists_inclusion_eq_adjoint_sub_pointwiseAdjoint`: `a* - a†` is a
  classical symbol of order `m - 1` with principal symbol `-i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`.
* `TauCeti.ClassicalSymbol.eq_adjoint_of_forall_integral_inner_eq`: if `Op(b)` is the formal
  adjoint of `Op(a)` on compactly supported Schwartz functions, then `b = a*`, and
  `TauCeti.ClassicalSymbol.adjoint_principal_eq_of_forall_integral_inner_eq`: the principal symbol
  of `b` is `a_m†`. For `b = a`, a formally self-adjoint quantization has `a* = a` and a pointwise
  self-adjoint principal symbol.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open Finset
open scoped SchwartzMap

namespace TauCeti

open HomogeneousSymbol

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### The terms of the adjoint expansion -/

section Term

/-- The term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of the adjoint expansion, as a classical
symbol of order `m - k`. It is defined by the recursion of `TauCeti.Symbol.adjointTerm`, whose full
symbol it has (`TauCeti.ClassicalSymbol.toSymbol_adjointTerm`):
`adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{xⱼ} ∂_{ξⱼ} a) k`, starting from the
pointwise adjoint `adjointTerm a 0 = a†`. -/
def adjointTerm : {m : ℝ} → ClassicalSymbol n V W m → (k : ℕ) → ClassicalSymbol n W V (m - k)
  | _, a, 0 => inclusion 0 (by simp) a.pointwiseAdjoint
  | _, a, k + 1 => inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, adjointTerm (spatialDeriv j (frequencyDeriv j a)) k)

theorem adjointTerm_zero (a : ClassicalSymbol n V W m) :
    a.adjointTerm 0 = inclusion 0 (by simp) a.pointwiseAdjoint := by
  rw [adjointTerm]

theorem adjointTerm_succ (a : ClassicalSymbol n V W m) (k : ℕ) :
    a.adjointTerm (k + 1) = inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, (spatialDeriv j (frequencyDeriv j a)).adjointTerm k) := by
  rw [adjointTerm]

/-- The full symbol of the classical term `adjointTerm a k` is the term `Symbol.adjointTerm` of the
adjoint expansion of the full symbol. -/
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

end Term

/-! ### The adjoint of a classical symbol -/

section Adjoint

/-- **The adjoint of a classical symbol is classical.** For a classical symbol `a` of order `m`
with compact spatial support, the adjoint symbol `a*`, whose quantization is the formal adjoint of
`Op(a)` (`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`), is a classical symbol of
order `m`: it is the asymptotic sum of the classical terms `adjointTerm a k`
(`TauCeti.Symbol.isAsymptoticSum_adjoint`). Its homogeneous term of degree `m - j` is
`∑_{k ≤ j} (adjointTerm a k)_{j - k}` (`TauCeti.ClassicalSymbol.asymptoticSumTerms`). -/
def adjoint (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport) :
    ClassicalSymbol n W V m :=
  ofAsymptoticSum (a.toSymbol.adjoint ha) a.adjointTerm (by
    simpa only [toSymbol_adjointTerm] using Symbol.isAsymptoticSum_adjoint ha)

variable (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport)

@[simp]
theorem toSymbol_adjoint : (a.adjoint ha).toSymbol = a.toSymbol.adjoint ha :=
  toSymbol_ofAsymptoticSum ..

@[simp]
theorem term_adjoint (j : ℕ) : (a.adjoint ha).term j = asymptoticSumTerms a.adjointTerm j :=
  term_ofAsymptoticSum ..

/-- **The principal symbol of the adjoint** is the pointwise adjoint of the principal symbol. -/
@[simp]
theorem principal_adjoint : (a.adjoint ha).principal = a.principal.adjoint := by
  ext1
  funext z
  simp [principal_def, coefficient_asymptoticSumTerms, adjointTerm_zero]

/-- The adjoint `a*` is elliptic exactly when `a` is. -/
@[simp]
theorem isElliptic_adjoint_iff : (a.adjoint ha).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_adjoint, HomogeneousSymbol.isElliptic_adjoint_iff, isElliptic_def]

/-- The term of degree `m - 1` of the adjoint `a*` of a classical symbol is
`a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`. -/
theorem coefficient_term_one_adjoint (z : CoordinateSpace n × CoordinateSpace n) :
    ((a.adjoint ha).term 1).coefficient z =
      ContinuousLinearMap.adjoint ((a.term 1).coefficient z) -
        Complex.I • ∑ j, ContinuousLinearMap.adjoint
          (((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  simp [coefficient_asymptoticSumTerms, Finset.sum_range_succ, adjointTerm_zero, adjointTerm_succ,
    sub_eq_add_neg, principal_def]

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
  -- The principal symbol of `c` is the term of index `1` of `a* - a†`.
  have hterm := congrArg (fun d : ClassicalSymbol n W V m => (d.term (1 + 0)).coefficient z) hc
  simp only [term_inclusion_add, coefficient_castDegree] at hterm
  rw [coefficient_principal, hterm, term_sub, HomogeneousSymbol.coefficient_sub, Pi.sub_apply,
    coefficient_term_one_adjoint, term_pointwiseAdjoint, coefficient_adjoint, neg_smul]
  abel

end Adjoint

/-! ### Uniqueness of the adjoint -/

section FormalAdjoint

variable (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport)

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
