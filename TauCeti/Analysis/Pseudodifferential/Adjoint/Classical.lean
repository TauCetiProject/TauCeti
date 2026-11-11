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
built from the pointwise adjoint and the derivatives of classical symbols. Collecting the
homogeneous terms of the same degree, the term of degree `m - j` of `a*` is the sum over `k ≤ j`
of the homogeneous term of index `j - k` of `adjointTerm a k`
(`TauCeti.ClassicalSymbol.homogeneousAdjointTerms`).

## Main results

* `TauCeti.ClassicalSymbol.adjoint`: **the adjoint of a classical symbol is classical**, with the
  terms `TauCeti.ClassicalSymbol.homogeneousAdjointTerms`.
* `TauCeti.ClassicalSymbol.principal_adjoint`: the principal symbol of `a*` is `a_m†`.
* `TauCeti.ClassicalSymbol.coefficient_term_one_adjoint`: the term of degree `m - 1` of `a*`.
* `TauCeti.ClassicalSymbol.exists_inclusion_eq_adjoint_sub_pointwiseAdjoint`: `a* - a†` is a
  classical symbol of order `m - 1` with principal symbol `-i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`.
* `TauCeti.ClassicalSymbol.adjoint_principal_eq_of_forall_integral_inner_eq`: if `Op(a)` is
  formally self-adjoint, then `a* = a` and the principal symbol is pointwise self-adjoint.

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

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### The pointwise adjoint -/

section PointwiseAdjoint

/-- The pointwise adjoint `(x, ξ) ↦ a(x, ξ)†` of a classical symbol between Hilbert spaces: a
classical symbol of the same order, whose homogeneous terms are the pointwise adjoints of those of
`a`. Its quantization is not the formal adjoint of `Op(a)`; that is the quantization of
`TauCeti.ClassicalSymbol.adjoint`, of which `a†` is the leading term. -/
def pointwiseAdjoint (a : ClassicalSymbol n V W m) : ClassicalSymbol n W V m where
  toSymbol := a.toSymbol.map adjointRealCLM
  term j := (a.term j).adjoint
  exists_remainder' := ⟨default, fun N => ⟨(a.remainder default N).map adjointRealCLM, fun p => by
    simp [map_sub, map_sum, map_smul, adjointRealCLM_apply]⟩⟩

variable (a b : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_pointwiseAdjoint : a.pointwiseAdjoint.toSymbol = a.toSymbol.map adjointRealCLM :=
  (rfl)

theorem coefficient_toSymbol_pointwiseAdjoint (p : CoordinateSpace n × CoordinateSpace n) :
    a.pointwiseAdjoint.toSymbol.coefficient p =
      ContinuousLinearMap.adjoint (a.toSymbol.coefficient p) := by
  simp [adjointRealCLM_apply]

@[simp]
theorem term_pointwiseAdjoint (j : ℕ) : a.pointwiseAdjoint.term j = (a.term j).adjoint :=
  (rfl)

/-- The principal symbol of `a†` is the pointwise adjoint of the principal symbol of `a`. -/
@[simp]
theorem principal_pointwiseAdjoint : a.pointwiseAdjoint.principal = a.principal.adjoint := by
  ext1
  funext z
  simp

@[simp]
theorem pointwiseAdjoint_pointwiseAdjoint : a.pointwiseAdjoint.pointwiseAdjoint = a :=
  ext <| Symbol.ext <| funext fun p => by simp [adjointRealCLM_apply]

@[simp]
theorem pointwiseAdjoint_add : (a + b).pointwiseAdjoint = a.pointwiseAdjoint + b.pointwiseAdjoint :=
  ext <| Symbol.ext <| funext fun p => by simp [adjointRealCLM_apply]

/-- The pointwise adjoint is conjugate linear. -/
@[simp]
theorem pointwiseAdjoint_smul (c : ℂ) :
    (c • a).pointwiseAdjoint = (starRingEnd ℂ c) • a.pointwiseAdjoint :=
  ext <| Symbol.ext <| funext fun p => by
    simpa [adjointRealCLM_apply] using map_smulₛₗ ContinuousLinearMap.adjoint c _

end PointwiseAdjoint

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

/-! ### The homogeneous terms of the adjoint -/

section Terms

/-- The homogeneous terms of the adjoint symbol `a*` of a classical symbol: the term of degree
`m - j` collects the terms of degree `m - j` of the classical symbols `adjointTerm a k`, `k ≤ j`,
which is the term of index `j - k` of `adjointTerm a k`. -/
def homogeneousAdjointTerms (a : ClassicalSymbol n V W m) (j : ℕ) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (m - j) :=
  ∑ k ∈ range (j + 1),
    if h : k ≤ j then ((a.adjointTerm k).term (j - k)).castDegree (by rw [Nat.cast_sub h]; ring)
    else 0

variable (a : ClassicalSymbol n V W m)

/-- The coefficient of the term of degree `m - j` of `a*` is `∑_{k ≤ j} (adjointTerm a k)_{j - k}`.
-/
theorem coefficient_homogeneousAdjointTerms (j : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (homogeneousAdjointTerms a j).coefficient z =
      ∑ k ∈ range (j + 1), ((a.adjointTerm k).term (j - k)).coefficient z := by
  rw [homogeneousAdjointTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [Nat.le_of_lt_succ (Finset.mem_range.1 hk)]

/-- The leading term of `a*` is the pointwise adjoint `a_m†` of the leading term of `a`. -/
@[simp]
theorem coefficient_homogeneousAdjointTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (homogeneousAdjointTerms a 0).coefficient z =
      ContinuousLinearMap.adjoint ((a.term 0).coefficient z) := by
  simp [coefficient_homogeneousAdjointTerms, adjointTerm_zero]

/-- The term of degree `m - 1` of `a*` is `a_{m-1}† - i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a_m)†`. -/
theorem coefficient_homogeneousAdjointTerms_one (z : CoordinateSpace n × CoordinateSpace n) :
    (homogeneousAdjointTerms a 1).coefficient z =
      ContinuousLinearMap.adjoint ((a.term 1).coefficient z) -
        Complex.I • ∑ j, ContinuousLinearMap.adjoint
          ((((a.term 0).frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
            (EuclideanSpace.single j 1)).coefficient z) := by
  simp [coefficient_homogeneousAdjointTerms, Finset.sum_range_succ, adjointTerm_zero,
    adjointTerm_succ, sub_eq_add_neg]

end Terms

/-! ### The adjoint of a classical symbol -/

section Adjoint

/-- The remainder of the adjoint symbol of a classical symbol after `N` terms has order `m - N`:
it is the remainder of the adjoint expansion after `N` terms, plus the remainder after `N - k`
homogeneous terms of each term `adjointTerm a k`, `k < N`. -/
private theorem exists_remainder_adjoint (a : ClassicalSymbol n V W m)
    (ha : a.toSymbol.HasCompactSpatialSupport) (χ : FrequencyCutoff (CoordinateSpace n))
    (N : ℕ) :
    ∃ r : Symbol n W V (m - N), ∀ p, r.coefficient p =
      (a.toSymbol.adjoint ha).coefficient p -
        ∑ j ∈ range N, χ p.2 • (homogeneousAdjointTerms a j).coefficient p := by
  -- The remainder of `adjointTerm a k` after `N - k` terms has order `m - N` for `k ≤ N`, and
  -- order `m - k ≤ m - N` for `k > N`.
  have hord (k : ℕ) : m - k - ((N - k : ℕ) : ℝ) ≤ m - N := by
    have : (N : ℝ) ≤ k + ((N - k : ℕ) : ℝ) := by exact_mod_cast le_add_tsub
    linarith
  refine ⟨a.toSymbol.adjointRemainder ha N +
    ∑ k ∈ range N, Symbol.inclusion (hord k) ((a.adjointTerm k).remainder χ (N - k)),
    fun p => ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Symbol.coefficient_inclusion,
    Symbol.coefficient_adjointRemainder, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    coefficient_remainder, toSymbol_adjointTerm, coefficient_homogeneousAdjointTerms,
    Finset.smul_sum, Finset.sum_sub_distrib]
  -- Reindex the double sum over `k + i = j < N` by `k < N`, `i < N - k`.
  rw [Finset.sum_range_diag_flip N
    fun k i => χ p.2 • ((a.adjointTerm k).term i).coefficient p]
  abel

/-- **The adjoint of a classical symbol is classical.** For a classical symbol `a` of order `m`
with compact spatial support, the adjoint symbol `a*`, whose quantization is the formal adjoint of
`Op(a)` (`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`), is a classical symbol of
order `m`. Its homogeneous term of degree `m - j` is `∑_{k ≤ j} (adjointTerm a k)_{j - k}`
(`TauCeti.ClassicalSymbol.homogeneousAdjointTerms`). -/
def adjoint (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport) :
    ClassicalSymbol n W V m where
  toSymbol := a.toSymbol.adjoint ha
  term := homogeneousAdjointTerms a
  exists_remainder' := ⟨default, exists_remainder_adjoint a ha default⟩

variable (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport)

@[simp]
theorem toSymbol_adjoint : (a.adjoint ha).toSymbol = a.toSymbol.adjoint ha :=
  (rfl)

@[simp]
theorem term_adjoint (j : ℕ) : (a.adjoint ha).term j = homogeneousAdjointTerms a j :=
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
  rw [term_adjoint, coefficient_homogeneousAdjointTerms_one, principal_def]
  simp

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

/-! ### Formally self-adjoint quantizations -/

section SelfAdjoint

variable (a : ClassicalSymbol n V V m) (ha : a.toSymbol.HasCompactSpatialSupport)

/-- If the quantization of a classical symbol `a` is formally self-adjoint on compactly supported
Schwartz functions, `∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(a) v⟫`, then `a` is its own adjoint symbol. -/
theorem adjoint_eq_self_of_forall_integral_inner_eq
    (h : ∀ (u v : 𝓢(CoordinateSpace n, V)), HasCompactSupport u → HasCompactSupport v →
      ∫ x, inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient u x) (v x) =
        ∫ x, inner ℂ (u x) (quantizeSchwartzValue a.toSymbol.coefficient v x)) :
    a.adjoint ha = a :=
  ext <| Symbol.ext (Symbol.coefficient_eq_adjoint_of_forall_integral_inner_eq ha h).symm

include ha in
/-- **The principal symbol of a formally self-adjoint operator is self-adjoint.** If the
quantization of a classical symbol `a` is formally self-adjoint on compactly supported Schwartz
functions, then its principal symbol `a_m(x, ξ)` is a self-adjoint operator at every position and
frequency. -/
theorem adjoint_principal_eq_of_forall_integral_inner_eq
    (h : ∀ (u v : 𝓢(CoordinateSpace n, V)), HasCompactSupport u → HasCompactSupport v →
      ∫ x, inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient u x) (v x) =
        ∫ x, inner ℂ (u x) (quantizeSchwartzValue a.toSymbol.coefficient v x)) :
    a.principal.adjoint = a.principal := by
  rw [← principal_adjoint a ha, adjoint_eq_self_of_forall_integral_inner_eq a ha h]

end SelfAdjoint

end ClassicalSymbol

end TauCeti
