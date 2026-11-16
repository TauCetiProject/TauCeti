/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.FormalComposition
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Composition and commutators of classical symbols

Let `a` be a classical symbol of order `m'` with values in `W →L[ℂ] U` and `b` a classical symbol
of order `m` with values in `V →L[ℂ] W` that vanishes for positions outside a compact set. This
file shows that their composition symbol `a # b` (`TauCeti.Symbol.sharp`), whose quantization is
`Op(a) ∘ Op(b)`, is again classical, of order `m' + m`, and computes its homogeneous terms. As a
consequence, the commutator `a # b - b # a` of two classical symbols with commuting principal
symbols is classical of order `m' + m - 1`, with an explicit leading term.

Each term `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of the composition expansion is a
classical symbol of order `m' + m - k` (`TauCeti.ClassicalSymbol.sharpTerm`), built from the
pointwise composition and the derivatives of classical symbols. Collecting the homogeneous terms of
the same degree, the term of degree `m' + m - j` of `a # b` is the sum over `k ≤ j` of the
homogeneous term of index `j - k` of `sharpTerm a b k`. Expanding each `sharpTerm a b k` into the
homogeneous terms of `a` and `b`, this is the formal composition
`TauCeti.ClassicalSymbol.sharpTerms a.term b.term` of the two expansions,

`(a # b)_{m'+m-k} = ∑_{i + j + r = k} ((-i)ʳ / r!) ∑_{|w| = r} ∂_ξ^w a_{m'-i} ∘ ∂_x^w b_{m-j}`.

In particular the principal symbol of `a # b` is `a_{m'} ∘ b_m`, and its next term is

`a_{m'} ∘ b_{m-1} + a_{m'-1} ∘ b_m - i ∑ⱼ ∂_{ξⱼ} a_{m'} ∘ ∂_{xⱼ} b_m`.

## Main results

* `TauCeti.ClassicalSymbol.sharp`: **the composition of classical symbols is classical**, with the
  terms `sharpTerms a.term b.term` (`TauCeti.ClassicalSymbol.term_sharp`), the formal composition
  of the expansions of `a` and `b`.
* `TauCeti.ClassicalSymbol.principal_sharp`: the principal symbol of `a # b` is `a_{m'} ∘ b_m`.
* `TauCeti.ClassicalSymbol.coefficient_term_one_sharp`: the term of degree `m' + m - 1` of `a # b`.
* `TauCeti.ClassicalSymbol.sharpCommutator`: the commutator symbol `a # b - b # a` of two classical
  symbols with values in `V →L[ℂ] V`, whose principal symbol is the pointwise commutator
  `[a_{m'}, b_m]` (`TauCeti.ClassicalSymbol.principal_sharpCommutator`).
* `TauCeti.ClassicalSymbol.exists_inclusion_eq_sharpCommutator`: **the commutator formula**. If
  the principal symbols commute, the commutator is a classical symbol of order `m' + m - 1` with
  principal symbol `-i ∑ⱼ (∂_{ξⱼ} a_{m'} ∂_{xⱼ} b_m - ∂_{ξⱼ} b_m ∂_{xⱼ} a_{m'})` plus the
  commutators `[a_{m'}, b_{m-1}] + [a_{m'-1}, b_m]`.

  Commuting principal symbols do not remove the two commutators of a principal with a subprincipal
  term.
* `TauCeti.ClassicalSymbol.exists_inclusion_eq_sharpCommutator_of_scalar`: for scalar symbols the
  commutator has order `m' + m - 1` and principal symbol `-i {a_{m'}, b_m}`, with the Poisson
  bracket `{p, q} = ∑ⱼ (∂_{ξⱼ} p ∂_{xⱼ} q - ∂_{xⱼ} p ∂_{ξⱼ} q)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8 and
  the remarks following it.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open Finset

namespace TauCeti

open HomogeneousSymbol

namespace ClassicalSymbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the composition expansion -/

section Term

/-- The term `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of the composition expansion, as a
classical symbol of order `m' + m - k`. It is defined by the recursion of
`TauCeti.Symbol.sharpTerm`, whose full symbol it has (`TauCeti.ClassicalSymbol.toSymbol_sharpTerm`):
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting from the
pointwise composition `sharpTerm a b 0 = a ∘ b`. -/
def sharpTerm : {m m' : ℝ} → ClassicalSymbol n W U m' → ClassicalSymbol n V W m → (k : ℕ) →
    ClassicalSymbol n V U (m' + m - k)
  | _, _, a, b, 0 => inclusion 0 (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

theorem sharpTerm_zero (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m) :
    a.sharpTerm b 0 = inclusion 0 (by simp) (a.comp b) := by
  rw [sharpTerm]

theorem sharpTerm_succ (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m) (k : ℕ) :
    a.sharpTerm b (k + 1) = inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, (frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

/-- The full symbol of the classical term `sharpTerm a b k` is the term `Symbol.sharpTerm` of the
composition expansion of the full symbols. -/
@[simp]
theorem toSymbol_sharpTerm (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m) (k : ℕ) :
    (a.sharpTerm b k).toSymbol = a.toSymbol.sharpTerm b.toSymbol k := by
  induction k generalizing m m' with
  | zero =>
    rw [sharpTerm_zero, Symbol.sharpTerm_zero]
    ext1
    simp
  | succ k ih =>
    rw [sharpTerm_succ, Symbol.sharpTerm_succ]
    ext1
    simp [ih]

/-- The homogeneous term of degree `m' + m - k - l` of `sharpTerm a b k` is
`∑_{i + j = l} HomogeneousSymbol.sharpTerm k a_{m'-i} b_{m-j}`. -/
theorem coefficient_term_sharpTerm (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
    (k l : ℕ) :
    ((a.sharpTerm b k).term l).coefficient =
      ∑ i ∈ range (l + 1),
        (HomogeneousSymbol.sharpTerm k (a.term i) (b.term (l - i))).coefficient := by
  induction k generalizing m' a b with
  | zero =>
    rw [ClassicalSymbol.sharpTerm_zero, term_inclusion_zero, coefficient_castDegree, term_comp]
    funext z
    simp [coefficient_compTerms]
  | succ k ih =>
    rw [ClassicalSymbol.sharpTerm_succ, term_inclusion_zero, coefficient_castDegree, term_smul,
      term_sum]
    funext z
    simp only [HomogeneousSymbol.coefficient_smul, HomogeneousSymbol.coefficient_sum,
      Pi.smul_apply, Finset.sum_apply, ih, HomogeneousSymbol.sharpTerm_succ, term_frequencyDeriv,
      term_spatialDeriv, sharpTerm_castDegree_left, coefficient_castDegree, smul_sum]
    exact Finset.sum_comm

end Term

/-! ### The homogeneous terms of a composition -/

section Terms

variable (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)

/-- The term `c_j` of the formal composition `sharpTerms a.term b.term` collects the terms of
degree `m' + m - j` of the classical symbols `sharpTerm a b k`, `k ≤ j`: it is
`∑_{k ≤ j} (sharpTerm a b k)_{j - k}`. -/
theorem coefficient_sharpTerms_eq_sum_term_sharpTerm (j : ℕ)
    (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms a.term b.term j).coefficient z =
      ∑ k ∈ range (j + 1), ((a.sharpTerm b k).term (j - k)).coefficient z := by
  rw [coefficient_sharpTerms]
  simp only [coefficient_term_sharpTerm, Finset.sum_apply]
  exact (sum_range_sum_range_tsub_eq_sum_ite
    (fun r i j ↦ (HomogeneousSymbol.sharpTerm r (a.term i) (b.term j)).coefficient z) j).symm

end Terms

/-! ### The composition of classical symbols -/

section Sharp

variable [CompleteSpace W] [CompleteSpace U]

/-- The remainder of the composition symbol of classical symbols after `N` terms has order
`m' + m - N`: it is the remainder of the composition expansion after `N` terms, plus the remainder
after `N - k` homogeneous terms of each term `sharpTerm a b k`, `k < N`. -/
private theorem exists_remainder_sharp (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
    (hb : b.toSymbol.HasCompactSpatialSupport) (χ : FrequencyCutoff (CoordinateSpace n))
    (N : ℕ) :
    ∃ r : Symbol n V U (m' + m - N), ∀ p, r.coefficient p =
      (a.toSymbol.sharp b.toSymbol hb).coefficient p -
        ∑ j ∈ range N, χ p.2 • (sharpTerms a.term b.term j).coefficient p := by
  -- The remainder of `sharpTerm a b k` after `N - k` terms has order `m' + m - N` for `k ≤ N`,
  -- and order `m' + m - k ≤ m' + m - N` for `k > N`.
  have hord (k : ℕ) : m' + m - k - ((N - k : ℕ) : ℝ) ≤ m' + m - N := by
    have : (N : ℝ) ≤ k + ((N - k : ℕ) : ℝ) := by exact_mod_cast le_add_tsub
    linarith
  refine ⟨a.toSymbol.sharpRemainder b.toSymbol hb N +
    ∑ k ∈ range N, Symbol.inclusion (hord k) ((a.sharpTerm b k).remainder χ (N - k)),
    fun p => ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Symbol.coefficient_inclusion,
    Symbol.coefficient_sharpRemainder, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    coefficient_remainder, toSymbol_sharpTerm, coefficient_sharpTerms_eq_sum_term_sharpTerm,
    Finset.smul_sum,
    Finset.sum_sub_distrib]
  -- Reindex the double sum over `k + i = j < N` by `k < N`, `i < N - k`.
  rw [Finset.sum_range_diag_flip N
    fun k i => χ p.2 • ((a.sharpTerm b k).term i).coefficient p]
  abel

/-- **The composition of classical symbols is classical.** For classical symbols `a` of order
`m'` and `b` of order `m`, with `b` of compact spatial support, the composition symbol `a # b`,
whose quantization is `Op(a) ∘ Op(b)`, is a classical symbol of order `m' + m`. Its homogeneous
terms are the formal composition `sharpTerms a.term b.term` of the expansions of `a` and `b`; the
term of degree `m' + m - j` is `∑_{k ≤ j} (sharpTerm a b k)_{j - k}`
(`TauCeti.ClassicalSymbol.coefficient_sharpTerms_eq_sum_term_sharpTerm`). -/
def sharp (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
    (hb : b.toSymbol.HasCompactSpatialSupport) : ClassicalSymbol n V U (m' + m) where
  toSymbol := a.toSymbol.sharp b.toSymbol hb
  term := sharpTerms a.term b.term
  exists_remainder' := ⟨default, exists_remainder_sharp a b hb default⟩

variable (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
  (hb : b.toSymbol.HasCompactSpatialSupport)

@[simp]
theorem toSymbol_sharp : (a.sharp b hb).toSymbol = a.toSymbol.sharp b.toSymbol hb :=
  (rfl)

@[simp]
theorem term_sharp (j : ℕ) : (a.sharp b hb).term j = sharpTerms a.term b.term j :=
  (rfl)

/-- **The principal symbol of a composition** is the composition of the principal symbols. -/
@[simp]
theorem principal_sharp : (a.sharp b hb).principal = a.principal.comp b.principal := by
  ext1
  funext z
  simp

/-- The term of degree `m' + m - 1` of the composition `a # b` of classical symbols is
`a_{m'} ∘ b_{m-1} + a_{m'-1} ∘ b_m - i ∑ⱼ ∂_{ξⱼ} a_{m'} ∘ ∂_{xⱼ} b_m`. -/
theorem coefficient_term_one_sharp (z : CoordinateSpace n × CoordinateSpace n) :
    ((a.sharp b hb).term 1).coefficient z =
      (a.principal.coefficient z).comp ((b.term 1).coefficient z) +
        ((a.term 1).coefficient z).comp (b.principal.coefficient z) -
        Complex.I • ∑ j, ((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).coefficient
          z).comp ((b.principal.spatialDeriv (EuclideanSpace.single j 1)).coefficient z) := by
  rw [term_sharp, coefficient_sharpTerms_one, principal_def, principal_def]
  simp

@[simp]
theorem zero_sharp : (0 : ClassicalSymbol n W U m').sharp b hb = 0 :=
  ext (Symbol.zero_sharp hb)

@[simp]
theorem sharp_zero (hb : (0 : ClassicalSymbol n V W m).toSymbol.HasCompactSpatialSupport) :
    a.sharp 0 hb = 0 :=
  ext (Symbol.sharp_zero _)

theorem add_sharp (a₁ a₂ : ClassicalSymbol n W U m') :
    (a₁ + a₂).sharp b hb = a₁.sharp b hb + a₂.sharp b hb :=
  ext (Symbol.add_sharp _ _ hb)

theorem sharp_add {b₁ b₂ : ClassicalSymbol n V W m} (hb₁ : b₁.toSymbol.HasCompactSpatialSupport)
    (hb₂ : b₂.toSymbol.HasCompactSpatialSupport) :
    a.sharp (b₁ + b₂) (hb₁.add hb₂) = a.sharp b₁ hb₁ + a.sharp b₂ hb₂ :=
  ext (Symbol.sharp_add _ hb₁ hb₂)

@[simp]
theorem smul_sharp (c : ℂ) : (c • a).sharp b hb = c • a.sharp b hb :=
  ext (Symbol.smul_sharp c _ hb)

@[simp]
theorem sharp_smul (c : ℂ) : a.sharp (c • b) (hb.smul c) = c • a.sharp b hb :=
  ext (Symbol.sharp_smul _ hb c)

@[simp]
theorem neg_sharp : (-a).sharp b hb = -a.sharp b hb :=
  ext (Symbol.neg_sharp _ hb)

@[simp]
theorem sharp_neg : a.sharp (-b) hb.neg = -a.sharp b hb :=
  ext (Symbol.sharp_neg _ hb)

theorem sub_sharp (a₁ a₂ : ClassicalSymbol n W U m') :
    (a₁ - a₂).sharp b hb = a₁.sharp b hb - a₂.sharp b hb :=
  ext (Symbol.sub_sharp _ _ hb)

theorem sharp_sub {b₁ b₂ : ClassicalSymbol n V W m} (hb₁ : b₁.toSymbol.HasCompactSpatialSupport)
    (hb₂ : b₂.toSymbol.HasCompactSpatialSupport) :
    a.sharp (b₁ - b₂) (hb₁.sub hb₂) = a.sharp b₁ hb₁ - a.sharp b₂ hb₂ :=
  ext (Symbol.sharp_sub _ hb₁ hb₂)

end Sharp

/-! ### Commutators -/

section Commutator

variable [CompleteSpace V]

/-- The commutator symbol `a # b - b # a` of classical symbols with values in `V →L[ℂ] V`, both
of compact spatial support: the symbol of the commutator `[Op(a), Op(b)]`, a classical symbol of
order `m' + m`. -/
def sharpCommutator (a : ClassicalSymbol n V V m') (b : ClassicalSymbol n V V m)
    (ha : a.toSymbol.HasCompactSpatialSupport) (hb : b.toSymbol.HasCompactSpatialSupport) :
    ClassicalSymbol n V V (m' + m) :=
  a.sharp b hb - inclusion 0 (by push_cast; ring) (b.sharp a ha)

variable (a : ClassicalSymbol n V V m') (b : ClassicalSymbol n V V m)
  (ha : a.toSymbol.HasCompactSpatialSupport) (hb : b.toSymbol.HasCompactSpatialSupport)

@[simp]
theorem coefficient_toSymbol_sharpCommutator (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpCommutator a b ha hb).toSymbol.coefficient z =
      (a.toSymbol.sharp b.toSymbol hb).coefficient z -
        (b.toSymbol.sharp a.toSymbol ha).coefficient z := by
  simp [sharpCommutator]

@[simp]
theorem coefficient_term_sharpCommutator (j : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    ((sharpCommutator a b ha hb).term j).coefficient z =
      ((a.sharp b hb).term j).coefficient z - ((b.sharp a ha).term j).coefficient z := by
  simp [sharpCommutator]

/-- The principal symbol of the commutator `a # b - b # a` is the pointwise commutator
`[a_{m'}, b_m]` of the principal symbols. -/
@[simp]
theorem principal_sharpCommutator :
    (sharpCommutator a b ha hb).principal =
      a.principal.comp b.principal - (b.principal.comp a.principal).castDegree (add_comm m m') := by
  ext1
  funext z
  simp

/-- **The commutator formula.** If the principal symbols of the classical symbols `a` and `b`
commute, their commutator `a # b - b # a` is a classical symbol of order `m' + m - 1`, with
principal symbol

`-i ∑ⱼ (∂_{ξⱼ} a_{m'} ∂_{xⱼ} b_m - ∂_{ξⱼ} b_m ∂_{xⱼ} a_{m'}) + [a_{m'}, b_{m-1}] + [a_{m'-1}, b_m]`.

The commutators of a principal with a subprincipal term remain, even though the principal terms
commute. -/
theorem exists_inclusion_eq_sharpCommutator
    (h : ∀ z, (a.principal.coefficient z).comp (b.principal.coefficient z) =
      (b.principal.coefficient z).comp (a.principal.coefficient z)) :
    ∃ c : ClassicalSymbol n V V (m' + m - 1), inclusion 1 (by simp) c = sharpCommutator a b ha hb ∧
      ∀ z, c.principal.coefficient z =
        -Complex.I • ∑ j,
          ((((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).coefficient z).comp
            ((b.principal.spatialDeriv (EuclideanSpace.single j 1)).coefficient z)) -
          (((b.principal.frequencyDeriv (EuclideanSpace.single j 1)).coefficient z).comp
            ((a.principal.spatialDeriv (EuclideanSpace.single j 1)).coefficient z))) +
        ((a.principal.coefficient z).comp ((b.term 1).coefficient z) -
          ((b.term 1).coefficient z).comp (a.principal.coefficient z)) +
        (((a.term 1).coefficient z).comp (b.principal.coefficient z) -
          (b.principal.coefficient z).comp ((a.term 1).coefficient z)) := by
  have h0 : (sharpCommutator a b ha hb).principal = 0 := by
    ext1
    funext z
    have hz := h z
    simp only [coefficient_principal] at hz
    simp [hz]
  obtain ⟨c, hc⟩ := (principal_eq_zero_iff_exists_inclusion _).1 h0
  refine ⟨c, hc, fun z => ?_⟩
  -- The principal symbol of `c` is the term of index `1` of the commutator.
  have hterm := congrArg (fun d : ClassicalSymbol n V V (m' + m) => (d.term (1 + 0)).coefficient z)
    hc
  simp only [term_inclusion_add, coefficient_castDegree] at hterm
  rw [coefficient_principal, hterm, coefficient_term_sharpCommutator, coefficient_term_one_sharp,
    coefficient_term_one_sharp, Finset.sum_sub_distrib, smul_sub, neg_smul, neg_smul]
  abel

/-- **The Poisson bracket formula.** For scalar classical symbols `a` and `b` of compact spatial
support, the commutator `a # b - b # a` is a classical symbol of order `m' + m - 1` whose principal
symbol is `-i {a_{m'}, b_m}`, with the Poisson bracket
`{p, q} = ∑ⱼ (∂_{ξⱼ} p ∂_{xⱼ} q - ∂_{xⱼ} p ∂_{ξⱼ} q)`. -/
theorem exists_inclusion_eq_sharpCommutator_of_scalar (a : ClassicalSymbol n ℂ ℂ m')
    (b : ClassicalSymbol n ℂ ℂ m) (ha : a.toSymbol.HasCompactSpatialSupport)
    (hb : b.toSymbol.HasCompactSpatialSupport) :
    ∃ c : ClassicalSymbol n ℂ ℂ (m' + m - 1), inclusion 1 (by simp) c = sharpCommutator a b ha hb ∧
      ∀ z, c.principal.coefficient z =
        -Complex.I • ∑ j,
          ((((a.principal.frequencyDeriv (EuclideanSpace.single j 1)).coefficient z).comp
            ((b.principal.spatialDeriv (EuclideanSpace.single j 1)).coefficient z)) -
          (((a.principal.spatialDeriv (EuclideanSpace.single j 1)).coefficient z).comp
            ((b.principal.frequencyDeriv (EuclideanSpace.single j 1)).coefficient z))) := by
  -- Continuous linear endomorphisms of `ℂ` commute.
  have hcomm (S T : ℂ →L[ℂ] ℂ) : S.comp T = T.comp S := by
    have h (f : ℂ →L[ℂ] ℂ) (x : ℂ) : f x = x * f 1 := by simpa using f.map_smul x 1
    ext1
    simp only [ContinuousLinearMap.comp_apply]
    rw [h S, h T (S 1), mul_comm]
  obtain ⟨c, hc, hσ⟩ := exists_inclusion_eq_sharpCommutator a b ha hb fun z => hcomm _ _
  refine ⟨c, hc, fun z => ?_⟩
  rw [hσ z, hcomm (a.principal.coefficient z) ((b.term 1).coefficient z),
    hcomm ((a.term 1).coefficient z) (b.principal.coefficient z), sub_self, sub_self, add_zero,
    add_zero]
  simp only [hcomm ((b.principal.frequencyDeriv _).coefficient z)]

end Commutator

end ClassicalSymbol

end TauCeti
