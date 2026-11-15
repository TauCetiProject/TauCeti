/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# The formal composition of homogeneous symbol expansions

The symbol of the composition of two pseudodifferential operators with classical symbols
`b ∼ ∑ᵢ b_{m'-i}` and `a ∼ ∑ⱼ a_{m-j}` has the expansion
`b # a ∼ ∑_α ((1/i)^|α| / α!) ∂_ξ^α b ∂_x^α a`, whose homogeneous term of degree `m' + m - k`
collects `∂_ξ^α b_{m'-i} ∘ ∂_x^α a_{m-j}` over `i + j + |α| = k`. This file sets up this formal
composition of expansions.

* `TauCeti.HomogeneousSymbol.sharpTerm k b a`: the homogeneous symbol
  `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of degree `m' + m - k`, summed over the words `w` of
  length `k` in the coordinate directions (`HomogeneousSymbol.coefficient_sharpTerm`). Summing over
  words rather than multi-indices, `1 / k!` replaces `1 / α!`.
* `TauCeti.ClassicalSymbol.sharpTerms q p`: the homogeneous terms
  `cₖ = ∑_{i + j + r = k} sharpTerm r qᵢ pⱼ` of the formal composition of two expansions. Its
  leading term is the pointwise composition `q₀ ∘ p₀` (`ClassicalSymbol.sharpTerms_zero`); unlike
  the terms `ClassicalSymbol.compTerms` of the pointwise composition, the lower order terms involve
  derivatives of the factors.

Everything here is a statement about homogeneous terms. That `sharpTerms` gives the expansion of
the symbol of the composed operators is the composition theorem of the symbol calculus: for
classical symbols `a` and `b`, with `b` of compact spatial support, the composition symbol
`TauCeti.ClassicalSymbol.sharp`, whose quantization is `Op(a) ∘ Op(b)`, is classical with the terms
`sharpTerms a.term b.term` (`TauCeti.ClassicalSymbol.term_sharp`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (2.5)–(2.7).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Finset Filter Topology

namespace TauCeti

variable {n : ℕ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m : ℝ}

namespace HomogeneousSymbol

/-- The homogeneous symbol `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of degree `m' + m - k`,
the part of the formal composition `b # a` with `k` derivatives on each factor. It is defined by
the recursion `sharpTerm 0 b a = b ∘ a` and
`sharpTerm (k + 1) b a = (-i / (k + 1)) ∑ⱼ sharpTerm k (∂_{ξⱼ} b) (∂_{xⱼ} a)`; the closed form is
`TauCeti.HomogeneousSymbol.coefficient_sharpTerm`. -/
def sharpTerm : (k : ℕ) → {m' : ℝ} →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U m' →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V U (m' + m - k)
  | 0, _, b, a => (b.comp a).castDegree (by simp)
  | k + 1, _, b, a => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (sharpTerm k (b.frequencyDeriv (EuclideanSpace.single j 1))
        (a.spatialDeriv (EuclideanSpace.single j 1))).castDegree (by push_cast; ring)

variable {m' : ℝ} (b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U m')
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

theorem sharpTerm_zero : sharpTerm 0 b a = (b.comp a).castDegree (by simp) :=
  (rfl)

theorem sharpTerm_succ (k : ℕ) :
    sharpTerm (k + 1) b a = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (sharpTerm k (b.frequencyDeriv (EuclideanSpace.single j 1))
        (a.spatialDeriv (EuclideanSpace.single j 1))).castDegree (by push_cast; ring) :=
  (rfl)

/-- Transporting the degree of the left factor transports the degree of every term of the formal
composition. -/
@[simp]
theorem sharpTerm_castDegree_left {m'' : ℝ} (h : m' = m'') (k : ℕ) :
    sharpTerm k (b.castDegree h) a = (sharpTerm k b a).castDegree (by rw [h]) := by
  subst h
  rw [castDegree_rfl, castDegree_rfl]

/-- Transporting the degree of the right factor transports the degree of every term of the formal
composition. -/
@[simp]
theorem sharpTerm_castDegree_right {m'' : ℝ} (h : m = m'') (k : ℕ) :
    sharpTerm k b (a.castDegree h) = (sharpTerm k b a).castDegree (by rw [h]) := by
  subst h
  rw [castDegree_rfl, castDegree_rfl]

@[simp]
theorem coefficient_sharpTerm_zero (p : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerm 0 b a).coefficient p = b.coefficient p ∘L a.coefficient p := by
  simp [sharpTerm_zero]

/-- At a nonzero frequency, a frequency derivative along a word of the frequency derivative
`∂_{ξ_j} b` is the frequency derivative of `b` along the word extended by `j`. -/
private theorem coordinateDeriv_frequencyDeriv (w : List (Fin n)) (j : Fin n)
    {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    coordinateDeriv w
        (fun η ↦ (b.frequencyDeriv (EuclideanSpace.single j 1)).coefficient (x, η)) ξ =
      coordinateDeriv (w ++ [j]) (fun η ↦ b.coefficient (x, η)) ξ := by
  rw [coordinateDeriv_append]
  refine (EventuallyEq.coordinateDeriv ?_ w).eq_of_nhds
  filter_upwards [isOpen_compl_singleton.mem_nhds hξ] with η hη
  simp [coefficient_frequencyDeriv _ _ hη, coordinateDeriv_cons]

/-- A spatial derivative along a word of the spatial derivative
`∂_{x_j} a` is the spatial derivative of `a` along the word extended by `j`. -/
private theorem coordinateDeriv_spatialDeriv (w : List (Fin n)) (j : Fin n)
    {x ξ : CoordinateSpace n} :
    coordinateDeriv w
        (fun y ↦ (a.spatialDeriv (EuclideanSpace.single j 1)).coefficient (y, ξ)) x =
      coordinateDeriv (w ++ [j]) (fun y ↦ a.coefficient (y, ξ)) x := by
  rw [coordinateDeriv_append]
  congr 1
  funext y
  simp [coefficient_spatialDeriv _ _, coordinateDeriv_cons]

/-- **Closed form of the composition terms.** At a nonzero frequency, `sharpTerm k b a` is
`((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a`, the sum over the words `w` of length `k` in the
coordinate directions. -/
theorem coefficient_sharpTerm (k : ℕ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (sharpTerm k b a).coefficient (x, ξ) =
      ((-Complex.I) ^ k / k.factorial : ℂ) • ∑ w : Fin k → Fin n,
        coordinateDeriv (List.ofFn w) (fun η ↦ b.coefficient (x, η)) ξ ∘L
          coordinateDeriv (List.ofFn w) (fun y ↦ a.coefficient (y, ξ)) x := by
  induction k generalizing m' b a with
  | zero => simp
  | succ k ih =>
    rw [sharpTerm_succ, coefficient_smul, Pi.smul_apply, coefficient_sum, Finset.sum_apply]
    simp only [coefficient_castDegree, ih, coordinateDeriv_frequencyDeriv _ _ _ hξ,
      coordinateDeriv_spatialDeriv _ _ _, Finset.smul_sum, smul_smul]
    rw [← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end HomogeneousSymbol

namespace ClassicalSymbol

open HomogeneousSymbol

section SharpTerms

variable {m' : ℝ}

/-- The homogeneous terms `cₖ = ∑_{i + j + r = k} ((-i)ʳ / r!) ∑_{|w| = r} ∂_ξ^w qᵢ ∘ ∂_x^w pⱼ`
of the formal composition `q # p` of two expansions, with the terms `qᵢ` of degree `m' - i` and
`pⱼ` of degree `m - j`. The term `cₖ` has degree `m' + m - k`. -/
def sharpTerms
    (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (k : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V U (m' + m - k) :=
  ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
    if h : i + j ≤ k then
      (sharpTerm (k - (i + j)) (q i) (p j)).castDegree (by rw [Nat.cast_sub h]; push_cast; ring)
    else 0

variable (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
  (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))

/-- The coefficient of `cₖ` is `∑_{i + j ≤ k} sharpTerm (k - i - j) qᵢ pⱼ`. -/
theorem coefficient_sharpTerms (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p k).coefficient z =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
        if i + j ≤ k then (sharpTerm (k - (i + j)) (q i) (p j)).coefficient z else 0 := by
  simp only [sharpTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

@[simp]
theorem coefficient_sharpTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p 0).coefficient z = (q 0).coefficient z ∘L (p 0).coefficient z := by
  simp [coefficient_sharpTerms]

/-- The term `c₁ = q₀ ∘ p₁ + q₁ ∘ p₀ - i ∑ⱼ ∂_{ξⱼ} q₀ ∘ ∂_{xⱼ} p₀` of the formal composition. -/
theorem coefficient_sharpTerms_one (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p 1).coefficient z =
      (q 0).coefficient z ∘L (p 1).coefficient z + (q 1).coefficient z ∘L (p 0).coefficient z -
        Complex.I • ∑ j, ((q 0).frequencyDeriv (EuclideanSpace.single j 1)).coefficient z ∘L
          ((p 0).spatialDeriv (EuclideanSpace.single j 1)).coefficient z := by
  simp [coefficient_sharpTerms, Finset.sum_range_succ, sharpTerm_succ, sub_eq_add_neg]
  abel

/-- The leading term of the formal composition is the composition of the leading terms. -/
theorem sharpTerms_zero : sharpTerms q p 0 = compTerms q p 0 := by
  ext1
  funext z
  simp

/-- The term `c_{k+1}` of the formal composition is `q_{k+1} ∘ p₀` plus terms involving only
`q₀, …, qₖ`. -/
theorem coefficient_sharpTerms_succ (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p (k + 1)).coefficient z =
      (q (k + 1)).coefficient z ∘L (p 0).coefficient z +
        ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2),
          if i + j ≤ k + 1 then (sharpTerm (k + 1 - (i + j)) (q i) (p j)).coefficient z
          else 0 := by
  rw [coefficient_sharpTerms, Finset.sum_range_succ, add_comm, Finset.sum_range_succ']
  congr 1
  rw [Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    coefficient_congr_index (fun r ↦ sharpTerm r (q (k + 1)) (p 0)) (show k + 1 - (k + 1 + 0) = 0
      by omega), coefficient_sharpTerm_zero]

/-- The term `c_{k+1}` of the formal composition is `q₀ ∘ p_{k+1}` plus terms involving only
`p₀, …, pₖ`. -/
theorem coefficient_sharpTerms_succ' (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p (k + 1)).coefficient z =
      (q 0).coefficient z ∘L (p (k + 1)).coefficient z +
        ∑ j ∈ range (k + 1), ∑ i ∈ range (k + 2),
          if i + j ≤ k + 1 then (sharpTerm (k + 1 - (i + j)) (q i) (p j)).coefficient z
          else 0 := by
  rw [coefficient_sharpTerms, Finset.sum_comm, Finset.sum_range_succ, add_comm,
    Finset.sum_range_succ']
  congr 1
  rw [Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    coefficient_congr_index (fun r ↦ sharpTerm r (q 0) (p (k + 1))) (show k + 1 - (0 + (k + 1)) = 0
      by omega), coefficient_sharpTerm_zero]

end SharpTerms

end ClassicalSymbol

end TauCeti
