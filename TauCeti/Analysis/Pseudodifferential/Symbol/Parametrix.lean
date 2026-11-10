/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Elliptic

/-!
# The formal parametrix of an elliptic classical symbol

The symbol of the composition of two pseudodifferential operators with classical symbols
`b ∼ ∑ᵢ b_{m'-i}` and `a ∼ ∑ⱼ a_{m-j}` has the expansion
`b # a ∼ ∑_α ((1/i)^|α| / α!) ∂_ξ^α b ∂_x^α a`, whose homogeneous term of degree `m' + m - k`
collects `∂_ξ^α b_{m'-i} ∘ ∂_x^α a_{m-j}` over `i + j + |α| = k`. This file sets up this formal
composition of expansions and solves it for an inverse: when the principal symbol `a_m` is
invertible away from the zero frequency, the equations "`q # a ∼ 1`" and "`a # q ∼ 1`" have
unique solutions `q ∼ ∑_k q_{-m-k}`, given by recursions starting from `q_{-m} = a_m⁻¹`.
Through the composition theorem of the symbol calculus, these are the expansions of a left and a
right parametrix of `Op(a)`.

* `TauCeti.HomogeneousSymbol.sharpTerm k b a`: the homogeneous symbol
  `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of degree `m' + m - k`, summed over the words `w` of
  length `k` in the coordinate directions (`HomogeneousSymbol.coefficient_sharpTerm`). Summing over
  words rather than multi-indices, `1 / k!` replaces `1 / α!`.
* `TauCeti.ClassicalSymbol.sharpTerms q p`: the homogeneous terms
  `cₖ = ∑_{i + j + r = k} sharpTerm r qᵢ pⱼ` of the formal composition of two expansions. Its
  leading term is the pointwise composition `q₀ ∘ p₀` (`ClassicalSymbol.sharpTerms_zero`); unlike
  the terms `ClassicalSymbol.compTerms` of the pointwise composition, the lower order terms involve
  derivatives of the factors.
* `TauCeti.ClassicalSymbol.leftInverseTerms` and `TauCeti.ClassicalSymbol.rightInverseTerms`: for
  an elliptic classical symbol `a` of order `m`, the formal left and right inverses, sequences of
  homogeneous terms of degrees `-m - k` whose formal composition with the terms of `a` is the
  identity (`ClassicalSymbol.sharpTerms_leftInverseTerms_zero`,
  `ClassicalSymbol.sharpTerms_leftInverseTerms_succ` and their right-handed versions). They are the
  only such sequences (`ClassicalSymbol.eq_leftInverseTerms_iff`,
  `ClassicalSymbol.eq_rightInverseTerms_iff`).
* `TauCeti.ClassicalSymbol.exists_sharpTerms_eq_left` and
  `TauCeti.ClassicalSymbol.exists_sharpTerms_eq_right`: by Borel summation of these terms, an
  elliptic classical symbol of order `m` has classical formal left and right inverses of order
  `-m` with principal symbol `a_m⁻¹`, unique modulo smoothing symbols
  (`ClassicalSymbol.isSmoothing_toSymbol_sub_of_sharpTerms_left`,
  `ClassicalSymbol.isSmoothing_toSymbol_sub_of_sharpTerms_right`).

Everything here is a statement about homogeneous terms. That `sharpTerms` gives the expansion of
the symbol of the composed operators is the composition theorem of the symbol calculus, and the
formal inverses become parametrices of `Op(a)` through it.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (2.5)–(2.7) and §4.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter I, §5.
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

/-- At a nonzero frequency, a spatial derivative along a word of the spatial derivative
`∂_{x_j} a` is the spatial derivative of `a` along the word extended by `j`. -/
private theorem coordinateDeriv_spatialDeriv (w : List (Fin n)) (j : Fin n)
    {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    coordinateDeriv w
        (fun y ↦ (a.spatialDeriv (EuclideanSpace.single j 1)).coefficient (y, ξ)) x =
      coordinateDeriv (w ++ [j]) (fun y ↦ a.coefficient (y, ξ)) x := by
  rw [coordinateDeriv_append]
  congr 1
  funext y
  simp [coefficient_spatialDeriv _ _ hξ, coordinateDeriv_cons]

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
      coordinateDeriv_spatialDeriv _ _ _ hξ, Finset.smul_sum, smul_smul]
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

section Inverse

variable [CompleteSpace V] (a : ClassicalSymbol n V W m) (ha : a.principal.IsElliptic)

/-- The homogeneous terms `q_{-m-k}` of a formal left inverse of an elliptic classical symbol `a`:
`q_{-m} = a_m⁻¹` and, for `k ≥ 0`, `q_{-m-k-1} = -(∑' sharpTerm (qᵢ) (aⱼ)) ∘ a_m⁻¹`, where the sum
runs over the terms of `c_{k+1}` in `sharpTerms q a.term` other than `q_{-m-k-1} ∘ a_m`. -/
def leftInverseTerms : (k : ℕ) →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (-m - k)
  | 0 => (a.principal.inverse ha).castDegree (by simp)
  | k + 1 => -(((∑ i ∈ (range (k + 1)).attach, ∑ j ∈ range (k + 2),
      if h : (i : ℕ) + j ≤ k + 1 then
        (sharpTerm (k + 1 - (i + j)) (leftInverseTerms i) (a.term j)).castDegree
          (m' := -m + m - (k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; ring)
      else 0).comp (a.principal.inverse ha)).castDegree (by push_cast; ring))
  decreasing_by exact Finset.mem_range.1 i.2

@[simp]
theorem coefficient_leftInverseTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (a.leftInverseTerms ha 0).coefficient z = (a.principal.coefficient z).inverse := by
  rw [leftInverseTerms]
  simp

/-- The recursion defining the formal left inverse. -/
theorem coefficient_leftInverseTerms_succ (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (a.leftInverseTerms ha (k + 1)).coefficient z =
      -((∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2),
        if i + j ≤ k + 1 then (sharpTerm (k + 1 - (i + j)) (a.leftInverseTerms ha i)
          (a.term j)).coefficient z else 0) ∘L (a.principal.coefficient z).inverse) := by
  rw [leftInverseTerms]
  simp only [coefficient_neg, coefficient_castDegree, coefficient_comp, coefficient_inverse,
    Pi.neg_apply, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  congr 2
  rw [← Finset.sum_attach (range (k + 1)) fun i ↦ ∑ j ∈ range (k + 2),
    if i + j ≤ k + 1 then
      (sharpTerm (k + 1 - (i + j)) (a.leftInverseTerms ha i) (a.term j)).coefficient z
    else 0]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

/-- **The formal left inverse.** The leading term of `sharpTerms (a.leftInverseTerms ha) a.term`
is the identity. -/
theorem sharpTerms_leftInverseTerms_zero :
    sharpTerms (a.leftInverseTerms ha) a.term 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree (by simp) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x ξ hξ
    rw [coefficient_principal] at hinv
    simp [coefficient_leftInverseTerms_zero, coefficient_id hξ, coefficient_principal,
      hinv.inverse_comp_self]

/-- **The formal left inverse.** All terms of `sharpTerms (a.leftInverseTerms ha) a.term` after
the leading one vanish. -/
theorem sharpTerms_leftInverseTerms_succ (k : ℕ) :
    sharpTerms (a.leftInverseTerms ha) a.term (k + 1) = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x ξ hξ
    rw [coefficient_principal] at hinv
    rw [coefficient_sharpTerms_succ, coefficient_leftInverseTerms_succ,
      ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    simp [coefficient_principal, hinv.inverse_comp_self]

/-- **Uniqueness of the formal left inverse.** A sequence of homogeneous terms `q` is the formal
left inverse of `a` exactly when the formal composition `sharpTerms q a.term` is the identity. -/
theorem eq_leftInverseTerms_iff
    {q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (-m - i)} :
    q = a.leftInverseTerms ha ↔
      sharpTerms q a.term 0 =
          (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree (by simp) ∧
        ∀ k, sharpTerms q a.term (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ ↦ funext fun k ↦ ?_⟩
  · rintro rfl
    exact ⟨a.sharpTerms_leftInverseTerms_zero ha, a.sharpTerms_leftInverseTerms_succ ha⟩
  induction k using Nat.strong_induction_on with | _ k ih
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  have hinv := isElliptic_iff.1 ha x ξ hξ
  rw [coefficient_principal] at hinv
  -- In both cases `q k ∘ a₀` is determined by the earlier terms; compose with `a₀⁻¹`.
  rw [← ContinuousLinearMap.comp_id ((q k).coefficient (x, ξ)), ← hinv.self_comp_inverse,
    ← ContinuousLinearMap.comp_assoc]
  cases k with
  | zero =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) h0
    simp only [coefficient_sharpTerms_zero, coefficient_castDegree, coefficient_id hξ] at h
    simp [h, coefficient_leftInverseTerms_zero, coefficient_principal]
  | succ k =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) (hsucc k)
    simp only [coefficient_sharpTerms_succ, coefficient_zero, Pi.zero_apply] at h
    rw [eq_neg_of_add_eq_zero_left h, coefficient_leftInverseTerms_succ, coefficient_principal]
    rw [ContinuousLinearMap.neg_comp]
    congr 2
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [ih i (by simpa using Finset.mem_range.1 hi)]

/-- The homogeneous terms `q_{-m-k}` of a formal right inverse of an elliptic classical symbol
`a`: `q_{-m} = a_m⁻¹` and, for `k ≥ 0`, `q_{-m-k-1} = -a_m⁻¹ ∘ ∑' sharpTerm (aᵢ) (qⱼ)`, where the
sum runs over the terms of `c_{k+1}` in `sharpTerms a.term q` other than `a_m ∘ q_{-m-k-1}`. -/
def rightInverseTerms : (k : ℕ) →
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (-m - k)
  | 0 => (a.principal.inverse ha).castDegree (by simp)
  | k + 1 => -((a.principal.inverse ha).comp (∑ j ∈ (range (k + 1)).attach, ∑ i ∈ range (k + 2),
      if h : i + (j : ℕ) ≤ k + 1 then
        (sharpTerm (k + 1 - (i + j)) (a.term i) (rightInverseTerms j)).castDegree
          (m' := m + -m - (k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; ring)
      else 0)).castDegree (by push_cast; ring)
  decreasing_by exact Finset.mem_range.1 j.2

@[simp]
theorem coefficient_rightInverseTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (a.rightInverseTerms ha 0).coefficient z = (a.principal.coefficient z).inverse := by
  rw [rightInverseTerms]
  simp

/-- The recursion defining the formal right inverse. -/
theorem coefficient_rightInverseTerms_succ (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (a.rightInverseTerms ha (k + 1)).coefficient z =
      -((a.principal.coefficient z).inverse ∘L ∑ j ∈ range (k + 1), ∑ i ∈ range (k + 2),
        if i + j ≤ k + 1 then (sharpTerm (k + 1 - (i + j)) (a.term i)
          (a.rightInverseTerms ha j)).coefficient z else 0) := by
  rw [rightInverseTerms]
  simp only [coefficient_neg, coefficient_castDegree, coefficient_comp, coefficient_inverse,
    Pi.neg_apply, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  congr 2
  rw [← Finset.sum_attach (range (k + 1)) fun j ↦ ∑ i ∈ range (k + 2),
    if i + j ≤ k + 1 then
      (sharpTerm (k + 1 - (i + j)) (a.term i) (a.rightInverseTerms ha j)).coefficient z
    else 0]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs <;> simp

/-- **The formal right inverse.** The leading term of `sharpTerms a.term (a.rightInverseTerms ha)`
is the identity. -/
theorem sharpTerms_rightInverseTerms_zero :
    sharpTerms a.term (a.rightInverseTerms ha) 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) W).castDegree (by simp) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x ξ hξ
    rw [coefficient_principal] at hinv
    simp [coefficient_rightInverseTerms_zero, coefficient_id hξ, coefficient_principal,
      hinv.self_comp_inverse]

/-- **The formal right inverse.** All terms of `sharpTerms a.term (a.rightInverseTerms ha)` after
the leading one vanish. -/
theorem sharpTerms_rightInverseTerms_succ (k : ℕ) :
    sharpTerms a.term (a.rightInverseTerms ha) (k + 1) = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x ξ hξ
    rw [coefficient_principal] at hinv
    rw [coefficient_sharpTerms_succ', coefficient_rightInverseTerms_succ,
      ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc]
    simp [coefficient_principal, hinv.self_comp_inverse]

/-- **Uniqueness of the formal right inverse.** A sequence of homogeneous terms `q` is the formal
right inverse of `a` exactly when the formal composition `sharpTerms a.term q` is the identity. -/
theorem eq_rightInverseTerms_iff
    {q : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (-m - j)} :
    q = a.rightInverseTerms ha ↔
      sharpTerms a.term q 0 =
          (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) W).castDegree (by simp) ∧
        ∀ k, sharpTerms a.term q (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ ↦ funext fun k ↦ ?_⟩
  · rintro rfl
    exact ⟨a.sharpTerms_rightInverseTerms_zero ha, a.sharpTerms_rightInverseTerms_succ ha⟩
  induction k using Nat.strong_induction_on with | _ k ih
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  have hinv := isElliptic_iff.1 ha x ξ hξ
  rw [coefficient_principal] at hinv
  -- In both cases `a₀ ∘ q k` is determined by the earlier terms; compose with `a₀⁻¹`.
  rw [← ContinuousLinearMap.id_comp ((q k).coefficient (x, ξ)), ← hinv.inverse_comp_self,
    ContinuousLinearMap.comp_assoc]
  cases k with
  | zero =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) h0
    simp only [coefficient_sharpTerms_zero, coefficient_castDegree, coefficient_id hξ] at h
    simp [h, coefficient_rightInverseTerms_zero, coefficient_principal]
  | succ k =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) (hsucc k)
    simp only [coefficient_sharpTerms_succ', coefficient_zero, Pi.zero_apply] at h
    rw [eq_neg_of_add_eq_zero_left h, coefficient_rightInverseTerms_succ, coefficient_principal,
      ContinuousLinearMap.comp_neg]
    congr 2
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [ih j (by simpa using Finset.mem_range.1 hj)]

/-! ### Classical symbols with the formal inverse as expansion -/

/-- **Formal left parametrix.** An elliptic classical symbol `a` of order `m` has a classical
left inverse of order `-m` up to formal composition: a classical symbol `b` whose principal
symbol is `a_m⁻¹` and whose expansion composes formally with that of `a` to the identity. -/
theorem exists_sharpTerms_eq_left :
    ∃ b : ClassicalSymbol n W V (-m), b.principal = a.principal.inverse ha ∧
      sharpTerms b.term a.term 0 =
          (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree (by simp) ∧
        ∀ k, sharpTerms b.term a.term (k + 1) = 0 := by
  obtain ⟨b, hb⟩ := exists_term_eq (a.leftInverseTerms ha)
  refine ⟨b, ext_of_ne_zero fun x ξ _ ↦ ?_, (a.eq_leftInverseTerms_iff ha).1 hb⟩
  rw [coefficient_principal, hb, coefficient_leftInverseTerms_zero, coefficient_inverse]

/-- **Formal right parametrix.** An elliptic classical symbol `a` of order `m` has a classical
right inverse of order `-m` up to formal composition: a classical symbol `b` whose principal
symbol is `a_m⁻¹` and whose expansion composes formally with that of `a` to the identity. -/
theorem exists_sharpTerms_eq_right :
    ∃ b : ClassicalSymbol n W V (-m), b.principal = a.principal.inverse ha ∧
      sharpTerms a.term b.term 0 =
          (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) W).castDegree (by simp) ∧
        ∀ k, sharpTerms a.term b.term (k + 1) = 0 := by
  obtain ⟨b, hb⟩ := exists_term_eq (a.rightInverseTerms ha)
  refine ⟨b, ext_of_ne_zero fun x ξ _ ↦ ?_, (a.eq_rightInverseTerms_iff ha).1 hb⟩
  rw [coefficient_principal, hb, coefficient_rightInverseTerms_zero, coefficient_inverse]

include ha in
/-- Two classical symbols whose expansions are formal left inverses of the expansion of an
elliptic classical symbol differ by a smoothing symbol. -/
theorem isSmoothing_toSymbol_sub_of_sharpTerms_left {b b' : ClassicalSymbol n W V (-m)}
    (hb₀ : sharpTerms b.term a.term 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree (by simp))
    (hb : ∀ k, sharpTerms b.term a.term (k + 1) = 0)
    (hb'₀ : sharpTerms b'.term a.term 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree (by simp))
    (hb' : ∀ k, sharpTerms b'.term a.term (k + 1) = 0) :
    (b.toSymbol - b'.toSymbol).IsSmoothing := by
  rw [isSmoothing_toSymbol_sub_iff, (a.eq_leftInverseTerms_iff ha).2 ⟨hb₀, hb⟩,
    (a.eq_leftInverseTerms_iff ha).2 ⟨hb'₀, hb'⟩]

include ha in
/-- Two classical symbols whose expansions are formal right inverses of the expansion of an
elliptic classical symbol differ by a smoothing symbol. -/
theorem isSmoothing_toSymbol_sub_of_sharpTerms_right {b b' : ClassicalSymbol n W V (-m)}
    (hb₀ : sharpTerms a.term b.term 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) W).castDegree (by simp))
    (hb : ∀ k, sharpTerms a.term b.term (k + 1) = 0)
    (hb'₀ : sharpTerms a.term b'.term 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) W).castDegree (by simp))
    (hb' : ∀ k, sharpTerms a.term b'.term (k + 1) = 0) :
    (b.toSymbol - b'.toSymbol).IsSmoothing := by
  rw [isSmoothing_toSymbol_sub_iff, (a.eq_rightInverseTerms_iff ha).2 ⟨hb₀, hb⟩,
    (a.eq_rightInverseTerms_iff ha).2 ⟨hb'₀, hb'⟩]

end Inverse

end ClassicalSymbol

end TauCeti
