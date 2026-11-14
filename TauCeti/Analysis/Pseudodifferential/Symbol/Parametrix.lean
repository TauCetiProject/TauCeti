/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Symbol.FormalComposition

/-!
# The formal parametrix of an elliptic classical symbol

The formal composition `ClassicalSymbol.sharpTerms q p` of two expansions of homogeneous terms
(see `TauCeti.Analysis.Pseudodifferential.Symbol.FormalComposition`) is the expansion of the symbol
of the composition of two pseudodifferential operators with classical symbols. This file solves it
for an inverse: when the principal symbol `a_m` is invertible away from the zero frequency, the
equations "`q # a ∼ 1`" and "`a # q ∼ 1`" have unique solutions `q ∼ ∑_k q_{-m-k}`, given by
recursions starting from `q_{-m} = a_m⁻¹`. Through the composition theorem of the symbol calculus,
these are the expansions of a left and a right parametrix of `Op(a)`.

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
the symbol of the composed operators is the composition theorem of the symbol calculus: for a right
factor of compact spatial support, the composition symbol `TauCeti.ClassicalSymbol.sharp` has the
terms `sharpTerms` of the expansions of its factors (`TauCeti.ClassicalSymbol.term_sharp`). The
formal inverses here need not have compact spatial support.

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

namespace ClassicalSymbol

open HomogeneousSymbol

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
@[simp]
theorem sharpTerms_leftInverseTerms_zero :
    sharpTerms (a.leftInverseTerms ha) a.term 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree (by simp) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := HomogeneousSymbol.isElliptic_iff.1 ha x ξ hξ
    rw [coefficient_principal] at hinv
    simp [coefficient_leftInverseTerms_zero, coefficient_id hξ, coefficient_principal,
      hinv.inverse_comp_self]

/-- **The formal left inverse.** All terms of `sharpTerms (a.leftInverseTerms ha) a.term` after
the leading one vanish. -/
@[simp]
theorem sharpTerms_leftInverseTerms_succ (k : ℕ) :
    sharpTerms (a.leftInverseTerms ha) a.term (k + 1) = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := HomogeneousSymbol.isElliptic_iff.1 ha x ξ hξ
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
  have hinv := HomogeneousSymbol.isElliptic_iff.1 ha x ξ hξ
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
@[simp]
theorem sharpTerms_rightInverseTerms_zero :
    sharpTerms a.term (a.rightInverseTerms ha) 0 =
      (HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) W).castDegree (by simp) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := HomogeneousSymbol.isElliptic_iff.1 ha x ξ hξ
    rw [coefficient_principal] at hinv
    simp [coefficient_rightInverseTerms_zero, coefficient_id hξ, coefficient_principal,
      hinv.self_comp_inverse]

/-- **The formal right inverse.** All terms of `sharpTerms a.term (a.rightInverseTerms ha)` after
the leading one vanish. -/
@[simp]
theorem sharpTerms_rightInverseTerms_succ (k : ℕ) :
    sharpTerms a.term (a.rightInverseTerms ha) (k + 1) = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hinv := HomogeneousSymbol.isElliptic_iff.1 ha x ξ hξ
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
  have hinv := HomogeneousSymbol.isElliptic_iff.1 ha x ξ hξ
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
