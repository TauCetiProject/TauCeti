/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Elliptic
public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.FormalComposition
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parametrix

/-!
# The formal parametrix of an elliptic classical symbol on an open set

Let `U ⊆ ℝⁿ` be open and let `a ∼ ∑ⱼ a_{m-j}` be a classical symbol of order `m` on `U`
(`TauCeti.LocalClassicalSymbol`) whose principal symbol `a_m` is invertible at every position of
`U` and every nonzero frequency. This file solves the equations "`q # a ∼ 1`" and "`a # q ∼ 1`" for
the formal composition of expansions on `U` (`TauCeti.LocalClassicalSymbol.sharpTerms`): they have
unique solutions `q ∼ ∑ₖ q_{-m-k}`, given by recursions starting from `q_{-m} = a_m⁻¹`, and by
Borel summation on `U` they are the expansions of classical symbols of order `-m` on `U`. These are
the symbols of the local left and right parametrices of an elliptic classical pseudodifferential
operator read in a chart, whose terms need not extend to `ℝⁿ`; on `ℝⁿ` this is
`TauCeti/Analysis/Pseudodifferential/Symbol/Parametrix.lean`.

* `TauCeti.LocalClassicalSymbol.leftInverseTerms` and
  `TauCeti.LocalClassicalSymbol.rightInverseTerms`: for an elliptic classical symbol `a` of order
  `m` on `U`, the formal left and right inverses, sequences of homogeneous symbols of degrees
  `-m - k` on `U` whose formal composition with the terms of `a` is the identity. They are the only
  such sequences (`TauCeti.LocalClassicalSymbol.eq_leftInverseTerms_iff`,
  `TauCeti.LocalClassicalSymbol.eq_rightInverseTerms_iff`).
* `TauCeti.LocalClassicalSymbol.exists_sharpTerms_eq_left` and
  `TauCeti.LocalClassicalSymbol.exists_sharpTerms_eq_right`: an elliptic classical symbol of order
  `m` on `U` has classical formal left and right inverses of order `-m` on `U`, with principal
  symbol `a_m⁻¹`, unique modulo smoothing symbols on `U`
  (`TauCeti.LocalClassicalSymbol.isSmoothing_toLocalSymbol_sub_of_sharpTerms_left`,
  `TauCeti.LocalClassicalSymbol.isSmoothing_toLocalSymbol_sub_of_sharpTerms_right`).
* `TauCeti.LocalClassicalSymbol.leftInverseTerms_restrict` and
  `TauCeti.ClassicalSymbol.leftInverseTerms_restrict`, with their right-handed versions: the formal
  inverses commute with restriction to smaller open sets, and on `U` the formal inverses of a
  classical symbol on `ℝⁿ` are the restrictions of its formal inverses on `ℝⁿ`. So formal inverses
  computed in two charts agree on their overlap.

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

variable {n : ℕ} {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

namespace LocalClassicalSymbol

open LocalHomogeneousSymbol

section Inverse

variable [CompleteSpace V] (a : LocalClassicalSymbol U V W m) (ha : a.IsElliptic)

/-- The homogeneous terms `q_{-m-k}` on `U` of a formal left inverse of an elliptic classical
symbol `a` on `U`: `q_{-m} = a_m⁻¹` and, for `k ≥ 0`,
`q_{-m-k-1} = -(∑' sharpTerm (qᵢ) (aⱼ)) ∘ a_m⁻¹`, where the sum runs over the terms of `c_{k+1}`
in `sharpTerms q a.term` other than `q_{-m-k-1} ∘ a_m`. -/
def leftInverseTerms : (k : ℕ) → LocalHomogeneousSymbol U W V (-m - k)
  | 0 => (a.principal.inverse (isElliptic_def.1 ha)).castDegree (by simp)
  | k + 1 => -(((∑ i ∈ (range (k + 1)).attach, ∑ j ∈ range (k + 2),
      if h : (i : ℕ) + j ≤ k + 1 then
        (sharpTerm (k + 1 - (i + j)) (leftInverseTerms i) (a.term j)).castDegree
          (m' := -m + m - (k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; ring)
      else 0).comp (a.principal.inverse (isElliptic_def.1 ha))).castDegree (by push_cast; ring))
  decreasing_by exact Finset.mem_range.1 i.property

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
    Pi.neg_apply, LocalHomogeneousSymbol.coefficient_sum, Finset.sum_apply]
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
    sharpTerms (a.leftInverseTerms ha) a.term 0 = (id U V).castDegree (by simp) :=
  ext_of_mem fun x hx ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x hx ξ hξ
    rw [coefficient_principal] at hinv
    simp [coefficient_id hx hξ, coefficient_principal, hinv.inverse_comp_self]

/-- **The formal left inverse.** All terms of `sharpTerms (a.leftInverseTerms ha) a.term` after
the leading one vanish. -/
@[simp]
theorem sharpTerms_leftInverseTerms_succ (k : ℕ) :
    sharpTerms (a.leftInverseTerms ha) a.term (k + 1) = 0 :=
  ext_of_mem fun x hx ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x hx ξ hξ
    rw [coefficient_principal] at hinv
    rw [coefficient_sharpTerms_succ, coefficient_leftInverseTerms_succ,
      ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    simp [coefficient_principal, hinv.inverse_comp_self]

/-- **Uniqueness of the formal left inverse.** A sequence of homogeneous terms `q` on `U` is the
formal left inverse of `a` exactly when the formal composition `sharpTerms q a.term` is the
identity. -/
theorem eq_leftInverseTerms_iff {q : (i : ℕ) → LocalHomogeneousSymbol U W V (-m - i)} :
    q = a.leftInverseTerms ha ↔
      sharpTerms q a.term 0 = (id U V).castDegree (by simp) ∧
        ∀ k, sharpTerms q a.term (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ ↦ funext fun k ↦ ?_⟩
  · rintro rfl
    exact ⟨a.sharpTerms_leftInverseTerms_zero ha, a.sharpTerms_leftInverseTerms_succ ha⟩
  induction k using Nat.strong_induction_on with | _ k ih
  refine ext_of_mem fun x hx ξ hξ ↦ ?_
  have hinv := isElliptic_iff.1 ha x hx ξ hξ
  rw [coefficient_principal] at hinv
  -- In both cases `q k ∘ a₀` is determined by the earlier terms; compose with `a₀⁻¹`.
  rw [← ContinuousLinearMap.comp_id ((q k).coefficient (x, ξ)), ← hinv.self_comp_inverse,
    ← ContinuousLinearMap.comp_assoc]
  cases k with
  | zero =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) h0
    simp only [coefficient_sharpTerms_zero, coefficient_castDegree, coefficient_id hx hξ] at h
    simp [h, coefficient_principal]
  | succ k =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) (hsucc k)
    simp only [coefficient_sharpTerms_succ, coefficient_zero, Pi.zero_apply] at h
    rw [eq_neg_of_add_eq_zero_left h, coefficient_leftInverseTerms_succ, coefficient_principal,
      ContinuousLinearMap.neg_comp]
    congr 2
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [ih i (by simpa using Finset.mem_range.1 hi)]

/-- The homogeneous terms `q_{-m-k}` on `U` of a formal right inverse of an elliptic classical
symbol `a` on `U`: `q_{-m} = a_m⁻¹` and, for `k ≥ 0`,
`q_{-m-k-1} = -a_m⁻¹ ∘ ∑' sharpTerm (aᵢ) (qⱼ)`, where the sum runs over the terms of `c_{k+1}`
in `sharpTerms a.term q` other than `a_m ∘ q_{-m-k-1}`. -/
def rightInverseTerms : (k : ℕ) → LocalHomogeneousSymbol U W V (-m - k)
  | 0 => (a.principal.inverse (isElliptic_def.1 ha)).castDegree (by simp)
  | k + 1 => -((a.principal.inverse (isElliptic_def.1 ha)).comp
      (∑ j ∈ (range (k + 1)).attach, ∑ i ∈ range (k + 2),
      if h : i + (j : ℕ) ≤ k + 1 then
        (sharpTerm (k + 1 - (i + j)) (a.term i) (rightInverseTerms j)).castDegree
          (m' := m + -m - (k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; ring)
      else 0)).castDegree (by push_cast; ring)
  decreasing_by exact Finset.mem_range.1 j.property

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
    Pi.neg_apply, LocalHomogeneousSymbol.coefficient_sum, Finset.sum_apply]
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
    sharpTerms a.term (a.rightInverseTerms ha) 0 = (id U W).castDegree (by simp) :=
  ext_of_mem fun x hx ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x hx ξ hξ
    rw [coefficient_principal] at hinv
    simp [coefficient_id hx hξ, coefficient_principal, hinv.self_comp_inverse]

/-- **The formal right inverse.** All terms of `sharpTerms a.term (a.rightInverseTerms ha)` after
the leading one vanish. -/
@[simp]
theorem sharpTerms_rightInverseTerms_succ (k : ℕ) :
    sharpTerms a.term (a.rightInverseTerms ha) (k + 1) = 0 :=
  ext_of_mem fun x hx ξ hξ ↦ by
    have hinv := isElliptic_iff.1 ha x hx ξ hξ
    rw [coefficient_principal] at hinv
    rw [coefficient_sharpTerms_succ', coefficient_rightInverseTerms_succ,
      ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc]
    simp [coefficient_principal, hinv.self_comp_inverse]

/-- **Uniqueness of the formal right inverse.** A sequence of homogeneous terms `q` on `U` is the
formal right inverse of `a` exactly when the formal composition `sharpTerms a.term q` is the
identity. -/
theorem eq_rightInverseTerms_iff {q : (j : ℕ) → LocalHomogeneousSymbol U W V (-m - j)} :
    q = a.rightInverseTerms ha ↔
      sharpTerms a.term q 0 = (id U W).castDegree (by simp) ∧
        ∀ k, sharpTerms a.term q (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ ↦ funext fun k ↦ ?_⟩
  · rintro rfl
    exact ⟨a.sharpTerms_rightInverseTerms_zero ha, a.sharpTerms_rightInverseTerms_succ ha⟩
  induction k using Nat.strong_induction_on with | _ k ih
  refine ext_of_mem fun x hx ξ hξ ↦ ?_
  have hinv := isElliptic_iff.1 ha x hx ξ hξ
  rw [coefficient_principal] at hinv
  -- In both cases `a₀ ∘ q k` is determined by the earlier terms; compose with `a₀⁻¹`.
  rw [← ContinuousLinearMap.id_comp ((q k).coefficient (x, ξ)), ← hinv.inverse_comp_self,
    ContinuousLinearMap.comp_assoc]
  cases k with
  | zero =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) h0
    simp only [coefficient_sharpTerms_zero, coefficient_castDegree, coefficient_id hx hξ] at h
    simp [h, coefficient_principal]
  | succ k =>
    have h := congrArg (fun c ↦ c.coefficient (x, ξ)) (hsucc k)
    simp only [coefficient_sharpTerms_succ', coefficient_zero, Pi.zero_apply] at h
    rw [eq_neg_of_add_eq_zero_left h, coefficient_rightInverseTerms_succ, coefficient_principal,
      ContinuousLinearMap.comp_neg]
    congr 2
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [ih j (by simpa using Finset.mem_range.1 hj)]

/-! ### Classical symbols on `U` with the formal inverse as expansion -/

/-- **Formal left parametrix on an open set.** An elliptic classical symbol `a` of order `m` on
`U` has a classical left inverse of order `-m` on `U` up to formal composition: a classical symbol
`b` on `U` whose principal symbol is `a_m⁻¹` and whose expansion composes formally with that of
`a` to the identity. -/
theorem exists_sharpTerms_eq_left :
    ∃ b : LocalClassicalSymbol U W V (-m),
      b.principal = a.principal.inverse (isElliptic_def.1 ha) ∧
      sharpTerms b.term a.term 0 = (id U V).castDegree (by simp) ∧
        ∀ k, sharpTerms b.term a.term (k + 1) = 0 := by
  obtain ⟨b, hb⟩ := exists_term_eq (a.leftInverseTerms ha)
  refine ⟨b, ext_of_mem fun x _ ξ _ ↦ ?_, (a.eq_leftInverseTerms_iff ha).1 hb⟩
  rw [coefficient_principal, hb, coefficient_leftInverseTerms_zero, coefficient_inverse]

/-- **Formal right parametrix on an open set.** An elliptic classical symbol `a` of order `m` on
`U` has a classical right inverse of order `-m` on `U` up to formal composition: a classical
symbol `b` on `U` whose principal symbol is `a_m⁻¹` and whose expansion composes formally with
that of `a` to the identity. -/
theorem exists_sharpTerms_eq_right :
    ∃ b : LocalClassicalSymbol U W V (-m),
      b.principal = a.principal.inverse (isElliptic_def.1 ha) ∧
      sharpTerms a.term b.term 0 = (id U W).castDegree (by simp) ∧
        ∀ k, sharpTerms a.term b.term (k + 1) = 0 := by
  obtain ⟨b, hb⟩ := exists_term_eq (a.rightInverseTerms ha)
  refine ⟨b, ext_of_mem fun x _ ξ _ ↦ ?_, (a.eq_rightInverseTerms_iff ha).1 hb⟩
  rw [coefficient_principal, hb, coefficient_rightInverseTerms_zero, coefficient_inverse]

include ha in
/-- Two classical symbols on `U` whose expansions are formal left inverses of the expansion of an
elliptic classical symbol on `U` differ by a smoothing symbol on `U`. -/
theorem isSmoothing_toLocalSymbol_sub_of_sharpTerms_left {b b' : LocalClassicalSymbol U W V (-m)}
    (hb₀ : sharpTerms b.term a.term 0 = (id U V).castDegree (by simp))
    (hb : ∀ k, sharpTerms b.term a.term (k + 1) = 0)
    (hb'₀ : sharpTerms b'.term a.term 0 = (id U V).castDegree (by simp))
    (hb' : ∀ k, sharpTerms b'.term a.term (k + 1) = 0) :
    (b.toLocalSymbol - b'.toLocalSymbol).IsSmoothing := by
  rw [isSmoothing_toLocalSymbol_sub_iff, (a.eq_leftInverseTerms_iff ha).2 ⟨hb₀, hb⟩,
    (a.eq_leftInverseTerms_iff ha).2 ⟨hb'₀, hb'⟩]

include ha in
/-- Two classical symbols on `U` whose expansions are formal right inverses of the expansion of an
elliptic classical symbol on `U` differ by a smoothing symbol on `U`. -/
theorem isSmoothing_toLocalSymbol_sub_of_sharpTerms_right {b b' : LocalClassicalSymbol U W V (-m)}
    (hb₀ : sharpTerms a.term b.term 0 = (id U W).castDegree (by simp))
    (hb : ∀ k, sharpTerms a.term b.term (k + 1) = 0)
    (hb'₀ : sharpTerms a.term b'.term 0 = (id U W).castDegree (by simp))
    (hb' : ∀ k, sharpTerms a.term b'.term (k + 1) = 0) :
    (b.toLocalSymbol - b'.toLocalSymbol).IsSmoothing := by
  rw [isSmoothing_toLocalSymbol_sub_iff, (a.eq_rightInverseTerms_iff ha).2 ⟨hb₀, hb⟩,
    (a.eq_rightInverseTerms_iff ha).2 ⟨hb'₀, hb'⟩]

/-! ### Restriction to smaller open sets -/

/-- The formal left inverse commutes with restriction to a smaller open set. -/
theorem leftInverseTerms_restrict (h : U' ≤ U) :
    (restrict h a).leftInverseTerms (ha.restrict h) =
      fun k ↦ LocalHomogeneousSymbol.restrict h (a.leftInverseTerms ha k) := by
  have ht : (restrict h a).term = fun j ↦ LocalHomogeneousSymbol.restrict h (a.term j) :=
    funext (term_restrict h a)
  refine (((restrict h a).eq_leftInverseTerms_iff (ha.restrict h)).2 ⟨?_, fun k ↦ ?_⟩).symm
  · rw [ht, ← restrict_sharpTerms, sharpTerms_leftInverseTerms_zero, restrict_castDegree,
      restrict_id]
  · rw [ht, ← restrict_sharpTerms, sharpTerms_leftInverseTerms_succ, map_zero]

/-- The formal right inverse commutes with restriction to a smaller open set. -/
theorem rightInverseTerms_restrict (h : U' ≤ U) :
    (restrict h a).rightInverseTerms (ha.restrict h) =
      fun k ↦ LocalHomogeneousSymbol.restrict h (a.rightInverseTerms ha k) := by
  have ht : (restrict h a).term = fun j ↦ LocalHomogeneousSymbol.restrict h (a.term j) :=
    funext (term_restrict h a)
  refine (((restrict h a).eq_rightInverseTerms_iff (ha.restrict h)).2 ⟨?_, fun k ↦ ?_⟩).symm
  · rw [ht, ← restrict_sharpTerms, sharpTerms_rightInverseTerms_zero, restrict_castDegree,
      restrict_id]
  · rw [ht, ← restrict_sharpTerms, sharpTerms_rightInverseTerms_succ, map_zero]

end Inverse

end LocalClassicalSymbol

namespace ClassicalSymbol

variable [CompleteSpace V] (a : ClassicalSymbol n V W m) (ha : a.IsElliptic)

/-- On an open set, the formal left inverse of the restriction of an elliptic classical symbol on
`ℝⁿ` is the restriction of its formal left inverse. -/
theorem leftInverseTerms_restrict :
    (restrict U a).leftInverseTerms ha.restrict =
      fun k ↦ HomogeneousSymbol.restrict U (a.leftInverseTerms (isElliptic_def.1 ha) k) := by
  have ht : (restrict U a).term = fun j ↦ HomogeneousSymbol.restrict U (a.term j) :=
    funext (term_restrict a)
  refine (((restrict U a).eq_leftInverseTerms_iff ha.restrict).2 ⟨?_, fun k ↦ ?_⟩).symm
  · rw [ht, ← restrict_sharpTerms, sharpTerms_leftInverseTerms_zero,
      HomogeneousSymbol.restrict_castDegree, HomogeneousSymbol.restrict_id]
  · rw [ht, ← restrict_sharpTerms, sharpTerms_leftInverseTerms_succ, map_zero]

/-- On an open set, the formal right inverse of the restriction of an elliptic classical symbol on
`ℝⁿ` is the restriction of its formal right inverse. -/
theorem rightInverseTerms_restrict :
    (restrict U a).rightInverseTerms ha.restrict =
      fun k ↦ HomogeneousSymbol.restrict U (a.rightInverseTerms (isElliptic_def.1 ha) k) := by
  have ht : (restrict U a).term = fun j ↦ HomogeneousSymbol.restrict U (a.term j) :=
    funext (term_restrict a)
  refine (((restrict U a).eq_rightInverseTerms_iff ha.restrict).2 ⟨?_, fun k ↦ ?_⟩).symm
  · rw [ht, ← restrict_sharpTerms, sharpTerms_rightInverseTerms_zero,
      HomogeneousSymbol.restrict_castDegree, HomogeneousSymbol.restrict_id]
  · rw [ht, ← restrict_sharpTerms, sharpTerms_rightInverseTerms_succ, map_zero]

end ClassicalSymbol

end TauCeti
