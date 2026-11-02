/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Ring.Ordering.Basic
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Order.Zorn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Extending field preorderings to orderings

A proper preordering on a field extends to a total ordering. The proof adjoins
one element to a preordering and then applies Zorn's lemma. In particular, it
preserves the prescribed positive elements, as required when ordering a field
extension of an already ordered field.

## References

This is the classical preordering extension argument; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 3](https://www.math.uni-konstanz.de/algebra/WS0910/Notes03.pdf),
Lemma 2.1 and Corollaries 3.2 and 3.4. The Lean construction uses Mathlib's
`Subsemiring.IsPreordering` and `Subsemiring.IsOrdering` interfaces.
-/

public section

variable {K : Type*} [Field K]

namespace Subsemiring.IsPreordering

variable {P : Subsemiring K}

/-- Adjoin an element to a field preordering using expressions `u + a * v`. -/
private def adjoin (hP : P.IsPreordering) (a : K) : Subsemiring K where
  carrier := {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v}
  zero_mem' := ⟨0, P.zero_mem, 0, P.zero_mem, by simp⟩
  one_mem' := ⟨1, P.one_mem, 0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
    exact ⟨u + w, P.add_mem hu hw, v + z, P.add_mem hv hz, by ring⟩
  mul_mem' := by
    rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
    exact ⟨u * w + a ^ 2 * (v * z),
      P.add_mem (P.mul_mem hu hw) (P.mul_mem (hP.pow_two_mem a) (P.mul_mem hv hz)),
      u * z + v * w, P.add_mem (P.mul_mem hu hz) (P.mul_mem hv hw), by ring⟩

/-- Adjoining an element whose negative is absent preserves properness. -/
private theorem isPreordering_adjoin (hP : P.IsPreordering) {a : K} (ha : -a ∉ P) :
    (hP.adjoin a).IsPreordering where
  mem_of_isSquare := by
    rintro x ⟨y, rfl⟩
    exact ⟨y * y, hP.mul_self_mem y, 0, P.zero_mem, by simp⟩
  neg_one_notMem := by
    rintro ⟨u, hu, v, hv, heq⟩
    by_cases hv0 : v = 0
    · apply hP.neg_one_notMem
      have heq' : -1 = u := by simpa only [hv0, mul_zero, add_zero] using heq
      exact heq' ▸ hu
    · apply ha
      have hmem : (1 + u) * v⁻¹ ∈ P :=
        P.mul_mem (P.add_mem P.one_mem hu) (hP.inv_mem hv)
      have hval : -a = (1 + u) * v⁻¹ := by
        field_simp
        linear_combination heq
      rwa [← hval] at hmem

private theorem le_adjoin (hP : P.IsPreordering) (a : K) : P ≤ hP.adjoin a :=
  fun x hx => ⟨x, hx, 0, P.zero_mem, by simp⟩

private theorem self_mem_adjoin (hP : P.IsPreordering) (a : K) : a ∈ hP.adjoin a :=
  ⟨0, P.zero_mem, 1, P.one_mem, by simp⟩

private def chainUnion (c : Set (Subsemiring K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : Subsemiring K := by
  have := hne.to_subtype
  have hd : Directed (· ≤ ·) (fun P : c => P.val) := hc.directed
  exact (⨆ P : c, P.val).copy {x | ∃ P ∈ c, x ∈ P} (by
    rw [Subsemiring.coe_iSup_of_directed hd]
    ext x
    simp)

private theorem le_chainUnion (c : Set (Subsemiring K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {P : Subsemiring K} (hP : P ∈ c) : P ≤ chainUnion c hc hne :=
  fun _ hx => ⟨P, hP, hx⟩

private theorem isPreordering_chainUnion (c : Set (Subsemiring K))
    (hpre : ∀ P ∈ c, P.IsPreordering) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    (chainUnion c hc hne).IsPreordering where
  mem_of_isSquare := by
    intro x hx
    obtain ⟨P, hP⟩ := hne
    exact ⟨P, hP, (hpre P hP).mem_of_isSquare hx⟩
  neg_one_notMem := by
    rintro ⟨P, hPc, hP⟩
    exact (hpre P hPc).neg_one_notMem hP

/-- A field preordering extends to an ordering, retaining every prescribed sign. -/
theorem exists_le_isOrdering (hP : P.IsPreordering) :
    ∃ Q : Subsemiring K, P ≤ Q ∧ Q.IsOrdering := by
  obtain ⟨Q, hPQ, hQ, hmax⟩ := zorn_le_nonempty₀ {Q : Subsemiring K | Q.IsPreordering}
    (fun c hpre hc y hy =>
      ⟨chainUnion c hc ⟨y, hy⟩, isPreordering_chainUnion c hpre hc ⟨y, hy⟩,
        fun z hz => le_chainUnion c hc ⟨y, hy⟩ hz⟩) P hP
  have htotal (a : K) : a ∈ Q ∨ -a ∈ Q := by
    by_cases ha : -a ∈ Q
    · exact Or.inr ha
    · exact Or.inl ((hmax (hQ.isPreordering_adjoin ha) (hQ.le_adjoin a))
        (hQ.self_mem_adjoin a))
  refine ⟨Q, hPQ, hQ.isOrdering_iff.mpr fun a b hab => ?_⟩
  by_cases ha : a ∈ Q
  · exact Or.inl ha
  by_cases hb : b ∈ Q
  · exact Or.inr hb
  have hna := (htotal a).resolve_left ha
  have hnb := (htotal b).resolve_left hb
  have hprod : a * b ∈ Q := by simpa using Q.mul_mem hna hnb
  rcases mul_eq_zero.mp (hQ.isPointed.eq_zero_of_mem_of_neg_mem hprod hab) with h | h
  · exact Or.inl (h ▸ Q.zero_mem)
  · exact Or.inr (h ▸ Q.zero_mem)

/-- An element whose negative is absent can be made nonnegative in an extending ordering. -/
theorem exists_le_isOrdering_mem (hP : P.IsPreordering) {a : K} (ha : -a ∉ P) :
    ∃ Q : Subsemiring K, P ≤ Q ∧ Q.IsOrdering ∧ a ∈ Q := by
  obtain ⟨Q, hQ, horder⟩ := (hP.isPreordering_adjoin ha).exists_le_isOrdering
  exact ⟨Q, (hP.le_adjoin a).trans hQ, horder, hQ (hP.self_mem_adjoin a)⟩

/-- Order a field while respecting all signs in a specified preordering. -/
theorem exists_linearOrder (hP : P.IsPreordering) :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K ∧ ∀ x ∈ P, 0 ≤ x := by
  classical
  obtain ⟨Q, hPQ, hQ⟩ := hP.exists_le_isOrdering
  let := LinearOrder.ofAddSubmonoid hQ.isPreordering.isPointed hQ.isSpanning
  have : IsOrderedRing K := IsOrderedRing.ofSubsemiring hQ.isPreordering.isPointed
  refine ⟨inferInstance, inferInstance, fun x hx => ?_⟩
  change x - 0 ∈ Q
  simpa only [sub_zero] using hPQ hx

end Subsemiring.IsPreordering
