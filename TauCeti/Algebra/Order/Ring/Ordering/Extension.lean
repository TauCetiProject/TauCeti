/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Order.Ring.Ordering.Basic
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

/-- Adjoining an element whose negative is absent preserves properness. -/
theorem isPreordering_adjoin (hP : P.IsPreordering) {a : K} (ha : -a ∉ P) :
    (hP.adjoin a).IsPreordering where
  mem_of_isSquare := by
    rintro x ⟨y, rfl⟩
    rw [mem_adjoin]
    exact ⟨y * y, hP.mul_self_mem y, 0, P.zero_mem, by simp⟩
  neg_one_notMem := by
    intro hx
    rw [mem_adjoin] at hx
    obtain ⟨u, hu, v, hv, heq⟩ := hx
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

/-- A field preordering extends to an ordering, retaining every prescribed sign. -/
theorem exists_le_isOrdering (hP : P.IsPreordering) :
    ∃ Q : Subsemiring K, P ≤ Q ∧ Q.IsOrdering := by
  obtain ⟨Q, hPQ, hQ, hmax⟩ := zorn_le_nonempty₀ {Q : Subsemiring K | Q.IsPreordering}
    (fun c hpre hc y hy => by
      let : Nonempty c := ⟨⟨y, hy⟩⟩
      refine ⟨⨆ P : c, P.val, ?_, fun z hz => le_iSup (fun P : c => P.val) ⟨z, hz⟩⟩
      exact Subsemiring.IsPreordering.iSup (fun P : c => hpre P.property) hc.directed) P hP
  have htotal (a : K) : a ∈ Q ∨ -a ∈ Q := by
    by_cases ha : -a ∈ Q
    · exact Or.inr ha
    · exact Or.inl ((hmax (hQ.isPreordering_adjoin ha) (hQ.le_adjoin a))
        (hQ.self_mem_adjoin a))
  exact ⟨Q, hPQ, hQ.isOrdering_of_isSpanning (Subsemiring.isSpanning_def.mpr htotal)⟩

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
  -- The order just constructed defines `a ≤ b` by `b - a ∈ Q`; expose it before `sub_zero`.
  change x - 0 ∈ Q
  simpa only [sub_zero] using hPQ hx

end Subsemiring.IsPreordering
