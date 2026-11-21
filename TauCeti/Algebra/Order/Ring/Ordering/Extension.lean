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
  mem_of_isSquare hx := hP.le_adjoin a (hP.mem_of_isSquare hx)
  neg_one_notMem := by
    intro hx
    obtain ⟨u, hu, v, hv, heq⟩ := (hP.mem_adjoin a _).1 hx
    rcases eq_or_ne v 0 with rfl | hv0
    · exact hP.neg_one_notMem (by simpa [heq] using hu)
    · have hval : -a = (1 + u) * v⁻¹ := by
        field_simp
        linear_combination heq
      exact ha (hval ▸ P.mul_mem (P.add_mem P.one_mem hu) (hP.inv_mem hv))

/-- Every preordering of a field is contained in an ordering. -/
theorem exists_le_isOrdering (hP : P.IsPreordering) :
    ∃ Q : Subsemiring K, P ≤ Q ∧ Q.IsOrdering := by
  obtain ⟨Q, hPQ, hQ, hmax⟩ := zorn_le_nonempty₀ {Q : Subsemiring K | Q.IsPreordering}
    (fun c hpre hc y hy => by
      have : Nonempty c := ⟨⟨y, hy⟩⟩
      exact ⟨⨆ P : c, P.val, .iSup (fun P : c => hpre P.property) hc.directed,
        fun z hz => le_iSup (fun P : c => P.val) ⟨z, hz⟩⟩) P hP
  -- A maximal preordering contains one sign of every element, since adjoining `a` when
  -- `-a` is absent yields another preordering.
  refine ⟨Q, hPQ, hQ.isOrdering_of_isSpanning (Subsemiring.isSpanning_def.mpr fun a => ?_)⟩
  exact or_iff_not_imp_right.mpr fun ha =>
    hmax (hQ.isPreordering_adjoin ha) (hQ.le_adjoin a) (hQ.self_mem_adjoin a)

/-- An element whose negative is absent can be made nonnegative in an extending ordering. -/
theorem exists_le_isOrdering_mem (hP : P.IsPreordering) {a : K} (ha : -a ∉ P) :
    ∃ Q : Subsemiring K, P ≤ Q ∧ Q.IsOrdering ∧ a ∈ Q := by
  obtain ⟨Q, hQ, horder⟩ := (hP.isPreordering_adjoin ha).exists_le_isOrdering
  exact ⟨Q, (hP.le_adjoin a).trans hQ, horder, hQ (hP.self_mem_adjoin a)⟩

/-- A field with a preordering `P` admits a linear order making it a strictly ordered ring
in which every element of `P` is nonnegative. -/
theorem exists_linearOrder (hP : P.IsPreordering) :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K ∧ ∀ x ∈ P, 0 ≤ x := by
  classical
  obtain ⟨Q, hPQ, hQ⟩ := hP.exists_le_isOrdering
  let := LinearOrder.ofAddSubmonoid hQ.isPreordering.isPointed hQ.isSpanning
  have : IsOrderedRing K := IsOrderedRing.ofSubsemiring hQ.isPreordering.isPointed
  exact ⟨inferInstance, inferInstance, fun x hx =>
    PartialOrder.ofAddSubmonoid_le_iff.mpr (by simpa using hPQ hx)⟩

end Subsemiring.IsPreordering
