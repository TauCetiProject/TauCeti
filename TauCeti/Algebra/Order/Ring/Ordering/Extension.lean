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
`RingPreordering` and `RingCone` interfaces.
-/

public section

variable {K : Type*} [Field K]

namespace RingPreordering

/-- Adjoin an element whose negative is absent from a field preordering. -/
def adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) : RingPreordering K :=
  RingPreordering.mk' {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v}
    (by
      rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
      exact ⟨u + w, add_mem hu hw, v + z, add_mem hv hz, by ring⟩)
    (by
      rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
      exact ⟨u * w + a ^ 2 * (v * z),
        add_mem (mul_mem hu hw) (mul_mem (P.pow_two_mem a) (mul_mem hv hz)),
        u * z + v * w, add_mem (mul_mem hu hz) (mul_mem hv hw), by ring⟩)
    (fun x => ⟨x * x, P.mul_self_mem x, 0, zero_mem P, by simp⟩)
    (by
      rintro ⟨u, hu, v, hv, heq⟩
      by_cases hv0 : v = 0
      · apply P.neg_one_notMem
        have heq' : -1 = u := by simpa only [hv0, mul_zero, add_zero] using heq
        exact heq' ▸ hu
      · apply ha
        have hmem : (1 + u) * v⁻¹ ∈ P :=
          mul_mem (add_mem (one_mem P) hu) (RingPreordering.inv_mem hv)
        have hval : -a = (1 + u) * v⁻¹ := by
          field_simp
          linear_combination heq
        rwa [← hval] at hmem)

@[simp] theorem mem_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) {x : K} :
    x ∈ adjoin P a ha ↔ ∃ u ∈ P, ∃ v ∈ P, x = u + a * v := (Iff.rfl)

theorem le_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) :
    P ≤ adjoin P a ha :=
  fun x hx => ⟨x, hx, 0, zero_mem P, by simp⟩

theorem self_mem_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) :
    a ∈ adjoin P a ha :=
  ⟨0, zero_mem P, 1, one_mem P, by simp⟩

/-- The generated preordering is contained in every preordering containing its generators. -/
theorem adjoin_le {P Q : RingPreordering K} {a : K} {ha : -a ∉ P}
    (hPQ : P ≤ Q) (haQ : a ∈ Q) : adjoin P a ha ≤ Q := by
  rintro x ⟨u, hu, v, hv, rfl⟩
  exact add_mem (hPQ hu) (mul_mem haQ (hPQ hv))

@[simp] theorem adjoin_le_iff {P Q : RingPreordering K} {a : K} {ha : -a ∉ P} :
    adjoin P a ha ≤ Q ↔ P ≤ Q ∧ a ∈ Q :=
  ⟨fun h => ⟨(le_adjoin P a ha).trans h, h (self_mem_adjoin P a ha)⟩,
    fun h => adjoin_le h.1 h.2⟩

/-- The union of a nonempty chain of preorderings is a preordering. -/
private def chainUnion (c : Set (RingPreordering K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : RingPreordering K := by
  have := hne.to_subtype
  have hd : Directed (· ≤ ·) (fun P : c => P.val.toSubsemiring) :=
    hc.directed.mono_comp _ RingPreordering.toSubsemiring_mono
  exact
    { (⨆ P : c, P.val.toSubsemiring).copy {x | ∃ P ∈ c, x ∈ P} (by
        rw [Subsemiring.coe_iSup_of_directed hd]
        ext x
        simp) with
      mem_of_isSquare' := by
        rintro x ⟨y, rfl⟩
        obtain ⟨P, hP⟩ := hne
        exact ⟨P, hP, P.mul_self_mem y⟩
      neg_one_notMem' := by
        rintro ⟨P, _, hP⟩
        exact P.neg_one_notMem hP }

private theorem le_chainUnion (c : Set (RingPreordering K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {P : RingPreordering K} (hP : P ∈ c) :
    P ≤ chainUnion c hc hne :=
  fun _ hx => ⟨P, hP, hx⟩

/-- A field preordering extends to an ordering, retaining every prescribed sign. -/
theorem exists_le_isOrdering (P : RingPreordering K) :
    ∃ Q : RingPreordering K, P ≤ Q ∧ Q.IsOrdering := by
  obtain ⟨Q, hPQ, hQ⟩ := zorn_le_nonempty_Ici₀ P
    (fun c _ hc y hy =>
      ⟨chainUnion c hc ⟨y, hy⟩, fun z hz => le_chainUnion c hc ⟨y, hy⟩ hz⟩) P le_rfl
  have htotal : HasMemOrNegMem Q := ⟨by
    intro a
    by_cases ha : -a ∈ Q
    · exact Or.inr ha
    · exact Or.inl ((hQ (le_adjoin Q a ha)) (self_mem_adjoin Q a ha))⟩
  exact ⟨Q, hPQ, { htotal with toIsPrime := inferInstance }⟩

/-- An element whose negative is absent can be made nonnegative in an extending ordering. -/
theorem exists_le_isOrdering_mem (P : RingPreordering K) {a : K} (ha : -a ∉ P) :
    ∃ Q : RingPreordering K, P ≤ Q ∧ Q.IsOrdering ∧ a ∈ Q := by
  obtain ⟨Q, hQ, horder⟩ := exists_le_isOrdering (adjoin P a ha)
  exact ⟨Q, (le_adjoin P a ha).trans hQ, horder, hQ (self_mem_adjoin P a ha)⟩

/-- A preordering on a field is a pointed ring cone. -/
def toRingCone (P : RingPreordering K) : RingCone K where
  __ := P.toSubsemiring
  eq_zero_of_mem_of_neg_mem' := P.eq_zero_of_mem_of_neg_mem

@[simp] theorem mem_toRingCone (P : RingPreordering K) {x : K} :
    x ∈ toRingCone P ↔ x ∈ P := (Iff.rfl)

instance (P : RingPreordering K) [P.IsOrdering] : HasMemOrNegMem (toRingCone P) where
  mem_or_neg_mem := mem_or_neg_mem P

/-- The linear order associated to a field ordering. -/
@[instance_reducible] noncomputable def linearOrder (P : RingPreordering K)
    [P.IsOrdering] : LinearOrder K := by
  classical
  exact .mkOfAddGroupCone (toRingCone P)

theorem isStrictOrderedRing (P : RingPreordering K) [P.IsOrdering] :
    letI := linearOrder P
    IsStrictOrderedRing K := by
  let := linearOrder P
  have : IsOrderedRing K := .mkOfCone (toRingCone P)
  infer_instance

theorem nonneg_iff (P : RingPreordering K) [P.IsOrdering] (x : K) :
    letI := linearOrder P
    0 ≤ x ↔ x ∈ P := by
  rw [PartialOrder.mkOfAddGroupCone_le_iff, sub_zero]
  exact mem_toRingCone P

/-- Order a field while respecting all signs in a specified preordering. -/
theorem exists_linearOrder (P : RingPreordering K) :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K ∧ ∀ x ∈ P, 0 ≤ x := by
  obtain ⟨Q, hPQ, hQ⟩ := exists_le_isOrdering P
  let := hQ
  exact ⟨linearOrder Q, isStrictOrderedRing Q, fun x hx => (nonneg_iff Q x).mpr (hPQ hx)⟩

end RingPreordering
