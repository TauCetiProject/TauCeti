/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic

/-!
# The length of strand diagrams and the identity diagrams of the strands algebra

The strands of a strand diagram `φ : S → T` only move upwards, so they have a total length
`TauCeti.StrandDiagram.length φ`, the sum over the strands `i ↦ j` of the number of points `x`
with `i < x ≤ j`. The length adds up under concatenation
(`TauCeti.StrandDiagram.length_trans_of_target_eq`), it is bounded by the square of the number of
points, and it vanishes exactly on the identity diagrams `I(S)`, whose strands are all horizontal
(`TauCeti.StrandDiagram.length_eq_zero_iff`).

In the strands algebra of Lipshitz, Ozsváth and Thurston this separates the idempotents `I(S)`
from the rest. A concatenation is an identity diagram only when both of its factors are, so the
coefficient of `I(S)` in a product is the product of the coefficients of `I(S)` in the factors
(`TauCeti.StrandsAlgebra.repr_mul_idOn`). And the diagrams of a product of `k` elements without
identity diagrams have length at least `k`, so an element whose coefficients on the identity
diagrams all vanish is nilpotent
(`TauCeti.StrandsAlgebra.isNilpotent_of_forall_repr_idOn_eq_zero`). These two facts are what
make the idempotents `I(s)` of the algebra of a pointed matched circle primitive
(`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Primitive`).

## Main definitions

* `TauCeti.StrandDiagram.length φ`: the total length of the strands of `φ`.

## Main results

* `TauCeti.StrandDiagram.length_trans_of_target_eq`: the length of a concatenation is the sum of
  the lengths.
* `TauCeti.StrandDiagram.length_eq_zero_iff`: a diagram has length zero exactly when it is an
  identity diagram.
* `TauCeti.StrandDiagram.trans_eq_idOn_iff`: a concatenation is an identity diagram exactly when
  both factors are.
* `TauCeti.StrandsAlgebra.repr_mul_idOn`: the coefficient of an identity diagram in a product is
  the product of its coefficients in the factors.
* `TauCeti.StrandsAlgebra.isNilpotent_of_forall_repr_idOn_eq_zero`: an element of the strands
  algebra without identity diagrams is nilpotent.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 (the
  strands algebra and its idempotents).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α] {φ ψ : StrandDiagram α}

/-- The total length of the strands of a strand diagram: the sum over its strands `i ↦ j` of the
number of points `x` with `i < x ≤ j`. -/
def length (φ : StrandDiagram α) : ℕ :=
  ∑ i ∈ φ.source, #{x | i < x ∧ x ≤ φ.endpoint i}

theorem length_def (φ : StrandDiagram α) :
    φ.length = ∑ i ∈ φ.source, #{x | i < x ∧ x ≤ φ.endpoint i} :=
  (rfl)

/-- Identity diagrams have length zero. -/
@[simp]
theorem length_idOn (s : Finset α) : (idOn s).length = 0 := by
  refine sum_eq_zero fun i hi ↦ ?_
  rw [source_idOn] at hi
  rw [endpoint_eq_of_mem (mem_idOn.2 ⟨rfl, hi⟩), card_eq_zero, filter_eq_empty_iff]
  exact fun x _ h ↦ lt_irrefl i (h.1.trans_le h.2)

/-- **A diagram has length zero exactly when it is an identity diagram**, all of its strands
being horizontal. -/
theorem length_eq_zero_iff : φ.length = 0 ↔ φ = idOn φ.source := by
  refine ⟨fun h ↦ ext fun i ↦ ?_, fun h ↦ by rw [h, length_idOn]⟩
  rw [idOn_apply]
  split_ifs with hi
  · -- A strand starting at `i` ends at a point `j ≥ i`, and `j > i` would contribute to the length.
    have hj : ¬i < φ.endpoint i := fun hlt ↦ by
      have h' := sum_eq_zero_iff.1 h i hi
      rw [card_eq_zero, filter_eq_empty_iff] at h'
      exact h' (mem_univ _) ⟨hlt, le_rfl⟩
    have hmem := endpoint_mem hi
    rw [le_antisymm (not_lt.1 hj) (φ.le_of_mem hmem)] at hmem
    exact Option.mem_def.1 hmem
  · exact apply_eq_none_of_notMem_source hi

/-- The length of a diagram is at most the square of the number of points: it has at most that
many strands, each of length at most that number. -/
theorem length_le (φ : StrandDiagram α) : φ.length ≤ Fintype.card α * Fintype.card α := by
  refine (sum_le_card_nsmul _ _ (Fintype.card α) fun i _ ↦ card_le_univ _).trans ?_
  rw [smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_le_univ _)

/-- **The length is additive under concatenation**: if `φ` ends where `ψ` starts, each strand of
`φ.trans ψ` is a strand of `φ` followed by a strand of `ψ`. -/
theorem length_trans_of_target_eq (h : φ.target = ψ.source) :
    (φ.trans ψ).length = φ.length + ψ.length := by
  have hψ : ψ.length =
      ∑ i ∈ φ.source, #{x | φ.endpoint i < x ∧ x ≤ ψ.endpoint (φ.endpoint i)} := by
    rw [length_def, ← h, target_eq_image, sum_image φ.injOn_getD]
    simp only [← endpoint_def]
  rw [hψ, length_def, length_def, source_trans_of_target_eq h, ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hj := h ▸ endpoint_mem_target hi
  let := Fintype.toLocallyFiniteOrder (α := α)
  rw [endpoint_trans_of_target_eq h hi, filter_lt_le_eq_Ioc, filter_lt_le_eq_Ioc,
    filter_lt_le_eq_Ioc, ← card_union_of_disjoint (Ioc_disjoint_Ioc_of_le le_rfl),
    Ioc_union_Ioc_eq_Ioc (φ.le_of_mem (endpoint_mem hi)) (ψ.le_of_mem (endpoint_mem hj))]

/-- **A concatenation is an identity diagram exactly when both factors are**: the lengths of the
factors add up to the length zero of an identity diagram. -/
theorem trans_eq_idOn_iff (h : φ.target = ψ.source) {s : Finset α} :
    φ.trans ψ = idOn s ↔ φ = idOn s ∧ ψ = idOn s := by
  refine ⟨fun he ↦ ?_, fun ⟨hφ, hψ⟩ ↦ ?_⟩
  · have hlen := length_trans_of_target_eq h
    rw [he, length_idOn] at hlen
    have hφ := length_eq_zero_iff.1 (by omega : φ.length = 0)
    have hψ := length_eq_zero_iff.1 (by omega : ψ.length = 0)
    have hs : φ.source = s := by rw [← source_trans_of_target_eq h, he, source_idOn]
    rw [hφ, hs] at h ⊢
    rw [target_idOn] at h
    rw [hψ, ← h]
    exact ⟨rfl, rfl⟩
  · rw [hφ, hψ, idOn_trans_of_eq_source (source_idOn s).symm]

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- **The coefficient of an identity diagram is multiplicative.** A concatenation is the identity
diagram on `s` only when both factors are, so the coefficient of `I(s)` in a product is the
product of the coefficients of `I(s)` in the factors. -/
@[simp]
theorem repr_mul_idOn (x y : StrandsAlgebra R α) (s : Finset α) :
    (basis R α).repr (x * y) (idOn s) =
      (basis R α).repr x (idOn s) * (basis R α).repr y (idOn s) := by
  have := Fintype.ofFinite (StrandDiagram α)
  rw [repr_mul_apply, Fintype.sum_eq_single (idOn s), Fintype.sum_eq_single (idOn s),
    ite_eq_left ⟨composable_idOn_left_iff.2 (source_idOn s).symm,
      idOn_trans_of_eq_source (source_idOn s).symm⟩]
  · exact fun ψ hψ ↦ ite_eq_right fun ⟨hc, he⟩ ↦ hψ ((trans_eq_idOn_iff hc.target_eq).1 he).2
  · exact fun φ hφ ↦ sum_eq_zero fun ψ _ ↦
      ite_eq_right fun ⟨hc, he⟩ ↦ hφ ((trans_eq_idOn_iff hc.target_eq).1 he).1

/-- **An element without identity diagrams is nilpotent.** The diagrams of `x ^ k` are
concatenations of `k` diagrams of `x`, each of positive length, so they have length at least `k`;
no diagram is longer than the square of the number of points. -/
theorem isNilpotent_of_forall_repr_idOn_eq_zero {x : StrandsAlgebra R α}
    (hx : ∀ s, (basis R α).repr x (idOn s) = 0) : IsNilpotent x := by
  have key (k : ℕ) (χ : StrandDiagram α) (hχ : (basis R α).repr (x ^ k) χ ≠ 0) :
      k ≤ χ.length := by
    induction k generalizing χ with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      rw [pow_succ] at hχ
      obtain ⟨φ, ψ, hc, rfl, hφ, hψ⟩ := exists_of_repr_mul_ne_zero hχ
      have hψ' : ψ.length ≠ 0 := fun h ↦ by
        have h' := hx ψ.source
        rw [← length_eq_zero_iff.1 h] at h'
        exact hψ h'
      have := ih φ hφ
      rw [length_trans_of_target_eq hc.target_eq]
      omega
  refine ⟨Fintype.card α * Fintype.card α + 1, (basis R α).ext_elem fun χ ↦ ?_⟩
  by_contra h
  rw [map_zero, Finsupp.zero_apply] at h
  have := key _ χ h
  have := χ.length_le
  omega

end StrandsAlgebra

end TauCeti
