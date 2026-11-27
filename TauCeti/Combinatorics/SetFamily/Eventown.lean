/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.FieldTheory.Finiteness
import TauCeti.InformationTheory.Coding.EuclideanDual

/-!
# The eventown theorem

A family of subsets of an `n`-element set whose members have even size and whose distinct
members meet in an even number of elements has at most `2 ^ ⌊n / 2⌋` members, and this bound is
attained. This is the eventown theorem of Berlekamp and of Graver.

The upper bound is a dimension count over `ZMod 2`: the incidence vectors of the members are
pairwise orthogonal, and each is orthogonal to itself, for the dot product, so they span a totally
isotropic subspace of `α → ZMod 2`. The dot product is nondegenerate, so this subspace has
dimension at most `⌊n / 2⌋` and at most `2 ^ ⌊n / 2⌋` elements, while distinct members have
distinct incidence vectors. The extremal family consists of the unions of some of `⌊n / 2⌋`
pairwise disjoint pairs.

## Main results

* `Finset.card_le_two_pow_of_even`: the eventown bound `#F ≤ 2 ^ ⌊n / 2⌋`.
* `TauCeti.exists_even_card_even_card_inter_card_eq_two_pow`: a family attaining it.

## References

* B. Sudakov and P. Vieira, *Two remarks on even and oddtown problems*, arXiv:1610.07907, §1.
-/

public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The eventown theorem.** A family of subsets of an `n`-element set whose members have even
size and whose distinct members meet in an even number of elements has at most `2 ^ ⌊n / 2⌋`
members. -/
theorem card_le_two_pow_of_even (F : Finset (Finset α)) (hsize : ∀ A ∈ F, Even #A)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Even #(A ∩ B)) :
    #F ≤ 2 ^ (Fintype.card α / 2) := by
  -- The incidence vectors of the members, in `α → ZMod 2`, and the subspace `W` they span.
  let v : Finset α → α → ZMod 2 := fun A a ↦ if a ∈ A then 1 else 0
  have hv : Function.Injective v := fun A B h ↦ by
    ext a
    have := congr_fun h a
    by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp_all [v]
  let W := Submodule.span (ZMod 2) (v '' F)
  -- The incidence vectors are pairwise orthogonal, and orthogonal to themselves, for the dot
  -- product, since the dot product of the incidence vectors of `A` and `B` is `#(A ∩ B)` modulo
  -- `2`.
  have horth : ∀ A ∈ F, ∀ B ∈ F, v A ⬝ᵥ v B = 0 := by
    intro A hA B hB
    have hdot : v A ⬝ᵥ v B = #(A ∩ B) := by simp [v, dotProduct, inter_comm A B]
    rw [hdot, ZMod.natCast_eq_zero_iff_even]
    obtain rfl | hAB := eq_or_ne A B
    · simpa using hsize A hA
    · exact hinter A hA B hB hAB
  -- Hence `W` is self-orthogonal, so has at most half the ambient dimension.
  have hW : W.IsSelfOrthogonal := by
    refine Submodule.isSelfOrthogonal_iff_le.mpr <| Submodule.span_le.mpr ?_
    rintro _ ⟨B, hB, rfl⟩
    exact Submodule.mem_euclideanDual_span.mpr <| by
      rintro _ ⟨A, hA, rfl⟩
      exact horth A hA B hB
  have hdim := hW.two_mul_finrank_le_card
  -- Distinct members give distinct elements of `W`, which has `2 ^ dim W` elements.
  classical
  calc #F = Fintype.card F := (Fintype.card_coe F).symm
    _ ≤ Fintype.card W := Fintype.card_le_of_injective
        (fun A ↦ ⟨v A, Submodule.subset_span ⟨A, A.property, rfl⟩⟩)
        fun A B h ↦ Subtype.ext (hv congr(($h).val))
    _ = 2 ^ Module.finrank (ZMod 2) W := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ ≤ 2 ^ (Fintype.card α / 2) := Nat.pow_le_pow_right two_pos (by omega)

end Finset

namespace TauCeti

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The eventown bound is attained: some family of `2 ^ ⌊n / 2⌋` subsets of an `n`-element set
has members of even size and distinct members meeting in an even number of elements. The family
consists of the unions of some of `⌊n / 2⌋` pairwise disjoint pairs. -/
theorem exists_even_card_even_card_inter_card_eq_two_pow :
    ∃ F : Finset (Finset α), (∀ A ∈ F, Even #A) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Even #(A ∩ B)) ∧ #F = 2 ^ (Fintype.card α / 2) := by
  -- Choose `⌊n / 2⌋` disjoint pairs `{g (i, 0), g (i, 1)}` in `α`.
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (Fintype.card α / 2) × Fin 2) (β := α) (by simpa using Nat.div_mul_le_self _ 2)
  -- The union of the pairs indexed by `S`.
  let u : Finset (Fin (Fintype.card α / 2)) → Finset α := fun S ↦ (S ×ˢ univ).map g
  have hu : Function.Injective u := fun S T h ↦ by
    ext i
    simpa [u] using congr_arg (g (i, 0) ∈ ·) h
  refine ⟨univ.map ⟨u, hu⟩, ?_, ?_, ?_⟩
  · simp [u]
  · rintro _ hA _ hB -
    simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk] at hA hB
    obtain ⟨S, rfl⟩ := hA
    obtain ⟨T, rfl⟩ := hB
    simp [u, ← map_inter, product_inter_product]
  · simp

end TauCeti
