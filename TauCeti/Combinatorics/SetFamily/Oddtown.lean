/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The oddtown theorem

A family of subsets of an `n`-element set has at most `n` members as soon as, in some field, the
sizes of its members are nonzero while the sizes of the intersections of distinct members vanish.
The incidence vectors of the members are then pairwise orthogonal for the dot product on the
`n`-dimensional space of functions on the ground set, and none of them is orthogonal to itself,
so they are linearly independent.

Over the integers modulo a prime `p` this is the oddtown theorem modulo `p`: if `p` divides the
size of no member and divides the size of the intersection of any two distinct members, the
family has at most `n` members. The case `p = 2`, in which the sizes are odd and the
intersections even, is the oddtown theorem proper.

## Main statements

* `Finset.card_le_of_natCast_card_inter_eq_zero`: the bound over a field.
* `Finset.card_le_of_not_dvd_card_of_dvd_card_inter`: the oddtown theorem modulo a prime.

## References

* Jiří Matoušek, *Thirty-three Miniatures: Mathematical and Algorithmic Applications of Linear
  Algebra*, Student Mathematical Library 53, American Mathematical Society, 2010, Miniature 3.
* Benny Sudakov and Pedro Vieira, *Two remarks on even and oddtown problems*, arXiv:1610.07907,
  §1.
-/

public section

open Finset

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of subsets of a finite type `α` has at most `Fintype.card α` members if, in a field
`K`, the size of each member is nonzero and the size of the intersection of any two distinct
members is zero. -/
theorem card_le_of_natCast_card_inter_eq_zero (F : Finset (Finset α)) (K : Type*) [Field K]
    (hsize : ∀ A ∈ F, (#A : K) ≠ 0)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (#(A ∩ B) : K) = 0) :
    #F ≤ Fintype.card α := by
  -- The incidence vectors of the members have Gram matrix `(#(A ∩ B))`.
  obtain ⟨v, hv⟩ : ∃ v : F → α → K, ∀ A B : F, v A ⬝ᵥ v B = (#(A.val ∩ B.val) : K) :=
    ⟨fun A a ↦ if a ∈ A.val then 1 else 0, fun A B ↦ by
      simp_rw [dotProduct, ite_zero_mul_ite_zero, mul_one, ← mem_inter, sum_boole, filter_univ_mem]⟩
  -- They are pairwise orthogonal for the dot product and none is orthogonal to itself.
  have hli : LinearIndependent K v :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := dotProductBilin K K)
      (LinearMap.BilinForm.iIsOrtho_def.mpr fun A B hAB ↦ by
        simpa [hv] using hinter A A.prop B B.prop (Subtype.coe_injective.ne hAB))
      fun A ↦ by simpa [hv] using hsize A A.prop
  simpa using hli.fintype_card_le_finrank

/-- **The oddtown theorem modulo a prime.** If a prime `p` divides the size of no member of a
family of subsets of a finite type `α` and divides the size of the intersection of any two
distinct members, then the family has at most `Fintype.card α` members. For `p = 2` this is the
oddtown theorem. -/
theorem card_le_of_not_dvd_card_of_dvd_card_inter (F : Finset (Finset α)) {p : ℕ} (hp : p.Prime)
    (hsize : ∀ A ∈ F, ¬ p ∣ #A) (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → p ∣ #(A ∩ B)) :
    #F ≤ Fintype.card α := by
  have := Fact.mk hp
  exact F.card_le_of_natCast_card_inter_eq_zero (ZMod p)
    (fun A hA ↦ mt (ZMod.natCast_eq_zero_iff _ _).mp (hsize A hA))
    fun A hA B hB hAB ↦ (ZMod.natCast_eq_zero_iff _ _).mpr (hinter A hA B hB hAB)

end Finset
