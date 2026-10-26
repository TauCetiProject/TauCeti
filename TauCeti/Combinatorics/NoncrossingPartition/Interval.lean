/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Set.Defs
public import TauCeti.Combinatorics.NoncrossingPartition.Basic

/-!
# Lower intervals of the lattice of noncrossing partitions

Let `π` be a noncrossing partition of a finite set `s` of positions in a linear order. A
noncrossing partition `σ ≤ π` is the same as a choice of a noncrossing partition of each part `B`
of `π`: restricting `σ` to the parts of `π` and juxtaposing noncrossing partitions of the parts
(`Finpartition.bind`) are inverse to each other, and both preserve refinement. Hence the lower
interval `[0_s, π]` of `NC(s)` is isomorphic, as an order, to the product of the lattices `NC(B)`
over the parts `B` of `π`.

Consequently, summing a multiplicative function `σ ↦ ∏_{C ∈ σ} g C` over `σ ≤ π` factors as the
product over the parts `B` of `π` of its sums over `NC(B)`. This factorisation is what makes the
free cumulant of a noncrossing partition the product of the free cumulants of its parts.

## Main definitions

* `TauCeti.NoncrossingPartition.iicOrderIso π` — the order isomorphism between the noncrossing
  partitions `σ ≤ π` and the families of noncrossing partitions of the parts of `π`.

## Main results

* `TauCeti.NoncrossingPartition.sum_Iic_prod_parts_eq_prod_sum` —
  `∑_{σ ≤ π} ∏_{C ∈ σ} g C = ∏_{B ∈ π} ∑_{τ ∈ NC(B)} ∏_{C ∈ τ} g C`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
* R. Speicher, *Multiplicative functions on the lattice of non-crossing partitions and free
  convolution*, Math. Ann. 298 (1994), 611–628.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- A member of the lower interval of `π` refines `π` as a finite partition. -/
private theorem coe_le_of_mem_Iic {π : NoncrossingPartition s} (σ : Set.Iic π) :
    (σ.1 : Finpartition s) ≤ π.1 :=
  Subtype.coe_le_coe.2 (Set.mem_Iic.1 σ.2)

/-- The lower interval `[0_s, π]` of the lattice of noncrossing partitions of `s` is isomorphic
to the product of the lattices of noncrossing partitions of the parts of `π`: a noncrossing
partition `σ ≤ π` corresponds to its restrictions to the parts of `π`, and a family of noncrossing
partitions of the parts corresponds to their juxtaposition. -/
noncomputable def iicOrderIso (π : NoncrossingPartition s) :
    Set.Iic π ≃o ((B : π.1.parts) → NoncrossingPartition B.1) where
  toFun σ B := ⟨σ.1.1.restrict (π.1.le B.2), σ.1.2.restrict _⟩
  invFun Q := ⟨⟨π.1.bind fun B hB => (Q ⟨B, hB⟩).1, π.2.bind fun B hB => (Q ⟨B, hB⟩).2⟩,
    Finpartition.bind_le _ _⟩
  left_inv σ := Subtype.ext <| Subtype.ext <| Finpartition.bind_restrict (coe_le_of_mem_Iic σ)
  right_inv Q := funext fun B => Subtype.ext <| Finpartition.restrict_bind B.2
  map_rel_iff' {σ σ'} := by
    refine ⟨fun h => ?_, fun h B => Finpartition.restrict_mono (π.1.le B.2) h⟩
    have := Finpartition.bind_mono (P := π.1) (Q := fun B hB => σ.1.1.restrict (π.1.le hB))
      (Q' := fun B hB => σ'.1.1.restrict (π.1.le hB)) fun B hB => h ⟨B, hB⟩
    rwa [Finpartition.bind_restrict (coe_le_of_mem_Iic σ),
      Finpartition.bind_restrict (coe_le_of_mem_Iic σ')] at this

@[simp]
theorem coe_iicOrderIso_apply (π : NoncrossingPartition s) (σ : Set.Iic π) (B : π.1.parts) :
    ((π.iicOrderIso σ B : NoncrossingPartition B.1) : Finpartition B.1) =
      (σ.1 : Finpartition s).restrict (π.1.le B.2) :=
  (rfl)

@[simp]
theorem coe_iicOrderIso_symm_apply (π : NoncrossingPartition s)
    (Q : (B : π.1.parts) → NoncrossingPartition B.1) :
    (((π.iicOrderIso.symm Q).1 : NoncrossingPartition s) : Finpartition s) =
      (π.1 : Finpartition s).bind fun B hB => (Q ⟨B, hB⟩).1 :=
  (rfl)

/-- Summing a multiplicative function of the noncrossing partitions over the lower interval of a
noncrossing partition `π` factors over the parts of `π`:
`∑_{σ ≤ π} ∏_{C ∈ σ} g C = ∏_{B ∈ π} ∑_{τ ∈ NC(B)} ∏_{C ∈ τ} g C`. -/
theorem sum_Iic_prod_parts_eq_prod_sum {M : Type*} [CommSemiring M] (π : NoncrossingPartition s)
    (g : Finset α → M) :
    ∑ σ ∈ Iic π, ∏ C ∈ σ.1.parts, g C =
      ∏ B ∈ π.1.parts, ∑ τ : NoncrossingPartition B, ∏ C ∈ τ.1.parts, g C := by
  rw [← prod_coe_sort, Fintype.prod_sum,
    sum_subtype (Iic π) (p := (· ∈ Set.Iic π)) fun _ => mem_Iic.trans Set.mem_Iic.symm]
  refine Fintype.sum_equiv π.iicOrderIso.toEquiv _ _ fun σ => ?_
  conv_lhs => rw [← Finpartition.bind_restrict (coe_le_of_mem_Iic σ)]
  rw [Finpartition.prod_parts_bind, ← univ_eq_attach]
  simp only [OrderIso.coe_toEquiv, coe_iicOrderIso_apply]

end TauCeti.NoncrossingPartition
