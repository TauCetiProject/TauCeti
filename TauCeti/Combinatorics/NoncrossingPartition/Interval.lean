/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Hom.Basic
public import TauCeti.Combinatorics.NoncrossingPartition.Basic

/-!
# Lower intervals of the lattice of noncrossing partitions

Let `π` be a noncrossing partition of a finite set `s` of positions in a linear order. A
noncrossing partition `σ ≤ π` of `s` is the same as a choice, for each part `B` of `π`, of a
noncrossing partition of `B`: restricting `σ` to the parts of `π` and juxtaposing partitions of the
parts of `π` (`Finpartition.bind`) are mutually inverse, and juxtaposing noncrossing partitions of
the parts of a noncrossing partition gives a noncrossing partition. Hence the lower interval
`[0_s, π]` of `NC(s)` is isomorphic to the product of the lattices `NC(B)` over the parts `B` of
`π`.

This factorization makes functions that are multiplicative over parts behave well under sums over
lower intervals; it is what makes free cumulants multiplicative over the parts of a noncrossing
partition.

## Main definitions

* `TauCeti.NoncrossingPartition.iicOrderIso π` — the order isomorphism between the noncrossing
  partitions refining `π` and the families of noncrossing partitions of the parts of `π`.

## Main results

* `Finpartition.IsNoncrossing.bind` — juxtaposing noncrossing partitions of the parts of a
  noncrossing partition gives a noncrossing partition.
* `TauCeti.NoncrossingPartition.sum_Iic_prod_parts` — a sum over `σ ≤ π` of a product over the
  parts of `σ` is the product over the parts `B` of `π` of the corresponding sums over `NC(B)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9
  (Proposition 9.11) and Lecture 11.
* R. Speicher, *Multiplicative functions on the lattice of non-crossing partitions and free
  convolution*, Math. Ann. 298 (1994), 611–628.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α} {P : Finpartition s}

/-- Juxtaposing noncrossing partitions of the parts of a noncrossing partition gives a noncrossing
partition. -/
theorem IsNoncrossing.bind (hP : P.IsNoncrossing) {Q : ∀ B ∈ P.parts, Finpartition B}
    (hQ : ∀ B hB, (Q B hB).IsNoncrossing) : (P.bind Q).IsNoncrossing := by
  refine isNoncrossing_iff.2 fun C hC D hD a ha b hb c hc d hd hab hbc hcd => ?_
  obtain ⟨B, hB, hC⟩ := mem_bind.1 hC
  obtain ⟨B', hB', hD⟩ := mem_bind.1 hD
  obtain rfl : B = B' := isNoncrossing_iff.1 hP B hB B' hB' a ((Q B hB).le hC ha) b
    ((Q B' hB').le hD hb) c ((Q B hB).le hC hc) d ((Q B' hB').le hD hd) hab hbc hcd
  exact isNoncrossing_iff.1 (hQ B hB) C hC D hD a ha b hb c hc d hd hab hbc hcd

end Finpartition

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The *interval factorization* of `NC(s)`: the noncrossing partitions `σ ≤ π` correspond, by
restriction to the parts of `π`, to the families of noncrossing partitions of the parts of `π`,
ordered componentwise. The inverse juxtaposes the partitions of the parts. -/
noncomputable def iicOrderIso (π : NoncrossingPartition s) :
    Set.Iic π ≃o ((B : π.1.parts) → NoncrossingPartition (B : Finset α)) :=
  Equiv.toOrderIso
    { toFun σ B := ⟨σ.1.1.restrict (π.1.le B.2), σ.1.2.restrict _⟩
      invFun τ := ⟨⟨π.1.bind fun B hB => (τ ⟨B, hB⟩).1, π.2.bind fun B hB => (τ ⟨B, hB⟩).2⟩,
        Finpartition.bind_le _ _⟩
      left_inv σ := Subtype.ext <| Subtype.ext <| Finpartition.bind_restrict_of_le σ.2
      right_inv _ := funext fun B => Subtype.ext <| Finpartition.restrict_bind _ B.2 }
    (fun _ _ h B => Finpartition.restrict_mono (π.1.le B.2) h)
    fun _ _ h => Finpartition.bind_mono fun B hB => h ⟨B, hB⟩

/-- The component of `iicOrderIso π σ` at a part `B` of `π` is the restriction of `σ` to `B`. -/
@[simp]
theorem coe_iicOrderIso_apply (π : NoncrossingPartition s) (σ : Set.Iic π) (B : π.1.parts) :
    (iicOrderIso π σ B : Finpartition (B : Finset α)) = σ.1.1.restrict (π.1.le B.2) :=
  (rfl)

/-- The noncrossing partition `(iicOrderIso π).symm τ` juxtaposes the partitions `τ B` of the
parts `B` of `π`. -/
@[simp]
theorem coe_iicOrderIso_symm_apply (π : NoncrossingPartition s)
    (τ : (B : π.1.parts) → NoncrossingPartition (B : Finset α)) :
    (((iicOrderIso π).symm τ : Set.Iic π) : Finpartition s) =
      π.1.bind fun B hB => (τ ⟨B, hB⟩).1 :=
  (rfl)

/-- A sum over the noncrossing partitions `σ ≤ π` of a product over the parts of `σ` factors as
the product over the parts `B` of `π` of the corresponding sums over the noncrossing partitions
of `B`. -/
theorem sum_Iic_prod_parts {M : Type*} [CommSemiring M] (π : NoncrossingPartition s)
    (f : Finset α → M) :
    ∑ σ ∈ Iic π, ∏ C ∈ σ.1.parts, f C =
      ∏ B ∈ π.1.parts, ∑ τ : NoncrossingPartition B, ∏ C ∈ τ.1.parts, f C := by
  rw [Finset.sum_subtype (Iic π) (p := (· ∈ Set.Iic π)) (fun _ => mem_Iic),
    ← (iicOrderIso π).symm.toEquiv.sum_comp, ← Finset.prod_coe_sort π.1.parts, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [OrderIso.coe_toEquiv, coe_iicOrderIso_symm_apply, Finpartition.prod_bind, univ_eq_attach]

end TauCeti.NoncrossingPartition
