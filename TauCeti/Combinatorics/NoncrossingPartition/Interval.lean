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
# Intervals of the lattice of noncrossing partitions

Let `π` be a noncrossing partition of a finite set `s` of positions in a linear order. A
noncrossing partition `σ ≤ π` is the same as a choice of a noncrossing partition of each part `B`
of `π`: restricting `σ` to the parts of `π` and juxtaposing noncrossing partitions of the parts
(`Finpartition.bind`) are inverse to each other, and both preserve refinement. Hence the lower
interval `[0_s, π]` of `NC(s)` is isomorphic, as an order, to the product of the lattices `NC(B)`
over the parts `B` of `π`.

Consequently, summing a multiplicative function `σ ↦ ∏_{C ∈ σ} g C` over `σ ≤ π` factors as the
product over the parts `B` of `π` of its sums over `NC(B)`. This factorisation is what makes the
free cumulant of a noncrossing partition the product of the free cumulants of its parts.

More generally, for `σ ≤ π` the interval `[σ, π]` is the product over the parts `B` of `π` of the
upper intervals `[σ|_B, 1_B]` of `NC(B)`, where `σ|_B` is the restriction of `σ` to `B`. This
factorisation makes the Möbius function of `NC(s)` multiplicative on all intervals.

## Main definitions

* `TauCeti.NoncrossingPartition.iicOrderIso π` — the order isomorphism between the noncrossing
  partitions `σ ≤ π` and the families of noncrossing partitions of the parts of `π`.
* `TauCeti.NoncrossingPartition.iccOrderIso h` — for `h : σ ≤ π`, the order isomorphism
  `[σ, π] ≃o ∏_{B ∈ π} [σ|_B, 1_B]`.

## Main results

* `TauCeti.NoncrossingPartition.sum_Iic_prod_parts_eq_prod_sum` —
  `∑_{σ ≤ π} ∏_{C ∈ σ} g C = ∏_{B ∈ π} ∑_{τ ∈ NC(B)} ∏_{C ∈ τ} g C`.
* `TauCeti.NoncrossingPartition.sum_Icc_prod_restrict_eq_prod_sum` —
  `∑_{σ ≤ τ ≤ π} ∏_{B ∈ π} g_B(τ|_B) = ∏_{B ∈ π} ∑_{ρ ∈ NC(B), σ|_B ≤ ρ} g_B(ρ)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 9 and 10.
* R. Speicher, *Multiplicative functions on the lattice of non-crossing partitions and free
  convolution*, Math. Ann. 298 (1994), 611–628.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- A member of the lower interval of `π` refines `π` as a finite partition. -/
private theorem coe_le_of_mem_Iic {π : NoncrossingPartition s} (σ : Set.Iic π) :
    (σ.val : Finpartition s) ≤ π.val :=
  Subtype.coe_le_coe.2 (Set.mem_Iic.1 σ.property)

/-- The lower interval `[0_s, π]` of the lattice of noncrossing partitions of `s` is isomorphic
to the product of the lattices of noncrossing partitions of the parts of `π`: a noncrossing
partition `σ ≤ π` corresponds to its restrictions to the parts of `π`, and a family of noncrossing
partitions of the parts corresponds to their juxtaposition. -/
noncomputable def iicOrderIso (π : NoncrossingPartition s) :
    Set.Iic π ≃o ((B : π.val.parts) → NoncrossingPartition B.val) where
  toFun σ B := σ.val.restrict (π.val.le B.property)
  invFun Q := ⟨⟨π.val.bind fun B hB => (Q ⟨B, hB⟩).val, π.property.bind fun B hB => (Q ⟨B,
      hB⟩).property⟩,
    Finpartition.bind_le _ _⟩
  left_inv σ := Subtype.ext <| Subtype.ext <| by
    simpa only [coe_restrict] using Finpartition.bind_restrict (coe_le_of_mem_Iic σ)
  right_inv Q := funext fun B => Subtype.ext <|
    (coe_restrict _ _).trans (Finpartition.restrict_bind B.property)
  map_rel_iff' {σ σ'} := by
    refine ⟨fun h => ?_, fun h B => restrict_mono (π.val.le B.property) h⟩
    have := Finpartition.bind_mono (P := π.val)
      (Q := fun B hB => (σ.val.restrict (π.val.le hB)).val)
      (Q' := fun B hB => (σ'.val.restrict (π.val.le hB)).val) fun B hB => h ⟨B, hB⟩
    simp only [coe_restrict] at this
    rwa [Finpartition.bind_restrict (coe_le_of_mem_Iic σ),
      Finpartition.bind_restrict (coe_le_of_mem_Iic σ')] at this

@[simp]
theorem iicOrderIso_apply (π : NoncrossingPartition s) (σ : Set.Iic π) (B : π.val.parts) :
    π.iicOrderIso σ B = σ.val.restrict (π.val.le B.property) :=
  (rfl)

theorem coe_iicOrderIso_apply (π : NoncrossingPartition s) (σ : Set.Iic π) (B : π.val.parts) :
    ((π.iicOrderIso σ B : NoncrossingPartition B.val) : Finpartition B.val) =
      (σ.val : Finpartition s).restrict (π.val.le B.property) :=
  coe_restrict _ _

@[simp]
theorem coe_iicOrderIso_symm_apply (π : NoncrossingPartition s)
    (Q : (B : π.val.parts) → NoncrossingPartition B.val) :
    (((π.iicOrderIso.symm Q).val : NoncrossingPartition s) : Finpartition s) =
      (π.val : Finpartition s).bind fun B hB => (Q ⟨B, hB⟩).val :=
  (rfl)

/-- Summing a multiplicative function of the noncrossing partitions over the lower interval of a
noncrossing partition `π` factors over the parts of `π`:
`∑_{σ ≤ π} ∏_{C ∈ σ} g C = ∏_{B ∈ π} ∑_{τ ∈ NC(B)} ∏_{C ∈ τ} g C`. -/
theorem sum_Iic_prod_parts_eq_prod_sum {M : Type*} [CommSemiring M] (π : NoncrossingPartition s)
    (g : Finset α → M) :
    ∑ σ ∈ Iic π, ∏ C ∈ σ.val.parts, g C =
      ∏ B ∈ π.val.parts, ∑ τ : NoncrossingPartition B, ∏ C ∈ τ.val.parts, g C := by
  rw [← prod_coe_sort, Fintype.prod_sum,
    sum_subtype (Iic π) (p := (· ∈ Set.Iic π)) fun _ => mem_Iic.trans Set.mem_Iic.symm]
  refine Fintype.sum_equiv π.iicOrderIso.toEquiv _ _ fun σ => ?_
  conv_lhs => rw [← Finpartition.bind_restrict (coe_le_of_mem_Iic σ)]
  rw [Finpartition.prod_parts_bind, ← univ_eq_attach]
  simp only [OrderIso.coe_toEquiv, coe_iicOrderIso_apply]

/-! ### General intervals -/

/-- The interval `[σ, π]` of the lattice of noncrossing partitions of `s` is isomorphic to the
product over the parts `B` of `π` of the upper intervals `[σ|_B, 1_B]` of the lattices `NC(B)`: a
noncrossing partition `τ` with `σ ≤ τ ≤ π` corresponds to its restrictions to the parts of `π`. -/
noncomputable def iccOrderIso {σ π : NoncrossingPartition s} (h : σ ≤ π) :
    Set.Icc σ π ≃o ((B : π.val.parts) → Set.Ici (σ.restrict (π.val.le B.property))) where
  toFun τ B := ⟨τ.val.restrict (π.val.le B.property), restrict_mono _ τ.property.1⟩
  invFun Q := ⟨π.iicOrderIso.symm (fun B => (Q B).val),
    Subtype.coe_le_coe.2 ((π.iicOrderIso.le_symm_apply (x := ⟨σ, h⟩)).2 fun B => (Q B).property),
    (π.iicOrderIso.symm _).property⟩
  left_inv τ := Subtype.ext
    (congrArg (fun x : Set.Iic π => x.val) (π.iicOrderIso.symm_apply_apply ⟨τ.val, τ.property.2⟩))
  right_inv Q := funext fun B => Subtype.ext <|
    congrFun (π.iicOrderIso.apply_symm_apply fun B => (Q B).val) B
  map_rel_iff' {τ τ'} := by
    have := π.iicOrderIso.le_iff_le (x := ⟨τ.val, τ.property.2⟩) (y := ⟨τ'.val, τ'.property.2⟩)
    simp only [Pi.le_def, iicOrderIso_apply, Subtype.mk_le_mk] at this
    simpa only [Equiv.coe_fn_mk, Pi.le_def, Subtype.mk_le_mk, ← Subtype.coe_le_coe] using this

@[simp]
theorem coe_iccOrderIso_apply {σ π : NoncrossingPartition s} (h : σ ≤ π) (τ : Set.Icc σ π)
    (B : π.val.parts) : (iccOrderIso h τ B).val = τ.val.restrict (π.val.le B.property) :=
  (rfl)

@[simp]
theorem coe_iccOrderIso_symm_apply {σ π : NoncrossingPartition s} (h : σ ≤ π)
    (Q : (B : π.val.parts) → Set.Ici (σ.restrict (π.val.le B.property))) :
    ((iccOrderIso h).symm Q).val = (π.iicOrderIso.symm fun B => (Q B).val).val :=
  (rfl)

/-- Summing a function of the restrictions to the parts of `π` over the interval `[σ, π]` factors
over the parts of `π`:
`∑_{σ ≤ τ ≤ π} ∏_{B ∈ π} g_B(τ|_B) = ∏_{B ∈ π} ∑_{ρ ∈ NC(B), σ|_B ≤ ρ} g_B(ρ)`. -/
theorem sum_Icc_prod_restrict_eq_prod_sum {M : Type*} [CommSemiring M]
    {σ π : NoncrossingPartition s} (h : σ ≤ π)
    (g : (B : π.val.parts) → NoncrossingPartition B.val → M) :
    ∑ τ ∈ Icc σ π, ∏ B : π.val.parts, g B (τ.restrict (π.val.le B.property)) =
      ∏ B : π.val.parts, ∑ ρ ∈ Ici (σ.restrict (π.val.le B.property)), g B ρ := by
  rw [sum_subtype (F := inferInstance) (Icc σ π) (p := (· ∈ Set.Icc σ π))
      fun _ => mem_Icc.trans Set.mem_Icc.symm,
    prod_congr rfl fun B _ => sum_subtype (F := inferInstance)
      (Ici (σ.restrict (π.val.le B.property))) (p := (· ∈ Set.Ici _))
      (fun _ => mem_Ici.trans Set.mem_Ici.symm) (g B),
    Fintype.prod_sum]
  exact Fintype.sum_equiv (iccOrderIso h).toEquiv _ _ fun _ => rfl

end TauCeti.NoncrossingPartition
