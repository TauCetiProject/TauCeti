/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.GroupAction.StrongJordan
public import TauCeti.GroupTheory.Perm.Jordan

/-!
# Explicit witnesses for the strong Jordan criterion

This local prototype supplies a bridge needed by the proposed certified
permutation computation roadmap. It imports the existing draft API and
does not assume that the proposed roadmap has been accepted.
-/

open MulAction SubMulAction Subgroup

@[expose] public section

namespace TauCeti

variable {G α : Type*} [Group G] [MulAction G α]

/-- A subgroup whose elements fix `s` and can move every point of its
complement to every other point has a doubly transitive normal closure
in a primitive ambient action. The hypotheses are explicit mathematical
witnesses that a finite certificate checker can verify. -/
theorem normalClosure_is_two_pretransitive_of_witnesses
    (hG : IsPreprimitive G α) {H : Subgroup G} {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hcard : n + 2 < Nat.card α)
    (hfix : H ≤ fixingSubgroup G s)
    (htrans : ∀ x y : α, x ∉ s → y ∉ s → ∃ h : H, (h : G) • x = y) :
    IsMultiplyPretransitive (normalClosure (H : Set G)) α 2 := by
  refine hG.is_two_pretransitive_of_normal hsn hcard ⟨fun x y ↦ ?_⟩
  obtain ⟨h, hh⟩ := htrans x y x.prop y.prop
  refine ⟨⟨⟨h, le_normalClosure h.prop⟩, ?_⟩, Subtype.ext hh⟩
  exact (mem_fixingSubgroup_iff _).mpr fun z hz ↦
    (mem_fixingSubgroup_iff G).mp (hfix h.prop) z hz

/-- It suffices to give orbit witnesses from one base point, as a
certificate can store one word for each point of the complement. -/
theorem normalClosure_is_two_pretransitive_of_base_witnesses
    (hG : IsPreprimitive G α) {H : Subgroup G} {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hcard : n + 2 < Nat.card α)
    (hfix : H ≤ fixingSubgroup G s) (b : α)
    (hbase : ∀ y : α, y ∉ s → ∃ h : H, (h : G) • b = y) :
    IsMultiplyPretransitive (normalClosure (H : Set G)) α 2 := by
  apply normalClosure_is_two_pretransitive_of_witnesses hG hsn hcard hfix
  intro x y hx hy
  obtain ⟨u, hu⟩ := hbase x hx
  obtain ⟨v, hv⟩ := hbase y hy
  refine ⟨v * u⁻¹, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← hu, inv_smul_smul]
  exact hv

section Permutations

open Equiv Equiv.Perm

variable [Fintype α] [DecidableEq α]
variable {P : Subgroup (Perm α)} {H : Subgroup P} {s : Set α} {n p : ℕ}

/-- An explicit prime cycle in the normal closure, combined with local
orbit witnesses, certifies that its permutation image contains `Aₙ`.
Membership is in the normal closure itself, not just in the ambient
permutation group. -/
theorem alternatingGroup_le_normalClosure_of_witnesses
    (hP : IsPreprimitive P α)
    (hsn : s.ncard = n + 1) (hcard : n + 2 < Nat.card α)
    (hfix : H ≤ fixingSubgroup P s)
    (htrans : ∀ x y : α, x ∉ s → y ∉ s → ∃ h : H, (h : P) • x = y)
    (hp : p.Prime) (hpcard : p + 3 ≤ Nat.card α)
    {g : Perm α} (hcycle : g.IsCycle) (hsize : g.support.card = p)
    (hg : g ∈ (normalClosure (H : Set P)).map P.subtype) :
    alternatingGroup α ≤ (normalClosure (H : Set P)).map P.subtype := by
  have hN := normalClosure_is_two_pretransitive_of_witnesses hP hsn hcard hfix htrans
  have hK : IsMultiplyPretransitive ((normalClosure (H : Set P)).map P.subtype) α 2 := by
    rw [is_two_pretransitive_iff] at hN ⊢
    intro a b c d hab hcd
    obtain ⟨u, hu, hv⟩ := hN hab hcd
    refine ⟨⟨(u : P), Subgroup.mem_map.mpr ⟨(u : P), u.prop, rfl⟩⟩, ?_, ?_⟩
    · exact hu
    · exact hv
  exact alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    (isPreprimitive_of_is_two_pretransitive hK) hp hpcard hcycle hsize hg

/-- Evenness of a subgroup is preserved by taking its normal closure
inside an ambient permutation subgroup. -/
theorem normalClosure_image_le_alternatingGroup
    (heven : H ≤ (alternatingGroup α).comap P.subtype) :
    (normalClosure (H : Set P)).map P.subtype ≤ alternatingGroup α :=
  map_le_iff_le_comap.mpr (normalClosure_le_normal heven)

/-- A subgroup containing the alternating group and an odd permutation
is the full symmetric group. -/
theorem eq_top_of_alternatingGroup_le_of_odd
    {K : Subgroup (Perm α)} (hA : alternatingGroup α ≤ K)
    {u : Perm α} (hu : u ∈ K) (hodd : sign u = -1) :
    K = ⊤ := by
  apply top_unique
  intro v _
  by_cases hv : sign v = 1
  · exact hA (mem_alternatingGroup.mpr hv)
  · have hv' : sign v = -1 := (Int.units_eq_one_or (sign v)).resolve_left hv
    have heven : v * u⁻¹ ∈ alternatingGroup α := by
      rw [mem_alternatingGroup, map_mul, map_inv, hv', hodd]
      simp
    simpa using K.mul_mem (hA heven) hu

/-- Local orbit, cycle, and evenness witnesses certify equality with
the alternating group. -/
theorem normalClosure_image_eq_alternatingGroup_of_witnesses
    (hP : IsPreprimitive P α)
    (hsn : s.ncard = n + 1) (hcard : n + 2 < Nat.card α)
    (hfix : H ≤ fixingSubgroup P s)
    (htrans : ∀ x y : α, x ∉ s → y ∉ s → ∃ h : H, (h : P) • x = y)
    (heven : H ≤ (alternatingGroup α).comap P.subtype)
    (hp : p.Prime) (hpcard : p + 3 ≤ Nat.card α)
    {g : Perm α} (hcycle : g.IsCycle) (hsize : g.support.card = p)
    (hg : g ∈ (normalClosure (H : Set P)).map P.subtype) :
    (normalClosure (H : Set P)).map P.subtype = alternatingGroup α :=
  le_antisymm (normalClosure_image_le_alternatingGroup heven)
    (alternatingGroup_le_normalClosure_of_witnesses
      hP hsn hcard hfix htrans hp hpcard hcycle hsize hg)

/-- Local orbit and cycle witnesses, together with an odd element of
the generating subgroup, certify the full symmetric group. -/
theorem normalClosure_image_eq_top_of_witnesses
    (hP : IsPreprimitive P α)
    (hsn : s.ncard = n + 1) (hcard : n + 2 < Nat.card α)
    (hfix : H ≤ fixingSubgroup P s)
    (htrans : ∀ x y : α, x ∉ s → y ∉ s → ∃ h : H, (h : P) • x = y)
    (hp : p.Prime) (hpcard : p + 3 ≤ Nat.card α)
    {g : Perm α} (hcycle : g.IsCycle) (hsize : g.support.card = p)
    (hg : g ∈ (normalClosure (H : Set P)).map P.subtype)
    {u : P} (hu : u ∈ H) (hodd : sign (u : Perm α) = -1) :
    (normalClosure (H : Set P)).map P.subtype = ⊤ := by
  apply eq_top_of_alternatingGroup_le_of_odd
    (alternatingGroup_le_normalClosure_of_witnesses
      hP hsn hcard hfix htrans hp hpcard hcycle hsize hg)
    (mem_map_of_mem P.subtype (le_normalClosure hu)) hodd

end Permutations


end TauCeti
