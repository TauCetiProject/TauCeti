/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Artin.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.CharacterTable.Galois

/-!
# Artin's fixed-point corollary for rational representations

A rational representation of a finite group is determined by the dimensions of its fixed spaces
under cyclic subgroups. In character language the invariant attached to `C ≤ G` is the raw sum

`∑ c : C, χ(c) = |C| · dim V^C`.

This module provides the subgroup character sum and identifies it with the corresponding
fixed-space dimension. Equality of these invariants on every cyclic subgroup determines a
rational representation up to isomorphism, both in character-sum form and in fixed-space form.

## Main result

* `FDRep.nonempty_iso_of_subgroupCharacterSum_eq_cyclic`: two rational representations with
  equal character sums on every cyclic subgroup are isomorphic.
* `FDRep.subgroupCharacterSum`: the character sum over a finite subgroup, with the finite
  structure chosen canonically up to proof irrelevance.
* `FDRep.nonempty_iso_of_finrank_invariants_eq_cyclic`: the equivalent fixed-space-dimension
  formulation.

## References

See J.-P. Serre, *Linear Representations of Finite Groups*, Part II, §9.2.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u

namespace FDRep

/-- The sum of a finite-group character over a subgroup. -/
noncomputable def _root_.FDRep.subgroupCharacterSum {k : Type*} {G : Type u} [Field k] [Group G]
    (X : FDRep k G) (C : Subgroup G) [Finite C] : k := by
  let _ : Fintype C := Fintype.ofFinite C
  exact ∑ c : C, X.character (c : G)

/-- The subgroup character sum is the sum over any supplied `Fintype` structure on the
subgroup. -/
@[simp]
theorem _root_.FDRep.subgroupCharacterSum_eq_sum {k : Type*} {G : Type u} [Field k] [Group G]
    (X : FDRep k G) (C : Subgroup G) [Fintype C] :
    X.subgroupCharacterSum C = ∑ c : C, X.character (c : G) := by
  classical
  unfold FDRep.subgroupCharacterSum
  apply Finset.sum_congr
  · ext
    simp
  · intro
    simp

/-- The character sum over `C` is `|C|` times the dimension of the fixed space of the restricted
representation. -/
theorem _root_.FDRep.subgroupCharacterSum_eq_card_mul_finrank_invariants
    {k : Type*} {G : Type u} [Field k] [Group G]
    (X : FDRep k G) (C : Subgroup G) [Finite C] [Invertible (Nat.card C : k)] :
    X.subgroupCharacterSum C =
      (Nat.card C : k) * Module.finrank k (_root_.Representation.invariants (resFDRep C X).ρ) := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  have hcard : (Nat.card C : k) ≠ 0 := (isUnit_of_invertible _).ne_zero
  have hav := FDRep.average_char_eq_finrank_invariants (resFDRep C X)
  have hsubtype (c : C) : C.subtype c = (c : G) := rfl
  simp_rw [FDRep.character_actionRes, hsubtype] at hav
  rw [X.subgroupCharacterSum_eq_sum]
  calc
    ∑ c : C, X.character (c : G) =
        (Nat.card C : k) * ((Nat.card C : k)⁻¹ * ∑ c : C, X.character (c : G)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    _ = (Nat.card C : k) *
        Module.finrank k (_root_.Representation.invariants (resFDRep C X).ρ) := by rw [hav]

/-- **Artin's fixed-point corollary.** A rational representation of a finite group is determined
by the sums of its character over the cyclic subgroups. Equivalently, since the sum over `C` is
`|C|` times the dimension of the `C`-fixed space, it is determined by those fixed-space
dimensions. -/
theorem _root_.FDRep.nonempty_iso_of_subgroupCharacterSum_eq_cyclic
    {G : Type u} [Group G] [Finite G]
    (V W : FDRep ℚ G)
    (h : ∀ C : Subgroup G, IsCyclic C →
      V.subgroupCharacterSum C = W.subgroupCharacterSum C) :
    Nonempty (V ≅ W) := by
  classical
  apply FDRep.nonempty_iso_of_character_eq V W
  funext g
  have hchar : ∀ n : ℕ, ∀ x : G, orderOf x = n → V.character x = W.character x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      let C := Subgroup.zpowers x
      let _ : Fintype C := Fintype.ofFinite C
      let _ : IsCyclic C := inferInstance
      let generators : Finset C := Finset.univ.filter fun c ↦ orderOf (c : G) = n
      have hsum : ∑ c : C, (V.character (c : G) - W.character (c : G)) = 0 := by
        rw [Finset.sum_sub_distrib, ← V.subgroupCharacterSum_eq_sum,
          ← W.subgroupCharacterSum_eq_sum,
          h C inferInstance, sub_self]
      have hterm (c : C) : V.character (c : G) - W.character (c : G) =
          if orderOf (c : G) = n then V.character x - W.character x else 0 := by
        split_ifs with hc
        · have hzpowers : Subgroup.zpowers (c : G) = Subgroup.zpowers x := by
            have heq := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr c.property) (by
              rw [Nat.card_zpowers, Nat.card_zpowers, hc, hx])
            simpa [C] using heq
          rw [V.character_eq_of_zpowers_eq hzpowers,
            W.character_eq_of_zpowers_eq hzpowers]
        · have hlt : orderOf (c : G) < n := by
            apply lt_of_le_of_ne
            · rw [← hx]
              exact Nat.le_of_dvd (orderOf_pos x) (orderOf_dvd_of_mem_zpowers c.property)
            · exact hc
          rw [ih (orderOf (c : G)) hlt (c : G) rfl, sub_self]
      have hgen : (⟨x, Subgroup.mem_zpowers x⟩ : C) ∈ generators := by
        simp only [generators, Finset.mem_filter, Finset.mem_univ, true_and, hx]
      have hcard : generators.card ≠ 0 := Finset.card_ne_zero.mpr ⟨_, hgen⟩
      have hmul : (generators.card : ℚ) * (V.character x - W.character x) = 0 := by
        have hsum_eq :
            ∑ c : C, (V.character (c : G) - W.character (c : G)) =
              ∑ c : C, if orderOf (c : G) = n then
                V.character x - W.character x else 0 :=
          Finset.sum_congr rfl fun c _ ↦ hterm c
        have hfilter :
            (∑ c : C, if orderOf (c : G) = n then
                V.character x - W.character x else 0) =
              (generators.card : ℚ) * (V.character x - W.character x) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [← hfilter, ← hsum_eq]
        exact hsum
      exact sub_eq_zero.mp <| (mul_eq_zero.mp hmul).resolve_left (Nat.cast_ne_zero.mpr hcard)
  exact hchar (orderOf g) g rfl

/-- **Artin's fixed-point corollary, in invariant-space form.** Two rational representations are
isomorphic when the dimensions of their fixed spaces agree on every cyclic subgroup. -/
theorem _root_.FDRep.nonempty_iso_of_finrank_invariants_eq_cyclic
    {G : Type u} [Group G] [Finite G]
    (V W : FDRep ℚ G)
    (h : ∀ C : Subgroup G, IsCyclic C →
      Module.finrank ℚ (_root_.Representation.invariants (resFDRep C V).ρ) =
        Module.finrank ℚ (_root_.Representation.invariants (resFDRep C W).ρ)) :
    Nonempty (V ≅ W) := by
  apply V.nonempty_iso_of_subgroupCharacterSum_eq_cyclic W
  intro C hC
  let _ : Invertible (Nat.card C : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [V.subgroupCharacterSum_eq_card_mul_finrank_invariants,
    W.subgroupCharacterSum_eq_card_mul_finrank_invariants, h C hC]

end FDRep

end TauCeti
