/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import TauCeti.GroupTheory.HaagerupProperty.Basic
import TauCeti.GroupTheory.PositiveDefinite.Basic

/-!
# The Haagerup property of directed unions

The Haagerup property of a discrete group is a local property. If every finite subset of `G` lies
in some subgroup `H i` with the Haagerup property, then `G` has the Haagerup property: an
approximating positive-definite function on `H i`, extended by zero to `G`, is positive definite,
equals `1` at the identity, vanishes at infinity, and is close to `1` on the given finite set.

Consequently the supremum of a directed family of subgroups with the Haagerup property, in
particular an increasing union, has the Haagerup property, and a group has the Haagerup property
exactly when all its finitely generated subgroups do. No countability is needed.

## Main declarations

* `TauCeti.HasHaagerupProperty.of_forall_finset_subset`: a group has the Haagerup property if
  each of its finite subsets lies in a subgroup with the Haagerup property, drawn from a fixed
  family.
* `TauCeti.hasHaagerupProperty_iSup_of_directed`: the supremum of a directed family of subgroups
  with the Haagerup property has the Haagerup property.
* `TauCeti.HasHaagerupProperty.of_directed_of_iSup_eq_top`: a group which is the supremum of a
  directed family of subgroups with the Haagerup property has the Haagerup property.
* `TauCeti.hasHaagerupProperty_iff_forall_fg`: a group has the Haagerup property if and only if
  its finitely generated subgroups do.

## References

* P.-A. Cherix, M. Cowling, P. Jolissaint, P. Julg and A. Valette, *Groups with the Haagerup
  property*, Progress in Mathematics 197, Birkhäuser (2001), Proposition 6.1.1.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §16.1.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- A group `G` has the Haagerup property if, for a family of subgroups `H i` with the Haagerup
property, every finite subset of `G` lies in some `H i`. -/
theorem HasHaagerupProperty.of_forall_finset_subset {ι : Type*} {H : ι → Subgroup G}
    (hH : ∀ i, HasHaagerupProperty (H i)) (h : ∀ s : Finset G, ∃ i, (s : Set G) ⊆ H i) :
    HasHaagerupProperty G := by
  classical
  refine hasHaagerupProperty_iff.mpr fun F ε hε ↦ ?_
  obtain ⟨i, hi⟩ := h F
  obtain ⟨φ, hpd, h1, hlim, hF⟩ := hasHaagerupProperty_iff.mp (hH i) (F.subtype (· ∈ H i)) ε hε
  have hext (x : H i) : Function.extend Subtype.val φ 0 (x : G) = φ x :=
    Subtype.val_injective.extend_apply φ 0 x
  refine ⟨Function.extend Subtype.val φ 0, hpd.extend_subtype, by rw [← (H i).coe_one, hext, h1],
    hlim.extend_cofinite Subtype.val (pure_le_nhds 0), fun g hg ↦ ?_⟩
  rw [hext ⟨g, hi hg⟩]
  exact hF _ (Finset.mem_subtype.mpr hg)

/-- The supremum `⨆ i, H i` of a directed family of subgroups with the Haagerup property has the
Haagerup property. It is the union of the family when the family is nonempty, and the trivial
subgroup when it is empty. -/
theorem hasHaagerupProperty_iSup_of_directed {ι : Type*} {H : ι → Subgroup G}
    (hdir : Directed (· ≤ ·) H) (hH : ∀ i, HasHaagerupProperty (H i)) :
    HasHaagerupProperty ↥(⨆ i, H i) := by
  classical
  obtain hι | hι := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    exact hasHaagerupProperty_of_finite
  refine .of_forall_finset_subset (H := fun i ↦ (H i).subgroupOf (⨆ i, H i))
    (fun i ↦ (hH i).of_injective (Subgroup.subgroupOfEquivOfLe (le_iSup H i)).toMonoidHom
      (MulEquiv.injective _)) fun s ↦ ?_
  have hdir' : Directed (· ⊆ ·) fun i ↦ (H i : Set G) :=
    hdir.mono_comp _ fun _ _ ↦ SetLike.coe_subset_coe.mpr
  obtain ⟨i, hi⟩ :=
      hdir'.exists_mem_subset_of_finset_subset_biUnion (s := s.image Subtype.val) <| by
    rw [Finset.coe_image, ← Subgroup.coe_iSup_of_directed hdir]
    exact Set.image_subset_iff.mpr fun x _ ↦ x.property
  exact ⟨i, fun x hx ↦ Subgroup.mem_subgroupOf.mpr (hi (Finset.mem_image_of_mem _ hx))⟩

/-- A group which is the supremum of a directed family of subgroups with the Haagerup property, for
instance an increasing union of such subgroups, has the Haagerup property. -/
theorem HasHaagerupProperty.of_directed_of_iSup_eq_top {ι : Type*} {H : ι → Subgroup G}
    (hdir : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) (hH : ∀ i, HasHaagerupProperty (H i)) :
    HasHaagerupProperty G :=
  (hasHaagerupProperty_iSup_of_directed hdir hH).of_injective
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.toMonoidHom
    (MulEquiv.injective _)

/-- A group has the Haagerup property if and only if all its finitely generated subgroups do. -/
theorem hasHaagerupProperty_iff_forall_fg :
    HasHaagerupProperty G ↔ ∀ K : Subgroup G, K.FG → HasHaagerupProperty K := by
  refine ⟨fun hG K _ ↦ hG.subgroup K, fun h ↦ ?_⟩
  refine .of_forall_finset_subset (H := fun K : {K : Subgroup G // K.FG} ↦ K.val)
    (fun K ↦ h K.val K.property) fun s ↦ ?_
  exact ⟨⟨Subgroup.closure s, (Group.fg_iff_subgroup_fg _).mp inferInstance⟩,
    Subgroup.subset_closure⟩

end TauCeti
