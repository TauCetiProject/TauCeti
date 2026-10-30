/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Commuting elements of a free group

An abelian subgroup of a free group is cyclic. This gives an intrinsic characterization of
commuting pairs: they are integer powers of a common element. The argument uses the
Nielsen–Schreier theorem and the fact that a free group on two distinct generators is not
abelian. It applies without choosing reduced-word representatives or a finite basis.
-/

public section

namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- A commutative free group is cyclic. -/
theorem isCyclic_of_isMulCommutative [IsMulCommutative G] : IsCyclic G := by
  classical
  let b := IsFreeGroup.basis G
  have h : IsMulCommutative (FreeGroup (IsFreeGroup.Generators G)) :=
    b.repr.surjective.isMulCommutative
  have : Subsingleton (IsFreeGroup.Generators G) :=
    FreeGroup.isMulCommutative_iff_subsingleton.mp h
  have : IsCyclic (FreeGroup (IsFreeGroup.Generators G)) :=
    FreeGroup.isCyclic_iff_subsingleton.mpr inferInstance
  exact isCyclic_of_surjective b.repr.symm.toMonoidHom b.repr.symm.surjective

end IsFreeGroup

namespace Subgroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- Every abelian subgroup of a free group is cyclic, including the trivial subgroup. -/
theorem isCyclic_of_isMulCommutative
    (H : Subgroup G) [IsMulCommutative H] : IsCyclic H := by
  have : IsFreeGroup H := H.isFreeGroupOfIsFreeGroup
  exact IsFreeGroup.isCyclic_of_isMulCommutative

end Subgroup

namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- Two elements of a free group commute exactly when they are integer powers of one element. -/
theorem commute_iff_exists_common_zpow (x y : G) :
    Commute x y ↔ ∃ r : G, ∃ m n : ℤ, x = r ^ m ∧ y = r ^ n := by
  classical
  constructor
  · intro hxy
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    have hp : ({x, y} : Set G).Pairwise Commute :=
      Set.pairwise_pair_of_symm_of_refl.mpr hxy
    have : IsMulCommutative H := Subgroup.isMulCommutative_closure hp
    have hcyc : IsCyclic H := H.isCyclic_of_isMulCommutative
    obtain ⟨r, hr⟩ := (H.isCyclic_iff_exists_zpowers_eq_top).mp hcyc
    have hx : x ∈ Subgroup.zpowers r := hr.symm ▸ Subgroup.subset_closure (by simp)
    have hy : y ∈ Subgroup.zpowers r := hr.symm ▸ Subgroup.subset_closure (by simp)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨r, m, n, hm.symm, hn.symm⟩
  · rintro ⟨r, m, n, rfl, rfl⟩
    exact (Commute.refl r).zpow_zpow m n

end IsFreeGroup
