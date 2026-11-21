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

Lifting a free basis gives a test for commutativity of a free group by homomorphisms: if every
homomorphism to a group `Q` with two noncommuting elements has commutative range, the free group
is commutative (`IsFreeGroup.isMulCommutative_of_forall_isMulCommutative_range`). Lyndon's theorem
`IsFreeGroup.isVaught` applies this test with `Q` the dihedral group of order `8`.
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
    obtain ⟨r, hr⟩ := (H.isCyclic_iff_exists_zpowers_eq).mp hcyc
    have hx : x ∈ Subgroup.zpowers r := hr.symm ▸ Subgroup.subset_closure (by simp)
    have hy : y ∈ Subgroup.zpowers r := hr.symm ▸ Subgroup.subset_closure (by simp)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨r, m, n, hm.symm, hn.symm⟩
  · rintro ⟨r, m, n, rfl, rfl⟩
    exact (Commute.refl r).zpow_zpow m n

/-- For commuting elements `x` and `y` of a free group, one of `x`, `y` and `x * y` is a
square. -/
theorem exists_eq_sq_of_commute {x y : G} (h : Commute x y) :
    ∃ z : G, x = z ^ 2 ∨ y = z ^ 2 ∨ x * y = z ^ 2 := by
  obtain ⟨r, m, n, rfl, rfl⟩ := (commute_iff_exists_common_zpow x y).1 h
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Int.even_or_odd m
  · exact ⟨r ^ k, .inl (by rw [pow_two, ← zpow_add])⟩
  obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := Int.even_or_odd n
  · exact ⟨r ^ l, .inr (.inl (by rw [pow_two, ← zpow_add]))⟩
  · refine ⟨r ^ (k + l + 1), .inr (.inr ?_)⟩
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    omega

/-- A free group is commutative as soon as every homomorphism from it to a fixed group `Q`
containing two noncommuting elements has commutative range. -/
theorem isMulCommutative_of_forall_isMulCommutative_range {Q : Type*} [Group Q] {x y : Q}
    (hxy : ¬Commute x y) (h : ∀ π : G →* Q, IsMulCommutative π.range) : IsMulCommutative G := by
  classical
  rcases subsingleton_or_nontrivial (Generators G) with hι | ⟨u, v, huv⟩
  · have := FreeGroup.isMulCommutative_iff_subsingleton.2 hι
    exact (toFreeGroup G).symm.surjective.isMulCommutative
  let π : G →* Q := lift fun i => if i = u then x else if i = v then y else 1
  have := h π
  refine absurd ((commute_iff_eq x y).2 ?_) hxy
  simpa [π, huv.symm] using
    setLike_mul_comm (π.mem_range.2 ⟨of u, rfl⟩) (π.mem_range.2 ⟨of v, rfl⟩)

end IsFreeGroup

namespace FreeGroup

/-- A free group on at least two generators is nonabelian. -/
theorem not_isMulCommutative {α : Type*} [Nontrivial α] : ¬ IsMulCommutative (FreeGroup α) :=
  fun h => not_subsingleton α (isMulCommutative_iff_subsingleton.mp h)

end FreeGroup
