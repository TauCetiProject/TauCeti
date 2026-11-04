/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Descent of unique subgroup factorizations to fixed points

Suppose `U` and `B` are subgroups of a group, and `n` is an element such that
`U ∩ n B n⁻¹ = 1`. The coordinates `u n b` on the subset `U n B` are then unique.
If an endomorphism preserves `U` and `B` and fixes `n`, a product `u n b` is fixed
if and only if both factors are fixed. Thus the fixed part of this cell is exactly
`Uᶠ n Bᶠ`, with unique coordinates in the two fixed subgroups.

This is the factorization step in fixed-point Bruhat descent: apply it to the
unipotent coordinate subgroup of a cell, a fixed normalizer representative, and
the Borel subgroup. Stability of the coordinate subgroup and existence of the
fixed representative must be proved separately; stability of the cell alone
would not suffice. Neither finiteness nor surjectivity of the endomorphism is
required.

The uniqueness argument reuses `Subgroup.mul_injective_of_disjoint`. The
rank-one matrix version is developed in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Bruhat`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11, Theorem 33.
-/

public section

open scoped Pointwise
open TauCeti

namespace Subgroup

variable {G : Type*} [Group G] (U B : Subgroup G) {n : G}

variable (F : G →* G)
  (hU : ∀ u ∈ U, F u ∈ U) (hB : ∀ b ∈ B, F b ∈ B)
  (hn : F n = n) (h : Disjoint U (B.map (MulAut.conj n).toMonoidHom))

include hU hB hn h

/-- In stable, unique coordinates with a fixed middle element, fixedness of the product
is equivalent to fixedness of each factor. -/
theorem mul_mul_mem_fixedSubgroup_iff (u : U) (b : B) :
    (u : G) * n * b ∈ fixedSubgroup F ↔
      (u : G) ∈ fixedSubgroup F ∧ (b : G) ∈ fixedSubgroup F := by
  constructor
  · intro hx
    have heq : F (u : G) * n * F (b : G) = (u : G) * n * b := by
      simpa only [map_mul, hn] using mem_fixedSubgroup.mp hx
    have hp := U.mul_mul_injective_of_disjoint B h
      (a₁ := (⟨F u, hU u u.property⟩, ⟨F b, hB b b.property⟩))
      (a₂ := (u, b)) heq
    exact ⟨mem_fixedSubgroup.mpr (congrArg (fun p : U × B => (p.1 : G)) hp),
      mem_fixedSubgroup.mpr (congrArg (fun p : U × B => (p.2 : G)) hp)⟩
  · rintro ⟨hu, hb⟩
    rw [mem_fixedSubgroup] at hu hb ⊢
    simp only [map_mul, hu, hb, hn]

/-- Intersecting a cell with the fixed subgroup gives the cell formed from its fixed
factors. The trivial-intersection hypothesis concerns `U` and the conjugate of `B`,
not just `U` and `B`. -/
theorem mul_singleton_mul_inter_fixedSubgroup :
    ((U : Set G) * {n} * (B : Set G)) ∩ (fixedSubgroup F : Set G) =
      ((U ⊓ fixedSubgroup F : Subgroup G) : Set G) * {n} *
        ((B ⊓ fixedSubgroup F : Subgroup G) : Set G) := by
  ext g
  constructor
  · rintro ⟨⟨_, ⟨u, hu, v, hv, rfl⟩, b, hb, rfl⟩, hfix⟩
    have hv' : v = n := Set.mem_singleton_iff.mp hv
    subst v
    obtain ⟨huf, hbf⟩ := (U.mul_mul_mem_fixedSubgroup_iff B F hU hB hn h
      ⟨u, hu⟩ ⟨b, hb⟩).mp hfix
    exact ⟨u * n, ⟨u, ⟨hu, huf⟩, n, rfl, rfl⟩, b, ⟨hb, hbf⟩, rfl⟩
  · rintro ⟨_, ⟨u, ⟨hu, huf⟩, v, hv, rfl⟩, b, ⟨hb, hbf⟩, rfl⟩
    have hv' : v = n := Set.mem_singleton_iff.mp hv
    subst v
    exact ⟨⟨u * n, ⟨u, hu, n, rfl, rfl⟩, b, hb, rfl⟩,
      (U.mul_mul_mem_fixedSubgroup_iff B F hU hB hn h ⟨u, hu⟩ ⟨b, hb⟩).mpr ⟨huf, hbf⟩⟩

/-- Every fixed element of the cell has unique coordinates in the fixed factors. -/
theorem existsUnique_fixed_mul_mul {g : G}
    (hg : g ∈ (U : Set G) * {n} * (B : Set G)) (hfix : F g = g) :
    ∃! p : (U ⊓ fixedSubgroup F : Subgroup G) × (B ⊓ fixedSubgroup F : Subgroup G),
      (p.1 : G) * n * p.2 = g := by
  have hmem : g ∈ ((U ⊓ fixedSubgroup F : Subgroup G) : Set G) * {n} *
      ((B ⊓ fixedSubgroup F : Subgroup G) : Set G) :=
    (U.mul_singleton_mul_inter_fixedSubgroup B F hU hB hn h).subset
      ⟨hg, mem_fixedSubgroup.mpr hfix⟩
  obtain ⟨_, ⟨u, hu, v, hv, rfl⟩, b, hb, rfl⟩ := hmem
  have hv' : v = n := Set.mem_singleton_iff.mp hv
  subst v
  refine ⟨(⟨u, hu⟩, ⟨b, hb⟩), rfl, ?_⟩
  intro q hq
  have hp := U.mul_mul_injective_of_disjoint B h
    (a₁ := (⟨q.1, q.1.property.1⟩, ⟨q.2, q.2.property.1⟩))
    (a₂ := (⟨u, hu.1⟩, ⟨b, hb.1⟩)) hq
  exact Prod.ext (Subtype.ext (congrArg (fun p => (p.1 : G)) hp))
    (Subtype.ext (congrArg (fun p => (p.2 : G)) hp))

end Subgroup
