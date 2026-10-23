/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FixedPointFree
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# Fixed points through a finite kernel

A surjective homomorphism intertwining two group endomorphisms induces an isomorphism of their
fixed subgroups when its kernel is finite and has no nonidentity fixed point. Neither endomorphism
needs to be invertible. The lifting argument corrects an arbitrary lift by an element of the kernel,
using `MonoidHom.FixedPointFree.commutatorMap_surjective`.
-/

public section

namespace MonoidHom

open TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- A fixed point has a unique fixed lift through an equivariant surjection with finite kernel
whose only fixed point is the identity. -/
theorem existsUnique_fixed_lift_of_finite_ker (ψ : G →* H) {F : G →* G} {F' : H →* H}
    [Finite ψ.ker]
    (hψ : ψ.comp F = F'.comp ψ) (hsurj : Function.Surjective ψ)
    (hker : Disjoint ψ.ker (fixedSubgroup F)) {y : H} (hy : F' y = y) :
    ∃! x : G, F x = x ∧ ψ x = y := by
  have heq (x : G) : ψ (F x) = F' (ψ x) := DFunLike.congr_fun hψ x
  let f : ψ.ker →* ψ.ker := (F.domRestrict ψ.ker).codRestrict ψ.ker fun k ↦ by
    apply MonoidHom.mem_ker.mpr
    rw [MonoidHom.domRestrict_apply, heq, MonoidHom.mem_ker.mp k.property, map_one]
  have hf : FixedPointFree f := by
    intro k hk
    apply Subtype.ext
    -- The restricted map acts by `F` on underlying elements of `G`.
    exact Subgroup.disjoint_def.mp hker k.property
      (TauCeti.mem_fixedSubgroup.mpr (congrArg Subtype.val hk))
  obtain ⟨x, rfl⟩ := hsurj y
  have hd : x / F x ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_div, heq, hy, div_self']
  obtain ⟨k, hk⟩ := hf.commutatorMap_surjective ⟨x / F x, hd⟩
  -- Coercing the kernel equation to `G` replaces the restricted map by `F`.
  have hcorr : (k : G) / F k = x / F x := congrArg Subtype.val hk
  have hfixed : F ((k : G)⁻¹ * x) = (k : G)⁻¹ * x := by
    apply mul_left_cancel (a := (k : G))
    calc
      (k : G) * F ((k : G)⁻¹ * x) = ((k : G) / F k) * F x := by
        rw [map_mul, map_inv, ← mul_assoc, div_eq_mul_inv]
      _ = (x / F x) * F x := by rw [hcorr]
      _ = (k : G) * ((k : G)⁻¹ * x) := by simp
  have himage : ψ ((k : G)⁻¹ * x) = ψ x := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp k.property, inv_one, one_mul]
  refine ⟨(k : G)⁻¹ * x, ⟨hfixed, himage⟩, ?_⟩
  rintro z ⟨hz, hzy⟩
  apply div_eq_one.mp
  apply Subgroup.disjoint_def.mp hker
  · rw [MonoidHom.mem_ker, map_div, hzy, himage, div_self']
  · rw [TauCeti.mem_fixedSubgroup, map_div, hz, hfixed]

/-- Restriction of an equivariant surjection to fixed subgroups, when its finite kernel has
no nonidentity fixed point. Its inverse sends a point to its unique fixed lift. -/
noncomputable def fixedSubgroupCongrOfFiniteKer (ψ : G →* H) {F : G →* G} {F' : H →* H}
    [Finite ψ.ker]
    (hψ : ψ.comp F = F'.comp ψ) (hsurj : Function.Surjective ψ)
    (hker : Disjoint ψ.ker (fixedSubgroup F)) :
    ↥(fixedSubgroup F) ≃* ↥(fixedSubgroup F') := by
  let f : ↥(fixedSubgroup F) →* ↥(fixedSubgroup F') :=
    (ψ.domRestrict (fixedSubgroup F)).codRestrict (fixedSubgroup F') fun x ↦
      map_fixedSubgroup_le ψ hψ ⟨x, x.property, rfl⟩
  apply MulEquiv.ofBijective f
  constructor
  · intro x z hxz
    apply Subtype.ext
    exact (ψ.existsUnique_fixed_lift_of_finite_ker hψ hsurj hker (f x).property).unique
      ⟨x.property, rfl⟩ ⟨z.property, (congrArg Subtype.val hxz).symm⟩
  · intro y
    obtain ⟨x, hx, -⟩ := ψ.existsUnique_fixed_lift_of_finite_ker hψ hsurj hker y.property
    exact ⟨⟨x, hx.1⟩, Subtype.ext hx.2⟩

@[simp]
theorem coe_fixedSubgroupCongrOfFiniteKer_apply (ψ : G →* H) {F : G →* G} {F' : H →* H}
    [Finite ψ.ker]
    (hψ : ψ.comp F = F'.comp ψ) (hsurj : Function.Surjective ψ)
    (hker : Disjoint ψ.ker (fixedSubgroup F)) (x : ↥(fixedSubgroup F)) :
    (ψ.fixedSubgroupCongrOfFiniteKer hψ hsurj hker x : H) = ψ (x : G) := by
  rfl

@[simp]
theorem map_fixedSubgroupCongrOfFiniteKer_symm_apply (ψ : G →* H) {F : G →* G} {F' : H →* H}
    [Finite ψ.ker]
    (hψ : ψ.comp F = F'.comp ψ) (hsurj : Function.Surjective ψ)
    (hker : Disjoint ψ.ker (fixedSubgroup F)) (y : ↥(fixedSubgroup F')) :
    ψ ((ψ.fixedSubgroupCongrOfFiniteKer hψ hsurj hker).symm y : G) = (y : H) :=
  congrArg Subtype.val ((ψ.fixedSubgroupCongrOfFiniteKer hψ hsurj hker).apply_symm_apply y)

end MonoidHom
