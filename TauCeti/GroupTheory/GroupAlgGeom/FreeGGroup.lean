/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Free `G`-groups

A group `H` receiving the coefficients through `ι : G →* H` is a *free `G`-group* when it is
isomorphic over `G` to `G[Y] = G ∗ F(Y)` for some set `Y` of free generators. Over trivial
coefficients these are the free groups, and `G` itself is the free `G`-group on no generators.
Free `G`-groups are the groups whose `G`-homomorphisms to any target are unconstrained
specialisations of the free generators; they label the leaves of Makanin–Razborov diagrams.

## Main definitions

* `TauCeti.GroupAlgGeom.IsFreeGGroup ι`: `ι : G →* H` exhibits `H` as a free `G`-group.

## Main results

* `TauCeti.GroupAlgGeom.isFreeGGroup_inl`: `G[Y]` is a free `G`-group.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.of_bijective`: a bijective coefficient map exhibits a free
  `G`-group on no generators.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.of_subsingleton`: over trivial coefficients, every free group
  is a free `G`-group.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.exists_gHom_apply_eq`: a free `G`-group has free generators
  which may be sent to arbitrary elements of any group under `G`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.2.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

universe u v

variable {G : Type v} [Group G] {H : Type u} [Group H]

/-- The coefficient map `ι : G →* H` exhibits `H` as a *free `G`-group*: there are a type `Y` and
an isomorphism `G[Y] ≃* H` restricting to `ι` on the coefficients. -/
def IsFreeGGroup (ι : G →* H) : Prop :=
  ∃ (Y : Type u) (e : GX G Y ≃* H), ∀ g, e (inl g) = ι g

theorem isFreeGGroup_iff {ι : G →* H} :
    IsFreeGGroup ι ↔ ∃ (Y : Type u) (e : GX G Y ≃* H), ∀ g, e (inl g) = ι g :=
  Iff.rfl

/-- The free `G`-group `G[Y]` is a free `G`-group. -/
theorem isFreeGGroup_inl (Y : Type (max u v)) : IsFreeGGroup (inl : G →* GX G Y) :=
  ⟨Y, .refl _, fun _ => rfl⟩

namespace IsFreeGGroup

/-- A bijective coefficient map exhibits its target as the free `G`-group on no generators. -/
theorem of_bijective {ι : G →* H} (hι : Function.Bijective ι) : IsFreeGGroup ι :=
  ⟨PEmpty, GX.equivOfIsEmpty.trans (MulEquiv.ofBijective ι hι), fun g => by simp⟩

/-- `G` is the free `G`-group on no generators. -/
protected theorem id (G : Type u) [Group G] : IsFreeGGroup (MonoidHom.id G) :=
  of_bijective Function.bijective_id

/-- Over trivial coefficients, every free group is a free `G`-group. -/
theorem of_subsingleton [Subsingleton G] [IsFreeGroup H] (ι : G →* H) : IsFreeGGroup ι :=
  ⟨IsFreeGroup.Generators H,
    (GX.equivFreeGroup G _).trans (IsFreeGroup.toFreeGroup H).symm, fun g => by
      rw [Subsingleton.elim g 1, map_one, map_one, map_one]⟩

/-- A free `G`-group has a family of free generators: they may be sent to arbitrary elements of
any group `K` receiving the coefficients, by a unique `G`-homomorphism. -/
theorem exists_gHom_apply_eq {ι : G →* H} (h : IsFreeGGroup ι) :
    ∃ (Y : Type u) (y : Y → H), ∀ {K : Type*} [Group K] (κ : G →* K) (v : Y → K),
      ∃! φ : GHom ι κ, ∀ i, φ (y i) = v i := by
  obtain ⟨Y, e, he⟩ := h
  refine ⟨Y, fun i => e (inr (FreeGroup.of i)), fun {K} _ κ v => ?_⟩
  refine ⟨⟨(eval κ v).comp e.symm.toMonoidHom, fun g => ?_⟩, fun i => ?_, fun φ hφ => ?_⟩
  · simp [← he g]
  · simp
  · refine GHom.ext fun x => ?_
    obtain ⟨w, rfl⟩ := e.surjective x
    have hc : ((φ : H →* K).comp e.toMonoidHom).comp inl = κ :=
      MonoidHom.ext fun g => by simp [he g]
    have := DFunLike.congr_fun (eval_eq_of_comp_inl hc) w
    simpa [hφ] using this.symm

end IsFreeGGroup

end TauCeti.GroupAlgGeom
