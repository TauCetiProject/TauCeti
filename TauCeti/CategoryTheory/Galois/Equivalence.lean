/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import TauCeti.CategoryTheory.Galois.Topology

/-!
# The equivalence with finite continuous `G`-sets for a fundamental group `G`

For a fibre functor `F` on a Galois category `C`, Mathlib's
`CategoryTheory.PreGaloisCategory.functorToContAction F` is an equivalence from `C` to finite
sets with a continuous action of the fundamental group `Aut F`; it sends `X` to the fibre
`F.obj X`, on which `Aut F` acts by evaluation. For any fundamental group `G` of `F`
(`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`), such as a Galois group, restricting along
the isomorphism of topological groups `G ≃ₜ* Aut F`
(`CategoryTheory.PreGaloisCategory.toAutContinuousMulEquiv`) gives an equivalence of `C` with finite
continuous `G`-sets in which `G` acts on each fibre through its given action
(`CategoryTheory.PreGaloisCategory.functorToContActionEquivOfIsFundamentalGroup`). This file
also compares the functors `functorToContAction F` for two fibre functors, that is, for two base
points.

A natural isomorphism `γ : F ≅ F'` (a path between the base points) identifies `Aut F` with
`Aut F'` by conjugation (`CategoryTheory.Iso.continuousConjAut`), and the bijections
`γ.app X : F.obj X ≅ F'.obj X` are equivariant for this identification. So
`functorToContAction F` is isomorphic to `functorToContAction F'` followed by restriction along
`γ.continuousConjAut` (`CategoryTheory.Iso.functorToContActionIso`). Since any two fibre functors
are isomorphic, the equivalence does not depend on the base point up to this conjugation. The
construction uses neither the Galois category nor the fibre functor axioms, so it is stated for
arbitrary functors `F F' : C ⥤ FintypeCat`.

## Main definitions

* `CategoryTheory.PreGaloisCategory.functorToContActionEquivOfIsFundamentalGroup F G`: the
  equivalence `C ≌ ContAction FintypeCat G` for a fundamental group `G` of `F`.
* `CategoryTheory.Iso.functorToContActionIso γ`: for `γ : F ≅ F'`, the natural isomorphism
  `functorToContAction F ≅ functorToContAction F' ⋙ ContAction.res _ γ.continuousConjAut`, with
  components `γ.app X`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §5.
* The Stacks Project, Section 58.3 (tag 0BMQ), *Galois categories*.
-/

public section

open CategoryTheory PreGaloisCategory FintypeCatDiscrete

universe u₁ u₂ w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F] (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ X, MulAction G (F.obj X)] [IsFundamentalGroup F G]

/-- **The equivalence with finite continuous `G`-sets.** For a fibre functor `F` on a Galois
category `C` and a fundamental group `G` of `F`, `C` is equivalent to finite sets with a continuous
action of `G`. It is `functorToContAction F` followed by restriction along
`toAutContinuousMulEquiv F G : G ≃ₜ* Aut F`, so it sends `X` to the fibre `F.obj X`, on which `G`
acts through its given action. -/
@[expose] noncomputable def functorToContActionEquivOfIsFundamentalGroup :
    C ≌ ContAction FintypeCat.{w} G :=
  (functorToContAction F).asEquivalence.trans (ContAction.resEquiv _ (toAutContinuousMulEquiv F G))

/-- In `functorToContActionEquivOfIsFundamentalGroup F G`, the finite `G`-set attached to `X` has
underlying set the fibre `F.obj X`. -/
@[simp]
theorem functorToContActionEquivOfIsFundamentalGroup_functor_obj_obj_V (X : C) :
    ((functorToContActionEquivOfIsFundamentalGroup F G).functor.obj X).obj.V = F.obj X :=
  (rfl)

variable {G} in
/-- In `functorToContActionEquivOfIsFundamentalGroup F G`, an element `g` of `G` acts on the fibre
`F.obj X` by its given action. -/
@[simp]
theorem functorToContActionEquivOfIsFundamentalGroup_functor_obj_obj_ρ_apply (X : C) (g : G)
    (a : F.obj X) :
    (((functorToContActionEquivOfIsFundamentalGroup F G).functor.obj X).obj.ρ g).asHom a = g • a :=
  -- `g` acts through `σ = toAutContinuousMulEquiv F G g` by its component at `X`, and `σ` is
  -- `toAut F G g`.
  (congrArg (fun σ : Aut F ↦ σ.asIso.hom.app X a) (toAutContinuousMulEquiv_apply F g)).trans
    (toAut_hom_app_apply _ g a)

/-- On a morphism `f`, the functor of `functorToContActionEquivOfIsFundamentalGroup F G` is the
induced map `F.map f` of fibres. -/
@[simp]
theorem functorToContActionEquivOfIsFundamentalGroup_functor_map_hom_hom {X Y : C} (f : X ⟶ Y) :
    ((functorToContActionEquivOfIsFundamentalGroup F G).functor.map f).hom.hom = F.map f :=
  (rfl)

end CategoryTheory.PreGaloisCategory

namespace CategoryTheory.Iso

variable {C : Type u₁} [Category.{u₂} C] {F F' : C ⥤ FintypeCat.{w}}

/-- **Change of base point.** A natural isomorphism `γ : F ≅ F'` of functors to finite sets, such
as a path between two fibre functors, identifies
`functorToContAction F` with `functorToContAction F'` followed by restriction along conjugation by
`γ`, `Aut F ≃ₜ* Aut F'`. The component at `X` is the bijection `γ.app X` of fibres, which is
equivariant because `γ.conjAut σ` has component `γ.app X ⁻¹ ≫ σ.app X ≫ γ.app X` at `X`. -/
noncomputable def functorToContActionIso (γ : F ≅ F') :
    functorToContAction F ≅
      functorToContAction F' ⋙ ContAction.res _ (γ.continuousConjAut : Aut F →ₜ* Aut F') :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (γ.app X) fun σ ↦ by
      -- Mathlib's `functorToAction` has no lemma for the action of `σ` on a fibre, which is
      -- `σ.asIso.hom.app X` by definition; `ContAction.res` acts through `γ.continuousConjAut`.
      change σ.asIso.hom.app X ≫ γ.hom.app X =
        γ.hom.app X ≫ (γ.continuousConjAut σ).asIso.hom.app X
      simp [conjAut_apply]))
    fun f ↦ by
      ext : 2
      exact γ.hom.naturality f

/-- The component of `γ.functorToContActionIso` at `X` is `γ.app X` on the fibres. -/
@[simp]
lemma functorToContActionIso_hom_app_hom_hom (γ : F ≅ F') (X : C) :
    (γ.functorToContActionIso.hom.app X).hom.hom = γ.hom.app X :=
  (rfl)

/-- The inverse component of `γ.functorToContActionIso` at `X` is `γ.inv.app X` on the fibres. -/
@[simp]
lemma functorToContActionIso_inv_app_hom_hom (γ : F ≅ F') (X : C) :
    (γ.functorToContActionIso.inv.app X).hom.hom = γ.inv.app X :=
  (rfl)

end CategoryTheory.Iso
