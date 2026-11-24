/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import TauCeti.CategoryTheory.Galois.Topology

/-!
# Changing the fibre functor of the equivalence with finite continuous `Aut F`-sets

For a fibre functor `F` on a Galois category `C`, Mathlib's
`CategoryTheory.PreGaloisCategory.functorToContAction F` is an equivalence from `C` to finite
sets with a continuous action of the fundamental group `Aut F`; it sends `X` to the fibre
`F.obj X`, on which `Aut F` acts by evaluation. This file compares these functors for two fibre
functors, that is, for two base points.

A natural isomorphism `γ : F ≅ F'` (a path between the base points) identifies `Aut F` with
`Aut F'` by conjugation (`CategoryTheory.Iso.continuousConjAut`), and the bijections
`γ.app X : F.obj X ≅ F'.obj X` are equivariant for this identification. So
`functorToContAction F` is isomorphic to `functorToContAction F'` followed by restriction along
`γ.continuousConjAut` (`CategoryTheory.Iso.functorToContActionIso`). Since any two fibre functors
are isomorphic, the equivalence does not depend on the base point up to this conjugation. The
construction uses neither the Galois category nor the fibre functor axioms, so it is stated for
arbitrary functors `F F' : C ⥤ FintypeCat`.

## Main definitions

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
