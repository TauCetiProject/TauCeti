/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Composition with a finite étale morphism and extension of covers

Let `g : T ⟶ S` be a finite étale morphism of schemes. Composing structure morphisms with `g`
sends a finite étale `T`-scheme to a finite étale `S`-scheme; this is the functor
`TauCeti.FiniteEtaleScheme.map g`, the restriction of Mathlib's `Over.map g`. When `g` is a
monomorphism, the base change of `X ⟶ T ⟶ S` back along `g` is `X` again: the square with sides
`𝟙 X`, `X ⟶ T`, `X ⟶ S` and `g` is a pullback because `g` is a monomorphism (Tau Ceti's
`CategoryTheory.Over.isIso_mapPullbackAdj_unit_app`). So for a monomorphism `g`, the functor
`map g` extends covers of `T` to covers of `S`: base change after it is the identity
(`TauCeti.FiniteEtaleScheme.mapCompPullbackIso`), and the geometric fibre of `(map g).obj X` at
`x ≫ g` is the geometric fibre of `X` at `x` (`TauCeti.FiniteEtaleScheme.mapCompFiberIso`).

The main example is the inclusion `U.ι` of a clopen subscheme, which is an open immersion with
closed range, hence a closed immersion and so finite, and étale; for `U` with
`Fact (IsClosed (U : Set S))` these are instances, through
`AlgebraicGeometry.Scheme.Opens.isClosedImmersion_ι_of_fact_isClosed` in
`TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic`. For it, `map U.ι` is the
extension of a cover of `U` by the empty cover of the complement.

## Main definitions

* `TauCeti.FiniteEtaleScheme.map g`: composition with a finite étale `g : T ⟶ S`, a functor
  from finite étale `T`-schemes to finite étale `S`-schemes.
* `TauCeti.FiniteEtaleScheme.mapPullbackAdj g`: `map g` is left adjoint to base change along
  `g`; for a monomorphism `g` its unit is the inverse of `mapCompPullbackIso g`
  (`mapCompPullbackIso_inv`).
* `TauCeti.FiniteEtaleScheme.mapCompPullbackIso g`: for a monomorphism `g`, base change along
  `g` after `map g` is the identity.
* `TauCeti.FiniteEtaleScheme.mapCompFiberIso g x`: for a monomorphism `g`, the geometric
  fibre of `(map g).obj X` at `x ≫ g` is the geometric fibre of `X` at `x`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}}

/-- **Composition with a finite étale morphism.** A finite étale `T`-scheme `X ⟶ T` gives the
finite étale `S`-scheme `X ⟶ T ⟶ S`; on underlying objects over the bases this is Mathlib's
`Over.map g`. For a monomorphism `g`, such as the inclusion of a clopen subscheme, it extends
covers of `T` to covers of `S`; for the clopen inclusion, by the empty cover of the complement. -/
@[expose] noncomputable def map (g : T ⟶ S) [IsFinite g] [Etale g] :
    FiniteEtaleScheme T ⥤ FiniteEtaleScheme S :=
  (finiteEtaleSchemeProperty S).lift ((finiteEtaleSchemeProperty T).ι ⋙ Over.map g)
    fun X ↦ (finiteEtaleSchemeProperty_iff _).mpr
      ⟨inferInstanceAs (IsFinite (X.obj.hom ≫ g)), inferInstanceAs (Etale (X.obj.hom ≫ g))⟩

/-- Forgetting finiteness and étaleness, `map g` is `Over.map g`. -/
@[simp]
theorem map_comp_ι (g : T ⟶ S) [IsFinite g] [Etale g] :
    map g ⋙ (finiteEtaleSchemeProperty S).ι = (finiteEtaleSchemeProperty T).ι ⋙ Over.map g :=
  (rfl)

/-- The scheme over `S` underlying `(map g).obj X` is `Over.map g` of the original. -/
@[simp]
theorem map_obj_obj (g : T ⟶ S) [IsFinite g] [Etale g] (X : FiniteEtaleScheme T) :
    ((map g).obj X).obj = (Over.map g).obj X.obj :=
  (rfl)

/-- On morphisms, `map g` is `Over.map g`. -/
@[simp]
theorem map_map_hom (g : T ⟶ S) [IsFinite g] [Etale g] {X Y : FiniteEtaleScheme T}
    (f : X ⟶ Y) : ((map g).map f).hom = (Over.map g).map f.hom :=
  (rfl)

/-- **Base change after `map g` is the identity** for a finite étale monomorphism `g`, such
as the inclusion of a clopen subscheme. The components are the inverses of the unit of
`Over.map g ⊣ Over.pullback g`. -/
noncomputable def mapCompPullbackIso (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g] :
    map g ⋙ pullback g ≅ 𝟭 _ :=
  (NatIso.ofComponents (F := 𝟭 (FiniteEtaleScheme T)) (G := map g ⋙ pullback g)
    (fun X ↦ ObjectProperty.isoMk _
      (asIso ((Over.mapPullbackAdj g).unit.app X.obj) :))
    fun {X Y} (f : X ⟶ Y) ↦ ObjectProperty.hom_ext _
      ((Over.mapPullbackAdj g).unit.naturality f.hom)).symm

/-- The components of `(mapCompPullbackIso g).inv` are those of the unit of
`Over.map g ⊣ Over.pullback g`. -/
@[simp]
theorem mapCompPullbackIso_inv_app_hom (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (X : FiniteEtaleScheme T) :
    ((mapCompPullbackIso g).inv.app X).hom = (Over.mapPullbackAdj g).unit.app X.obj :=
  (rfl)

/-- The components of `(mapCompPullbackIso g).hom` are the inverses of those of the unit of
`Over.map g ⊣ Over.pullback g`. -/
@[simp]
theorem mapCompPullbackIso_hom_app_hom (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (X : FiniteEtaleScheme T) :
    ((mapCompPullbackIso g).hom.app X).hom = inv ((Over.mapPullbackAdj g).unit.app X.obj) :=
  (rfl)

/-- **Extension is left adjoint to base change.** For a finite étale `g : T ⟶ S`, composition
with `g` is left adjoint to base change along `g`; this is Mathlib's `Over.mapPullbackAdj g`
restricted to finite étale schemes. -/
noncomputable def mapPullbackAdj (g : T ⟶ S) [IsFinite g] [Etale g] : map g ⊣ pullback g :=
  (Over.mapPullbackAdj g).restrictFullyFaithful (finiteEtaleSchemeProperty T).fullyFaithfulι
    (finiteEtaleSchemeProperty S).fullyFaithfulι (eqToIso (map_comp_ι g).symm)
    (eqToIso (pullback_comp_ι g).symm)

/-- The components of the unit of `map g ⊣ pullback g` are those of the unit of
`Over.map g ⊣ Over.pullback g`. -/
@[simp]
theorem mapPullbackAdj_unit_app_hom (g : T ⟶ S) [IsFinite g] [Etale g] (X : FiniteEtaleScheme T) :
    ((mapPullbackAdj g).unit.app X).hom = (Over.mapPullbackAdj g).unit.app X.obj := by
  rw [← ObjectProperty.ι_map, mapPullbackAdj, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
  -- The remaining `eqToHom` is an identity: `map_comp_ι` and `pullback_comp_ι` hold by `rfl`.
  exact Category.comp_id _

/-- The components of the counit of `map g ⊣ pullback g` are those of the counit of
`Over.map g ⊣ Over.pullback g`. -/
@[simp]
theorem mapPullbackAdj_counit_app_hom (g : T ⟶ S) [IsFinite g] [Etale g]
    (Y : FiniteEtaleScheme S) :
    ((mapPullbackAdj g).counit.app Y).hom = (Over.mapPullbackAdj g).counit.app Y.obj := by
  rw [← ObjectProperty.ι_map, mapPullbackAdj, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans_assoc]
  -- The remaining `eqToHom` is an identity: `map_comp_ι` and `pullback_comp_ι` hold by `rfl`.
  exact Category.id_comp _

/-- For a finite étale monomorphism `g`, the inverse of `mapCompPullbackIso g` is the unit of
`map g ⊣ pullback g`. Not `@[simp]`: the components of both sides already have the same simp
normal form, by `mapCompPullbackIso_inv_app_hom` and `mapPullbackAdj_unit_app_hom`. -/
theorem mapCompPullbackIso_inv (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g] :
    (mapCompPullbackIso g).inv = (mapPullbackAdj g).unit := by
  ext X : 3
  rw [mapCompPullbackIso_inv_app_hom, mapPullbackAdj_unit_app_hom]

/-- For a finite étale monomorphism `g`, the unit of `map g ⊣ pullback g` is an isomorphism:
`map g` is fully faithful. -/
instance isIso_mapPullbackAdj_unit (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g] :
    IsIso (mapPullbackAdj g).unit :=
  mapCompPullbackIso_inv g ▸ inferInstance

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **Fibres of an extension.** For a finite étale monomorphism `g : T ⟶ S` and a geometric
point `x` of `T`, the geometric fibre at `x ≫ g` of `(map g).obj X` is the geometric fibre of
`X` at `x`. -/
noncomputable def mapCompFiberIso (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (x : Spec (.of Ω) ⟶ T) : map g ⋙ fiber (x ≫ g) ≅ fiber x :=
  Functor.isoWhiskerLeft (map g) (pullbackCompFiberIso g x).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (mapCompPullbackIso g) (fiber x) ≪≫ Functor.leftUnitor _

/-- The components of `(mapCompFiberIso g x).inv` are the fibres of the unit of
`Over.map g ⊣ Over.pullback g`, followed by the comparison `pullbackCompFiberIso`. -/
@[simp]
theorem mapCompFiberIso_inv_app (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (x : Spec (.of Ω) ⟶ T) (X : FiniteEtaleScheme T) :
    (mapCompFiberIso g x).inv.app X =
      (fiber x).map ((mapCompPullbackIso g).inv.app X) ≫
        (pullbackCompFiberIso g x).hom.app ((map g).obj X) := by
  simp [mapCompFiberIso, -pullbackCompFiberIso_hom_app]

/-- The components of `(mapCompFiberIso g x).hom` are the comparison `pullbackCompFiberIso`,
followed by the fibres of the inverse of the unit of `Over.map g ⊣ Over.pullback g`. -/
@[simp]
theorem mapCompFiberIso_hom_app (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (x : Spec (.of Ω) ⟶ T) (X : FiniteEtaleScheme T) :
    (mapCompFiberIso g x).hom.app X =
      (pullbackCompFiberIso g x).inv.app ((map g).obj X) ≫
        (fiber x).map ((mapCompPullbackIso g).hom.app X) := by
  simp [mapCompFiberIso, -pullbackCompFiberIso_inv_app]

end TauCeti.FiniteEtaleScheme
