/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber

/-!
# Extending finite étale covers from a clopen subscheme

Let `g : T ⟶ S` be a finite étale morphism of schemes. Composing structure morphisms with `g`
sends a finite étale `T`-scheme to a finite étale `S`-scheme; this is the functor
`TauCeti.FiniteEtaleScheme.extend g`, the restriction of Mathlib's `Over.map g`. When `g` is a
monomorphism, the base change of `X ⟶ T ⟶ S` back along `g` is `X` again: the square with sides
`𝟙 X`, `X ⟶ T`, `X ⟶ S` and `g` is a pullback because `g` is a monomorphism. So extension
followed by base change is the identity (`TauCeti.FiniteEtaleScheme.extendCompPullbackIso`), and
the geometric fibre of the extension at `x ≫ g` is the geometric fibre at `x`
(`TauCeti.FiniteEtaleScheme.extendCompFiberIso`).

The main example is the inclusion `U.ι` of a clopen subscheme, which is an open immersion with
closed range, hence a closed immersion and so finite, and étale. For it, `extend U.ι` is the
extension of a cover of `U` by the empty cover of the complement.

## Main definitions

* `TauCeti.FiniteEtaleScheme.extend g`: composition with a finite étale `g : T ⟶ S`, a functor
  from finite étale `T`-schemes to finite étale `S`-schemes.
* `TauCeti.FiniteEtaleScheme.extendCompPullbackIso g`: for a monomorphism `g`, base change along
  `g` after extension is the identity.
* `TauCeti.FiniteEtaleScheme.extendCompFiberIso g x`: for a monomorphism `g`, the geometric
  fibre of the extension at `x ≫ g` is the geometric fibre at `x`.

## Main results

* `TauCeti.FiniteEtaleScheme.isFinite_ι_of_isClosed`: the inclusion of a clopen subscheme is
  finite.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}}

/-- The inclusion of an open subscheme with closed underlying set is finite. -/
instance isFinite_ι_of_isClosed (U : S.Opens) [h : Fact (IsClosed (U : Set S))] : IsFinite U.ι :=
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact h.out)
  inferInstance

/-- **Extension along a finite étale morphism.** A finite étale `T`-scheme `X ⟶ T` gives the
finite étale `S`-scheme `X ⟶ T ⟶ S`; on underlying objects over the bases this is Mathlib's
`Over.map g`. For the inclusion of a clopen subscheme it is extension by the empty cover of the
complement. -/
@[expose] noncomputable def extend (g : T ⟶ S) [IsFinite g] [Etale g] :
    FiniteEtaleScheme T ⥤ FiniteEtaleScheme S :=
  (finiteEtaleSchemeProperty S).lift ((finiteEtaleSchemeProperty T).ι ⋙ Over.map g)
    fun X ↦ (finiteEtaleSchemeProperty_iff _).mpr
      ⟨inferInstanceAs (IsFinite (X.obj.hom ≫ g)), inferInstanceAs (Etale (X.obj.hom ≫ g))⟩

/-- Forgetting finiteness and étaleness, extension is `Over.map g`. -/
@[simp]
theorem extend_comp_ι (g : T ⟶ S) [IsFinite g] [Etale g] :
    extend g ⋙ (finiteEtaleSchemeProperty S).ι = (finiteEtaleSchemeProperty T).ι ⋙ Over.map g :=
  (rfl)

/-- The scheme over `S` underlying an extension is `Over.map g` of the original. -/
@[simp]
theorem extend_obj_obj (g : T ⟶ S) [IsFinite g] [Etale g] (X : FiniteEtaleScheme T) :
    ((extend g).obj X).obj = (Over.map g).obj X.obj :=
  (rfl)

/-- On morphisms, extension is `Over.map g`. -/
@[simp]
theorem extend_map_hom (g : T ⟶ S) [IsFinite g] [Etale g] {X Y : FiniteEtaleScheme T}
    (f : X ⟶ Y) : ((extend g).map f).hom = (Over.map g).map f.hom :=
  (rfl)

/-- For a monomorphism `g`, the unit `X ⟶ g^*(g_! X)` of `Over.map g ⊣ Over.pullback g` is an
isomorphism: the square with sides `𝟙 X`, `X ⟶ T`, `X ⟶ S` and `g` is a pullback. -/
theorem isIso_mapPullbackAdj_unit_app (g : T ⟶ S) [Mono g] (X : Over T) :
    IsIso ((Over.mapPullbackAdj g).unit.app X) := by
  have h : IsPullback (𝟙 X.left) X.hom (X.hom ≫ g) g :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hl : ((Over.mapPullbackAdj g).unit.app X).left = h.isoPullback.hom := by
    apply pullback.hom_ext <;> simp
  have : IsIso ((Over.forget T).map ((Over.mapPullbackAdj g).unit.app X)) := by
    rw [Over.forget_map, hl]
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget T)

/-- **Base change after extension is the identity** for a finite étale monomorphism `g`, such
as the inclusion of a clopen subscheme. The components are the inverses of the unit of
`Over.map g ⊣ Over.pullback g`. -/
noncomputable def extendCompPullbackIso (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g] :
    extend g ⋙ pullback g ≅ 𝟭 _ :=
  (NatIso.ofComponents (F := 𝟭 (FiniteEtaleScheme T)) (G := extend g ⋙ pullback g)
    (fun X ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _ ((Over.mapPullbackAdj g).unit.app X.obj)
        (isIso_mapPullbackAdj_unit_app g X.obj)))
    fun {X Y} (f : X ⟶ Y) ↦ ObjectProperty.hom_ext _
      ((Over.mapPullbackAdj g).unit.naturality f.hom)).symm

/-- The components of `(extendCompPullbackIso g).inv` are those of the unit of
`Over.map g ⊣ Over.pullback g`. -/
@[simp]
theorem extendCompPullbackIso_inv_app_hom (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (X : FiniteEtaleScheme T) :
    ((extendCompPullbackIso g).inv.app X).hom = (Over.mapPullbackAdj g).unit.app X.obj :=
  (rfl)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **Fibres of an extension.** For a finite étale monomorphism `g : T ⟶ S` and a geometric
point `x` of `T`, the geometric fibre at `x ≫ g` of the extension of `X` is the geometric fibre
of `X` at `x`. -/
noncomputable def extendCompFiberIso (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (x : Spec (.of Ω) ⟶ T) : extend g ⋙ fiber (x ≫ g) ≅ fiber x :=
  Functor.isoWhiskerLeft (extend g) (pullbackCompFiberIso g x).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (extendCompPullbackIso g) (fiber x) ≪≫ Functor.leftUnitor _

/-- The components of `(extendCompFiberIso g x).inv` are the fibres of the unit of
`Over.map g ⊣ Over.pullback g`, followed by the comparison `pullbackCompFiberIso`. -/
theorem extendCompFiberIso_inv_app (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    (x : Spec (.of Ω) ⟶ T) (X : FiniteEtaleScheme T) :
    (extendCompFiberIso g x).inv.app X =
      (fiber x).map ((extendCompPullbackIso g).inv.app X) ≫
        (pullbackCompFiberIso g x).hom.app ((extend g).obj X) := by
  simp [extendCompFiberIso, -pullbackCompFiberIso_hom_app]

end TauCeti.FiniteEtaleScheme
