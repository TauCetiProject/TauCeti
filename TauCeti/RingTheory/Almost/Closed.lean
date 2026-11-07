/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Elements
public import TauCeti.RingTheory.Almost.Hom
public import TauCeti.RingTheory.Almost.Monoidal

import all TauCeti.RingTheory.Almost.Module
import all TauCeti.RingTheory.Almost.Elements

/-!
# Internal Hom of almost modules

For a basic setup `S = (V, m)`, the internal Hom of almost modules `M` and `N` is
the almostification of the `V`-module of morphisms `M ⟶ N`. It is right adjoint
to tensoring with `M`, making almost modules a closed symmetric monoidal category.
In particular tensoring preserves arbitrary colimits, and internal Hom preserves limits.

The construction uses the adjoint triple `(−)_! ⊣ (−)^a ⊣ (−)_*`:
the ordinary tensor–Hom adjunction, placed between these adjunctions, has left
adjoint `N ↦ (M_! ⊗ N_!)^a ≅ M ⊗ N` and right adjoint
`N ↦ Hom_V(M_!, N_*)^a ≅ Hom(M, N)^a`.
For ordinary modules this gives the almost-Hom formula
`alHom(M^a, N^a) ≅ Hom_V(m~ ⊗ M, N)^a`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, §2.2, (2.2.10)–(2.2.11).
* P. Scholze, *Perfectoid spaces*, §4, Proposition 4.5.
-/

public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite TensorProduct

namespace TauCeti.Almost.Module

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- Internal Hom out of `M`: almostify the `V`-modules of morphisms out of `M`. -/
noncomputable def alHom (M : Module S) : Module S ⥤ Module S :=
  (linearCoyoneda V (Module S)).obj (op M) ⋙ toAlmost S

/-- The internal Hom object is the almostification of the module of almost morphisms. -/
@[simp]
theorem alHom_obj (M N : Module S) :
    (alHom S M).obj N = (toAlmost S).obj (ModuleCat.of V (M ⟶ N)) :=
  (rfl)

/-- Internal Hom acts on its target by postcomposition. This is a named rewrite so
generic functor laws still match before the map is expanded. -/
theorem alHom_map {M N N' : Module S} (f : N ⟶ N') :
    (alHom S M).map f = eqToHom (alHom_obj S M N) ≫
      (toAlmost S).map (ModuleCat.ofHom (Linear.rightComp V M f)) ≫
        eqToHom (alHom_obj S M N').symm :=
  (rfl)

/-- Internal Hom is additive in its target. -/
instance alHom_additive (M : Module S) : (alHom S M).Additive :=
  inferInstanceAs (((linearCoyoneda V (Module S)).obj (op M) ⋙ toAlmost S).Additive)

/-- Internal Hom is `V`-linear in its target. -/
instance alHom_linear (M : Module S) : (alHom S M).Linear V :=
  inferInstanceAs (((linearCoyoneda V (Module S)).obj (op M) ⋙ toAlmost S).Linear V)

private noncomputable def shriekTensorToAlmostIso (M : Module S) :
    shriek S ⋙ tensorLeft ((shriek S).obj M) ⋙ toAlmost S ≅ tensorLeft M :=
  Functor.isoWhiskerLeft _ (Functor.Monoidal.commTensorLeft (toAlmost S) _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (adjShriek S).unit).symm _ ≪≫
    Functor.leftUnitor _ ≪≫
    (tensoringLeft (Module S)).mapIso (asIso ((adjShriek S).unit.app M)).symm

private noncomputable def shriekHomElementsEquiv (M N : Module S) :
    ((shriek S).obj M ⟶ (elements S).obj N) ≃ₗ[V] (M ⟶ N) where
  toEquiv := ((adjElements S).homEquiv _ _).symm.trans
    (Iso.homCongr (asIso ((adjShriek S).unit.app M)).symm (Iso.refl N))
  map_add' f g := by
    simp [Adjunction.homEquiv_counit]
  map_smul' c f := by
    simp [Adjunction.homEquiv_counit]

private noncomputable def homElementsIso (M : Module S) :
    elements S ⋙ ihom ((shriek S).obj M) ≅
      (linearCoyoneda V (Module S)).obj (op M) :=
  NatIso.ofComponents (fun N ↦ (shriekHomElementsEquiv S M N).toModuleIso)
    fun {N N'} f ↦ by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun (g : (shriek S).obj M ⟶ (elements S).obj N) ↦ ?_
      -- The source of the component is an ordinary internal Hom, while its target
      -- is a linear coyoneda object; compute their actions on the morphism `g`.
      change (adjShriek S).unit.app M ≫
          ((adjElements S).homEquiv _ _).symm (g ≫ (elements S).map f) =
        ((adjShriek S).unit.app M ≫ ((adjElements S).homEquiv _ _).symm g) ≫ f
      simpa only [Category.assoc] using
        congrArg (fun k ↦ (adjShriek S).unit.app M ≫ k)
          ((adjElements S).homEquiv_naturality_right_symm g f)

/-- The tensor–internal-Hom adjunction for almost modules. -/
noncomputable def alHomAdj (M : Module S) : tensorLeft M ⊣ alHom S M :=
  (((adjShriek S).comp (ihom.adjunction ((shriek S).obj M))).comp (adjElements S)).ofNatIsoLeft
    (shriekTensorToAlmostIso S M) |>.ofNatIsoRight
      (Functor.isoWhiskerRight (homElementsIso S M) (toAlmost S))

/-- Internal Hom is a right adjoint, so in particular it preserves all limits. -/
instance alHom_isRightAdjoint (M : Module S) : (alHom S M).IsRightAdjoint :=
  (alHomAdj S M).isRightAdjoint

/-- Almost modules form a closed symmetric monoidal category, with internal Hom
the almostification of the module of almost morphisms. -/
noncomputable instance monoidalClosed : MonoidalClosed (Module S) where
  closed M := ⟨alHom S M, alHomAdj S M⟩

/-- The chosen internal Hom functor is `alHom`. -/
@[simp]
theorem ihom_eq_alHom (M : Module S) : ihom M = alHom S M :=
  (rfl)

/-- Internal Hom between almostifications is computed by linear maps out of `m~ ⊗ M`. -/
noncomputable def alHomToAlmost (M N : ModuleCat.{u} V) :
    (alHom S ((toAlmost S).obj M)).obj ((toAlmost S).obj N) ≅
      (toAlmost S).obj (ModuleCat.of V (S.tilde ⊗[V] M →ₗ[V] N)) :=
  (toAlmost S).mapIso (homLinearEquiv S M N).toModuleIso

/-- The comparison on almostifications is the almostification of the linear
almost-Hom comparison. This is a named rewrite so generic isomorphism inverse
laws still match before the comparison maps are expanded. -/
theorem alHomToAlmost_hom (M N : ModuleCat.{u} V) :
    (alHomToAlmost S M N).hom =
      eqToHom (alHom_obj S ((toAlmost S).obj M) ((toAlmost S).obj N)) ≫
        (toAlmost S).map (homLinearEquiv S M N).toModuleIso.hom :=
  (rfl)

/-- The inverse comparison almostifies the inverse linear almost-Hom comparison. -/
theorem alHomToAlmost_inv (M N : ModuleCat.{u} V) :
    (alHomToAlmost S M N).inv =
      (toAlmost S).map (homLinearEquiv S M N).toModuleIso.inv ≫
        eqToHom (alHom_obj S ((toAlmost S).obj M) ((toAlmost S).obj N)).symm :=
  (rfl)

end TauCeti.Almost.Module
