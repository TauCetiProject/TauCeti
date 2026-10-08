/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.RegularFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic

/-!
# Functoriality of the algebra of regular functions

A scheme `p : V ⟶ X` over `X` has a commutative `𝒪ₓ`-algebra of regular functions, carried by
the actual pushforward `p_* 𝒪_V` (`AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra`).
This file makes that algebra contravariantly functorial in schemes over `X`: a morphism
`g : V ⟶ W` over `X` pulls back regular functions, giving a morphism of `𝒪ₓ`-algebras
`q_* 𝒪_W ⟶ p_* 𝒪_V`.

The morphism of algebras is the pushforward along `q` of the unit `𝒪_W ⟶ g_* 𝒪_V` of the
function algebra of `g`, transported along the identification `q_* g_* ≅ (g ≫ q)_* = p_*` of lax
monoidal functors, using Mathlib's `Functor.mapCommMon` and `Functor.mapCommMonNatTrans`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap g h`: the morphism of function
  algebras `q_* 𝒪_W ⟶ p_* 𝒪_V` induced by `g : V ⟶ W` with `h : g ≫ q = p`;
* `AlgebraicGeometry.Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply`: on
  sections over `U`, it is the map `Γ(W, q⁻¹ U) ⟶ Γ(V, p⁻¹ U)` induced by `g`;
* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_id` and
  `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_comp`: functoriality.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative
  spectrum).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X V W : Scheme.{u}} {p : V ⟶ X} {q : W ⟶ X}

/-- The morphism of function algebras `q_* 𝒪_W ⟶ p_* 𝒪_V` induced by a morphism `g : V ⟶ W` of
schemes over `X`: pullback of regular functions along `g`. It is the pushforward along `q` of
the unit `𝒪_W ⟶ g_* 𝒪_V` of the function algebra of `g`, followed by the identification
`q_* g_* ≅ (g ≫ q)_* = p_*` of lax monoidal functors. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap (g : V ⟶ W)
    (h : g ≫ q = p) : q.pushforwardStructureAlgebra ⟶ p.pushforwardStructureAlgebra :=
  (Scheme.Modules.pushforward q).mapCommMon.map
      (default : CommMon.trivial W.Modules ⟶ g.pushforwardStructureAlgebra) ≫
    Functor.mapCommMonCompIso.inv.app (CommMon.trivial V.Modules) ≫
    (Functor.mapCommMonNatTrans (Scheme.Modules.pushforwardComp g q).hom).app _ ≫
    (Functor.mapCommMonNatTrans (Scheme.Modules.pushforwardCongr h).hom).app _

/-- As a morphism of modules, the morphism of function algebras induced by `g` is the
pushforward along `q` of the map `𝒪_W ⟶ g_* 𝒪_V` given by `g` on sections, followed by the
identification `q_* g_* ≅ (g ≫ q)_* = p_*`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_hom (g : V ⟶ W)
    (h : g ≫ q = p) :
    (Scheme.Hom.pushforwardStructureAlgebraMap g h).hom.hom =
      (Scheme.Modules.pushforward q).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp g q).hom.app _ ≫
          (Scheme.Modules.pushforwardCongr h).hom.app _ := by
  unfold Scheme.Hom.pushforwardStructureAlgebraMap Scheme.Hom.pushforwardStructureAlgebra
  simp only [CommMon.comp_hom, Functor.mapCommMonNatTrans_app_hom_hom,
    Functor.mapCommMonCompIso_inv_app_hom_hom]
  exact congrArg (· ≫ _)
    ((Scheme.Modules.pushforward q).congr_map (Scheme.Hom.pushforwardStructureAlgebra_one g))

/-- On sections over an open `U` of the base, the morphism of function algebras induced by `g`
is the pullback `Γ(W, q⁻¹ U) ⟶ Γ(V, p⁻¹ U)` of regular functions along `g`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply
    (g : V ⟶ W) (h : g ≫ q = p) (U : X.Opens) (x : Γ(q.pushforwardStructureAlgebra.X, U)) :
    CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) U x =
      (p.pushforwardStructureAlgebraSectionsRingEquiv U).symm
        (g.appLE (q ⁻¹ᵁ U) (p ⁻¹ᵁ U) (by subst h; exact le_rfl)
          (q.pushforwardStructureAlgebraSectionsRingEquiv U x)) := by
  rw [Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply,
    Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply,
    CommMon.sectionsAlgHom_apply, Scheme.Hom.pushforwardStructureAlgebraMap_hom]
  -- On sections over `U`, `pushforwardComp` is the identity, `pushforwardCongr` is the
  -- restriction `Γ(V, (g ≫ q)⁻¹ U) ⟶ Γ(V, p⁻¹ U)` of the structure sheaf, and
  -- `unitToPushforwardObjUnit` is `g.app (q⁻¹ U)`; their composite is `appLE` by definition.
  rfl

/-- The identity of a scheme over `X` induces the identity of its function algebra. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_id :
    Scheme.Hom.pushforwardStructureAlgebraMap (𝟙 V) (Category.id_comp p) = 𝟙 _ := by
  refine CommMon.hom_ext_of_sectionsAlgHom fun U ↦ AlgHom.ext fun x ↦ ?_
  have hid : Scheme.Hom.appLE (𝟙 V) (p ⁻¹ᵁ U) (p ⁻¹ᵁ U) le_rfl = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 V)).trans (Scheme.Hom.id_app (p ⁻¹ᵁ U))
  simp only [Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, hid,
    CommMon.sectionsAlgHom_id, AlgHom.id_apply, CommRingCat.id_apply, RingEquiv.symm_apply_apply]

variable {V' : Scheme.{u}} {p' : V' ⟶ X}

/-- Pullback of regular functions is contravariantly functorial in morphisms over `X`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_comp (g : V' ⟶ V)
    (g' : V ⟶ W) (h : g ≫ p = p') (h' : g' ≫ q = p) :
    Scheme.Hom.pushforwardStructureAlgebraMap (g ≫ g') (by rw [Category.assoc, h', h]) =
      Scheme.Hom.pushforwardStructureAlgebraMap g' h' ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g h := by
  refine CommMon.hom_ext_of_sectionsAlgHom fun U ↦ AlgHom.ext fun x ↦ ?_
  simp only [CommMon.sectionsAlgHom_comp, AlgHom.comp_apply,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, RingEquiv.apply_symm_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end

end TauCeti
