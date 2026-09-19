/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Conflation
public import TauCeti.CategoryTheory.Exact.Stable.Suspension

/-!
# The connecting morphism of a conflation in a Frobenius stable category

Let `E` be a Frobenius exact structure and let `X ⟶ Y ⟶ Z` be a conflation. The inflation
`X ⟶ I(X)` of the chosen suspension presentation extends along `X ⟶ Y` to a map `Y ⟶ I(X)`,
since `I(X)` is injective, and this extension induces a map `Z ⟶ ΣX` on cokernels. In the
projective stable category the result does not depend on the chosen extension. This is the
connecting morphism of Happel's standard triangle

`X ⟶ Y ⟶ Z ⟶ ΣX`.

This file constructs the connecting morphism, shows that it is independent of choices in the
stable category, that the consecutive composites `Y ⟶ Z ⟶ ΣX` and `Z ⟶ ΣX ⟶ ΣY` vanish there,
and that it is natural in morphisms of conflations. The last fact is packaged as a natural
transformation between functors on the category of conflations. For the chosen suspension
presentation itself the connecting morphism is the identity of `ΣX`, and for a split conflation it
is zero.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.connectingMiddleMap`: a chosen extension `Y ⟶ I(X)`.
* `TauCeti.ExactStructure.IsFrobenius.connectingMap`: the induced map `Z ⟶ ΣX`.
* `TauCeti.ExactStructure.IsFrobenius.stableConnecting`: the natural transformation from the
  third term of a conflation to the suspension of its first term, in the stable category.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_connectingMap_eq`: any map
  induced by an extension to `I(X)` agrees with `connectingMap` in the stable category.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_g_comp_connectingMap` and
  `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_connectingMap_comp_suspensionMap`:
  consecutive composites of the standard triangle vanish in the stable category.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_connectingMap_naturality`:
  naturality with respect to morphisms of conflations.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- A map `h` out of the third term of a conflation `S` becomes zero in the stable category
once `S.g ≫ h` factors as `b ≫ p` through the chosen suspension deflation `p` of some object,
with `b` killing the inflation of `S`: then `h` factors through the injective `I(X)`. -/
private theorem projectiveStableFunctor_map_eq_zero_of_g_comp_eq {S : ShortComplex C}
    (hS : E.Conflation S) {X : C} {h : S.X₃ ⟶ hE.suspensionObj X}
    {b : S.X₂ ⟶ hE.suspensionInjective X} (hb : S.f ≫ b = 0)
    (hh : S.g ≫ h = b ≫ hE.suspensionDeflation X) :
    E.projectiveStableFunctor.map h = 0 := by
  have hkc := E.isKernelCokernelPair S hS
  have := hkc.epi_g
  have ht : h = hkc.desc b hb ≫ hE.suspensionDeflation X := by
    rw [← cancel_epi S.g, hh, ← Category.assoc, hkc.g_desc]
  rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff, ht]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    ((hE.projective_iff_injective _).mpr (hE.suspensionPresentation X).isInjective) _ _

variable {S : ShortComplex C} (hS : E.Conflation S)

/-- A chosen extension `Y ⟶ I(X)` of the suspension inflation `X ⟶ I(X)` along the inflation
`X ⟶ Y` of a conflation `X ⟶ Y ⟶ Z`. -/
noncomputable def connectingMiddleMap : S.X₂ ⟶ hE.suspensionInjective S.X₁ :=
  (hE.suspensionPresentation S.X₁).isInjective.factorThru (E.isInflation_f hS)
    (hE.suspensionInflation S.X₁)

/-- The chosen middle map extends the suspension inflation along the inflation of `S`. -/
@[reassoc (attr := simp)]
theorem f_comp_connectingMiddleMap :
    S.f ≫ hE.connectingMiddleMap hS = hE.suspensionInflation S.X₁ :=
  (hE.suspensionPresentation S.X₁).isInjective.comp_factorThru (E.isInflation_f hS)
    (hE.suspensionInflation S.X₁)

/-- The connecting map `Z ⟶ ΣX` of a conflation `X ⟶ Y ⟶ Z`, induced on cokernels by the chosen
extension `Y ⟶ I(X)`. Its image in the stable category is independent of that choice. -/
noncomputable def connectingMap : S.X₃ ⟶ hE.suspensionObj S.X₁ :=
  (E.isKernelCokernelPair S hS).desc
    (hE.connectingMiddleMap hS ≫ hE.suspensionDeflation S.X₁) (by
      rw [hE.f_comp_connectingMiddleMap_assoc, (hE.suspensionPresentation S.X₁).zero])

/-- The connecting map makes the square on the two deflations commute. -/
@[reassoc (attr := simp)]
theorem g_comp_connectingMap :
    S.g ≫ hE.connectingMap hS = hE.connectingMiddleMap hS ≫ hE.suspensionDeflation S.X₁ :=
  (E.isKernelCokernelPair S hS).g_desc _ _

/-- Any map `Z ⟶ ΣX` induced by some extension `Y ⟶ I(X)` of the suspension inflation agrees
with `connectingMap` in the stable category. -/
theorem projectiveStableFunctor_map_connectingMap_eq
    (a : S.X₂ ⟶ hE.suspensionInjective S.X₁) (δ : S.X₃ ⟶ hE.suspensionObj S.X₁)
    (ha : S.f ≫ a = hE.suspensionInflation S.X₁)
    (hδ : S.g ≫ δ = a ≫ hE.suspensionDeflation S.X₁) :
    E.projectiveStableFunctor.map (hE.connectingMap hS) = E.projectiveStableFunctor.map δ := by
  rw [← sub_eq_zero, ← Functor.map_sub]
  refine hE.projectiveStableFunctor_map_eq_zero_of_g_comp_eq hS
    (b := hE.connectingMiddleMap hS - a) ?_ ?_
  · rw [Preadditive.comp_sub, ha, f_comp_connectingMiddleMap, sub_self]
  · rw [Preadditive.comp_sub, Preadditive.sub_comp, g_comp_connectingMap, hδ]

/-- The composite `Y ⟶ Z ⟶ ΣX` of the standard triangle vanishes in the stable category: it
factors through the injective `I(X)`. -/
@[simp]
theorem projectiveStableFunctor_map_g_comp_connectingMap :
    E.projectiveStableFunctor.map (S.g ≫ hE.connectingMap hS) = 0 := by
  rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff, g_comp_connectingMap]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    ((hE.projective_iff_injective _).mpr (hE.suspensionPresentation S.X₁).isInjective) _ _

/-- The composite `Z ⟶ ΣX ⟶ ΣY` of the standard triangle vanishes in the stable category. -/
@[simp]
theorem projectiveStableFunctor_map_connectingMap_comp_suspensionMap :
    E.projectiveStableFunctor.map (hE.connectingMap hS ≫ hE.suspensionMap S.f) = 0 := by
  refine hE.projectiveStableFunctor_map_eq_zero_of_g_comp_eq hS
    (b := hE.connectingMiddleMap hS ≫ hE.suspensionMiddleMap S.f - hE.suspensionInflation S.X₂)
    ?_ ?_
  · rw [Preadditive.comp_sub, hE.f_comp_connectingMiddleMap_assoc,
      suspensionInflation_comp_suspensionMiddleMap, sub_self]
  · rw [Preadditive.sub_comp, (hE.suspensionPresentation S.X₂).zero, sub_zero,
      g_comp_connectingMap_assoc, suspensionDeflation_comp_suspensionMap, Category.assoc]

/-- The connecting map is natural in morphisms of conflations, in the stable category: for
`φ : S ⟶ T`, the square with `φ.τ₃` and the suspension of `φ.τ₁` commutes. -/
theorem projectiveStableFunctor_map_connectingMap_naturality {T : ShortComplex C}
    (hT : E.Conflation T) (φ : S ⟶ T) :
    E.projectiveStableFunctor.map (φ.τ₃ ≫ hE.connectingMap hT) =
      E.projectiveStableFunctor.map (hE.connectingMap hS ≫ hE.suspensionMap φ.τ₁) := by
  rw [← sub_eq_zero, ← Functor.map_sub]
  refine hE.projectiveStableFunctor_map_eq_zero_of_g_comp_eq hS
    (b := φ.τ₂ ≫ hE.connectingMiddleMap hT -
      hE.connectingMiddleMap hS ≫ hE.suspensionMiddleMap φ.τ₁) ?_ ?_
  · rw [Preadditive.comp_sub, ← φ.comm₁₂_assoc, f_comp_connectingMiddleMap,
      hE.f_comp_connectingMiddleMap_assoc, suspensionInflation_comp_suspensionMiddleMap,
      sub_self]
  · rw [Preadditive.comp_sub, Preadditive.sub_comp, ← φ.comm₂₃_assoc, g_comp_connectingMap,
      g_comp_connectingMap_assoc, suspensionDeflation_comp_suspensionMap, Category.assoc,
      Category.assoc]

/-- For the chosen suspension presentation `X ⟶ I(X) ⟶ ΣX` itself, the connecting map is the
identity of `ΣX` in the stable category. -/
@[simp]
theorem projectiveStableFunctor_map_connectingMap_suspensionPresentation (X : C) :
    E.projectiveStableFunctor.map
        (hE.connectingMap (hE.suspensionPresentation X).conflation) =
      𝟙 _ := by
  rw [hE.projectiveStableFunctor_map_connectingMap_eq _ (𝟙 _) (𝟙 _) (Category.comp_id _)
    (by simp), CategoryTheory.Functor.map_id]

/-- The connecting map of a split conflation is zero in the stable category. -/
theorem projectiveStableFunctor_map_connectingMap_eq_zero_of_splitting (s : S.Splitting) :
    E.projectiveStableFunctor.map (hE.connectingMap hS) = 0 := by
  rw [hE.projectiveStableFunctor_map_connectingMap_eq hS (s.r ≫ hE.suspensionInflation S.X₁) 0
    (by rw [s.f_r_assoc]) (by
      rw [comp_zero, Category.assoc, (hE.suspensionPresentation S.X₁).zero, comp_zero]),
    Functor.map_zero]

/-- The connecting maps of all conflations, as a natural transformation from the third term to
the suspension of the first term, both taken in the stable category. -/
noncomputable def stableConnecting :
    ConflationClass.ConflationCategory.π₃ E.toConflationClass ⋙ E.projectiveStableFunctor ⟶
      ConflationClass.ConflationCategory.π₁ E.toConflationClass ⋙ hE.suspensionToStable where
  app S := E.projectiveStableFunctor.map (hE.connectingMap S.property) ≫
    eqToHom (hE.suspensionToStable_obj S.obj.X₁).symm
  naturality S T φ := by
    -- The functors `π₁` and `π₃` evaluate to `S.obj.X₁` and `S.obj.X₃` only after unfolding,
    -- so the square is proved in those terms and then used at the definitionally equal goal.
    have h : E.projectiveStableFunctor.map φ.hom.τ₃ ≫
        E.projectiveStableFunctor.map (hE.connectingMap T.property) ≫
          eqToHom (hE.suspensionToStable_obj T.obj.X₁).symm =
        (E.projectiveStableFunctor.map (hE.connectingMap S.property) ≫
          eqToHom (hE.suspensionToStable_obj S.obj.X₁).symm) ≫
            hE.suspensionToStable.map φ.hom.τ₁ := by
      have key :=
        hE.projectiveStableFunctor_map_connectingMap_naturality S.property T.property φ.hom
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at key
      simp only [suspensionToStable_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, reassoc_of% key]
    exact h

/-- The component of `stableConnecting` at a conflation is its connecting map, read in the
stable category. -/
@[simp]
theorem stableConnecting_app (S : E.ConflationCategory) :
    hE.stableConnecting.app S = E.projectiveStableFunctor.map (hE.connectingMap S.property) ≫
      eqToHom (hE.suspensionToStable_obj S.obj.X₁).symm :=
  (rfl)

end ExactStructure.IsFrobenius

end TauCeti
