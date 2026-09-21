/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Bicartesian
public import TauCeti.CategoryTheory.Exact.Stable.Connecting

/-!
# The cone of a morphism in a Frobenius exact category

Let `E` be a Frobenius exact structure with chosen conflations `X ⟶ I(X) ⟶ ΣX`. The **cone** of
a morphism `f : X ⟶ Y` is the pushout

```text
X  --i(X)-->  I(X)
|               |
-f              |
v               v
Y  ------->  cone f
```

of the chosen inflation of `X` along `-f`. The sign is what makes the associated conflation of
the pushout square read

`X --(i(X), f)--> I(X) ⊞ Y --> cone f`,

so that the cone is the cokernel of `(i(X), f)`.

That conflation is the point of the construction. Since `I(X)` is projective-injective, the
biproduct inclusion `Y ⟶ I(X) ⊞ Y` becomes an isomorphism in the projective stable category and
carries `f` to the inflation of the conflation. Thus every morphism of the underlying category
is, up to a canonical isomorphism of its target in the stable category, the inflation of a
conflation, and `f` acquires the standard sequence

`X ⟶ Y ⟶ cone f ⟶ ΣX`

whose last map is the connecting morphism of the cone conflation. This file constructs the cone
together with that sequence, proves that consecutive composites vanish in the stable category,
and makes the cone act on commutative squares.

The cone extends the construction it is modelled on. When `f` is already the inflation of a
conflation `X ⟶ Y ⟶ Z`, the cone of `f` is an extension of `Z` by the projective-injective
`I(X)`, so it represents `Z` in the stable category.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.coneObj`: the cone `cone f` of `f : X ⟶ Y`.
* `TauCeti.ExactStructure.IsFrobenius.coneInclusion`: the map `Y ⟶ cone f`.
* `TauCeti.ExactStructure.IsFrobenius.coneInjectiveMap`: the map `I(X) ⟶ cone f`.
* `TauCeti.ExactStructure.IsFrobenius.coneConnectingMap`: the map `cone f ⟶ ΣX`.
* `TauCeti.ExactStructure.IsFrobenius.coneMap`: the map of cones induced by a commutative
  square.
* `TauCeti.ExactStructure.IsFrobenius.coneComparison`: the map from the cone of the first map of
  a short complex to its third term.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.isPushout_cone`: the defining pushout square, which
  supplies the universal property of the cone.
* `TauCeti.ExactStructure.IsFrobenius.conflation_cone`: the conflation
  `X ⟶ I(X) ⊞ Y ⟶ cone f`.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_coneInflation`: in the stable
  category, the inflation of the cone conflation is `f` followed by the isomorphism
  `Y ≅ I(X) ⊞ Y`.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_comp_coneInclusion`,
  `TauCeti.ExactStructure.IsFrobenius.coneInclusion_comp_coneConnectingMap` and
  `projectiveStableFunctor_map_coneConnectingMap_comp_cokernelMap`:
  consecutive composites of `X ⟶ Y ⟶ cone f ⟶ ΣX ⟶ ΣY` vanish in the stable category.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_connectingMap_cone`: the
  connecting morphism of the cone conflation is `coneConnectingMap f`.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_coneMap_id` and
  `TauCeti.ExactStructure.IsFrobenius.projectiveStableFunctor_map_coneMap_comp`: cone maps
  preserve identities and composition in the stable category.
* `TauCeti.ExactStructure.IsFrobenius.conflation_coneComparison` and
  `TauCeti.ExactStructure.IsFrobenius.isIso_projectiveStableFunctor_map_coneComparison`: the cone
  of the inflation of a conflation is an extension of its third term by `I(X)`, and represents
  that third term in the stable category.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* Theo Bühler, *Exact Categories*, Expositiones Mathematicae **28** (2010), 1–69,
  Proposition 2.12.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius) {X Y : C}

/-- The pushout defining the cone exists, by Quillen's axiom E2 for the inflation `X ⟶ I(X)`. -/
private theorem hasPushout_cone (f : X ⟶ Y) :
    HasPushout (hE.suspensionInflation X) (-f) :=
  E.inflations.hasPushout _ (hE.isInflation_suspensionInflation X)

/-- The **cone** of `f : X ⟶ Y`: the pushout of the chosen inflation `X ⟶ I(X)` along `-f`. -/
noncomputable def coneObj (f : X ⟶ Y) : C :=
  haveI := hE.hasPushout_cone f
  pushout (hE.suspensionInflation X) (-f)

/-- The map from the chosen injective object of `X` to the cone of `f : X ⟶ Y`. -/
noncomputable def coneInjectiveMap (f : X ⟶ Y) : hE.suspensionInjective X ⟶ hE.coneObj f :=
  haveI := hE.hasPushout_cone f
  pushout.inl _ _

/-- The map from the target of `f : X ⟶ Y` to its cone. -/
noncomputable def coneInclusion (f : X ⟶ Y) : Y ⟶ hE.coneObj f :=
  haveI := hE.hasPushout_cone f
  pushout.inr _ _

/-- The cone of `f` is the pushout of the chosen inflation `X ⟶ I(X)` along `-f`. This is the
universal property of the cone. -/
theorem isPushout_cone (f : X ⟶ Y) :
    IsPushout (hE.suspensionInflation X) (-f) (hE.coneInjectiveMap f) (hE.coneInclusion f) :=
  haveI := hE.hasPushout_cone f
  IsPushout.of_hasPushout _ _

/-- The defining square of the cone, with the sign moved onto the injective side. -/
@[reassoc]
theorem suspensionInflation_comp_coneInjectiveMap (f : X ⟶ Y) :
    hE.suspensionInflation X ≫ hE.coneInjectiveMap f = -(f ≫ hE.coneInclusion f) := by
  simpa using (hE.isPushout_cone f).w

/-- The inflation `(i(X), f) : X ⟶ I(X) ⊞ Y` of the cone conflation of `f`. -/
noncomputable abbrev coneInflation (f : X ⟶ Y) : X ⟶ hE.suspensionInjective X ⊞ Y :=
  biprod.lift (hE.suspensionInflation X) f

/-- The deflation `I(X) ⊞ Y ⟶ cone f` of the cone conflation of `f`. -/
noncomputable abbrev coneDeflation (f : X ⟶ Y) :
    hE.suspensionInjective X ⊞ Y ⟶ hE.coneObj f :=
  biprod.desc (hE.coneInjectiveMap f) (hE.coneInclusion f)

/-- The two maps of the cone conflation compose to zero. -/
@[reassoc]
theorem coneInflation_comp_coneDeflation (f : X ⟶ Y) :
    hE.coneInflation f ≫ hE.coneDeflation f = 0 := by
  simp [hE.suspensionInflation_comp_coneInjectiveMap f]

/-- **The cone conflation of `f : X ⟶ Y`**: the cone is the cokernel of the inflation
`(i(X), f) : X ⟶ I(X) ⊞ Y`. -/
theorem conflation_cone (f : X ⟶ Y) :
    E.Conflation (ShortComplex.mk (hE.coneInflation f) (hE.coneDeflation f)
      (hE.coneInflation_comp_coneDeflation f)) := by
  have h := E.conflation_shortComplex_of_isPushout_of_isInflation
    (hE.isInflation_suspensionInflation X) (hE.isPushout_cone f)
  simpa only [CommSq.shortComplex, neg_neg] using h

/-- The connecting map `cone f ⟶ ΣX` of the cone of `f : X ⟶ Y`, induced by the chosen
deflation `I(X) ⟶ ΣX` and the zero map on `Y`. -/
noncomputable def coneConnectingMap (f : X ⟶ Y) : hE.coneObj f ⟶ hE.suspensionObj X :=
  (hE.isPushout_cone f).desc (hE.suspensionDeflation X) 0
    (by simp [(hE.suspensionPresentation X).zero])

/-- The connecting map of the cone restricts on the injective object to the chosen suspension
deflation. -/
@[reassoc (attr := simp)]
theorem coneInjectiveMap_comp_coneConnectingMap (f : X ⟶ Y) :
    hE.coneInjectiveMap f ≫ hE.coneConnectingMap f = hE.suspensionDeflation X :=
  (hE.isPushout_cone f).inl_desc _ _ _

/-- The composite `Y ⟶ cone f ⟶ ΣX` of the cone sequence vanishes. -/
@[reassoc (attr := simp)]
theorem coneInclusion_comp_coneConnectingMap (f : X ⟶ Y) :
    hE.coneInclusion f ≫ hE.coneConnectingMap f = 0 :=
  (hE.isPushout_cone f).inr_desc _ _ _

section Stable

/-- In the projective stable category, the inflation of the cone conflation of `f` is `f`
followed by the isomorphism `Y ≅ I(X) ⊞ Y`. -/
@[simp]
theorem projectiveStableFunctor_map_coneInflation (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (hE.coneInflation f) =
      E.projectiveStableFunctor.map f ≫
        (E.projectiveStableIsoBiprod (hE.isProjective_I (hE.suspensionPresentation X)) Y).hom := by
  have hsplit : hE.coneInflation f - f ≫ biprod.inr =
      hE.suspensionInflation X ≫ biprod.inl := by
    rw [coneInflation, biprod.lift_eq]
    abel
  rw [projectiveStableIsoBiprod_hom, ← Functor.map_comp, ← sub_eq_zero, ← Functor.map_sub,
    hsplit, E.projectiveStableFunctor_map_eq_zero_iff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    (hE.isProjective_I (hE.suspensionPresentation X)) _ _

/-- The composite `X ⟶ Y ⟶ cone f` of the cone sequence vanishes in the projective stable
category: it factors through the injective `I(X)`. -/
@[simp]
theorem projectiveStableFunctor_map_comp_coneInclusion (f : X ⟶ Y) :
    E.projectiveStableFunctor.map f ≫
      E.projectiveStableFunctor.map (hE.coneInclusion f) = 0 := by
  have hfac : f ≫ hE.coneInclusion f = -(hE.suspensionInflation X ≫ hE.coneInjectiveMap f) := by
    rw [hE.suspensionInflation_comp_coneInjectiveMap, neg_neg]
  rw [← Functor.map_comp, hfac, Functor.map_neg, neg_eq_zero,
    E.projectiveStableFunctor_map_eq_zero_iff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    (hE.isProjective_I (hE.suspensionPresentation X)) _ _

/-- The connecting morphism of the cone conflation is the connecting map of the cone. -/
@[simp]
theorem projectiveStableFunctor_map_connectingMap_cone (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (hE.connectingMap (hE.conflation_cone f)) =
      E.projectiveStableFunctor.map (hE.coneConnectingMap f) :=
  hE.projectiveStableFunctor_map_connectingMap_eq (hE.conflation_cone f) biprod.fst
    (hE.coneConnectingMap f) (by simp) (by refine biprod.hom_ext' _ _ ?_ ?_ <;> simp)

/-- The composite `cone f ⟶ ΣX ⟶ ΣY` of the cone sequence vanishes in the projective stable
category: it factors through the injective `I(Y)`. -/
@[simp]
theorem projectiveStableFunctor_map_coneConnectingMap_comp_cokernelMap (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (hE.coneConnectingMap f) ≫
        E.projectiveStableFunctor.map ((hE.suspensionPresentation X).cokernelMap
          (hE.suspensionPresentation Y) f) = 0 := by
  have hw : hE.suspensionInflation X ≫
      (hE.suspensionPresentation X).middleMap (hE.suspensionPresentation Y) f =
      (-f) ≫ (-(hE.suspensionInflation Y)) := by
    rw [InjectivePresentation.i_comp_middleMap, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_neg]
  have hfac : hE.coneConnectingMap f ≫ (hE.suspensionPresentation X).cokernelMap
      (hE.suspensionPresentation Y) f =
      (hE.isPushout_cone f).desc
        ((hE.suspensionPresentation X).middleMap (hE.suspensionPresentation Y) f)
        (-(hE.suspensionInflation Y)) hw ≫ hE.suspensionDeflation Y := by
    refine (hE.isPushout_cone f).hom_ext ?_ ?_
    · simp [InjectivePresentation.p_comp_cokernelMap]
    · simp [(hE.suspensionPresentation Y).zero]
  rw [← Functor.map_comp, hfac, E.projectiveStableFunctor_map_eq_zero_iff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    (hE.isProjective_I (hE.suspensionPresentation Y)) _ _

end Stable

section Functoriality

variable {X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The map of cones induced by a commutative square `f ≫ b = a ≫ f'`. -/
noncomputable def coneMap (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ f') :
    hE.coneObj f ⟶ hE.coneObj f' :=
  (hE.isPushout_cone f).desc
    ((hE.suspensionPresentation X).middleMap (hE.suspensionPresentation X') a ≫
      hE.coneInjectiveMap f')
    (b ≫ hE.coneInclusion f')
    (by
      rw [← Category.assoc, InjectivePresentation.i_comp_middleMap, Category.assoc,
        hE.suspensionInflation_comp_coneInjectiveMap, Preadditive.comp_neg, Preadditive.neg_comp,
        neg_inj, ← Category.assoc, ← w, Category.assoc])

/-- The cone map restricts on the injective objects to the map induced by `a` on the chosen
injective presentations. -/
@[reassoc (attr := simp)]
theorem coneInjectiveMap_comp_coneMap (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ f') :
    hE.coneInjectiveMap f ≫ hE.coneMap a b w =
      (hE.suspensionPresentation X).middleMap (hE.suspensionPresentation X') a ≫
        hE.coneInjectiveMap f' :=
  (hE.isPushout_cone f).inl_desc _ _ _

/-- The cone map commutes with the cone inclusions. -/
@[reassoc (attr := simp)]
theorem coneInclusion_comp_coneMap (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ f') :
    hE.coneInclusion f ≫ hE.coneMap a b w = b ≫ hE.coneInclusion f' :=
  (hE.isPushout_cone f).inr_desc _ _ _

/-- Cone maps preserve identities in the projective stable category. The equality need not hold
before passing to the stable category because the chosen maps between injective presentations need
not preserve identities strictly. -/
@[simp]
theorem projectiveStableFunctor_map_coneMap_id (f : X ⟶ Y) :
    E.projectiveStableFunctor.map
        (hE.coneMap (𝟙 X) (𝟙 Y) (by simp : f ≫ 𝟙 Y = 𝟙 X ≫ f)) =
      𝟙 (E.projectiveStableFunctor.obj (hE.coneObj f)) := by
  let d : hE.coneObj f ⟶ hE.suspensionInjective X :=
    (hE.isPushout_cone f).desc
      ((hE.suspensionPresentation X).middleMap (hE.suspensionPresentation X) (𝟙 X) - 𝟙 _)
      0 (by simp)
  have hdiff :
      hE.coneMap (𝟙 X) (𝟙 Y) (by simp : f ≫ 𝟙 Y = 𝟙 X ≫ f) - 𝟙 _ =
        d ≫ hE.coneInjectiveMap f := by
    refine (hE.isPushout_cone f).hom_ext ?_ ?_
    · simp [d, Preadditive.comp_sub]
    · simp [d, Preadditive.comp_sub]
  rw [← E.projectiveStableFunctor.map_id, ← sub_eq_zero, ← Functor.map_sub, hdiff,
    E.projectiveStableFunctor_map_eq_zero_iff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    (hE.isProjective_I (hE.suspensionPresentation X)) _ _

variable {X'' Y'' : C} {f'' : X'' ⟶ Y''}

/-- Cone maps preserve composition in the projective stable category. The equality need not hold
before passing to the stable category because the chosen maps between injective presentations need
not preserve composition strictly.

This is not a `simp` lemma: the left-hand side mentions neither the intermediate morphism `f'`
nor the two squares `w` and `w'`, so `simp` could never instantiate them. -/
theorem projectiveStableFunctor_map_coneMap_comp (a : X ⟶ X') (b : Y ⟶ Y')
    (a' : X' ⟶ X'') (b' : Y' ⟶ Y'') (w : f ≫ b = a ≫ f')
    (w' : f' ≫ b' = a' ≫ f'') :
    E.projectiveStableFunctor.map
        (hE.coneMap (a ≫ a') (b ≫ b')
          (by rw [← Category.assoc, w, Category.assoc, w', ← Category.assoc])) =
      E.projectiveStableFunctor.map (hE.coneMap a b w) ≫
        E.projectiveStableFunctor.map (hE.coneMap a' b' w') := by
  let d : hE.coneObj f ⟶ hE.suspensionInjective X'' :=
    (hE.isPushout_cone f).desc
      ((hE.suspensionPresentation X).middleMap (hE.suspensionPresentation X'') (a ≫ a') -
        (hE.suspensionPresentation X).middleMap (hE.suspensionPresentation X') a ≫
          (hE.suspensionPresentation X').middleMap (hE.suspensionPresentation X'') a')
      0 (by simp [Preadditive.comp_sub, Category.assoc])
  have hdiff :
      hE.coneMap (a ≫ a') (b ≫ b')
          (by rw [← Category.assoc, w, Category.assoc, w', ← Category.assoc]) -
          hE.coneMap a b w ≫ hE.coneMap a' b' w' =
        d ≫ hE.coneInjectiveMap f'' := by
    refine (hE.isPushout_cone f).hom_ext ?_ ?_
    · simp [d, Preadditive.comp_sub, Category.assoc]
    · simp [d, Preadditive.comp_sub, Category.assoc]
  rw [← E.projectiveStableFunctor.map_comp, ← sub_eq_zero, ← Functor.map_sub, hdiff,
    E.projectiveStableFunctor_map_eq_zero_iff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    (hE.isProjective_I (hE.suspensionPresentation X'')) _ _

/-- The cone map commutes with the connecting maps and the map induced by `a` on the cokernel
terms of the chosen injective presentations. -/
@[reassoc (attr := simp)]
theorem coneMap_comp_coneConnectingMap (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ f') :
    hE.coneMap a b w ≫ hE.coneConnectingMap f' =
      hE.coneConnectingMap f ≫
        (hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation X') a := by
  refine (hE.isPushout_cone f).hom_ext ?_ ?_
  · simp [InjectivePresentation.p_comp_cokernelMap]
  · simp

end Functoriality

section Comparison

variable {S : ShortComplex C}

/-- The comparison from the cone of the first map of a short complex `X ⟶ Y ⟶ Z` to its third
term `Z`, induced by the zero map on `I(X)` and by the second map on `Y`. -/
noncomputable def coneComparison (S : ShortComplex C) : hE.coneObj S.f ⟶ S.X₃ :=
  (hE.isPushout_cone S.f).desc 0 S.g (by simp [S.zero])

/-- The comparison kills the injective object of the cone. -/
@[reassoc (attr := simp)]
theorem coneInjectiveMap_comp_coneComparison (S : ShortComplex C) :
    hE.coneInjectiveMap S.f ≫ hE.coneComparison S = 0 :=
  (hE.isPushout_cone S.f).inl_desc _ _ _

/-- The comparison carries the cone inclusion to the second map of the short complex. -/
@[reassoc (attr := simp)]
theorem coneInclusion_comp_coneComparison (S : ShortComplex C) :
    hE.coneInclusion S.f ≫ hE.coneComparison S = S.g :=
  (hE.isPushout_cone S.f).inr_desc _ _ _

/-- The third term of a kernel–cokernel pair is the cokernel of the injective object inside the
cone of its first map. -/
noncomputable def isColimitConeComparison (hkc : IsKernelCokernelPair S) :
    IsColimit (CokernelCofork.ofπ (hE.coneComparison S)
      (hE.coneInjectiveMap_comp_coneComparison S)) := by
  have := hkc.epi_g
  have hzero : ∀ (W : C) (u : hE.coneObj S.f ⟶ W), hE.coneInjectiveMap S.f ≫ u = 0 →
      S.f ≫ hE.coneInclusion S.f ≫ u = 0 := by
    intro W u hu
    have hfac : S.f ≫ hE.coneInclusion S.f =
        -(hE.suspensionInflation S.X₁ ≫ hE.coneInjectiveMap S.f) := by
      rw [hE.suspensionInflation_comp_coneInjectiveMap, neg_neg]
    rw [← Category.assoc, hfac, Preadditive.neg_comp, Category.assoc, hu, comp_zero, neg_zero]
  refine Cofork.IsColimit.mk _
    (fun c ↦ hkc.desc (hE.coneInclusion S.f ≫ Cofork.π c)
      (hzero _ _ (CokernelCofork.condition c))) (fun c ↦ ?_) (fun c m hm ↦ ?_)
  · refine (hE.isPushout_cone S.f).hom_ext ?_ ?_
    · simp [CokernelCofork.condition c]
    · simp [hkc.g_desc]
  · have hm' : hE.coneComparison S ≫ m = Cofork.π c := hm
    rw [← cancel_epi S.g, hkc.g_desc, ← hE.coneInclusion_comp_coneComparison S,
      Category.assoc, hm']

/-- **The cone of the inflation of a conflation differs from its third term by the chosen
injective object**: `I(X) ⟶ cone S.f ⟶ Z` is a conflation. -/
theorem conflation_coneComparison (hS : E.Conflation S) :
    E.Conflation (ShortComplex.mk (hE.coneInjectiveMap S.f) (hE.coneComparison S)
      (hE.coneInjectiveMap_comp_coneComparison S)) :=
  E.conflation_of_isColimit_of_isInflation
    (hE.isColimitConeComparison (E.isKernelCokernelPair S hS))
    (E.isStableUnderCobaseChange_inflations.of_isPushout (hE.isPushout_cone S.f)
      (E.isInflation_f hS).neg)

/-- **The cone of the inflation of a conflation represents its third term in the projective
stable category**, because it differs from it by a projective-injective summand. -/
theorem isIso_projectiveStableFunctor_map_coneComparison (hS : E.Conflation S) :
    IsIso (E.projectiveStableFunctor.map (hE.coneComparison S)) := by
  let sp := E.splittingOfInjective (hE.conflation_coneComparison hS)
    (hE.suspensionPresentation S.X₁).isInjective
  refine ⟨E.projectiveStableFunctor.map sp.s, ?_, ?_⟩
  · have hid : hE.coneComparison S ≫ sp.s = 𝟙 (hE.coneObj S.f) -
        sp.r ≫ hE.coneInjectiveMap S.f := sp.g_s
    rw [← Functor.map_comp, hid, Functor.map_sub, E.projectiveStableFunctor.map_id,
      sub_eq_self, E.projectiveStableFunctor_map_eq_zero_iff]
    exact ObjectProperty.factorsThrough_comp E.isProjective
      (hE.isProjective_I (hE.suspensionPresentation S.X₁)) _ _
  · rw [← Functor.map_comp, sp.s_g, E.projectiveStableFunctor.map_id]

end Comparison

end ExactStructure.IsFrobenius

end TauCeti
