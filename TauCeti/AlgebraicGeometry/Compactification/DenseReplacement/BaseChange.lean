/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import TauCeti.AlgebraicGeometry.Compactification.DenseReplacement.Basic

/-!
# Naturality of dense replacement under base change

The canonical map from the dense replacement after base change to the base change of the
dense replacement is natural in compactification morphisms. Thus changing a compactification
by a refinement commutes with this comparison. We bundle these maps as a natural
transformation, compatible with the canonical maps back to the original compactifications.
For a flat base change it is a natural isomorphism.

The comparison is directed from taking schematic closure after base change to base-changing
the schematic closure. No density preservation is required for its naturality.

## References

* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RA).
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}

/-- A refinement commutes with the dense-replacement base-change comparison, even when
base change does not preserve schematic density. -/
@[reassoc]
theorem denseReplacementBaseChange_naturality {C D : Compactification f} (h : C ⟶ D)
    (g : T ⟶ S) :
    ((denseReplacementFunctor (pullback.snd f g)).map (baseChangeMap h g)).hom ≫
        denseReplacementBaseChange D g =
      denseReplacementBaseChange C g ≫
        baseChangeMap ((denseReplacementFunctor f).map h).hom g := by
  rw [← cancel_mono (baseChangeMap (denseReplacementMap D) g)]
  have hb : baseChangeMap ((denseReplacementFunctor f).map h).hom g ≫
        baseChangeMap (denseReplacementMap D) g =
      baseChangeMap (denseReplacementMap C) g ≫ baseChangeMap h g := by
    have hb := (baseChangeFunctor g).congr_map (denseReplacementFunctor_map_hom_comp h)
    simp only [Functor.map_comp] at hb
    simpa only [baseChangeFunctor_map] using hb
  simp only [Category.assoc, denseReplacementBaseChange_comp,
    denseReplacementFunctor_map_hom_comp]
  rw [hb, denseReplacementBaseChange_comp_assoc]

noncomputable section

/-- The natural comparison from dense replacement after base change to base change after
dense replacement, viewed in the category of all compactifications. -/
def denseReplacementBaseChangeNatTrans (g : T ⟶ S) :
    baseChangeFunctor (f := f) g ⋙ denseReplacementFunctor (pullback.snd f g) ⋙
        (denseCompactificationProperty (pullback.snd f g)).ι ⟶
      denseReplacementFunctor f ⋙ (denseCompactificationProperty f).ι ⋙ baseChangeFunctor g where
  app C := denseReplacementBaseChange C g
  naturality _ _ h := denseReplacementBaseChange_naturality h g

@[simp]
theorem denseReplacementBaseChangeNatTrans_app (g : T ⟶ S) (C : Compactification f) :
    (denseReplacementBaseChangeNatTrans (f := f) g).app C =
      denseReplacementBaseChange C g :=
  (rfl)

/-- The comparison respects the counits, that is, the canonical maps from dense replacements
back to the original compactifications. -/
@[simp]
theorem denseReplacementBaseChangeNatTrans_counit (g : T ⟶ S) :
    denseReplacementBaseChangeNatTrans (f := f) g ≫
        Functor.whiskerRight (denseReplacementAdjunction f).counit (baseChangeFunctor g) =
      Functor.whiskerLeft (baseChangeFunctor g)
        (denseReplacementAdjunction (pullback.snd f g)).counit := by
  ext C
  simp

/-- Flat base change commutes naturally with dense replacement. -/
def denseReplacementBaseChangeNatIso (g : T ⟶ S) [Flat g] :
    baseChangeFunctor (f := f) g ⋙ denseReplacementFunctor (pullback.snd f g) ⋙
        (denseCompactificationProperty (pullback.snd f g)).ι ≅
      denseReplacementFunctor f ⋙ (denseCompactificationProperty f).ι ⋙ baseChangeFunctor g :=
  NatIso.ofComponents (fun C ↦ asIso (denseReplacementBaseChange C g))
    (fun h ↦ denseReplacementBaseChange_naturality h g)

@[simp]
theorem denseReplacementBaseChangeNatIso_hom (g : T ⟶ S) [Flat g] :
    (denseReplacementBaseChangeNatIso (f := f) g).hom =
      denseReplacementBaseChangeNatTrans g := by
  ext C
  rfl

@[simp]
theorem denseReplacementBaseChangeNatIso_inv_app (g : T ⟶ S) [Flat g]
    (C : Compactification f) :
    (denseReplacementBaseChangeNatIso (f := f) g).inv.app C =
      inv (denseReplacementBaseChange C g) :=
  (rfl)

end

end TauCeti.Compactification
