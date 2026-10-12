/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Bicartesian
public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Exact functors preserve admissible base change

A conflation-exact additive functor preserves pushout squares whose specified map is an
inflation, and dually pullback squares whose specified map is a deflation. The pushout statement
follows by expressing an admissible pushout as a distinguished kernel--cokernel pair on a
biproduct. Additive functors preserve this biproduct, and the image conflation supplies the
cokernel universal property of the image square. The pullback statement follows by duality.

These results let constructions made by Quillen's base-change axioms pass through exact
functors without assuming preservation of arbitrary finite limits or colimits.

See Theo Bühler, *Exact categories*, Section 5, for the exact-functor calculus.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ExactStructure.IsConflationExact

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

/-- A conflation-exact functor preserves a pushout square of an inflation. The square may be
formed along an arbitrary morphism; no preservation of arbitrary pushouts is assumed. -/
theorem map_isPushout (hF : E.IsConflationExact E' F)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  let sq := hsq.toCommSq
  let sq' := F.map_commSq sq
  have hc : E'.Conflation sq'.shortComplex :=
    E'.conflation_of_iso (sq.shortComplexMapIso (F := F))
      (hF.map_conflation (E.conflation_shortComplex_of_isPushout_of_isInflation hf hsq))
  have hp := E'.isKernelCokernelPair sq'.shortComplex hc
  exact IsPushout.of_isColimit' sq'
    (sq'.isColimitEquivIsColimitCokernelCofork.symm hp.gIsCokernel)

/-- A conflation-exact functor preserves a pullback square of a deflation. The square may be
formed along an arbitrary morphism; no preservation of arbitrary pullbacks is assumed. -/
theorem map_isPullback (hF : E.IsConflationExact E' F)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hh : E.IsDeflation h) (hsq : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  have hop : IsPushout h.op i.op f.op g.op := hsq.op.flip
  have hhop : E.op.IsInflation h.op := by simpa using hh
  have hmap := hF.op.map_isPushout hhop hop
  simpa using hmap.unop.flip

end ExactStructure.IsConflationExact

end TauCeti
