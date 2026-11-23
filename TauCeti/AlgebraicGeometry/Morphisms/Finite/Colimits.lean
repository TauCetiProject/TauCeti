/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Over
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

/-!
# Finite coproducts of finite morphisms

Schemes with a finite morphism to a fixed scheme `X` are closed under finite coproducts: if `ι`
is finite and every `f i : Y i ⟶ X` is finite, then so is `Sigma.desc f : ∐ Y ⟶ X`
(`TauCeti.IsFinite.sigmaDesc`). This includes the empty coproduct, and extends Mathlib's instance
for binary coproducts, which makes `coprod.desc f g` finite when `f` and `g` are.

`TauCeti.IsFinite.isClosedUnderFiniteCoproducts_overObj` states this as closure of
`MorphismProperty.overObj @IsFinite` under finite coproducts in `Over X`.
`TauCeti.IsFinite.isClosedUnderColimitsOfShape_discrete` states it as closure of
`MorphismProperty.costructuredArrowObj L @IsFinite` under coproducts indexed by a finite type
`ι`, for a functor `L : C ⥤ Scheme` such that `C` has coproducts indexed by `ι` and `L` preserves
them. It has the shape of Mathlib's
`AlgebraicGeometry.IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete`.
-/
public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

/-- Over a fixed scheme `X`, binary coproducts of schemes finite over `X` are finite over `X`. -/
private lemma isClosedUnderBinaryCoproducts_overObj_isFinite (X : Scheme.{u}) :
    (MorphismProperty.overObj @IsFinite (X := X)).IsClosedUnderBinaryCoproducts := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape (fun D _ ↦ colimit.cocone D)
    (fun D _ ↦ colimit.isColimit D) (fun D _ X s hs ↦ ?_) X
  have := hs ⟨.left⟩
  have := hs ⟨.right⟩
  have hdesc : (colimit.isColimit D).desc (Cocone.mk X s) =
      (HasColimit.isoOfNatIso (diagramIsoPair D)).hom ≫
        coprod.desc (s.app ⟨.left⟩) (s.app ⟨.right⟩) := by
    rw [HasColimit.isoOfNatIso_hom_desc]
    congr
    ext ⟨_ | _⟩ <;> simp
  rw [hdesc]
  infer_instance

/-- Over a fixed scheme `X`, the empty scheme is finite over `X`. -/
private lemma isClosedUnderColimitsOfShape_pEmpty_overObj_isFinite (X : Scheme.{u}) :
    (MorphismProperty.overObj @IsFinite (X := X)).IsClosedUnderColimitsOfShape
      (Discrete PEmpty.{1}) where
  colimitsOfShape_le Y hY := by
    obtain ⟨t⟩ := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _).mp hY
    have : IsEmpty Y.left := isInitial_iff_isEmpty.mp ⟨t.isInitialObj (Over.forget X) Y⟩
    rw [MorphismProperty.overObj_iff (W := @IsFinite)]
    infer_instance

/-- Schemes finite over a fixed scheme `X` are closed under finite coproducts in `Over X`. -/
instance IsFinite.isClosedUnderFiniteCoproducts_overObj (X : Scheme.{u}) :
    (MorphismProperty.overObj @IsFinite (X := X)).IsClosedUnderFiniteCoproducts := by
  have := isClosedUnderBinaryCoproducts_overObj_isFinite X
  have := isClosedUnderColimitsOfShape_pEmpty_overObj_isFinite X
  exact .mk'

/-- A morphism out of a finite coproduct of schemes is finite if each of its components is. -/
theorem IsFinite.sigmaDesc {X : Scheme.{u}} {ι : Type*} [Finite ι] {Y : ι → Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} (hf : ∀ i, IsFinite (f i)) : IsFinite (Sigma.desc f) :=
  (MorphismProperty.overObj @IsFinite).prop_of_isColimit
    (Over.isColimitLiftCocone _ (Sigma.desc f) (coproductIsCoproduct Y))
    fun ⟨i⟩ ↦ by
      simp only [Over.lift_obj, NatTrans.comp_app, Functor.const_map_app, colimit.cocone_ι,
        colimit.ι_desc, Cofan.mk_ι_app]
      rw [MorphismProperty.overObj_iff (W := @IsFinite)]
      exact hf i

/-- Objects of `CostructuredArrow L X` whose structure morphism is finite are closed under
coproducts indexed by a finite type `ι`, provided that `C` has such coproducts and `L` preserves
them. -/
instance IsFinite.isClosedUnderColimitsOfShape_discrete {ι : Type*} [Finite ι] {C : Type*}
    [Category* C] [HasColimitsOfShape (Discrete ι) C] (L : C ⥤ Scheme.{u})
    [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (MorphismProperty.costructuredArrowObj L @IsFinite (X := X)).IsClosedUnderColimitsOfShape
      (Discrete ι) :=
  CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ ↦ coproductIsCoproduct' _)
    (fun _ _ _ _ h ↦ IsFinite.sigmaDesc (h ⟨·⟩)) _

end TauCeti
