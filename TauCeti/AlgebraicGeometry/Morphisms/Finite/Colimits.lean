/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.MorphismProperty
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

/-!
# Finite coproducts of finite morphisms

Schemes with a finite morphism to a fixed scheme `X` are closed under finite coproducts: if
`ι` is finite and every `f i : Y i ⟶ X` is finite, then so is `Sigma.desc f : ∐ Y ⟶ X`
(`AlgebraicGeometry.IsFinite.sigmaDesc`). This includes the empty coproduct, and for binary
coproducts it recovers Mathlib's instance for `coprod.desc f g`, on which the proof rests: finite
coproduct closure in `Over X` is assembled from the binary and the empty case with Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'`.

`AlgebraicGeometry.IsFinite.isClosedUnderColimitsOfShape_discrete` states this as closure of
`MorphismProperty.costructuredArrowObj L @IsFinite` under coproducts indexed by a finite type, in
the shape of Mathlib's
`AlgebraicGeometry.IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete`.
-/
public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Over a fixed scheme `X`, binary coproducts of schemes finite over `X` are finite over `X`. -/
private lemma isClosedUnderBinaryCoproducts_overObj_isFinite (X : Scheme.{u}) :
    (MorphismProperty.overObj @IsFinite (X := X)).IsClosedUnderBinaryCoproducts := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape (fun D _ ↦ colimit.cocone D)
    (fun D _ ↦ colimit.isColimit D) (fun D _ X s hs ↦ ?_) X
  have hdesc : (colimit.isColimit D).desc (Cocone.mk X s) =
      (HasColimit.isoOfNatIso (diagramIsoPair D)).hom ≫
        coprod.desc (s.app ⟨.left⟩) (s.app ⟨.right⟩) := by
    refine colimit.hom_ext fun ⟨j⟩ ↦ ?_
    cases j <;> simp
  have := hs ⟨.left⟩
  have := hs ⟨.right⟩
  rw [hdesc]
  infer_instance

/-- Over a fixed scheme `X`, the empty scheme is finite over `X`. -/
private lemma isClosedUnderColimitsOfShape_pEmpty_overObj_isFinite (X : Scheme.{u}) :
    (MorphismProperty.overObj @IsFinite (X := X)).IsClosedUnderColimitsOfShape
      (Discrete PEmpty.{1}) where
  colimitsOfShape_le Y hY := by
    obtain ⟨t⟩ := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _).mp hY
    have : IsEmpty Y.left := isInitial_iff_isEmpty.mp ⟨t.isInitialObj (Over.forget X) Y⟩
    exact (inferInstance : IsFinite Y.hom)

/-- A morphism out of a finite coproduct of schemes is finite if each of its components is. -/
theorem IsFinite.sigmaDesc {X : Scheme.{u}} {ι : Type*} [Finite ι] {Y : ι → Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} (hf : ∀ i, IsFinite (f i)) : IsFinite (Sigma.desc f) := by
  have := isClosedUnderBinaryCoproducts_overObj_isFinite X
  have := isClosedUnderColimitsOfShape_pEmpty_overObj_isFinite X
  have : (MorphismProperty.overObj @IsFinite (X := X)).IsClosedUnderFiniteCoproducts := .mk'
  -- The cofan of the objects `Over.mk (f i)` with cocone point `Over.mk (Sigma.desc f)` is a
  -- coproduct in `Over X`, since its image in `Scheme` is the coproduct of the `Y i`.
  let c : Cofan fun i ↦ Over.mk (f i) := Cofan.mk (Over.mk (Sigma.desc f))
    fun i ↦ Over.homMk (Sigma.ι Y i)
  have hc : IsColimit c := Cofan.IsColimit.mk _
    (fun s ↦ Over.homMk (Sigma.desc fun i ↦ (s.inj i).left)
      (Sigma.hom_ext _ _ fun i ↦ by simp [c]))
    (fun s i ↦ by ext; simp [c]) fun s m hm ↦ by
      ext1
      exact Sigma.hom_ext _ _ fun i ↦ by simpa [c] using congr_arg CommaMorphism.left (hm i)
  exact (MorphismProperty.overObj @IsFinite).prop_of_isColimit_cofan hc hf

/-- Objects of `CostructuredArrow L X` whose structure morphism is finite are closed under finite
coproducts. -/
instance IsFinite.isClosedUnderColimitsOfShape_discrete {ι : Type*} [Finite ι] {C : Type*}
    [Category* C] [HasColimitsOfShape (Discrete ι) C] (L : C ⥤ Scheme.{u})
    [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (MorphismProperty.costructuredArrowObj L @IsFinite (X := X)).IsClosedUnderColimitsOfShape
      (Discrete ι) :=
  CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ ↦ coproductIsCoproduct' _)
    (fun _ _ _ _ h ↦ IsFinite.sigmaDesc (h ⟨·⟩)) _

end AlgebraicGeometry
