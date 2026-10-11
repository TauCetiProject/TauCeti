/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Nodal

/-!
# Source locality of nodal relative curves

Over an affine base, the singular subscheme of a relative curve restricts to the singular
subscheme of every open subscheme. Consequently, the scheme-theoretic nodal criterion can
be checked on an open cover of the source. This permits nodal affine charts to be glued,
including the three charts of the blowup of a node.

## References

* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u


section Nodal

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Restriction along an open immersion preserves the nodal-curve criterion. -/
theorem AtWorstNodalOfRelativeDimensionOne.isOpenImmersion_comp
    {f : Y ⟶ Spec (.of R)} (h : AtWorstNodalOfRelativeDimensionOne f)
    (i : X ⟶ Y) [IsOpenImmersion i] :
    AtWorstNodalOfRelativeDimensionOne (i ≫ f) := by
  let : Y.Over (Spec (.of R)) := ⟨f⟩
  let : X.Over (Spec (.of R)) := ⟨i ≫ f⟩
  have : i.IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 f := h.syntomic
  have : SyntomicOfRelativeDimension 1 (i ≫ f) :=
    IsZariskiLocalAtSource.comp h.syntomic i
  refine AtWorstNodalOfRelativeDimensionOne.mk inferInstance ?_
  have : Flat (X ↘ Spec (.of R)) := SyntomicOfRelativeDimension.flat 1 (i ≫ f)
  have : LocallyOfFinitePresentation (X ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 (i ≫ f)
  have : PureRelativeDimension 1 (X ↘ Spec (.of R)) :=
    PureRelativeDimension.of_syntomicOfRelativeDimension (i ≫ f)
  have : Flat (Y ↘ Spec (.of R)) := SyntomicOfRelativeDimension.flat 1 f
  have : LocallyOfFinitePresentation (Y ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 f
  have : PureRelativeDimension 1 (Y ↘ Spec (.of R)) :=
    PureRelativeDimension.of_syntomicOfRelativeDimension f
  have H := Scheme.isPullback_singularLocus_of_isOpenImmersion (R := R) i
  have hi := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H
    (inferInstanceAs (IsOpenImmersion i))
  have : FormallyUnramified ((Y.singularLocus R).subschemeι ≫ f) :=
    h.singular_formallyUnramified
  have : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @FormallyUnramified.{u}) (Q := RingHom.FormallyUnramified)
  -- The local `Over` instances identify the structure maps with `f` and `i ≫ f`.
  erw [H.w_assoc]
  exact IsZariskiLocalAtSource.comp
    (inferInstanceAs (FormallyUnramified ((Y.singularLocus R).subschemeι ≫ f))) _

/-- The nodal-curve criterion over an affine base can be checked on an open cover of the
source. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_openCover
    {f : Y ⟶ Spec (.of R)} (𝒰 : Y.OpenCover)
    (h : ∀ j, AtWorstNodalOfRelativeDimensionOne (𝒰.f j ≫ f)) :
    AtWorstNodalOfRelativeDimensionOne f := by
  let : Y.Over (Spec (.of R)) := ⟨f⟩
  have : SyntomicOfRelativeDimension 1 f :=
    IsZariskiLocalAtSource.of_openCover 𝒰 fun j ↦ (h j).syntomic
  refine AtWorstNodalOfRelativeDimensionOne.mk inferInstance ?_
  have : Flat (Y ↘ Spec (.of R)) := SyntomicOfRelativeDimension.flat 1 f
  have : LocallyOfFinitePresentation (Y ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 f
  have : PureRelativeDimension 1 (Y ↘ Spec (.of R)) :=
    PureRelativeDimension.of_syntomicOfRelativeDimension f
  have : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @FormallyUnramified.{u}) (Q := RingHom.FormallyUnramified)
  refine IsZariskiLocalAtSource.of_openCover
    (𝒰.pullback₁ (Y.singularLocus R).subschemeι) fun j ↦ ?_
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  let : (𝒰.X j).Over (Spec (.of R)) := ⟨𝒰.f j ≫ f⟩
  have : (𝒰.f j).IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 (𝒰.f j ≫ f) := (h j).syntomic
  have : Flat ((𝒰.X j) ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.flat 1 (𝒰.f j ≫ f)
  have : LocallyOfFinitePresentation ((𝒰.X j) ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 (𝒰.f j ≫ f)
  have : PureRelativeDimension 1 ((𝒰.X j) ↘ Spec (.of R)) :=
    PureRelativeDimension.of_syntomicOfRelativeDimension (𝒰.f j ≫ f)
  have : MorphismProperty.RespectsIso @FormallyUnramified.{u} :=
    MorphismProperty.IsLocalAtSource.toRespects
      (P := @FormallyUnramified.{u}) (K := Scheme.zariskiPrecoverage)
  have H := (Scheme.isPullback_singularLocus_of_isOpenImmersion
    (R := R) (𝒰.f j)).flip
  -- The pulled-back cover is the chosen pullback; its projections are hidden by the cover
  -- wrappers, so expose that morphism before transporting along the comparison isomorphism.
  change FormallyUnramified
    (pullback.fst (Y.singularLocus R).subschemeι (𝒰.f j) ≫
      (Y.singularLocus R).subschemeι ≫ f)
  erw [← MorphismProperty.cancel_left_of_respectsIso (P := @FormallyUnramified.{u})
    H.isoPullback.hom, H.isoPullback_hom_fst_assoc, H.w_assoc]
  simpa only [Category.assoc] using (h j).singular_formallyUnramified

/-- A relative curve over an affine base is nodal if and only if its restrictions to every
member of an open cover are nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_of_openCover
    (f : Y ⟶ Spec (.of R)) (𝒰 : Y.OpenCover) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∀ j, AtWorstNodalOfRelativeDimensionOne (𝒰.f j ≫ f) :=
  ⟨fun h j ↦ h.isOpenImmersion_comp (𝒰.f j),
    AtWorstNodalOfRelativeDimensionOne.of_openCover 𝒰⟩

end Nodal

end TauCeti.AlgebraicGeometry
