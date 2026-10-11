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

local instance : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @FormallyUnramified.{u}) (Q := RingHom.FormallyUnramified)

section Nodal

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Restriction along an open immersion preserves the nodal-curve criterion. -/
theorem AtWorstNodalOfRelativeDimensionOne.comp_of_isOpenImmersion
    {f : Y ⟶ Spec (.of R)} (h : AtWorstNodalOfRelativeDimensionOne f)
    (i : X ⟶ Y) [IsOpenImmersion i] :
    AtWorstNodalOfRelativeDimensionOne (i ≫ f) := by
  let : Y.Over (Spec (.of R)) := ⟨f⟩
  let : X.Over (Spec (.of R)) := ⟨i ≫ f⟩
  have : i.IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 (Y ↘ Spec (.of R)) := h.syntomic
  have hs : SyntomicOfRelativeDimension 1 (i ≫ f) :=
    IsZariskiLocalAtSource.comp h.syntomic i
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hs
  refine AtWorstNodalOfRelativeDimensionOne.mk hs ?_
  suffices hsing : FormallyUnramified ((X.singularLocus R).subschemeι ≫ i ≫ f) from hsing
  have H := Scheme.isPullback_singularLocus_of_isOpenImmersion (R := R) i
  have hi := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H
    (inferInstanceAs (IsOpenImmersion i))
  have : FormallyUnramified ((Y.singularLocus R).subschemeι ≫ f) :=
    h.singular_formallyUnramified
  rw [H.w_assoc]
  exact IsZariskiLocalAtSource.comp
    (inferInstanceAs (FormallyUnramified ((Y.singularLocus R).subschemeι ≫ f))) _

/-- The nodal-curve criterion over an affine base can be checked on an open cover of the
source. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_openCover
    {f : Y ⟶ Spec (.of R)} (𝒰 : Y.OpenCover)
    (h : ∀ j, AtWorstNodalOfRelativeDimensionOne (𝒰.f j ≫ f)) :
    AtWorstNodalOfRelativeDimensionOne f := by
  let : Y.Over (Spec (.of R)) := ⟨f⟩
  have hs : SyntomicOfRelativeDimension 1 f :=
    IsZariskiLocalAtSource.of_openCover 𝒰 fun j ↦ (h j).syntomic
  have : SyntomicOfRelativeDimension 1 (Y ↘ Spec (.of R)) := hs
  refine AtWorstNodalOfRelativeDimensionOne.mk hs ?_
  suffices hsing : FormallyUnramified ((Y.singularLocus R).subschemeι ≫ f) from hsing
  refine IsZariskiLocalAtSource.of_openCover
    (𝒰.pullback₁ (Y.singularLocus R).subschemeι) fun j ↦ ?_
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  let : (𝒰.X j).Over (Spec (.of R)) := ⟨𝒰.f j ≫ f⟩
  have : (𝒰.f j).IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 ((𝒰.X j) ↘ Spec (.of R)) := (h j).syntomic
  have : MorphismProperty.RespectsIso @FormallyUnramified.{u} :=
    MorphismProperty.IsLocalAtSource.toRespects
      (P := @FormallyUnramified.{u}) (K := Scheme.zariskiPrecoverage)
  have H := (Scheme.isPullback_singularLocus_of_isOpenImmersion
    (R := R) (𝒰.f j)).flip
  dsimp only [Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @FormallyUnramified.{u})
    H.isoPullback.hom, H.isoPullback_hom_fst_assoc, H.w_assoc]
  simpa only [Category.assoc] using (h j).singular_formallyUnramified

/-- A relative curve over an affine base is nodal if and only if its restrictions to every
member of an open cover are nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_of_openCover
    (f : Y ⟶ Spec (.of R)) (𝒰 : Y.OpenCover) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∀ j, AtWorstNodalOfRelativeDimensionOne (𝒰.f j ≫ f) :=
  ⟨fun h j ↦ h.comp_of_isOpenImmersion (𝒰.f j),
    AtWorstNodalOfRelativeDimensionOne.of_openCover 𝒰⟩

end Nodal

end TauCeti.AlgebraicGeometry
