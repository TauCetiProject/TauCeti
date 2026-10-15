/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Nodal
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth

/-!
# Source locality of nodal relative curves

Over an affine base, the singular subscheme of a relative curve pulls back to the singular
subscheme of every étale neighbourhood, in particular of every open subscheme. Consequently,
the scheme-theoretic nodal criterion is inherited by étale neighbourhoods, and it can be
checked on an open cover of the source. This permits nodal affine charts to be glued,
including the three charts of the blowup of a node.

## Main results

* `AtWorstNodalOfRelativeDimensionOne.comp_of_etale`: an étale neighbourhood of a nodal
  relative curve is nodal.
* `atWorstNodalOfRelativeDimensionOne_iff_of_openCover`: nodality is local on the source for
  open covers.

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

/-- Pulling back along an étale morphism preserves the nodal-curve criterion: the singular
subscheme of the étale source is the base change of the singular subscheme of the target. In
particular this applies to restriction to an open subscheme. -/
theorem AtWorstNodalOfRelativeDimensionOne.comp_of_etale
    {f : Y ⟶ Spec (.of R)} (h : AtWorstNodalOfRelativeDimensionOne f)
    (g : X ⟶ Y) [Etale g] :
    AtWorstNodalOfRelativeDimensionOne (g ≫ f) := by
  let : Y.Over (Spec (.of R)) := ⟨f⟩
  let : X.Over (Spec (.of R)) := ⟨g ≫ f⟩
  have : g.IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 (Y ↘ Spec (.of R)) := h.syntomic
  have : SyntomicOfRelativeDimension 1 f := h.syntomic
  -- An étale morphism is syntomic of relative dimension zero, and dimensions add.
  have hs : SyntomicOfRelativeDimension 1 (g ≫ f) :=
    zero_add 1 ▸ inferInstanceAs (SyntomicOfRelativeDimension (0 + 1) (g ≫ f))
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hs
  refine AtWorstNodalOfRelativeDimensionOne.mk hs ?_
  have H := Scheme.isPullback_singularLocus_subschemeι_of_etale (R := R) g
  have : Etale ((X.singularLocus R).subschemeMap (Y.singularLocus R) g
      (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
        (Scheme.singularLocus_eq_comap_of_etale g).ge)) :=
    MorphismProperty.of_isPullback (P := @Etale) H inferInstance
  have : Unramified ((Y.singularLocus R).subschemeι ≫ f) := h.unramified_singularLocus
  -- The local `Over` instance has structure map `g ≫ f`; its inferred flatness, finite
  -- presentation, and relative dimension proofs agree by proof irrelevance with those in `mk`.
  change Unramified ((X.singularLocus R).subschemeι ≫ g ≫ f)
  rw [H.w_assoc]
  infer_instance

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
  -- The local `Over` instance has structure map `f`; its inferred flatness, finite
  -- presentation, and relative dimension proofs agree by proof irrelevance with those in `mk`.
  suffices hsing : FormallyUnramified ((Y.singularLocus R).subschemeι ≫ f) from
    { toLocallyOfFiniteType := inferInstance, toFormallyUnramified := hsing }
  -- Fix the morphism-property universe so instance search finds Mathlib's locality instance.
  refine IsZariskiLocalAtSource.of_openCover
    (P := (show MorphismProperty Scheme.{u} from @FormallyUnramified.{u}))
    (𝒰.pullback₁ (Y.singularLocus R).subschemeι) fun j ↦ ?_
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  let : (𝒰.X j).Over (Spec (.of R)) := ⟨𝒰.f j ≫ f⟩
  have : (𝒰.f j).IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 ((𝒰.X j) ↘ Spec (.of R)) := (h j).syntomic
  have : MorphismProperty.RespectsIso @FormallyUnramified.{u} :=
    MorphismProperty.IsLocalAtSource.toRespects
      (P := (show MorphismProperty Scheme.{u} from @FormallyUnramified.{u}))
      (K := Scheme.zariskiPrecoverage)
  have H := (Scheme.isPullback_singularLocus_subschemeι_of_etale (R := R) (𝒰.f j)).flip
  -- The cover index and the source of its map depend on these projections. The generated
  -- projection lemmas do not simplify this dependent goal, so reduce just the two wrappers.
  dsimp only [Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @FormallyUnramified.{u})
    H.isoPullback.hom, H.isoPullback_hom_fst_assoc, H.w_assoc]
  simpa only [Category.assoc] using (h j).unramified_singularLocus.toFormallyUnramified

/-- A relative curve over an affine base is nodal if and only if its restrictions to every
member of an open cover are nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_of_openCover
    (f : Y ⟶ Spec (.of R)) (𝒰 : Y.OpenCover) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∀ j, AtWorstNodalOfRelativeDimensionOne (𝒰.f j ≫ f) :=
  ⟨fun h j ↦ h.comp_of_etale (𝒰.f j),
    AtWorstNodalOfRelativeDimensionOne.of_openCover 𝒰⟩

end Nodal

end TauCeti.AlgebraicGeometry
