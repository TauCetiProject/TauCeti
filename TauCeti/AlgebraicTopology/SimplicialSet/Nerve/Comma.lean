/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.AlgebraicTopology.SimplicialSet.Comma
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Coslice
public import TauCeti.CategoryTheory.Comma.StructuredArrow.Pullback

/-!
# Nerves of comma categories

The nerve of the ordinary comma category `StructuredArrow b F` is the comma
simplicial set of `nerveMap F` under `b`. The comparison is over the nerve of the
source category and the coslice under `b`, so it identifies the comma diagrams
used in pointwise Kan extension formulas and finality criteria.

The pullback square is obtained from `StructuredArrow.isPullback_proj_pre` by
Mathlib's nerve adjunction, using `CategoryTheory.nerve.cosliceIso` to identify
the nerve of the undercategory with the simplicial coslice.

## References

* J. Lurie, *Higher Topos Theory*, §§1.2.9, 4.3.2–4.3.3 and Theorem 4.1.3.1.
-/

public section

universe u

open SSet CategoryTheory Limits Simplicial

namespace CategoryTheory.Functor

open nerve

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- The nerve of the structured arrow category over `x` is the pullback of the nerve
map of `F` along the simplicial coslice projection at `x`. -/
theorem isPullback_nerveMap_structuredArrow_coslice (F : C ⥤ D) (x : D) :
    IsPullback (nerveMap (StructuredArrow.proj x F))
      (nerveMap (StructuredArrow.pre x F (𝟭 D)) ≫ (cosliceIso x).hom)
      (nerveMap F) (coslice.π (SSet.const (nerveEquiv.symm x) : Δ[0] ⟶ nerve D)) := by
  have : nerveFunctor.{u, u}.IsRightAdjoint := nerveAdjunction.isRightAdjoint
  have h : IsPullback (nerveMap (StructuredArrow.proj x F))
      (nerveMap (StructuredArrow.pre x F (𝟭 D))) (nerveMap F) (nerveMap (Under.forget x)) :=
    (StructuredArrow.isPullback_proj_pre x F (𝟭 D)).map nerveFunctor
  refine h.of_iso (Iso.refl _) (Iso.refl _) (cosliceIso x) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (cosliceIso_hom_comp_π x).symm

/-- The nerve of the ordinary comma category is the simplicial comma construction. -/
noncomputable def nerveCommaIso (F : C ⥤ D) (b : D) :
    nerve (StructuredArrow b F) ≅ SSet.comma (nerveMap F) (nerveEquiv.symm b) :=
  (F.isPullback_nerveMap_structuredArrow_coslice b).isoIsPullback _ _
    (SSet.comma.isPullback _ _)

@[reassoc (attr := simp)]
lemma nerveCommaIso_hom_π (F : C ⥤ D) (b : D) :
    (F.nerveCommaIso b).hom ≫ SSet.comma.π (nerveMap F) (nerveEquiv.symm b) =
      nerveMap (StructuredArrow.proj b F) :=
  (F.isPullback_nerveMap_structuredArrow_coslice b).isoIsPullback_hom_fst _ _ _

@[reassoc (attr := simp)]
lemma nerveCommaIso_hom_toCoslice (F : C ⥤ D) (b : D) :
    (F.nerveCommaIso b).hom ≫ SSet.comma.toCoslice (nerveMap F) (nerveEquiv.symm b) =
      nerveMap (StructuredArrow.pre b F (𝟭 D)) ≫ (cosliceIso b).hom :=
  (F.isPullback_nerveMap_structuredArrow_coslice b).isoIsPullback_hom_snd _ _ _

end CategoryTheory.Functor
