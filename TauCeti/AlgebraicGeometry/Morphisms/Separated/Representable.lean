/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Separatedness from the diagonal of a represented functor

A scheme representing a presheaf on schemes over a base is separated over that base whenever
the diagonal of the presheaf is representable by closed immersions.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A scheme representing a presheaf with diagonal representable by closed immersions is
separated over the base. -/
theorem isSeparated_of_representableBy_of_relative_diag {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {H : Over S}
    (h : MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage (@IsClosedImmersion : MorphismProperty Scheme.{u})
        (Over.forget S)) (diag F)) (e : F.RepresentableBy H) : IsSeparated H.hom := by
  let P := MorphismProperty.inverseImage (@IsClosedImmersion : MorphismProperty Scheme.{u})
    (Over.forget S)
  have hdiag : P.relative yoneda (diag (yoneda.obj H)) :=
    ((P.relative yoneda).arrow_mk_iso_iff
      (Arrow.isoMk e.toIso (prod.mapIso e.toIso e.toIso)
        (prod.diag_map e.toIso.hom).symm)).mpr h
  have hcomp : yoneda.map (diag H) ≫ (PreservesLimitPair.iso yoneda H H).hom =
      diag (yoneda.obj H) := by
    apply prod.hom_ext <;> simp [PreservesLimitPair.iso_hom, prodComparison, ← yoneda.map_comp]
  have hmap : P.relative yoneda (yoneda.map (diag H)) := by
    rw [← hcomp] at hdiag
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).mp hdiag
  have hd : IsClosedImmersion (diag H).left :=
    MorphismProperty.of_relative_map (P := P) (F := yoneda) hmap
  have heq : (diag H).left ≫ (Over.prodLeftIsoPullback H H).hom =
      pullback.diagonal H.hom := by
    apply pullback.hom_ext <;>
      simp [← Over.comp_left, diag]
  refine ⟨?_⟩
  rw [← heq]
  infer_instance

end AlgebraicGeometry
