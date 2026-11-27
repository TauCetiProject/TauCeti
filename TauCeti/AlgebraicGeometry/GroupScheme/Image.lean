/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.CategoryTheory.Comma.Over

/-!
# Scheme-theoretic images of group homomorphisms over a field

The scheme-theoretic image of a quasi-compact group homomorphism over a field is a closed
subgroup. Schematic dominance of the map to the image, also on its fibre square, detects
factorization of the group operations via `TauCeti.GroupScheme.grpObjOfClosedImmersion`.
For the image theorem for algebraic groups, see J. S. Milne, *Algebraic Groups* (2017),
Theorem 5.39.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

section OverBase

variable {S : Scheme.{u}} {G H : Over S} (f : G ⟶ H)

/-- The schematic image equipped with its structure morphism to the base. -/
abbrev imageOver : Over S :=
  Over.mk (f.left.imageι ≫ H.hom)

/-- The closed immersion of the schematic image, over the base. -/
def imageι : imageOver f ⟶ H :=
  Over.homMk f.left.imageι

/-- The underlying morphism of the image inclusion is the canonical closed immersion. -/
@[simp]
lemma imageι_left : (imageι f).left = f.left.imageι := (rfl)

instance : IsClosedImmersion (imageι f).left := by
  rw [imageι_left]
  infer_instance

instance : Mono (imageι f) := Over.mono_of_mono_left _

/-- The canonical factorization through the schematic image, over the base. -/
def toImage : G ⟶ imageOver f :=
  Over.homMk f.left.toImage (by simp [← Category.assoc])

/-- The underlying morphism to the image is the canonical map of schemes to the image. -/
@[simp]
lemma toImage_left : (toImage f).left = f.left.toImage := (rfl)

/-- The scheme-theoretic image factorization recovers the original morphism over the base. -/
@[reassoc (attr := simp)]
lemma toImage_imageι : toImage f ≫ imageι f = f := by
  ext1
  simp

end OverBase

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} (f : G ⟶ H)
  [QuasiCompact f.left]

private lemma schematicDominance_square :
    IsSchemeTheoreticallyDominant ((toImage f) ⊗ₘ (toImage f)).left := by
  let p := toImage f
  -- Factor the product map into two flat base changes of the map onto the image.
  have h₁ : IsPullback (p ▷ G).left (pullback.fst G.hom G.hom)
      (pullback.fst (imageOver f).hom G.hom) p.left := by
    exact Over.isPullback_pullback_map_left G.hom p
  have h₂ : IsPullback ((imageOver f) ◁ p).left
      (pullback.snd (imageOver f).hom G.hom)
      (pullback.snd (imageOver f).hom (imageOver f).hom) p.left := by
    refine IsPullback.of_right ?_ (Over.whiskerLeft_left_snd p)
      (IsPullback.of_hasPullback (imageOver f).hom (imageOver f).hom)
    rw [Over.whiskerLeft_left_fst, Over.w p]
    exact IsPullback.of_hasPullback _ _
  have : QuasiCompact p.left := inferInstanceAs (QuasiCompact f.left.toImage)
  have : IsSchemeTheoreticallyDominant p.left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant f.left.toImage)
  have : IsSchemeTheoreticallyDominant (p ▷ G).left :=
    .of_isPullback h₁.flip
  have : IsSchemeTheoreticallyDominant ((imageOver f) ◁ p).left :=
    .of_isPullback h₂.flip
  rw [tensorHom_def, Over.comp_left]
  infer_instance

variable [GrpObj G] [GrpObj H] [IsMonHom f]

private lemma image_group_ker :
    (imageι f).left.ker ≤ η[H].left.ker ∧
    (imageι f).left.ker ≤ (((imageι f) ⊗ₘ (imageι f)) ≫ μ[H]).left.ker ∧
    (imageι f).left.ker ≤ (imageι f ≫ ι[H]).left.ker := by
  simp only [imageι_left, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨?_, ?_, ?_⟩
  · rw [← IsMonHom.one_hom f, Over.comp_left]
    exact Scheme.Hom.le_ker_comp _ _
  · have hd := schematicDominance_square f
    -- Test factorization of multiplication after the schematically dominant product map.
    rw [← Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant
      ((toImage f) ⊗ₘ (toImage f)).left, ← Over.comp_left, ← Category.assoc,
      tensorHom_comp_tensorHom, toImage_imageι, ← IsMonHom.mul_hom f, Over.comp_left]
    exact Scheme.Hom.le_ker_comp _ _
  · have : IsSchemeTheoreticallyDominant (toImage f).left :=
      inferInstanceAs (IsSchemeTheoreticallyDominant f.left.toImage)
    rw [← Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant (toImage f).left,
      ← Over.comp_left, ← Category.assoc, toImage_imageι, ← GrpObj.inv_hom f, Over.comp_left]
    exact Scheme.Hom.le_ker_comp _ _

/-- The unique group law on the schematic image for which the inclusion is a homomorphism. -/
@[instance_reducible]
def imageGrpObj : GrpObj (imageOver f) :=
  grpObjOfClosedImmersion (imageι f)
    (image_group_ker f).1 (image_group_ker f).2.1 (image_group_ker f).2.2

/-- The closed immersion of the schematic image preserves the induced group law. -/
lemma isMonHom_imageι : letI := imageGrpObj f; IsMonHom (imageι f) :=
  isMonHom_grpObjOfClosedImmersion _ _ _ _

/-- The factorization of the original homomorphism through its image preserves the group law. -/
lemma isMonHom_toImage : letI := imageGrpObj f; IsMonHom (toImage f) := by
  let := imageGrpObj f
  have := isMonHom_imageι f
  constructor
  · rw [← cancel_mono (imageι f)]
    simp [IsMonHom.one_hom]
  · rw [← cancel_mono (imageι f)]
    rw [Category.assoc, toImage_imageι, Category.assoc, IsMonHom.mul_hom (imageι f),
      ← Category.assoc, tensorHom_comp_tensorHom, toImage_imageι, IsMonHom.mul_hom f]

end TauCeti.GroupScheme
