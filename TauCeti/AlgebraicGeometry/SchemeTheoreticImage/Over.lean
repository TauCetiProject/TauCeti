/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Scheme-theoretic images over a common base

A morphism of schemes over `S` factors over `S` through its scheme-theoretic image, with
structure map given by the closed immersion into the original target followed by the target's
structure map.
-/

public section

open AlgebraicGeometry

namespace CategoryTheory.Over.Hom

universe u

variable {S : Scheme.{u}} {G H : Over S}

/-- The scheme-theoretic image of a morphism over `S`, equipped with its structure morphism
through the target. -/
-- The dependent types of the two maps identify its underlying scheme with the schematic image.
noncomputable abbrev imageOver (f : G ⟶ H) : Over S :=
  Over.mk (f.left.imageι ≫ H.hom)

@[simp]
lemma imageOver_left (f : G ⟶ H) : f.imageOver.left = f.left.image :=
  (rfl)

@[simp]
lemma imageOver_hom (f : G ⟶ H) : f.imageOver.hom = f.left.imageι ≫ H.hom :=
  (rfl)

/-- The closed immersion of a scheme-theoretic image into the target over the common base. -/
noncomputable def imageιOver (f : G ⟶ H) : f.imageOver ⟶ H :=
  Over.homMk f.left.imageι

@[simp]
lemma imageιOver_left (f : G ⟶ H) : f.imageιOver.left = f.left.imageι :=
  (rfl)

/-- The canonical factor to the scheme-theoretic image, as a morphism over the common base. -/
noncomputable def toImageOver (f : G ⟶ H) : G ⟶ f.imageOver :=
  Over.homMk f.left.toImage (f.left.toImage_imageι_assoc H.hom |>.trans (Over.w f))

@[simp]
lemma toImageOver_left (f : G ⟶ H) : f.toImageOver.left = f.left.toImage :=
  (rfl)

@[reassoc (attr := simp)]
lemma toImageOver_imageιOver (f : G ⟶ H) : f.toImageOver ≫ f.imageιOver = f := by
  ext
  simp

/-- The image inclusion over the base is a closed immersion of underlying schemes. -/
instance isClosedImmersion_imageιOver (f : G ⟶ H) : IsClosedImmersion f.imageιOver.left := by
  rw [imageιOver_left]
  infer_instance

/-- The map to the image of a quasi-compact morphism is quasi-compact. -/
instance quasiCompact_toImageOver (f : G ⟶ H) [QuasiCompact f.left] :
    QuasiCompact f.toImageOver.left := by
  rw [toImageOver_left]
  infer_instance

/-- The map to the image of a quasi-compact morphism is schematically dominant. -/
instance isSchemeTheoreticallyDominant_toImageOver (f : G ⟶ H) [QuasiCompact f.left] :
    IsSchemeTheoreticallyDominant f.toImageOver.left := by
  rw [toImageOver_left]
  infer_instance

end CategoryTheory.Over.Hom
