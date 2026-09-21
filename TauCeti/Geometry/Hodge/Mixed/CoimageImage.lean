/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import TauCeti.Geometry.Hodge.Mixed.Limits

/-!
# Coimages and images of mixed Hodge morphisms

The canonical map from the coimage of a mixed Hodge morphism to its image is an isomorphism.
Thus the quotient by the kernel agrees, as a mixed Hodge structure, with the image carrying
the induced filtrations. This is the first isomorphism theorem for mixed Hodge structures,
and supplies the coimage–image condition in the characterization of an abelian category.

Rational realization preserves kernels and cokernels and reflects isomorphisms by strictness.
Mathlib's `CategoryTheory.Abelian.PreservesCoimageImageComparison.iso` therefore reduces the
comparison to the first isomorphism theorem for rational vector spaces.

## References

Deligne, *Théorie de Hodge II*, 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/

public section

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

/-- The canonical coimage-to-image map of a mixed Hodge morphism is an isomorphism. -/
noncomputable instance isIso_coimageImageComparison {X Y : MixedHodgeStructureCat.{u}}
    (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) := by
  have : IsIso (rational.map (Abelian.coimageImageComparison f)) :=
    (Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso rational f).hom).mpr inferInstance
  exact isIso_of_reflects_iso _ rational

end TauCeti.Hodge.MixedHodgeStructureCat
