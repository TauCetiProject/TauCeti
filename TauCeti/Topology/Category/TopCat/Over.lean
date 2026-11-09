/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Isomorphisms in `TopCat / X`

A morphism in the over category `TopCat / X` is an isomorphism exactly when its map of total
spaces is a homeomorphism, and the same holds in every full subcategory of `TopCat / X`, such as
the categories of covering spaces in `TauCeti.Topology.Covering.Category`.

## Main declarations

* `TauCeti.Over.isIso_iff_isHomeomorph_left`: a morphism in `TopCat / X` is an isomorphism
  exactly when its map on left objects is a homeomorphism.
* `TauCeti.Over.isIso_iff_isHomeomorph_hom_left`: a morphism in a full subcategory of
  `TopCat / X` is an isomorphism exactly when its map of total spaces is a homeomorphism.
-/

public section

universe u

namespace TauCeti.Over

open CategoryTheory

/-- A morphism in `TopCat / X` is an isomorphism exactly when its map on left objects is a
homeomorphism. -/
theorem isIso_iff_isHomeomorph_left {X : TopCat.{u}} {p q : CategoryTheory.Over X}
    (f : p ⟶ q) : IsIso f ↔ IsHomeomorph f.left := by
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact (isIso_iff_of_reflects_iso _ (CategoryTheory.Over.forget X)).symm

/-- A morphism in a full subcategory of `TopCat / X` is an isomorphism exactly when its map of
total spaces is a homeomorphism. This applies to maps in `TauCeti.CoveringSpace X` and in every
`TauCeti.CoveringSpace.FullSubcategory X P`. -/
theorem isIso_iff_isHomeomorph_hom_left {X : TopCat.{u}}
    {Q : ObjectProperty (CategoryTheory.Over X)} {p q : Q.FullSubcategory} (f : p ⟶ q) :
    IsIso f ↔ IsHomeomorph f.hom.left := by
  rw [← ObjectProperty.isIso_hom_iff, isIso_iff_isHomeomorph_left]

end TauCeti.Over
