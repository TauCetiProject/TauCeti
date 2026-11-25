/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Projections of the concrete product comparison in `Rep`

The comparison `Rep.prodIsoProduct` identifies the componentwise product action with the
categorical product. These projection formulas characterize both directions without unfolding
the chosen categorical limit, and support product comparisons in finite representation categories.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable {k G : Type*} [Ring k] [Monoid G] (A B : Rep k G)

/-- The concrete product comparison preserves the first projection. -/
@[reassoc (attr := simp)]
theorem prodIsoProduct_hom_fst :
    (prodIsoProduct A B).hom ≫ prod.fst = ofHom (.fst k A.ρ B.ρ) :=
  (binaryBiconeIsBilimit A B).isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨.left⟩

/-- The concrete product comparison preserves the second projection. -/
@[reassoc (attr := simp)]
theorem prodIsoProduct_hom_snd :
    (prodIsoProduct A B).hom ≫ prod.snd = ofHom (.snd k A.ρ B.ρ) :=
  (binaryBiconeIsBilimit A B).isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨.right⟩

/-- The inverse concrete product comparison preserves the first projection. -/
@[reassoc (attr := simp)]
theorem prodIsoProduct_inv_fst :
    (prodIsoProduct A B).inv ≫ ofHom (.fst k A.ρ B.ρ) = prod.fst := by
  simp [Iso.inv_comp_eq]

/-- The inverse concrete product comparison preserves the second projection. -/
@[reassoc (attr := simp)]
theorem prodIsoProduct_inv_snd :
    (prodIsoProduct A B).inv ≫ ofHom (.snd k A.ρ B.ρ) = prod.snd := by
  simp [Iso.inv_comp_eq]

end Rep
