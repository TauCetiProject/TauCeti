/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product

/-!
# Tests for faithful flatness of surjective homomorphisms of abelian varieties

* The identity of an abelian variety is faithfully flat; this includes the abelian variety
  `Spec K` of dimension zero.
* For abelian varieties `A` and `B`, the projection `A × B ⟶ A` is faithfully flat. It is
  surjective because the homomorphism `a ↦ (a, 0)` is a section of it, so
  `AbelianVariety.Hom.faithfullyFlat_of_surjective` applies although `A × B` and `A` have different
  dimensions when `B` has positive dimension.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TauCeti.AlgebraicGeometry.AbelianVariety.Hom

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K]

/-- The identity of an abelian variety is faithfully flat. -/
example (A : AbelianVariety K) :
    Flat (Hom.toSchemeHom (𝟙 A)) ∧ Surjective (Hom.toSchemeHom (𝟙 A)) := by
  have : Surjective (Hom.toSchemeHom (𝟙 A)) := by
    rw [Hom.toSchemeHom_id]
    infer_instance
  exact Hom.faithfullyFlat_of_surjective (𝟙 A)

/-- The first projection `A × B ⟶ A` of a product of abelian varieties is faithfully flat: it is
surjective, since the homomorphism `a ↦ (a, 0)` is a section of it. -/
example (A B : AbelianVariety K) :
    Flat (Hom.toSchemeHom (prod.fst A B)) ∧ Surjective (Hom.toSchemeHom (prod.fst A B)) := by
  let s : A ⟶ prod A B := prod.lift (𝟙 A) 1
  have : Surjective (Hom.toSchemeHom s ≫ Hom.toSchemeHom (prod.fst A B)) := by
    rw [← Hom.toSchemeHom_comp, prod.lift_fst, Hom.toSchemeHom_id]
    infer_instance
  have : Surjective (Hom.toSchemeHom (prod.fst A B)) := .of_comp (Hom.toSchemeHom s) _
  exact Hom.faithfullyFlat_of_surjective (prod.fst A B)

end TauCeti.AlgebraicGeometry.AbelianVariety
