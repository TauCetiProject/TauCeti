/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Antipode endomorphism of cocommutative Hopf algebras

For cocommutative `H : CommHopfAlgCat R` (`[Coalgebra.IsCocomm R H]`), `antipodeEnd H`
represents group-scheme inversion `g ↦ g⁻¹` on `Spec H`.

## Main declarations

* `CommHopfAlgCat.antipodeEnd`, `antipodeEnd_comp_antipodeEnd`: the antipode endomorphism `H ⟶ H`
  and its involutivity.
-/

public section

open CategoryTheory TauCeti

universe u v

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] (H : CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H]

/-- The antipode endomorphism of cocommutative `H : CommHopfAlgCat R`. -/
noncomputable def antipodeEnd : H ⟶ H :=
  CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R) (A := H))

/-- Underlying bialgebra morphism of `antipodeEnd H`. -/
@[simp]
theorem antipodeEnd_hom : (antipodeEnd H).hom = HopfAlgebra.antipodeBialgHom (R := R) (A := H) :=
  CommHopfAlgCat.hom_ofHom _

/-- The antipode endomorphism of a cocommutative Hopf algebra is involutive. -/
@[reassoc (attr := simp)]
theorem antipodeEnd_comp_antipodeEnd : antipodeEnd H ≫ antipodeEnd H = 𝟙 H := by
  apply CommHopfAlgCat.hom_ext; ext x; simp [HopfAlgebra.antipode_antipode]

end CommHopfAlgCat
