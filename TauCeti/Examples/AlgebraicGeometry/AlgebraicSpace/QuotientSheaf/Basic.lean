/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf

/-!
# The quotient sheaf of the diagonal relation

For a scheme `U`, the diagonal relation `R = U` with `s = t = 𝟙 U`, that is
`(𝟙 U, 𝟙 U) : U ⟶ U × U`, relates each point only to itself, and its quotient sheaf is the
representable sheaf: `U/Δ ≅ h_U`, through the projection `quotientSheaf.π`
(`TauCeti.CategoryTheory.quotientSheaf.isIso_π_self`).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Spaces.QuotientSheafExample

/-- **`U/Δ ≅ h_U`.** The quotient sheaf of the diagonal relation on a scheme `U` is the
representable sheaf of `U`, through the projection. -/
def diagonalQuotientSheafIso (U : Scheme.{u}) :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.obj U ≅ quotientSheaf (𝟙 U) (𝟙 U) :=
  asIso (TauCeti.CategoryTheory.quotientSheaf.π _ (𝟙 U) (𝟙 U))

/-- The isomorphism `h_U ≅ U/Δ` is the projection onto the quotient sheaf. -/
@[simp]
lemma diagonalQuotientSheafIso_hom (U : Scheme.{u}) :
    (diagonalQuotientSheafIso U).hom =
      TauCeti.CategoryTheory.quotientSheaf.π _ (𝟙 U) (𝟙 U) :=
  (rfl)

/-- The inverse of the isomorphism `h_U ≅ U/Δ` is the factorisation of the identity of `h_U`
through the quotient sheaf. -/
@[simp]
lemma diagonalQuotientSheafIso_inv (U : Scheme.{u}) :
    (diagonalQuotientSheafIso U).inv = TauCeti.CategoryTheory.quotientSheaf.desc (𝟙 _) rfl := by
  rw [diagonalQuotientSheafIso, asIso_inv, TauCeti.CategoryTheory.quotientSheaf.inv_π_self]

end TauCeti.AlgebraicGeometry.Spaces.QuotientSheafExample
