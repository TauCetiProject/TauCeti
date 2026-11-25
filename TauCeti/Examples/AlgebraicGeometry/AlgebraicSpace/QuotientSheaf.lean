/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf

/-!
# The quotient sheaf of the diagonal relation

For a scheme `U`, the diagonal relation `R = U` with `s = t = 𝟙 U`, the diagonal `U ⟶ U ×_S U`,
relates each point only to itself, and its quotient sheaf is the representable sheaf:
`U/Δ ≅ h_U`, through the projection `quotientSheaf.π`
(`TauCeti.CategoryTheory.quotientSheaf.isIso_π_self`). This is the SchemeAndStackFoundations §1.5
Check `U/Δ ≅ h_U`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Spaces.QuotientSheafExample

/-- **`U/Δ ≅ h_U`.** The quotient sheaf of the diagonal relation on a scheme `U` is the
representable sheaf of `U`, through the projection. -/
@[expose] def diagonalQuotientSheafIso (U : Scheme.{u}) :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.obj U ≅ quotientSheaf (𝟙 U) (𝟙 U) :=
  asIso (TauCeti.CategoryTheory.quotientSheaf.π _ (𝟙 U) (𝟙 U))

/-- The isomorphism `h_U ≅ U/Δ` is the projection onto the quotient sheaf. -/
@[simp]
lemma diagonalQuotientSheafIso_hom (U : Scheme.{u}) :
    (diagonalQuotientSheafIso U).hom =
      TauCeti.CategoryTheory.quotientSheaf.π _ (𝟙 U) (𝟙 U) :=
  rfl

end TauCeti.AlgebraicGeometry.Spaces.QuotientSheafExample
