/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Plucker
public import TauCeti.AlgebraicGeometry.Grassmannian.RankOne
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver.Basic

/-!
# Projectivity of the Grassmannian

The Plücker closed immersion followed by the rank-one identification with a symmetric-algebra
Proj proves projectivity of the quotient Grassmannian over its native structure map. Only the
relevant exterior power must be finite; finiteness of the ambient module suffices.

This supplies the projective ambient schemes for closed loci of stable submodules in finite
lattice charts.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TauCeti.SymmetricAlgebra

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The quotient Grassmannian is projective over its coefficient ring when its Plücker
coordinate module is finite. In particular, every quotient Grassmannian of a finite module
is projective, without a freeness or projectivity assumption on the ambient module. -/
instance isProjectiveOver_scheme (r : ℕ) [Module.Finite R (⋀[R]^r M)] :
    (scheme R M r).IsProjectiveOver R := by
  let f := pluckerHom R M r ≫ (toProjIso R).hom
  have : f.IsOver (Spec (.of R)) := ⟨by
    simp only [f, over_eq_projToSpec, over_scheme, Category.assoc,
      toProjIso_hom_projToSpec, pluckerHom_toSpec]⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion R f

end Module.Grassmannian
