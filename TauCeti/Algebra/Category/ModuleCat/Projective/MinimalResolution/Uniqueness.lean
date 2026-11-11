/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.ModuleCat.Minimal

/-!
# Uniqueness of minimal projective resolutions

Two minimal projective resolutions with finite terms of the same module are isomorphic as
augmented complexes. The isomorphism is the forward map of Mathlib's comparison homotopy
equivalence; it need not be unique. Invariants of the terms and differentials are therefore
independent of the chosen minimal resolution.

Minimality means that each differential lands in the Jacobson radical times its target,
which over a local ring is the usual maximal-ideal criterion. Projectivity is supplied by
`ProjectiveResolution`, and finite generation is required for every term, not just the
resolved module. There is no finite projective-dimension assumption.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 20.
* Mathlib's `ProjectiveResolution.homotopyEquiv` supplies the comparison maps and homotopies.
-/

public section

namespace CategoryTheory.ProjectiveResolution

universe u v

variable {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
  (P Q : ProjectiveResolution M)
  [∀ i, Module.Finite R (P.complex.X i)] [∀ i, Module.Finite R (Q.complex.X i)]

/-- Minimal projective resolutions with finite terms of the same module are isomorphic.
The isomorphism is compatible with the augmentations. -/
noncomputable def isoOfMinimal (hP : P.complex.IsMinimal) (hQ : Q.complex.IsMinimal) :
    P.complex ≅ Q.complex :=
  have := hP.isIso_hom_of_homotopyEquiv hQ (P.homotopyEquiv Q)
  asIso (P.homotopyEquiv Q).hom

/-- The isomorphism of minimal resolutions uses the forward comparison map. -/
@[simp]
theorem isoOfMinimal_hom (hP : P.complex.IsMinimal) (hQ : Q.complex.IsMinimal) :
    (P.isoOfMinimal Q hP hQ).hom = (P.homotopyEquiv Q).hom := (rfl)

/-- The inverse comparison isomorphism also respects the augmentations. -/
@[reassoc (attr := simp)]
theorem isoOfMinimal_inv_comp_π (hP : P.complex.IsMinimal) (hQ : Q.complex.IsMinimal) :
    (P.isoOfMinimal Q hP hQ).inv ≫ P.π = Q.π := by
  rw [Iso.inv_comp_eq]
  simp

end CategoryTheory.ProjectiveResolution
