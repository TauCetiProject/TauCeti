/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Tilde
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# The total space of the vector bundle of a finite projective module

For a commutative ring `R` and a finitely generated projective `R`-module `P`, the sheaf `P~` on
`Spec R` is a vector bundle (`FiniteLocallyFreeSheaf.finiteProjectiveEquiv`). Its geometric total
space `𝕍(P~) = Spec_{Spec R} (Sym (P~)^∨)` is the spectrum `Spec (Sym_R P^∨)` of the symmetric
algebra of the dual module `P^∨ = Hom_R(P, R)`, over `Spec R`
(`totalSpaceSchemeFiniteProjectiveIso`).

The dual of `P~` is the sheaf associated with `P^∨`
(`FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso`), and the relative spectrum of the symmetric
algebra of a sheaf `M~` is `Spec (Sym_R M)` (`relativeSpecSymmetricAlgebraTildeIso`).

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceSchemeFiniteProjectiveIso`: the isomorphism
  `𝕍(P~) ≅ Spec (Sym_R P^∨)` of affine schemes over `Spec R`.

## References

These use the convention `V(F) = Spec_X (Sym F)`, in which the total space of `E` is `V(E^∨)`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`.

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

variable (R : CommRingCat.{u})

/-- The dual of the vector bundle `P~` of a finite projective module `P`, as a quasicoherent sheaf,
is the sheaf associated with the dual module `P^∨`. -/
private def tildeDualIso (P : (finiteProjectiveModules R).FullSubcategory) :
    tildeEquiv.functor.obj (FiniteProjectiveModules.dual R P).obj ≅
      (toQuasicoherent (Spec R)).obj (dual ((finiteProjectiveEquiv R).functor.obj P)) :=
  -- Both underlying sheaves of the first step are `(P^∨)~`, by definition of the two embeddings.
  ObjectProperty.isoMk _ (Iso.refl _) ≪≫
    (toQuasicoherent (Spec R)).mapIso (finiteProjectiveEquivDualIso R P)

/-- **The total space of the vector bundle of a finite projective module.** For a finitely
generated projective `R`-module `P`, the geometric total space
`𝕍(P~) = Spec_{Spec R} (Sym (P~)^∨)` of the vector bundle `P~` on `Spec R` is isomorphic over
`Spec R` to the spectrum `Spec (Sym_R P^∨)` of the symmetric algebra of the dual module `P^∨`.
It is the relative spectrum of the symmetric algebra of `(P~)^∨ ≅ (P^∨)~`, followed by
`relativeSpecSymmetricAlgebraTildeIso`. -/
def totalSpaceSchemeFiniteProjectiveIso (P : (finiteProjectiveModules R).FullSubcategory) :
    (totalSpaceScheme (Spec R)).obj ((finiteProjectiveEquiv R).functor.obj P) ≅
      specSymmetricAlgebraOver R (FiniteProjectiveModules.dual R P).obj :=
  (relativeSpec (Spec R)).mapIso ((symmetricAlgebra (Spec R)).mapIso (tildeDualIso R P)).op ≪≫
    relativeSpecSymmetricAlgebraTildeIso R _

end TauCeti.AlgebraicGeometry
