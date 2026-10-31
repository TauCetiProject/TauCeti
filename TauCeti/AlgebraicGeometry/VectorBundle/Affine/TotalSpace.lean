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
# The total space of a vector bundle on an affine scheme

Let `M` be a finitely generated projective `R`-module and `M~` the associated finite locally free
sheaf on `Spec R` (`FiniteLocallyFreeSheaf.finiteProjectiveEquiv`). Its geometric total space
`𝕍(M~) = Spec_{Spec R} (Sym (M~)^∨)` is the spectrum `Spec (Sym_R M^∨)` of the symmetric algebra of
the linear dual `M^∨ = Hom_R(M, R)`, as schemes over `Spec R` (`totalSpaceFiniteProjectiveIso`).

The isomorphism identifies the dual sheaf `(M~)^∨` with `(M^∨)~`
(`FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso`) and then applies the affine computation
`Spec_{Spec R} (Sym N~) ≅ Spec (Sym_R N)` of relative spectra of symmetric algebras
(`relativeSpecSymmetricAlgebraTildeIso`) to `N = M^∨`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

variable {R : CommRingCat.{u}}

/-- **The total space of the vector bundle of a finite projective module.** For a finitely
generated projective `R`-module `M`, the geometric total space `𝕍(M~) = Spec_{Spec R} (Sym (M~)^∨)`
of the associated finite locally free sheaf on `Spec R` is isomorphic over `Spec R` to the spectrum
`Spec (Sym_R M^∨)` of the symmetric algebra of the linear dual of `M`. -/
def totalSpaceFiniteProjectiveIso (M : (finiteProjectiveModules R).FullSubcategory) :
    (totalSpaceScheme (Spec R)).obj ((finiteProjectiveEquiv R).functor.obj M) ≅
      specSymmetricAlgebraOver (ModuleCat.of R (Module.Dual R M.obj)) :=
  (relativeSpec (Spec R)).mapIso ((symmetricAlgebra (Spec R)).mapIso
    ((toQuasicoherent (Spec R)).mapIso (finiteProjectiveEquivDualIso R M))).op ≪≫
    relativeSpecSymmetricAlgebraTildeIso (ModuleCat.of R (Module.Dual R M.obj))

end TauCeti.AlgebraicGeometry

end
