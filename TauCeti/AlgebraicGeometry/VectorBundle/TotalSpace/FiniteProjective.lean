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

Let `M` be a finitely generated projective module over a commutative ring `R`, and let `M~` be
the associated finite locally free sheaf on `Spec R`
(`FiniteLocallyFreeSheaf.finiteProjectiveEquiv`).
The geometric total space `𝕍(M~) = Spec_{Spec R} (Sym (M~)^∨)` is the affine scheme
`Spec (Sym_R M^∨)` over `Spec R`, where `M^∨ = Hom_R(M, R)` is the linear dual
(`totalSpaceFiniteProjectiveIso`).

This combines two identifications: the dual of `M~` is the sheaf associated with `M^∨`
(`FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso`), and the relative spectrum of the
symmetric algebra of the sheaf associated with an `R`-module `N` is `Spec (Sym_R N)`
(`relativeSpecSymmetricAlgebraTildeIso`). Under the resulting isomorphism, a point
`t : T ⟶ 𝕍(M~)` over `Spec R` goes to the point of `Spec (Sym_R M^∨)` whose linear map
`M^∨ → Γ(T, ⊤)` evaluates the module map `(M~)^∨ ⟶ q_* 𝒪_T` of `t` on the sections associated with
linear forms (`specSymmetricAlgebraHomEquiv_comp_totalSpaceFiniteProjectiveIso_hom`).

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceFiniteProjectiveIso`: the isomorphism
  `𝕍(M~) ≅ Spec (Sym_R M^∨)` of affine schemes over `Spec R`;
* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraHomEquiv_comp_totalSpaceFiniteProjectiveIso_hom`:
  its action on points.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.18.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

variable {R : CommRingCat.{u}} (M : (finiteProjectiveModules R).FullSubcategory)

/-- The dual of the finite locally free sheaf `M~` of a finite projective module `M`, as a
quasicoherent sheaf, is the sheaf associated with the linear dual `M^∨`. -/
private def toQuasicoherentDualFiniteProjectiveIso :
    tildeEquiv.functor.obj (ModuleCat.of R (Module.Dual R M.obj)) ≅
      (toQuasicoherent (Spec R)).obj (dual ((finiteProjectiveEquiv R).functor.obj M)) :=
  (toQuasicoherent (Spec R)).mapIso (finiteProjectiveEquivDualIso R M)

/-- **The total space of the vector bundle of a finite projective module.** For a finitely
generated projective `R`-module `M`, the total space `𝕍(M~) = Spec_{Spec R} (Sym (M~)^∨)` of the
associated finite locally free sheaf is isomorphic over `Spec R` to `Spec (Sym_R M^∨)`. It is the
relative spectrum of the symmetric algebra of the identification `(M^∨)~ ≅ (M~)^∨`, followed by
`relativeSpecSymmetricAlgebraTildeIso`. -/
def totalSpaceFiniteProjectiveIso :
    (totalSpaceScheme (Spec R)).obj ((finiteProjectiveEquiv R).functor.obj M) ≅
      specSymmetricAlgebraOver R (ModuleCat.of R (Module.Dual R M.obj)) :=
  (relativeSpec (Spec R)).mapIso
      ((symmetricAlgebra (Spec R)).mapIso (toQuasicoherentDualFiniteProjectiveIso M)).op ≪≫
    relativeSpecSymmetricAlgebraTildeIso _

/-- **Points of the total space of the vector bundle of a finite projective module.** Under
`totalSpaceFiniteProjectiveIso`, a point `t : T ⟶ 𝕍(M~)` over `Spec R` goes to the point of
`Spec (Sym_R M^∨)` whose `R`-linear map `M^∨ → Γ(T, ⊤)` is the adjoint of the module map
`(M^∨)~ ≅ (M~)^∨ ⟶ q_* 𝒪_T` of `t`, read in the global functions on `T`. -/
lemma specSymmetricAlgebraHomEquiv_comp_totalSpaceFiniteProjectiveIso_hom (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj
      ((totalSpaceScheme (Spec R)).obj ((finiteProjectiveEquiv R).functor.obj M))) :
    specSymmetricAlgebraHomEquiv _ T
        (t ≫ (MorphismProperty.Over.forget _ _ _).map (totalSpaceFiniteProjectiveIso M).hom) =
      tilde.adjunction.homEquiv _ _ ((finiteProjectiveEquivDualIso R M).hom.hom ≫
          relativeSpecSymmetricAlgebraHomEquiv _ T t) ≫
        (moduleSpecΓPushforwardIso T).hom := by
  -- The isomorphism is the relative spectrum `a` of the dual comparison followed by
  -- `relativeSpecSymmetricAlgebraTildeIso`: split the composite, then combine the descriptions of
  -- points for both factors.
  let a := (relativeSpec (Spec R)).map
    ((symmetricAlgebra (Spec R)).map (toQuasicoherentDualFiniteProjectiveIso M).hom).op
  refine (congrArg (specSymmetricAlgebraHomEquiv _ T) (?_ : _ = (t ≫
      (MorphismProperty.Over.forget _ _ _).map a) ≫ (MorphismProperty.Over.forget _ _ _).map
        (relativeSpecSymmetricAlgebraTildeIso _).hom)).trans
    ((specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom _ T _).trans ?_)
  · exact (congrArg (t ≫ ·) ((MorphismProperty.Over.forget _ _ _).map_comp a
      (relativeSpecSymmetricAlgebraTildeIso _).hom)).trans (Category.assoc _ _ _).symm
  · exact (relativeSpecSymmetricAlgebraTildeHomEquiv_apply _ T _).trans
      (congrArg (fun φ ↦ tilde.adjunction.homEquiv _ _ φ ≫ (moduleSpecΓPushforwardIso T).hom)
        (relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map
          ((toQuasicoherent (Spec R)).map (finiteProjectiveEquivDualIso R M).hom) T t))

end TauCeti.AlgebraicGeometry
