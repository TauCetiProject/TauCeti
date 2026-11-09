/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.ResidueField
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.TotalSpace
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.AffineSpace

/-!
# Fibres of the total space of a vector bundle

Let `E` be a finite locally free sheaf on a scheme `X` and `𝕍(E) = Spec_X (Sym E^∨)` its geometric
total space.

Over an affine scheme `f : Spec R ⟶ X`, the base change `Spec R ×_X 𝕍(E)` is the spectrum
`Spec (Sym_R V^∨)` of the symmetric algebra of the linear dual of the finitely generated projective
`R`-module `V = Γ(Spec R, f^* E)` (`totalSpaceBaseChangeSpecIso`). This combines the base change
`𝕍(f^* E) ≅ Spec R ×_X 𝕍(E)` of the total space with the affine computation
`𝕍(M~) ≅ Spec (Sym_R M^∨)` for finite projective `M`, applied to `f^* E ≅ V~`.

If `R` is local, then `V` is free, of rank the rank of `E` at the image `x` of the closed point, so
`Spec R ×_X 𝕍(E)` is the affine space `𝔸ⁿ_R` with `n = rank_x E`
(`totalSpaceBaseChangeAffineSpaceIso`). In particular, for a point `x` of `X` with residue field
`κ(x)`, the fibre `Spec κ(x) ×_X 𝕍(E)` of the total space over `x` is the affine space
`𝔸ⁿ_{κ(x)}` of dimension `n = rank_x E` (`totalSpaceFiberIso`). These identifications depend on a
choice of basis of `V`; the canonical form of the fibre is `Spec (Sym_{κ(x)} V^∨)` with
`V = Γ(Spec κ(x), ι^* E)`, the case `f = ι : Spec κ(x) ⟶ X` of `totalSpaceBaseChangeSpecIso`.
Here `V` is the module fibre `κ(x) ⊗_{𝒪_{X,x}} E_x` of `E` at `x`
(`AlgebraicGeometry.Scheme.Modules.residueFieldPullbackSectionsEquiv`), so the fibre of `𝕍(E)`
over `x` is `Spec (Sym_{κ(x)} (κ(x) ⊗_{𝒪_{X,x}} E_x)^∨)` (`totalSpaceFiberSpecIso`).

The input is that a finite locally free sheaf on the spectrum of a local ring is free
(`FiniteLocallyFreeSheaf.isoFreeOfIsLocalRing`).

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceBaseChangeSpecIso`: `Spec R ×_X 𝕍(E) ≅ Spec (Sym_R V^∨)`
  for `V = Γ(Spec R, f^* E)`;
* `TauCeti.AlgebraicGeometry.totalSpaceBaseChangeAffineSpaceIso`: over a local ring,
  `Spec R ×_X 𝕍(E) ≅ 𝔸ⁿ_R` with `n` the rank of `E` at the image of the closed point;
* `TauCeti.AlgebraicGeometry.totalSpaceFiberIso`: the fibre of `𝕍(E)` over `x` is `𝔸ⁿ_{κ(x)}`
  with `n = rank_x E`;
* `TauCeti.AlgebraicGeometry.totalSpaceFiberSpecIso`: the fibre of `𝕍(E)` over `x` is
  `Spec (Sym_{κ(x)} (κ(x) ⊗_{𝒪_{X,x}} E_x)^∨)`, without a choice of basis.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.18.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {R : CommRingCat.{u}}

variable {X : Scheme.{u}}

/-- **The total space over an affine scheme.** For a morphism `f : Spec R ⟶ X` and a finite
locally free sheaf `E` on `X`, the base change `Spec R ×_X 𝕍(E)` of the total space of `E` is
isomorphic over `Spec R` to the spectrum `Spec (Sym_R V^∨)` of the symmetric algebra of the linear
dual of the finitely generated projective `R`-module `V = Γ(Spec R, f^* E)`. -/
def totalSpaceBaseChangeSpecIso (E : FiniteLocallyFreeSheaf X) (f : Spec R ⟶ X) :
    (baseChangeAffineSchemeOver f).obj ((totalSpaceScheme X).obj E) ≅
      specSymmetricAlgebraOver (ModuleCat.of R
        (Module.Dual R (moduleSpecΓFunctor.obj ((pullback f).obj E).obj))) :=
  ((totalSpaceSchemeBaseChangeIso f).app E).symm ≪≫
    (totalSpaceScheme (Spec R)).mapIso
      ((finiteProjectiveEquiv R).counitIso.app ((pullback f).obj E)).symm ≪≫
    totalSpaceFiniteProjectiveIso ((finiteProjectiveEquiv R).inverse.obj ((pullback f).obj E))

/-- `totalSpaceBaseChangeSpecIso` is the inverse of the base change of the total space, followed
by the total space of the inverse of the counit `(Γ(Spec R, f^* E))~ ≅ f^* E` and the affine
computation `totalSpaceFiniteProjectiveIso`. -/
lemma totalSpaceBaseChangeSpecIso_hom (E : FiniteLocallyFreeSheaf X) (f : Spec R ⟶ X) :
    (totalSpaceBaseChangeSpecIso E f).hom =
      (totalSpaceSchemeBaseChangeIso f).inv.app E ≫
        (totalSpaceScheme (Spec R)).map
          ((finiteProjectiveEquiv R).counitIso.inv.app ((pullback f).obj E)) ≫
        (totalSpaceFiniteProjectiveIso
          ((finiteProjectiveEquiv R).inverse.obj ((pullback f).obj E))).hom :=
  (rfl)

/-- **The total space over a local scheme is affine space.** For a local ring `R`, a morphism
`f : Spec R ⟶ X` and a finite locally free sheaf `E` on `X` of rank `n` at the image of the closed
point, the base change `Spec R ×_X 𝕍(E)` of the total space of `E` is isomorphic over `Spec R` to
the affine space `𝔸ⁿ_R`. -/
def totalSpaceBaseChangeAffineSpaceIso [IsLocalRing R] (E : FiniteLocallyFreeSheaf X)
    (f : Spec R ⟶ X) {n : ℕ} (hn : E.rank (f (IsLocalRing.closedPoint R)) = n) :
    (baseChangeAffineSchemeOver f).obj ((totalSpaceScheme X).obj E) ≅
      affineSpaceOver (Spec R) (ULift.{u} (Fin n)) :=
  ((totalSpaceSchemeBaseChangeIso f).app E).symm ≪≫
    (totalSpaceScheme (Spec R)).mapIso
      (isoFreeOfIsLocalRing ((pullback f).obj E) ((rank_pullback_apply f E _).trans hn)) ≪≫
    totalSpaceFreeIso (Spec R) (ULift.{u} (Fin n))

/-- `totalSpaceBaseChangeAffineSpaceIso` is the inverse of the base change of the total space,
followed by the total space of a trivialization `f^* E ≅ 𝒪ⁿ` and `totalSpaceFreeIso`. -/
lemma totalSpaceBaseChangeAffineSpaceIso_hom [IsLocalRing R] (E : FiniteLocallyFreeSheaf X)
    (f : Spec R ⟶ X) {n : ℕ} (hn : E.rank (f (IsLocalRing.closedPoint R)) = n) :
    (totalSpaceBaseChangeAffineSpaceIso E f hn).hom =
      (totalSpaceSchemeBaseChangeIso f).inv.app E ≫
        (totalSpaceScheme (Spec R)).map (isoFreeOfIsLocalRing ((pullback f).obj E)
          ((rank_pullback_apply f E _).trans hn)).hom ≫
        (totalSpaceFreeIso (Spec R) (ULift.{u} (Fin n))).hom :=
  (rfl)

/-- **The fibre of the total space of a vector bundle is affine space.** For a finite locally free
sheaf `E` on `X` and a point `x` of `X` with residue field `κ(x)`, the fibre
`Spec κ(x) ×_X 𝕍(E)` of the total space of `E` over `x` is isomorphic over `Spec κ(x)` to the affine
space `𝔸ⁿ_{κ(x)}` of dimension `n = rank_x E`. -/
def totalSpaceFiberIso (E : FiniteLocallyFreeSheaf X) (x : X) :
    (baseChangeAffineSchemeOver (X.fromSpecResidueField x)).obj ((totalSpaceScheme X).obj E) ≅
      affineSpaceOver (Spec (X.residueField x)) (ULift.{u} (Fin (E.rank x))) :=
  totalSpaceBaseChangeAffineSpaceIso E (X.fromSpecResidueField x)
    (congrArg E.rank (X.fromSpecResidueField_apply x _))

/-- `totalSpaceFiberIso` is `totalSpaceBaseChangeAffineSpaceIso` for the morphism
`Spec κ(x) ⟶ X`, whose closed point maps to `x`. -/
lemma totalSpaceFiberIso_def (E : FiniteLocallyFreeSheaf X) (x : X) :
    totalSpaceFiberIso E x = totalSpaceBaseChangeAffineSpaceIso E (X.fromSpecResidueField x)
      (congrArg E.rank (X.fromSpecResidueField_apply x _)) :=
  (rfl)

/-- **The fibre of the total space of a vector bundle, without a choice of basis.** For a finite
locally free sheaf `E` on `X` and a point `x` of `X`, the fibre
`Spec κ(x) ×_X 𝕍(E)` of the total space of `E` over `x` is isomorphic over `Spec κ(x)` to
`Spec (Sym_{κ(x)} (κ(x) ⊗_{𝒪_{X,x}} E_x)^∨)`, the spectrum of the symmetric algebra of the dual of
the module fibre `κ(x) ⊗_{𝒪_{X,x}} E_x`. The module fibre is identified with the global sections
of the pullback of `E` along `Spec κ(x) ⟶ X` by
`Scheme.Modules.residueFieldPullbackSectionsEquiv`. -/
def totalSpaceFiberSpecIso (E : FiniteLocallyFreeSheaf X) (x : X) :
    (baseChangeAffineSchemeOver (X.fromSpecResidueField x)).obj ((totalSpaceScheme X).obj E) ≅
      specSymmetricAlgebraOver (ModuleCat.of (X.residueField x)
        (Module.Dual (X.residueField x)
          (X.residueField x ⊗[X.presheaf.stalk x] E.obj.presheaf.stalk x))) :=
  totalSpaceBaseChangeSpecIso E (X.fromSpecResidueField x) ≪≫
    specSymmetricAlgebraOverIso
      ((Scheme.Modules.residueFieldPullbackSectionsEquiv x E.obj).trans
        (moduleSpecΓFunctor.mapIso (eqToIso (pullback_obj_obj _ E).symm)).toLinearEquiv).dualMap

/-- `totalSpaceFiberSpecIso` is `totalSpaceBaseChangeSpecIso` for the morphism `Spec κ(x) ⟶ X`,
followed by the dual of the identification `κ(x) ⊗_{𝒪_{X,x}} E_x ≅ Γ(Spec κ(x), ι^* E)` of the
module fibre with the global sections of the pullback. -/
lemma totalSpaceFiberSpecIso_hom (E : FiniteLocallyFreeSheaf X) (x : X) :
    (totalSpaceFiberSpecIso E x).hom =
      (totalSpaceBaseChangeSpecIso E (X.fromSpecResidueField x)).hom ≫
        (specSymmetricAlgebraOverIso
          ((Scheme.Modules.residueFieldPullbackSectionsEquiv x E.obj).trans
            (moduleSpecΓFunctor.mapIso
              (eqToIso (pullback_obj_obj _ E).symm)).toLinearEquiv).dualMap).hom :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
