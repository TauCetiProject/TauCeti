/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.ResidueField
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Rational points of a vector bundle over a point

Let `E` be a finite locally free sheaf on a scheme `X` and `x` a point of `X`, with residue field
`κ(x)` and canonical morphism `ι : Spec κ(x) ⟶ X`. The `κ(x)`-rational points of the total space
`𝕍(E) = Spec_X (Sym E^∨)` lying over `x`, that is the morphisms `Spec κ(x) ⟶ 𝕍(E)` over `X`, are
the vectors of the fibre `E_x ⊗_{𝒪_{X,x}} κ(x)` of `E` at `x`
(`totalSpaceResidueFieldHomEquiv`).

This combines three identifications: points of `𝕍(E)` over `ι` are sections `𝒪 ⟶ ι^* E`
(`totalSpaceHomEquiv`), such sections are the global sections of `ι^* E`
(`AlgebraicGeometry.Scheme.Modules.unitHomEquivTop`), and these are the fibre
`κ(x) ⊗_{𝒪_{X,x}} E_x` (`AlgebraicGeometry.Scheme.Modules.residueFieldPullbackSectionsEquiv`).
The vector `c ⊗ s_x` given by the germ of a section `s` of `E` near `x` corresponds to the point
whose section is `c` times the pullback of `s` (`totalSpaceResidueFieldHomEquiv_symm_tmul_germ`).

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in `E`; see the module docstring of
`TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace` for the comparison with the convention
`V(F) = Spec_X (Sym F)` of the references.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X) (x : X)

/-- **Rational points of a vector bundle over a point are the vectors of its fibre.** For a
finite locally free sheaf `E` on `X` and a point `x` of `X`, the morphisms
`Spec κ(x) ⟶ 𝕍(E) = Spec_X (Sym E^∨)` over `X` correspond to the vectors of the fibre
`κ(x) ⊗_{𝒪_{X,x}} E_x` of `E` at `x`. -/
def totalSpaceResidueFieldHomEquiv :
    (Over.mk (X.fromSpecResidueField x) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) ≃
        X.residueField x ⊗[X.presheaf.stalk x] E.obj.presheaf.stalk x :=
  (totalSpaceHomEquiv E (Over.mk (X.fromSpecResidueField x))).trans <|
    (Scheme.Modules.unitHomEquivTop _).trans
      (Scheme.Modules.residueFieldPullbackSectionsEquiv x E.obj).symm.toEquiv

/-- The point of `𝕍(E)` over `x` given by the vector `c ⊗ s_x`, for a section `s` of `E` over an
open `V ∋ x`, is the point whose section of `ι^* E` is `c` times the pullback of `s` along
`ι : Spec κ(x) ⟶ X`. -/
theorem totalSpaceResidueFieldHomEquiv_symm_tmul_germ {V : X.Opens} (hx : x ∈ V)
    (c : X.residueField x) (s : Γ(E.obj, V)) :
    (totalSpaceResidueFieldHomEquiv E x).symm (c ⊗ₜ E.obj.presheaf.germ V x hx s) =
      (totalSpaceHomEquiv E (Over.mk (X.fromSpecResidueField x))).symm
        ((Scheme.Modules.unitHomEquivTop _).symm
          (c • Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) E.obj V ⊤
            (Scheme.fromSpecResidueField_preimage_eq_top x hx).ge s)) :=
  -- The inverse of the composite equivalence applies the three inverses in turn.
  congrArg (fun t ↦ (totalSpaceHomEquiv E (Over.mk (X.fromSpecResidueField x))).symm
      ((Scheme.Modules.unitHomEquivTop _).symm t))
    (Scheme.Modules.residueFieldPullbackSectionsEquiv_tmul_germ x E.obj hx c s)

end

end TauCeti.AlgebraicGeometry
