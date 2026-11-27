/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
public import TauCeti.AlgebraicGeometry.Cohomology.PuncturedPlane
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# The first higher direct image of the punctured plane

Let `R` be a nonzero commutative ring and `f : 𝔸²_R ∖ {0} ⟶ Spec R` the structure morphism of the
punctured plane. It is quasi-compact and quasi-separated (its source is a quasi-compact open of
`𝔸²_R`, `TauCeti.PuncturedAffineSpace.instCompactSpace`), so over the affine base `Spec R` the
global sections of `R¹ f_* 𝒪` are `H¹(𝔸²_R ∖ {0}, 𝒪)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv`), which is nonzero
(`TauCeti.PuncturedAffineSpace.nontrivial_cohomology_one_puncturedPlane`). Hence `R¹ f_* 𝒪 ≠ 0`,
so a quasi-compact quasi-separated morphism to an affine base can have a nonzero first higher
direct image of the structure sheaf.

* `TauCeti.PuncturedAffineSpace.nontrivial_higherDirectImage_one_puncturedPlane`: the global
  sections of `R¹ f_* 𝒪` are nonzero.
* `TauCeti.PuncturedAffineSpace.not_isZero_higherDirectImage_one_puncturedPlane`: `R¹ f_* 𝒪` is
  not the zero module.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.PuncturedAffineSpace

variable (R : Type u) [CommRing R] [Nontrivial R]

/-- **The punctured plane has a nonzero first higher direct image.** Over a nonzero ring `R`, the
global sections of `R¹ f_* 𝒪` for the structure morphism `f : 𝔸²_R ∖ {0} ⟶ Spec R` are nonzero:
they are `H¹(𝔸²_R ∖ {0}, 𝒪)`. -/
theorem nontrivial_higherDirectImage_one_puncturedPlane :
    Nontrivial Γ(((puncturedAffineSpace R (Fin 2)).hom.higherDirectImage 1).obj
      (SheafOfModules.unit (puncturedAffineSpace R (Fin 2)).left.ringCatSheaf), ⊤) := by
  have := nontrivial_cohomology_one_puncturedPlane (R := R)
  let f := (puncturedAffineSpace R (Fin 2)).hom
  let M := SheafOfModules.unit (puncturedAffineSpace R (Fin 2)).left.ringCatSheaf
  have e := (f.higherDirectImageSectionsAddEquiv M 1 (isAffineOpen_top (Spec (.of R)))).symm.trans
    (eqToIso (congrArg (cohomologyOn M 1) (Scheme.Hom.preimage_top f)) ≪≫
      cohomologyOnTopIso M 1).addCommGroupIsoToAddEquiv
  exact e.toEquiv.nontrivial

/-- **`R¹ f_* 𝒪 ≠ 0` for the punctured plane.** Over a nonzero ring `R`, the first higher direct
image of the structure sheaf along `f : 𝔸²_R ∖ {0} ⟶ Spec R` is not the zero module. -/
theorem not_isZero_higherDirectImage_one_puncturedPlane :
    ¬ IsZero (((puncturedAffineSpace R (Fin 2)).hom.higherDirectImage 1).obj
      (SheafOfModules.unit (puncturedAffineSpace R (Fin 2)).left.ringCatSheaf)) := fun h ↦ by
  have := nontrivial_higherDirectImage_one_puncturedPlane R
  -- `Γ(M, ⊤)` is the value at `⊤` of the abelian presheaf `(Scheme.Modules.toPresheaf _).obj M`.
  exact not_subsingleton _ (AddCommGrpCat.subsingleton_of_isZero (G := Γ(_, ⊤))
    (((Scheme.Modules.toPresheaf _).map_isZero h).obj (.op ⊤)))

end TauCeti.PuncturedAffineSpace
