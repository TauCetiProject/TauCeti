/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified

import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes

/-!
# Unramified and tamely ramified covers in codimension one

Let `X` be a scheme, `U ⊆ X` an open subscheme and `f : Y ⟶ U` a morphism, typically a finite
étale cover of `U`. Following Stacks, Section 58.31, `Y` is *unramified* (resp. *tamely
ramified*) *over `X` in codimension one* if for every codimension-one point `ξ ∉ U` of `X` the
generic fibre of `Y` over `Spec 𝒪_{X,ξ}` is unramified (resp. tamely ramified) with respect to
`𝒪_{X,ξ}`, in the sense of `TauCeti.Algebra.IsUnramifiedWRT` (resp.
`TauCeti.Algebra.IsTamelyRamifiedWRT`).

Stacks writes the generic fibre as `Y ×_U Spec K_ξ = Spec L_ξ`, where `K_ξ` is the fraction field
of the discrete valuation ring `𝒪_{X,ξ}`, and asks the condition of each field factor of the
finite separable `K_ξ`-algebra `L_ξ`. Here the condition is stated pointwise. The points of
`Spec 𝒪_{X,ξ}` map bijectively onto the generizations of `ξ`; for a discrete valuation ring the
only one other than `ξ` is the image `η` of the generic point, and `κ(η)` is `K_ξ`
(`TauCeti.AlgebraicGeometry.Scheme.isFractionRing_residueField_of_specializes`). The field
factors of `L_ξ` are the residue fields `κ(y)` of the points `y` of `Y` over `η`, as
`𝒪_{X,ξ}`-algebras through `𝒪_{X,ξ} ⟶ κ(η) ⟶ κ(y)`. So the definitions ask, for every `y : Y`
whose image in `X` generizes `ξ`, that `κ(y)` be unramified (resp. tamely ramified) with respect
to `𝒪_{X,ξ}`. Since `ξ ∉ U`, such an image is never `ξ` itself.

Hypotheses such as `X` locally Noetherian, `U` dense, `f` finite étale and `𝒪_{X,ξ}` a discrete
valuation ring are carried by the statements that use them, not by the definitions.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsUnramifiedInCodimOne f`: `f : Y ⟶ U` is unramified over `X`
  in codimension one.
* `AlgebraicGeometry.Scheme.Hom.IsTamelyRamifiedInCodimOne f`: `f : Y ⟶ U` is tamely ramified
  over `X` in codimension one.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsUnramifiedInCodimOne.isTamelyRamifiedInCodimOne`: unramified
  in codimension one implies tamely ramified in codimension one.
* `AlgebraicGeometry.Scheme.Hom.isUnramifiedInCodimOne_of_isOpenImmersion`: if the codimension
  one points outside `U` have regular local rings, every open subscheme of `U`, for instance the
  trivial cover `𝟙 U`, is unramified over `X` in codimension one.

## References

* [Stacks Project, Section 58.31](https://stacks.math.columbia.edu/tag/0BSE), the definitions
  preceding Lemma 58.31.1.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} {U : X.Opens} (f : Y ⟶ U)

/-- `f : Y ⟶ U` is **unramified over `X` in codimension one**: for every codimension-one point `ξ`
of `X` outside `U` and every point `y` of `Y` whose image in `X` generizes `ξ`, the residue field
`κ(y)` is unramified with respect to `𝒪_{X,ξ}`, as an algebra through `𝒪_{X,ξ} ⟶ κ(f y) ⟶ κ(y)`.
For `f` finite étale and `𝒪_{X,ξ}` a discrete valuation ring, these residue fields are the field
factors of the generic fibre `L_ξ` of `Y` over `Spec 𝒪_{X,ξ}`. -/
@[stacks 0BSE "unramified over `X` in codimension one, stated on residue fields of points"]
def IsUnramifiedInCodimOne : Prop :=
  ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
    letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
      (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
    TauCeti.Algebra.IsUnramifiedWRT (X.presheaf.stalk ξ) (Y.residueField y)

/-- `f : Y ⟶ U` is **tamely ramified over `X` in codimension one**: for every codimension-one point
`ξ` of `X` outside `U` and every point `y` of `Y` whose image in `X` generizes `ξ`, the residue
field `κ(y)` is tamely ramified with respect to `𝒪_{X,ξ}`, as an algebra through
`𝒪_{X,ξ} ⟶ κ(f y) ⟶ κ(y)`. For `f` finite étale and `𝒪_{X,ξ}` a discrete valuation ring, these
residue fields are the field factors of the generic fibre `L_ξ` of `Y` over `Spec 𝒪_{X,ξ}`. -/
@[stacks 0BSE "tamely ramified over `X` in codimension one, stated on residue fields of points"]
def IsTamelyRamifiedInCodimOne : Prop :=
  ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
    letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
      (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
    TauCeti.Algebra.IsTamelyRamifiedWRT (X.presheaf.stalk ξ) (Y.residueField y)

/-- Unfolds `IsUnramifiedInCodimOne` to its condition on the residue fields of points. -/
theorem isUnramifiedInCodimOne_def :
    f.IsUnramifiedInCodimOne ↔
      ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
        letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
          (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
        TauCeti.Algebra.IsUnramifiedWRT (X.presheaf.stalk ξ) (Y.residueField y) :=
  Iff.rfl

/-- Unfolds `IsTamelyRamifiedInCodimOne` to its condition on the residue fields of points. -/
theorem isTamelyRamifiedInCodimOne_def :
    f.IsTamelyRamifiedInCodimOne ↔
      ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
        letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
          (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
        TauCeti.Algebra.IsTamelyRamifiedWRT (X.presheaf.stalk ξ) (Y.residueField y) :=
  Iff.rfl

variable {f}

/-- A cover unramified over `X` in codimension one is tamely ramified over `X` in codimension
one. -/
theorem IsUnramifiedInCodimOne.isTamelyRamifiedInCodimOne (hf : f.IsUnramifiedInCodimOne) :
    f.IsTamelyRamifiedInCodimOne := fun ξ hξ y h ↦
  letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
    (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
  (hf ξ hξ y h).isTamelyRamifiedWRT

/-- If the local rings of `X` at the codimension-one points outside `U` are regular, so discrete
valuation rings, then an open immersion into `U`, for instance the trivial cover `𝟙 U`, is
unramified over `X` in codimension one: each residue field `κ(y)` is the fraction field `K_ξ`. -/
theorem isUnramifiedInCodimOne_of_isOpenImmersion [IsOpenImmersion f]
    (hX : ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → IsRegularLocalRing (X.presheaf.stalk ξ)) :
    f.IsUnramifiedInCodimOne := by
  intro ξ hξ y h
  have := hX ξ hξ
  have hne : (f ≫ U.ι) y ≠ ξ := fun he ↦ hξ (he ▸ (f y).2)
  -- The residue field at the image of `y` is the fraction field of `𝒪_{X,ξ}`.
  let := (X.presheaf.stalkSpecializes h ≫ X.residue _).hom.toAlgebra
  have := Scheme.isFractionRing_residueField_of_specializes h hne
  -- An open immersion induces an isomorphism of residue fields.
  let := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
    (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
  have : IsFractionRing (X.presheaf.stalk ξ) (Y.residueField y) :=
    IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv
      (f := (asIso ((f ≫ U.ι).residueFieldMap y)).commRingCatIsoToRingEquiv) fun _ ↦ rfl)
  exact TauCeti.Algebra.isUnramifiedWRT_of_isFractionRing _ _

end AlgebraicGeometry.Scheme.Hom
