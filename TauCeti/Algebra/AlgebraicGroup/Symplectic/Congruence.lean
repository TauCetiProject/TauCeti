/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence
public import TauCeti.Algebra.AlgebraicGroup.Pinning.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth

/-!
# The symplectic group of another Gram matrix

The carrier of `Sp₂ₘ` is the constant-form subgroup scheme of `TauCeti.JFin m R`. Another
alternating Gram matrix `C` that is congruent to it, `P C Pᵀ = JFin m R` for an invertible
matrix `P`, gives the same group: conjugation by `P` is an isomorphism from
`ConstantForm.groupScheme R (m + m) C` onto `Sp₂ₘ` (`TauCeti.ConstantForm.groupSchemeCongr`).
This file records that isomorphism, the smoothness of the coordinate algebra of
`ConstantForm.groupScheme R (m + m) C` that it implies, and the pinning transported along it
from the standard pinning of `Sp₂ₘ` by `TauCeti.Pinning.comapOfIso`.

## Main declarations

* `TauCeti.Symplectic.constantFormCoordinateIso`: the coordinate Hopf algebra of the subgroup
  scheme preserving `C` is isomorphic to that of `Sp₂ₘ`.
* `TauCeti.Symplectic.constantFormGroupSchemeIso`: `ConstantForm.groupScheme R (m + m) C ≅ Sp₂ₘ`.
* `TauCeti.Symplectic.smooth_constantForm_of_congr`: the coordinate algebra of the subgroup
  scheme preserving `C` is smooth.
* `TauCeti.Symplectic.constantFormPinning`: the standard pinning of `Sp₂ₘ` transported to the
  subgroup scheme preserving `C`.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1, for transporting pinnings.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.Symplectic

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {C : Matrix (Fin (m + m)) (Fin (m + m)) R}

/-- **Another Gram matrix, in coordinates.** If `P C Pᵀ = JFin m R`, the coordinate Hopf algebra
of the subgroup scheme of `GL₂ₘ` preserving `C` is isomorphic to that of `Sp₂ₘ`, by conjugation
by `P`. -/
noncomputable def constantFormCoordinateIso (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    ConstantForm.coordinateHopfAlgebra R (m + m) C ≅ coordinateHopfAlgebra R m :=
  ConstantForm.coordinateHopfAlgebraCongr P hP

/-- The coordinate isomorphism to `Sp₂ₘ` is the coordinate isomorphism of congruent forms. -/
theorem constantFormCoordinateIso_def (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    constantFormCoordinateIso P hP = ConstantForm.coordinateHopfAlgebraCongr P hP :=
  (rfl)

/-- The coordinate isomorphism to `Sp₂ₘ` is induced by conjugation by `P⁻¹` on the coordinates
of `GL₂ₘ`: on points, it sends a symplectic matrix `M` to `P⁻¹ M P`. -/
theorem coordinateMap_comp_constantFormCoordinateIso_hom (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    ConstantForm.coordinateMap R (m + m) C ≫ (constantFormCoordinateIso P hP).hom =
      (GeneralLinear.conjCoordinateIso P⁻¹).hom ≫ coordinateMap R m :=
  ConstantForm.coordinateMap_comp_coordinateHopfAlgebraCongr_hom P hP

/-- **Another Gram matrix gives `Sp₂ₘ`.** If `P C Pᵀ = JFin m R`, conjugation by `P` is an
isomorphism from the subgroup scheme of `GL₂ₘ` preserving `C` onto `Sp₂ₘ`. -/
noncomputable def constantFormGroupSchemeIso (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    ConstantForm.groupScheme R (m + m) C ≅ groupScheme R m :=
  ConstantForm.groupSchemeCongr P hP

/-- The isomorphism onto `Sp₂ₘ` is the isomorphism of congruent forms. -/
theorem constantFormGroupSchemeIso_def (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    constantFormGroupSchemeIso P hP = ConstantForm.groupSchemeCongr P hP :=
  (rfl)

/-- The coordinate algebra of the subgroup scheme preserving a Gram matrix congruent to
`JFin m R` is smooth, as that of `Sp₂ₘ` is. -/
theorem smooth_constantForm_of_congr (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C) :=
  Algebra.Smooth.of_equiv
    (CommHopfAlgCat.ofIso (constantFormCoordinateIso P hP).symm).toAlgEquiv

/-- **The transported pinning.** For a Gram matrix `C` with `P C Pᵀ = JFin m R`, the standard
pinning of `Sp₂ₘ` pulled back along `TauCeti.Symplectic.constantFormCoordinateIso`: its torus
and Borel subgroup are the conjugates by `P⁻¹` of the diagonal torus and the isotropic-flag
Borel subgroup of `Sp₂ₘ`. The smoothness instance it needs holds by
`TauCeti.Symplectic.smooth_constantForm_of_congr`. -/
noncomputable def constantFormPinning [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    Pinning R (ConstantForm.coordinateHopfAlgebra R (m + m) C) m :=
  (standardPinning R m).comapOfIso (constantFormCoordinateIso P hP)

/-- The torus of the transported pinning is the pullback of the diagonal torus of `Sp₂ₘ`. -/
@[simp]
theorem constantFormPinning_torus [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    (constantFormPinning P hP).torus =
      (splitMaximalTorus R m).comapOfIso (constantFormCoordinateIso P hP) := by
  rw [constantFormPinning, Pinning.comapOfIso_torus, standardPinning_torus]

/-- The Borel subgroup of the transported pinning is the pullback of the isotropic-flag Borel
subgroup of `Sp₂ₘ`. -/
@[simp]
theorem constantFormPinning_borel [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    (constantFormPinning P hP).borel =
      (IsotropicFlag.definingHopfIdeal R m).comapOfSurjective
        (constantFormCoordinateIso P hP).hom.hom
        (ConcreteCategory.bijective_of_isIso (constantFormCoordinateIso P hP).hom).2 := by
  rw [constantFormPinning, Pinning.comapOfIso_borel, standardPinning_borel]

end TauCeti.Symplectic
