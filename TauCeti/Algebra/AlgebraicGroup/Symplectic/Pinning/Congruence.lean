/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence.Basic
public import TauCeti.Algebra.AlgebraicGroup.Pinning.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Basic

/-!
# The symplectic group of another Gram matrix

The carrier of `Sp₂ₘ` is the constant-form subgroup scheme of `TauCeti.JFin m R`. Another
alternating Gram matrix `C` that is congruent to it, `P C Pᵀ = JFin m R` for an invertible
matrix `P`, gives the same group: conjugation by `P` is an isomorphism from
`ConstantForm.groupScheme R (m + m) C` onto `Sp₂ₘ` (`TauCeti.ConstantForm.groupSchemeCongr`).
Since `Sp₂ₘ` and its coordinate Hopf algebra are abbreviations for the constant-form ones, that
isomorphism and its coordinate version `TauCeti.ConstantForm.coordinateHopfAlgebraCongr` apply
directly with `C' = JFin m R`; so does the smoothness transfer
`TauCeti.ConstantForm.smooth_of_congr`, with the smoothness of `Sp₂ₘ`. This file records the
pinning transported along them from the standard pinning of `Sp₂ₘ` by
`TauCeti.Pinning.comapOfIso`.

## Main declarations

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

/-- **The transported pinning.** For a Gram matrix `C` with `P C Pᵀ = JFin m R`, the standard
pinning of `Sp₂ₘ` pulled back along `TauCeti.ConstantForm.coordinateHopfAlgebraCongr`: its torus
and Borel subgroup are the conjugates by `P⁻¹` of the diagonal torus and the isotropic-flag
Borel subgroup of `Sp₂ₘ`. The smoothness instance it needs holds by
`TauCeti.ConstantForm.smooth_of_congr`. -/
noncomputable def constantFormPinning [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    Pinning R (ConstantForm.coordinateHopfAlgebra R (m + m) C) m :=
  (standardPinning R m).comapOfIso (ConstantForm.coordinateHopfAlgebraCongr P hP)

/-- The torus of the transported pinning is the pullback of the diagonal torus of `Sp₂ₘ`. -/
@[simp]
theorem constantFormPinning_torus [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    (constantFormPinning P hP).torus =
      (splitMaximalTorus R m).comapOfIso (ConstantForm.coordinateHopfAlgebraCongr P hP) := by
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
        (ConstantForm.coordinateHopfAlgebraCongr P hP).hom.hom
        (ConcreteCategory.bijective_of_isIso
          (ConstantForm.coordinateHopfAlgebraCongr P hP).hom).2 := by
  rw [constantFormPinning, Pinning.comapOfIso_borel, standardPinning_borel]

end TauCeti.Symplectic
