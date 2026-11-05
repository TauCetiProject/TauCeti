/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Universal
public import TauCeti.RingTheory.PowerSeries.Coordinate.Universal

/-!
# Strict coordinate changes of formal group laws of exponent two

Write `MO = ExponentTwoLazardRing = 𝔽₂[aᵢ : i ≠ 2ᵏ - 1]` for the universal ring of commutative
formal group laws `F` with `[2]_F = 0`. Changing the coordinate of such an `F` by a strict
coordinate `φ = X + ∑ bᵢ X^(i + 1)` gives again a law of exponent two,
`φ • F = φ(F(φ⁻¹(X), φ⁻¹(Y)))` (`FormalGroup.nsmulSeries_smul_eq_zero_iff`), and the coefficients
`bᵢ` of `φ` are arbitrary (`TauCeti.FormalCoordinate.strictLift`). Hence pairs `(F, φ)` over `R`,
that is strict isomorphisms `φ : F → φ • F` between formal group laws of exponent two, are the ring
homomorphisms to `R` from the polynomial ring

  `MO[b₁, b₂, …] = MvPolynomial ℕ+ ExponentTwoLazardRing`.

All `bᵢ` occur, including those with `i = 2ᵏ - 1`: the normalisation of the logarithm restricts the
coefficients of a formal group law of exponent two, not those of an isomorphism between two of
them.

The source `F` and the target `φ • F` are classified by the inclusion of constants
`η_L = MvPolynomial.C` and by the **right unit** `η_R`, which classifies the change of coordinate of
the universal formal group law of exponent two by the universal strict coordinate. The **counit**
`ε`, classifying the identity coordinate, is a retraction of both. Through Quillen's
identification of `MO` with the unoriented bordism ring `MO_*`, the ring `MO[b₁, b₂, …]`
corresponds to the cooperations `MO_*MO`, with `bᵢ` in degree `i`; the grading is not treated
here.

The construction follows the one for the Lazard ring in
`TauCeti.RingTheory.FormalGroup.CoordinateChange.Lazard` (`TauCeti.LazardRing.coordinateChangeLift`,
`TauCeti.LazardRing.rightUnit`, `TauCeti.LazardRing.counit` and their lemmas), with `LazardRing`
replaced by `ExponentTwoLazardRing` and the condition `[2]_F = 0` carried along.

## Main definitions

* `TauCeti.ExponentTwoLazardRing.coordinateChangeLift`: the bijection between pairs of a
  commutative formal group law of exponent two and a strict coordinate over `R` and ring
  homomorphisms `MO[b₁, b₂, …] →+* R`.
* `TauCeti.ExponentTwoLazardRing.rightUnit`: the right unit `η_R : MO →+* MO[b₁, b₂, …]`.
* `TauCeti.ExponentTwoLazardRing.counit`: the counit `ε : MO[b₁, b₂, …] →+* MO`.

## Main results

* `TauCeti.ExponentTwoLazardRing.coordinateChangeLift_comp_C`: `η_L` classifies the source `F`.
* `TauCeti.ExponentTwoLazardRing.coordinateChangeLift_comp_rightUnit`: `η_R` classifies the
  target `φ • F`.
* `TauCeti.ExponentTwoLazardRing.counit_comp_C`,
  `TauCeti.ExponentTwoLazardRing.counit_comp_rightUnit`: `ε` is a retraction of both units.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

namespace TauCeti

namespace ExponentTwoLazardRing

variable {R : Type*} [CommRing R]

open MvPolynomial
open FormalCoordinate (universalStrictCoordinate)

/-- **Strict coordinate changes of formal group laws of exponent two are representable**: pairs of
a commutative formal group law `F` over `R` with `[2]_F = 0` and a strict coordinate `φ` over `R`
correspond to ring homomorphisms `MO[b₁, b₂, …] →+* R`. The homomorphism attached to `(F, φ)`
restricts to the homomorphism `MO →+* R` classifying `F` and sends `bᵢ` to the coefficient of
`X^(i + 1)` in `φ`. -/
def coordinateChangeLift :
    {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
        (FormalCoordinate.linearCoeff (R := R)).ker ≃
      (MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :=
  (lift.prodCongr (Equiv.refl _)).trans FormalCoordinate.strictLift

/-- The formal group law classified by `f : MO[b₁, b₂, …] →+* R` is the one classified by its
restriction along `η_L = C`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_fst (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    (coordinateChangeLift.symm f).1 = lift.symm (f.comp C) := by
  simp [coordinateChangeLift]

/-- The strict coordinate classified by `f : MO[b₁, b₂, …] →+* R` has coefficients `f (bᵢ)`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_snd (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    (coordinateChangeLift.symm f).2 = FormalCoordinate.strictCoeffsEquiv (f ∘ X) := by
  simp [coordinateChangeLift]

/-- The homomorphism classifying `(F, φ)` restricts along `η_L = C` to the homomorphism classifying
the source `F`. -/
@[simp]
theorem coordinateChangeLift_comp_C
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker) :
    (coordinateChangeLift p).comp C = lift p.1 :=
  FormalCoordinate.strictLift_comp_C _

/-- The homomorphism classifying `(F, φ)` agrees on constants with the homomorphism classifying the
source `F`. -/
@[simp]
theorem coordinateChangeLift_C
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker)
    (r : ExponentTwoLazardRing) :
    coordinateChangeLift p (C r) = lift p.1 r :=
  FormalCoordinate.strictLift_C _ r

/-- The homomorphism classifying `(F, φ)` sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
@[simp]
theorem coordinateChangeLift_X
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker)
    (i : ℕ+) :
    coordinateChangeLift p (X i) = PowerSeries.coeff (i + 1) p.2.1.toPowerSeries :=
  FormalCoordinate.strictLift_X _ i

/-- The homomorphism classifying `(F, φ)` specializes the universal strict coordinate to `φ`. -/
@[simp]
theorem map_coordinateChangeLift_universalStrictCoordinate
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker) :
    FormalCoordinate.map (coordinateChangeLift p) universalStrictCoordinate = p.2.1 :=
  FormalCoordinate.map_strictLift_universalStrictCoordinate _

/-- The **right unit** `η_R : MO →+* MO[b₁, b₂, …]`: the homomorphism classifying the change of
coordinate of the universal formal group law of exponent two by the universal strict coordinate
`X + ∑ bᵢ X^(i + 1)`. -/
def rightUnit : ExponentTwoLazardRing →+* MvPolynomial ℕ+ ExponentTwoLazardRing :=
  lift ⟨universalStrictCoordinate (A := ExponentTwoLazardRing) • formalGroup.map C, inferInstance,
    by simp⟩

/-- The base change of the universal formal group law of exponent two along `η_R` is the change of
coordinate of its base change along `η_L` by the universal strict coordinate. -/
@[simp]
theorem map_rightUnit :
    formalGroup.map rightUnit =
      universalStrictCoordinate (A := ExponentTwoLazardRing) • formalGroup.map C :=
  map_lift _

/-- The homomorphism classifying `(F, φ)` restricts along `η_R` to the homomorphism classifying
the target `φ • F` of the strict isomorphism `φ`. -/
@[simp]
theorem coordinateChangeLift_comp_rightUnit
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker) :
    (coordinateChangeLift p).comp rightUnit =
      lift ⟨p.2.1 • p.1.1, have := p.1.2.1; inferInstance,
        (FormalGroup.nsmulSeries_smul_eq_zero_iff _ _).mpr p.1.2.2⟩ :=
  hom_ext <| by
    rw [← FormalGroup.map_comp, map_rightUnit, FormalGroup.map_smul,
      map_coordinateChangeLift_universalStrictCoordinate, FormalGroup.map_comp,
      coordinateChangeLift_comp_C, map_lift, map_lift]

/-- A ring homomorphism `f` out of `MO[b₁, b₂, …]` restricts along `η_R` to the homomorphism
classifying the target of the strict isomorphism classified by `f`: the base change of the universal
formal group law along `f ∘ η_R` is the base change of the universal strict coordinate along `f`
acting on the base change along `f ∘ η_L`. -/
theorem map_comp_rightUnit (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    formalGroup.map (f.comp rightUnit) =
      FormalCoordinate.map f universalStrictCoordinate • formalGroup.map (f.comp C) := by
  rw [← FormalGroup.map_comp, map_rightUnit, FormalGroup.map_smul, FormalGroup.map_comp]

/-- The **counit** `ε : MO[b₁, b₂, …] →+* MO`, classifying the universal formal group law of
exponent two with the identity coordinate. It sends every `bᵢ` to `0`. -/
def counit : MvPolynomial ℕ+ ExponentTwoLazardRing →+* ExponentTwoLazardRing :=
  FormalCoordinate.strictLift (RingHom.id _, 1)

@[simp]
theorem counit_X (i : ℕ+) : counit (X i) = 0 := by
  simp [counit, PowerSeries.coeff_X]

/-- The counit classifies the identity coordinate. -/
@[simp]
theorem map_counit_universalStrictCoordinate :
    FormalCoordinate.map counit universalStrictCoordinate = 1 :=
  FormalCoordinate.map_strictLift_universalStrictCoordinate _

/-- The counit is a retraction of the left unit `η_L = C`. -/
@[simp]
theorem counit_comp_C : counit.comp C = RingHom.id ExponentTwoLazardRing :=
  FormalCoordinate.strictLift_comp_C _

/-- The counit is the identity on constants. -/
@[simp]
theorem counit_C (r : ExponentTwoLazardRing) : counit (C r) = r :=
  FormalCoordinate.strictLift_C _ r

/-- The counit is a retraction of the right unit `η_R`: changing the coordinate by the identity
does not change a formal group law. -/
@[simp]
theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id ExponentTwoLazardRing :=
  hom_ext <| by
    rw [map_comp_rightUnit, map_counit_universalStrictCoordinate, counit_comp_C, one_smul]

end ExponentTwoLazardRing

end TauCeti
