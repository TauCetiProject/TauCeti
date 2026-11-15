/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.LazardRing.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Universal

/-!
# Strict coordinate changes of formal group laws are represented by `L[b₁, b₂, …]`

A strict formal coordinate over a commutative ring `R` is a series
`φ(X) = X + ∑_{i ≥ 1} bᵢ X^(i + 1)`, determined by the arbitrary family `(bᵢ)` of its coefficients
(`TauCeti.FormalCoordinate.strictCoeffsEquiv`). Together with the universal property of the Lazard
ring `L` and the universal strict coordinate (`TauCeti.FormalCoordinate.strictLift`), this shows
that pairs `(F, φ)` of a commutative formal group law `F` over `R` and a strict coordinate `φ` over
`R` are the ring homomorphisms to `R` from the polynomial ring

  `L[b₁, b₂, …] = MvPolynomial ℕ+ LazardRing`.

Such a pair is a strict isomorphism `φ : F → φ • F` of formal group laws, where
`φ • F = φ(F(φ⁻¹(X), φ⁻¹(Y)))` is the change of coordinate. Its source `F` and target `φ • F` are
classified by two ring homomorphisms `L → L[b₁, b₂, …]`: the inclusion of constants
`η_L = MvPolynomial.C` for the source, and the **right unit** `η_R` for the target, which classifies
the change of coordinate of the universal formal group law by the universal strict coordinate
`X + ∑ bᵢ X^(i + 1)`. The **counit** `ε : L[b₁, b₂, …] → L`, classifying the universal formal group
law with the identity coordinate, sends every `bᵢ` to `0`, and `ε ∘ η_L = ε ∘ η_R = id`.

These are the unit and counit maps of the Hopf algebroid `(L, L[b₁, b₂, …])` that represents the
groupoid of commutative formal group laws and their strict isomorphisms; through Quillen's
theorem it is the Hopf algebroid `(MU_*, MU_*MU)` of complex cobordism. Its coproduct and
conjugation, and the remaining Hopf algebroid equations, are in
`TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid`.

## Main definitions

* `TauCeti.LazardRing.coordinateChangeLift`: the bijection between pairs of a commutative formal
  group law and a strict coordinate over `R` and ring homomorphisms `L[b₁, b₂, …] →+* R`.
* `TauCeti.LazardRing.rightUnit`: the right unit `η_R : L →+* L[b₁, b₂, …]`.
* `TauCeti.LazardRing.counit`: the counit `ε : L[b₁, b₂, …] →+* L`.

## Main results

* `TauCeti.LazardRing.coordinateChangeLift_comp_C`: `η_L` classifies the source `F`.
* `TauCeti.LazardRing.coordinateChangeLift_comp_rightUnit`: `η_R` classifies the target `φ • F`.
* `TauCeti.LazardRing.counit_comp_C`, `TauCeti.LazardRing.counit_comp_rightUnit`: `ε` is a
  retraction of both units.
* `TauCeti.LazardRing.map_comp_rightUnit`: the target of the strict isomorphism classified by any
  `f : L[b₁, b₂, …] →+* R` is classified by `f ∘ η_R`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
* J. Lurie, *Chromatic Homotopy Theory* (Harvard lecture notes, 2010), Lecture 3.
-/

public section

noncomputable section

namespace TauCeti

namespace LazardRing

variable {R : Type*} [CommRing R]

open MvPolynomial
open FormalCoordinate (universalStrictCoordinate)

/-- **Strict coordinate changes of commutative formal group laws are representable**: pairs of a
commutative formal group law `F` and a strict coordinate `φ` over `R` correspond to ring
homomorphisms `L[b₁, b₂, …] →+* R`. The homomorphism attached to `(F, φ)` restricts to the
homomorphism `L →+* R` classifying `F` and sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
def coordinateChangeLift :
    {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker ≃
      (MvPolynomial ℕ+ LazardRing →+* R) :=
  (lift.prodCongr (Equiv.refl _)).trans FormalCoordinate.strictLift

/-- The commutative formal group law classified by `f : L[b₁, b₂, …] →+* R` is the one classified
by its restriction along `η_L = C`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_fst (f : MvPolynomial ℕ+ LazardRing →+* R) :
    (coordinateChangeLift.symm f).1 = lift.symm (f.comp C) := by
  simp [coordinateChangeLift]

/-- The strict coordinate classified by `f : L[b₁, b₂, …] →+* R` has coefficients `f (bᵢ)`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_snd (f : MvPolynomial ℕ+ LazardRing →+* R) :
    (coordinateChangeLift.symm f).2 = FormalCoordinate.strictCoeffsEquiv (f ∘ X) := by
  simp [coordinateChangeLift]

/-- The homomorphism classifying `(F, φ)` restricts along `η_L = C` to the homomorphism classifying
the source `F`. -/
@[simp]
theorem coordinateChangeLift_comp_C
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker) :
    (coordinateChangeLift p).comp C = lift p.1 :=
  FormalCoordinate.strictLift_comp_C _

/-- The homomorphism classifying `(F, φ)` agrees on constants with the homomorphism classifying the
source `F`. -/
@[simp]
theorem coordinateChangeLift_C
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker)
    (r : LazardRing) :
    coordinateChangeLift p (C r) = lift p.1 r :=
  FormalCoordinate.strictLift_C _ r

/-- The homomorphism classifying `(F, φ)` sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
@[simp]
theorem coordinateChangeLift_X
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker)
    (i : ℕ+) :
    coordinateChangeLift p (X i) = PowerSeries.coeff (i + 1) p.2.1.toPowerSeries :=
  FormalCoordinate.strictLift_X _ i

/-- The homomorphism classifying `(F, φ)` specializes the universal strict coordinate to `φ`. -/
@[simp]
theorem map_coordinateChangeLift_universalStrictCoordinate
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker) :
    FormalCoordinate.map (coordinateChangeLift p) universalStrictCoordinate = p.2.1 :=
  FormalCoordinate.map_strictLift_universalStrictCoordinate _

/-- The **right unit** `η_R : L →+* L[b₁, b₂, …]`: the homomorphism classifying the change of
coordinate of the universal formal group law by the universal strict coordinate
`X + ∑ bᵢ X^(i + 1)`. -/
def rightUnit : LazardRing →+* MvPolynomial ℕ+ LazardRing :=
  lift ⟨universalStrictCoordinate (A := LazardRing) • formalGroup.map C, inferInstance⟩

/-- The base change of the universal formal group law along `η_R` is the change of coordinate of
its base change along `η_L` by the universal strict coordinate. -/
@[simp]
theorem map_rightUnit :
    formalGroup.map rightUnit = universalStrictCoordinate (A := LazardRing) • formalGroup.map C :=
  map_lift _

/-- The homomorphism classifying `(F, φ)` restricts along `η_R` to the homomorphism classifying
the target `φ • F` of the strict isomorphism `φ`. -/
@[simp]
theorem coordinateChangeLift_comp_rightUnit
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker) :
    (coordinateChangeLift p).comp rightUnit =
      lift ⟨p.2.1 • p.1.1, have := p.1.2; inferInstance⟩ :=
  hom_ext <| by
    rw [← FormalGroup.map_comp, map_rightUnit, FormalGroup.map_smul,
      map_coordinateChangeLift_universalStrictCoordinate, FormalGroup.map_comp,
      coordinateChangeLift_comp_C, map_lift, map_lift]

/-- A ring homomorphism `f` out of `L[b₁, b₂, …]` restricts along `η_R` to the homomorphism
classifying the target of the strict isomorphism classified by `f`: the base change of the universal
formal group law along `f ∘ η_R` is the base change of the universal strict coordinate along `f`
acting on the base change along `f ∘ η_L`. -/
theorem map_comp_rightUnit (f : MvPolynomial ℕ+ LazardRing →+* R) :
    formalGroup.map (f.comp rightUnit) =
      FormalCoordinate.map f universalStrictCoordinate • formalGroup.map (f.comp C) := by
  rw [← FormalGroup.map_comp, map_rightUnit, FormalGroup.map_smul, FormalGroup.map_comp]

/-- The **counit** `ε : L[b₁, b₂, …] →+* L`, classifying the universal formal group law with the
identity coordinate. It sends every `bᵢ` to `0`. -/
def counit : MvPolynomial ℕ+ LazardRing →+* LazardRing :=
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
theorem counit_comp_C : counit.comp C = RingHom.id LazardRing :=
  FormalCoordinate.strictLift_comp_C _

/-- The counit is the identity on constants. -/
@[simp]
theorem counit_C (r : LazardRing) : counit (C r) = r :=
  FormalCoordinate.strictLift_C _ r

/-- The counit is a retraction of the right unit `η_R`: changing the coordinate by the identity
does not change a formal group law. -/
@[simp]
theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id LazardRing :=
  hom_ext <| by
    rw [map_comp_rightUnit, map_counit_universalStrictCoordinate, counit_comp_C, one_smul]

end LazardRing

end TauCeti
