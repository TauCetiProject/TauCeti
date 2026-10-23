/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.LazardRing

/-!
# Strict coordinate changes of formal group laws are represented by `L[b₁, b₂, …]`

A strict formal coordinate over a commutative ring `R` is a series
`φ(X) = X + ∑_{i ≥ 1} bᵢ X^(i + 1)`, determined by the arbitrary family `(bᵢ)` of its coefficients
(`TauCeti.FormalCoordinate.strictCoeffsEquiv`). Together with the universal property of the Lazard
ring `L`, this shows that pairs `(F, φ)` of a commutative formal group law `F` over `R` and a strict
coordinate `φ` over `R` are the ring homomorphisms to `R` from the polynomial ring

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
theorem it is the Hopf algebroid `(MU_*, MU_*MU)` of complex cobordism. The coproduct and
conjugation of this Hopf algebroid, and its remaining equations, are not constructed here.

## Main definitions

* `TauCeti.LazardRing.universalStrictCoordinate`: the strict coordinate `X + ∑ bᵢ X^(i + 1)` over
  `L[b₁, b₂, …]`.
* `TauCeti.LazardRing.coordinateChangeLift`: the bijection between pairs of a commutative formal
  group law and a strict coordinate over `R` and ring homomorphisms `L[b₁, b₂, …] →+* R`.
* `TauCeti.LazardRing.rightUnit`: the right unit `η_R : L →+* L[b₁, b₂, …]`.
* `TauCeti.LazardRing.counit`: the counit `ε : L[b₁, b₂, …] →+* L`.

## Main results

* `TauCeti.LazardRing.coordinateChangeLift_comp_C`: `η_L` classifies the source `F`.
* `TauCeti.LazardRing.coordinateChangeLift_comp_rightUnit`: `η_R` classifies the target `φ • F`.
* `TauCeti.LazardRing.counit_comp_C`, `TauCeti.LazardRing.counit_comp_rightUnit`: `ε` is a
  retraction of both units.

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

/-- The universal strict coordinate `X + ∑_{i ≥ 1} bᵢ X^(i + 1)` over `L[b₁, b₂, …]`, whose
coefficients are the variables `bᵢ`. -/
def universalStrictCoordinate : FormalCoordinate (MvPolynomial ℕ+ LazardRing) :=
  FormalCoordinate.ofStrictCoeffs X

/-- The strict coordinate `universalStrictCoordinate` has the variable `bᵢ` as its coefficient of
`X^(i + 1)`. -/
@[simp]
theorem coeff_succ_universalStrictCoordinate (i : ℕ+) :
    PowerSeries.coeff (i + 1) universalStrictCoordinate.toPowerSeries = X i :=
  FormalCoordinate.coeff_succ_ofStrictCoeffs X i

/-- **Strict coordinate changes of commutative formal group laws are representable**: pairs of a
commutative formal group law `F` and a strict coordinate `φ` over `R` correspond to ring
homomorphisms `L[b₁, b₂, …] →+* R`. The homomorphism attached to `(F, φ)` restricts to the
homomorphism `L →+* R` classifying `F` and sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
def coordinateChangeLift :
    {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker ≃
      (MvPolynomial ℕ+ LazardRing →+* R) where
  toFun p := eval₂Hom (lift p.1) (FormalCoordinate.strictCoeffsEquiv.symm p.2)
  invFun f := (lift.symm (f.comp C), FormalCoordinate.strictCoeffsEquiv (f ∘ X))
  left_inv p := by
    have h : ⇑(eval₂Hom (lift p.1) (FormalCoordinate.strictCoeffsEquiv.symm p.2)) ∘ X =
        FormalCoordinate.strictCoeffsEquiv.symm p.2 :=
      funext fun i ↦ eval₂Hom_X' _ _ i
    refine Prod.ext ?_ ?_ <;> dsimp only
    · rw [(RingHom.ext (eval₂Hom_C _ _) : (eval₂Hom (lift p.1) _).comp C = lift p.1),
        Equiv.symm_apply_apply]
    · rw [h, Equiv.apply_symm_apply]
  right_inv f := ringHom_ext' (RingHom.ext fun r ↦ by simp) fun i ↦ by simp

/-- The commutative formal group law classified by `f : L[b₁, b₂, …] →+* R` is the one classified
by its restriction along `η_L = C`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_fst (f : MvPolynomial ℕ+ LazardRing →+* R) :
    (coordinateChangeLift.symm f).1 = lift.symm (f.comp C) :=
  (rfl)

/-- The strict coordinate classified by `f : L[b₁, b₂, …] →+* R` has coefficients `f (bᵢ)`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_snd (f : MvPolynomial ℕ+ LazardRing →+* R) :
    (coordinateChangeLift.symm f).2 = FormalCoordinate.strictCoeffsEquiv (f ∘ X) :=
  (rfl)

/-- The homomorphism classifying `(F, φ)` restricts along `η_L = C` to the homomorphism classifying
the source `F`. -/
@[simp]
theorem coordinateChangeLift_comp_C
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker) :
    (coordinateChangeLift p).comp C = lift p.1 :=
  RingHom.ext (eval₂Hom_C _ _)

/-- The homomorphism classifying `(F, φ)` agrees on constants with the homomorphism classifying the
source `F`. -/
@[simp]
theorem coordinateChangeLift_C
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker)
    (r : LazardRing) :
    coordinateChangeLift p (C r) = lift p.1 r :=
  RingHom.congr_fun (coordinateChangeLift_comp_C p) r

/-- The homomorphism classifying `(F, φ)` sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
@[simp]
theorem coordinateChangeLift_X
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker)
    (i : ℕ+) :
    coordinateChangeLift p (X i) = PowerSeries.coeff (i + 1) p.2.1.toPowerSeries :=
  (eval₂Hom_X' _ _ _).trans (FormalCoordinate.strictCoeffsEquiv_symm_apply p.2 i)

/-- The homomorphism classifying `(F, φ)` specializes the universal strict coordinate to `φ`. -/
@[simp]
theorem map_coordinateChangeLift_universalStrictCoordinate
    (p : {F : FormalGroup R // F.IsComm} × (FormalCoordinate.linearCoeff (R := R)).ker) :
    FormalCoordinate.map (coordinateChangeLift p) universalStrictCoordinate = p.2.1 := by
  have h : ⇑(coordinateChangeLift p) ∘ X = FormalCoordinate.strictCoeffsEquiv.symm p.2 :=
    funext fun i ↦ by simp
  rw [universalStrictCoordinate, FormalCoordinate.map_ofStrictCoeffs, h,
    ← FormalCoordinate.coe_strictCoeffsEquiv_apply, Equiv.apply_symm_apply]

/-- The **right unit** `η_R : L →+* L[b₁, b₂, …]`: the homomorphism classifying the change of
coordinate of the universal formal group law by the universal strict coordinate
`X + ∑ bᵢ X^(i + 1)`. -/
def rightUnit : LazardRing →+* MvPolynomial ℕ+ LazardRing :=
  lift ⟨universalStrictCoordinate • formalGroup.map C, inferInstance⟩

/-- The base change of the universal formal group law along `η_R` is the change of coordinate of
its base change along `η_L` by the universal strict coordinate. -/
@[simp]
theorem map_rightUnit :
    formalGroup.map rightUnit = universalStrictCoordinate • formalGroup.map C :=
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

/-- The **counit** `ε : L[b₁, b₂, …] →+* L`, classifying the universal formal group law with the
identity coordinate. It sends every `bᵢ` to `0`. -/
def counit : MvPolynomial ℕ+ LazardRing →+* LazardRing :=
  coordinateChangeLift (⟨formalGroup, inferInstance⟩, 1)

@[simp]
theorem counit_X (i : ℕ+) : counit (X i) = 0 := by
  simp [counit, PowerSeries.coeff_X]

/-- The counit is a retraction of the left unit `η_L = C`. -/
@[simp]
theorem counit_comp_C : counit.comp C = RingHom.id LazardRing :=
  (coordinateChangeLift_comp_C _).trans <| hom_ext <| by rw [map_lift, FormalGroup.map_id]

/-- The counit is the identity on constants. -/
@[simp]
theorem counit_C (r : LazardRing) : counit (C r) = r :=
  RingHom.congr_fun counit_comp_C r

/-- The counit is a retraction of the right unit `η_R`: changing the coordinate by the identity
does not change a formal group law. -/
@[simp]
theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id LazardRing :=
  (coordinateChangeLift_comp_rightUnit _).trans <| hom_ext <| by
    rw [map_lift, FormalGroup.map_id]
    exact one_smul _ _

end LazardRing

end TauCeti
