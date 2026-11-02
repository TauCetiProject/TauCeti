/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Universal

/-!
# Strict coordinate changes of formal group laws of exponent two

Write `MO = ExponentTwoLazardRing = 𝔽₂[aᵢ : i ≠ 2ᵏ - 1]` for the universal ring of commutative
formal group laws `F` with `[2]_F = 0`. Changing the coordinate of such an `F` by a strict
coordinate `φ = X + ∑ bᵢ X^(i + 1)` gives again a law of exponent two,
`φ • F = φ(F(φ⁻¹(X), φ⁻¹(Y)))` (`FormalGroup.nsmulSeries_smul_eq_zero_iff`), and the coefficients
`bᵢ` of `φ` are arbitrary. Hence pairs `(F, φ)` over `R`, that is strict isomorphisms
`φ : F → φ • F` between formal group laws of exponent two, are the ring homomorphisms to `R` from
the polynomial ring

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

## Main definitions

* `TauCeti.ExponentTwoLazardRing.universalStrictCoordinate`: the strict coordinate
  `X + ∑ bᵢ X^(i + 1)` over `MO[b₁, b₂, …]`.
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
* `TauCeti.ExponentTwoLazardRing.ringHom_ext_universalStrictCoordinate`: a ring homomorphism out
  of `MO[b₁, b₂, …]` is determined by the pair `(F, φ)` it classifies.

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

/-- Every base change of the universal formal group law of exponent two has exponent two. -/
@[simp]
theorem nsmulSeries_two_map_formalGroup (f : ExponentTwoLazardRing →+* R) :
    (formalGroup.map f).nsmulSeries 2 = 0 := by
  rw [← FormalGroup.map_nsmulSeries, nsmulSeries_two_formalGroup, map_zero]

/-- The universal strict coordinate `X + ∑_{i ≥ 1} bᵢ X^(i + 1)` over `MO[b₁, b₂, …]`, whose
coefficients are the variables `bᵢ`. -/
def universalStrictCoordinate : FormalCoordinate (MvPolynomial ℕ+ ExponentTwoLazardRing) :=
  FormalCoordinate.ofStrictCoeffs X

/-- The strict coordinate `universalStrictCoordinate` has the variable `bᵢ` as its coefficient of
`X^(i + 1)`. -/
@[simp]
theorem coeff_succ_universalStrictCoordinate (i : ℕ+) :
    PowerSeries.coeff (i + 1) universalStrictCoordinate.toPowerSeries = X i :=
  FormalCoordinate.coeff_succ_ofStrictCoeffs X i

/-- **Strict coordinate changes of formal group laws of exponent two are representable**: pairs of
a commutative formal group law `F` over `R` with `[2]_F = 0` and a strict coordinate `φ` over `R`
correspond to ring homomorphisms `MO[b₁, b₂, …] →+* R`. The homomorphism attached to `(F, φ)`
restricts to the homomorphism `MO →+* R` classifying `F` and sends `bᵢ` to the coefficient of
`X^(i + 1)` in `φ`. -/
def coordinateChangeLift :
    {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
        (FormalCoordinate.linearCoeff (R := R)).ker ≃
      (MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) where
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

/-- The formal group law classified by `f : MO[b₁, b₂, …] →+* R` is the one classified by its
restriction along `η_L = C`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_fst (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    (coordinateChangeLift.symm f).1 = lift.symm (f.comp C) :=
  (rfl)

/-- The strict coordinate classified by `f : MO[b₁, b₂, …] →+* R` has coefficients `f (bᵢ)`. -/
@[simp]
theorem coordinateChangeLift_symm_apply_snd (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    (coordinateChangeLift.symm f).2 = FormalCoordinate.strictCoeffsEquiv (f ∘ X) :=
  (rfl)

/-- The homomorphism classifying `(F, φ)` restricts along `η_L = C` to the homomorphism classifying
the source `F`. -/
@[simp]
theorem coordinateChangeLift_comp_C
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker) :
    (coordinateChangeLift p).comp C = lift p.1 :=
  RingHom.ext (eval₂Hom_C _ _)

/-- The homomorphism classifying `(F, φ)` agrees on constants with the homomorphism classifying the
source `F`. -/
@[simp]
theorem coordinateChangeLift_C
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker)
    (r : ExponentTwoLazardRing) :
    coordinateChangeLift p (C r) = lift p.1 r :=
  RingHom.congr_fun (coordinateChangeLift_comp_C p) r

/-- The homomorphism classifying `(F, φ)` sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
@[simp]
theorem coordinateChangeLift_X
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker)
    (i : ℕ+) :
    coordinateChangeLift p (X i) = PowerSeries.coeff (i + 1) p.2.1.toPowerSeries :=
  (eval₂Hom_X' _ _ _).trans (FormalCoordinate.strictCoeffsEquiv_symm_apply p.2 i)

/-- The homomorphism classifying `(F, φ)` specializes the universal strict coordinate to `φ`. -/
@[simp]
theorem map_coordinateChangeLift_universalStrictCoordinate
    (p : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ×
      (FormalCoordinate.linearCoeff (R := R)).ker) :
    FormalCoordinate.map (coordinateChangeLift p) universalStrictCoordinate = p.2.1 := by
  have h : ⇑(coordinateChangeLift p) ∘ X = FormalCoordinate.strictCoeffsEquiv.symm p.2 :=
    funext fun i ↦ by simp
  rw [universalStrictCoordinate, FormalCoordinate.map_ofStrictCoeffs, h,
    ← FormalCoordinate.coe_strictCoeffsEquiv_apply, Equiv.apply_symm_apply]

/-- The base change of the universal strict coordinate along `f` is the strict coordinate
`X + ∑ f(bᵢ) X^(i + 1)`. -/
theorem map_universalStrictCoordinate (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    FormalCoordinate.map f universalStrictCoordinate = FormalCoordinate.ofStrictCoeffs (f ∘ X) :=
  FormalCoordinate.map_ofStrictCoeffs f X

/-- Base change of the universal strict coordinate is strict. -/
theorem map_universalStrictCoordinate_mem_ker (f : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R) :
    FormalCoordinate.map f universalStrictCoordinate ∈ (FormalCoordinate.linearCoeff (R := R)).ker
    := by
  rw [map_universalStrictCoordinate]
  exact FormalCoordinate.ofStrictCoeffs_mem_ker_linearCoeff _

/-- A ring homomorphism out of `MO[b₁, b₂, …]` is determined by its restriction to `MO` and by its
base change of the universal strict coordinate, that is, by the pair `(F, φ)` it classifies. -/
theorem ringHom_ext_universalStrictCoordinate
    {f g : MvPolynomial ℕ+ ExponentTwoLazardRing →+* R} (hC : f.comp C = g.comp C)
    (hφ : FormalCoordinate.map f universalStrictCoordinate =
      FormalCoordinate.map g universalStrictCoordinate) : f = g :=
  ringHom_ext' hC fun i ↦ by
    simpa using congrArg (fun φ ↦ PowerSeries.coeff (i + 1) φ.toPowerSeries) hφ

/-- The **right unit** `η_R : MO →+* MO[b₁, b₂, …]`: the homomorphism classifying the change of
coordinate of the universal formal group law of exponent two by the universal strict coordinate
`X + ∑ bᵢ X^(i + 1)`. -/
def rightUnit : ExponentTwoLazardRing →+* MvPolynomial ℕ+ ExponentTwoLazardRing :=
  lift ⟨universalStrictCoordinate • formalGroup.map C, inferInstance, by simp⟩

/-- The base change of the universal formal group law of exponent two along `η_R` is the change of
coordinate of its base change along `η_L` by the universal strict coordinate. -/
@[simp]
theorem map_rightUnit :
    formalGroup.map rightUnit = universalStrictCoordinate • formalGroup.map C :=
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
  coordinateChangeLift (⟨formalGroup, inferInstance, nsmulSeries_two_formalGroup⟩, 1)

@[simp]
theorem counit_X (i : ℕ+) : counit (X i) = 0 := by
  simp [counit, PowerSeries.coeff_X]

/-- The counit classifies the identity coordinate. -/
@[simp]
theorem map_counit_universalStrictCoordinate :
    FormalCoordinate.map counit universalStrictCoordinate = 1 :=
  map_coordinateChangeLift_universalStrictCoordinate _

/-- The counit is a retraction of the left unit `η_L = C`. -/
@[simp]
theorem counit_comp_C : counit.comp C = RingHom.id ExponentTwoLazardRing :=
  (coordinateChangeLift_comp_C _).trans <| hom_ext <| by rw [map_lift, FormalGroup.map_id]

/-- The counit is the identity on constants. -/
@[simp]
theorem counit_C (r : ExponentTwoLazardRing) : counit (C r) = r :=
  RingHom.congr_fun counit_comp_C r

/-- The counit is a retraction of the right unit `η_R`: changing the coordinate by the identity
does not change a formal group law. -/
@[simp]
theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id ExponentTwoLazardRing :=
  (coordinateChangeLift_comp_rightUnit _).trans <| hom_ext <| by
    rw [map_lift, FormalGroup.map_id]
    exact one_smul _ _

end ExponentTwoLazardRing

end TauCeti
