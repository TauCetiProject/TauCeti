/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Grading
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Coproduct
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Homogeneous

/-!
# The graded Hopf-algebroid homomorphism `(L, L[b₁, b₂, …]) → (A, A[r, s, t])`

The universal Weierstrass curve over `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and the universal strict
coordinate transition `Strict.formalCoordinate` over `A[r, s, t]` induce a graded morphism of Hopf
algebroids from the Lazard Hopf algebroid `(L, L[b₁, b₂, …])` of commutative formal group laws and
their strict coordinate changes to Bauer's strict Weierstrass Hopf algebroid `(A, A[r, s, t])`.

Concretely:
* `Strict.gradedLazardBaseHom : LazardRing.grading →+*ᵍ Strict.baseGrading` (with underlying ring
  homomorphism `Strict.lazardBaseHom : LazardRing →+* MvPolynomial Coeff ℤ`) classifies the
  universal Weierstrass formal group law `formalGroup Universal.curve`;
* `Strict.gradedLazardArrowHom : LazardRing.coordinateGrading →+*ᵍ Strict.arrowGrading` (with
  underlying ring homomorphism `Strict.lazardArrowHom : MvPolynomial ℕ+ LazardRing →+* ArrowRing`)
  classifies `(formalGroup (WeierstrassCurve.map Universal.curve C), Strict.formalCoordinate)`;
* `Strict.gradedLazardTensorHom : LazardRing.coordinateTensorGrading →+*ᵍ Strict.tensorGrading`
  is the induced graded map on composable pairs;
* `(lazardBaseHom, lazardArrowHom)` intertwines the left units, right units, counits, coproducts
  and conjugations of `(L, L[b₁, b₂, …])` and `(A, A[r, s, t])`;
* on the first three strict coordinate generators `b₁, b₂, b₃`, `lazardArrowHom` sends
  `b₁ ↦ -s`, `b₂ ↦ s² - r` and `b₃ ↦ -t - s³ + 2 r s - a₁ r`, so the base-changed `A`-algebra map
  `Strict.lazardArrowAlgHom : A[b₁, b₂, …] →ₐ[A] A[r, s, t]` admits an explicit `A`-algebra
  section `Strict.lazardArrowAlgSection` and is surjective.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.Strict.gradedLazardBaseHom`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardBaseHom`: the graded classifying map `L → A` of the
  universal Weierstrass formal group law.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.gradedLazardArrowHom`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom`: the graded classifying map
  `L[b₁, b₂, …] → A[r, s, t]` of the universal strict Weierstrass coordinate transition.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.gradedLazardTensorHom`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardTensorHom`: the induced graded map on tensor
  squares `Γ_L ⊗_L Γ_L → Γ_W ⊗_A Γ_W`.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowAlgHom`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowAlgSection`: the `A`-algebra homomorphism
  `A[b₁, b₂, …] →ₐ[A] A[r, s, t]` and its explicit right inverse.

## Main results

* `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom_comp_C`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom_comp_rightUnit`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.counit_comp_lazardArrowHom`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardTensorHom_comp_coproduct`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom_comp_conjugation`: the Hopf-algebroid
  homomorphism identities.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom_X_one`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom_X_two`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowHom_X_three`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.lazardArrowAlgHom_surjective`: explicit values on
  `b₁, b₂, b₃` and surjectivity of `A[b₁, b₂, …] →ₐ[A] A[r, s, t]`.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.map_lazardBaseHom_heightIdeal`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.map_rightUnit_heightIdeal`: base change and
  `Strict.rightUnit`-invariance of the height ideals of the universal Weierstrass formal group.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.1, A2.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section

noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid.Strict

open MvPolynomial _root_.WeierstrassCurve _root_.WeierstrassCurve.VariableChange
open TauCeti.WeierstrassChange.StrictChangeRing

/-! ### Compatibility of `Strict.formalCoordinate` with counit, coproduct and conjugation -/

/-- The counit sends `Strict.formalCoordinate` to the identity formal coordinate. -/
@[simp]
theorem map_counit_formalCoordinate : formalCoordinate.map counit = 1 := by
  rw [formalCoordinate_def, _root_.map_inv, ← map_formalCoordinate, universalChange_map_counit,
    WeierstrassCurve.map_map, counit_comp_C, WeierstrassCurve.map_id, formalCoordinate_one,
    inv_one]

/-- The coproduct sends `Strict.formalCoordinate` to the composite of the universal strict formal
coordinates on the right and left factors of `A[r, s, t] ⊗_A A[r, s, t]`. -/
@[simp]
theorem map_coproduct_formalCoordinate :
    formalCoordinate.map coproduct =
      formalCoordinate.map (MvPolynomial.map rightUnit) * formalCoordinate.map C := by
  have hcop :
      WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C) coproduct =
        WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C)
          (C : ArrowRing →+* WeierstrassChange.StrictChangeRing ArrowRing) := by
    rw [WeierstrassCurve.map_map, coproduct_comp_C, ← WeierstrassCurve.map_map]
  have hW : ((universalChange (MvPolynomial Coeff ℤ)).map
        (C : ArrowRing →+* WeierstrassChange.StrictChangeRing ArrowRing)) •
      WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C) coproduct =
      WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C)
        (MvPolynomial.map rightUnit) := by
    calc
      ((universalChange (MvPolynomial Coeff ℤ)).map
            (C : ArrowRing →+* WeierstrassChange.StrictChangeRing ArrowRing)) •
          WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C) coproduct =
          WeierstrassCurve.map (WeierstrassCurve.map Universal.curve rightUnit) C := by
        rw [hcop, map_variableChange, ← map_rightUnit]
      _ = WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C)
            (MvPolynomial.map rightUnit) := by
        rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
        congr 1
        exact RingHom.ext fun a ↦ (MvPolynomial.map_C rightUnit a).symm
  simp only [formalCoordinate_def, _root_.map_inv, ← map_formalCoordinate]
  rw [universalChange_map_coproduct, formalCoordinate_mul, mul_inv_rev, hW, hcop,
    universalChange_map_map]

/-- The conjugation sends `Strict.formalCoordinate` to its inverse in `FormalCoordinate ArrowRing`.
-/
@[simp]
theorem map_conjugation_formalCoordinate :
    formalCoordinate.map conjugation = formalCoordinate⁻¹ := by
  nth_rw 1 [formalCoordinate_def]
  rw [_root_.map_inv, ← map_formalCoordinate, universalChange_map_conjugation,
    WeierstrassCurve.map_map, conjugation_comp_C, ← formalCoordinate_eq_inv_formalCoordinate]

/-! ### The graded base homomorphism `L → A` -/

/-- The graded ring homomorphism `L →+*ᵍ A` classifying the universal Weierstrass formal group law,
preserving homological degrees (`|xₙ| = 2n`, `|aᵢ| = 2i`). -/
def gradedLazardBaseHom : LazardRing.grading →+*ᵍ baseGrading :=
  LazardRing.gradedLift
    ⟨formalGroup Universal.curve, inferInstance, Universal.coeff_formalGroup_mem_baseGrading⟩

/-- The ring homomorphism `L →+* ℤ[a₁, a₂, a₃, a₄, a₆]` classifying `formalGroup Universal.curve`.
-/
def lazardBaseHom : LazardRing →+* MvPolynomial Coeff ℤ :=
  gradedLazardBaseHom.toRingHom

@[simp]
theorem toRingHom_gradedLazardBaseHom : gradedLazardBaseHom.toRingHom = lazardBaseHom :=
  (rfl)

@[simp]
theorem coe_gradedLazardBaseHom : ⇑gradedLazardBaseHom = lazardBaseHom :=
  (rfl)

/-- `lazardBaseHom` preserves the even homological grading. -/
theorem lazardBaseHom_mem_baseGrading {n : ℕ} {x : LazardRing} (hx : x ∈ LazardRing.grading n) :
    lazardBaseHom x ∈ baseGrading n :=
  gradedLazardBaseHom.map_mem hx

/-- An element of `L_{2k}` maps under `lazardBaseHom` to a weighted homogeneous polynomial of
modular weight `k` in `a₁, a₂, a₃, a₄, a₆`. -/
theorem isWeightedHomogeneous_lazardBaseHom {k : ℕ} {x : LazardRing}
    (hx : x ∈ LazardRing.grading (2 * k)) :
    (lazardBaseHom x).IsWeightedHomogeneous coefficientWeight k :=
  mem_baseGrading_two_mul_iff.mp (lazardBaseHom_mem_baseGrading hx)

/-- Base change of the universal formal group law along `lazardBaseHom` recovers the universal
Weierstrass formal group law. -/
@[simp]
theorem map_lazardBaseHom_formalGroup :
    LazardRing.formalGroup.map lazardBaseHom = formalGroup Universal.curve := by
  rw [lazardBaseHom, gradedLazardBaseHom, LazardRing.toRingHom_gradedLift, LazardRing.map_lift]

/-- Composing `lazardBaseHom` with `W.specialize` gives the Lazard classifying map of
`formalGroup W`. -/
@[simp]
theorem specialize_comp_lazardBaseHom {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.specialize.comp lazardBaseHom = LazardRing.lift ⟨formalGroup W, inferInstance⟩ := by
  apply LazardRing.hom_ext
  rw [← FormalGroup.map_comp, map_lazardBaseHom_formalGroup, ← map_formalGroup, LazardRing.map_lift]
  congr 1
  exact WeierstrassCurve.map_specialize W

/-- `lazardBaseHom` pushes the `n`-th height ideal of the universal formal group law at `p` forward
to the `n`-th height ideal of `formalGroup Universal.curve`. -/
theorem map_lazardBaseHom_heightIdeal (p n : ℕ) :
    (LazardRing.formalGroup.heightIdeal p n).map lazardBaseHom =
      (formalGroup Universal.curve).heightIdeal p n := by
  rw [FormalGroup.map_heightIdeal, map_lazardBaseHom_formalGroup]

/-! ### The graded arrow homomorphism `L[b₁, b₂, …] → A[r, s, t]` -/

private theorem coeff_map_C_formalGroup_mem_arrowGrading (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup (WeierstrassCurve.map Universal.curve C)).toPowerSeries ∈
      arrowGrading (2 * (d.degree - 1)) := by
  rw [map_formalGroup, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
  exact C_mem_arrowGrading (Universal.coeff_formalGroup_mem_baseGrading d)

/-- The graded ring homomorphism `L[b₁, b₂, …] →+*ᵍ A[r, s, t]` classifying the source formal group
law `formalGroup (WeierstrassCurve.map Universal.curve C)` together with `Strict.formalCoordinate`.
-/
def gradedLazardArrowHom : LazardRing.coordinateGrading →+*ᵍ arrowGrading :=
  LazardRing.gradedCoordinateChangeLift
    ⟨(⟨formalGroup (WeierstrassCurve.map Universal.curve C), inferInstance⟩,
        ⟨formalCoordinate, formalCoordinate_mem_ker_linearCoeff⟩),
      coeff_map_C_formalGroup_mem_arrowGrading, coeff_succ_formalCoordinate_mem_arrowGrading⟩

/-- The ring homomorphism `L[b₁, b₂, …] →+* A[r, s, t]` classifying the universal strict
Weierstrass formal coordinate transition. -/
def lazardArrowHom : MvPolynomial ℕ+ LazardRing →+* ArrowRing :=
  gradedLazardArrowHom.toRingHom

@[simp]
theorem toRingHom_gradedLazardArrowHom : gradedLazardArrowHom.toRingHom = lazardArrowHom :=
  (rfl)

@[simp]
theorem coe_gradedLazardArrowHom : ⇑gradedLazardArrowHom = lazardArrowHom :=
  (rfl)

/-- `lazardArrowHom` preserves homological degrees (`|bᵢ| = 2i`, `|r| = 4`, `|s| = 2`, `|t| = 6`).
-/
theorem lazardArrowHom_mem_arrowGrading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ LazardRing.coordinateGrading n) : lazardArrowHom x ∈ arrowGrading n :=
  gradedLazardArrowHom.map_mem hx

/-- `lazardArrowHom` sends the strict coordinate generator `bᵢ = X i` to the coefficient of
`z^(i + 1)` in `Strict.formalCoordinate`. -/
@[simp]
theorem lazardArrowHom_X (i : ℕ+) :
    lazardArrowHom (X i) = PowerSeries.coeff (i + 1) formalCoordinate.toPowerSeries := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_X]

/-- `lazardArrowHom` specializes the universal strict coordinate to `Strict.formalCoordinate`. -/
@[simp]
theorem map_lazardArrowHom_universalStrictCoordinate :
    FormalCoordinate.map lazardArrowHom FormalCoordinate.universalStrictCoordinate =
      formalCoordinate := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.map_coordinateChangeLift_universalStrictCoordinate]

/-- Composing `lazardArrowHom` with the homomorphism classifying `(W, a)` over `R` gives the Lazard
coordinate-change homomorphism of `(formalGroup W, ((heisenbergHom R a).formalCoordinate W)⁻¹)`. -/
@[simp]
theorem lift_comp_lazardArrowHom {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (a : HeisenbergGroup R) :
    (lift (W.specialize, a)).comp lazardArrowHom =
      LazardRing.coordinateChangeLift (⟨formalGroup W, inferInstance⟩,
        ⟨((heisenbergHom R a).formalCoordinate W)⁻¹, MonoidHom.mem_ker.mpr (by simp)⟩) := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, lazardArrowHom, gradedLazardArrowHom,
      LazardRing.toRingHom_gradedCoordinateChangeLift, LazardRing.coordinateChangeLift_comp_C,
      LazardRing.coordinateChangeLift_comp_C]
    apply LazardRing.hom_ext
    rw [← FormalGroup.map_comp, LazardRing.map_lift, LazardRing.map_lift, ← map_formalGroup,
      WeierstrassCurve.map_map, lift_comp_C]
    congr 1
    exact WeierstrassCurve.map_specialize W
  · rw [FormalCoordinate.map_comp, map_lazardArrowHom_universalStrictCoordinate,
      map_lift_formalCoordinate, LazardRing.map_coordinateChangeLift_universalStrictCoordinate]

/-! ### Explicit values on `b₁, b₂, b₃` and surjectivity onto `A[r, s, t]` -/

/-- `lazardArrowHom` sends `b₁` to `-s`. -/
theorem lazardArrowHom_X_one : lazardArrowHom (X 1) = -(X 1 : ArrowRing) := by
  simp [lazardArrowHom_X]

/-- `lazardArrowHom` sends `b₂` to `s² - r`. -/
theorem lazardArrowHom_X_two : lazardArrowHom (X 2) = X 1 ^ 2 - (X 0 : ArrowRing) := by
  simp [lazardArrowHom_X]

/-- `lazardArrowHom` sends `b₃` to `-t - s³ + 2 r s - a₁ r`. -/
theorem lazardArrowHom_X_three :
    lazardArrowHom (X 3) =
      -X 2 - X 1 ^ 3 + 2 * X 0 * X 1 - C (X .A₁) * (X 0 : ArrowRing) := by
  simp [lazardArrowHom_X]

/-- **Left-unit compatibility**: `lazardArrowHom` intertwines the left units `η_L = C` of
`(L, L[b₁, b₂, …])` and `(A, A[r, s, t])`. -/
@[simp]
theorem lazardArrowHom_comp_C : lazardArrowHom.comp C = C.comp lazardBaseHom := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_comp_C]
  apply LazardRing.hom_ext
  rw [LazardRing.map_lift, ← FormalGroup.map_comp, map_lazardBaseHom_formalGroup]
  dsimp only
  rw [map_formalGroup]

@[simp]
theorem lazardArrowHom_C (x : LazardRing) : lazardArrowHom (C x) = C (lazardBaseHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_C x

/-- The base-changed `A`-algebra homomorphism `A[b₁, b₂, …] →ₐ[A] A[r, s, t]` sending `bᵢ` to the
coefficient of `z^(i + 1)` in `Strict.formalCoordinate`. -/
def lazardArrowAlgHom :
    MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) →ₐ[MvPolynomial Coeff ℤ] ArrowRing :=
  MvPolynomial.aeval fun i : ℕ+ ↦ lazardArrowHom (X i)

@[simp]
theorem lazardArrowAlgHom_X (i : ℕ+) : lazardArrowAlgHom (X i) = lazardArrowHom (X i) :=
  MvPolynomial.aeval_X _ i

theorem lazardArrowAlgHom_C (f : MvPolynomial Coeff ℤ) : lazardArrowAlgHom (C f) = C f :=
  MvPolynomial.aeval_C _ f

/-- `lazardArrowHom` factors through `MvPolynomial.map lazardBaseHom` and `lazardArrowAlgHom`. -/
@[simp]
theorem lazardArrowAlgHom_map_lazardBaseHom (x : MvPolynomial ℕ+ LazardRing) :
    lazardArrowAlgHom (MvPolynomial.map lazardBaseHom x) = lazardArrowHom x := by
  have h : lazardArrowAlgHom.toRingHom.comp (MvPolynomial.map lazardBaseHom) = lazardArrowHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext fun r ↦ by simp) (fun i ↦ by simp)
  exact RingHom.congr_fun h x

/-- An explicit `A`-algebra section `A[r, s, t] →ₐ[A] A[b₁, b₂, …]` of `lazardArrowAlgHom`,
expressing `r = b₁² - b₂`, `s = -b₁` and `t = -b₃ + b₁³ - 2(b₁² - b₂)b₁ - a₁(b₁² - b₂)`. -/
def lazardArrowAlgSection :
    ArrowRing →ₐ[MvPolynomial Coeff ℤ] MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) :=
  let r₀ : MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) := X 1 ^ 2 - X 2
  MvPolynomial.aeval ![r₀, -X 1, -X 3 + X 1 ^ 3 - 2 * r₀ * X 1 - C (X .A₁) * r₀]

/-- `lazardArrowAlgSection` is a right inverse to `lazardArrowAlgHom`. -/
@[simp]
theorem lazardArrowAlgHom_comp_lazardArrowAlgSection :
    lazardArrowAlgHom.comp lazardArrowAlgSection = AlgHom.id (MvPolynomial Coeff ℤ) ArrowRing := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [lazardArrowAlgSection]
  · simp [lazardArrowAlgSection]
  · simp [lazardArrowAlgSection, map_ofNat]
    ring

@[simp]
theorem lazardArrowAlgHom_lazardArrowAlgSection (p : ArrowRing) :
    lazardArrowAlgHom (lazardArrowAlgSection p) = p :=
  AlgHom.congr_fun lazardArrowAlgHom_comp_lazardArrowAlgSection p

/-- The `A`-algebra homomorphism `A[b₁, b₂, …] →ₐ[A] A[r, s, t]` induced by the universal strict
Weierstrass coordinate transition is surjective. -/
theorem lazardArrowAlgHom_surjective : Function.Surjective lazardArrowAlgHom :=
  Function.RightInverse.surjective lazardArrowAlgHom_lazardArrowAlgSection

/-! ### Remaining Hopf-algebroid homomorphism identities and height ideals -/

/-- **Right-unit compatibility**: `lazardArrowHom` intertwines the right units `η_R` of
`(L, L[b₁, b₂, …])` and `(A, A[r, s, t])`. -/
@[simp]
theorem lazardArrowHom_comp_rightUnit :
    lazardArrowHom.comp LazardRing.rightUnit = rightUnit.comp lazardBaseHom := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_comp_rightUnit]
  apply LazardRing.hom_ext
  rw [LazardRing.map_lift, ← FormalGroup.map_comp, map_lazardBaseHom_formalGroup]
  dsimp only
  rw [formalCoordinate_smul_formalGroup, map_formalGroup]

@[simp]
theorem lazardArrowHom_rightUnit (x : LazardRing) :
    lazardArrowHom (LazardRing.rightUnit x) = rightUnit (lazardBaseHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_rightUnit x

/-- **Counit compatibility**: `(lazardBaseHom, lazardArrowHom)` intertwines the counits of
`(L, L[b₁, b₂, …])` and `(A, A[r, s, t])`. -/
@[simp]
theorem counit_comp_lazardArrowHom :
    counit.comp lazardArrowHom = lazardBaseHom.comp LazardRing.counit := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, lazardArrowHom_comp_C, ← RingHom.comp_assoc, counit_comp_C,
      RingHom.id_comp, RingHom.comp_assoc, LazardRing.counit_comp_C, RingHom.comp_id]
  · rw [FormalCoordinate.map_comp, map_lazardArrowHom_universalStrictCoordinate,
      map_counit_formalCoordinate, FormalCoordinate.map_comp,
      LazardRing.map_counit_universalStrictCoordinate, _root_.map_one]

@[simp]
theorem counit_lazardArrowHom (x : MvPolynomial ℕ+ LazardRing) :
    counit (lazardArrowHom x) = lazardBaseHom (LazardRing.counit x) :=
  RingHom.congr_fun counit_comp_lazardArrowHom x

/-- **Conjugation compatibility**: `lazardArrowHom` intertwines the conjugations of
`(L, L[b₁, b₂, …])` and `(A, A[r, s, t])`. -/
@[simp]
theorem lazardArrowHom_comp_conjugation :
    lazardArrowHom.comp LazardRing.conjugation = conjugation.comp lazardArrowHom := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, LazardRing.conjugation_comp_C, lazardArrowHom_comp_rightUnit,
      RingHom.comp_assoc, lazardArrowHom_comp_C, ← RingHom.comp_assoc, conjugation_comp_C]
  · rw [FormalCoordinate.map_comp, LazardRing.map_conjugation_universalStrictCoordinate,
      _root_.map_inv, map_lazardArrowHom_universalStrictCoordinate, FormalCoordinate.map_comp,
      map_lazardArrowHom_universalStrictCoordinate, map_conjugation_formalCoordinate]

@[simp]
theorem lazardArrowHom_conjugation (x : MvPolynomial ℕ+ LazardRing) :
    lazardArrowHom (LazardRing.conjugation x) = conjugation (lazardArrowHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_conjugation x

/-- The ring homomorphism `Γ_L ⊗_L Γ_L →+* Γ_W ⊗_A Γ_W` induced on composable pairs by
`(lazardBaseHom, lazardArrowHom)`. -/
def lazardTensorHom :
    MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+*
      WeierstrassChange.StrictChangeRing ArrowRing :=
  LazardRing.tensorLift
    ⟨(C.comp lazardArrowHom, (MvPolynomial.map rightUnit).comp lazardArrowHom),
      RingHom.ext fun r ↦ by simp⟩

@[simp]
theorem lazardTensorHom_comp_C : lazardTensorHom.comp C = C.comp lazardArrowHom :=
  LazardRing.tensorLift_comp_C _

@[simp]
theorem lazardTensorHom_comp_map_rightUnit :
    lazardTensorHom.comp (MvPolynomial.map LazardRing.rightUnit) =
      (MvPolynomial.map rightUnit).comp lazardArrowHom :=
  LazardRing.tensorLift_comp_map_rightUnit _

/-- `lazardTensorHom` preserves the combined homological grading on tensor squares. -/
theorem lazardTensorHom_mem_tensorGrading {n : ℕ}
    {x : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)}
    (hx : x ∈ LazardRing.coordinateTensorGrading n) :
    lazardTensorHom x ∈ tensorGrading n := by
  have hright : ∀ ⦃m⦄ ⦃y : ArrowRing⦄, y ∈ arrowGrading m →
      MvPolynomial.map rightUnit y ∈ tensorGrading m :=
    fun _ _ hy ↦ (arrowGrading_map_mem_iff tensorGrading (.id ℕ) (MvPolynomial.map rightUnit)).mpr
      ⟨fun _ _ hp ↦ by simpa using C_mem_tensorGrading (rightUnit_mem_arrowGrading hp),
        fun i ↦ by simp⟩ hy
  exact LazardRing.tensorLift_mem tensorGrading (.id ℕ) _
    (fun _ _ hy ↦ C_mem_tensorGrading (lazardArrowHom_mem_arrowGrading hy))
    (fun _ _ hy ↦ hright (lazardArrowHom_mem_arrowGrading hy)) hx

/-- The graded ring homomorphism on tensor squares `Γ_L ⊗_L Γ_L →+*ᵍ Γ_W ⊗_A Γ_W`. -/
def gradedLazardTensorHom : LazardRing.coordinateTensorGrading →+*ᵍ tensorGrading where
  toRingHom := lazardTensorHom
  map_mem hx := lazardTensorHom_mem_tensorGrading hx

@[simp]
theorem toRingHom_gradedLazardTensorHom : gradedLazardTensorHom.toRingHom = lazardTensorHom :=
  (rfl)

/-- **Coproduct compatibility**: `(lazardBaseHom, lazardArrowHom)` intertwines the coproducts of
`(L, L[b₁, b₂, …])` and `(A, A[r, s, t])`. -/
@[simp]
theorem lazardTensorHom_comp_coproduct :
    lazardTensorHom.comp LazardRing.coproduct = coproduct.comp lazardArrowHom := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate ?_ ?_
  · exact RingHom.ext fun r ↦ by simp [lazardTensorHom]
  · rw [LazardRing.map_comp_coproduct_universalStrictCoordinate,
      lazardTensorHom_comp_map_rightUnit, lazardTensorHom_comp_C, FormalCoordinate.map_comp,
      FormalCoordinate.map_comp, map_lazardArrowHom_universalStrictCoordinate,
      FormalCoordinate.map_comp, map_lazardArrowHom_universalStrictCoordinate,
      map_coproduct_formalCoordinate]

@[simp]
theorem lazardTensorHom_coproduct (x : MvPolynomial ℕ+ LazardRing) :
    lazardTensorHom (LazardRing.coproduct x) = coproduct (lazardArrowHom x) :=
  RingHom.congr_fun lazardTensorHom_comp_coproduct x

/-- **The height ideals of `formalGroup Universal.curve` are invariant ideals of
`(A, A[r, s, t])`**: their extensions along `Strict.rightUnit` and `C` agree. -/
theorem map_rightUnit_heightIdeal (p n : ℕ) :
    ((formalGroup Universal.curve).heightIdeal p n).map rightUnit =
      ((formalGroup Universal.curve).heightIdeal p n).map C := by
  rw [FormalGroup.map_heightIdeal, FormalGroup.map_heightIdeal, ← map_formalGroup,
    ← map_formalGroup, ← formalCoordinate_smul_formalGroup, FormalGroup.heightIdeal_smul]

/-- For every `p` and `n`, the coefficient of `z^(p^n)` in `[p]` on `formalGroup Universal.curve`
is invariant modulo the `n`-th height ideal in `A[r, s, t]`. -/
theorem rightUnit_coeff_nsmulSeries_sub_C_mem_map_heightIdeal (p n : ℕ) :
    rightUnit (PowerSeries.coeff (p ^ n) ((formalGroup Universal.curve).nsmulSeries p)) -
        C (PowerSeries.coeff (p ^ n) ((formalGroup Universal.curve).nsmulSeries p)) ∈
      ((formalGroup Universal.curve).heightIdeal p n).map C := by
  have h := Ideal.mem_map_of_mem lazardArrowHom
    (LazardRing.rightUnit_sub_C_mem_map_heightIdeal p n)
  rw [Ideal.map_map, lazardArrowHom_comp_C, ← Ideal.map_map, map_lazardBaseHom_heightIdeal,
    map_sub, lazardArrowHom_rightUnit, lazardArrowHom_C] at h
  have hc : lazardBaseHom (PowerSeries.coeff (p ^ n) (LazardRing.formalGroup.nsmulSeries p)) =
      PowerSeries.coeff (p ^ n) ((formalGroup Universal.curve).nsmulSeries p) := by
    rw [← FormalGroup.coeff_nsmulSeries_map, map_lazardBaseHom_formalGroup]
  rwa [hc] at h

end TauCeti.WeierstrassHopfAlgebroid.Strict
