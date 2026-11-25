/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Grading
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Coproduct

/-!
# The graded Hopf-algebroid homomorphism `(L, L[b₁, b₂, …]) → (A, A[r, s, t])`

`Universal.curve` over `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `Strict.formalCoordinate` over `A[r, s, t]`
induce a graded Hopf-algebroid morphism `(L, L[b₁, b₂, …]) → (A, A[r, s, t])`. Since
`lazardArrowHom` sends `(b₁, b₂, b₃) ↦ (-s, s² - r, -t - s³ + 2 r s - a₁ r)`, the induced
`A`-algebra map `A[b₁, b₂, …] →ₐ[A] A[r, s, t]` admits an explicit section and is surjective.

## Main definitions and results

* `Strict.gradedLazardBaseHom`, `lazardBaseHom`, `gradedLazardArrowHom`, `lazardArrowHom`,
  `gradedLazardTensorHom`, `lazardTensorHom` and their Hopf-algebroid compatibility identities.
* `Strict.lazardArrowAlgHom`, `lazardArrowAlgSection`, `lazardArrowAlgHom_surjective`.
* `Strict.map_lazardBaseHom_heightIdeal`, `map_rightUnit_heightIdeal`.

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

/-! ### The graded base homomorphism `L → A` -/

/-- The graded ring homomorphism `L →+*ᵍ A` classifying `formalGroup Universal.curve`. -/
def gradedLazardBaseHom : LazardRing.grading →+*ᵍ baseGrading :=
  LazardRing.gradedLift
    ⟨formalGroup Universal.curve, inferInstance, Universal.coeff_formalGroup_mem_baseGrading⟩
/-- The ring homomorphism `L →+* A` classifying `formalGroup Universal.curve`. -/
def lazardBaseHom : LazardRing →+* MvPolynomial Coeff ℤ := gradedLazardBaseHom.toRingHom
@[simp] theorem toRingHom_gradedLazardBaseHom : gradedLazardBaseHom.toRingHom = lazardBaseHom :=
  (rfl)
@[simp] theorem coe_gradedLazardBaseHom : ⇑gradedLazardBaseHom = lazardBaseHom := (rfl)

theorem lazardBaseHom_mem_baseGrading {n : ℕ} {x : LazardRing} (hx : x ∈ LazardRing.grading n) :
    lazardBaseHom x ∈ baseGrading n := gradedLazardBaseHom.map_mem hx
theorem isWeightedHomogeneous_lazardBaseHom {k : ℕ} {x : LazardRing}
    (hx : x ∈ LazardRing.grading (2 * k)) :
    (lazardBaseHom x).IsWeightedHomogeneous coefficientWeight k :=
  mem_baseGrading_two_mul_iff.mp (lazardBaseHom_mem_baseGrading hx)
@[simp] theorem map_lazardBaseHom_formalGroup :
    LazardRing.formalGroup.map lazardBaseHom = formalGroup Universal.curve := by
  rw [lazardBaseHom, gradedLazardBaseHom, LazardRing.toRingHom_gradedLift, LazardRing.map_lift]

/-- Specializing `lazardBaseHom` along `W.specialize` recovers `LazardRing.lift` for `W`. -/
@[simp] theorem specialize_comp_lazardBaseHom {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.specialize.comp lazardBaseHom = LazardRing.lift ⟨formalGroup W, inferInstance⟩ := by
  apply LazardRing.hom_ext
  rw [← FormalGroup.map_comp, map_lazardBaseHom_formalGroup, map_specialize_formalGroup,
    LazardRing.map_lift]

/-- `lazardBaseHom` extends `I_n` to `(formalGroup Universal.curve).heightIdeal p n`. -/
theorem map_lazardBaseHom_heightIdeal (p n : ℕ) :
    (LazardRing.formalGroup.heightIdeal p n).map lazardBaseHom =
      (formalGroup Universal.curve).heightIdeal p n := by
  rw [FormalGroup.map_heightIdeal, map_lazardBaseHom_formalGroup]

/-! ### The graded arrow homomorphism `L[b₁, b₂, …] → A[r, s, t]` -/

/-- The graded ring homomorphism `L[b₁, b₂, …] →+*ᵍ A[r, s, t]` classifying
`(formalGroup (WeierstrassCurve.map Universal.curve C), Strict.formalCoordinate)`. -/
def gradedLazardArrowHom : LazardRing.coordinateGrading →+*ᵍ arrowGrading :=
  LazardRing.gradedCoordinateChangeLift
    ⟨(⟨formalGroup (WeierstrassCurve.map Universal.curve C), inferInstance⟩,
        ⟨formalCoordinate, formalCoordinate_mem_ker_linearCoeff⟩),
      fun d ↦ by
        dsimp only
        rw [map_formalGroup, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
        exact C_mem_arrowGrading (Universal.coeff_formalGroup_mem_baseGrading d),
      coeff_succ_formalCoordinate_mem_arrowGrading⟩
/-- The ring homomorphism `L[b₁, b₂, …] →+* A[r, s, t]` classifying `Strict.formalCoordinate`. -/
def lazardArrowHom : MvPolynomial ℕ+ LazardRing →+* ArrowRing := gradedLazardArrowHom.toRingHom
@[simp] theorem toRingHom_gradedLazardArrowHom : gradedLazardArrowHom.toRingHom = lazardArrowHom :=
  (rfl)
@[simp] theorem coe_gradedLazardArrowHom : ⇑gradedLazardArrowHom = lazardArrowHom := (rfl)
theorem lazardArrowHom_mem_arrowGrading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ LazardRing.coordinateGrading n) : lazardArrowHom x ∈ arrowGrading n :=
  gradedLazardArrowHom.map_mem hx
@[simp] theorem lazardArrowHom_X (i : ℕ+) :
    lazardArrowHom (X i) = PowerSeries.coeff (i + 1) formalCoordinate.toPowerSeries := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_X]
@[simp] theorem map_lazardArrowHom_universalStrictCoordinate :
    FormalCoordinate.map lazardArrowHom FormalCoordinate.universalStrictCoordinate =
      formalCoordinate := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.map_coordinateChangeLift_universalStrictCoordinate]

/-- **Left-unit compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem lazardArrowHom_comp_C : lazardArrowHom.comp C = C.comp lazardBaseHom := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_comp_C]
  apply LazardRing.hom_ext
  rw [LazardRing.map_lift, ← FormalGroup.map_comp, map_lazardBaseHom_formalGroup]
  dsimp only; rw [map_formalGroup]
@[simp] theorem lazardArrowHom_C (x : LazardRing) : lazardArrowHom (C x) = C (lazardBaseHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_C x

/-- Specializing `lazardArrowHom` along `(W, a)` recovers `LazardRing.coordinateChangeLift` for
`formalGroup W` and `((heisenbergHom R a).formalCoordinate W)⁻¹`. -/
@[simp] theorem lift_comp_lazardArrowHom {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (a : HeisenbergGroup R) :
    (lift (W.specialize, a)).comp lazardArrowHom =
      LazardRing.coordinateChangeLift (⟨formalGroup W, inferInstance⟩,
        ⟨((heisenbergHom R a).formalCoordinate W)⁻¹, MonoidHom.mem_ker.mpr (by simp)⟩) :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (by rw [RingHom.comp_assoc, lazardArrowHom_comp_C, ← RingHom.comp_assoc]; simp)
    (by simp [FormalCoordinate.map_comp])

/-! ### Explicit values on `b₁, b₂, b₃` and surjectivity onto `A[r, s, t]` -/

/-- `lazardArrowHom` sends `b₁ = X 1` to `-s` (`-X 1`). -/
theorem lazardArrowHom_X_one : lazardArrowHom (X 1) = -(X 1 : ArrowRing) := by simp
/-- `lazardArrowHom` sends `b₂ = X 2` to `s² - r` (`X 1 ^ 2 - X 0`). -/
theorem lazardArrowHom_X_two : lazardArrowHom (X 2) = X 1 ^ 2 - (X 0 : ArrowRing) := by simp
/-- `lazardArrowHom` sends `b₃ = X 3` to `-t - s³ + 2 r s - a₁ r`. -/
theorem lazardArrowHom_X_three :
    lazardArrowHom (X 3) = -X 2 - X 1 ^ 3 + 2 * X 0 * X 1 - C (X .A₁) * (X 0 : ArrowRing) := by simp

/-- The base-changed `A`-algebra homomorphism `A[b₁, b₂, …] →ₐ[A] A[r, s, t]`. -/
def lazardArrowAlgHom : MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) →ₐ[MvPolynomial Coeff ℤ] ArrowRing :=
  MvPolynomial.aeval fun i : ℕ+ ↦ lazardArrowHom (X i)
@[simp] theorem lazardArrowAlgHom_X (i : ℕ+) : lazardArrowAlgHom (X i) = lazardArrowHom (X i) :=
  MvPolynomial.aeval_X _ i
theorem lazardArrowAlgHom_C (f : MvPolynomial Coeff ℤ) : lazardArrowAlgHom (C f) = C f :=
  MvPolynomial.aeval_C _ f
@[simp] theorem lazardArrowAlgHom_map_lazardBaseHom (x : MvPolynomial ℕ+ LazardRing) :
    lazardArrowAlgHom (MvPolynomial.map lazardBaseHom x) = lazardArrowHom x := by
  have h : lazardArrowAlgHom.toRingHom.comp (MvPolynomial.map lazardBaseHom) = lazardArrowHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun _ ↦ by simp
  exact RingHom.congr_fun h x

/-- An explicit `A`-algebra section `A[r, s, t] →ₐ[A] A[b₁, b₂, …]` of `lazardArrowAlgHom`. -/
def lazardArrowAlgSection :
    ArrowRing →ₐ[MvPolynomial Coeff ℤ] MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) :=
  let r₀ : MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) := X 1 ^ 2 - X 2
  MvPolynomial.aeval ![r₀, -X 1, -X 3 + X 1 ^ 3 - 2 * r₀ * X 1 - C (X .A₁) * r₀]
theorem lazardArrowAlgSection_C (f : MvPolynomial Coeff ℤ) : lazardArrowAlgSection (C f) = C f :=
  algHom_C _ f
@[simp] theorem lazardArrowAlgSection_X_zero : lazardArrowAlgSection (X 0) = X 1 ^ 2 - X 2 := by
  simp [lazardArrowAlgSection]
@[simp] theorem lazardArrowAlgSection_X_one : lazardArrowAlgSection (X 1) = -X 1 := by
  simp [lazardArrowAlgSection]
@[simp] theorem lazardArrowAlgSection_X_two :
    lazardArrowAlgSection (X 2) =
      -X 3 + X 1 ^ 3 - 2 * (X 1 ^ 2 - X 2) * X 1 - C (X .A₁) * (X 1 ^ 2 - X 2) := by
  simp [lazardArrowAlgSection]
@[simp] theorem lazardArrowAlgHom_comp_lazardArrowAlgSection :
    lazardArrowAlgHom.comp lazardArrowAlgSection = AlgHom.id (MvPolynomial Coeff ℤ) ArrowRing :=
  MvPolynomial.algHom_ext fun i ↦ by
    fin_cases i
    · simp
    · simp
    · simp [map_ofNat]; ring
@[simp] theorem lazardArrowAlgHom_lazardArrowAlgSection (p : ArrowRing) :
    lazardArrowAlgHom (lazardArrowAlgSection p) = p :=
  AlgHom.congr_fun lazardArrowAlgHom_comp_lazardArrowAlgSection p

/-- The `A`-algebra homomorphism `A[b₁, b₂, …] →ₐ[A] A[r, s, t]` is surjective. -/
theorem lazardArrowAlgHom_surjective : Function.Surjective lazardArrowAlgHom :=
  Function.RightInverse.surjective lazardArrowAlgHom_lazardArrowAlgSection

/-! ### Remaining Hopf-algebroid homomorphism identities and height ideals -/

/-- **Right-unit compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem lazardArrowHom_comp_rightUnit :
    lazardArrowHom.comp LazardRing.rightUnit = rightUnit.comp lazardBaseHom := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_comp_rightUnit]
  apply LazardRing.hom_ext
  rw [LazardRing.map_lift, ← FormalGroup.map_comp, map_lazardBaseHom_formalGroup]
  dsimp only; rw [formalCoordinate_smul_formalGroup, map_formalGroup]
@[simp] theorem lazardArrowHom_rightUnit (x : LazardRing) :
    lazardArrowHom (LazardRing.rightUnit x) = rightUnit (lazardBaseHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_rightUnit x

/-- **Counit compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem counit_comp_lazardArrowHom :
    counit.comp lazardArrowHom = lazardBaseHom.comp LazardRing.counit :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate (RingHom.ext fun _ ↦ by simp)
    (by simp [FormalCoordinate.map_comp])
@[simp] theorem counit_lazardArrowHom (x : MvPolynomial ℕ+ LazardRing) :
    counit (lazardArrowHom x) = lazardBaseHom (LazardRing.counit x) :=
  RingHom.congr_fun counit_comp_lazardArrowHom x

/-- **Conjugation compatibility** of `lazardArrowHom`. -/
@[simp] theorem lazardArrowHom_comp_conjugation :
    lazardArrowHom.comp LazardRing.conjugation = conjugation.comp lazardArrowHom :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate (RingHom.ext fun _ ↦ by simp)
    (by simp [FormalCoordinate.map_comp])
@[simp] theorem lazardArrowHom_conjugation (x : MvPolynomial ℕ+ LazardRing) :
    lazardArrowHom (LazardRing.conjugation x) = conjugation (lazardArrowHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_conjugation x

/-- The ring homomorphism `Γ_L ⊗_L Γ_L →+* Γ_W ⊗_A Γ_W` induced on composable pairs. -/
def lazardTensorHom :
    MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* WeierstrassChange.StrictChangeRing ArrowRing :=
  pushoutLift LazardRing.rightUnit
    ⟨(C.comp lazardArrowHom, (MvPolynomial.map rightUnit).comp lazardArrowHom),
      RingHom.ext fun _ ↦ by simp⟩

@[simp] theorem lazardTensorHom_comp_C : lazardTensorHom.comp C = C.comp lazardArrowHom :=
  pushoutLift_comp_C _ _
@[simp] theorem lazardTensorHom_comp_map_rightUnit :
    lazardTensorHom.comp (MvPolynomial.map LazardRing.rightUnit) =
      (MvPolynomial.map rightUnit).comp lazardArrowHom := pushoutLift_comp_map _ _
@[simp] theorem lazardTensorHom_C (x : MvPolynomial ℕ+ LazardRing) :
    lazardTensorHom (C x) = C (lazardArrowHom x) := pushoutLift_C _ _ x
@[simp] theorem lazardTensorHom_map_rightUnit (x : MvPolynomial ℕ+ LazardRing) :
    lazardTensorHom (MvPolynomial.map LazardRing.rightUnit x) =
      MvPolynomial.map rightUnit (lazardArrowHom x) := pushoutLift_map _ _ x
@[simp] theorem lazardTensorHom_X (i : ℕ+) :
    lazardTensorHom (X i) = MvPolynomial.map rightUnit (lazardArrowHom (X i)) := by
  simp [lazardTensorHom]

theorem lazardTensorHom_mem_tensorGrading {n : ℕ}
    {x : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)}
    (hx : x ∈ LazardRing.coordinateTensorGrading n) : lazardTensorHom x ∈ tensorGrading n :=
  (LazardRing.coordinateTensorGrading_map_mem_iff tensorGrading (.id ℕ) lazardTensorHom).mpr
    ⟨fun _ _ hy ↦ by simpa using C_mem_tensorGrading (lazardArrowHom_mem_arrowGrading hy),
      fun i ↦ by simpa using coeff_succ_formalCoordinate_mem_arrowGrading i⟩ hx

/-- The graded ring homomorphism on tensor squares `Γ_L ⊗_L Γ_L →+*ᵍ Γ_W ⊗_A Γ_W`. -/
def gradedLazardTensorHom : LazardRing.coordinateTensorGrading →+*ᵍ tensorGrading where
  toRingHom := lazardTensorHom
  map_mem hx := lazardTensorHom_mem_tensorGrading hx

@[simp] theorem toRingHom_gradedLazardTensorHom :
    gradedLazardTensorHom.toRingHom = lazardTensorHom := (rfl)
@[simp] theorem coe_gradedLazardTensorHom : ⇑gradedLazardTensorHom = lazardTensorHom := (rfl)

/-- **Coproduct compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem lazardTensorHom_comp_coproduct :
    lazardTensorHom.comp LazardRing.coproduct = coproduct.comp lazardArrowHom := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (RingHom.ext fun _ ↦ by simp [lazardTensorHom]) ?_
  rw [LazardRing.map_comp_coproduct_universalStrictCoordinate]; simp [FormalCoordinate.map_comp]
@[simp] theorem lazardTensorHom_coproduct (x : MvPolynomial ℕ+ LazardRing) :
    lazardTensorHom (LazardRing.coproduct x) = coproduct (lazardArrowHom x) :=
  RingHom.congr_fun lazardTensorHom_comp_coproduct x

/-- **Height-ideal invariance**: the extensions of `(formalGroup Universal.curve).heightIdeal p n`
along `Strict.rightUnit` and `C` agree. -/
theorem map_rightUnit_heightIdeal (p n : ℕ) :
    ((formalGroup Universal.curve).heightIdeal p n).map rightUnit =
      ((formalGroup Universal.curve).heightIdeal p n).map C := by
  rw [FormalGroup.map_heightIdeal, FormalGroup.map_heightIdeal, ← map_formalGroup,
    ← map_formalGroup, ← formalCoordinate_smul_formalGroup, FormalGroup.heightIdeal_smul]

/-- `Strict.rightUnit` fixes the `p ^ n` coefficient `v_n` of `[p](z)` on `Universal.curve` modulo
the extended height ideal `I_n A[r, s, t]`. -/
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
