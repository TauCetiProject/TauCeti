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

`Universal.curve` over `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `strictFormalCoordinate` over `A[r, s, t]`
(`StrictArrowRing`) induce a graded Hopf-algebroid morphism `(L, L[b₁, b₂, …]) → (A, A[r, s, t])`.
Since `lazardArrowHom` sends `(b₁, b₂, b₃) ↦ (-s, s² - r, -t - s³ + 2 r s - a₁ r)`, the induced
base-changed homomorphism `A[b₁, b₂, …] →+* A[r, s, t]` over `A` admits an explicit section over `A`
and is surjective.

## Main definitions and results

* `TauCeti.WeierstrassHopfAlgebroid.gradedLazardBaseHom`, `lazardBaseHom`, `gradedLazardArrowHom`,
  `lazardArrowHom`, `gradedLazardPairHom`, `lazardPairHom` and their Hopf-algebroid compatibility
  identities (`lazardArrowHom_comp_C`, `lazardArrowHom_comp_rightUnit`,
  `strictCounit_comp_lazardArrowHom`, `lazardArrowHom_comp_conjugation`,
  `lazardPairHom_comp_coproduct`).
* `TauCeti.WeierstrassHopfAlgebroid.lazardArrowBaseChangeHom`, `lazardArrowBaseChangeSection`, and
  `lazardArrowBaseChangeHom_surjective`.
* `TauCeti.WeierstrassHopfAlgebroid.map_lazardBaseHom_heightIdeal`,
  `map_strictRightUnit_heightIdeal`, and
  `strictRightUnit_coeff_nsmulSeries_sub_strictLeftUnit_mem_map_heightIdeal`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.1, A2.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section

noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve _root_.WeierstrassCurve.VariableChange

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

/-- `lazardBaseHom` preserves homological degrees. -/
theorem lazardBaseHom_mem_baseGrading {n : ℕ} {x : LazardRing} (hx : x ∈ LazardRing.grading n) :
    lazardBaseHom x ∈ baseGrading n := gradedLazardBaseHom.map_mem hx

/-- `lazardBaseHom` pushes `LazardRing.formalGroup` forward to `formalGroup Universal.curve`. -/
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
`(formalGroup (WeierstrassCurve.map Universal.curve strictLeftUnit), strictFormalCoordinate)`. -/
def gradedLazardArrowHom : LazardRing.coordinateGrading →+*ᵍ strictArrowGrading :=
  LazardRing.gradedCoordinateChangeLift
    ⟨(⟨formalGroup (WeierstrassCurve.map Universal.curve strictLeftUnit), inferInstance⟩,
        ⟨strictFormalCoordinate, strictFormalCoordinate_mem_ker_linearCoeff⟩),
      fun d ↦ by
        dsimp only
        rw [map_formalGroup, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
        exact strictLeftUnit_mem_strictArrowGrading (Universal.coeff_formalGroup_mem_baseGrading d),
      coeff_succ_strictFormalCoordinate_mem_strictArrowGrading⟩

/-- The ring homomorphism `L[b₁, b₂, …] →+* A[r, s, t]` classifying `strictFormalCoordinate`. -/
def lazardArrowHom : MvPolynomial ℕ+ LazardRing →+* StrictArrowRing :=
  gradedLazardArrowHom.toRingHom

@[simp] theorem toRingHom_gradedLazardArrowHom : gradedLazardArrowHom.toRingHom = lazardArrowHom :=
  (rfl)
@[simp] theorem coe_gradedLazardArrowHom : ⇑gradedLazardArrowHom = lazardArrowHom := (rfl)

/-- `lazardArrowHom` preserves homological degrees. -/
theorem lazardArrowHom_mem_strictArrowGrading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ LazardRing.coordinateGrading n) : lazardArrowHom x ∈ strictArrowGrading n :=
  gradedLazardArrowHom.map_mem hx

/-- `lazardArrowHom` maps `bᵢ = X i` to the `z^(i + 1)` coefficient of `strictFormalCoordinate`. -/
@[simp] theorem lazardArrowHom_X (i : ℕ+) :
    lazardArrowHom (X i) = PowerSeries.coeff (i + 1) strictFormalCoordinate.toPowerSeries := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_X]

/-- `lazardArrowHom` maps `universalStrictCoordinate` to `strictFormalCoordinate`. -/
@[simp] theorem map_lazardArrowHom_universalStrictCoordinate :
    FormalCoordinate.map lazardArrowHom FormalCoordinate.universalStrictCoordinate =
      strictFormalCoordinate := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.map_coordinateChangeLift_universalStrictCoordinate]

/-- **Left-unit compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem lazardArrowHom_comp_C :
    lazardArrowHom.comp C = strictLeftUnit.comp lazardBaseHom := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_comp_C]
  apply LazardRing.hom_ext
  rw [LazardRing.map_lift, ← FormalGroup.map_comp, map_lazardBaseHom_formalGroup]
  dsimp only; rw [map_formalGroup]

@[simp] theorem lazardArrowHom_C (x : LazardRing) :
    lazardArrowHom (C x) = strictLeftUnit (lazardBaseHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_C x

/-- Specializing `lazardArrowHom` along `(strictArrowEquiv R).symm (W, a)` recovers
`LazardRing.coordinateChangeLift` for `formalGroup W` and
`((heisenbergHom R a).formalCoordinate W)⁻¹`. -/
theorem strictArrowEquiv_symm_comp_lazardArrowHom {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (a : HeisenbergGroup R) :
    ((strictArrowEquiv R).symm (W, a)).comp lazardArrowHom =
      LazardRing.coordinateChangeLift (⟨formalGroup W, inferInstance⟩,
        ⟨((heisenbergHom R a).formalCoordinate W)⁻¹, MonoidHom.mem_ker.mpr (by simp)⟩) := by
  have hW : ((strictArrowEquiv R).symm (W, a)).comp strictLeftUnit = W.specialize := by
    have h := congrArg Prod.fst ((strictArrowEquiv R).apply_symm_apply (W, a))
    rw [strictArrowEquiv_apply] at h; dsimp only at h
    exact Universal.map_curve_injective (h.trans (map_specialize W).symm)
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (by rw [RingHom.comp_assoc, lazardArrowHom_comp_C, ← RingHom.comp_assoc, hW]; simp) ?_
  rw [FormalCoordinate.map_comp, map_lazardArrowHom_universalStrictCoordinate,
    map_strictArrowEquiv_symm_strictFormalCoordinate,
    LazardRing.map_coordinateChangeLift_universalStrictCoordinate]

/-! ### Base-changed surjectivity onto `A[r, s, t]` -/

/-- The base-changed homomorphism `A[b₁, b₂, …] = A ⊗_L L[b₁, b₂, …] →+* A[r, s, t]` induced by
`strictLeftUnit` and `lazardArrowHom`. -/
def lazardArrowBaseChangeHom : MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) →+* StrictArrowRing :=
  pushoutLift lazardBaseHom ⟨(strictLeftUnit, lazardArrowHom), lazardArrowHom_comp_C.symm⟩

@[simp] theorem lazardArrowBaseChangeHom_comp_C :
    lazardArrowBaseChangeHom.comp C = strictLeftUnit :=
  pushoutLift_comp_C _ _
@[simp] theorem lazardArrowBaseChangeHom_C (f : MvPolynomial Coeff ℤ) :
    lazardArrowBaseChangeHom (C f) = strictLeftUnit f :=
  pushoutLift_C _ _ f
@[simp] theorem lazardArrowBaseChangeHom_comp_map_lazardBaseHom :
    lazardArrowBaseChangeHom.comp (MvPolynomial.map lazardBaseHom) = lazardArrowHom :=
  pushoutLift_comp_map _ _
@[simp] theorem lazardArrowBaseChangeHom_map_lazardBaseHom (x : MvPolynomial ℕ+ LazardRing) :
    lazardArrowBaseChangeHom (MvPolynomial.map lazardBaseHom x) = lazardArrowHom x :=
  pushoutLift_map _ _ x
@[simp] theorem lazardArrowBaseChangeHom_X (i : ℕ+) :
    lazardArrowBaseChangeHom (X i) = lazardArrowHom (X i) :=
  pushoutLift_X _ _ i

/-- An explicit section `A[r, s, t] →+* A[b₁, b₂, …]` over `A` of `lazardArrowBaseChangeHom`. -/
def lazardArrowBaseChangeSection :
    StrictArrowRing →+* MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) :=
  let r₀ : MvPolynomial ℕ+ (MvPolynomial Coeff ℤ) := X 1 ^ 2 - X 2
  (aeval (Sum.elim (fun i ↦ C (X i))
    ![r₀, -X 1, -X 3 + X 1 ^ 3 - 2 * r₀ * X 1 - C (X .A₁) * r₀])).toRingHom

@[simp] theorem lazardArrowBaseChangeSection_X_inl (i : Coeff) :
    lazardArrowBaseChangeSection (X (.inl i)) = C (X i) := by
  simp [lazardArrowBaseChangeSection]
@[simp] theorem lazardArrowBaseChangeSection_X_inr_zero :
    lazardArrowBaseChangeSection (X (.inr 0)) = X 1 ^ 2 - X 2 := by
  simp [lazardArrowBaseChangeSection]
@[simp] theorem lazardArrowBaseChangeSection_X_inr_one :
    lazardArrowBaseChangeSection (X (.inr 1)) = -X 1 := by
  simp [lazardArrowBaseChangeSection]
@[simp] theorem lazardArrowBaseChangeSection_X_inr_two :
    lazardArrowBaseChangeSection (X (.inr 2)) =
      -X 3 + X 1 ^ 3 - 2 * (X 1 ^ 2 - X 2) * X 1 - C (X .A₁) * (X 1 ^ 2 - X 2) := by
  simp [lazardArrowBaseChangeSection]

/-- `lazardArrowBaseChangeSection` restricts to `C` along `strictLeftUnit`. -/
@[simp] theorem lazardArrowBaseChangeSection_comp_strictLeftUnit :
    lazardArrowBaseChangeSection.comp strictLeftUnit = C :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp

@[simp] theorem lazardArrowBaseChangeSection_strictLeftUnit (f : MvPolynomial Coeff ℤ) :
    lazardArrowBaseChangeSection (strictLeftUnit f) = C f :=
  RingHom.congr_fun lazardArrowBaseChangeSection_comp_strictLeftUnit f

/-- `lazardArrowBaseChangeSection` is a right inverse to `lazardArrowBaseChangeHom`. -/
@[simp] theorem lazardArrowBaseChangeHom_comp_lazardArrowBaseChangeSection :
    lazardArrowBaseChangeHom.comp lazardArrowBaseChangeSection = RingHom.id StrictArrowRing :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simp
    · fin_cases j
      · simp
      · simp
      · simp [map_ofNat]; ring

@[simp] theorem lazardArrowBaseChangeHom_lazardArrowBaseChangeSection (p : StrictArrowRing) :
    lazardArrowBaseChangeHom (lazardArrowBaseChangeSection p) = p :=
  RingHom.congr_fun lazardArrowBaseChangeHom_comp_lazardArrowBaseChangeSection p

/-- The base-changed homomorphism `A[b₁, b₂, …] →+* A[r, s, t]` is surjective. -/
theorem lazardArrowBaseChangeHom_surjective : Function.Surjective lazardArrowBaseChangeHom :=
  Function.RightInverse.surjective lazardArrowBaseChangeHom_lazardArrowBaseChangeSection

/-! ### Remaining Hopf-algebroid homomorphism identities and height ideals -/

/-- **Right-unit compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem lazardArrowHom_comp_rightUnit :
    lazardArrowHom.comp LazardRing.rightUnit = strictRightUnit.comp lazardBaseHom := by
  rw [lazardArrowHom, gradedLazardArrowHom, LazardRing.toRingHom_gradedCoordinateChangeLift,
    LazardRing.coordinateChangeLift_comp_rightUnit]
  apply LazardRing.hom_ext
  rw [LazardRing.map_lift, ← FormalGroup.map_comp, map_lazardBaseHom_formalGroup]
  dsimp only; rw [strictFormalCoordinate_smul_formalGroup, map_formalGroup]

@[simp] theorem lazardArrowHom_rightUnit (x : LazardRing) :
    lazardArrowHom (LazardRing.rightUnit x) = strictRightUnit (lazardBaseHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_rightUnit x

/-- **Counit compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem strictCounit_comp_lazardArrowHom :
    strictCounit.comp lazardArrowHom = lazardBaseHom.comp LazardRing.counit :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate (RingHom.ext fun _ ↦ by simp)
    (by simp [FormalCoordinate.map_comp])

@[simp] theorem strictCounit_lazardArrowHom (x : MvPolynomial ℕ+ LazardRing) :
    strictCounit (lazardArrowHom x) = lazardBaseHom (LazardRing.counit x) :=
  RingHom.congr_fun strictCounit_comp_lazardArrowHom x

/-- **Conjugation compatibility** of `lazardArrowHom`. -/
@[simp] theorem lazardArrowHom_comp_conjugation :
    lazardArrowHom.comp LazardRing.conjugation = strictConjugation.comp lazardArrowHom :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate (RingHom.ext fun _ ↦ by simp)
    (by simp [FormalCoordinate.map_comp])

@[simp] theorem lazardArrowHom_conjugation (x : MvPolynomial ℕ+ LazardRing) :
    lazardArrowHom (LazardRing.conjugation x) = strictConjugation (lazardArrowHom x) :=
  RingHom.congr_fun lazardArrowHom_comp_conjugation x

/-- The ring homomorphism `L[b₁, b₂, …] ⊗_L L[b₁, b₂, …] →+* A[r, s, t] ⊗_A A[r, s, t]` induced on
composable pairs. -/
def lazardPairHom : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* StrictPairRing :=
  pushoutLift LazardRing.rightUnit
    ⟨(strictLeft.comp lazardArrowHom, strictRight.comp lazardArrowHom),
      RingHom.ext fun x ↦ by
        simp only [RingHom.comp_apply, lazardArrowHom_rightUnit, lazardArrowHom_C]
        exact (RingHom.congr_fun strictRight_comp_strictLeftUnit (lazardBaseHom x)).symm⟩

@[simp] theorem lazardPairHom_comp_C : lazardPairHom.comp C = strictLeft.comp lazardArrowHom :=
  pushoutLift_comp_C _ _
@[simp] theorem lazardPairHom_comp_map_rightUnit :
    lazardPairHom.comp (MvPolynomial.map LazardRing.rightUnit) =
      strictRight.comp lazardArrowHom := pushoutLift_comp_map _ _
@[simp] theorem lazardPairHom_C (x : MvPolynomial ℕ+ LazardRing) :
    lazardPairHom (C x) = strictLeft (lazardArrowHom x) := pushoutLift_C _ _ x
@[simp] theorem lazardPairHom_map_rightUnit (x : MvPolynomial ℕ+ LazardRing) :
    lazardPairHom (MvPolynomial.map LazardRing.rightUnit x) =
      strictRight (lazardArrowHom x) := pushoutLift_map _ _ x
@[simp] theorem lazardPairHom_X (i : ℕ+) :
    lazardPairHom (X i) = strictRight (lazardArrowHom (X i)) :=
  pushoutLift_X _ _ i

/-- `lazardPairHom` preserves homological degrees. -/
theorem lazardPairHom_mem_strictPairGrading {n : ℕ}
    {x : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)}
    (hx : x ∈ LazardRing.coordinateTensorGrading n) : lazardPairHom x ∈ strictPairGrading n :=
  (LazardRing.coordinateTensorGrading_map_mem_iff strictPairGrading (.id ℕ) lazardPairHom).mpr
    ⟨fun _ _ hy ↦ by simpa using lazardArrowHom_mem_strictArrowGrading hy,
      fun i ↦ by simpa using coeff_succ_strictFormalCoordinate_mem_strictArrowGrading i⟩ hx

/-- The graded ring homomorphism `L[b₁, b₂, …] ⊗_L L[b₁, b₂, …] →+*ᵍ A[r, s, t] ⊗_A A[r, s, t]`
on composable pairs. -/
def gradedLazardPairHom : LazardRing.coordinateTensorGrading →+*ᵍ strictPairGrading where
  toRingHom := lazardPairHom
  map_mem hx := lazardPairHom_mem_strictPairGrading hx

@[simp] theorem toRingHom_gradedLazardPairHom :
    gradedLazardPairHom.toRingHom = lazardPairHom := (rfl)
@[simp] theorem coe_gradedLazardPairHom : ⇑gradedLazardPairHom = lazardPairHom := (rfl)

/-- **Coproduct compatibility** of `(lazardBaseHom, lazardArrowHom)`. -/
@[simp] theorem lazardPairHom_comp_coproduct :
    lazardPairHom.comp LazardRing.coproduct = strictCoproduct.comp lazardArrowHom := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (RingHom.ext fun x ↦ by
      simp only [RingHom.comp_apply, LazardRing.coproduct_C, lazardPairHom_C, lazardArrowHom_C]
      exact (RingHom.congr_fun strictCoproduct_comp_strictLeftUnit (lazardBaseHom x)).symm) ?_
  rw [LazardRing.map_comp_coproduct_universalStrictCoordinate]; simp [FormalCoordinate.map_comp]

@[simp] theorem lazardPairHom_coproduct (x : MvPolynomial ℕ+ LazardRing) :
    lazardPairHom (LazardRing.coproduct x) = strictCoproduct (lazardArrowHom x) :=
  RingHom.congr_fun lazardPairHom_comp_coproduct x

/-- **Height-ideal invariance**: the extensions of `(formalGroup Universal.curve).heightIdeal p n`
along `strictRightUnit` and `strictLeftUnit` agree. -/
theorem map_strictRightUnit_heightIdeal (p n : ℕ) :
    ((formalGroup Universal.curve).heightIdeal p n).map strictRightUnit =
      ((formalGroup Universal.curve).heightIdeal p n).map strictLeftUnit := by
  rw [FormalGroup.map_heightIdeal, FormalGroup.map_heightIdeal, ← map_formalGroup,
    ← map_formalGroup, ← strictFormalCoordinate_smul_formalGroup, FormalGroup.heightIdeal_smul]

/-- `strictRightUnit` fixes the `p ^ n` coefficient `v_n` of `[p](z)` on `Universal.curve` modulo
the extended height ideal `I_n A[r, s, t]`. -/
theorem strictRightUnit_coeff_nsmulSeries_sub_strictLeftUnit_mem_map_heightIdeal (p n : ℕ) :
    strictRightUnit (PowerSeries.coeff (p ^ n) ((formalGroup Universal.curve).nsmulSeries p)) -
        strictLeftUnit (PowerSeries.coeff (p ^ n) ((formalGroup Universal.curve).nsmulSeries p)) ∈
      ((formalGroup Universal.curve).heightIdeal p n).map strictLeftUnit := by
  have h := Ideal.mem_map_of_mem lazardArrowHom
    (LazardRing.rightUnit_sub_C_mem_map_heightIdeal p n)
  rw [Ideal.map_map, lazardArrowHom_comp_C, ← Ideal.map_map, map_lazardBaseHom_heightIdeal,
    map_sub, lazardArrowHom_rightUnit, lazardArrowHom_C] at h
  have hc : lazardBaseHom (PowerSeries.coeff (p ^ n) (LazardRing.formalGroup.nsmulSeries p)) =
      PowerSeries.coeff (p ^ n) ((formalGroup Universal.curve).nsmulSeries p) := by
    rw [← FormalGroup.coeff_nsmulSeries_map, map_lazardBaseHom_formalGroup]
  rwa [hc] at h

end TauCeti.WeierstrassHopfAlgebroid
