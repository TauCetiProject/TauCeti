/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import TauCeti.RingTheory.MvPolynomial.Pushout
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# The strict Weierstrass Hopf algebroid

Over `A = ℤ[a₁, a₂, a₃, a₄, a₆]`, the strict coordinate-change ring
`StrictChangeRing A = A[r, s, t]` from `VariableChange.Representable` forms Bauer's cubic Hopf
algebroid `(A, A[r, s, t])` (`TauCeti.WeierstrassHopfAlgebroid.Strict`), with `MvPolynomial.C`,
`Strict.rightUnit`, `Strict.counit`, `Strict.coproduct` (`Δr = r₁ + r₂`, `Δs = s₁ + s₂`,
`Δt = t₁ + t₂ + s₁ r₂`), and `Strict.conjugation` (`(r, s, t) ↦ (-r, -s, r s - t)`). Setting
`u = 1` gives `(id_A, toStrict) : (A, Γ) → (A, A[r, s, t])` and
`isIntegralModularForm_iff_strictRightUnit`.

`WeierstrassHopfAlgebroid.Strict` adapts the Hopf-algebroid templates in
`TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/HopfAlgebroid.lean` and
`TauCeti/RingTheory/FormalGroup/CoordinateChange/HopfAlgebroid.lean` (via
`MvPolynomial.pushoutLift`).

## Main definitions and results

* `TauCeti.WeierstrassHopfAlgebroid.Strict`: `ArrowRing`, `rightUnit`, `counit`, `coproduct`,
  `conjugation` and their Hopf-algebroid laws (`coproduct_coassoc`, counit and antipode laws).
* `TauCeti.WeierstrassHopfAlgebroid.toStrict`, `toStrictTensor`,
  `WeierstrassCurve.isIntegralModularForm_iff_strictRightUnit`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.1.
-/

public section

noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve _root_.WeierstrassCurve.VariableChange
open TauCeti.WeierstrassChange TauCeti.WeierstrassChange.StrictChangeRing

namespace Strict

variable {R : Type*} [CommRing R]

/-! ### The strict Weierstrass Hopf algebroid `(A, A[r, s, t])` -/

/-- The ring `A[r, s, t] = ℤ[a₁, a₂, a₃, a₄, a₆][r, s, t]` of arrows of the strict Weierstrass
Hopf algebroid. -/
abbrev ArrowRing : Type := StrictChangeRing (MvPolynomial Coeff ℤ)

/-- The **right unit** `η_R : ℤ[a₁, ⋯, a₆] →+* A[r, s, t]`, classifying `(1, r, s, t) • W`. -/
def rightUnit : MvPolynomial Coeff ℤ →+* ArrowRing :=
  (universalChange (MvPolynomial Coeff ℤ) • WeierstrassCurve.map Universal.curve C).specialize
@[simp] theorem map_rightUnit :
    WeierstrassCurve.map Universal.curve rightUnit =
      universalChange (MvPolynomial Coeff ℤ) • WeierstrassCurve.map Universal.curve C :=
  map_specialize _
@[simp] theorem rightUnit_A₁ : rightUnit (X .A₁) = C (X .A₁) + 2 * (X 1 : ArrowRing) := by
  simp [rightUnit, variableChange_a₁]
@[simp] theorem rightUnit_A₂ :
    rightUnit (X .A₂) = C (X .A₂) - X 1 * C (X .A₁) + 3 * X 0 - (X 1 : ArrowRing) ^ 2 := by
  simp [rightUnit, variableChange_a₂]
@[simp] theorem rightUnit_A₃ :
    rightUnit (X .A₃) = C (X .A₃) + X 0 * C (X .A₁) + 2 * (X 2 : ArrowRing) := by
  simp [rightUnit, variableChange_a₃]
@[simp] theorem rightUnit_A₄ :
    rightUnit (X .A₄) =
      C (X .A₄) - X 1 * C (X .A₃) + 2 * X 0 * C (X .A₂) - (X 2 + X 0 * X 1) * C (X .A₁) +
        3 * X 0 ^ 2 - 2 * X 1 * (X 2 : ArrowRing) := by simp [rightUnit, variableChange_a₄]
@[simp] theorem rightUnit_A₆ :
    rightUnit (X .A₆) =
      C (X .A₆) + X 0 * C (X .A₄) + X 0 ^ 2 * C (X .A₂) + X 0 ^ 3 - X 2 * C (X .A₃) -
        X 2 ^ 2 - X 0 * X 2 * (C (X .A₁) : ArrowRing) := by simp [rightUnit, variableChange_a₆]

theorem map_comp_rightUnit (k : ArrowRing →+* R) :
    WeierstrassCurve.map Universal.curve (k.comp rightUnit) =
      (universalChange (MvPolynomial Coeff ℤ)).map k •
        WeierstrassCurve.map Universal.curve (k.comp C) := by
  rw [← WeierstrassCurve.map_map, map_rightUnit, ← map_variableChange, WeierstrassCurve.map_map]
theorem comp_rightUnit (k : ArrowRing →+* R) :
    k.comp rightUnit =
      ((universalChange (MvPolynomial Coeff ℤ)).map k •
        WeierstrassCurve.map Universal.curve (k.comp C)).specialize := by
  rw [← map_comp_rightUnit, WeierstrassCurve.specialize_map, Universal.specialize_curve,
    RingHom.comp_id]

variable (R) in
/-- **Homomorphisms out of `A[r, s, t]` classify strict arrows** `W → heisenbergHom R a • W`. -/
def arrowEquiv : (ArrowRing →+* R) ≃ WeierstrassCurve R × HeisenbergGroup R where
  toFun k := (WeierstrassCurve.map Universal.curve (k.comp C),
    HeisenbergGroup.map k (universalHeisenberg (MvPolynomial Coeff ℤ)))
  invFun p := StrictChangeRing.lift (p.1.specialize, p.2)
  left_inv _ := StrictChangeRing.ringHom_ext (by simp) (by simp)
  right_inv _ := by simp
@[simp] theorem arrowEquiv_apply (k : ArrowRing →+* R) :
    arrowEquiv R k = (WeierstrassCurve.map Universal.curve (k.comp C),
      HeisenbergGroup.map k (universalHeisenberg (MvPolynomial Coeff ℤ))) := (rfl)
@[simp] theorem arrowEquiv_symm_apply (p : WeierstrassCurve R × HeisenbergGroup R) :
    (arrowEquiv R).symm p = StrictChangeRing.lift (p.1.specialize, p.2) := (rfl)

/-! ### The counit -/

/-- The **counit** `ε : A[r, s, t] →+* ℤ[a₁, ⋯, a₆]`, sending `r, s, t` to `0`. -/
def counit : ArrowRing →+* MvPolynomial Coeff ℤ := StrictChangeRing.lift (RingHom.id _, 1)

@[simp] theorem counit_X (i : Fin 3) : counit (X i) = 0 := by fin_cases i <;> simp [counit]
@[simp] theorem counit_comp_C : counit.comp C = RingHom.id (MvPolynomial Coeff ℤ) :=
  StrictChangeRing.lift_comp_C _
@[simp] theorem counit_C (a : MvPolynomial Coeff ℤ) : counit (C a) = a :=
  StrictChangeRing.lift_C _ a
theorem map_counit_universalHeisenberg :
    HeisenbergGroup.map counit (universalHeisenberg (MvPolynomial Coeff ℤ)) = 1 :=
  StrictChangeRing.map_lift_universalHeisenberg _
@[simp] theorem universalChange_map_counit :
    (universalChange (MvPolynomial Coeff ℤ)).map counit = 1 := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_counit_universalHeisenberg,
    _root_.map_one]
@[simp] theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id (MvPolynomial Coeff ℤ) :=
  Universal.map_curve_injective (by simp [map_comp_rightUnit])
@[simp] theorem counit_rightUnit (a : MvPolynomial Coeff ℤ) : counit (rightUnit a) = a :=
  RingHom.congr_fun counit_comp_rightUnit a

/-! ### The coproduct -/

/-- The **coproduct** `Δ : A[r, s, t] →+* A[r, s, t][r', s', t']`, classifying the composite
`a₂ * a₁` of the universal composable pair of strict arrows. -/
def coproduct : ArrowRing →+* StrictChangeRing ArrowRing :=
  StrictChangeRing.lift (C.comp C,
    HeisenbergGroup.map (MvPolynomial.map rightUnit) (universalHeisenberg (MvPolynomial Coeff ℤ)) *
      HeisenbergGroup.map C (universalHeisenberg (MvPolynomial Coeff ℤ)))

@[simp] theorem coproduct_comp_C : coproduct.comp C = C.comp C := StrictChangeRing.lift_comp_C _
@[simp] theorem coproduct_C (a : MvPolynomial Coeff ℤ) : coproduct (C a) = C (C a) :=
  RingHom.congr_fun coproduct_comp_C a
theorem map_coproduct_universalHeisenberg :
    HeisenbergGroup.map coproduct (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      HeisenbergGroup.map (MvPolynomial.map rightUnit)
        (universalHeisenberg (MvPolynomial Coeff ℤ)) *
        HeisenbergGroup.map C (universalHeisenberg (MvPolynomial Coeff ℤ)) :=
  StrictChangeRing.map_lift_universalHeisenberg _
@[simp] theorem universalChange_map_coproduct :
    (universalChange (MvPolynomial Coeff ℤ)).map coproduct =
      universalChange ArrowRing * (universalChange (MvPolynomial Coeff ℤ)).map C := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_coproduct_universalHeisenberg,
    _root_.map_mul, map_map_universalHeisenberg, ← map_heisenbergHom,
    ← universalChange_eq_heisenbergHom, ← universalChange_eq_heisenbergHom]
@[simp] theorem coproduct_comp_rightUnit :
    coproduct.comp rightUnit = (MvPolynomial.map rightUnit).comp rightUnit :=
  Universal.map_curve_injective (by simp [map_comp_rightUnit, mul_smul])
@[simp] theorem coproduct_rightUnit (a : MvPolynomial Coeff ℤ) :
    coproduct (rightUnit a) = MvPolynomial.map rightUnit (rightUnit a) :=
  RingHom.congr_fun coproduct_comp_rightUnit a
@[simp] theorem coproduct_r : coproduct (X 0) = C (X 0) + (X 0 : StrictChangeRing ArrowRing) := by
  simpa [coproduct] using add_comm (X 0 : StrictChangeRing ArrowRing) (C (X 0))
@[simp] theorem coproduct_s : coproduct (X 1) = C (X 1) + (X 1 : StrictChangeRing ArrowRing) := by
  simpa [coproduct] using add_comm (X 1 : StrictChangeRing ArrowRing) (C (X 1))
@[simp] theorem coproduct_t :
    coproduct (X 2) = C (X 2) + X 2 + C (X 1) * (X 0 : StrictChangeRing ArrowRing) := by
  simp [coproduct]; ring

theorem map_comp_coproduct_universalHeisenberg (k : StrictChangeRing ArrowRing →+* R) :
    HeisenbergGroup.map (k.comp coproduct) (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      HeisenbergGroup.map (k.comp (MvPolynomial.map rightUnit))
        (universalHeisenberg (MvPolynomial Coeff ℤ)) *
        HeisenbergGroup.map (k.comp C) (universalHeisenberg (MvPolynomial Coeff ℤ)) := by
  ext <;> simp <;> ring

/-- **The left counit law** `(ε ⊗ id) Δ = id`. -/
theorem pushoutLift_counit_id_comp_coproduct :
    (pushoutLift rightUnit ⟨(C.comp counit, RingHom.id ArrowRing), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          coproduct = RingHom.id ArrowRing :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by fin_cases i <;> simp

/-- **The right counit law** `(id ⊗ ε) Δ = id`. -/
theorem pushoutLift_id_counit_comp_coproduct :
    (pushoutLift rightUnit ⟨(RingHom.id ArrowRing, rightUnit.comp counit), by
        rw [RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]⟩).comp coproduct =
      RingHom.id ArrowRing :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by fin_cases i <;> simp

/-- The map `Δ ⊗ id` into `A[r, s, t] ⊗_A A[r, s, t] ⊗_A A[r, s, t]`. -/
def coproductLeft :
    StrictChangeRing ArrowRing →+* StrictChangeRing (StrictChangeRing ArrowRing) :=
  pushoutLift rightUnit
    ⟨(C.comp coproduct, MvPolynomial.map ((MvPolynomial.map rightUnit).comp rightUnit)),
      RingHom.ext fun _ ↦ by simp⟩

@[simp] theorem coproductLeft_comp_C :
    coproductLeft.comp C = (C : StrictChangeRing ArrowRing →+* _).comp coproduct :=
  pushoutLift_comp_C _ _
@[simp] theorem coproductLeft_comp_map :
    coproductLeft.comp (MvPolynomial.map rightUnit) =
      MvPolynomial.map ((MvPolynomial.map rightUnit).comp rightUnit) :=
  pushoutLift_comp_map _ _
@[simp] theorem coproductLeft_C (x : ArrowRing) : coproductLeft (C x) = C (coproduct x) :=
  pushoutLift_C _ _ x
@[simp] theorem coproductLeft_map (x : ArrowRing) :
    coproductLeft (MvPolynomial.map rightUnit x) =
      MvPolynomial.map ((MvPolynomial.map rightUnit).comp rightUnit) x :=
  pushoutLift_map _ _ x
@[simp] theorem coproductLeft_X (i : Fin 3) : coproductLeft (X i) = X i := by simp [coproductLeft]

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ` of the strict Weierstrass coproduct. -/
theorem coproduct_coassoc :
    coproductLeft.comp coproduct =
      (pushoutLift rightUnit
        ⟨((C : StrictChangeRing ArrowRing →+* _).comp C,
          (MvPolynomial.map (MvPolynomial.map rightUnit)).comp coproduct),
          RingHom.ext fun _ ↦ by simp⟩).comp coproduct :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp [coproductLeft]) fun i ↦ by
    fin_cases i <;> simp [coproductLeft] <;> ring

/-! ### The conjugation -/

/-- The **conjugation** `c : A[r, s, t] →+* A[r, s, t]`, classifying `(1, -r, -s, r s - t)`. -/
def conjugation : ArrowRing →+* ArrowRing :=
  StrictChangeRing.lift (rightUnit, (universalHeisenberg (MvPolynomial Coeff ℤ))⁻¹)

@[simp] theorem conjugation_comp_C : conjugation.comp C = rightUnit :=
  StrictChangeRing.lift_comp_C _
@[simp] theorem conjugation_C (a : MvPolynomial Coeff ℤ) : conjugation (C a) = rightUnit a :=
  StrictChangeRing.lift_C _ a
theorem map_conjugation_universalHeisenberg :
    HeisenbergGroup.map conjugation (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      (universalHeisenberg (MvPolynomial Coeff ℤ))⁻¹ :=
  StrictChangeRing.map_lift_universalHeisenberg _
@[simp] theorem universalChange_map_conjugation :
    (universalChange (MvPolynomial Coeff ℤ)).map conjugation =
      (universalChange (MvPolynomial Coeff ℤ))⁻¹ := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_conjugation_universalHeisenberg,
    _root_.map_inv]
@[simp] theorem conjugation_r : conjugation (X 0) = -(X 0 : ArrowRing) := by simp [conjugation]
@[simp] theorem conjugation_s : conjugation (X 1) = -(X 1 : ArrowRing) := by simp [conjugation]
@[simp] theorem conjugation_t : conjugation (X 2) = X 0 * X 1 - (X 2 : ArrowRing) := by
  simp [conjugation]; ring
@[simp] theorem conjugation_comp_rightUnit : conjugation.comp rightUnit = C :=
  Universal.map_curve_injective (by
    dsimp only
    rw [map_comp_rightUnit, universalChange_map_conjugation, conjugation_comp_C, map_rightUnit,
      inv_smul_smul])
@[simp] theorem conjugation_rightUnit (a : MvPolynomial Coeff ℤ) :
    conjugation (rightUnit a) = C a := RingHom.congr_fun conjugation_comp_rightUnit a
@[simp] theorem conjugation_comp_conjugation :
    conjugation.comp conjugation = RingHom.id ArrowRing :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by fin_cases i <;> simp
@[simp] theorem conjugation_conjugation (x : ArrowRing) : conjugation (conjugation x) = x :=
  RingHom.congr_fun conjugation_comp_conjugation x
@[simp] theorem counit_comp_conjugation : counit.comp conjugation = counit :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by fin_cases i <;> simp
@[simp] theorem counit_conjugation (x : ArrowRing) : counit (conjugation x) = counit x :=
  RingHom.congr_fun counit_comp_conjugation x

/-- **The left antipode equation** `μ (c ⊗ id) Δ = η_R ε`. -/
theorem pushoutLift_conjugation_id_comp_coproduct :
    (pushoutLift rightUnit ⟨(conjugation, RingHom.id ArrowRing), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp coproduct =
      rightUnit.comp counit :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by
    fin_cases i
    · simp
    · simp
    · simp; ring

/-- **The right antipode equation** `μ (id ⊗ c) Δ = η_L ε`. -/
theorem pushoutLift_id_conjugation_comp_coproduct :
    (pushoutLift rightUnit ⟨(RingHom.id ArrowRing, conjugation), by
        rw [conjugation_comp_C, RingHom.id_comp]⟩).comp coproduct =
      C.comp counit :=
  MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by
    fin_cases i
    · simp
    · simp
    · simp; ring

end Strict

/-! ### Comparison between `(A, Γ)` and `(A, A[r, s, t])` -/

/-- The Hopf-algebroid specialization `Γ = A[u, u⁻¹, r, s, t] →+* A[r, s, t]` setting `u = 1`. -/
def toStrict : ArrowRing →+* Strict.ArrowRing := fromChangeRing (MvPolynomial Coeff ℤ)

@[simp] theorem toStrict_comp_algebraMap :
    toStrict.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) = C :=
  fromChangeRing_comp_algebraMap _
@[simp] theorem toStrict_algebraMap (a : MvPolynomial Coeff ℤ) :
    toStrict (algebraMap (MvPolynomial Coeff ℤ) ArrowRing a) = C a :=
  fromChangeRing_algebraMap _ a
@[simp] theorem toStrict_algebraMap_X (i : Fin 4) :
    toStrict (algebraMap (MvPolynomial (Fin 4) (MvPolynomial Coeff ℤ)) ArrowRing (X i)) =
      ![1, X 0, X 1, X 2] i := fromChangeRing_algebraMap_X _ i
@[simp] theorem universalChange_map_toStrict :
    (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map toStrict =
      StrictChangeRing.universalChange (MvPolynomial Coeff ℤ) :=
  universalChange_map_fromChangeRing _
theorem toStrict_u :
    toStrict ((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u : ArrowRing) = 1 := by
  simp [toStrict, ChangeRing.universalChange_u]
@[simp] theorem toStrict_u_inv :
    toStrict ((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u⁻¹ : ArrowRingˣ) = 1 := by
  simp [toStrict]
@[simp] theorem toStrict_comp_rightUnit : toStrict.comp rightUnit = Strict.rightUnit :=
  Universal.map_curve_injective (by simp [map_comp_rightUnit])
@[simp] theorem toStrict_rightUnit (a : MvPolynomial Coeff ℤ) :
    toStrict (rightUnit a) = Strict.rightUnit a := RingHom.congr_fun toStrict_comp_rightUnit a
@[simp] theorem strictCounit_comp_toStrict : Strict.counit.comp toStrict = counit :=
  ChangeRing.ringHom_ext (RingHom.ext fun _ ↦ by simp) (by simp [← VariableChange.map_map])
@[simp] theorem strictCounit_toStrict (x : ArrowRing) : Strict.counit (toStrict x) = counit x :=
  RingHom.congr_fun strictCounit_comp_toStrict x

/-- The tensor-square specialization `Γ ⊗_A Γ →+* A[r, s, t] ⊗_A A[r, s, t]`. -/
def toStrictTensor : ChangeRing ArrowRing →+* StrictChangeRing Strict.ArrowRing :=
  ChangeRing.pushoutLift rightUnit
    ⟨(C.comp toStrict, (MvPolynomial.map Strict.rightUnit).comp toStrict),
      RingHom.ext fun _ ↦ by simp⟩

@[simp] theorem toStrictTensor_comp_algebraMap :
    toStrictTensor.comp (algebraMap ArrowRing (ChangeRing ArrowRing)) = C.comp toStrict :=
  ChangeRing.pushoutLift_comp_algebraMap _ _
@[simp] theorem toStrictTensor_comp_map :
    toStrictTensor.comp (ChangeRing.map rightUnit) =
      (MvPolynomial.map Strict.rightUnit).comp toStrict := ChangeRing.pushoutLift_comp_map _ _
@[simp] theorem toStrictTensor_algebraMap (x : ArrowRing) :
    toStrictTensor (algebraMap ArrowRing (ChangeRing ArrowRing) x) = C (toStrict x) :=
  ChangeRing.pushoutLift_algebraMap _ _ x
@[simp] theorem toStrictTensor_map (x : ArrowRing) :
    toStrictTensor (ChangeRing.map rightUnit x) =
      MvPolynomial.map Strict.rightUnit (toStrict x) := ChangeRing.pushoutLift_map _ _ x

/-- `toStrict` intertwines the coproducts of `(A, Γ)` and `(A, A[r, s, t])`. -/
@[simp] theorem toStrictTensor_comp_coproduct :
    toStrictTensor.comp coproduct = Strict.coproduct.comp toStrict := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun _ ↦ by simp [toStrictTensor]) ?_
  rw [universalChange_map_comp_coproduct]; simp [← VariableChange.map_map]
@[simp] theorem toStrictTensor_coproduct (x : ArrowRing) :
    toStrictTensor (coproduct x) = Strict.coproduct (toStrict x) :=
  RingHom.congr_fun toStrictTensor_comp_coproduct x
@[simp] theorem toStrict_comp_conjugation :
    toStrict.comp conjugation = Strict.conjugation.comp toStrict :=
  ChangeRing.ringHom_ext (RingHom.ext fun _ ↦ by simp) (by simp [← VariableChange.map_map])
@[simp] theorem toStrict_conjugation (x : ArrowRing) :
    toStrict (conjugation x) = Strict.conjugation (toStrict x) :=
  RingHom.congr_fun toStrict_comp_conjugation x

end TauCeti.WeierstrassHopfAlgebroid

namespace WeierstrassCurve

open MvPolynomial TauCeti.WeierstrassHopfAlgebroid TauCeti.WeierstrassChange

/-- **Integral modular forms via the strict Weierstrass Hopf algebroid**: `f ∈ ℤ[a₁, ⋯, a₆]` is an
integral modular form of weight `k` iff `f` is weighted homogeneous of weight `k` and
`Strict.rightUnit f = C f`. -/
theorem isIntegralModularForm_iff_strictRightUnit {k : ℕ} {f : MvPolynomial Coeff ℤ} :
    IsIntegralModularForm k f ↔
      f.IsWeightedHomogeneous coefficientWeight k ∧ Strict.rightUnit f = C f := by
  refine ⟨fun hf ↦ ⟨hf.isWeightedHomogeneous, ?_⟩, fun ⟨hdeg, hstrict⟩ ↦ ?_⟩
  · simpa using congrArg toStrict (isIntegralModularForm_iff_rightUnit.mp hf)
  · refine isIntegralModularForm_def.mpr fun R _ W C₀ ↦ ?_
    obtain ⟨⟨a, u₀⟩, rfl⟩ := (VariableChange.semidirectProductEquiv R).surjective C₀
    simp only [VariableChange.semidirectProductEquiv_apply]
    have hk := congrArg
      (StrictChangeRing.lift ((VariableChange.scaling R u₀ • W).specialize, a)) hstrict
    rw [← RingHom.comp_apply, Strict.comp_rightUnit] at hk
    have h₁ : (VariableChange.heisenbergHom R a •
          (VariableChange.scaling R u₀ • W)).specialize f =
        (VariableChange.scaling R u₀ • W).specialize f := by simpa using hk
    have h₂ : (VariableChange.scaling R u₀ • W).specialize f = ↑u₀⁻¹ ^ k * W.specialize f := by
      rw [VariableChange.scaling_apply]
      exact isWeightedHomogeneous_iff_forall_specialize_mk_smul.mp hdeg R W u₀
    have hu : (VariableChange.heisenbergHom R a * VariableChange.scaling R u₀).u = u₀ := by
      simp [VariableChange.mul_def]
    rw [mul_smul, h₁, h₂, hu]

end WeierstrassCurve
