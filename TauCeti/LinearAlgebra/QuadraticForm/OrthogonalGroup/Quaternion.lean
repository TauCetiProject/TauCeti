/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.LowRank.Three
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import Mathlib.Algebra.Quaternion
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Quaternion
import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Kernel
import TauCeti.Algebra.Quaternion.CentralSimple
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quaternion units and ternary special orthogonal groups

For a regular ternary quadratic form over a field of characteristic different from two, all
units of its even Clifford algebra act by conjugation. This action is onto the special orthogonal
group and its kernel consists exactly of the nonzero scalars. Transport through a quaternion
model therefore identifies the special orthogonal group with quaternion units modulo scalars.
The quaternion algebra may be nonsplit, and the norms of its units need not be squares.

The action consumes `CliffordAlgebra.unitsMap_even_mem_lipschitzGroup_of_finrank_eq_three`;
surjectivity and the scalar kernel use the existing Lipschitz action and Cartan–Dieudonné.

## Main results

* `CliffordAlgebra.evenUnitsToSpecialOrthogonal` and
  `CliffordAlgebra.quaternionUnitsToSpecialOrthogonal` are the conjugation actions, with
  surjectivity and scalar-kernel theorems for each.
* `CliffordAlgebra.quaternionUnitsQuotientCenterEquivSpecialOrthogonal` identifies quaternion
  units modulo their center with the ternary special orthogonal group; its evaluation and
  inverse evaluation equations characterize the equivalence.
* `CliffordAlgebra.exists_quaternionUnitsQuotientCenterEquivSpecialOrthogonal_of_finrank_eq_three`
  supplies such a quaternion description for every regular ternary quadratic form.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion

namespace CliffordAlgebra

open TauCeti

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

private noncomputable def evenUnitsToLipschitz (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    (even Q)ˣ →* lipschitzGroup Q :=
  (Units.map (even Q).val.toMonoidHom).codRestrict (lipschitzGroup Q)
    (unitsMap_even_mem_lipschitzGroup_of_finrank_eq_three Q hQ hV)

/-- Conjugation by units of the even Clifford algebra acts on a regular ternary quadratic space
by determinant-one isometries. -/
noncomputable def evenUnitsToSpecialOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    (even Q)ˣ →* QuadraticMap.specialOrthogonalGroup Q := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  exact (((QuadraticMap.orthogonalGroup Q).subtype.comp (lipschitzToOrthogonal Q)).comp
    (evenUnitsToLipschitz Q hQ hV)).codRestrict (QuadraticMap.specialOrthogonalGroup Q)
      (fun x => QuadraticMap.mem_specialOrthogonalGroup_iff.mpr
        ⟨(lipschitzToOrthogonal Q (evenUnitsToLipschitz Q hQ hV x)).2,
          by
            simpa only [QuadraticMap.orthogonalDet_apply, MonoidHom.comp_apply,
              Subgroup.coe_subtype] using
              det_lipschitzToOrthogonal_eq_one_of_mem_even Q
                (evenUnitsToLipschitz Q hQ hV x) (x : even Q).2⟩)

/-- The even-unit action is conjugation on the embedded quadratic space. -/
@[simp]
theorem ι_evenUnitsToSpecialOrthogonal_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (x : (even Q)ˣ) (v : V) :
    ι Q ((evenUnitsToSpecialOrthogonal Q hQ hV x : V ≃ₗ[K] V) v) =
      ((x : even Q) : CliffordAlgebra Q) * ι Q v *
        (((x⁻¹ : (even Q)ˣ) : even Q) : CliffordAlgebra Q) := by
  rw [evenUnitsToSpecialOrthogonal]
  simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.coe_subtype, coe_lipschitzToOrthogonal_apply, ι_lipschitzVectorAction_apply]
  -- Expose the codomain restriction and unit-map projections before the grading identity.
  change involute ((x : even Q) : CliffordAlgebra Q) * ι Q v *
    (((x⁻¹ : (even Q)ˣ) : even Q) : CliffordAlgebra Q) = _
  rw [involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact (x : even Q).2)]

/-- Every proper ternary isometry is conjugation by an even Clifford unit. -/
theorem evenUnitsToSpecialOrthogonal_surjective (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    Function.Surjective (evenUnitsToSpecialOrthogonal Q hQ hV) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  intro g
  obtain ⟨l, hl⟩ := lipschitzToOrthogonal_surjective Q hQ
    (QuadraticMap.specialOrthogonalToOrthogonal Q g)
  have hd : QuadraticMap.orthogonalDet Q (lipschitzToOrthogonal Q l) = 1 := by
    rw [hl]
    exact QuadraticMap.orthogonalDet_specialOrthogonalToOrthogonal g
  have he := mem_even_of_det_lipschitzToOrthogonal_eq_one Q l hd
  have hi := mem_even_of_det_lipschitzToOrthogonal_eq_one Q l⁻¹ (by
    rw [map_inv, map_inv, hd, inv_one])
  let x : (even Q)ˣ :=
    ⟨⟨(l : (CliffordAlgebra Q)ˣ), he⟩,
      ⟨(((l : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q), hi⟩,
      Subtype.ext (Units.mul_inv (l : (CliffordAlgebra Q)ˣ)),
      Subtype.ext (Units.inv_mul (l : (CliffordAlgebra Q)ˣ))⟩
  refine ⟨x, ?_⟩
  ext v
  apply ι_injective Q
  rw [ι_evenUnitsToSpecialOrthogonal_apply]
  have h := congrArg (fun a : QuadraticMap.orthogonalGroup Q => (a : V ≃ₗ[K] V) v) hl
  rw [QuadraticMap.coe_specialOrthogonalToOrthogonal, coe_lipschitzToOrthogonal_apply] at h
  rw [← h, ι_lipschitzVectorAction_apply]
  rw [involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact he)]
  rfl

/-- The kernel of the ternary even-unit action consists exactly of scalar units. -/
theorem ker_evenUnitsToSpecialOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    (evenUnitsToSpecialOrthogonal Q hQ hV).ker =
      (Units.map (algebraMap K (even Q)).toMonoidHom).range := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have hk : (evenUnitsToSpecialOrthogonal Q hQ hV).ker =
      ((lipschitzToOrthogonal Q).comp (evenUnitsToLipschitz Q hQ hV)).ker := by
    rw [evenUnitsToSpecialOrthogonal, MonoidHom.ker_codRestrict, MonoidHom.comp_assoc,
      MonoidHom.ker_comp_of_injective _ _ Subtype.val_injective]
  rw [hk]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    mem_ker_lipschitzToOrthogonal_iff hQ]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, Units.ext (Subtype.ext ?_)⟩
    exact hr.symm
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

/-- A quaternion model of a ternary even Clifford algebra acts on the quadratic space through
all quaternion units. -/
noncomputable def quaternionUnitsToSpecialOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : Kˣ}
    (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)]) :
    ℍ[K,(a : K),(b : K)]ˣ →* QuadraticMap.specialOrthogonalGroup Q :=
  (evenUnitsToSpecialOrthogonal Q hQ hV).comp
    (Units.mapEquiv e.toMulEquiv).symm.toMonoidHom

/-- Under the chosen quaternion model, the special orthogonal action is Clifford conjugation
by the inverse image of the quaternion unit. -/
@[simp]
theorem ι_quaternionUnitsToSpecialOrthogonal_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : Kˣ}
    (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)]) (q : ℍ[K,(a : K),(b : K)]ˣ) (v : V) :
    ι Q ((quaternionUnitsToSpecialOrthogonal Q hQ hV e q : V ≃ₗ[K] V) v) =
      (e.symm q : CliffordAlgebra Q) * ι Q v * (e.symm (q⁻¹ : ℍ[K,(a : K),(b : K)]ˣ) :
        CliffordAlgebra Q) := by
  rw [quaternionUnitsToSpecialOrthogonal, MonoidHom.comp_apply,
    ι_evenUnitsToSpecialOrthogonal_apply]
  simp only [← map_inv, Units.mapEquiv_symm, MulEquiv.coe_toMonoidHom,
    Units.coe_mapEquiv]
  -- The remaining equality only forgets the algebra structure of the chosen equivalence.
  rfl

/-- Every proper ternary isometry is induced by a quaternion unit in any quaternion model of
its even Clifford algebra. -/
theorem quaternionUnitsToSpecialOrthogonal_surjective (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : Kˣ}
    (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)]) :
    Function.Surjective (quaternionUnitsToSpecialOrthogonal Q hQ hV e) :=
  (evenUnitsToSpecialOrthogonal_surjective Q hQ hV).comp
    (Units.mapEquiv e.toMulEquiv).symm.surjective

/-- The kernel of the quaternion-unit action consists of scalar units. -/
theorem ker_quaternionUnitsToSpecialOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : Kˣ}
    (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)]) :
    (quaternionUnitsToSpecialOrthogonal Q hQ hV e).ker =
      (Units.map (algebraMap K ℍ[K,(a : K),(b : K)]).toMonoidHom).range := by
  ext q
  rw [MonoidHom.mem_ker, quaternionUnitsToSpecialOrthogonal, MonoidHom.comp_apply,
    ← MonoidHom.mem_ker, ker_evenUnitsToSpecialOrthogonal, MonoidHom.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have h := congrArg (Units.mapEquiv e.toMulEquiv) hr
    apply Units.ext
    simpa using congrArg Units.val h
  · rintro ⟨r, rfl⟩
    refine ⟨r, Units.ext ?_⟩
    simp

/-- The kernel of the ternary quaternion-unit action is the center of the unit group. -/
theorem ker_quaternionUnitsToSpecialOrthogonal_eq_center (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : Kˣ}
    (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)]) :
    (quaternionUnitsToSpecialOrthogonal Q hQ hV e).ker =
      Subgroup.center ℍ[K,(a : K),(b : K)]ˣ := by
  rw [ker_quaternionUnitsToSpecialOrthogonal,
    QuaternionAlgebra.center_units_eq_range_unitsMap_algebraMap a b
      (isUnit_of_invertible (2 : K)).isRegular.left]

/-- A regular ternary special orthogonal group is the quaternion unit group modulo its center.
The equivalence uses the chosen quaternion model of the even Clifford algebra. -/
noncomputable def quaternionUnitsQuotientCenterEquivSpecialOrthogonal
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3)
    {a b : Kˣ} (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)]) :
    (ℍ[K,(a : K),(b : K)]ˣ ⧸ Subgroup.center ℍ[K,(a : K),(b : K)]ˣ) ≃*
      QuadraticMap.specialOrthogonalGroup Q :=
  (QuotientGroup.quotientMulEquivOfEq
    (ker_quaternionUnitsToSpecialOrthogonal_eq_center Q hQ hV e).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (quaternionUnitsToSpecialOrthogonal_surjective Q hQ hV e))

/-- The center-quotient equivalence sends a quaternion class to its conjugation action. -/
@[simp]
theorem quaternionUnitsQuotientCenterEquivSpecialOrthogonal_mk
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3)
    {a b : Kˣ} (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)])
    (q : ℍ[K,(a : K),(b : K)]ˣ) :
    quaternionUnitsQuotientCenterEquivSpecialOrthogonal Q hQ hV e (QuotientGroup.mk q) =
      quaternionUnitsToSpecialOrthogonal Q hQ hV e q := by
  simp only [quaternionUnitsQuotientCenterEquivSpecialOrthogonal, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The inverse quotient equivalence recovers the class of any quaternion unit inducing the
given isometry. -/
@[simp]
theorem quaternionUnitsQuotientCenterEquivSpecialOrthogonal_symm_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3)
    {a b : Kˣ} (e : even Q ≃ₐ[K] ℍ[K,(a : K),(b : K)])
    (q : ℍ[K,(a : K),(b : K)]ˣ) :
    (quaternionUnitsQuotientCenterEquivSpecialOrthogonal Q hQ hV e).symm
        (quaternionUnitsToSpecialOrthogonal Q hQ hV e q) = QuotientGroup.mk q := by
  rw [← quaternionUnitsQuotientCenterEquivSpecialOrthogonal_mk Q hQ hV e q,
    MulEquiv.symm_apply_apply]

/-- Every regular ternary special orthogonal group admits a quaternion unit-group description
over the base field, including nonsplit quaternion models. -/
theorem exists_quaternionUnitsQuotientCenterEquivSpecialOrthogonal_of_finrank_eq_three
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ∃ a b : Kˣ, Nonempty ((ℍ[K,(a : K),(b : K)]ˣ ⧸
      Subgroup.center ℍ[K,(a : K),(b : K)]ˣ) ≃* QuadraticMap.specialOrthogonalGroup Q) := by
  obtain ⟨a, b, e, _⟩ := exists_evenQuaternionEquiv_of_finrank_eq_three Q hQ hV
  exact ⟨a, b, ⟨quaternionUnitsQuotientCenterEquivSpecialOrthogonal Q hQ hV e⟩⟩

end CliffordAlgebra
