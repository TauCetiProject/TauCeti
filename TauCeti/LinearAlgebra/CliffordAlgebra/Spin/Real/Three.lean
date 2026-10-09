/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Three
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.ReflectionPair
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Hamilton

/-!
# The compact three-dimensional Spin group

The reversal-preserving algebra equivalence `Cl⁺(3,0) ≃ ℍ` transports the even unitary carrier
to the group of unitary Hamilton quaternions. Every such quaternion is a product of two unit
vectors, so its inverse image belongs to the Lipschitz group and the even unitary carrier is
exactly Spin. The vector representation becomes conjugation on the pure quaternions.

Realizing the unit quaternions as complex matrices turns this into the compact real form of the
exceptional isomorphism `Spin₃ ≅ SL₂`, namely `Spin(3) ≅ SU(2)`.

The general unitary transport mechanism lives in
`CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv`; this file records its compact
three-dimensional specialization and closes the remaining Lipschitz condition. The action
comparison specializes the general sum-of-three-squares Hamilton calculation in
`CliffordAlgebra.spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_action`.

## Main definitions and results

* `TauCeti.realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary` identifies the even unitary
  carrier of `Cl(3,0)` with the unitary Hamilton quaternions.
* `TauCeti.realCliffordThreeZeroEvenUnitaryGroup_le_lipschitzGroup` proves that this carrier is
  contained in the Lipschitz group.
* `TauCeti.realSpinThreeEquivQuaternionUnitary` identifies the compact real Spin group with the
  unit Hamilton quaternions.
* `TauCeti.realSpinThreeEquivQuaternionUnitary_action` identifies the vector action with
  quaternion conjugation.
* `TauCeti.realSpinThreeEquivSpecialUnitary` identifies the compact real Spin group with `SU(2)`,
  by composing with `Quaternion.unitaryEquivSpecialUnitaryGroup`.

## Reference

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open scoped Quaternion
open QuadraticMap

namespace TauCeti

/-- The even unitary carrier of the compact three-dimensional real Clifford algebra is the group
of unitary Hamilton quaternions. -/
noncomputable def realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0) ≃* unitary ℍ[ℝ] :=
  CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv
    (realCliffordForm 3 0) realCliffordThreeZeroEvenEquivQuaternion
    realCliffordThreeZeroEvenEquivQuaternion_reverseEven

/-- The quaternion underlying the compact even-unitary equivalence is obtained by applying the
even Clifford-algebra equivalence to the Clifford value. -/
@[simp]
theorem coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0)) :
    (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary x : ℍ[ℝ]) =
      realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0) x) := by
  apply CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply

/-- The inverse compact even-unitary equivalence has Clifford value obtained by applying the
inverse even Clifford-algebra equivalence to the quaternion. -/
@[simp]
theorem coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_symm_apply
    (q : unitary ℍ[ℝ]) :
    ((((realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary.symm q :
        CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0)) :
          (CliffordAlgebra (realCliffordForm 3 0))ˣ) :
            CliffordAlgebra (realCliffordForm 3 0))) =
      (realCliffordThreeZeroEvenEquivQuaternion.symm (q : ℍ[ℝ]) :
        CliffordAlgebra.even (realCliffordForm 3 0)) := by
  apply CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_symm_apply

private theorem exists_unit_vectors_mapping_to_quaternion
    (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) :
    ∃ m n : Fin 3 → ℝ,
      realCliffordForm 3 0 m = 1 ∧ realCliffordForm 3 0 n = 1 ∧
        realCliffordThreeZeroEvenEquivQuaternion
          ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n) = q := by
  by_cases h : q.imI ^ 2 + q.imJ ^ 2 = 0
  · have hi : q.imI = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ]
    have hj : q.imJ = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ]
    refine ⟨![1, 0, 0], ![q.re, -q.imK, 0], ?_, ?_, ?_⟩
    · simp [realCliffordForm_three_zero_apply]
    · simp [realCliffordForm_three_zero_apply, Quaternion.normSq_def'] at hq ⊢
      nlinarith
    · rw [realCliffordThreeZeroEvenEquivQuaternion_ι]
      ext <;> simp [hi, hj]
  · let t : ℝ := q.imI ^ 2 + q.imJ ^ 2
    let s : ℝ := Real.sqrt t
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hs : 0 < s := Real.sqrt_pos.2 ht
    have hs2 : s ^ 2 = t := Real.sq_sqrt ht.le
    dsimp [t] at hs2
    let m : Fin 3 → ℝ := ![q.imI / s, q.imJ / s, 0]
    let n : Fin 3 → ℝ :=
      ![(q.re * q.imI + q.imK * q.imJ) / s,
        (q.re * q.imJ - q.imK * q.imI) / s, s]
    refine ⟨m, n, ?_, ?_, ?_⟩
    · simp [m, realCliffordForm_three_zero_apply]
      field_simp
      nlinarith
    · have hnum :
          (q.re * q.imI + q.imK * q.imJ) ^ 2 +
              (q.re * q.imJ - q.imK * q.imI) ^ 2 =
            (q.re ^ 2 + q.imK ^ 2) * (q.imI ^ 2 + q.imJ ^ 2) := by
        ring
      simp [n, realCliffordForm_three_zero_apply, Quaternion.normSq_def'] at hq ⊢
      field_simp
      nlinarith
    · rw [realCliffordThreeZeroEvenEquivQuaternion_ι]
      apply QuaternionAlgebra.ext
      · dsimp [m, n]
        field_simp
        rw [hs2]
        ring
      · dsimp [m, n]
        field_simp
        ring
      · dsimp [m, n]
        field_simp
        ring
      · dsimp [m, n]
        field_simp
        rw [hs2]
        ring

private theorem real_spin_three_to_even_unitary_surjective :
    Function.Surjective
      (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0)) := by
  intro x
  let q : unitary ℍ[ℝ] := realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary x
  obtain ⟨m, n, hm, hn, hmn⟩ :=
    exists_unit_vectors_mapping_to_quaternion (q : ℍ[ℝ])
      (Quaternion.normSq_coe_unitary_eq_one q)
  let s := CliffordAlgebra.spinReflectionPair (realCliffordForm 3 0) m n hm hn
  refine ⟨s, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
  dsimp only [s]
  -- Normalize the nested Spin and unit coercions before using the reflection-pair formula.
  change ((CliffordAlgebra.spinReflectionPair (realCliffordForm 3 0) m n hm hn :
    spinGroup (realCliffordForm 3 0)) : CliffordAlgebra (realCliffordForm 3 0)) = _
  rw [CliffordAlgebra.coe_spinReflectionPair]
  have heven :
      (CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n =
        CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0) x := by
    apply realCliffordThreeZeroEvenEquivQuaternion.injective
    rw [hmn]
    rw [coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_apply]
  calc
    CliffordAlgebra.ι (realCliffordForm 3 0) m *
          CliffordAlgebra.ι (realCliffordForm 3 0) n =
        (((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n :
          CliffordAlgebra.even (realCliffordForm 3 0)) :
            CliffordAlgebra (realCliffordForm 3 0)) := rfl
    _ = (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0) x :
          CliffordAlgebra (realCliffordForm 3 0)) := congrArg Subtype.val heven
    _ = ((x : (CliffordAlgebra (realCliffordForm 3 0))ˣ) :
          CliffordAlgebra (realCliffordForm 3 0)) :=
      CliffordAlgebra.coe_evenUnitaryGroupEvenPart (realCliffordForm 3 0) x

/-- Every even unitary element of `Cl(3,0)` belongs to its Lipschitz group. Thus the extra
Lipschitz condition in the definition of Spin imposes no restriction in this dimension. -/
theorem realCliffordThreeZeroEvenUnitaryGroup_le_lipschitzGroup :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 3 0) ≤
      lipschitzGroup (realCliffordForm 3 0) := by
  intro x hx
  obtain ⟨s, hs⟩ := real_spin_three_to_even_unitary_surjective ⟨x, hx⟩
  have hUnits : spinGroup.toUnits s = x := by
    simpa using congrArg Subtype.val hs
  rw [← hUnits]
  exact spinGroup.units_mem_lipschitzGroup s.2

/-- The compact real three-dimensional Spin group is the group of unit Hamilton quaternions. -/
noncomputable def realSpinThreeEquivQuaternionUnitary :
    spinGroup (realCliffordForm 3 0) ≃* unitary ℍ[ℝ] :=
  (MulEquiv.ofBijective
      (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0))
      ⟨CliffordAlgebra.spinGroupToEvenUnitary_injective (realCliffordForm 3 0),
        real_spin_three_to_even_unitary_surjective⟩).trans
    realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary

/-- The underlying quaternion of the compact real Spin equivalence is obtained by applying the
even Clifford-algebra equivalence to the Spin element. -/
@[simp]
theorem coe_realSpinThreeEquivQuaternionUnitary_apply
    (s : spinGroup (realCliffordForm 3 0)) :
    (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) =
      realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) := by
  apply coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_apply

/-- The inverse compact real Spin equivalence has Clifford value obtained by applying the inverse
even Clifford-algebra equivalence to the quaternion. -/
@[simp]
theorem coe_realSpinThreeEquivQuaternionUnitary_symm_apply (q : unitary ℍ[ℝ]) :
    ((realSpinThreeEquivQuaternionUnitary.symm q :
        spinGroup (realCliffordForm 3 0)) :
      CliffordAlgebra (realCliffordForm 3 0)) =
        (realCliffordThreeZeroEvenEquivQuaternion.symm (q : ℍ[ℝ]) :
          CliffordAlgebra.even (realCliffordForm 3 0)) := by
  let s := realSpinThreeEquivQuaternionUnitary.symm q
  have hs : CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s =
      realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary.symm q := by
    apply realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary.injective
    apply Subtype.ext
    calc
      (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s) : ℍ[ℝ]) =
          realCliffordThreeZeroEvenEquivQuaternion
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
            (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) :=
        coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_apply _
      _ =
          (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) :=
        (coe_realSpinThreeEquivQuaternionUnitary_apply s).symm
      _ = (q : ℍ[ℝ]) :=
        congrArg Subtype.val (realSpinThreeEquivQuaternionUnitary.apply_symm_apply q)
      _ = (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary
          (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary.symm q) : ℍ[ℝ]) :=
        congrArg Subtype.val
          (realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary.apply_symm_apply q).symm
  have h := coe_realCliffordThreeZeroEvenUnitaryEquivQuaternionUnitary_symm_apply q
  rw [← hs] at h
  dsimp only [s] at h
  calc
    ((realSpinThreeEquivQuaternionUnitary.symm q :
        spinGroup (realCliffordForm 3 0)) : CliffordAlgebra (realCliffordForm 3 0)) =
        ((spinGroup.toUnits (realSpinThreeEquivQuaternionUnitary.symm q) :
          (CliffordAlgebra (realCliffordForm 3 0))ˣ) :
            CliffordAlgebra (realCliffordForm 3 0)) := rfl
    _ = (realCliffordThreeZeroEvenEquivQuaternion.symm (q : ℍ[ℝ]) :
          CliffordAlgebra.even (realCliffordForm 3 0)) := by
      simpa only [CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
        CliffordAlgebra.coe_spinGroupToEvenUnitary_apply] using h

private noncomputable def realThreeToWeightedSumSquaresOne :
    (realCliffordForm 3 0).IsometryEquiv (weightedSumSquares ℝ ![(1 : ℝ), 1, 1]) where
  __ := LinearEquiv.refl ℝ (Fin 3 → ℝ)
  map_app' v := congrArg (fun Q : QuadraticForm ℝ (Fin 3 → ℝ) => Q v)
    (realCliffordForm_zero_eq_weightedSumSquares_one 3).symm

@[simp]
private theorem realThreeToWeightedSumSquaresOne_apply (v : Fin 3 → ℝ) :
    realThreeToWeightedSumSquaresOne v = v := rfl

private noncomputable def realThreeTransportedEvenEquiv :
    CliffordAlgebra.even (realCliffordForm 3 0) ≃ₐ[ℝ] ℍ[ℝ] :=
  (CliffordAlgebra.evenEquivOfIsometry realThreeToWeightedSumSquaresOne).trans
    CliffordAlgebra.evenHamiltonEquivWeightedSumSquaresOne

private theorem realThreeTransportedEvenEquiv_eq :
    realThreeTransportedEvenEquiv = realCliffordThreeZeroEvenEquivQuaternion := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply CliffordAlgebra.even.algHom_ext
  apply CliffordAlgebra.EvenHom.ext
  apply LinearMap.ext₂
  intro x y
  change realThreeTransportedEvenEquiv
      ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin x y) =
    realCliffordThreeZeroEvenEquivQuaternion
      ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin x y)
  rw [realThreeTransportedEvenEquiv, AlgEquiv.trans_apply,
    CliffordAlgebra.evenEquivOfIsometry_ι, realThreeToWeightedSumSquaresOne_apply]
  rw [CliffordAlgebra.evenHamiltonEquivWeightedSumSquaresOne_ι,
    realCliffordThreeZeroEvenEquivQuaternion_ι]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk] <;> ring

private noncomputable def realThreeTransportedSpinEquiv :
    spinGroup (realCliffordForm 3 0) ≃* unitary ℍ[ℝ] :=
  realThreeToWeightedSumSquaresOne.spinGroupEquiv.trans
    CliffordAlgebra.spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne

private theorem realThreeTransportedSpinEquiv_eq :
    realThreeTransportedSpinEquiv = realSpinThreeEquivQuaternionUnitary := by
  apply MulEquiv.ext
  intro s
  apply Subtype.ext
  rw [realThreeTransportedSpinEquiv, MulEquiv.trans_apply,
    CliffordAlgebra.coe_spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_apply,
    coe_realSpinThreeEquivQuaternionUnitary_apply]
  rw [← realThreeTransportedEvenEquiv_eq]
  rw [show CliffordAlgebra.evenUnitaryGroupEvenPart _
        (CliffordAlgebra.spinGroupToEvenUnitary _
          (realThreeToWeightedSumSquaresOne.spinGroupEquiv s)) =
      CliffordAlgebra.evenEquivOfIsometry realThreeToWeightedSumSquaresOne
        (CliffordAlgebra.evenUnitaryGroupEvenPart _
          (CliffordAlgebra.spinGroupToEvenUnitary _ s)) by
    apply Subtype.ext
    simp only [CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
      CliffordAlgebra.coe_spinGroupToEvenUnitary_apply,
      CliffordAlgebra.coe_evenEquivOfIsometry_apply]
    change (realThreeToWeightedSumSquaresOne.spinGroupEquiv s : CliffordAlgebra _) =
      CliffordAlgebra.equivOfIsometry realThreeToWeightedSumSquaresOne
        (s : CliffordAlgebra _)
    rw [QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
      QuadraticMap.Isometry.coe_spinGroupMap_apply,
      CliffordAlgebra.equivOfIsometry_apply]]
  rfl

/-- Under the compact real three-dimensional Spin equivalence and the oriented pure-quaternion
isometry, the Spin action is conjugation by the corresponding unit quaternion. -/
theorem realSpinThreeEquivQuaternionUnitary_action
    (s : spinGroup (realCliffordForm 3 0)) (v : Fin 3 → ℝ) :
    (realCliffordThreeZeroPureQuaternionEquiv (s • v) : ℍ[ℝ]) =
      (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) *
        (realCliffordThreeZeroPureQuaternionEquiv v : ℍ[ℝ]) *
          star (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) := by
  have h := CliffordAlgebra.spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_action
    (s := realThreeToWeightedSumSquaresOne.spinGroupEquiv s) v
  have ha : realThreeToWeightedSumSquaresOne.spinGroupEquiv s • v = s • v := by
    rw [CliffordAlgebra.spinGroup_smul_apply, CliffordAlgebra.spinGroup_smul_apply]
    have hmap := QuadraticMap.Isometry.spinGroupMap_spinVectorAction
      realThreeToWeightedSumSquaresOne.toIsometry s v
    change CliffordAlgebra.spinVectorAction _
        (realThreeToWeightedSumSquaresOne.toIsometry.spinGroupMap s) v =
      CliffordAlgebra.spinVectorAction _ s v at hmap
    simpa only [QuadraticMap.IsometryEquiv.spinGroupEquiv_apply] using hmap
  rw [ha] at h
  rw [← realThreeTransportedSpinEquiv_eq]
  simpa only [realThreeTransportedSpinEquiv, MulEquiv.trans_apply,
    coe_realCliffordThreeZeroPureQuaternionEquiv_apply,
    CliffordAlgebra.coe_pureHamiltonEquivWeightedSumSquaresOne_apply] using h

/-! ### `Spin(3) ≅ SU(2)` -/

/-- **The compact real three-dimensional Spin group is `SU(2)`.** The identification with the unit
Hamilton quaternions, composed with their realization as special unitary matrices of degree two
(`Quaternion.unitaryEquivSpecialUnitaryGroup`), is the compact real form of the exceptional
isomorphism `Spin₃ ≅ SL₂`. -/
noncomputable def realSpinThreeEquivSpecialUnitary :
    spinGroup (realCliffordForm 3 0) ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinThreeEquivQuaternionUnitary.trans Quaternion.unitaryEquivSpecialUnitaryGroup

/-- The special unitary matrix of a Spin element is the matrix of the corresponding unit
quaternion. -/
@[simp]
theorem coe_realSpinThreeEquivSpecialUnitary_apply (s : spinGroup (realCliffordForm 3 0)) :
    (realSpinThreeEquivSpecialUnitary s : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) := by
  simp [realSpinThreeEquivSpecialUnitary]

/-- The Spin element underlying a special unitary matrix has the expected quaternion: the composite
equivalence is determined by `Quaternion.toComplexMatrix` in both directions. -/
theorem toComplexMatrix_coe_realSpinThreeEquivQuaternionUnitary_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Quaternion.toComplexMatrix
        ((realSpinThreeEquivQuaternionUnitary
          (realSpinThreeEquivSpecialUnitary.symm M) : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      (M : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← coe_realSpinThreeEquivSpecialUnitary_apply]
  exact congrArg Subtype.val (realSpinThreeEquivSpecialUnitary.apply_symm_apply M)

/-- **The vector action of `SU(2)` on three-dimensional space is quaternion conjugation.** The
degree-two special unitary matrix of a Spin element determines its rotation of `ℝ³` through the
unit quaternion it is the matrix of. -/
theorem realSpinThreeEquivSpecialUnitary_action
    (s : spinGroup (realCliffordForm 3 0)) (v : Fin 3 → ℝ) :
    Quaternion.toComplexMatrix (realCliffordThreeZeroPureQuaternionEquiv (s • v) : ℍ[ℝ]) =
      (realSpinThreeEquivSpecialUnitary s : Matrix (Fin 2) (Fin 2) ℂ) *
        Quaternion.toComplexMatrix (realCliffordThreeZeroPureQuaternionEquiv v : ℍ[ℝ]) *
          star (realSpinThreeEquivSpecialUnitary s : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [realSpinThreeEquivQuaternionUnitary_action s v, map_mul, map_mul,
    coe_realSpinThreeEquivSpecialUnitary_apply, map_star]

end TauCeti

end
