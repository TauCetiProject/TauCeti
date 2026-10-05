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
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

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
three-dimensional specialization and closes the remaining Lipschitz condition.

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

private abbrev Q3 := realCliffordForm 3 0

private noncomputable abbrev e3 (i : Fin 3) : Fin 3 → ℝ :=
  Pi.basisFun ℝ (Fin 3) i

private noncomputable def basisList3 : List (Fin 3 → ℝ) :=
  [e3 0, e3 1, e3 2]

private theorem basisList3_pairwise : basisList3.Pairwise Q3.IsOrtho := by
  simp [basisList3, e3, QuadraticMap.isOrtho_def,
    realCliffordForm_three_zero_apply, Pi.basisFun_apply]

private theorem basisList3_span :
    Submodule.span ℝ {x | x ∈ basisList3} = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin 3)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [basisList3, e3]

private noncomputable def volume3 : CliffordAlgebra Q3 :=
  (basisList3.map (CliffordAlgebra.ι Q3)).prod

private theorem volume3_mem_center :
    volume3 ∈ Subalgebra.center ℝ (CliffordAlgebra Q3) := by
  apply CliffordAlgebra.prod_map_ι_mem_center_of_odd_length basisList3_pairwise
    (by decide) basisList3_span

private noncomputable def vectorEven3 :
    (Fin 3 → ℝ) →ₗ[ℝ] CliffordAlgebra.even Q3 where
  toFun v :=
    v 0 • (CliffordAlgebra.even.ι Q3).bilin (e3 1) (e3 2) +
      v 1 • (CliffordAlgebra.even.ι Q3).bilin (e3 2) (e3 0) +
        v 2 • (CliffordAlgebra.even.ι Q3).bilin (e3 0) (e3 1)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]
    abel

private theorem map_vectorEven3 (v : Fin 3 → ℝ) :
    realCliffordThreeZeroEvenEquivQuaternion (vectorEven3 v) =
      (realCliffordThreeZeroPureQuaternionEquiv v : ℍ[ℝ]) := by
  simp only [vectorEven3, coe_realCliffordThreeZeroPureQuaternionEquiv_apply]
  ext <;> simp [e3, Pi.basisFun_apply]

private theorem e3_isOrtho {i j : Fin 3} (hij : i ≠ j) :
    Q3.IsOrtho (e3 i) (e3 j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [QuadraticMap.isOrtho_def, realCliffordForm_three_zero_apply,
      e3, Pi.basisFun_apply]

private theorem iota_e3_sq (i : Fin 3) :
    CliffordAlgebra.ι Q3 (e3 i) * CliffordAlgebra.ι Q3 (e3 i) = 1 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  fin_cases i <;> simp [Q3, e3, Pi.basisFun_apply]

private theorem vectorEven3_e3 (i : Fin 3) :
    vectorEven3 (e3 i) =
      ![(CliffordAlgebra.even.ι Q3).bilin (e3 1) (e3 2),
        (CliffordAlgebra.even.ι Q3).bilin (e3 2) (e3 0),
        (CliffordAlgebra.even.ι Q3).bilin (e3 0) (e3 1)] i := by
  fin_cases i <;> apply Subtype.ext <;>
    simp [vectorEven3, CliffordAlgebra.even.ι, e3, Pi.basisFun_apply]

private theorem volume3_eq :
    volume3 =
      CliffordAlgebra.ι Q3 (e3 0) *
        (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)) := by
  simp [volume3, basisList3]

private theorem coe_vectorEven3_e3 (i : Fin 3) :
    (vectorEven3 (e3 i) : CliffordAlgebra Q3) =
      CliffordAlgebra.ι Q3 (e3 i) * volume3 := by
  have h10 := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    (e3_isOrtho (i := 0) (j := 1) (by decide)).symm
  have h20 := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    (e3_isOrtho (i := 0) (j := 2) (by decide)).symm
  have h21 := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    (e3_isOrtho (i := 1) (j := 2) (by decide)).symm
  rw [vectorEven3_e3, volume3_eq]
  -- Expanding the indexed basis value leaves the three standard Clifford calculations below.
  fin_cases i
  · change CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2) =
      CliffordAlgebra.ι Q3 (e3 0) *
        (CliffordAlgebra.ι Q3 (e3 0) *
          (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)))
    rw [← mul_assoc, iota_e3_sq, one_mul]
  · change CliffordAlgebra.ι Q3 (e3 2) * CliffordAlgebra.ι Q3 (e3 0) =
      CliffordAlgebra.ι Q3 (e3 1) *
        (CliffordAlgebra.ι Q3 (e3 0) *
          (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)))
    calc
      CliffordAlgebra.ι Q3 (e3 2) * CliffordAlgebra.ι Q3 (e3 0) =
          -(CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 2)) := h20
      _ = -((CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 1)) *
          (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2))) := by
        congr 1
        calc
          CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 2) =
              CliffordAlgebra.ι Q3 (e3 0) *
                (1 * CliffordAlgebra.ι Q3 (e3 2)) := by rw [one_mul]
          _ = CliffordAlgebra.ι Q3 (e3 0) *
                ((CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 1)) *
                  CliffordAlgebra.ι Q3 (e3 2)) := by rw [iota_e3_sq]
          _ = (CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 1)) *
                (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)) := by
            noncomm_ring
      _ = (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 0)) *
          (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)) := by
        rw [h10, neg_mul]
      _ = CliffordAlgebra.ι Q3 (e3 1) *
          (CliffordAlgebra.ι Q3 (e3 0) *
            (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2))) := by
        noncomm_ring
  · change CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 1) =
      CliffordAlgebra.ι Q3 (e3 2) *
        (CliffordAlgebra.ι Q3 (e3 0) *
          (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)))
    symm
    calc
      CliffordAlgebra.ι Q3 (e3 2) *
          (CliffordAlgebra.ι Q3 (e3 0) *
            (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2))) =
          (CliffordAlgebra.ι Q3 (e3 2) * CliffordAlgebra.ι Q3 (e3 0)) *
            (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)) := by
        noncomm_ring
      _ = -(CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 2)) *
          (CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)) := by
        rw [h20]
      _ = -(CliffordAlgebra.ι Q3 (e3 0) *
          ((CliffordAlgebra.ι Q3 (e3 2) * CliffordAlgebra.ι Q3 (e3 1)) *
            CliffordAlgebra.ι Q3 (e3 2))) := by
        noncomm_ring
      _ = -(CliffordAlgebra.ι Q3 (e3 0) *
          (-(CliffordAlgebra.ι Q3 (e3 1) * CliffordAlgebra.ι Q3 (e3 2)) *
            CliffordAlgebra.ι Q3 (e3 2))) := by
        rw [h21]
      _ = CliffordAlgebra.ι Q3 (e3 0) *
          (CliffordAlgebra.ι Q3 (e3 1) *
            (CliffordAlgebra.ι Q3 (e3 2) * CliffordAlgebra.ι Q3 (e3 2))) := by
        noncomm_ring
      _ = CliffordAlgebra.ι Q3 (e3 0) * CliffordAlgebra.ι Q3 (e3 1) := by
        rw [iota_e3_sq, mul_one]

private theorem coe_vectorEven3 (v : Fin 3 → ℝ) :
    (vectorEven3 v : CliffordAlgebra Q3) =
      CliffordAlgebra.ι Q3 v * volume3 := by
  -- Both sides are linear in `v`; the indexed basis lemma packages all coordinate calculations.
  suffices h :
      (CliffordAlgebra.even Q3).toSubmodule.subtype.comp vectorEven3 =
        (LinearMap.mulRight ℝ volume3).comp (CliffordAlgebra.ι Q3) by
    exact LinearMap.congr_fun h v
  apply (Pi.basisFun ℝ (Fin 3)).ext
  intro i
  simp only [LinearMap.comp_apply]
  change (vectorEven3 (e3 i) : CliffordAlgebra Q3) =
    CliffordAlgebra.ι Q3 (e3 i) * volume3
  exact coe_vectorEven3_e3 i

private theorem vectorEven3_spin_action (s : spinGroup Q3) (v : Fin 3 → ℝ) :
    vectorEven3 (s • v) =
      CliffordAlgebra.evenUnitaryGroupEvenPart Q3
          (CliffordAlgebra.spinGroupToEvenUnitary Q3 s) *
        vectorEven3 v *
          CliffordAlgebra.reverseEven Q3
            (CliffordAlgebra.evenUnitaryGroupEvenPart Q3
              (CliffordAlgebra.spinGroupToEvenUnitary Q3 s)) := by
  apply Subtype.ext
  rw [coe_vectorEven3, CliffordAlgebra.spinGroup_smul_apply,
    CliffordAlgebra.ι_spinVectorAction_apply]
  simp only [Subalgebra.coe_mul, coe_vectorEven3]
  rw [CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_reverseEven_apply,
    CliffordAlgebra.coe_evenUnitaryGroupEvenPart]
  rw [CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
  -- Normalize subtype and unit coercions to an equality in the ambient Clifford algebra.
  change (s : CliffordAlgebra Q3) * CliffordAlgebra.ι Q3 v *
      star (s : CliffordAlgebra Q3) * volume3 =
    (s : CliffordAlgebra Q3) * (CliffordAlgebra.ι Q3 v * volume3) *
      CliffordAlgebra.reverse (s : CliffordAlgebra Q3)
  rw [CliffordAlgebra.reverse_eq_star_of_mem_even
    ⟨(s : CliffordAlgebra Q3), spinGroup.mem_even s.2⟩]
  have hcomm : volume3 * star (s : CliffordAlgebra Q3) =
      star (s : CliffordAlgebra Q3) * volume3 :=
    (Subalgebra.mem_center_iff.mp volume3_mem_center _).symm
  calc
    (s : CliffordAlgebra Q3) * CliffordAlgebra.ι Q3 v *
          star (s : CliffordAlgebra Q3) * volume3 =
        (s : CliffordAlgebra Q3) *
          (CliffordAlgebra.ι Q3 v * (star (s : CliffordAlgebra Q3) * volume3)) := by
      noncomm_ring
    _ = (s : CliffordAlgebra Q3) *
          (CliffordAlgebra.ι Q3 v * (volume3 * star (s : CliffordAlgebra Q3))) := by
      rw [hcomm]
    _ = (s : CliffordAlgebra Q3) * (CliffordAlgebra.ι Q3 v * volume3) *
          star (s : CliffordAlgebra Q3) := by
      noncomm_ring

/-- Under the compact real three-dimensional Spin equivalence and the oriented pure-quaternion
isometry, the Spin action is conjugation by the corresponding unit quaternion. -/
theorem realSpinThreeEquivQuaternionUnitary_action
    (s : spinGroup (realCliffordForm 3 0)) (v : Fin 3 → ℝ) :
    (realCliffordThreeZeroPureQuaternionEquiv (s • v) : ℍ[ℝ]) =
      (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) *
        (realCliffordThreeZeroPureQuaternionEquiv v : ℍ[ℝ]) *
          star (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) := by
  rw [← map_vectorEven3, vectorEven3_spin_action, map_mul, map_mul,
    map_vectorEven3, realCliffordThreeZeroEvenEquivQuaternion_reverseEven,
    coe_realSpinThreeEquivQuaternionUnitary_apply]

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
