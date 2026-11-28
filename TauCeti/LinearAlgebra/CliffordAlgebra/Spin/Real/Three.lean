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
    · have _ :
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
  exact spinGroup.units_mem_lipschitzGroup s.property

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

private theorem weightedSumSquares_one_three_eq :
    weightedSumSquares ℝ (1 : Fin 3 → ℝ) = weightedSumSquares ℝ ![(1 : ℝ), 1, 1] := by
  congr 1
  funext i
  fin_cases i <;> rfl

private noncomputable def castEvenEquiv {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)} (hQ : Q₀ = Q₁)
    (e : CliffordAlgebra.even Q₁ ≃ₐ[ℝ] ℍ[ℝ]) : CliffordAlgebra.even Q₀ ≃ₐ[ℝ] ℍ[ℝ] :=
  hQ ▸ e

private noncomputable def castSpinEquiv {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)} (hQ : Q₀ = Q₁)
    (e : spinGroup Q₁ ≃* unitary ℍ[ℝ]) : spinGroup Q₀ ≃* unitary ℍ[ℝ] :=
  hQ ▸ e

private def castSpinElem {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)} (hQ : Q₀ = Q₁)
    (s : spinGroup Q₀) : spinGroup Q₁ :=
  hQ ▸ s

private theorem algEquiv_trans_castEvenEquiv_apply {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)}
    (hQ : Q₀ = Q₁) (e₀ : CliffordAlgebra.even (realCliffordForm 3 0) ≃ₐ[ℝ] CliffordAlgebra.even Q₀)
    (e₁ : CliffordAlgebra.even Q₁ ≃ₐ[ℝ] ℍ[ℝ])
    (x : CliffordAlgebra.even (realCliffordForm 3 0)) :
    (e₀.trans (castEvenEquiv hQ e₁)) x = e₁ (hQ ▸ e₀ x) := by
  cases hQ
  rfl

private theorem castEvenEquiv_apply {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)} (hQ : Q₀ = Q₁)
    (e₁ : CliffordAlgebra.even Q₁ ≃ₐ[ℝ] ℍ[ℝ]) (x : CliffordAlgebra.even Q₀) :
    (castEvenEquiv hQ e₁) x = e₁ (hQ ▸ x) := by
  cases hQ
  rfl

private theorem mulEquiv_trans_castSpinEquiv_apply {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)}
    (hQ : Q₀ = Q₁) (e₀ : spinGroup (realCliffordForm 3 0) ≃* spinGroup Q₀)
    (e₁ : spinGroup Q₁ ≃* unitary ℍ[ℝ])
    (s : spinGroup (realCliffordForm 3 0)) :
    (e₀.trans (castSpinEquiv hQ e₁)) s = e₁ (castSpinElem hQ (e₀ s)) := by
  cases hQ
  rfl

private theorem cast_even_ι_bilin {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)} (hQ : Q₀ = Q₁)
    (x y : Fin 3 → ℝ) :
    hQ ▸ ((CliffordAlgebra.even.ι Q₀).bilin x y) = (CliffordAlgebra.even.ι Q₁).bilin x y := by
  cases hQ
  rfl

private theorem coe_castEven_spinGroupToEvenUnitary {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)}
    (hQ : Q₀ = Q₁) (e₁ : CliffordAlgebra.even Q₁ ≃ₐ[ℝ] ℍ[ℝ]) (s : spinGroup Q₀) :
    e₁ (CliffordAlgebra.evenUnitaryGroupEvenPart Q₁
        (CliffordAlgebra.spinGroupToEvenUnitary Q₁ (castSpinElem hQ s))) =
      (castEvenEquiv hQ e₁) (CliffordAlgebra.evenUnitaryGroupEvenPart Q₀
        (CliffordAlgebra.spinGroupToEvenUnitary Q₀ s)) := by
  cases hQ
  rfl

private theorem castSpinElem_smul {Q₀ Q₁ : QuadraticForm ℝ (Fin 3 → ℝ)} (hQ : Q₀ = Q₁)
    (s : spinGroup Q₀) (v : Fin 3 → ℝ) :
    (castSpinElem hQ s) • v = s • v := by
  cases hQ
  rfl

private noncomputable def realThreeTransportedEvenEquiv :
    CliffordAlgebra.even (realCliffordForm 3 0) ≃ₐ[ℝ] ℍ[ℝ] :=
  (CliffordAlgebra.evenEquivOfIsometry (realCliffordFormZeroIsometryWeightedSumSquares 3)).trans
    (castEvenEquiv weightedSumSquares_one_three_eq
      CliffordAlgebra.evenHamiltonEquivWeightedSumSquaresOne)

private theorem realThreeTransportedEvenEquiv_eq :
    realThreeTransportedEvenEquiv = realCliffordThreeZeroEvenEquivQuaternion := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply CliffordAlgebra.even.algHom_ext
  apply CliffordAlgebra.EvenHom.ext
  apply LinearMap.ext₂
  intro x y
  -- `EvenHom.ext` leaves equality of the underlying bilinear generator maps. Expose their
  -- applications because the available transport lemmas rewrite the generators, not these maps.
  change realThreeTransportedEvenEquiv
      ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin x y) =
    realCliffordThreeZeroEvenEquivQuaternion
      ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin x y)
  rw [realThreeTransportedEvenEquiv, algEquiv_trans_castEvenEquiv_apply,
    CliffordAlgebra.evenEquivOfIsometry_ι, realCliffordFormZeroIsometryWeightedSumSquares_apply,
    realCliffordFormZeroIsometryWeightedSumSquares_apply,
    cast_even_ι_bilin weightedSumSquares_one_three_eq x y,
    CliffordAlgebra.evenHamiltonEquivWeightedSumSquaresOne_ι,
    realCliffordThreeZeroEvenEquivQuaternion_ι]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk] <;> ring

private noncomputable def realThreeTransportedSpinEquiv :
    spinGroup (realCliffordForm 3 0) ≃* unitary ℍ[ℝ] :=
  (realCliffordFormZeroIsometryWeightedSumSquares 3).spinGroupEquiv.trans
    (castSpinEquiv weightedSumSquares_one_three_eq
      CliffordAlgebra.spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne)

private theorem realThreeTransportedSpinEquiv_eq :
    realThreeTransportedSpinEquiv = realSpinThreeEquivQuaternionUnitary := by
  apply MulEquiv.ext
  intro s
  apply Subtype.ext
  rw [realThreeTransportedSpinEquiv, mulEquiv_trans_castSpinEquiv_apply,
    CliffordAlgebra.coe_spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_apply,
    coe_castEven_spinGroupToEvenUnitary, coe_realSpinThreeEquivQuaternionUnitary_apply,
    ← realThreeTransportedEvenEquiv_eq, realThreeTransportedEvenEquiv,
    algEquiv_trans_castEvenEquiv_apply, castEvenEquiv_apply]
  congr 2
  apply Subtype.ext
  simp only [CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_spinGroupToEvenUnitary_apply,
    CliffordAlgebra.coe_evenEquivOfIsometry_apply]
  -- The coercion lemmas reduce both even-unitary values to Clifford elements; expose the
  -- remaining bundled Spin-equivalence coercion before applying its named application lemma.
  change ((realCliffordFormZeroIsometryWeightedSumSquares 3).spinGroupEquiv s :
      CliffordAlgebra _) =
    CliffordAlgebra.equivOfIsometry (realCliffordFormZeroIsometryWeightedSumSquares 3)
      (s : CliffordAlgebra _)
  rw [QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
    QuadraticMap.Isometry.coe_spinGroupMap_apply,
    CliffordAlgebra.equivOfIsometry_apply]

/-- Under the compact real three-dimensional Spin equivalence and the oriented pure-quaternion
isometry, the Spin action is conjugation by the corresponding unit quaternion. -/
theorem realSpinThreeEquivQuaternionUnitary_action
    (s : spinGroup (realCliffordForm 3 0)) (v : Fin 3 → ℝ) :
    (realCliffordThreeZeroPureQuaternionEquiv (s • v) : ℍ[ℝ]) =
      (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) *
        (realCliffordThreeZeroPureQuaternionEquiv v : ℍ[ℝ]) *
          star (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]) := by
  have h := CliffordAlgebra.spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_action
    (s := castSpinElem weightedSumSquares_one_three_eq
      ((realCliffordFormZeroIsometryWeightedSumSquares 3).spinGroupEquiv s)) v
  have ha :
      (castSpinElem weightedSumSquares_one_three_eq
        ((realCliffordFormZeroIsometryWeightedSumSquares 3).spinGroupEquiv s)) • v = s • v := by
    rw [castSpinElem_smul, CliffordAlgebra.spinGroup_smul_apply,
      CliffordAlgebra.spinGroup_smul_apply]
    have hmap := QuadraticMap.Isometry.spinGroupMap_spinVectorAction
      (realCliffordFormZeroIsometryWeightedSumSquares 3).toIsometry s v
    simp only [QuadraticMap.IsometryEquiv.toIsometry_apply,
      realCliffordFormZeroIsometryWeightedSumSquares_apply] at hmap
    simpa only [QuadraticMap.IsometryEquiv.spinGroupEquiv_apply] using hmap
  rw [ha] at h
  rw [← realThreeTransportedSpinEquiv_eq]
  simpa only [realThreeTransportedSpinEquiv, mulEquiv_trans_castSpinEquiv_apply,
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
