/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv

/-!
# The compact three-dimensional even Clifford algebra

The even Clifford algebra of the positive-definite real form in dimension three is the quaternion
algebra. Under this identification, Clifford reversal is quaternion conjugation, so the reverse
norm is the quaternion norm-square. Consequently the even unitary carrier is the group of unitary
quaternions, equivalently the norm-one quaternions.

## Main definitions and results

* `CliffordAlgebra.realCliffordPositiveThreeEvenEquivQuaternion` identifies the even algebra of
  `Cliff(3,0)` with `ℍ[ℝ]`.
* `CliffordAlgebra.realCliffordPositiveThreeEvenEquivQuaternion_reverse` identifies reversal with
  quaternion conjugation.
* `CliffordAlgebra.realEvenUnitaryThreeEquivQuaternionUnitary` identifies the even unitary carrier
  with the unitary quaternions.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap
open scoped Quaternion

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- A quaternion is unitary exactly when its norm-square is one. -/
@[simp]
theorem mem_unitary_iff_normSq_eq_one (q : ℍ[R]) :
    q ∈ unitary ℍ[R] ↔ normSq q = 1 := by
  rw [Unitary.mem_iff, star_mul_self, self_mul_star, and_self]
  constructor
  · intro h
    simpa using congrArg (fun x : ℍ[R] => x.re) h
  · intro h
    simp [h]

end Quaternion

namespace CliffordAlgebra

private noncomputable def realCliffordNegativeLineIsometry :
    (TauCeti.realCliffordForm 0 1).IsometryEquiv
      (-QuadraticMap.sq (R := ℝ) (A := ℝ)) :=
  ⟨(LinearEquiv.funUnique (Fin 1) ℝ ℝ : (Fin (0 + 1) → ℝ) ≃ₗ[ℝ] ℝ), fun v => by
    simp [TauCeti.realCliffordForm_zero_one_apply, QuadraticMap.sq_apply]⟩

private noncomputable def realCliffordZeroThreeAugmentedIsometry :
    (TauCeti.realCliffordForm 0 3).IsometryEquiv
      (EquivEven.Q' (TauCeti.realCliffordForm 0 2)) :=
  (TauCeti.realCliffordSplitIsometry 0 0 2 1).trans
    ((QuadraticMap.IsometryEquiv.refl (TauCeti.realCliffordForm 0 2)).prod
      realCliffordNegativeLineIsometry)

private theorem map_even_eq {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Q : QuadraticForm R M} {P : QuadraticForm R N} (e : Q.IsometryEquiv P) :
    (even Q).map (equivOfIsometry e).toAlgHom = even P := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact map_mem_even e.toIsometry hx
  · intro y hy
    refine ⟨(equivOfIsometry e).symm y, map_mem_even e.symm.toIsometry hy, ?_⟩
    exact (equivOfIsometry e).apply_symm_apply y

private noncomputable def evenEquivOfIsometry {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Q : QuadraticForm R M} {P : QuadraticForm R N} (e : Q.IsometryEquiv P) :
    even Q ≃ₐ[R] even P :=
  ((equivOfIsometry e).subalgebraMap (even Q)).trans
    (Subalgebra.equivOfEq _ _ (map_even_eq e))

@[simp]
private theorem coe_evenEquivOfIsometry_apply {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Q : QuadraticForm R M} {P : QuadraticForm R N} (e : Q.IsometryEquiv P) (x : even Q) :
    (evenEquivOfIsometry e x : CliffordAlgebra P) =
      equivOfIsometry e (x : CliffordAlgebra Q) :=
  rfl

private theorem evenEquivOfIsometry_reverse {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Q : QuadraticForm R M} {P : QuadraticForm R N} (e : Q.IsometryEquiv P) (x : even Q) :
    evenEquivOfIsometry e (reverseEven Q x) = reverseEven P (evenEquivOfIsometry e x) := by
  apply Subtype.ext
  simp only [coe_reverseEven_apply, coe_evenEquivOfIsometry_apply]
  change map e.toIsometry (reverse (x : CliffordAlgebra Q)) =
    reverse (map e.toIsometry (x : CliffordAlgebra Q))
  rw [reverse_eq_star_of_mem_even x,
    reverse_eq_star_of_mem_even
      ⟨map e.toIsometry (x : CliffordAlgebra Q), map_mem_even e.toIsometry x.2⟩]
  exact map_star e.toIsometry (x : CliffordAlgebra Q)

private theorem evenEquivEvenNeg_reverse_bilin {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (m₁ m₂ : M) :
    evenEquivEvenNeg Q (reverseEven Q ((even.ι Q).bilin m₁ m₂)) =
      reverseEven (-Q) (evenEquivEvenNeg Q ((even.ι Q).bilin m₁ m₂)) := by
  have hreverse : reverseEven Q ((even.ι Q).bilin m₁ m₂) =
      (even.ι Q).bilin m₂ m₁ := by
    apply Subtype.ext
    simp [even.ι]
  rw [hreverse, evenEquivEvenNeg_apply, evenEquivEvenNeg_apply,
    evenToNeg_ι, evenToNeg_ι]
  apply Subtype.ext
  simp [even.ι]

private theorem evenEquivEvenNeg_reverse {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (x : even Q) :
    evenEquivEvenNeg Q (reverseEven Q x) =
      reverseEven (-Q) (evenEquivEvenNeg Q x) := by
  rcases x with ⟨x, hx⟩
  induction x, hx using even_induction with
  | algebraMap r =>
      change evenEquivEvenNeg Q
          (reverseEven Q (algebraMap R (even Q) r)) =
        reverseEven (-Q) (evenEquivEvenNeg Q (algebraMap R (even Q) r))
      simp
  | add x y hx hy ihx ihy =>
      change evenEquivEvenNeg Q
          (reverseEven Q (⟨x, hx⟩ + ⟨y, hy⟩)) =
        reverseEven (-Q) (evenEquivEvenNeg Q (⟨x, hx⟩ + ⟨y, hy⟩))
      rw [map_add, map_add, map_add, ihx, ihy]
      exact ((reverseEven (-Q)).map_add _ _).symm
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      let z : even Q := ⟨x, by change x ∈ evenOdd Q 0; exact hx⟩
      change evenEquivEvenNeg Q
          (reverseEven Q ((even.ι Q).bilin m₁ m₂ * z)) =
        reverseEven (-Q)
          (evenEquivEvenNeg Q ((even.ι Q).bilin m₁ m₂ * z))
      rw [reverseEven_mul, map_mul, map_mul, reverseEven_mul, ih,
        evenEquivEvenNeg_reverse_bilin]

private theorem equivEven_symm_reverse {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
    (x : even (EquivEven.Q' Q)) :
    (equivEven Q).symm (reverseEven (EquivEven.Q' Q) x) =
      star ((equivEven Q).symm x) := by
  apply (equivEven Q).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_reverseEven_apply]
  change reverse (x : CliffordAlgebra (EquivEven.Q' Q)) =
    (toEven Q (star ((equivEven Q).symm x)) : CliffordAlgebra (EquivEven.Q' Q))
  rw [star_def]
  rw [coe_toEven_reverse_involute]
  exact congrArg (fun y : even (EquivEven.Q' Q) =>
    reverse (y : CliffordAlgebra (EquivEven.Q' Q)))
      ((equivEven Q).apply_symm_apply x).symm

private theorem realCliffordZeroTwoEquivQuaternion_star
    (x : CliffordAlgebra (TauCeti.realCliffordForm 0 2)) :
    TauCeti.realCliffordZeroTwoEquivQuaternion (star x) =
      star (TauCeti.realCliffordZeroTwoEquivQuaternion x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp [star_def']
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-- The even Clifford algebra of the positive-definite three-dimensional real quadratic form is
the quaternion algebra. -/
noncomputable def realCliffordPositiveThreeEvenEquivQuaternion :
    even (TauCeti.realCliffordForm 3 0) ≃ₐ[ℝ] ℍ[ℝ] :=
  (evenEquivEvenNeg (TauCeti.realCliffordForm 3 0)).trans
    ((evenEquivOfIsometry (TauCeti.realCliffordFormNegIsometry 3 0)).trans
      ((evenEquivOfIsometry realCliffordZeroThreeAugmentedIsometry).trans
        ((equivEven (TauCeti.realCliffordForm 0 2)).symm.trans
          TauCeti.realCliffordZeroTwoEquivQuaternion)))

/-- Under the compact three-dimensional quaternion model, Clifford reversal is quaternion
conjugation. -/
@[simp]
theorem realCliffordPositiveThreeEvenEquivQuaternion_reverse
    (x : even (TauCeti.realCliffordForm 3 0)) :
    realCliffordPositiveThreeEvenEquivQuaternion
        (reverseEven (TauCeti.realCliffordForm 3 0) x) =
      star (realCliffordPositiveThreeEvenEquivQuaternion x) := by
  simp only [realCliffordPositiveThreeEvenEquivQuaternion, AlgEquiv.trans_apply]
  rw [evenEquivEvenNeg_reverse, evenEquivOfIsometry_reverse,
    evenEquivOfIsometry_reverse, equivEven_symm_reverse,
    realCliffordZeroTwoEquivQuaternion_star]

/-- The reverse norm in the compact three-dimensional even Clifford algebra is the quaternion
norm-square. -/
theorem realCliffordPositiveThreeEvenEquivQuaternion_reverse_mul_self
    (x : even (TauCeti.realCliffordForm 3 0)) :
    realCliffordPositiveThreeEvenEquivQuaternion
        (reverseEven (TauCeti.realCliffordForm 3 0) x * x) =
      Quaternion.normSq (realCliffordPositiveThreeEvenEquivQuaternion x) := by
  rw [map_mul, realCliffordPositiveThreeEvenEquivQuaternion_reverse,
    Quaternion.star_mul_self]

private def realEvenUnitaryThreeEvenPart :
    evenUnitaryGroup (TauCeti.realCliffordForm 3 0) →*
      even (TauCeti.realCliffordForm 3 0) where
  toFun x :=
    ⟨((x : (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
      CliffordAlgebra (TauCeti.realCliffordForm 3 0)),
        evenUnitaryGroup.mem_even (TauCeti.realCliffordForm 3 0) x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
private theorem coe_realEvenUnitaryThreeEvenPart
    (x : evenUnitaryGroup (TauCeti.realCliffordForm 3 0)) :
    (realEvenUnitaryThreeEvenPart x :
      CliffordAlgebra (TauCeti.realCliffordForm 3 0)) =
        ((x : (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
          CliffordAlgebra (TauCeti.realCliffordForm 3 0)) :=
  rfl

private noncomputable def realEvenUnitaryThreeToQuaternionUnitary :
    evenUnitaryGroup (TauCeti.realCliffordForm 3 0) →* unitary ℍ[ℝ] :=
  (realCliffordPositiveThreeEvenEquivQuaternion.toMonoidHom.comp
    realEvenUnitaryThreeEvenPart).codRestrict (unitary ℍ[ℝ]) fun x => by
      rw [Unitary.mem_iff]
      let a := realEvenUnitaryThreeEvenPart x
      have ha : (a : CliffordAlgebra (TauCeti.realCliffordForm 3 0)) =
          ((x : (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
            CliffordAlgebra (TauCeti.realCliffordForm 3 0)) :=
        coe_realEvenUnitaryThreeEvenPart x
      have hleft : reverseEven (TauCeti.realCliffordForm 3 0) a * a = 1 := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply]
        rw [reverse_eq_star_of_mem_even a, ha]
        exact Unitary.star_mul_self_of_mem
          (evenUnitaryGroup.mem_unitary (TauCeti.realCliffordForm 3 0) x.2)
      have hright : a * reverseEven (TauCeti.realCliffordForm 3 0) a = 1 := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply]
        rw [reverse_eq_star_of_mem_even a, ha]
        exact Unitary.mul_star_self_of_mem
          (evenUnitaryGroup.mem_unitary (TauCeti.realCliffordForm 3 0) x.2)
      constructor
      · change star (realCliffordPositiveThreeEvenEquivQuaternion a) *
          realCliffordPositiveThreeEvenEquivQuaternion a = 1
        rw [← realCliffordPositiveThreeEvenEquivQuaternion_reverse, ← map_mul, hleft,
          map_one]
      · change realCliffordPositiveThreeEvenEquivQuaternion a *
          star (realCliffordPositiveThreeEvenEquivQuaternion a) = 1
        rw [← realCliffordPositiveThreeEvenEquivQuaternion_reverse, ← map_mul, hright,
          map_one]

private noncomputable def quaternionUnitaryToRealEvenUnitary :
    unitary ℍ[ℝ] →* evenUnitaryGroup (TauCeti.realCliffordForm 3 0) where
  toFun q := by
    let a : even (TauCeti.realCliffordForm 3 0) :=
      realCliffordPositiveThreeEvenEquivQuaternion.symm (q : ℍ[ℝ])
    let uEven : (even (TauCeti.realCliffordForm 3 0))ˣ :=
      Units.map realCliffordPositiveThreeEvenEquivQuaternion.symm.toMonoidHom
        (Unitary.toUnits q)
    let u : (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ :=
      Units.map (even (TauCeti.realCliffordForm 3 0)).val.toMonoidHom uEven
    refine ⟨u, ?_⟩
    have hu : (u : CliffordAlgebra (TauCeti.realCliffordForm 3 0)) = a := rfl
    have hreverse : reverseEven (TauCeti.realCliffordForm 3 0) a =
        realCliffordPositiveThreeEvenEquivQuaternion.symm (star (q : ℍ[ℝ])) := by
      apply realCliffordPositiveThreeEvenEquivQuaternion.injective
      rw [realCliffordPositiveThreeEvenEquivQuaternion_reverse,
        AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [evenUnitaryGroup.mem_iff]
    constructor
    · rw [hu]
      exact a.2
    · rw [Unitary.mem_iff, hu]
      constructor
      · rw [← reverse_eq_star_of_mem_even a]
        have h : reverseEven (TauCeti.realCliffordForm 3 0) a * a = 1 := by
          apply realCliffordPositiveThreeEvenEquivQuaternion.injective
          rw [map_mul, hreverse, AlgEquiv.apply_symm_apply,
            AlgEquiv.apply_symm_apply, map_one]
          exact Unitary.star_mul_self_of_mem q.2
        simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply] using
          congrArg Subtype.val h
      · rw [← reverse_eq_star_of_mem_even a]
        have h : a * reverseEven (TauCeti.realCliffordForm 3 0) a = 1 := by
          apply realCliffordPositiveThreeEvenEquivQuaternion.injective
          rw [map_mul, hreverse, AlgEquiv.apply_symm_apply,
            AlgEquiv.apply_symm_apply, map_one]
          exact Unitary.mul_star_self_of_mem q.2
        simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply] using
          congrArg Subtype.val h
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' q r := by
    apply Subtype.ext
    apply Units.ext
    simp

/-- The even unitary carrier of the compact three-dimensional real Clifford algebra is the group
of unitary quaternions. -/
noncomputable def realEvenUnitaryThreeEquivQuaternionUnitary :
    evenUnitaryGroup (TauCeti.realCliffordForm 3 0) ≃* unitary ℍ[ℝ] where
  toFun := realEvenUnitaryThreeToQuaternionUnitary
  invFun := quaternionUnitaryToRealEvenUnitary
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    simp [realEvenUnitaryThreeToQuaternionUnitary, quaternionUnitaryToRealEvenUnitary,
      realEvenUnitaryThreeEvenPart]
  right_inv q := by
    apply Subtype.ext
    simp [realEvenUnitaryThreeToQuaternionUnitary, quaternionUnitaryToRealEvenUnitary,
      realEvenUnitaryThreeEvenPart]
  map_mul' := map_mul realEvenUnitaryThreeToQuaternionUnitary

private theorem coe_realEvenUnitaryThreeEquivQuaternionUnitary_apply_aux
    (x : evenUnitaryGroup (TauCeti.realCliffordForm 3 0)) :
    (realEvenUnitaryThreeEquivQuaternionUnitary x : ℍ[ℝ]) =
      realCliffordPositiveThreeEvenEquivQuaternion
        ⟨((x : (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
          CliffordAlgebra (TauCeti.realCliffordForm 3 0)),
            evenUnitaryGroup.mem_even (TauCeti.realCliffordForm 3 0) x.2⟩ := by
  rfl

private theorem coe_realEvenUnitaryThreeEquivQuaternionUnitary_symm_apply_aux
    (q : unitary ℍ[ℝ]) :
    ((((realEvenUnitaryThreeEquivQuaternionUnitary.symm q :
        evenUnitaryGroup (TauCeti.realCliffordForm 3 0)) :
          (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
            CliffordAlgebra (TauCeti.realCliffordForm 3 0))) =
      (realCliffordPositiveThreeEvenEquivQuaternion.symm (q : ℍ[ℝ]) :
        even (TauCeti.realCliffordForm 3 0)) := by
  rfl

/-- The quaternion underlying the even-unitary equivalence is obtained by applying the even
Clifford algebra equivalence to the Clifford value. -/
@[simp]
theorem coe_realEvenUnitaryThreeEquivQuaternionUnitary_apply
    (x : evenUnitaryGroup (TauCeti.realCliffordForm 3 0)) :
    (realEvenUnitaryThreeEquivQuaternionUnitary x : ℍ[ℝ]) =
      realCliffordPositiveThreeEvenEquivQuaternion
        ⟨((x : (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
          CliffordAlgebra (TauCeti.realCliffordForm 3 0)),
            evenUnitaryGroup.mem_even (TauCeti.realCliffordForm 3 0) x.2⟩ :=
  coe_realEvenUnitaryThreeEquivQuaternionUnitary_apply_aux x

/-- The inverse even-unitary equivalence has Clifford value obtained by applying the inverse even
Clifford algebra equivalence to the quaternion. -/
@[simp]
theorem coe_realEvenUnitaryThreeEquivQuaternionUnitary_symm_apply (q : unitary ℍ[ℝ]) :
    ((((realEvenUnitaryThreeEquivQuaternionUnitary.symm q :
        evenUnitaryGroup (TauCeti.realCliffordForm 3 0)) :
          (CliffordAlgebra (TauCeti.realCliffordForm 3 0))ˣ) :
            CliffordAlgebra (TauCeti.realCliffordForm 3 0))) =
      (realCliffordPositiveThreeEvenEquivQuaternion.symm (q : ℍ[ℝ]) :
        even (TauCeti.realCliffordForm 3 0)) :=
  coe_realEvenUnitaryThreeEquivQuaternionUnitary_symm_apply_aux q

/-- Every quaternion in the image of the compact three-dimensional even unitary carrier has
norm-square one. -/
theorem normSq_realEvenUnitaryThreeEquivQuaternionUnitary
    (x : evenUnitaryGroup (TauCeti.realCliffordForm 3 0)) :
    Quaternion.normSq (realEvenUnitaryThreeEquivQuaternionUnitary x : ℍ[ℝ]) = 1 :=
  (Quaternion.mem_unitary_iff_normSq_eq_one _).mp
    (realEvenUnitaryThreeEquivQuaternionUnitary x).2

end CliffordAlgebra
