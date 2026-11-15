/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Algebra.Star.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Three

/-!
# The compact four-dimensional Spin group

The reversal-preserving equivalence `Cl⁺(4,0) ≃ ℍ × ℍ` transports the even unitary carrier to a
pair of unit-quaternion groups.  The general rank-four comparison between Spin and the even
unitary carrier then gives

`Spin(4) ≃ unitary ℍ × unitary ℍ ≃ SU(2) × SU(2)`.

This is the compact real form of the exceptional type-`D₂ = A₁ × A₁` isomorphism.  Both quaternion
factors have norm one; in particular the split discriminant algebra does not make either factor a
split real group.

In addition to the native coordinate model arising from the dimension-shift reduction of `Cl(4,0)`,
this file provides the calibrated model `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd`
compatible with the standard ordered `(1, i, j, k)` quaternion identification of `ℝ⁴`
(`TauCeti.realCliffordFourZeroCalibratedQuaternionEquiv`).  In these coordinates:

* `(q_L, q_R)` acts on `v ∈ ℝ⁴ ≃ ℍ` by `v ↦ q_L * v * star q_R`;
* first-coordinate stabilization `Spin(3) →* Spin(4)` (`v ↦ Fin.cons 0 v`) embeds `Spin(3)` onto
  the diagonal subgroup `q_L = q_R`, intertwined with `TauCeti.realSpinThreeEquivQuaternionUnitary`
  by inner conjugation by `(1 + k) / √2`;
* conjugation by first-coordinate reflection (`v ↦ Fin.cons (-v 0) (Fin.tail v)`) swaps the two
  unit-quaternion factors.

## Main definitions and results

* `TauCeti.realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd` identifies the even unitary
  carrier with two unit-quaternion groups.
* `TauCeti.realSpinFourEquivQuaternionUnitaryProd` identifies compact real `Spin(4)` with two
  unit-quaternion groups and exposes its forward and inverse Clifford equations.
* `TauCeti.normSq_fst_realSpinFourEquivQuaternionUnitaryProd` and
  `TauCeti.normSq_snd_realSpinFourEquivQuaternionUnitaryProd` state the two norm-one conditions.
* `TauCeti.realSpinFourEquivQuaternionUnitaryProd_action` identifies the vector action with left
  multiplication by the first quaternion and inverse right multiplication by the second.
* `TauCeti.realSpinFourEquivSpecialUnitaryProd` identifies compact real `Spin(4)` with
  `SU(2) × SU(2)`.
* `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd`,
  `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd_action`, and
  `TauCeti.realSpinFourCalibratedEquivSpecialUnitaryProd` provide the calibrated `(1, i, j, k)`
  unit-quaternion and `SU(2) × SU(2)` models and vector-action formula.
* `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion` and
  `TauCeti.mem_range_realCliffordSpinFirstInclusion_three_iff` identify the image of
  first-coordinate stabilization `Spin(3) →* Spin(4)` with the diagonal subgroup.
* `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection` proves that
  first-coordinate reflection swaps the two `Spin(4)` factors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open scoped Quaternion

namespace TauCeti

/-- The even unitary carrier of the compact four-dimensional real Clifford algebra is a product
of two unit-quaternion groups. -/
noncomputable def realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0) ≃*
      unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  (CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv
    (realCliffordForm 4 0) realCliffordFourZeroEvenEquivQuaternionProd
    realCliffordFourZeroEvenEquivQuaternionProd_reverseEven).trans
      (Unitary.prodEquiv ℍ[ℝ] ℍ[ℝ])

/-- The quaternion pair underlying the compact even-unitary equivalence is obtained by applying
the even Clifford-algebra equivalence to the Clifford value. -/
@[simp]
theorem coe_realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0)) :
    (((realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd x).1 : ℍ[ℝ]),
        ((realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd x).2 : ℍ[ℝ])) =
      realCliffordFourZeroEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0) x) := by
  rw [realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    Unitary.coe_prodEquiv_apply]
  exact CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply
    (realCliffordForm 4 0) realCliffordFourZeroEvenEquivQuaternionProd
      realCliffordFourZeroEvenEquivQuaternionProd_reverseEven x

/-- The inverse compact even-unitary equivalence has Clifford value obtained by applying the
inverse quaternion-pair algebra equivalence. -/
@[simp]
theorem coe_realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    ((((realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0)) :
          (CliffordAlgebra (realCliffordForm 4 0))ˣ) :
            CliffordAlgebra (realCliffordForm 4 0))) =
      (realCliffordFourZeroEvenEquivQuaternionProd.symm
          ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra.even (realCliffordForm 4 0)) := by
  rw [realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd,
    MulEquiv.symm_trans_apply]
  refine (CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_symm_apply
    (realCliffordForm 4 0) realCliffordFourZeroEvenEquivQuaternionProd
      realCliffordFourZeroEvenEquivQuaternionProd_reverseEven
      ((Unitary.prodEquiv ℍ[ℝ] ℍ[ℝ]).symm q)).trans ?_
  exact congrArg (fun p : ℍ[ℝ] × ℍ[ℝ] =>
    (realCliffordFourZeroEvenEquivQuaternionProd.symm p :
      CliffordAlgebra (realCliffordForm 4 0)))
    (Unitary.coe_prodEquiv_symm_apply ℍ[ℝ] ℍ[ℝ] q)

/-- The compact real Spin group in dimension four is a product of two unit-quaternion groups. -/
noncomputable def realSpinFourEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  (CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour
    (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp) (by simp)).trans
    realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd

/-- The compact `Spin(4)` equivalence evaluates the quaternion-pair algebra model on the
underlying even Clifford element. -/
@[simp]
theorem coe_realSpinFourEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    (((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
        ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) =
      realCliffordFourZeroEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) := by
  rw [realSpinFourEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_realCliffordFourZeroEvenUnitaryEquivQuaternionUnitaryProd_apply _

/-- The inverse compact `Spin(4)` equivalence recovers the Clifford value from the inverse
quaternion-pair algebra model. -/
@[simp]
theorem coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    (realSpinFourEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra (realCliffordForm 4 0)) =
      (realCliffordFourZeroEvenEquivQuaternionProd.symm
          ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra (realCliffordForm 4 0)) := by
  let s := realSpinFourEquivQuaternionUnitaryProd.symm q
  have hs :
      realCliffordFourZeroEvenEquivQuaternionProd
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
            (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) =
        ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) := by
    rw [← coe_realSpinFourEquivQuaternionUnitaryProd_apply]
    exact congrArg (fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      ((p.1 : ℍ[ℝ]), (p.2 : ℍ[ℝ])))
        (realSpinFourEquivQuaternionUnitaryProd.apply_symm_apply q)
  have h := congrArg
    (fun x : CliffordAlgebra.even (realCliffordForm 4 0) =>
      (x : CliffordAlgebra (realCliffordForm 4 0)))
    ((realCliffordFourZeroEvenEquivQuaternionProd.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

/-- The first quaternion attached to a compact `Spin(4)` element has norm one. -/
theorem normSq_fst_realSpinFourEquivQuaternionUnitaryProd
    (s : spinGroup (realCliffordForm 4 0)) :
    Quaternion.normSq
        ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) = (1 : ℝ) :=
  Quaternion.normSq_coe_unitary_eq_one _

/-- The second quaternion attached to a compact `Spin(4)` element has norm one. -/
theorem normSq_snd_realSpinFourEquivQuaternionUnitaryProd
    (s : spinGroup (realCliffordForm 4 0)) :
    Quaternion.normSq
        ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ]) = (1 : ℝ) :=
  Quaternion.normSq_coe_unitary_eq_one _

private abbrev Q4 := realCliffordForm 4 0

private noncomputable abbrev e4 (i : Fin 4) : Fin 4 → ℝ :=
  Pi.basisFun ℝ (Fin 4) i

private noncomputable def vectorEven4 :
    (Fin 4 → ℝ) →ₗ[ℝ] CliffordAlgebra.even Q4 :=
  (CliffordAlgebra.even.ι Q4).bilin.flip (e4 3)

private theorem map_vectorEven4 (v : Fin 4 → ℝ) :
    (realCliffordFourZeroEvenEquivQuaternionProd (vectorEven4 v)).1 *
        (_root_.QuaternionAlgebra.Basis.self ℝ).k =
      realCliffordFourZeroQuaternionEquiv v := by
  rw [vectorEven4, LinearMap.flip_apply,
    realCliffordFourZeroEvenEquivQuaternionProd_ι]
  ext <;> simp [e4, Pi.basisFun_apply, QuaternionAlgebra.mk_mul_mk]

private noncomputable def quaternionKUnitary : unitary ℍ[ℝ] :=
  ⟨(_root_.QuaternionAlgebra.Basis.self ℝ).k, by
    rw [Quaternion.mem_unitary_iff_normSq_eq_one]
    simp [Quaternion.normSq]⟩

private noncomputable def quaternionKConj : ℍ[ℝ] ≃⋆ₐ[ℝ] ℍ[ℝ] :=
  Unitary.conjStarAlgAut ℝ ℍ[ℝ] quaternionKUnitary

private theorem quaternionKConj_apply (q : ℍ[ℝ]) :
    quaternionKConj q = ⟨q.re, -q.imI, -q.imJ, q.imK⟩ :=
  by
    simp only [quaternionKConj, Unitary.conjStarAlgAut_apply]
    ext <;> simp [quaternionKUnitary]

private theorem e4_three_sq :
    CliffordAlgebra.ι Q4 (e4 3) * CliffordAlgebra.ι Q4 (e4 3) = 1 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [Q4, e4, Pi.basisFun_apply]

private noncomputable def referenceConjEven :
    CliffordAlgebra.even Q4 →ₐ[ℝ] CliffordAlgebra.even Q4 where
  toFun x :=
    ⟨CliffordAlgebra.ι Q4 (e4 3) * x * CliffordAlgebra.ι Q4 (e4 3), by
      -- Expose membership in the degree-zero part after multiplying degrees `1 + 0 + 1`.
      change _ ∈ CliffordAlgebra.evenOdd Q4 0
      have h := SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (CliffordAlgebra.ι_mem_evenOdd_one Q4 (e4 3)) x.2)
        (CliffordAlgebra.ι_mem_evenOdd_one Q4 (e4 3))
      exact (show (1 + 1 : ZMod 2) = 0 by decide) ▸ h⟩
  map_one' := by
    apply Subtype.ext
    -- Expose the even-subalgebra coercions in the ambient Clifford algebra.
    change CliffordAlgebra.ι Q4 (e4 3) * 1 * CliffordAlgebra.ι Q4 (e4 3) = 1
    simpa only [mul_one] using e4_three_sq
  map_mul' x y := by
    apply Subtype.ext
    -- Expose multiplication through the even-subalgebra coercion.
    change CliffordAlgebra.ι Q4 (e4 3) * (x * y) * CliffordAlgebra.ι Q4 (e4 3) =
      (CliffordAlgebra.ι Q4 (e4 3) * x * CliffordAlgebra.ι Q4 (e4 3)) *
        (CliffordAlgebra.ι Q4 (e4 3) * y * CliffordAlgebra.ι Q4 (e4 3))
    -- Reassociate so that the square of the reference vector can be simplified.
    rw [show (CliffordAlgebra.ι Q4 (e4 3) * x * CliffordAlgebra.ι Q4 (e4 3)) *
          (CliffordAlgebra.ι Q4 (e4 3) * y * CliffordAlgebra.ι Q4 (e4 3)) =
        CliffordAlgebra.ι Q4 (e4 3) * x *
          (CliffordAlgebra.ι Q4 (e4 3) * CliffordAlgebra.ι Q4 (e4 3)) * y *
            CliffordAlgebra.ι Q4 (e4 3) by noncomm_ring, e4_three_sq]
    simp only [mul_one]
    noncomm_ring
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [mul_add, add_mul]
  commutes' r := by
    apply Subtype.ext
    -- Expose scalar multiplication in the ambient algebra before commuting the scalar.
    change CliffordAlgebra.ι Q4 (e4 3) * algebraMap ℝ (CliffordAlgebra Q4) r *
      CliffordAlgebra.ι Q4 (e4 3) = algebraMap ℝ (CliffordAlgebra Q4) r
    rw [← Algebra.commutes, mul_assoc, e4_three_sq, mul_one]

private theorem coe_referenceConjEven (x : CliffordAlgebra.even Q4) :
    (referenceConjEven x : CliffordAlgebra Q4) =
      CliffordAlgebra.ι Q4 (e4 3) * x * CliffordAlgebra.ι Q4 (e4 3) :=
  rfl

private noncomputable def swapQuaternionKConj : ℍ[ℝ] × ℍ[ℝ] →ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] where
  toFun q := (quaternionKConj q.2, quaternionKConj q.1)
  map_one' := by ext <;> simp
  map_mul' q r := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' q r := by ext <;> simp
  commutes' r := by ext <;> simp [quaternionKConj_apply]

private theorem referenceConjEven_bilin (m n : Fin 4 → ℝ) :
    referenceConjEven ((CliffordAlgebra.even.ι Q4).bilin m n) =
      (CliffordAlgebra.even.ι Q4).bilin (e4 3) m *
        (CliffordAlgebra.even.ι Q4).bilin n (e4 3) := by
  apply Subtype.ext
  -- Expose both even bilinear products in the ambient Clifford algebra.
  change CliffordAlgebra.ι Q4 (e4 3) *
      (CliffordAlgebra.ι Q4 m * CliffordAlgebra.ι Q4 n) *
        CliffordAlgebra.ι Q4 (e4 3) =
    (CliffordAlgebra.ι Q4 (e4 3) * CliffordAlgebra.ι Q4 m) *
      (CliffordAlgebra.ι Q4 n * CliffordAlgebra.ι Q4 (e4 3))
  noncomm_ring

private theorem map_referenceConjEven (x : CliffordAlgebra.even Q4) :
    realCliffordFourZeroEvenEquivQuaternionProd (referenceConjEven x) =
      swapQuaternionKConj (realCliffordFourZeroEvenEquivQuaternionProd x) := by
  have h :
      realCliffordFourZeroEvenEquivQuaternionProd.toAlgHom.comp referenceConjEven =
        swapQuaternionKConj.comp realCliffordFourZeroEvenEquivQuaternionProd.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    apply CliffordAlgebra.EvenHom.ext
    apply LinearMap.ext₂
    intro m n
    -- Expose evaluation of the two composed homomorphisms on a bilinear generator.
    change realCliffordFourZeroEvenEquivQuaternionProd
        (referenceConjEven ((CliffordAlgebra.even.ι Q4).bilin m n)) =
      swapQuaternionKConj (realCliffordFourZeroEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι Q4).bilin m n))
    rw [referenceConjEven_bilin, map_mul,
      realCliffordFourZeroEvenEquivQuaternionProd_ι,
      realCliffordFourZeroEvenEquivQuaternionProd_ι,
      realCliffordFourZeroEvenEquivQuaternionProd_ι]
    apply Prod.ext <;> ext <;>
      simp [swapQuaternionKConj, quaternionKConj_apply, e4, Pi.basisFun_apply,
        QuaternionAlgebra.mk_mul_mk] <;> ring
  exact DFunLike.congr_fun h x

private theorem quaternionKConj_star_mul_k (q : ℍ[ℝ]) :
    quaternionKConj (star q) * (_root_.QuaternionAlgebra.Basis.self ℝ).k =
      (_root_.QuaternionAlgebra.Basis.self ℝ).k * star q := by
  ext <;> simp [quaternionKConj_apply, QuaternionAlgebra.mk_mul_mk]

private theorem coe_vectorEven4 (v : Fin 4 → ℝ) :
    (vectorEven4 v : CliffordAlgebra Q4) =
      CliffordAlgebra.ι Q4 v * CliffordAlgebra.ι Q4 (e4 3) :=
  rfl

private theorem vectorEven4_spin_action (s : spinGroup Q4) (v : Fin 4 → ℝ) :
    vectorEven4 (s • v) =
      CliffordAlgebra.evenUnitaryGroupEvenPart Q4
          (CliffordAlgebra.spinGroupToEvenUnitary Q4 s) *
        vectorEven4 v *
          referenceConjEven
            (CliffordAlgebra.reverseEven Q4
              (CliffordAlgebra.evenUnitaryGroupEvenPart Q4
                (CliffordAlgebra.spinGroupToEvenUnitary Q4 s))) := by
  apply Subtype.ext
  rw [coe_vectorEven4, CliffordAlgebra.spinGroup_smul_apply,
    CliffordAlgebra.ι_spinVectorAction_apply]
  simp only [Subalgebra.coe_mul, coe_vectorEven4]
  rw [coe_referenceConjEven, CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_reverseEven_apply,
    CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
    CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
  -- Expose every even-part coercion in the ambient Clifford algebra.
  change (s : CliffordAlgebra Q4) * CliffordAlgebra.ι Q4 v *
      star (s : CliffordAlgebra Q4) * CliffordAlgebra.ι Q4 (e4 3) =
    (s : CliffordAlgebra Q4) *
      (CliffordAlgebra.ι Q4 v * CliffordAlgebra.ι Q4 (e4 3)) *
        (CliffordAlgebra.ι Q4 (e4 3) *
          CliffordAlgebra.reverse (s : CliffordAlgebra Q4) *
            CliffordAlgebra.ι Q4 (e4 3))
  rw [CliffordAlgebra.reverse_eq_star_of_mem_even
    ⟨(s : CliffordAlgebra Q4), spinGroup.mem_even s.2⟩]
  -- Reassociate twice to isolate and cancel the square of the reference vector.
  rw [show (s : CliffordAlgebra Q4) * CliffordAlgebra.ι Q4 v *
          star (s : CliffordAlgebra Q4) * CliffordAlgebra.ι Q4 (e4 3) =
        (s : CliffordAlgebra Q4) *
          (CliffordAlgebra.ι Q4 v * CliffordAlgebra.ι Q4 (e4 3)) *
            (CliffordAlgebra.ι Q4 (e4 3) * star (s : CliffordAlgebra Q4) *
              CliffordAlgebra.ι Q4 (e4 3)) by
      rw [show (s : CliffordAlgebra Q4) *
              (CliffordAlgebra.ι Q4 v * CliffordAlgebra.ι Q4 (e4 3)) *
                (CliffordAlgebra.ι Q4 (e4 3) * star (s : CliffordAlgebra Q4) *
                  CliffordAlgebra.ι Q4 (e4 3)) =
            (s : CliffordAlgebra Q4) * CliffordAlgebra.ι Q4 v *
              (CliffordAlgebra.ι Q4 (e4 3) * CliffordAlgebra.ι Q4 (e4 3)) *
                star (s : CliffordAlgebra Q4) * CliffordAlgebra.ι Q4 (e4 3) by
          noncomm_ring, e4_three_sq]
      simp only [mul_one]]

/-- Under the compact real four-dimensional Spin equivalence and the quaternion
isometry, the vector action is left multiplication by the first unit quaternion and inverse right
multiplication by the second. -/
theorem realSpinFourEquivQuaternionUnitaryProd_action
    (s : spinGroup (realCliffordForm 4 0)) (v : Fin 4 → ℝ) :
    realCliffordFourZeroQuaternionEquiv (s • v) =
      (realSpinFourEquivQuaternionUnitaryProd s).1 *
        realCliffordFourZeroQuaternionEquiv v *
          star (realSpinFourEquivQuaternionUnitaryProd s).2 := by
  rw [← map_vectorEven4, vectorEven4_spin_action, map_mul, map_mul,
    map_referenceConjEven, realCliffordFourZeroEvenEquivQuaternionProd_reverseEven,
    ← coe_realSpinFourEquivQuaternionUnitaryProd_apply]
  -- Expose the two quaternion components and the reference-vector coordinate factor.
  change ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) *
        (realCliffordFourZeroEvenEquivQuaternionProd (vectorEven4 v)).1 *
          quaternionKConj (star ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) *
            (_root_.QuaternionAlgebra.Basis.self ℝ).k =
      ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) *
        realCliffordFourZeroQuaternionEquiv v *
          star ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])
  -- Reassociate to apply the identity moving quaternion `k` past the conjugated factor.
  rw [show ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) *
          (realCliffordFourZeroEvenEquivQuaternionProd (vectorEven4 v)).1 *
            quaternionKConj
              (star ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) *
              (_root_.QuaternionAlgebra.Basis.self ℝ).k =
        ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) *
          (realCliffordFourZeroEvenEquivQuaternionProd (vectorEven4 v)).1 *
            (quaternionKConj
              (star ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) *
              (_root_.QuaternionAlgebra.Basis.self ℝ).k) by noncomm_ring,
    quaternionKConj_star_mul_k]
  -- Reassociate once more to expose the vector-to-quaternion coordinate equation.
  rw [show ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) *
          (realCliffordFourZeroEvenEquivQuaternionProd (vectorEven4 v)).1 *
            ((_root_.QuaternionAlgebra.Basis.self ℝ).k *
              star ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) =
        ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) *
          ((realCliffordFourZeroEvenEquivQuaternionProd (vectorEven4 v)).1 *
            (_root_.QuaternionAlgebra.Basis.self ℝ).k) *
              star ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ]) by
      noncomm_ring, map_vectorEven4]

/-- The compact real form of the exceptional isomorphism in dimension four:
`Spin(4) ≃ SU(2) × SU(2)`. -/
noncomputable def realSpinFourEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourEquivQuaternionUnitaryProd.trans
    (Quaternion.unitaryEquivSpecialUnitaryGroup.prodCongr
      Quaternion.unitaryEquivSpecialUnitaryGroup)

/-- The two matrices underlying the compact `Spin(4) ≃ SU(2) × SU(2)` equivalence are the complex
matrix models of its two quaternion components. -/
@[simp]
theorem coe_realSpinFourEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    (((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ),
        ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).1,
        Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).2) := by
  apply Prod.ext
  · exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply _
  · exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply _

/-- The `Spin(4)` element underlying a pair of special unitary matrices has the expected pair of
unit quaternions. -/
theorem toComplexMatrix_coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ ×
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (Quaternion.toComplexMatrix
        ((realSpinFourEquivQuaternionUnitaryProd
          (realSpinFourEquivSpecialUnitaryProd.symm M)).1 : ℍ[ℝ]),
      Quaternion.toComplexMatrix
        ((realSpinFourEquivQuaternionUnitaryProd
          (realSpinFourEquivSpecialUnitaryProd.symm M)).2 : ℍ[ℝ])) =
      ((M.1 : Matrix (Fin 2) (Fin 2) ℂ),
        (M.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [← coe_realSpinFourEquivSpecialUnitaryProd_apply]
  exact congrArg (fun p : Matrix.specialUnitaryGroup (Fin 2) ℂ ×
    Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      ((p.1 : Matrix (Fin 2) (Fin 2) ℂ),
        (p.2 : Matrix (Fin 2) (Fin 2) ℂ)))
    (realSpinFourEquivSpecialUnitaryProd.apply_symm_apply M)

/-- In the compact `Spin(4)` quaternion-pair model, the central element `-1` has coordinates
`(-1, -1)`. -/
@[simp]
theorem realSpinFourEquivQuaternionUnitaryProd_negOne :
    realSpinFourEquivQuaternionUnitaryProd
        (CliffordAlgebra.spinGroup.negOne (realCliffordForm 4 0)
          (nondegenerate_realCliffordForm 4 0).ne_zero) = (-1, -1) := by
  rw [← realSpinFourEquivQuaternionUnitaryProd.eq_symm_apply]
  apply Subtype.ext
  rw [coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply,
    CliffordAlgebra.spinGroup.coe_negOne]
  -- Expose the product negation in `ℍ[ℝ] × ℍ[ℝ]` before applying `map_neg` and `map_one`.
  change (-1 : CliffordAlgebra (realCliffordForm 4 0)) =
    (realCliffordFourZeroEvenEquivQuaternionProd.symm (-1) :
      CliffordAlgebra (realCliffordForm 4 0))
  rw [map_neg, map_one, Subalgebra.coe_neg, Subalgebra.coe_one]

/-! ### Calibrated `(1, i, j, k)` `Spin(4)` model -/

/-- The even unitary carrier of `Cl(4,0)` identified with `unitary ℍ[ℝ] × unitary ℍ[ℝ]` via the
calibrated `(1, i, j, k)` even Clifford-algebra equivalence. -/
noncomputable def realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0) ≃*
      unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  (CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv
    (realCliffordForm 4 0) realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven).trans
      (Unitary.prodEquiv ℍ[ℝ] ℍ[ℝ])

/-- The quaternion pair underlying
`realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd` is obtained by applying
`realCliffordFourZeroCalibratedEvenEquivQuaternionProd` to the even part. -/
@[simp]
theorem coe_realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd_apply
    (x : CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0)) :
    (((realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd x).1 : ℍ[ℝ]),
        ((realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd x).2 : ℍ[ℝ])) =
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0) x) := by
  rw [realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    Unitary.coe_prodEquiv_apply]
  exact CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply
    (realCliffordForm 4 0) realCliffordFourZeroCalibratedEvenEquivQuaternionProd
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven x

/-- The inverse calibrated even-unitary equivalence recovers the Clifford value via
`realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm`. -/
@[simp]
theorem coe_realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    ((((realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra.evenUnitaryGroup (realCliffordForm 4 0)) :
          (CliffordAlgebra (realCliffordForm 4 0))ˣ) :
            CliffordAlgebra (realCliffordForm 4 0))) =
      (realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm
          ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra.even (realCliffordForm 4 0)) := by
  rw [realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd,
    MulEquiv.symm_trans_apply]
  refine (CliffordAlgebra.coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_symm_apply
    (realCliffordForm 4 0) realCliffordFourZeroCalibratedEvenEquivQuaternionProd
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven
      ((Unitary.prodEquiv ℍ[ℝ] ℍ[ℝ]).symm q)).trans ?_
  exact congrArg (fun p : ℍ[ℝ] × ℍ[ℝ] =>
    (realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm p :
      CliffordAlgebra (realCliffordForm 4 0)))
    (Unitary.coe_prodEquiv_symm_apply ℍ[ℝ] ℍ[ℝ] q)

/-- **Calibrated compact `Spin(4) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` equivalence**, aligned with the
standard ordered `(1, i, j, k)` quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  (CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour
    (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp) (by simp)).trans
    realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd

/-- `realSpinFourCalibratedEquivQuaternionUnitaryProd` evaluates
`realCliffordFourZeroCalibratedEvenEquivQuaternionProd` on the underlying even Clifford element. -/
@[simp]
theorem coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    (((realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
        ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) =
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) := by
  rw [realSpinFourCalibratedEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_realCliffordFourZeroCalibratedEvenUnitaryEquivQuaternionUnitaryProd_apply _

/-- `realSpinFourCalibratedEquivQuaternionUnitaryProd.symm` recovers the Clifford value from
`realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm`. -/
@[simp]
theorem coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    (realSpinFourCalibratedEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra (realCliffordForm 4 0)) =
      (realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm
          ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra (realCliffordForm 4 0)) := by
  let s := realSpinFourCalibratedEquivQuaternionUnitaryProd.symm q
  have hs :
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd
          (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
            (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) =
        ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) := by
    rw [← coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply]
    exact congrArg (fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      ((p.1 : ℍ[ℝ]), (p.2 : ℍ[ℝ])))
        (realSpinFourCalibratedEquivQuaternionUnitaryProd.apply_symm_apply q)
  have h := congrArg
    (fun x : CliffordAlgebra.even (realCliffordForm 4 0) =>
      (x : CliffordAlgebra (realCliffordForm 4 0)))
    ((realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

/-- The calibrated `Spin(4)` unit-quaternion factors are obtained from the native ones by swapping
the two factors and conjugating by `realCliffordFourZeroCalibrationUnitary` and its inverse. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_eq
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedEquivQuaternionUnitaryProd s =
      (MulAut.conj realCliffordFourZeroCalibrationUnitary
          (realSpinFourEquivQuaternionUnitaryProd s).2,
        (MulAut.conj realCliffordFourZeroCalibrationUnitary).symm
          (realSpinFourEquivQuaternionUnitaryProd s).1) := by
  have hpair :
      (((realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
          ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) =
        realCliffordFourZeroQuaternionProdCalibrationEquiv
          (((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
            ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) := by
    rw [coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_eq_calibrationEquiv,
      ← coe_realSpinFourEquivQuaternionUnitaryProd_apply]
  apply Prod.ext <;> apply Subtype.ext
  · refine (congrArg Prod.fst hpair).trans ?_
    simp only [realCliffordFourZeroQuaternionProdCalibrationEquiv_apply, MulAut.conj_apply,
      Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
  · refine (congrArg Prod.snd hpair).trans ?_
    simp only [realCliffordFourZeroQuaternionProdCalibrationEquiv_apply, MulAut.conj_symm_apply,
      Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]

/-- In the calibrated `Spin(4)` quaternion-pair model, the central element `-1` has coordinates
`(-1, -1)`. -/
@[simp]
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_negOne :
    realSpinFourCalibratedEquivQuaternionUnitaryProd
        (CliffordAlgebra.spinGroup.negOne (realCliffordForm 4 0)
          (nondegenerate_realCliffordForm 4 0).ne_zero) = (-1, -1) := by
  simp [realSpinFourCalibratedEquivQuaternionUnitaryProd_eq]

/-- **Calibrated `Spin(4)` vector action**: under
`realSpinFourCalibratedEquivQuaternionUnitaryProd` and the standard `(1, i, j, k)` quaternion
isometry `realCliffordFourZeroCalibratedQuaternionEquiv`, a Spin element `(q_L, q_R)` acts on
`v ∈ ℝ⁴` by `v ↦ q_L * v * star q_R`. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_action
    (s : spinGroup (realCliffordForm 4 0)) (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv (s • v) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 *
        realCliffordFourZeroCalibratedQuaternionEquiv v *
          star (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  let u : ℍ[ℝ] := (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ])
  let n₁ : ℍ[ℝ] := ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ])
  let n₂ : ℍ[ℝ] := ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])
  let w : ℍ[ℝ] := realCliffordFourZeroQuaternionEquiv v
  have hu₁ : star u * u = 1 :=
    Unitary.star_mul_self_of_mem realCliffordFourZeroCalibrationUnitary.2
  have hu₂ : u * star u = 1 :=
    Unitary.mul_star_self_of_mem realCliffordFourZeroCalibrationUnitary.2
  have hq₁ : ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) =
      u * n₂ * star u := by
    rw [realSpinFourCalibratedEquivQuaternionUnitaryProd_eq]
    simp only [MulAut.conj_apply, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
    rfl
  have hq₂ : star ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 : ℍ[ℝ]) =
      star u * star n₁ * u := by
    rw [realSpinFourCalibratedEquivQuaternionUnitaryProd_eq]
    simp only [MulAut.conj_symm_apply, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star,
      star_mul, star_star]
    simp only [mul_assoc]
    rfl
  rw [realCliffordFourZeroCalibratedQuaternionEquiv_eq_calibrationUnitary,
    realSpinFourEquivQuaternionUnitaryProd_action,
    realCliffordFourZeroCalibratedQuaternionEquiv_eq_calibrationUnitary,
    Unitary.coe_star, Unitary.coe_star, hq₁, hq₂]
  have hstar : star (n₁ * w * star n₂) = n₂ * star w * star n₁ := by
    simp [mul_assoc]
  -- Fold the `let`-abbreviations `u`, `n₁`, `n₂`, `w` in the target equation.
  change -(u * star (n₁ * w * star n₂) * u) =
    u * n₂ * star u * -(u * star w * u) * (star u * star n₁ * u)
  rw [hstar]
  calc
    -(u * (n₂ * star w * star n₁) * u)
      = -((u * n₂ * (star u * u)) * star w * ((u * star u) * star n₁ * u)) := by
          rw [hu₁, hu₂]
          simp [mul_assoc]
    _ = u * n₂ * star u * -(u * star w * u) * (star u * star n₁ * u) := by
          simp [mul_assoc]

/-- Under `realSpinFourCalibratedEquivQuaternionUnitaryProd` and
`realCliffordFourZeroCalibratedQuaternionEquiv`, the Spin double-cover projection
`spinToSpecialOrthogonal` acts on `v ∈ ℝ⁴` by `v ↦ q_L * v * star q_R`. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_spinToSpecialOrthogonal
    (s : spinGroup (realCliffordForm 4 0)) (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv
        ((CliffordAlgebra.spinToSpecialOrthogonal (realCliffordForm 4 0) s :
          (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) v) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 *
        realCliffordFourZeroCalibratedQuaternionEquiv v *
          star (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  rw [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply, ← CliffordAlgebra.spinGroup_smul_apply,
    realSpinFourCalibratedEquivQuaternionUnitaryProd_action]

/-- Multiplying a vector `v ∈ ℝ⁴` on the right by the reference basis vector `e₀` embeds `v` into
`Cl⁺(4,0)` with calibrated quaternion-pair coordinates `(φ v, star (φ v))`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_right
    (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin v (Pi.single 0 1)) =
      (realCliffordFourZeroCalibratedQuaternionEquiv v,
        star (realCliffordFourZeroCalibratedQuaternionEquiv v)) := by
  have he₀ : realCliffordFourZeroCalibratedQuaternionEquiv (Pi.single 0 1) = 1 := by
    ext <;> simp
  rw [realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι, he₀, star_one, mul_one, mul_one]

/-- Multiplying a vector `v ∈ ℝ⁴` on the left by the reference basis vector `e₀` embeds `v` into
`Cl⁺(4,0)` with calibrated quaternion-pair coordinates `(star (φ v), φ v)`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_left
    (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) v) =
      (star (realCliffordFourZeroCalibratedQuaternionEquiv v),
        realCliffordFourZeroCalibratedQuaternionEquiv v) := by
  have he₀ : realCliffordFourZeroCalibratedQuaternionEquiv (Pi.single 0 1) = 1 := by
    ext <;> simp
  rw [realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι, he₀, star_one, one_mul, one_mul]

/-- **Calibrated compact `Spin(4) ≃* SU(2) × SU(2)` equivalence**, aligned with the `(1, i, j, k)`
quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourCalibratedEquivQuaternionUnitaryProd.trans
    (Quaternion.unitaryEquivSpecialUnitaryGroup.prodCongr
      Quaternion.unitaryEquivSpecialUnitaryGroup)

/-- The two matrices underlying `realSpinFourCalibratedEquivSpecialUnitaryProd` are the complex
matrix models of its two calibrated unit-quaternion components. -/
@[simp]
theorem coe_realSpinFourCalibratedEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    (((realSpinFourCalibratedEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ),
        ((realSpinFourCalibratedEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Quaternion.toComplexMatrix (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1,
        Quaternion.toComplexMatrix (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2) := by
  apply Prod.ext
  · exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply _
  · exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply _

/-! ### Compatibility with first-coordinate stabilization and reflection -/

private theorem inv_sqrt_two_mul_self' :
    (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
  rw [← sq, inv_pow, Real.sq_sqrt (by norm_num)]

/-- The unit quaternion `(1 + k) / √2` aligning `realSpinThreeEquivQuaternionUnitary` with the
diagonal subgroup of `realSpinFourCalibratedEquivQuaternionUnitaryProd` under first-coordinate
stabilization `v ↦ Fin.cons 0 v`. -/
noncomputable def realSpinThreeToFourCalibrationUnitary : unitary ℍ[ℝ] :=
  ⟨⟨(Real.sqrt 2)⁻¹, 0, 0, (Real.sqrt 2)⁻¹⟩, by
    rw [Quaternion.mem_unitary_iff_normSq_eq_one, Quaternion.normSq_def']
    simp only [sq, inv_sqrt_two_mul_self']
    norm_num⟩

/-- The underlying quaternion of `realSpinThreeToFourCalibrationUnitary` is `(1 + k) / √2`. -/
@[simp]
theorem coe_realSpinThreeToFourCalibrationUnitary :
    (realSpinThreeToFourCalibrationUnitary : ℍ[ℝ]) =
      ⟨(Real.sqrt 2)⁻¹, 0, 0, (Real.sqrt 2)⁻¹⟩ :=
  (rfl)

private noncomputable def firstInclusionEvenAlgHom :
    CliffordAlgebra.even (realCliffordForm 3 0) →ₐ[ℝ]
      CliffordAlgebra.even (realCliffordForm 4 0) where
  toFun x :=
    ⟨CliffordAlgebra.map (realCliffordSpinFirstInclusionIsometry 3) x,
      CliffordAlgebra.map_mem_even _ x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' _ _ := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' _ _ := by apply Subtype.ext; simp
  commutes' _ := by apply Subtype.ext; simp

/-- Under `realCliffordFourZeroCalibratedEvenEquivQuaternionProd`, first-coordinate inclusion
`v ↦ Fin.cons 0 v` embeds `Cl⁺(3,0) ≃ ℍ` diagonally into `Cl⁺(4,0) ≃ ℍ × ℍ` after conjugating by
`realSpinThreeToFourCalibrationUnitary`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstInclusion
    (x : CliffordAlgebra.even (realCliffordForm 3 0)) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ⟨CliffordAlgebra.map (realCliffordSpinFirstInclusionIsometry 3) x,
          CliffordAlgebra.map_mem_even _ x.2⟩ =
      (Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
          (realCliffordThreeZeroEvenEquivQuaternion x),
        Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
          (realCliffordThreeZeroEvenEquivQuaternion x)) := by
  let c :=
    (Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary).toAlgEquiv.toAlgHom
  have h :
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd.toAlgHom.comp firstInclusionEvenAlgHom =
        (c.prod c).comp realCliffordThreeZeroEvenEquivQuaternion.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    apply CliffordAlgebra.EvenHom.ext
    apply LinearMap.ext₂
    intro m n
    have hbilin :
        firstInclusionEvenAlgHom ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n) =
          (CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin
            (Fin.cons 0 m) (Fin.cons 0 n) := by
      apply Subtype.ext
      simp [firstInclusionEvenAlgHom, CliffordAlgebra.even.ι]
    have hcons (u : Fin 3 → ℝ) :
        realCliffordFourZeroCalibratedQuaternionEquiv (Fin.cons 0 u) = ⟨0, u 0, u 1, u 2⟩ := by
      rw [realCliffordFourZeroCalibratedQuaternionEquiv_apply]
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
      · simp
      · simp
      · simpa using Fin.cons_succ (α := fun _ ↦ ℝ) 0 u 1
      · simpa using Fin.cons_succ (α := fun _ ↦ ℝ) 0 u 2
    -- Expose evaluation of both composed algebra homomorphisms on a bilinear generator.
    change realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (firstInclusionEvenAlgHom ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n)) =
      (Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
          (realCliffordThreeZeroEvenEquivQuaternion
            ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n)),
        Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
          (realCliffordThreeZeroEvenEquivQuaternion
            ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin m n)))
    rw [hbilin, realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι, hcons, hcons,
      realCliffordThreeZeroEvenEquivQuaternion_ι]
    apply Prod.ext <;> ext <;>
      simp only [Unitary.conjStarAlgAut_apply, coe_realSpinThreeToFourCalibrationUnitary,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk] <;>
      ring_nf <;>
      simp only [sq, inv_sqrt_two_mul_self'] <;>
      ring
  simpa [firstInclusionEvenAlgHom, c] using DFunLike.congr_fun h x

/-- **First-coordinate Spin stabilization `Spin(3) →* Spin(4)` is diagonal in the calibrated
quaternion-pair model**, up to inner conjugation by `realSpinThreeToFourCalibrationUnitary` on
`unitary ℍ[ℝ]`. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion
    (s : spinGroup (realCliffordForm 3 0)) :
    realSpinFourCalibratedEquivQuaternionUnitaryProd (realCliffordSpinFirstInclusion 3 s) =
      (MulAut.conj realSpinThreeToFourCalibrationUnitary
          (realSpinThreeEquivQuaternionUnitary s),
        MulAut.conj realSpinThreeToFourCalibrationUnitary
          (realSpinThreeEquivQuaternionUnitary s)) := by
  let x := CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
    (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)
  have heven :
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0)
            (realCliffordSpinFirstInclusion 3 s)) =
        ⟨CliffordAlgebra.map (realCliffordSpinFirstInclusionIsometry 3) x,
          CliffordAlgebra.map_mem_even _ x.2⟩ := by
    apply Subtype.ext
    simp only [x, CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply,
      CliffordAlgebra.coe_spinGroupToEven_apply, coe_realCliffordSpinFirstInclusion_apply]
  have hpair :
      (((realSpinFourCalibratedEquivQuaternionUnitaryProd
          (realCliffordSpinFirstInclusion 3 s)).1 : ℍ[ℝ]),
        ((realSpinFourCalibratedEquivQuaternionUnitaryProd
          (realCliffordSpinFirstInclusion 3 s)).2 : ℍ[ℝ])) =
        (Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
            (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ]),
          Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
            (realSpinThreeEquivQuaternionUnitary s : ℍ[ℝ])) := by
    rw [coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply, heven,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstInclusion,
      ← coe_realSpinThreeEquivQuaternionUnitary_apply]
  apply Prod.ext <;> apply Subtype.ext
  · refine (congrArg Prod.fst hpair).trans ?_
    simp only [Unitary.conjStarAlgAut_apply, MulAut.conj_apply, Submonoid.coe_mul,
      ← Unitary.star_eq_inv, Unitary.coe_star]
  · refine (congrArg Prod.snd hpair).trans ?_
    simp only [Unitary.conjStarAlgAut_apply, MulAut.conj_apply, Submonoid.coe_mul,
      ← Unitary.star_eq_inv, Unitary.coe_star]

/-- An element of `Spin(4)` lies in the image of first-coordinate stabilization
`Spin(3) →* Spin(4)` if and only if its two unit-quaternion coordinates in the calibrated model
coincide. -/
theorem mem_range_realCliffordSpinFirstInclusion_three_iff
    (s : spinGroup (realCliffordForm 4 0)) :
    s ∈ Set.range (realCliffordSpinFirstInclusion 3) ↔
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 =
        (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion]
  · intro hs
    let q := (MulAut.conj realSpinThreeToFourCalibrationUnitary).symm
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1
    refine ⟨realSpinThreeEquivQuaternionUnitary.symm q, ?_⟩
    apply realSpinFourCalibratedEquivQuaternionUnitaryProd.injective
    rw [realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion,
      realSpinThreeEquivQuaternionUnitary.apply_symm_apply,
      (MulAut.conj realSpinThreeToFourCalibrationUnitary).apply_symm_apply]
    nth_rw 2 [hs]

/-- First-coordinate reflection `v ↦ Fin.cons (-v 0) (Fin.tail v)` on `ℝ⁴` corresponds to `-star`
in the standard `(1, i, j, k)` quaternion model. -/
theorem realCliffordFourZeroCalibratedQuaternionEquiv_firstReflection (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv (realCliffordFirstReflectionIsometry 3 v) =
      -star (realCliffordFourZeroCalibratedQuaternionEquiv v) := by
  rw [realCliffordFirstReflectionIsometry_apply,
    realCliffordFourZeroCalibratedQuaternionEquiv_apply,
    realCliffordFourZeroCalibratedQuaternionEquiv_apply]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · simp
  · simp [Fin.tail_def]
  · simpa [Fin.tail_def] using Fin.cons_succ (-v 0) (Fin.tail v) 1
  · simpa [Fin.tail_def] using Fin.cons_succ (-v 0) (Fin.tail v) 2

/-- In the calibrated `Cl⁺(4,0) ≃ ℍ × ℍ` model, the algebra automorphism induced by
first-coordinate reflection swaps the two quaternion factors. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstReflection
    (x : CliffordAlgebra.even (realCliffordForm 4 0)) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenEquivOfIsometry (realCliffordFirstReflectionIsometry 3) x) =
      Prod.swap (realCliffordFourZeroCalibratedEvenEquivQuaternionProd x) := by
  let swapAlgHom : ℍ[ℝ] × ℍ[ℝ] →ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
    (AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ])
  have h :
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd.toAlgHom.comp
          (CliffordAlgebra.evenEquivOfIsometry (realCliffordFirstReflectionIsometry 3)).toAlgHom =
        swapAlgHom.comp realCliffordFourZeroCalibratedEvenEquivQuaternionProd.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    apply CliffordAlgebra.EvenHom.ext
    apply LinearMap.ext₂
    intro m n
    -- Expose evaluation of the composed algebra homomorphisms on a bilinear generator.
    change realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenEquivOfIsometry (realCliffordFirstReflectionIsometry 3)
          ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin m n)) =
      Prod.swap (realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin m n))
    rw [CliffordAlgebra.evenEquivOfIsometry_ι,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι,
      realCliffordFourZeroCalibratedQuaternionEquiv_firstReflection,
      realCliffordFourZeroCalibratedQuaternionEquiv_firstReflection]
    simp
  exact DFunLike.congr_fun h x

-- Not `@[simp]`: `QuadraticMap.IsometryEquiv.spinGroupEquiv_apply` rewrites `.spinGroupEquiv` to
-- `.toIsometry.spinGroupMap`; see
-- `realSpinFourCalibratedEquivQuaternionUnitaryProd_spinGroupMap_firstReflection`.
/-- **First-coordinate reflection swaps the two `Spin(4)` factors** in the calibrated
unit-quaternion product model. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedEquivQuaternionUnitaryProd
        ((realCliffordFirstReflectionIsometry 3).spinGroupEquiv s) =
      Prod.swap (realSpinFourCalibratedEquivQuaternionUnitaryProd s) := by
  let x := CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
    (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)
  have heven :
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0)
            ((realCliffordFirstReflectionIsometry 3).spinGroupEquiv s)) =
        CliffordAlgebra.evenEquivOfIsometry (realCliffordFirstReflectionIsometry 3) x := by
    apply Subtype.ext
    simp only [x, CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply,
      CliffordAlgebra.coe_spinGroupToEven_apply, CliffordAlgebra.coe_evenEquivOfIsometry_apply,
      CliffordAlgebra.equivOfIsometry_apply, QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
      QuadraticMap.Isometry.coe_spinGroupMap_apply]
  have hpair :
      (((realSpinFourCalibratedEquivQuaternionUnitaryProd
          ((realCliffordFirstReflectionIsometry 3).spinGroupEquiv s)).1 : ℍ[ℝ]),
        ((realSpinFourCalibratedEquivQuaternionUnitaryProd
          ((realCliffordFirstReflectionIsometry 3).spinGroupEquiv s)).2 : ℍ[ℝ])) =
        Prod.swap
          (((realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
            ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) := by
    rw [coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply, heven,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstReflection,
      ← coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply]
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

/-- Simp-normal form of `realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection` on
`spinGroupMap`. -/
@[simp]
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_spinGroupMap_firstReflection
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedEquivQuaternionUnitaryProd
        ((realCliffordFirstReflectionIsometry 3).toIsometry.spinGroupMap s) =
      Prod.swap (realSpinFourCalibratedEquivQuaternionUnitaryProd s) := by
  rw [← QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
    realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection]

end TauCeti

end
