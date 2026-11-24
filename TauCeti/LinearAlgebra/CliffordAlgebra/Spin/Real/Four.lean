/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Algebra.Star.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.QuaternionProduct
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

In addition to the native coordinate model, this file provides the calibrated `(1, i, j, k)` model
`TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd`, under which `(q_L, q_R)` acts on
`v ∈ ℝ⁴ ≃ ℍ` by `v ↦ q_L * v * star q_R`, first-coordinate stabilization `Spin(3) →* Spin(4)` maps
onto the diagonal subgroup `q_L = q_R` up to conjugation by `(1 + k) / √2`, and first-coordinate
reflection (`TauCeti.realCliffordCoordReflection 0`) swaps the two unit-quaternion factors.

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
  `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd_action`,
  `TauCeti.realSpinFourCalibratedEquivSpecialUnitaryProd`,
  `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion`, and
  `TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection`: calibrated
  `(1, i, j, k)` models, vector action, stabilization, and reflection swap.

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
        (SetLike.mul_mem_graded (CliffordAlgebra.ι_mem_evenOdd_one Q4 (e4 3)) x.property)
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
    ⟨(s : CliffordAlgebra Q4), spinGroup.mem_even s.property⟩]
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

/-- `realSpinFourEquivSpecialUnitaryProd` factors through `realSpinFourEquivQuaternionUnitaryProd`
and `Quaternion.unitaryEquivSpecialUnitaryGroup`. -/
theorem realSpinFourEquivSpecialUnitaryProd_eq :
    realSpinFourEquivSpecialUnitaryProd =
      realSpinFourEquivQuaternionUnitaryProd.trans
        (Quaternion.unitaryEquivSpecialUnitaryGroup.prodCongr
          Quaternion.unitaryEquivSpecialUnitaryGroup) := (rfl)

/-- `realSpinFourEquivQuaternionUnitaryProd` is an instance of
`CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd`. -/
theorem realSpinFourEquivQuaternionUnitaryProd_eq :
    realSpinFourEquivQuaternionUnitaryProd =
      CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd
        (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp)
        realCliffordFourZeroEvenEquivQuaternionProd
        realCliffordFourZeroEvenEquivQuaternionProd_reverseEven := by
  ext s : 1
  have h := (coe_realSpinFourEquivQuaternionUnitaryProd_apply s).trans
    (CliffordAlgebra.coe_spinGroupEquivQuaternionUnitaryProd_apply
      (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp)
      realCliffordFourZeroEvenEquivQuaternionProd
      realCliffordFourZeroEvenEquivQuaternionProd_reverseEven s).symm
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- In the compact `Spin(4)` quaternion-pair model, the central element `-1` has coordinates
`(-1, -1)`. -/
@[simp]
theorem realSpinFourEquivQuaternionUnitaryProd_negOne :
    realSpinFourEquivQuaternionUnitaryProd
        (CliffordAlgebra.spinGroup.negOne (realCliffordForm 4 0)
          (nondegenerate_realCliffordForm 4 0).ne_zero) = (-1, -1) := by
  rw [realSpinFourEquivQuaternionUnitaryProd_eq]
  exact CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd_negOne
    (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroEvenEquivQuaternionProd
    realCliffordFourZeroEvenEquivQuaternionProd_reverseEven

/-! ### Calibrated `(1, i, j, k)` `Spin(4)` model -/

section Calibrated

variable (s : spinGroup (realCliffordForm 4 0))

/-- **Calibrated compact `Spin(4) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` equivalence**, aligned with the
standard ordered `(1, i, j, k)` quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd (realCliffordForm 4 0)
    (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven

/-- `realSpinFourCalibratedEquivQuaternionUnitaryProd` is an instance of
`CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd`. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_eq :
    realSpinFourCalibratedEquivQuaternionUnitaryProd =
      CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd (realCliffordForm 4 0)
        (nondegenerate_realCliffordForm 4 0) (by simp)
        realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven := (rfl)

/-- `realSpinFourCalibratedEquivQuaternionUnitaryProd` evaluates
`realCliffordFourZeroCalibratedEvenEquivQuaternionProd` on the underlying even Clifford element. -/
theorem coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply :
    (((realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
        ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) =
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) :=
  CliffordAlgebra.coe_spinGroupEquivQuaternionUnitaryProd_apply (realCliffordForm 4 0)
    (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven s

/-- First quaternion coordinate of `realSpinFourCalibratedEquivQuaternionUnitaryProd`. -/
@[simp] theorem coe_fst_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply :
    ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]) =
      (realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s))).1 :=
  congrArg Prod.fst (coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply s)

/-- Second quaternion coordinate of `realSpinFourCalibratedEquivQuaternionUnitaryProd`. -/
@[simp] theorem coe_snd_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply :
    ((realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 : ℍ[ℝ]) =
      (realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s))).2 :=
  congrArg Prod.snd (coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply s)

/-- `realSpinFourCalibratedEquivQuaternionUnitaryProd.symm` recovers the Clifford value from
`realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm`. -/
@[simp] theorem coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    (realSpinFourCalibratedEquivQuaternionUnitaryProd.symm q :
        CliffordAlgebra (realCliffordForm 4 0)) =
      (realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm ((q.1 : ℍ[ℝ]), (q.2 : ℍ[ℝ])) :
        CliffordAlgebra (realCliffordForm 4 0)) :=
  CliffordAlgebra.coe_spinGroupEquivQuaternionUnitaryProd_symm_apply (realCliffordForm 4 0)
    (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven q

/-- Relation between the calibrated and native `Spin(4)` unit-quaternion factors. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_apply :
    realSpinFourCalibratedEquivQuaternionUnitaryProd s =
      (MulAut.conj realCliffordFourZeroCalibrationUnitary
          (realSpinFourEquivQuaternionUnitaryProd s).2,
        (MulAut.conj realCliffordFourZeroCalibrationUnitary).symm
          (realSpinFourEquivQuaternionUnitaryProd s).1) := by
  apply Prod.ext <;> apply Subtype.ext
  · rw [coe_fst_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_eq_calibrationEquiv,
      ← coe_realSpinFourEquivQuaternionUnitaryProd_apply,
      realCliffordFourZeroQuaternionProdCalibrationEquiv_apply, Unitary.coe_conj_apply]
  · rw [coe_snd_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_eq_calibrationEquiv,
      ← coe_realSpinFourEquivQuaternionUnitaryProd_apply,
      realCliffordFourZeroQuaternionProdCalibrationEquiv_apply, Unitary.coe_conj_symm_apply]

/-- In the calibrated `Spin(4)` quaternion-pair model, `-1` has coordinates `(-1, -1)`. -/
@[simp] theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_negOne :
    realSpinFourCalibratedEquivQuaternionUnitaryProd
        (CliffordAlgebra.spinGroup.negOne (realCliffordForm 4 0)
          (nondegenerate_realCliffordForm 4 0).ne_zero) = (-1, -1) :=
  CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd_negOne (realCliffordForm 4 0)
    (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven

/-- **Calibrated `Spin(4)` vector action**: in `(1, i, j, k)` coordinates, `(q_L, q_R)` acts on
`v ∈ ℝ⁴` by `v ↦ q_L * v * star q_R`. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_action (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv (s • v) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 *
        realCliffordFourZeroCalibratedQuaternionEquiv v *
          star (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  rw [realCliffordFourZeroCalibratedQuaternionEquiv_eq_neg_mul_star_mul,
    realSpinFourEquivQuaternionUnitaryProd_action,
    realCliffordFourZeroCalibratedQuaternionEquiv_eq_neg_mul_star_mul,
    realSpinFourCalibratedEquivQuaternionUnitaryProd_apply]
  simp only [Unitary.coe_star, Unitary.coe_conj_apply, Unitary.coe_conj_symm_apply, star_mul,
    star_star]
  set u : ℍ[ℝ] := (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ])
  set n₁ : ℍ[ℝ] := ((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ])
  set n₂ : ℍ[ℝ] := ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])
  set w : ℍ[ℝ] := realCliffordFourZeroQuaternionEquiv v
  have hu₁ := Unitary.star_mul_self_of_mem realCliffordFourZeroCalibrationUnitary.property
  have hu₂ := Unitary.mul_star_self_of_mem realCliffordFourZeroCalibrationUnitary.property
  calc
    -(u * (n₂ * (star w * star n₁)) * u)
      = -((u * n₂ * (star u * u)) * star w * ((u * star u) * star n₁ * u)) := by
          rw [hu₁, hu₂]; simp [mul_assoc]
    _ = u * n₂ * star u * -(u * star w * u) * (star u * (star n₁ * u)) := by simp [mul_assoc]

/-- Under the calibrated `(1, i, j, k)` model, `spinToSpecialOrthogonal` acts on `v ∈ ℝ⁴` by
`v ↦ q_L * v * star q_R`. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_spinToSpecialOrthogonal (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv
        ((CliffordAlgebra.spinToSpecialOrthogonal (realCliffordForm 4 0) s :
          (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) v) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 *
        realCliffordFourZeroCalibratedQuaternionEquiv v *
          star (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  rw [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply, ← CliffordAlgebra.spinGroup_smul_apply,
    realSpinFourCalibratedEquivQuaternionUnitaryProd_action]

/-- **Calibrated compact `Spin(4) ≃* SU(2) × SU(2)` equivalence** in `(1, i, j, k)` coordinates. -/
noncomputable def realSpinFourCalibratedEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourCalibratedEquivQuaternionUnitaryProd.trans
    (Quaternion.unitaryEquivSpecialUnitaryGroup.prodCongr
      Quaternion.unitaryEquivSpecialUnitaryGroup)

/-- Factorization of `realSpinFourCalibratedEquivSpecialUnitaryProd`. -/
theorem realSpinFourCalibratedEquivSpecialUnitaryProd_eq :
    realSpinFourCalibratedEquivSpecialUnitaryProd =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.trans
        (Quaternion.unitaryEquivSpecialUnitaryGroup.prodCongr
          Quaternion.unitaryEquivSpecialUnitaryGroup) := (rfl)

/-- Forward evaluation of `realSpinFourCalibratedEquivSpecialUnitaryProd`. -/
@[simp] theorem realSpinFourCalibratedEquivSpecialUnitaryProd_apply :
    realSpinFourCalibratedEquivSpecialUnitaryProd s =
      (Quaternion.unitaryEquivSpecialUnitaryGroup
          (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1,
        Quaternion.unitaryEquivSpecialUnitaryGroup
          (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2) := (rfl)

/-- Inverse of `realSpinFourCalibratedEquivSpecialUnitaryProd`. -/
@[simp] theorem realSpinFourCalibratedEquivSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    realSpinFourCalibratedEquivSpecialUnitaryProd.symm M =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.symm
        (Quaternion.unitaryEquivSpecialUnitaryGroup.symm M.1,
          Quaternion.unitaryEquivSpecialUnitaryGroup.symm M.2) := (rfl)

/-- Complex matrices underlying `realSpinFourCalibratedEquivSpecialUnitaryProd`. -/
theorem coe_realSpinFourCalibratedEquivSpecialUnitaryProd_apply :
    (((realSpinFourCalibratedEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ),
        ((realSpinFourCalibratedEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Quaternion.toComplexMatrix (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1,
        Quaternion.toComplexMatrix (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2) := by
  simp

/-! ### Compatibility with first-coordinate stabilization and reflection -/

/-- The unit quaternion `(1 + k) / √2` aligning `realSpinThreeEquivQuaternionUnitary` with the
diagonal subgroup of `realSpinFourCalibratedEquivQuaternionUnitaryProd`. -/
noncomputable def realSpinThreeToFourCalibrationUnitary : unitary ℍ[ℝ] :=
  ⟨⟨(Real.sqrt 2)⁻¹, 0, 0, (Real.sqrt 2)⁻¹⟩, by
    rw [Quaternion.mem_unitary_iff_normSq_eq_one, Quaternion.normSq_def']
    simp only [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num⟩

/-- The underlying quaternion of `realSpinThreeToFourCalibrationUnitary` is `(1 + k) / √2`. -/
@[simp] theorem coe_realSpinThreeToFourCalibrationUnitary :
    (realSpinThreeToFourCalibrationUnitary : ℍ[ℝ]) = ⟨(Real.sqrt 2)⁻¹, 0, 0, (Real.sqrt 2)⁻¹⟩ :=
  (rfl)

/-- First-coordinate inclusion embeds `Cl⁺(3,0) ≃ ℍ` diagonally into calibrated `Cl⁺(4,0) ≃ ℍ × ℍ`
after conjugating by `realSpinThreeToFourCalibrationUnitary`. -/
@[simp] theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstInclusion
    (x : CliffordAlgebra.even (realCliffordForm 3 0)) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenMap (realCliffordSpinFirstInclusionIsometry 3) x) =
      (Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
          (realCliffordThreeZeroEvenEquivQuaternion x),
        Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary
          (realCliffordThreeZeroEvenEquivQuaternion x)) := by
  let c :=
    (Unitary.conjStarAlgAut ℝ ℍ[ℝ] realSpinThreeToFourCalibrationUnitary).toAlgEquiv.toAlgHom
  have h : realCliffordFourZeroCalibratedEvenEquivQuaternionProd.toAlgHom.comp
      (CliffordAlgebra.evenMap (realCliffordSpinFirstInclusionIsometry 3)) =
      (c.prod c).comp realCliffordThreeZeroEvenEquivQuaternion.toAlgHom :=
    CliffordAlgebra.even.algHom_ext _ <| CliffordAlgebra.EvenHom.ext <| LinearMap.ext₂ fun m n ↦ by
      have hcons (u : Fin 3 → ℝ) :
          realCliffordFourZeroCalibratedQuaternionEquiv (Fin.cons 0 u) = ⟨0, u 0, u 1, u 2⟩ :=
        QuaternionAlgebra.ext (by simp) (by simp)
          (by simpa using Fin.cons_succ (α := fun _ ↦ ℝ) 0 u 1)
          (by simpa using Fin.cons_succ (α := fun _ ↦ ℝ) 0 u 2)
      simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.prod_apply,
        c, StarAlgEquiv.coe_toAlgEquiv, CliffordAlgebra.evenMap_ι,
        realCliffordSpinFirstInclusionIsometry_apply,
        realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι, hcons,
        realCliffordThreeZeroEvenEquivQuaternion_ι]
      ext <;>
        simp only [Unitary.conjStarAlgAut_apply,
          coe_realSpinThreeToFourCalibrationUnitary, QuaternionAlgebra.star_mk,
          QuaternionAlgebra.mk_mul_mk] <;>
        ring_nf <;> simp only [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> ring
  simpa [c] using DFunLike.congr_fun h x

/-- **First-coordinate Spin stabilization `Spin(3) →* Spin(4)` is diagonal in the calibrated
quaternion-pair model**, up to inner conjugation by `realSpinThreeToFourCalibrationUnitary`. -/
@[simp] theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion
    (t : spinGroup (realCliffordForm 3 0)) :
    realSpinFourCalibratedEquivQuaternionUnitaryProd (realCliffordSpinFirstInclusion 3 t) =
      (MulAut.conj realSpinThreeToFourCalibrationUnitary (realSpinThreeEquivQuaternionUnitary t),
        MulAut.conj realSpinThreeToFourCalibrationUnitary
          (realSpinThreeEquivQuaternionUnitary t)) := by
  let x := CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
    (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) t)
  have heven : CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
      (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0)
        (realCliffordSpinFirstInclusion 3 t)) =
      CliffordAlgebra.evenMap (realCliffordSpinFirstInclusionIsometry 3) x := Subtype.ext <| by
    simp only [x, CliffordAlgebra.coe_evenMap_apply,
      CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply,
      CliffordAlgebra.coe_spinGroupToEven_apply, coe_realCliffordSpinFirstInclusion_apply]
  apply Prod.ext <;> apply Subtype.ext <;>
    simp only [coe_fst_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply,
      coe_snd_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply, heven,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstInclusion,
      coe_realSpinThreeEquivQuaternionUnitary_apply, Unitary.conjStarAlgAut_apply,
      Unitary.coe_conj_apply, x]

/-- An element of `Spin(4)` lies in the image of `Spin(3) →* Spin(4)` iff its two calibrated
unit-quaternion coordinates coincide. -/
theorem mem_range_realCliffordSpinFirstInclusion_three_iff :
    s ∈ Set.range (realCliffordSpinFirstInclusion 3) ↔
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 =
        (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  refine ⟨fun ⟨t, ht⟩ ↦ ht ▸ by simp, fun hs ↦ ?_⟩
  let q := (MulAut.conj realSpinThreeToFourCalibrationUnitary).symm
    (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1
  refine ⟨realSpinThreeEquivQuaternionUnitary.symm q,
    realSpinFourCalibratedEquivQuaternionUnitaryProd.injective ?_⟩
  rw [realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion,
    realSpinThreeEquivQuaternionUnitary.apply_symm_apply,
    (MulAut.conj realSpinThreeToFourCalibrationUnitary).apply_symm_apply]
  nth_rw 2 [hs]

-- Not `@[simp]`: `QuadraticMap.IsometryEquiv.spinGroupEquiv_apply` rewrites `.spinGroupEquiv` to
-- `.toIsometry.spinGroupMap`; see
-- `realSpinFourCalibratedEquivQuaternionUnitaryProd_spinGroupMap_firstReflection`.
/-- **First-coordinate reflection swaps the two `Spin(4)` factors** in the calibrated
unit-quaternion product model. -/
theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection :
    realSpinFourCalibratedEquivQuaternionUnitaryProd
        ((realCliffordCoordReflection 0).spinGroupEquiv s) =
      Prod.swap (realSpinFourCalibratedEquivQuaternionUnitaryProd s) := by
  let x := CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
    (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)
  have heven : CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
      (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0)
        ((realCliffordCoordReflection 0).spinGroupEquiv s)) =
      CliffordAlgebra.evenEquivOfIsometry (realCliffordCoordReflection 0) x := Subtype.ext <| by
    simp only [x, CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply,
      CliffordAlgebra.coe_spinGroupToEven_apply, CliffordAlgebra.coe_evenEquivOfIsometry_apply,
      CliffordAlgebra.equivOfIsometry_apply, QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
      QuadraticMap.Isometry.coe_spinGroupMap_apply]
  apply Prod.ext <;> apply Subtype.ext <;>
    simp only [coe_fst_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply,
      coe_snd_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply, heven,
      realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstReflection, Prod.fst_swap,
      Prod.snd_swap, x]

/-- Simp-normal form of `realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection` on
`spinGroupMap`. -/
@[simp] theorem realSpinFourCalibratedEquivQuaternionUnitaryProd_spinGroupMap_firstReflection :
    realSpinFourCalibratedEquivQuaternionUnitaryProd
        ((realCliffordCoordReflection 0).toIsometry.spinGroupMap s) =
      Prod.swap (realSpinFourCalibratedEquivQuaternionUnitaryProd s) := by
  rw [← QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
    realSpinFourCalibratedEquivQuaternionUnitaryProd_firstReflection]

end Calibrated

end TauCeti

end
