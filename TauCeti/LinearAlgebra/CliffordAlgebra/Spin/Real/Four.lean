/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# The compact four-dimensional Spin group

The reversal-preserving equivalence `Cl⁺(4,0) ≃ ℍ × ℍ` transports the even unitary carrier to a
pair of unit-quaternion groups.  The general rank-four comparison between Spin and the even
unitary carrier then gives

`Spin(4) ≃ unitary ℍ × unitary ℍ ≃ SU(2) × SU(2)`.

This is the compact real form of the exceptional type-`D₂ = A₁ × A₁` isomorphism.  Both quaternion
factors have norm one; in particular the split discriminant algebra does not make either factor a
split real group.

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

end TauCeti

end
