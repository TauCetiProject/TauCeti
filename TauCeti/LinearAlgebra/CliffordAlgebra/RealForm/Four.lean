/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Reflection
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
public import TauCeti.Algebra.Central.Quaternion
public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.Algebra.Subalgebra.Center
import TauCeti.RingTheory.Nilpotent.Reduced

/-!
# The compact four-dimensional even Clifford algebra

The Clifford algebra `Cl(0,3)` is the product of two copies of the Hamilton quaternions.  Under
the explicit model used here, Clifford conjugation becomes componentwise quaternion conjugation.
Combining this with the standard equivalence `Cl⁺(4,0) ≃ Cl(0,3)` identifies the even Clifford
algebra of the positive-definite four-dimensional real form with `ℍ × ℍ`, and carries reversal to
componentwise conjugation.

The two quaternion factors are distinguished by the sign of the third Clifford generator.  The
volume element therefore maps to `(-1, 1)`, which separates the factors and proves surjectivity of
the model.

Since `ℍ` is a central `ℝ`-algebra, the centre of `Cl⁺(4,0)`, the discriminant quadratic algebra
of the sum of four squares, is the split algebra `ℝ × ℝ`. A split centre does not split the two
factors: here they are the division algebra `ℍ`, so `Cl⁺(4,0)` is not `M₂(ℝ) × M₂(ℝ)`. By
contrast the hyperbolic space `H ⟂ H`, whose centre is also split
(`TauCeti.hyperbolicFourCenterEvenEquivProd`), has two matrix-algebra factors.

In the standard ordered `(1, i, j, k)` quaternion identification of `ℝ⁴`
(`TauCeti.realCliffordFourZeroCalibratedQuaternionEquiv`), swapping and conjugating the native
factors by `u = (1 + j) / √2` gives `TauCeti.realCliffordFourZeroCalibratedEvenEquivQuaternionProd`
with generator formula `(m * star n, star m * n)`, chirality volume element `(1, -1)`, and
factor-swapping first-coordinate reflection (`TauCeti.realCliffordCoordReflection 0`).

## Main definitions and results

* `TauCeti.realCliffordZeroThreeEquivQuaternionProd` identifies `Cl(0,3)` with `ℍ × ℍ`.
* `TauCeti.realCliffordZeroThreeEquivQuaternionProd_star` identifies Clifford conjugation with
  componentwise quaternion conjugation.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd` identifies `Cl⁺(4,0)` with `ℍ × ℍ`.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd_ι` gives its bilinear-generator
  coordinates.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd_symm_neg_one_one` identifies the element
  with coordinates `(-1, 1)` as `-(e₀ e₁)(e₂ e₃)`.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd_reverseEven` identifies reversal with
  componentwise quaternion conjugation.
* `TauCeti.realCliffordFourZeroCenterEvenEquivProd` identifies the centre of `Cl⁺(4,0)` with
  `ℝ × ℝ`.
* `TauCeti.isEmpty_realCliffordFourZeroEven_algEquiv_matrix_prod`: `Cl⁺(4,0)` is not a product of
  two real matrix algebras of degree two.
* `TauCeti.realCliffordFourZeroQuaternionEquiv` identifies the underlying quadratic space of
  `Cl(4,0)` with the Hamilton quaternion norm form.
* `TauCeti.realCliffordFourZeroCalibratedQuaternionEquiv` and
  `TauCeti.realCliffordFourZeroCalibratedEvenEquivQuaternionProd`: calibrated `(1, i, j, k)` models
  of `ℝ⁴` and `Cl⁺(4,0)`, generator evaluations, and reflection swap.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

open scoped Quaternion

namespace TauCeti

private def realCliffordZeroThreeToQuaternionProd :
    CliffordAlgebra (realCliffordForm 0 3) →ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  CliffordAlgebra.lift _
    ⟨{
      toFun v :=
        (⟨0, v 0, v 1, v 2⟩, ⟨0, v 0, v 1, -v 2⟩)
      map_add' := by
        intro v w
        ext <;> simp [add_comm]
      map_smul' := by
        intro r v
        ext <;> simp }, fun v => by
      ext <;>
        rw [realCliffordForm_apply, Fin.sum_univ_three] <;>
        simp <;>
        ring⟩

private theorem realCliffordZeroThreeToQuaternionProd_ι (v : Fin (0 + 3) → ℝ) :
    realCliffordZeroThreeToQuaternionProd (CliffordAlgebra.ι _ v) =
      (⟨0, v 0, v 1, v 2⟩, ⟨0, v 0, v 1, -v 2⟩) :=
  CliffordAlgebra.lift_ι_apply _ _ v

private theorem realCliffordZeroThreeToQuaternionProd_surjective :
    Function.Surjective realCliffordZeroThreeToQuaternionProd := by
  rintro ⟨q, r⟩
  let e (i : Fin 3) : CliffordAlgebra (realCliffordForm 0 3) :=
    CliffordAlgebra.ι _ (Pi.single i 1)
  let z := e 0 * e 1 * e 2
  let p := (2 : ℝ)⁻¹ • (1 - z)
  let n := (2 : ℝ)⁻¹ • (1 + z)
  let q' := algebraMap ℝ _ q.re + q.imI • e 0 + q.imJ • e 1 + q.imK • (e 0 * e 1)
  let r' := algebraMap ℝ _ r.re + r.imI • e 0 + r.imJ • e 1 + r.imK • (e 0 * e 1)
  refine ⟨p * q' + n * r', ?_⟩
  ext <;>
    simp [p, n, q', r', z, e, realCliffordZeroThreeToQuaternionProd_ι] <;>
    ring

private theorem realCliffordZeroThreeToQuaternionProd_bijective :
    Function.Bijective realCliffordZeroThreeToQuaternionProd := by
  have hrank :
      Module.finrank ℝ (CliffordAlgebra (realCliffordForm 0 3)) =
        Module.finrank ℝ (ℍ[ℝ] × ℍ[ℝ]) := by
    rw [finrank_cliffordAlgebra_realCliffordForm, Module.finrank_prod,
      Quaternion.finrank_eq_four]
    norm_num
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := realCliffordZeroThreeToQuaternionProd.toLinearMap) hrank).2
    realCliffordZeroThreeToQuaternionProd_surjective,
    realCliffordZeroThreeToQuaternionProd_surjective⟩

/-- **`Cl(0,3) ≃ ℍ × ℍ`**: the first two negative Clifford generators act as `(i,i)` and
`(j,j)`, while the third acts as `(k,-k)`. -/
noncomputable def realCliffordZeroThreeEquivQuaternionProd :
    CliffordAlgebra (realCliffordForm 0 3) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  AlgEquiv.ofBijective realCliffordZeroThreeToQuaternionProd
    realCliffordZeroThreeToQuaternionProd_bijective

/-- The quaternion-pair coordinates of a generator of `Cl(0,3)`. -/
@[simp]
theorem realCliffordZeroThreeEquivQuaternionProd_ι (v : Fin (0 + 3) → ℝ) :
    realCliffordZeroThreeEquivQuaternionProd (CliffordAlgebra.ι _ v) =
      (⟨0, v 0, v 1, v 2⟩, ⟨0, v 0, v 1, -v 2⟩) := by
  rw [realCliffordZeroThreeEquivQuaternionProd, AlgEquiv.ofBijective_apply,
    realCliffordZeroThreeToQuaternionProd_ι]

/-- The `Cl(0,3)` quaternion-pair model identifies Clifford conjugation with componentwise
quaternion conjugation. -/
@[simp]
theorem realCliffordZeroThreeEquivQuaternionProd_star
    (x : CliffordAlgebra (realCliffordForm 0 3)) :
    realCliffordZeroThreeEquivQuaternionProd (star x) =
      star (realCliffordZeroThreeEquivQuaternionProd x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => ext <;> simp
  | ι v =>
      rw [CliffordAlgebra.star_ι, map_neg,
        realCliffordZeroThreeEquivQuaternionProd_ι]
      ext <;> simp
  | add x y hx hy =>
      rw [star_add, map_add, hx, hy]
      apply Prod.ext <;> simp
  | mul x y hx hy =>
      rw [star_mul, map_mul, hy, hx]
      apply Prod.ext <;> simp

private noncomputable def realCliffordZeroFourAugmentedIsometry :
    (realCliffordForm 0 4).IsometryEquiv
      (CliffordAlgebra.EquivEven.Q' (realCliffordForm 0 3)) :=
  (realCliffordSplitIsometry 0 0 3 1).trans
    ((QuadraticMap.IsometryEquiv.refl (realCliffordForm 0 3)).prod
      realCliffordZeroOneIsometry)

@[simp]
private theorem realCliffordFormNegIsometry_four_zero (v : Fin 4 → ℝ) :
    realCliffordFormNegIsometry 4 0 v = v := by
  funext i
  simpa using realCliffordFormNegIsometry_apply_natAdd 4 0 v i

private theorem realCliffordZeroFourAugmentedIsometry_apply (v : Fin 4 → ℝ) :
    realCliffordZeroFourAugmentedIsometry v = (![v 0, v 1, v 2], v 3) := by
  classical
  apply Prod.ext
  · funext i
    -- The product/composite isometry has no application lemma; expose its first projection so the
    -- split-isometry coordinate theorem can rewrite it.
    change (realCliffordSplitIsometry 0 0 3 1 v).1 i = _
    convert realCliffordSplitIsometry_fst_neg 0 0 3 1 v i using 1
    all_goals fin_cases i <;> simp
  · -- Likewise, expose the second projection before applying the one-dimensional coordinate
    -- theorem; rewriting cannot see through the composed isometry wrapper.
    change realCliffordZeroOneIsometry
      (realCliffordSplitIsometry 0 0 3 1 v).2 = v 3
    rw [realCliffordZeroOneIsometry_apply]
    convert realCliffordSplitIsometry_snd_neg 0 0 3 1 v (0 : Fin 1)
      using 1 <;> simp

/-- The even Clifford algebra of the positive-definite four-dimensional real form is a product of
two Hamilton quaternion algebras. -/
noncomputable def realCliffordFourZeroEvenEquivQuaternionProd :
    CliffordAlgebra.even (realCliffordForm 4 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  (CliffordAlgebra.evenEquivEvenNeg (realCliffordForm 4 0)).trans
    ((CliffordAlgebra.evenEquivOfIsometry (realCliffordFormNegIsometry 4 0)).trans
      ((CliffordAlgebra.evenEquivOfIsometry realCliffordZeroFourAugmentedIsometry).trans
        ((CliffordAlgebra.equivEven (realCliffordForm 0 3)).symm.trans
          realCliffordZeroThreeEquivQuaternionProd)))

/-- The centre of the even Clifford algebra of the positive-definite four-dimensional real form,
its discriminant quadratic algebra, is the split algebra `ℝ × ℝ`. -/
noncomputable def realCliffordFourZeroCenterEvenEquivProd :
    Subalgebra.center ℝ (CliffordAlgebra.even (realCliffordForm 4 0)) ≃ₐ[ℝ] ℝ × ℝ :=
  (Subalgebra.centerCongr realCliffordFourZeroEvenEquivQuaternionProd).trans
    (centerProdAlgEquivOfIsCentral ℝ ℍ[ℝ] ℍ[ℝ])

/-- The inverse of the compact centre equivalence sends a pair of reals to the even Clifford
element whose two quaternion components are the corresponding real quaternions. -/
@[simp]
theorem coe_realCliffordFourZeroCenterEvenEquivProd_symm (r : ℝ × ℝ) :
    (realCliffordFourZeroCenterEvenEquivProd.symm r :
        CliffordAlgebra.even (realCliffordForm 4 0)) =
      realCliffordFourZeroEvenEquivQuaternionProd.symm ((r.1 : ℍ[ℝ]), (r.2 : ℍ[ℝ])) := by
  simp [realCliffordFourZeroCenterEvenEquivProd]

/-- Although its centre is split, the even Clifford algebra of the positive-definite
four-dimensional real form is not a product of two real matrix algebras of degree two: it is
`ℍ × ℍ`, which has no nonzero nilpotent elements. -/
theorem isEmpty_realCliffordFourZeroEven_algEquiv_matrix_prod :
    IsEmpty (CliffordAlgebra.even (realCliffordForm 4 0) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨fun f ↦ ?_⟩
  have : IsReduced (Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) :=
    isReduced_of_injective (f.symm.trans realCliffordFourZeroEvenEquivQuaternionProd)
      (AlgEquiv.injective _)
  have : IsReduced (Matrix (Fin 2) (Fin 2) ℝ) :=
    isReduced_of_injective ((RingHom.id _).prod (RingHom.id _)) fun _ _ h ↦ congrArg Prod.fst h
  exact zero_ne_one ((Matrix.subsingleton_of_isReduced (m := Fin 2) (A := ℝ)).elim 0 1)

/-- The quaternion-pair coordinates of the image of a product of two compact
four-dimensional Clifford generators. -/
@[simp]
theorem realCliffordFourZeroEvenEquivQuaternionProd_ι (m n : Fin 4 → ℝ) :
    realCliffordFourZeroEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin m n) =
      (-(⟨m 3, m 0, m 1, m 2⟩ * ⟨-n 3, n 0, n 1, n 2⟩ : ℍ[ℝ]),
        -(⟨m 3, m 0, m 1, -m 2⟩ * ⟨-n 3, n 0, n 1, -n 2⟩ : ℍ[ℝ])) := by
  classical
  simp only [realCliffordFourZeroEvenEquivQuaternionProd, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivEvenNeg_apply, CliffordAlgebra.evenToNeg_ι,
    map_neg, CliffordAlgebra.evenEquivOfIsometry_ι,
    map_neg, CliffordAlgebra.evenEquivOfIsometry_ι, map_neg,
    CliffordAlgebra.equivEven_symm_apply, CliffordAlgebra.ofEven_ι]
  simp only [realCliffordFormNegIsometry_four_zero,
    realCliffordZeroFourAugmentedIsometry_apply]
  ext <;> simp [realCliffordZeroThreeEquivQuaternionProd_ι] <;> ring

/-- The element with quaternion-pair coordinates `(-1, 1)` is `-(e₀ e₁)(e₂ e₃)` in the even
Clifford algebra of the positive-definite four-dimensional real form. -/
theorem realCliffordFourZeroEvenEquivQuaternionProd_symm_neg_one_one :
    realCliffordFourZeroEvenEquivQuaternionProd.symm (-1, 1) =
      -((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 1 1) *
        (CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 2 1)
          (Pi.single 3 1)) := by
  rw [AlgEquiv.symm_apply_eq, map_neg, map_mul, realCliffordFourZeroEvenEquivQuaternionProd_ι,
    realCliffordFourZeroEvenEquivQuaternionProd_ι]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In the compact four-dimensional quaternion-pair model, Clifford reversal is componentwise
quaternion conjugation. -/
@[simp]
theorem realCliffordFourZeroEvenEquivQuaternionProd_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 4 0)) :
    realCliffordFourZeroEvenEquivQuaternionProd
        (CliffordAlgebra.reverseEven (realCliffordForm 4 0) x) =
      star (realCliffordFourZeroEvenEquivQuaternionProd x) := by
  simp only [realCliffordFourZeroEvenEquivQuaternionProd, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivEvenNeg_reverseEven,
    CliffordAlgebra.evenEquivOfIsometry_reverseEven,
    CliffordAlgebra.evenEquivOfIsometry_reverseEven,
    CliffordAlgebra.equivEven_symm_reverseEven,
    realCliffordZeroThreeEquivQuaternionProd_star]

/-- The reverse norm in `Cl⁺(4,0)` becomes the pair of quaternion norm-squares. -/
theorem realCliffordFourZeroEvenEquivQuaternionProd_map_reverseEven_mul_self_eq_normSq
    (x : CliffordAlgebra.even (realCliffordForm 4 0)) :
    realCliffordFourZeroEvenEquivQuaternionProd
        (CliffordAlgebra.reverseEven (realCliffordForm 4 0) x * x) =
      (algebraMap ℝ ℍ[ℝ]
          (Quaternion.normSq (realCliffordFourZeroEvenEquivQuaternionProd x).1),
        algebraMap ℝ ℍ[ℝ]
          (Quaternion.normSq (realCliffordFourZeroEvenEquivQuaternionProd x).2)) := by
  rw [map_mul, realCliffordFourZeroEvenEquivQuaternionProd_reverseEven]
  ext <;> simp [Quaternion.star_mul_self]

/-- A Hamilton-quaternion model of the vector space underlying `Cl(4,0)`. The
coordinate order is chosen so that the two unit-quaternion factors act by left and inverse right
multiplication. -/
noncomputable def realCliffordFourZeroQuaternionEquiv :
    (realCliffordForm 4 0).IsometryEquiv
      (QuaternionAlgebra.normForm (-1 : ℝ) 0 (-1 : ℝ)) where
  toFun v := ⟨-v 2, v 1, -v 0, v 3⟩
  invFun q := ![-q.imJ, q.imI, -q.re, q.imK]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv q := by ext <;> simp
  map_add' _ _ := by ext <;> simp <;> abel
  map_smul' _ _ := by ext <;> simp
  map_app' v := by
    rw [QuaternionAlgebra.normForm_apply_coordinates, realCliffordForm_apply,
      Fin.sum_univ_four]
    simp
    ring

/-- The Hamilton-quaternion coordinates of a vector in the compact real four-dimensional
model. -/
@[simp]
theorem realCliffordFourZeroQuaternionEquiv_apply (v : Fin 4 → ℝ) :
    realCliffordFourZeroQuaternionEquiv v = ⟨-v 2, v 1, -v 0, v 3⟩ :=
  (rfl)

/-- The vector coordinates recovered from a Hamilton quaternion. -/
@[simp]
theorem realCliffordFourZeroQuaternionEquiv_symm_apply (q : ℍ[ℝ]) :
    realCliffordFourZeroQuaternionEquiv.symm q =
      ![-q.imJ, q.imI, -q.re, q.imK] :=
  (rfl)

/-! ### Calibrated `(1, i, j, k)` quaternion model -/

/-- **Calibrated Hamilton-quaternion model of `ℝ⁴`**: the quadratic isometry identifying
`Fin 4 → ℝ` under `realCliffordForm 4 0` with `ℍ[ℝ]` in the standard ordered basis `(1, i, j, k)`,
sending `v` to `⟨v 0, v 1, v 2, v 3⟩`. -/
noncomputable def realCliffordFourZeroCalibratedQuaternionEquiv :
    (realCliffordForm 4 0).IsometryEquiv (QuaternionAlgebra.normForm (-1 : ℝ) 0 (-1 : ℝ)) where
  __ := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1 : ℝ)).symm
  map_app' v := by
    have hw : realCliffordWeight 4 0 = ![(1 : ℝ), -(-1), -(-1), (-1) * (-1)] := funext fun i ↦ by
      rw [realCliffordWeight_of_lt (by omega)]
      fin_cases i <;> norm_num
    simpa [realCliffordForm_def, hw] using
      (QuaternionAlgebra.normFormIsometryEquivWeightedSumSquares (-1 : ℝ) (-1 : ℝ)).symm.map_app v

/-- The `(1, i, j, k)` quaternion coordinates of a vector in `ℝ⁴`. -/
@[simp]
theorem realCliffordFourZeroCalibratedQuaternionEquiv_apply (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv v = ⟨v 0, v 1, v 2, v 3⟩ := (rfl)

/-- The vector coordinates recovered from a Hamilton quaternion in the `(1, i, j, k)` model. -/
@[simp]
theorem realCliffordFourZeroCalibratedQuaternionEquiv_symm_apply (q : ℍ[ℝ]) :
    realCliffordFourZeroCalibratedQuaternionEquiv.symm q = ![q.re, q.imI, q.imJ, q.imK] := (rfl)

/-- The unit quaternion `(1 + j) / √2` relating the native and `(1, i, j, k)` models of
`Cl⁺(4,0)`. -/
noncomputable def realCliffordFourZeroCalibrationUnitary : unitary ℍ[ℝ] :=
  ⟨⟨(Real.sqrt 2)⁻¹, 0, (Real.sqrt 2)⁻¹, 0⟩, by
    rw [QuaternionAlgebra.mem_unitary_iff_normForm_eq_one,
      QuaternionAlgebra.normForm_apply_coordinates]
    simp only [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num⟩

/-- The underlying quaternion of `realCliffordFourZeroCalibrationUnitary` is `(1 + j) / √2`. -/
@[simp]
theorem coe_realCliffordFourZeroCalibrationUnitary :
    (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ]) = ⟨(Real.sqrt 2)⁻¹, 0, (Real.sqrt 2)⁻¹, 0⟩ :=
  (rfl)

/-- Relation between the calibrated and native vector-to-quaternion isometries. -/
theorem realCliffordFourZeroCalibratedQuaternionEquiv_eq_neg_mul_star_mul (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv v =
      -((realCliffordFourZeroCalibrationUnitary : ℍ[ℝ]) *
        star (realCliffordFourZeroQuaternionEquiv v) *
          (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ])) := by
  ext <;>
    simp only [realCliffordFourZeroCalibratedQuaternionEquiv_apply,
      coe_realCliffordFourZeroCalibrationUnitary, realCliffordFourZeroQuaternionEquiv_apply,
      QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.re_neg,
      QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg] <;>
    ring_nf <;> simp only [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> ring

/-- The involutive `ℝ`-`⋆`-algebra equivalence `(n₁, n₂) ↦ (u * n₂ * star u, star u * n₁ * u)` on
`ℍ × ℍ` for `u = (1 + j) / √2`. -/
noncomputable def realCliffordFourZeroQuaternionProdCalibrationEquiv :
    ℍ[ℝ] × ℍ[ℝ] ≃⋆ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  let c := Unitary.conjStarAlgAut ℝ ℍ[ℝ] realCliffordFourZeroCalibrationUnitary
  { toFun p := (c p.2, c.symm p.1)
    invFun p := (c p.2, c.symm p.1)
    left_inv p := Prod.ext (c.apply_symm_apply p.1) (c.symm_apply_apply p.2)
    right_inv p := Prod.ext (c.apply_symm_apply p.1) (c.symm_apply_apply p.2)
    map_mul' p q := Prod.ext (map_mul _ p.2 q.2) (map_mul _ p.1 q.1)
    map_add' p q := Prod.ext (map_add _ p.2 q.2) (map_add _ p.1 q.1)
    map_smul' r p := Prod.ext (map_smul _ r p.2) (map_smul _ r p.1)
    map_star' p := Prod.ext (map_star _ p.2) (map_star _ p.1) }

/-- Coordinates of `realCliffordFourZeroQuaternionProdCalibrationEquiv`. -/
@[simp]
theorem realCliffordFourZeroQuaternionProdCalibrationEquiv_apply (p : ℍ[ℝ] × ℍ[ℝ]) :
    realCliffordFourZeroQuaternionProdCalibrationEquiv p =
      ((realCliffordFourZeroCalibrationUnitary : ℍ[ℝ]) * p.2 *
          star (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ]),
        star (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ]) * p.1 *
          (realCliffordFourZeroCalibrationUnitary : ℍ[ℝ])) := by
  simp [realCliffordFourZeroQuaternionProdCalibrationEquiv, Unitary.conjStarAlgAut_apply,
    Unitary.coe_star]

/-- `realCliffordFourZeroQuaternionProdCalibrationEquiv` is an involution. -/
@[simp]
theorem realCliffordFourZeroQuaternionProdCalibrationEquiv_symm :
    realCliffordFourZeroQuaternionProdCalibrationEquiv.symm =
      realCliffordFourZeroQuaternionProdCalibrationEquiv := (rfl)

/-- **Calibrated `Cl⁺(4,0) ≃ₐ[ℝ] ℍ × ℍ` equivalence** for `(1, i, j, k)` coordinates on `ℝ⁴`. -/
noncomputable def realCliffordFourZeroCalibratedEvenEquivQuaternionProd :
    CliffordAlgebra.even (realCliffordForm 4 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  realCliffordFourZeroEvenEquivQuaternionProd.trans
    realCliffordFourZeroQuaternionProdCalibrationEquiv.toAlgEquiv

/-- `realCliffordFourZeroCalibratedEvenEquivQuaternionProd` factors through the native model. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_eq_calibrationEquiv
    (x : CliffordAlgebra.even (realCliffordForm 4 0)) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd x =
      realCliffordFourZeroQuaternionProdCalibrationEquiv
        (realCliffordFourZeroEvenEquivQuaternionProd x) := by
  simp [realCliffordFourZeroCalibratedEvenEquivQuaternionProd]

/-- In the calibrated quaternion-pair model, Clifford reversal is componentwise conjugation. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 4 0)) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.reverseEven (realCliffordForm 4 0) x) =
      star (realCliffordFourZeroCalibratedEvenEquivQuaternionProd x) := by
  rw [realCliffordFourZeroCalibratedEvenEquivQuaternionProd, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, realCliffordFourZeroEvenEquivQuaternionProd_reverseEven,
    StarAlgEquiv.coe_toAlgEquiv, map_star]

/-- **Calibrated bilinear-generator formula**: `ι(m) ι(n)` maps to `(m * star n, star m * n)`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι (m n : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin m n) =
      (realCliffordFourZeroCalibratedQuaternionEquiv m *
          star (realCliffordFourZeroCalibratedQuaternionEquiv n),
        star (realCliffordFourZeroCalibratedQuaternionEquiv m) *
          realCliffordFourZeroCalibratedQuaternionEquiv n) := by
  simp only [realCliffordFourZeroCalibratedEvenEquivQuaternionProd, AlgEquiv.trans_apply,
    StarAlgEquiv.coe_toAlgEquiv, realCliffordFourZeroEvenEquivQuaternionProd_ι,
    realCliffordFourZeroQuaternionProdCalibrationEquiv_apply,
    coe_realCliffordFourZeroCalibrationUnitary, realCliffordFourZeroCalibratedQuaternionEquiv_apply]
  ext <;>
    simp only [mul_neg, neg_mul, QuaternionAlgebra.star_mk,
      QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg,
      QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg] <;>
    ring_nf <;> simp only [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> ring

/-- Right-multiplying `v ∈ ℝ⁴` by `e₀` gives calibrated coordinates `(φ v, star (φ v))`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_right (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin v (Pi.single 0 1)) =
      (realCliffordFourZeroCalibratedQuaternionEquiv v,
        star (realCliffordFourZeroCalibratedQuaternionEquiv v)) := by
  have he₀ : realCliffordFourZeroCalibratedQuaternionEquiv (Pi.single 0 1) = 1 := by ext <;> simp
  rw [realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι, he₀, star_one, mul_one, mul_one]

/-- Left-multiplying `v ∈ ℝ⁴` by `e₀` gives calibrated coordinates `(star (φ v), φ v)`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_left (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) v) =
      (star (realCliffordFourZeroCalibratedQuaternionEquiv v),
        realCliffordFourZeroCalibratedQuaternionEquiv v) := by
  have he₀ : realCliffordFourZeroCalibratedQuaternionEquiv (Pi.single 0 1) = 1 := by ext <;> simp
  rw [realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι, he₀, star_one, one_mul, one_mul]

/-- In the calibrated model, `e₀ e₁` maps to `(-i, i)`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_one :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 1 1)) =
      ((⟨0, -1, 0, 0⟩ : ℍ[ℝ]), (⟨0, 1, 0, 0⟩ : ℍ[ℝ])) :=
  (realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι _ _).trans <| by ext <;> simp

/-- In the calibrated model, `e₀ e₂` maps to `(-j, j)`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_two :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 2 1)) =
      ((⟨0, 0, -1, 0⟩ : ℍ[ℝ]), (⟨0, 0, 1, 0⟩ : ℍ[ℝ])) :=
  (realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι _ _).trans <| by ext <;> simp

/-- In the calibrated model, `e₀ e₃` maps to `(-k, k)`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_three :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 3 1)) =
      ((⟨0, 0, 0, -1⟩ : ℍ[ℝ]), (⟨0, 0, 0, 1⟩ : ℍ[ℝ])) :=
  (realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι _ _).trans <| by ext <;> simp

/-- In the calibrated model, `e₁ e₂` maps to `(-k, -k)`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_one_two :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 1 1) (Pi.single 2 1)) =
      ((⟨0, 0, 0, -1⟩ : ℍ[ℝ]), (⟨0, 0, 0, -1⟩ : ℍ[ℝ])) :=
  (realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι _ _).trans <| by
    ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In the calibrated model, `e₁ e₃` maps to `(j, j)`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_one_three :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 1 1) (Pi.single 3 1)) =
      ((⟨0, 0, 1, 0⟩ : ℍ[ℝ]), (⟨0, 0, 1, 0⟩ : ℍ[ℝ])) :=
  (realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι _ _).trans <| by
    ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In the calibrated model, `e₂ e₃` maps to `(-i, -i)`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_two_three :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        ((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 2 1) (Pi.single 3 1)) =
      ((⟨0, -1, 0, 0⟩ : ℍ[ℝ]), (⟨0, -1, 0, 0⟩ : ℍ[ℝ])) :=
  (realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι _ _).trans <| by
    ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In the calibrated model, the chirality volume element `-(e₀ e₁)(e₂ e₃)` has coordinates
`(1, -1)`. -/
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_symm_one_neg_one :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd.symm (1, -1) =
      -((CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 1 1) *
        (CliffordAlgebra.even.ι (realCliffordForm 4 0)).bilin (Pi.single 2 1)
          (Pi.single 3 1)) := by
  rw [AlgEquiv.symm_apply_eq, map_neg, map_mul,
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_zero_one,
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι_single_two_three]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- First-coordinate reflection on `ℝ⁴` corresponds to `-star` in `(1, i, j, k)` coordinates. -/
theorem realCliffordFourZeroCalibratedQuaternionEquiv_firstReflection (v : Fin 4 → ℝ) :
    realCliffordFourZeroCalibratedQuaternionEquiv (realCliffordCoordReflection 0 v) =
      -star (realCliffordFourZeroCalibratedQuaternionEquiv v) := by ext <;> simp

/-- First-coordinate reflection swaps the two quaternion factors of `Cl⁺(4,0) ≃ ℍ × ℍ`. -/
@[simp]
theorem realCliffordFourZeroCalibratedEvenEquivQuaternionProd_firstReflection
    (x : CliffordAlgebra.even (realCliffordForm 4 0)) :
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
        (CliffordAlgebra.evenEquivOfIsometry (realCliffordCoordReflection 0) x) =
      Prod.swap (realCliffordFourZeroCalibratedEvenEquivQuaternionProd x) := by
  let swapAlgHom : ℍ[ℝ] × ℍ[ℝ] →ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
    (AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ])
  have h : realCliffordFourZeroCalibratedEvenEquivQuaternionProd.toAlgHom.comp
      (CliffordAlgebra.evenEquivOfIsometry (realCliffordCoordReflection 0)).toAlgHom =
      swapAlgHom.comp realCliffordFourZeroCalibratedEvenEquivQuaternionProd.toAlgHom :=
    CliffordAlgebra.even.algHom_ext _ <| CliffordAlgebra.EvenHom.ext <| LinearMap.ext₂ fun m n ↦ by
      simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.prod_apply,
        AlgHom.snd_apply, AlgHom.fst_apply, swapAlgHom, CliffordAlgebra.evenEquivOfIsometry_ι,
        realCliffordFourZeroCalibratedEvenEquivQuaternionProd_ι,
        realCliffordFourZeroCalibratedQuaternionEquiv_firstReflection, star_neg, star_star, neg_mul,
        mul_neg, neg_neg]
  simpa [swapAlgHom, Prod.ext_iff] using DFunLike.congr_fun h x

end TauCeti

end
