/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
public import TauCeti.Algebra.Quaternion.NormForm

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

## Main definitions and results

* `TauCeti.realCliffordZeroThreeEquivQuaternionProd` identifies `Cl(0,3)` with `ℍ × ℍ`.
* `TauCeti.realCliffordZeroThreeEquivQuaternionProd_star` identifies Clifford conjugation with
  componentwise quaternion conjugation.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd` identifies `Cl⁺(4,0)` with `ℍ × ℍ`.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd_ι` gives its bilinear-generator
  coordinates.
* `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd_reverseEven` identifies reversal with
  componentwise quaternion conjugation.
* `TauCeti.realCliffordFourZeroQuaternionEquiv` identifies the underlying quadratic space of
  `Cl(4,0)` with the Hamilton quaternion norm form.

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

end TauCeti

end
