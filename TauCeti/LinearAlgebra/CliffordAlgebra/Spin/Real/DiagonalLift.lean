/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DiagonalLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization
import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.GroupTheory.Perm.Inversion

/-!
# The compact real diagonal Spin lift `SO(k) →* Spin(k + k)`

Specializing `CliffordAlgebra.spinDiagonalLift` to the positive-definite real form
`realCliffordForm k 0` and transporting along `(realCliffordSplitIsometry k k 0 0).symm` produces
the compact real diagonal Spin lift

`TauCeti.realCliffordSpinDiagonalLift k : SO(k) →* Spin(k + k)`

lifting the diagonal block embedding `g ↦ realCliffordSpecialOrthogonalBlockSum k k (g, g)`.

This module establishes the algebraic properties of `realCliffordSpinDiagonalLift`:
* Compatibility with `realCliffordSpinBlockSum` and `spinToSpecialOrthogonal`, diagonal vector
  action on `Fin.append u v`, and injectivity.
* Low-rank checks: in ranks `0` and `1`, `SO(k)` is trivial and `realCliffordSpinDiagonalLift k`
  is constantly `1`.
* Explicit coordinate-plane rotation formula: for distinct `i, j : Fin k`, the diagonal lift of
  the rotation induced by `spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1) t`
  is the commuting product of the two `spinRotation` elements in the first and second `k`-blocks,
  with Clifford expansion
  `(cos t + sin t · ι e_i ι e_j) * (cos t + sin t · ι e_{k + i} ι e_{k + j})`, which closes to `1`
  at Spin angle `t = π` (a full `2π` rotation in `SO(k)`).
* Block-swap invariance and orientation signs: `realCliffordBlockSwapIsometry k k` has determinant
  `(-1) ^ k` and fixes `realCliffordSpinDiagonalLift k g`, while the middle-block exchange
  `TauCeti.realCliffordMiddleSwapIsometry p q` sending
  `Fin.append (Fin.append u₁ v₁) (Fin.append u₂ v₂)` to
  `Fin.append (Fin.append u₁ u₂) (Fin.append v₁ v₂)` has determinant `(-1) ^ (p * q)` and
  intertwines `realCliffordSpinDiagonalLift (p + q)` on a block sum `(g₁, g₂)` with the Spin block
  sum of `realCliffordSpinDiagonalLift p g₁` and `realCliffordSpinDiagonalLift q g₂`.

## Main definitions

* `TauCeti.realCliffordSpinDiagonalLift`: the canonical homomorphism `SO(k) →* Spin(k + k)`
  lifting `g ↦ diag(g, g)`.
* `TauCeti.realCliffordMiddleSwapIsometry`: the isometric equivalence
  `realCliffordForm ((p + q) + (p + q)) 0 ≃qᵢ realCliffordForm ((p + p) + (q + q)) 0` swapping
  the middle two coordinate blocks.

## Main results

* `TauCeti.realCliffordSpinDiagonalLift_spinToSpecialOrthogonal`,
  `TauCeti.spinToSpecialOrthogonal_realCliffordSpinDiagonalLift`,
  `TauCeti.spinVectorAction_realCliffordSpinDiagonalLift_append`, and
  `TauCeti.realCliffordSpinDiagonalLift_injective`: characterizing equations and injectivity.
* `TauCeti.realCliffordSpinDiagonalLift_zero` and `TauCeti.realCliffordSpinDiagonalLift_one`:
  low-rank triviality in ranks `0` and `1`.
* `TauCeti.realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation`,
  `TauCeti.coe_realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation`, and
  `TauCeti.realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation_pi`: coordinate-plane
  rotation formula and full-turn closure.
* `TauCeti.det_realCliffordFormZeroReindex`, `TauCeti.det_realCliffordBlockSwapIsometry`,
  `TauCeti.det_realCliffordBlockSwapIsometry_self`, and
  `TauCeti.det_realCliffordMiddleSwapIsometry`: determinants of coordinate permutations and block
  exchanges.
* `TauCeti.spinGroupEquiv_realCliffordBlockSwapIsometry_realCliffordSpinDiagonalLift`,
  `TauCeti.spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinBlockSum`,
  `TauCeti.spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinDiagonalLift`, and
  `TauCeti.specialOrthogonalGroupCongr_realCliffordMiddleSwapIsometry_blockSum`: block-swap
  invariance and ordered direct-sum coherence of `realCliffordSpinDiagonalLift` and block sums.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§2 and 6.
-/

public section

open QuadraticMap

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.QuadraticMap

noncomputable section

/-! ### The compact real diagonal Spin lift -/

/-- **The compact real diagonal Spin lift `SO(k) →* Spin(k + k)`**, lifting the diagonal block
embedding `g ↦ realCliffordSpecialOrthogonalBlockSum k k (g, g)`. -/
def realCliffordSpinDiagonalLift (k : ℕ) :
    specialOrthogonalGroup (realCliffordForm k 0) →* realCliffordSpinGroupZero (k + k) :=
  (realCliffordSplitIsometry k k 0 0).symm.spinGroupEquiv.toMonoidHom.comp
    (spinDiagonalLift (realCliffordForm k 0) (nondegenerate_realCliffordForm k 0)
      (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero k)))

/-- `realCliffordSpinDiagonalLift` is `spinDiagonalLift` transported along
`(realCliffordSplitIsometry k k 0 0).symm`. -/
theorem realCliffordSpinDiagonalLift_apply (k : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm k 0)) :
    realCliffordSpinDiagonalLift k g =
      (realCliffordSplitIsometry k k 0 0).symm.spinGroupEquiv
        (spinDiagonalLift (realCliffordForm k 0) (nondegenerate_realCliffordForm k 0)
          (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero k)) g) :=
  (rfl)

/-- Evaluating `realCliffordSpinDiagonalLift` on the projection of `x ∈ Spin(k)` gives the diagonal
block sum `realCliffordSpinBlockSum k k (x, x)`. -/
@[simp]
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal (k : ℕ)
    (x : realCliffordSpinGroupZero k) :
    realCliffordSpinDiagonalLift k (spinToSpecialOrthogonal (realCliffordForm k 0) x) =
      realCliffordSpinBlockSum k k (x, x) := by
  rw [realCliffordSpinDiagonalLift_apply, spinDiagonalLift_spinToSpecialOrthogonal,
    realCliffordSpinBlockSum_apply]

/-- Evaluating `realCliffordSpinDiagonalLift` on the projection of `x ∈ Spin(k)` multiplies the
left- and right-block Spin images of `x`. -/
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_eq_mul (k : ℕ)
    (x : realCliffordSpinGroupZero k) :
    realCliffordSpinDiagonalLift k (spinToSpecialOrthogonal (realCliffordForm k 0) x) =
      (realCliffordSpinBlockInlIsometry k k).spinGroupMap x *
        (realCliffordSpinBlockInrIsometry k k).spinGroupMap x := by
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal, realCliffordSpinBlockSum_eq_mul]

/-- **The projection of `realCliffordSpinDiagonalLift` to `SO(k + k)`** is the diagonal block
embedding `g ↦ realCliffordSpecialOrthogonalBlockSum k k (g, g)`. -/
@[simp]
theorem spinToSpecialOrthogonal_realCliffordSpinDiagonalLift (k : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm k 0)) :
    spinToSpecialOrthogonal (realCliffordForm (k + k) 0) (realCliffordSpinDiagonalLift k g) =
      realCliffordSpecialOrthogonalBlockSum k k (g, g) := by
  rw [realCliffordSpinDiagonalLift_apply,
    ← IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    spinToSpecialOrthogonal_spinDiagonalLift, realCliffordSpecialOrthogonalBlockSum_apply]

/-- **`realCliffordSpinDiagonalLift` acts diagonally on `Fin.append u v`.** -/
@[simp]
theorem spinVectorAction_realCliffordSpinDiagonalLift_append (k : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm k 0)) (u v : Fin k → ℝ) :
    spinVectorAction (realCliffordForm (k + k) 0) (realCliffordSpinDiagonalLift k g)
        (Fin.append u v : Fin (k + k) → ℝ) =
      Fin.append ((g : (Fin k → ℝ) ≃ₗ[ℝ] (Fin k → ℝ)) u)
        ((g : (Fin k → ℝ) ≃ₗ[ℝ] (Fin k → ℝ)) v) := by
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm k 0) (posDef_realCliffordForm_zero k) g
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal,
    spinVectorAction_realCliffordSpinBlockSum_append, coe_spinToSpecialOrthogonal_apply,
    coe_spinToSpecialOrthogonal_apply]

/-- **The compact real diagonal Spin lift `SO(k) →* Spin(k + k)` is injective.** -/
theorem realCliffordSpinDiagonalLift_injective (k : ℕ) :
    Function.Injective (realCliffordSpinDiagonalLift k) :=
  (realCliffordSplitIsometry k k 0 0).symm.spinGroupEquiv.injective.comp
    (spinDiagonalLift_injective _ _ _)

/-! ### Low-rank checks -/

/-- In rank zero, `realCliffordSpinDiagonalLift 0` is constantly `1`. -/
@[simp]
theorem realCliffordSpinDiagonalLift_zero
    (g : specialOrthogonalGroup (realCliffordForm 0 0)) :
    realCliffordSpinDiagonalLift 0 g = 1 := by
  rw [realCliffordSpinDiagonalLift_apply,
    spinDiagonalLift_eq_one_of_finrank_le_one _ _ _ (by simp), map_one]

/-- In rank one, `SO(1)` is trivial and `realCliffordSpinDiagonalLift 1` is constantly `1` in
`Spin(2)`. -/
@[simp]
theorem realCliffordSpinDiagonalLift_one
    (g : specialOrthogonalGroup (realCliffordForm 1 0)) :
    realCliffordSpinDiagonalLift 1 g = 1 := by
  rw [realCliffordSpinDiagonalLift_apply,
    spinDiagonalLift_eq_one_of_finrank_le_one _ _ _ (by simp), map_one]

/-! ### Coordinate-plane rotations -/

private theorem realCliffordSpinBlockInlIsometry_single (p q : ℕ) (i : Fin p) :
    realCliffordSpinBlockInlIsometry p q (Pi.single i (1 : ℝ)) =
      Pi.single (Fin.castAdd q i) (1 : ℝ) := by
  rw [realCliffordSpinBlockInlIsometry_apply]
  funext a
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) a
  · simp [Fin.append_left, Pi.single_apply]
  · rw [Fin.append_right, Pi.zero_apply, Pi.single_apply]
    have hne : Fin.natAdd p j ≠ Fin.castAdd q i := fun h ↦ by
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [hne]

private theorem realCliffordSpinBlockInrIsometry_single (p q : ℕ) (i : Fin q) :
    realCliffordSpinBlockInrIsometry p q (Pi.single i (1 : ℝ)) =
      Pi.single (Fin.natAdd p i) (1 : ℝ) := by
  rw [realCliffordSpinBlockInrIsometry_apply]
  funext a
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) a
  · rw [Fin.append_left, Pi.zero_apply, Pi.single_apply]
    have hne : Fin.castAdd q j ≠ Fin.natAdd p i := fun h ↦ by
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [hne]
  · simp [Fin.append_right, Pi.single_apply]

/-- **Coordinate-plane rotation formula for `realCliffordSpinDiagonalLift`**: the diagonal lift of
a rotation in the `(i, j)` coordinate plane of `ℝ^k` (`i ≠ j`) is the commuting product of the
corresponding `spinRotation` elements in the first and second `k`-blocks of `ℝ^(k + k)`. -/
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) (t : ℝ) :
    realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) t)) =
      spinRotation (realCliffordForm (k + k) 0)
          (Pi.single (Fin.castAdd k i) 1) (Pi.single (Fin.castAdd k j) 1)
          (realCliffordForm_zero_single_one (k + k) (Fin.castAdd k i))
          (realCliffordForm_zero_single_one (k + k) (Fin.castAdd k j))
          (isOrtho_realCliffordForm_single (p := k + k) (q := 0)
            ((Fin.castAdd_injective k k).ne hij) 1 1) t *
        spinRotation (realCliffordForm (k + k) 0)
          (Pi.single (Fin.natAdd k i) 1) (Pi.single (Fin.natAdd k j) 1)
          (realCliffordForm_zero_single_one (k + k) (Fin.natAdd k i))
          (realCliffordForm_zero_single_one (k + k) (Fin.natAdd k j))
          (isOrtho_realCliffordForm_single (p := k + k) (q := 0)
            ((Fin.natAdd_injective k k).ne hij) 1 1) t := by
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_eq_mul,
    (realCliffordSpinBlockInlIsometry k k).spinGroupMap_spinRotation
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1)
      (by rw [realCliffordSpinBlockInlIsometry_single]; exact realCliffordForm_zero_single_one _ _)
      (by rw [realCliffordSpinBlockInlIsometry_single]; exact realCliffordForm_zero_single_one _ _)
      (by
        rw [realCliffordSpinBlockInlIsometry_single, realCliffordSpinBlockInlIsometry_single]
        exact isOrtho_realCliffordForm_single (p := k + k) (q := 0)
          ((Fin.castAdd_injective k k).ne hij) 1 1),
    (realCliffordSpinBlockInrIsometry k k).spinGroupMap_spinRotation
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1)
      (by rw [realCliffordSpinBlockInrIsometry_single]; exact realCliffordForm_zero_single_one _ _)
      (by rw [realCliffordSpinBlockInrIsometry_single]; exact realCliffordForm_zero_single_one _ _)
      (by
        rw [realCliffordSpinBlockInrIsometry_single, realCliffordSpinBlockInrIsometry_single]
        exact isOrtho_realCliffordForm_single (p := k + k) (q := 0)
          ((Fin.natAdd_injective k k).ne hij) 1 1)]
  simp only [realCliffordSpinBlockInlIsometry_single, realCliffordSpinBlockInrIsometry_single]

/-- **Explicit Clifford-algebra expansion of the doubled coordinate-plane rotation**:
`(cos t + sin t · ι e_i ι e_j) * (cos t + sin t · ι e_{k + i} ι e_{k + j})`. -/
theorem coe_realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) (t : ℝ) :
    (realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) t)) :
        _root_.CliffordAlgebra (realCliffordForm (k + k) 0)) =
      (algebraMap ℝ _ (Real.cos t) +
          Real.sin t •
            (ι (realCliffordForm (k + k) 0) (Pi.single (Fin.castAdd k i) 1) *
              ι (realCliffordForm (k + k) 0) (Pi.single (Fin.castAdd k j) 1))) *
        (algebraMap ℝ _ (Real.cos t) +
          Real.sin t •
            (ι (realCliffordForm (k + k) 0) (Pi.single (Fin.natAdd k i) 1) *
              ι (realCliffordForm (k + k) 0) (Pi.single (Fin.natAdd k j) 1))) := by
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation hij t,
    Submonoid.coe_mul, spinRotation_eq_spinCircle, spinRotation_eq_spinCircle,
    coe_spinCircle, coe_spinCircle]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- At Spin angle `π` (a full `2π` rotation in `SO(k)`), the diagonal lift of a coordinate-plane
rotation closes to `1` in `Spin(k + k)`. -/
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation_pi {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) :
    realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) Real.pi)) = 1 := by
  rw [spinRotation_pi, spinGroup.spinToSpecialOrthogonal_negOne, map_one]

/-! ### Determinants of coordinate permutations and block-swap invariance -/

/-- The determinant of the coordinate-permutation isometry `realCliffordFormZeroReindex σ` is the
sign of the permutation `σ`. -/
theorem det_realCliffordFormZeroReindex (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (realCliffordFormZeroReindex σ).toLinearMap =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) := by
  have hlin : (realCliffordFormZeroReindex σ).toLinearMap =
      Matrix.toLin' (σ.permMatrix ℝ) :=
    LinearMap.ext fun x ↦ funext fun i ↦ by
      change realCliffordFormZeroReindex σ x i = _
      rw [realCliffordFormZeroReindex_apply, Matrix.toLin'_apply, Matrix.permMatrix_mulVec,
        Function.comp_apply]
  rw [hlin, LinearMap.det_toLin', Matrix.det_permutation]

/-- Swapping the first `p` and last `q` coordinates of `ℝ^(p + q)` has determinant
`(-1) ^ (p * q)`. -/
theorem det_realCliffordBlockSwapIsometry (p q : ℕ) :
    LinearMap.det ((realCliffordBlockSwapIsometry p q).trans
        (realCliffordFormCongr (add_comm q p) rfl)).toLinearMap =
      (-1 : ℝ) ^ (p * q) := by
  let σ : Equiv.Perm (Fin (p + q)) := (finCongr (add_comm p q)).trans finAddFlip
  have hσ : (realCliffordBlockSwapIsometry p q).trans
      (realCliffordFormCongr (add_comm q p) rfl) = realCliffordFormZeroReindex σ := by
    refine DFunLike.ext _ _ fun x ↦ funext fun i ↦ ?_
    rw [QuadraticMap.IsometryEquiv.trans_apply, realCliffordFormCongr_apply,
      realCliffordBlockSwapIsometry_apply, realCliffordFormZeroReindex_apply]
    rfl
  have hinv : σ = (finAddFlip.trans (finCongr (add_comm q p)))⁻¹ := by
    ext i
    simp [σ, Equiv.Perm.inv_def, finAddFlip, finCongr]
  rw [hσ, det_realCliffordFormZeroReindex, hinv, Equiv.Perm.sign_inv,
    sign_finAddFlip_trans_finCongr]
  simp

/-- Swapping the two `k`-blocks of `ℝ^(k + k)` has determinant `(-1) ^ k`. -/
theorem det_realCliffordBlockSwapIsometry_self (k : ℕ) :
    LinearMap.det (realCliffordBlockSwapIsometry k k).toLinearMap = (-1 : ℝ) ^ k := by
  have h : (realCliffordBlockSwapIsometry k k).trans
      (realCliffordFormCongr (add_comm k k) rfl) = realCliffordBlockSwapIsometry k k :=
    DFunLike.ext _ _ fun _ ↦ funext fun _ ↦ by simp
  rw [← h, det_realCliffordBlockSwapIsometry]
  rcases Nat.even_or_odd k with hk | hk
  · rw [(hk.mul_left k).neg_one_pow, hk.neg_one_pow]
  · rw [(hk.mul hk).neg_one_pow, hk.neg_one_pow]

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Block-swap invariance of `realCliffordSpinDiagonalLift`**: swapping the two `k`-blocks of
`ℝ^(k + k)` fixes `realCliffordSpinDiagonalLift k g`. -/
theorem spinGroupEquiv_realCliffordBlockSwapIsometry_realCliffordSpinDiagonalLift (k : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm k 0)) :
    (realCliffordBlockSwapIsometry k k).spinGroupEquiv (realCliffordSpinDiagonalLift k g) =
      realCliffordSpinDiagonalLift k g := by
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm k 0) (posDef_realCliffordForm_zero k) g
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal,
    spinGroupEquiv_realCliffordBlockSwapIsometry_realCliffordSpinBlockSum, Prod.swap_prod_mk]

/-! ### Middle-block exchange and ordered direct-sum coherence -/

/-- The coordinate isometry exchanging the middle two blocks of `((ℝ^p ⊕ ℝ^q) ⊕ (ℝ^p ⊕ ℝ^q))` to
form `((ℝ^p ⊕ ℝ^p) ⊕ (ℝ^q ⊕ ℝ^q))`, sending `Fin.append (Fin.append u₁ v₁) (Fin.append u₂ v₂)` to
`Fin.append (Fin.append u₁ u₂) (Fin.append v₁ v₂)`. -/
def realCliffordMiddleSwapIsometry (p q : ℕ) :
    (realCliffordForm ((p + q) + (p + q)) 0).IsometryEquiv
      (realCliffordForm ((p + p) + (q + q)) 0) :=
  (realCliffordSplitIsometry (p + q) (p + q) 0 0).trans <|
    ((realCliffordSplitIsometry p q 0 0).prod (realCliffordSplitIsometry p q 0 0)).trans <|
      (QuadraticMap.IsometryEquiv.prodProdProdComm (realCliffordForm p 0) (realCliffordForm q 0)
        (realCliffordForm p 0) (realCliffordForm q 0)).trans <|
        ((realCliffordSplitIsometry p p 0 0).symm.prod
          (realCliffordSplitIsometry q q 0 0).symm).trans
          (realCliffordSplitIsometry (p + p) (q + q) 0 0).symm

/-- `realCliffordMiddleSwapIsometry` exchanges the middle two blocks of a four-block
concatenation. -/
@[simp]
theorem realCliffordMiddleSwapIsometry_append (p q : ℕ)
    (u₁ u₂ : Fin p → ℝ) (v₁ v₂ : Fin q → ℝ) :
    realCliffordMiddleSwapIsometry p q
        (Fin.append (Fin.append u₁ v₁ : Fin (p + q) → ℝ)
          (Fin.append u₂ v₂ : Fin (p + q) → ℝ) : Fin ((p + q) + (p + q)) → ℝ) =
      Fin.append (Fin.append u₁ u₂ : Fin (p + p) → ℝ)
        (Fin.append v₁ v₂ : Fin (q + q) → ℝ) := by
  rw [realCliffordMiddleSwapIsometry, QuadraticMap.IsometryEquiv.trans_apply,
    realCliffordSplitIsometry_zero_append, QuadraticMap.IsometryEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.prod_apply, realCliffordSplitIsometry_zero_append,
    realCliffordSplitIsometry_zero_append, QuadraticMap.IsometryEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.trans_apply, QuadraticMap.IsometryEquiv.prod_apply]
  change (realCliffordSplitIsometry (p + p) (q + q) 0 0).symm
      ((realCliffordSplitIsometry p p 0 0).symm (u₁, u₂),
        (realCliffordSplitIsometry q q 0 0).symm (v₁, v₂)) = _
  rw [realCliffordSplitIsometry_zero_symm_apply, realCliffordSplitIsometry_zero_symm_apply,
    realCliffordSplitIsometry_zero_symm_apply]

/-- Block equivalence packaging `Fin ((p + q) + (p + q))` as `Fin p ⊕ (Fin (p + q) ⊕ Fin q)` so
that the middle-block exchange is the block swap on the middle `Fin (p + q)` factor. -/
private def middleSwapIndexEquiv (p q : ℕ) :
    Fin p ⊕ (Fin (p + q) ⊕ Fin q) ≃ Fin ((p + q) + (p + q)) :=
  ((Equiv.refl (Fin p)).sumCongr finSumFinEquiv).trans <|
    finSumFinEquiv.trans (finCongr (by omega))

/-- The permutation on `Fin ((p + q) + (p + q))` underlying the middle-block exchange. -/
private def middleSwapPerm (p q : ℕ) : Equiv.Perm (Fin ((p + q) + (p + q))) :=
  (middleSwapIndexEquiv p q).permCongr
    (Equiv.Perm.sumCongr 1
      (Equiv.Perm.sumCongr (finAddFlip.trans (finCongr (add_comm q p))) 1))

private theorem realCliffordMiddleSwapIsometry_trans_congr_eq_reindex (p q : ℕ) :
    (realCliffordMiddleSwapIsometry p q).trans
        (realCliffordFormCongr (add_add_add_comm p p q q) rfl) =
      realCliffordFormZeroReindex (middleSwapPerm p q) := by
  have hsplit (a b : ℕ) (y : Fin (a + b) → ℝ) : ∃ u v, y = Fin.append u v :=
    ⟨(realCliffordSplitIsometry a b 0 0 y).1, (realCliffordSplitIsometry a b 0 0 y).2,
      ((realCliffordSplitIsometry a b 0 0).symm_apply_apply y).symm.trans
        (realCliffordSplitIsometry_zero_symm_apply a b _)⟩
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨y₁, y₂, rfl⟩ := hsplit (p + q) (p + q) x
  obtain ⟨u₁, v₁, rfl⟩ := hsplit p q y₁
  obtain ⟨u₂, v₂, rfl⟩ := hsplit p q y₂
  funext (i : Fin ((p + q) + (p + q)))
  rw [QuadraticMap.IsometryEquiv.trans_apply, realCliffordFormCongr_apply,
    realCliffordMiddleSwapIsometry_append, realCliffordFormZeroReindex_apply]
  obtain ⟨k, rfl⟩ := (middleSwapIndexEquiv p q).surjective i
  rcases k with a | (b | c)
  · have hcast : (middleSwapIndexEquiv p q (Sum.inl a)).cast (by omega) =
        Fin.castAdd (q + q) (Fin.castAdd p a) := Fin.ext (by simp [middleSwapIndexEquiv])
    have hperm : middleSwapPerm p q (middleSwapIndexEquiv p q (Sum.inl a)) =
        Fin.castAdd (p + q) (Fin.castAdd q a) :=
      Fin.ext (by simp [middleSwapPerm, middleSwapIndexEquiv])
    rw [hcast, hperm, Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
  · refine Fin.addCases (fun a ↦ ?_) (fun b' ↦ ?_) b
    · have hcast : (middleSwapIndexEquiv p q (Sum.inr (Sum.inl (Fin.castAdd q a)))).cast
          (by omega) = Fin.castAdd (q + q) (Fin.natAdd p a) :=
        Fin.ext (by simp [middleSwapIndexEquiv]; omega)
      have hperm : middleSwapPerm p q
            (middleSwapIndexEquiv p q (Sum.inr (Sum.inl (Fin.castAdd q a)))) =
          Fin.natAdd (p + q) (Fin.castAdd q a) :=
        Fin.ext (by simp [middleSwapPerm, middleSwapIndexEquiv, finAddFlip_apply_castAdd]; omega)
      rw [hcast, hperm, Fin.append_left, Fin.append_right, Fin.append_right, Fin.append_left]
    · have hcast : (middleSwapIndexEquiv p q (Sum.inr (Sum.inl (Fin.natAdd p b')))).cast
          (by omega) = Fin.natAdd (p + p) (Fin.castAdd q b') :=
        Fin.ext (by simp [middleSwapIndexEquiv]; omega)
      have hperm : middleSwapPerm p q
            (middleSwapIndexEquiv p q (Sum.inr (Sum.inl (Fin.natAdd p b')))) =
          Fin.castAdd (p + q) (Fin.natAdd p b') :=
        Fin.ext (by simp [middleSwapPerm, middleSwapIndexEquiv, finAddFlip_apply_natAdd])
      rw [hcast, hperm, Fin.append_right, Fin.append_left, Fin.append_left, Fin.append_right]
  · have hcast : (middleSwapIndexEquiv p q (Sum.inr (Sum.inr c))).cast (by omega) =
        Fin.natAdd (p + p) (Fin.natAdd q c) :=
      Fin.ext (by simp [middleSwapIndexEquiv]; omega)
    have hperm : middleSwapPerm p q (middleSwapIndexEquiv p q (Sum.inr (Sum.inr c))) =
        Fin.natAdd (p + q) (Fin.natAdd p c) :=
      Fin.ext (by simp [middleSwapPerm, middleSwapIndexEquiv]; omega)
    rw [hcast, hperm, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right]

/-- **The determinant of the middle-block exchange `realCliffordMiddleSwapIsometry p q` is
`(-1) ^ (p * q)`.** -/
theorem det_realCliffordMiddleSwapIsometry (p q : ℕ) :
    LinearMap.det ((realCliffordMiddleSwapIsometry p q).trans
        (realCliffordFormCongr (add_add_add_comm p p q q) rfl)).toLinearMap =
      (-1 : ℝ) ^ (p * q) := by
  rw [realCliffordMiddleSwapIsometry_trans_congr_eq_reindex, det_realCliffordFormZeroReindex,
    middleSwapPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr,
    sign_finAddFlip_trans_finCongr]
  simp

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Middle-block exchange coherence of `realCliffordSpinBlockSum`**: transporting a four-block
Spin sum along `realCliffordMiddleSwapIsometry p q` swaps the middle two blocks with no sign. -/
theorem spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinBlockSum (p q : ℕ)
    (x₁ x₃ : realCliffordSpinGroupZero p) (x₂ x₄ : realCliffordSpinGroupZero q) :
    (realCliffordMiddleSwapIsometry p q).spinGroupEquiv
        (realCliffordSpinBlockSum (p + q) (p + q)
          (realCliffordSpinBlockSum p q (x₁, x₂), realCliffordSpinBlockSum p q (x₃, x₄))) =
      realCliffordSpinBlockSum (p + p) (q + q)
        (realCliffordSpinBlockSum p p (x₁, x₃), realCliffordSpinBlockSum q q (x₂, x₄)) := by
  simp only [realCliffordMiddleSwapIsometry, realCliffordSpinBlockSum_apply,
    IsometryEquiv.spinGroupEquiv_trans, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, spinGroupEquiv_prod_spinGroupProd,
    ← IsometryEquiv.spinGroupEquiv_symm, spinGroupEquiv_prodProdProdComm_spinGroupProd]

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Ordered direct-sum coherence of `realCliffordSpinDiagonalLift`**: transporting the diagonal
Spin lift of a block sum `(g₁, g₂) ∈ SO(p) × SO(q)` along `realCliffordMiddleSwapIsometry p q`
gives the Spin block sum of `realCliffordSpinDiagonalLift p g₁` and
`realCliffordSpinDiagonalLift q g₂`, with no sign. -/
theorem spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinDiagonalLift (p q : ℕ)
    (g₁ : specialOrthogonalGroup (realCliffordForm p 0))
    (g₂ : specialOrthogonalGroup (realCliffordForm q 0)) :
    (realCliffordMiddleSwapIsometry p q).spinGroupEquiv
        (realCliffordSpinDiagonalLift (p + q)
          (realCliffordSpecialOrthogonalBlockSum p q (g₁, g₂))) =
      realCliffordSpinBlockSum (p + p) (q + q)
        (realCliffordSpinDiagonalLift p g₁, realCliffordSpinDiagonalLift q g₂) := by
  obtain ⟨x₁, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm p 0) (posDef_realCliffordForm_zero p) g₁
  obtain ⟨x₂, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm q 0) (posDef_realCliffordForm_zero q) g₂
  rw [← spinToSpecialOrthogonal_realCliffordSpinBlockSum p q (x₁, x₂),
    realCliffordSpinDiagonalLift_spinToSpecialOrthogonal,
    realCliffordSpinDiagonalLift_spinToSpecialOrthogonal,
    realCliffordSpinDiagonalLift_spinToSpecialOrthogonal,
    spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinBlockSum]

/-- **Middle-block exchange coherence of `realCliffordSpecialOrthogonalBlockSum`**: transporting a
four-block special-orthogonal sum along `realCliffordMiddleSwapIsometry p q` swaps the middle two
blocks. -/
@[simp]
theorem specialOrthogonalGroupCongr_realCliffordMiddleSwapIsometry_blockSum (p q : ℕ)
    (g₁ g₃ : specialOrthogonalGroup (realCliffordForm p 0))
    (g₂ g₄ : specialOrthogonalGroup (realCliffordForm q 0)) :
    (realCliffordMiddleSwapIsometry p q).specialOrthogonalGroupCongr
        (realCliffordSpecialOrthogonalBlockSum (p + q) (p + q)
          (realCliffordSpecialOrthogonalBlockSum p q (g₁, g₂),
            realCliffordSpecialOrthogonalBlockSum p q (g₃, g₄))) =
      realCliffordSpecialOrthogonalBlockSum (p + p) (q + q)
        (realCliffordSpecialOrthogonalBlockSum p p (g₁, g₃),
          realCliffordSpecialOrthogonalBlockSum q q (g₂, g₄)) := by
  obtain ⟨x₁, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm p 0) (posDef_realCliffordForm_zero p) g₁
  obtain ⟨x₂, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm q 0) (posDef_realCliffordForm_zero q) g₂
  obtain ⟨x₃, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm p 0) (posDef_realCliffordForm_zero p) g₃
  obtain ⟨x₄, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm q 0) (posDef_realCliffordForm_zero q) g₄
  rw [← spinToSpecialOrthogonal_realCliffordSpinBlockSum p q (x₁, x₂),
    ← spinToSpecialOrthogonal_realCliffordSpinBlockSum p q (x₃, x₄),
    ← spinToSpecialOrthogonal_realCliffordSpinBlockSum (p + q) (p + q)
      (realCliffordSpinBlockSum p q (x₁, x₂), realCliffordSpinBlockSum p q (x₃, x₄)),
    IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinBlockSum,
    spinToSpecialOrthogonal_realCliffordSpinBlockSum,
    spinToSpecialOrthogonal_realCliffordSpinBlockSum,
    spinToSpecialOrthogonal_realCliffordSpinBlockSum]

end

end TauCeti
