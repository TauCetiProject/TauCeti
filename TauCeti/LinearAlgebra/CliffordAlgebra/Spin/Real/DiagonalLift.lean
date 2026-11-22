/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DiagonalLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization

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
* Block-swap invariance and ordered direct-sum coherence: `realCliffordBlockSwapIsometry k k`
  fixes `realCliffordSpinDiagonalLift k g`, and the middle-block exchange
  `TauCeti.realCliffordMiddleSwapIsometry p q` intertwines `realCliffordSpinDiagonalLift (p + q)` on
  a block sum `(g₁, g₂)` with the Spin block sum of `realCliffordSpinDiagonalLift p g₁` and
  `realCliffordSpinDiagonalLift q g₂`.

## Main definitions

* `TauCeti.realCliffordSpinDiagonalLift`: the canonical homomorphism `SO(k) →* Spin(k + k)`
  lifting `g ↦ diag(g, g)`.

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
* `TauCeti.spinGroupEquiv_realCliffordBlockSwapIsometry_realCliffordSpinDiagonalLift` and
  `TauCeti.spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinDiagonalLift`: block-swap
  invariance and ordered direct-sum coherence of `realCliffordSpinDiagonalLift`.

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

/-! ### Block-swap invariance and ordered direct-sum coherence -/

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

end

end TauCeti
