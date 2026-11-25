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

Specializing `CliffordAlgebra.diagSpinLift` to the positive-definite real form
`realCliffordForm k 0` and transporting along `(realCliffordSplitIsometry k k 0 0).symm` produces
the compact real diagonal Spin lift

`TauCeti.realCliffordSpinDiagonalLift k : SO(k) →* Spin(k + k)`

lifting the diagonal block embedding `g ↦ realCliffordSpecialOrthogonalBlockSum k k (g, g)`.

This module establishes the algebraic properties of `realCliffordSpinDiagonalLift`:
* Compatibility with `realCliffordSpinBlockSum` and `spinToSpecialOrthogonal`, diagonal vector
  action on `Fin.append u v`, and injectivity.
* Low-rank checks: in ranks `0` and `1`, `SO(k)` is trivial and `realCliffordSpinDiagonalLift k`
  is constantly `1`.
* Block-swap invariance and ordered direct-sum coherence: `realCliffordBlockSwapIsometry k k`
  fixes `realCliffordSpinDiagonalLift k g`, and the middle-block exchange
  `TauCeti.realCliffordMiddleSwapIsometry p q` intertwines `realCliffordSpinDiagonalLift (p + q)`
  applied to a block sum `(g₁, g₂)` with the Spin block sum of `realCliffordSpinDiagonalLift p g₁`
  and `realCliffordSpinDiagonalLift q g₂`.

## Main definitions

* `TauCeti.realCliffordSpinDiagonalLift`: the canonical homomorphism `SO(k) →* Spin(k + k)`
  lifting `g ↦ diag(g, g)`.

## Main results

* `TauCeti.realCliffordSpinDiagonalLift_spinToSpecialOrthogonal`,
  `TauCeti.eq_realCliffordSpinDiagonalLift_of_comp_spinToSpecialOrthogonal`,
  `TauCeti.spinToSpecialOrthogonal_realCliffordSpinDiagonalLift`,
  `TauCeti.spinVectorAction_realCliffordSpinDiagonalLift_append`, and
  `TauCeti.realCliffordSpinDiagonalLift_injective`: characterizing equations, algebraic descent
  uniqueness, and injectivity.
* `TauCeti.realCliffordSpinDiagonalLift_zero` and `TauCeti.realCliffordSpinDiagonalLift_one`:
  low-rank triviality in ranks `0` and `1`.
* `TauCeti.realCliffordSpinDiagonalLift_congr`,
  `TauCeti.realCliffordSpinDiagonalLift_zero_add`,
  `TauCeti.spinGroupEquiv_realCliffordBlockSwapIsometry_realCliffordSpinDiagonalLift`, and
  `TauCeti.spinGroupEquiv_realCliffordMiddleSwapIsometry_realCliffordSpinDiagonalLift`: rank
  congruence (including left-unit transport from `0 + k` to `k`), block-swap invariance, and
  ordered direct-sum coherence of `realCliffordSpinDiagonalLift`.

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
    (diagSpinLift (realCliffordForm k 0) (nondegenerate_realCliffordForm k 0)
      (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero k)))

/-- `realCliffordSpinDiagonalLift` is `diagSpinLift` transported along
`(realCliffordSplitIsometry k k 0 0).symm`. -/
theorem realCliffordSpinDiagonalLift_apply (k : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm k 0)) :
    realCliffordSpinDiagonalLift k g =
      (realCliffordSplitIsometry k k 0 0).symm.spinGroupEquiv
        (diagSpinLift (realCliffordForm k 0) (nondegenerate_realCliffordForm k 0)
          (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero k)) g) :=
  (rfl)

/-- Evaluating `realCliffordSpinDiagonalLift` on the projection of `x ∈ Spin(k)` gives the diagonal
block sum `realCliffordSpinBlockSum k k (x, x)`. -/
@[simp]
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal (k : ℕ)
    (x : realCliffordSpinGroupZero k) :
    realCliffordSpinDiagonalLift k (spinToSpecialOrthogonal (realCliffordForm k 0) x) =
      realCliffordSpinBlockSum k k (x, x) := by
  rw [realCliffordSpinDiagonalLift_apply, diagSpinLift_spinToSpecialOrthogonal,
    realCliffordSpinBlockSum_apply]

/-- **Algebraic descent uniqueness for `realCliffordSpinDiagonalLift`**: any homomorphism
`SO(k) →* Spin(k + k)` agreeing with `x ↦ realCliffordSpinBlockSum k k (x, x)` after
precomposition with `spinToSpecialOrthogonal` equals `realCliffordSpinDiagonalLift k`. -/
theorem eq_realCliffordSpinDiagonalLift_of_comp_spinToSpecialOrthogonal (k : ℕ)
    (f : specialOrthogonalGroup (realCliffordForm k 0) →* realCliffordSpinGroupZero (k + k))
    (hf : ∀ x : realCliffordSpinGroupZero k,
      f (spinToSpecialOrthogonal (realCliffordForm k 0) x) =
        realCliffordSpinBlockSum k k (x, x)) :
    f = realCliffordSpinDiagonalLift k := by
  refine MonoidHom.ext fun g ↦ ?_
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm k 0) (posDef_realCliffordForm_zero k) g
  rw [hf, realCliffordSpinDiagonalLift_spinToSpecialOrthogonal]

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
    spinToSpecialOrthogonal_diagSpinLift, realCliffordSpecialOrthogonalBlockSum_apply]

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
    (diagSpinLift_injective _ _)

/-! ### Low-rank checks -/

/-- In rank zero, `realCliffordSpinDiagonalLift 0` is constantly `1`. -/
@[simp]
theorem realCliffordSpinDiagonalLift_zero
    (g : specialOrthogonalGroup (realCliffordForm 0 0)) :
    realCliffordSpinDiagonalLift 0 g = 1 := by
  rw [realCliffordSpinDiagonalLift_apply,
    diagSpinLift_eq_one_of_finrank_le_one _ _ (by simp), map_one]

/-- In rank one, `SO(1)` is trivial and `realCliffordSpinDiagonalLift 1` is constantly `1` in
`Spin(2)`. -/
@[simp]
theorem realCliffordSpinDiagonalLift_one
    (g : specialOrthogonalGroup (realCliffordForm 1 0)) :
    realCliffordSpinDiagonalLift 1 g = 1 := by
  rw [realCliffordSpinDiagonalLift_apply,
    diagSpinLift_eq_one_of_finrank_le_one _ _ (by simp), map_one]

/-! ### Block-swap invariance and ordered direct-sum coherence -/

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Rank-congruence naturality of `realCliffordSpinDiagonalLift`**: transporting along an
equality `hk : k₁ = k₂` via `realCliffordFormCongr` on source and target commutes with
`realCliffordSpinDiagonalLift`. -/
theorem realCliffordSpinDiagonalLift_congr {k₁ k₂ : ℕ} (hk : k₁ = k₂)
    (g : specialOrthogonalGroup (realCliffordForm k₁ 0)) :
    (realCliffordFormCongr (congrArg₂ (· + ·) hk hk) rfl).spinGroupEquiv
        (realCliffordSpinDiagonalLift k₁ g) =
      realCliffordSpinDiagonalLift k₂
        ((realCliffordFormCongr hk rfl).specialOrthogonalGroupCongr g) := by
  subst hk
  have hcongr (m : ℕ) : realCliffordFormCongr (rfl : m = m) (rfl : (0 : ℕ) = 0) =
      QuadraticMap.IsometryEquiv.refl (realCliffordForm m 0) :=
    DFunLike.ext _ _ fun _ ↦ funext fun _ ↦ by
      rw [realCliffordFormCongr_apply, QuadraticMap.IsometryEquiv.refl_apply]
      rfl
  rw [hcongr k₁, hcongr (k₁ + k₁), IsometryEquiv.spinGroupEquiv_refl,
    IsometryEquiv.specialOrthogonalGroupCongr_refl, MulEquiv.refl_apply, MulEquiv.refl_apply]

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Left-unit rank transport for `realCliffordSpinDiagonalLift`**: transporting from rank `0 + k`
to rank `k` via `realCliffordFormCongr (Nat.zero_add k) rfl` commutes with the diagonal lift (the
right-unit rank equality `k + 0 = k` is definitional). -/
theorem realCliffordSpinDiagonalLift_zero_add (k : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm (0 + k) 0)) :
    (realCliffordFormCongr (congrArg₂ (· + ·) (Nat.zero_add k) (Nat.zero_add k)) rfl).spinGroupEquiv
        (realCliffordSpinDiagonalLift (0 + k) g) =
      realCliffordSpinDiagonalLift k
        ((realCliffordFormCongr (Nat.zero_add k) rfl).specialOrthogonalGroupCongr g) :=
  realCliffordSpinDiagonalLift_congr (Nat.zero_add k) g

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
