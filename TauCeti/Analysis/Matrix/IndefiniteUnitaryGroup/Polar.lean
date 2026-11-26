/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Cartan
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Matrix.Exponential.Log

/-!
# Polar and Cartan decomposition in indefinite unitary groups

Let `𝕜` be `ℝ` or `ℂ` (`[RCLike 𝕜]`) and let `J : Matrix n n 𝕜` be a Hermitian involution
(`J.IsHermitian` and `J * J = 1`), such as `J = diag(1, …, 1, -1, …, -1)` for `U(p, q)` or
`O(p, q)`.

The indefinite unitary group `Matrix.unitaryGroupOf J` is closed under conjugate transpose and, for
every Hermitian matrix `X`, the exponential `exp X` preserves `J` (`star (exp X) * J * exp X = J`)
if and only if `J * X + X * J = 0`. Consequently, `t ↦ exp (t • X)` remains in `unitaryGroupOf J`
whenever `exp X` does, and `Subgroup.cartanHomeomorph` yields the global Cartan decomposition
`Matrix.unitaryGroupOf.cartanHomeomorph`: every `g ∈ unitaryGroupOf J` factors uniquely as
`g = k * exp X` with `k ∈ unitaryGroupOf J ∩ unitaryGroup n 𝕜` and `X` Hermitian anticommuting
with `J` (so `exp X` is positive definite and lies in `unitaryGroupOf J`).

For `TauCeti.Matrix.indefiniteUnitaryGroup p q 𝕜`, the maximal compact intersection with the
unitary group is precisely the block-diagonal subgroup `U(p) × U(q)` (the range of
`fromBlocksHom p q 𝕜`), giving `TauCeti.Matrix.indefiniteUnitaryGroup.existsUnique_polar`.

## Main definitions and results

* `Matrix.unitaryGroupOf.star_mem_of_mul_self_eq_one`: for `J * J = 1`, `unitaryGroupOf J` is
  closed under `star`.
* `Matrix.unitaryGroupOf.star_exp_mul_mul_exp_eq_iff`: for Hermitian `X`,
  `star (exp X) * J * exp X = J ↔ J * X + X * J = 0`.
* `Matrix.unitaryGroupOf.cartanHomeomorph`, `Matrix.unitaryGroupOf.val_cartanHomeomorph_apply`,
  `Matrix.unitaryGroupOf.existsUnique_polar`: global Cartan homeomorphism and unique polar
  factorization in `unitaryGroupOf J`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.mem_range_fromBlocksHom_iff_mem_unitaryGroup`,
  `TauCeti.Matrix.indefiniteUnitaryGroup.existsUnique_polar`: identifies `U(p, q) ∩ U(p ⊕ q)`
  with `U(p) × U(q)` and yields unique polar factorization in `U(p, q)` and `O(p, q)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Chapter VI, §1.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer, 2015, §2.5.
* Adapted from `src/Lib/General/LinearAlgebra/PolarDecomposition.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC), generalized
  from complex sign matrices to arbitrary Hermitian involutions over `ℝ` or `ℂ` (`[RCLike 𝕜]`).
-/

public section

noncomputable section

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder

namespace Matrix.unitaryGroupOf

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- If `J * J = 1`, then `unitaryGroupOf J` is closed under conjugate transpose (`star`). -/
theorem star_mem_of_mul_self_eq_one {J : Matrix n n 𝕜} (hJ_sq : J * J = 1) {g : GL n 𝕜}
    (hg : g ∈ unitaryGroupOf J) : star g ∈ unitaryGroupOf J := by
  have hJ_unit : IsUnit J := isUnit_iff_exists_inv.2 ⟨J, hJ_sq⟩
  have hJ_inv : J⁻¹ = J := inv_eq_left_inv hJ_sq
  simpa only [hJ_inv] using (star_mem_unitaryGroupOf_inv_iff hJ_unit).2 hg

/-- For a Hermitian involution `J` and a Hermitian matrix `X`, the exponential `exp X` preserves
the form `J` if and only if `J * X + X * J = 0`. -/
theorem star_exp_mul_mul_exp_eq_iff {J X : Matrix n n 𝕜} (hJ_herm : J.IsHermitian)
    (hJ_sq : J * J = 1) (hX : X.IsHermitian) :
    star (exp X) * J * exp X = J ↔ J * X + X * J = 0 := by
  open scoped Matrix.Norms.L2Operator in
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  let uJ : (Matrix n n 𝕜)ˣ := ⟨J, J, hJ_sq, hJ_sq⟩
  have hJXJ_herm : (J * X * J).IsHermitian := by
    simpa only [hJ_herm.eq] using isHermitian_conjTranspose_mul_mul J hX
  have hexp_star : star (exp X) = exp X := by
    rw [star_eq_conjTranspose, ← exp_conjTranspose, hX.eq]
  have hexp_conj : J * exp X * J = exp (J * X * J) :=
    (NormedSpace.exp_units_conj uJ X).symm
  have hexp_mul_neg : exp X * exp (-X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl X).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  rw [hexp_star]
  constructor
  · intro h
    have hmul_one : J * exp X * J * exp X = 1 := by
      rw [Matrix.mul_assoc J (exp X) J, Matrix.mul_assoc J, h, hJ_sq]
    have heq : exp (J * X * J) = exp (-X) := by
      calc exp (J * X * J)
          = exp (J * X * J) * (exp X * exp (-X)) := by rw [hexp_mul_neg, Matrix.mul_one]
        _ = (J * exp X * J * exp X) * exp (-X) := by
            rw [← hexp_conj]
            simp only [Matrix.mul_assoc]
        _ = exp (-X) := by rw [hmul_one, Matrix.one_mul]
    have hX_anti : J * X * J = -X := (hJXJ_herm.exp_eq_exp_iff hX.neg).1 heq
    calc J * X + X * J = (J * X * J) * J + X * J := by rw [Matrix.mul_assoc, hJ_sq, Matrix.mul_one]
      _ = (-X) * J + X * J := by rw [hX_anti]
      _ = 0 := by simp
  · intro h
    have hX_anti : J * X * J = -X := by
      have h' : X * J = -(J * X) := eq_neg_of_add_eq_zero_right h
      calc J * X * J = J * -(J * X) := by rw [Matrix.mul_assoc, h']
        _ = -(J * J * X) := by rw [mul_neg, Matrix.mul_assoc]
        _ = -X := by rw [hJ_sq, Matrix.one_mul]
    have h1 : J * exp X * J = exp (-X) := by rw [hexp_conj, hX_anti]
    calc exp X * J * exp X = (exp X * (J * exp X * J)) * J := by
          simp only [Matrix.mul_assoc, hJ_sq, Matrix.mul_one]
      _ = (exp X * exp (-X)) * J := by rw [h1]
      _ = J := by rw [hexp_mul_neg, Matrix.one_mul]

/-- **Global Cartan decomposition of `unitaryGroupOf J`** for a Hermitian involution `J` over `ℝ`
or `ℂ`: the map `(k, X) ↦ k * exp X` is a homeomorphism from the product of
`unitaryGroupOf J ∩ unitaryGroup n 𝕜` and the Hermitian matrices anticommuting with `J` onto
`unitaryGroupOf J`. -/
def cartanHomeomorph {J : Matrix n n 𝕜} (hJ_herm : J.IsHermitian) (hJ_sq : J * J = 1) :
    {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ unitaryGroupOf J} ×
      {X : selfAdjoint (Matrix n n 𝕜) //
        J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0} ≃ₜ
      unitaryGroupOf J := by
  open scoped Matrix.Norms.L2Operator in
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  letI : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  have hstar : ∀ g ∈ unitaryGroupOf J, star g ∈ unitaryGroupOf J :=
    fun _ hg ↦ star_mem_of_mul_self_eq_one hJ_sq hg
  have hexp_mem (X : Matrix n n 𝕜) (hX : X.IsHermitian) :
      TauCeti.expUnit X ∈ unitaryGroupOf J ↔ J * X + X * J = 0 := by
    rw [mem_unitaryGroupOf_iff, TauCeti.expUnit_coe, star_exp_mul_mul_exp_eq_iff hJ_herm hJ_sq hX]
  have hexp : ∀ X : Matrix n n 𝕜, IsSelfAdjoint X → TauCeti.expUnit X ∈ unitaryGroupOf J →
      ∀ t : ℝ, TauCeti.expUnit (t • X) ∈ unitaryGroupOf J := by
    intro X hX hmem t
    have hX' : X.IsHermitian := isHermitian_iff_isSelfAdjoint.2 hX
    have hanti : J * X + X * J = 0 := (hexp_mem X hX').1 hmem
    have htX : (t • X).IsHermitian := isHermitian_iff_isSelfAdjoint.2 (by
      rw [IsSelfAdjoint, star_smul, star_trivial, hX.star_eq])
    refine (hexp_mem (t • X) htX).2 ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hanti, smul_zero]
  have hiff (X : selfAdjoint (Matrix n n 𝕜)) :
      (∀ t : ℝ, TauCeti.expUnit (t • (X : Matrix n n 𝕜)) ∈ unitaryGroupOf J) ↔
        J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0 := by
    have hX' : (X : Matrix n n 𝕜).IsHermitian := isHermitian_iff_isSelfAdjoint.2 X.property
    refine ⟨fun h ↦ (hexp_mem _ hX').1 (by simpa using h 1),
      fun h t ↦ hexp _ X.property ((hexp_mem _ hX').2 h) t⟩
  let e₂ : {X : selfAdjoint (Matrix n n 𝕜) //
        J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0} ≃ₜ
      {X : selfAdjoint (Matrix n n 𝕜) //
        ∀ t : ℝ, TauCeti.expUnit (t • (X : Matrix n n 𝕜)) ∈ unitaryGroupOf J} :=
    { toFun := fun ⟨X, hX⟩ ↦ ⟨X, (hiff X).2 hX⟩
      invFun := fun ⟨X, hX⟩ ↦ ⟨X, (hiff X).1 hX⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_induced_rng.2 continuous_induced_dom
      continuous_invFun := continuous_induced_rng.2 continuous_induced_dom }
  exact (Homeomorph.prodCongr (Homeomorph.refl _) e₂).trans
    ((unitaryGroupOf J).cartanHomeomorph hstar hexp)

/-- The Cartan homeomorphism of `unitaryGroupOf J` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorph_apply {J : Matrix n n 𝕜} (hJ_herm : J.IsHermitian) (hJ_sq : J * J = 1)
    (p : {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ unitaryGroupOf J} ×
      {X : selfAdjoint (Matrix n n 𝕜) //
        J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0}) :
    ((cartanHomeomorph hJ_herm hJ_sq p : GL n 𝕜) : Matrix n n 𝕜) =
      (p.1.val : Matrix n n 𝕜) * exp (p.2.val : Matrix n n 𝕜) := by
  open scoped Matrix.Norms.L2Operator in
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  dsimp [cartanHomeomorph]
  exact (unitaryGroupOf J).val_cartanHomeomorph_apply _ _ _

/-- **Unique polar decomposition in `unitaryGroupOf J`** for a Hermitian involution `J` over `ℝ` or
`ℂ`: every `g : unitaryGroupOf J` factors uniquely as `g = k * exp X` with `k` unitary in
`unitaryGroupOf J` and `X` Hermitian anticommuting with `J` (so `exp X` is positive definite). -/
theorem existsUnique_polar {J : Matrix n n 𝕜} (hJ_herm : J.IsHermitian) (hJ_sq : J * J = 1)
    (g : unitaryGroupOf J) :
    ∃! p : {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ unitaryGroupOf J} ×
        {X : selfAdjoint (Matrix n n 𝕜) //
          J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0},
      ((g : GL n 𝕜) : Matrix n n 𝕜) =
        (p.1.val : Matrix n n 𝕜) * exp (p.2.val : Matrix n n 𝕜) := by
  let e := cartanHomeomorph hJ_herm hJ_sq
  refine ⟨e.symm g, ?_, ?_⟩
  · have h := congrArg (fun x : unitaryGroupOf J ↦ ((x : GL n 𝕜) : Matrix n n 𝕜))
      (e.apply_symm_apply g)
    simpa only [e, val_cartanHomeomorph_apply] using h.symm
  · intro p hp
    apply e.injective
    apply unitaryGroupOf.ext
    simpa only [e, val_cartanHomeomorph_apply, e.apply_symm_apply] using hp.symm

end Matrix.unitaryGroupOf

namespace TauCeti.Matrix.indefiniteUnitaryGroup

open LieAlgebra.Orthogonal

variable {p q 𝕜 : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [RCLike 𝕜]

/-- An element of `U(p, q)` (or `O(p, q)`) is unitary in the ambient space if and only if it lies
in the block-diagonal maximal compact subgroup `U(p) × U(q)` (the range of `fromBlocksHom`). -/
theorem mem_range_fromBlocksHom_iff_mem_unitaryGroup (g : indefiniteUnitaryGroup p q 𝕜) :
    g ∈ (fromBlocksHom p q 𝕜).range ↔
      ((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) ∈ unitaryGroup (p ⊕ q) 𝕜 := by
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    rw [val_fromBlocksHom, mem_unitaryGroup_iff', star_eq_conjTranspose, fromBlocks_conjTranspose,
      fromBlocks_multiply]
    simp [← star_eq_conjTranspose, (mem_unitaryGroup_iff').1 u.property,
      (mem_unitaryGroup_iff').1 v.property]
  · intro hU
    rw [mem_range_fromBlocksHom_iff]
    set M : Matrix (p ⊕ q) (p ⊕ q) 𝕜 := ((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜)
    set J : Matrix (p ⊕ q) (p ⊕ q) 𝕜 := indefiniteDiagonal p q 𝕜
    have hJM : Mᴴ * J * M = J := by
      simpa only [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 g.property
    have hcomm : J * M = M * J := by
      have h1 : M * Mᴴ = 1 := (mem_unitaryGroup_iff).1 hU
      calc J * M = (M * Mᴴ) * J * M := by rw [h1, Matrix.one_mul]
        _ = M * (Mᴴ * J * M) := by simp only [Matrix.mul_assoc]
        _ = M * J := by rw [hJM]
    have h21 : (J * M).toBlocks₂₁ = (M * J).toBlocks₂₁ := congrArg Matrix.toBlocks₂₁ hcomm
    have hJblock : J = fromBlocks 1 0 0 (-1) := indefiniteDiagonal_eq_fromBlocks
    rw [← fromBlocks_toBlocks M, hJblock] at h21
    simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, toBlocks_fromBlocks₂₁] at h21
    have h2 : (2 : 𝕜) • M.toBlocks₂₁ = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.1 h21.symm
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- **Polar decomposition in `U(p, q)` (and `O(p, q)`):** every `g ∈ indefiniteUnitaryGroup p q 𝕜`
factors uniquely as `g = fromBlocksHom p q 𝕜 (u, v) * exp X` where `u ∈ U(p)`, `v ∈ U(q)`, and `X`
is a Hermitian matrix anticommuting with `indefiniteDiagonal p q 𝕜` (so `exp X` is positive
definite and lies in `indefiniteUnitaryGroup p q 𝕜`). -/
theorem existsUnique_polar (g : indefiniteUnitaryGroup p q 𝕜) :
    ∃! x : (unitaryGroup p 𝕜 × unitaryGroup q 𝕜) ×
        {X : selfAdjoint (Matrix (p ⊕ q) (p ⊕ q) 𝕜) //
          indefiniteDiagonal p q 𝕜 * (X : Matrix (p ⊕ q) (p ⊕ q) 𝕜) +
            (X : Matrix (p ⊕ q) (p ⊕ q) 𝕜) * indefiniteDiagonal p q 𝕜 = 0},
      ((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) =
        ((fromBlocksHom p q 𝕜 x.1 : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) *
          exp (x.2.val : Matrix (p ⊕ q) (p ⊕ q) 𝕜) := by
  obtain ⟨⟨⟨u, hu⟩, X⟩, hgx, huniq⟩ :=
    Matrix.unitaryGroupOf.existsUnique_polar
      (isHermitian_indefiniteDiagonal (p := p) (q := q) (R := 𝕜))
      (indefiniteDiagonal_mul_indefiniteDiagonal (p := p) (q := q) (R := 𝕜)) g
  have hmem : (⟨Unitary.toUnits u, hu⟩ : indefiniteUnitaryGroup p q 𝕜) ∈
      (fromBlocksHom p q 𝕜).range :=
    (mem_range_fromBlocksHom_iff_mem_unitaryGroup _).2 u.property
  obtain ⟨uv, huv⟩ := hmem
  refine ⟨⟨uv, X⟩, ?_, ?_⟩
  · have hval : ((fromBlocksHom p q 𝕜 uv : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) =
        (u : Matrix (p ⊕ q) (p ⊕ q) 𝕜) :=
      congrArg (fun a : indefiniteUnitaryGroup p q 𝕜 ↦
        ((a : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜)) huv
    dsimp only
    rw [hval]
    exact hgx
  · rintro ⟨uv', X'⟩ h'
    have huv'_mem : ((fromBlocksHom p q 𝕜 uv' : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) ∈
        unitaryGroup (p ⊕ q) 𝕜 :=
      (mem_range_fromBlocksHom_iff_mem_unitaryGroup _).1 (MonoidHom.mem_range.2 ⟨uv', rfl⟩)
    let u' : unitaryGroup (p ⊕ q) 𝕜 := ⟨_, huv'_mem⟩
    have hu' : Unitary.toUnits u' ∈ indefiniteUnitaryGroup p q 𝕜 := by
      convert (fromBlocksHom p q 𝕜 uv').property
      ext
      rfl
    have heq := huniq ⟨⟨u', hu'⟩, X'⟩ h'
    have hfst : u' = u := congrArg (fun a ↦ a.1.val) heq
    have hsnd : X' = X := congrArg Prod.snd heq
    have huv_eq : uv' = uv := fromBlocksHom_injective (by
      apply Matrix.unitaryGroupOf.ext
      have h1 : ((fromBlocksHom p q 𝕜 uv : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) =
          (u : Matrix (p ⊕ q) (p ⊕ q) 𝕜) :=
        congrArg (fun a : indefiniteUnitaryGroup p q 𝕜 ↦
          ((a : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜)) huv
      rw [h1]
      exact congrArg Subtype.val hfst)
    exact Prod.ext huv_eq hsnd

end TauCeti.Matrix.indefiniteUnitaryGroup

end
