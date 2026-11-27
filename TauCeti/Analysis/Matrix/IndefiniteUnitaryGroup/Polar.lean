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
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Polar and Cartan decomposition in indefinite unitary groups

Let `𝕜` be `ℝ` or `ℂ` (`[RCLike 𝕜]`). For any matrix `J : Matrix n n 𝕜` and any Hermitian matrix
`X : Matrix n n 𝕜`, the exponential `exp X` preserves `J` (`star (exp X) * J * exp X = J`) if and
only if `J * X + X * J = 0` (`Matrix.IsHermitian.star_exp_mul_mul_exp_eq_iff`). Consequently,
`t ↦ exp (t • X)` remains in `unitaryGroupOf J` whenever `exp X` does.

When `J` is an involution (`J * J = 1`), such as
`J = diag(1, …, 1, -1, …, -1)` for `U(p, q)` or `O(p, q)`, the indefinite unitary group
`Matrix.unitaryGroupOf J` is closed under conjugate transpose
(`Matrix.star_mem_unitaryGroupOf_iff_of_mul_self_eq_one`), and `Subgroup.cartanHomeomorph` yields
the global Cartan decomposition `Matrix.unitaryGroupOf.cartanHomeomorph`: every
`g ∈ unitaryGroupOf J` factors uniquely as `g = k * exp X` with
`k ∈ unitaryGroupOf J ∩ unitaryGroup n 𝕜` and `X` Hermitian anticommuting with `J` (so `exp X` is
positive definite and lies in `unitaryGroupOf J`).

For `TauCeti.Matrix.indefiniteUnitaryGroup p q 𝕜`, the maximal compact intersection with the
unitary group is precisely the block-diagonal subgroup `U(p) × U(q)` (the range of
`fromBlocksHom p q 𝕜`), giving
`TauCeti.Matrix.indefiniteUnitaryGroup.existsUnique_fromBlocksHom_mul_exp`.

## Main definitions and results

* `Matrix.unitaryGroupOf.cartanHomeomorph`, `Matrix.unitaryGroupOf.val_cartanHomeomorph_apply`,
  `Matrix.unitaryGroupOf.coe_cartanHomeomorph_symm_apply_fst`,
  `Matrix.unitaryGroupOf.coe_cartanHomeomorph_symm_apply_snd`,
  `Matrix.unitaryGroupOf.existsUnique_unitary_mul_exp`: global Cartan homeomorphism and unique
  polar factorization in `unitaryGroupOf J`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.existsUnique_fromBlocksHom_mul_exp`: unique polar
  factorization in `U(p, q)` and `O(p, q)` with block-diagonal unitary factor in `U(p) × U(q)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Chapter VI, §1.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer, 2015, §2.5.
* Adapted from `src/Lib/General/LinearAlgebra/PolarDecomposition.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC), generalized
  from complex sign matrices to arbitrary involutions `J * J = 1` over `ℝ` or `ℂ` (`[RCLike 𝕜]`).
-/

public section

noncomputable section

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.unitaryGroupOf

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

private lemma expUnit_mem_unitaryGroupOf_iff {J X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    TauCeti.expUnit X ∈ unitaryGroupOf J ↔ J * X + X * J = 0 := by
  rw [mem_unitaryGroupOf_iff, TauCeti.expUnit_coe, hX.star_exp_mul_mul_exp_eq_iff J]

private lemma expUnit_smul_mem_of_mem {J : Matrix n n 𝕜} (X : Matrix n n 𝕜) (hX : IsSelfAdjoint X)
    (hmem : TauCeti.expUnit X ∈ unitaryGroupOf J) (t : ℝ) :
    TauCeti.expUnit (t • X) ∈ unitaryGroupOf J := by
  have hanti : J * X + X * J = 0 :=
    (expUnit_mem_unitaryGroupOf_iff (isHermitian_iff_isSelfAdjoint.2 hX)).1 hmem
  have htX : (t • X).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 ((IsSelfAdjoint.all t).smul hX)
  rw [expUnit_mem_unitaryGroupOf_iff htX, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hanti,
    smul_zero]

private lemma forall_expUnit_smul_mem_iff {J : Matrix n n 𝕜} (X : selfAdjoint (Matrix n n 𝕜)) :
    (∀ t : ℝ, TauCeti.expUnit (t • (X : Matrix n n 𝕜)) ∈ unitaryGroupOf J) ↔
      J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0 := by
  have hX' : (X : Matrix n n 𝕜).IsHermitian := isHermitian_iff_isSelfAdjoint.2 X.property
  refine ⟨fun h ↦ (expUnit_mem_unitaryGroupOf_iff hX').1 (by simpa using h 1),
    fun h t ↦ expUnit_smul_mem_of_mem _ X.property ((expUnit_mem_unitaryGroupOf_iff hX').2 h) t⟩

/-- **Global Cartan decomposition of `unitaryGroupOf J`** for an involution `J` over `ℝ` or `ℂ`:
the map `(k, X) ↦ k * exp X` is a homeomorphism from the product of
`unitaryGroupOf J ∩ unitaryGroup n 𝕜` and the Hermitian matrices anticommuting with `J` onto
`unitaryGroupOf J`. -/
def cartanHomeomorph {J : Matrix n n 𝕜} (hJ_sq : J * J = 1) :
    {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ unitaryGroupOf J} ×
      {X : selfAdjoint (Matrix n n 𝕜) //
        J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0} ≃ₜ
      unitaryGroupOf J :=
  (Homeomorph.prodCongr (Homeomorph.refl _)
      (Homeomorph.setCongr
        (s := {X : selfAdjoint (Matrix n n 𝕜) |
          J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0})
        (t := {X : selfAdjoint (Matrix n n 𝕜) |
          ∀ t : ℝ, TauCeti.expUnit (t • (X : Matrix n n 𝕜)) ∈ unitaryGroupOf J})
        (Set.ext fun X ↦ (forall_expUnit_smul_mem_iff X).symm))).trans
    ((unitaryGroupOf J).cartanHomeomorph
      (fun _ hg ↦ (star_mem_unitaryGroupOf_iff_of_mul_self_eq_one hJ_sq).2 hg)
      expUnit_smul_mem_of_mem)

/-- The Cartan homeomorphism of `unitaryGroupOf J` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorph_apply {J : Matrix n n 𝕜} (hJ_sq : J * J = 1)
    (p : {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ unitaryGroupOf J} ×
      {X : selfAdjoint (Matrix n n 𝕜) //
        J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0}) :
    ((cartanHomeomorph hJ_sq p : GL n 𝕜) : Matrix n n 𝕜) =
      (p.1.val : Matrix n n 𝕜) * exp (p.2.val : Matrix n n 𝕜) := by
  rw [cartanHomeomorph, Homeomorph.trans_apply, Subgroup.val_cartanHomeomorph_apply]
  simp

/-- The unitary factor of the Cartan decomposition of `g ∈ unitaryGroupOf J` is its polar unitary
factor. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_fst {J : Matrix n n 𝕜} (hJ_sq : J * J = 1)
    (g : unitaryGroupOf J) :
    (((cartanHomeomorph hJ_sq).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary := by
  simpa [cartanHomeomorph] using Subgroup.coe_cartanHomeomorph_symm_apply_fst _ _ g

/-- The Hermitian factor of the Cartan decomposition of `g ∈ unitaryGroupOf J` is
`log √(g⋆ g)`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_snd {J : Matrix n n 𝕜} (hJ_sq : J * J = 1)
    (g : unitaryGroupOf J) :
    ((((cartanHomeomorph hJ_sq).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
      Matrix n n 𝕜) =
      CFC.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  simpa [cartanHomeomorph] using Subgroup.coe_cartanHomeomorph_symm_apply_snd _ _ g

/-- **Unique polar decomposition in `unitaryGroupOf J`** for an involution `J` over `ℝ` or `ℂ`:
every `g : unitaryGroupOf J` factors uniquely as `g = k * exp X` with `k` unitary in
`unitaryGroupOf J` and `X` Hermitian anticommuting with `J` (so `exp X` is positive definite). -/
theorem existsUnique_unitary_mul_exp {J : Matrix n n 𝕜} (hJ_sq : J * J = 1)
    (g : unitaryGroupOf J) :
    ∃! p : {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ unitaryGroupOf J} ×
        {X : selfAdjoint (Matrix n n 𝕜) //
          J * (X : Matrix n n 𝕜) + (X : Matrix n n 𝕜) * J = 0},
      ((g : GL n 𝕜) : Matrix n n 𝕜) =
        (p.1.val : Matrix n n 𝕜) * exp (p.2.val : Matrix n n 𝕜) := by
  refine (existsUnique_congr fun p ↦ ?_).1
    ((cartanHomeomorph hJ_sq).bijective.existsUnique g)
  rw [Subtype.ext_iff, Units.ext_iff, val_cartanHomeomorph_apply, eq_comm]

end Matrix.unitaryGroupOf

namespace TauCeti.Matrix.indefiniteUnitaryGroup

open LieAlgebra.Orthogonal

variable {p q 𝕜 : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [RCLike 𝕜]

/-- **Polar decomposition in `U(p, q)` (and `O(p, q)`):** every `g ∈ indefiniteUnitaryGroup p q 𝕜`
factors uniquely as `g = fromBlocksHom p q 𝕜 (u, v) * exp X` where `u ∈ U(p)`, `v ∈ U(q)`, and `X`
is a Hermitian matrix anticommuting with `indefiniteDiagonal p q 𝕜` (so `exp X` is positive
definite and lies in `indefiniteUnitaryGroup p q 𝕜`). -/
theorem existsUnique_fromBlocksHom_mul_exp (g : indefiniteUnitaryGroup p q 𝕜) :
    ∃! x : (unitaryGroup p 𝕜 × unitaryGroup q 𝕜) ×
        {X : selfAdjoint (Matrix (p ⊕ q) (p ⊕ q) 𝕜) //
          indefiniteDiagonal p q 𝕜 * (X : Matrix (p ⊕ q) (p ⊕ q) 𝕜) +
            (X : Matrix (p ⊕ q) (p ⊕ q) 𝕜) * indefiniteDiagonal p q 𝕜 = 0},
      ((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) =
        ((fromBlocksHom p q 𝕜 x.1 : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) *
          exp (x.2.val : Matrix (p ⊕ q) (p ⊕ q) 𝕜) := by
  obtain ⟨⟨⟨u, hu⟩, X⟩, hgx, huniq⟩ :=
    Matrix.unitaryGroupOf.existsUnique_unitary_mul_exp
      (indefiniteDiagonal_mul_indefiniteDiagonal (p := p) (q := q) (R := 𝕜)) g
  have hmem : (⟨Unitary.toUnits u, hu⟩ : indefiniteUnitaryGroup p q 𝕜) ∈
      (fromBlocksHom p q 𝕜).range :=
    (mem_range_fromBlocksHom_iff_mem_unitaryGroup
      (fun _ _ h ↦ mul_left_cancel₀ (two_ne_zero (α := 𝕜)) h) _).2 u.property
  obtain ⟨uv, huv⟩ := hmem
  have hval : ((fromBlocksHom p q 𝕜 uv : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) =
      (u : Matrix (p ⊕ q) (p ⊕ q) 𝕜) :=
    congrArg (fun a : indefiniteUnitaryGroup p q 𝕜 ↦
      ((a : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜)) huv
  refine ⟨⟨uv, X⟩, by dsimp only; rw [hval]; exact hgx, ?_⟩
  rintro ⟨uv', X'⟩ h'
  have htoUnits : Unitary.toUnits (UnitaryGroup.sum uv') = (fromBlocksHom p q 𝕜 uv' : GL _ _) := by
    apply Units.ext
    rw [Unitary.val_toUnits_apply, UnitaryGroup.coe_sum, val_fromBlocksHom]
  have hu' : Unitary.toUnits (UnitaryGroup.sum uv') ∈ indefiniteUnitaryGroup p q 𝕜 := by
    rw [htoUnits]
    exact (fromBlocksHom p q 𝕜 uv').property
  have h'sum : ((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) =
      (UnitaryGroup.sum uv' : Matrix (p ⊕ q) (p ⊕ q) 𝕜) *
        exp (X'.val : Matrix (p ⊕ q) (p ⊕ q) 𝕜) := by
    simpa only [UnitaryGroup.coe_sum, ← val_fromBlocksHom] using h'
  have heq := huniq ⟨⟨UnitaryGroup.sum uv', hu'⟩, X'⟩ h'sum
  have hfst : UnitaryGroup.sum uv' = u := congrArg (fun a ↦ a.1.val) heq
  have hsnd : X' = X := congrArg Prod.snd heq
  have huv_eq : uv' = uv := fromBlocksHom_injective (by
    apply Matrix.unitaryGroupOf.ext
    rw [hval, val_fromBlocksHom, ← UnitaryGroup.coe_sum]
    exact congrArg Subtype.val hfst)
  exact Prod.ext huv_eq hsnd

end TauCeti.Matrix.indefiniteUnitaryGroup

end
