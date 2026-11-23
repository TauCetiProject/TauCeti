/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Products
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import TauCeti.Algebra.Lie.GeneralLinear.Basic

/-! # Surjectivity of the two adjoint-square contractions

Off-diagonal matrix units factor through the third index. The two remaining
diagonal coordinates use differences of diagonal units, since the trace is zero.
-/

public section
namespace TauCeti.AdjointSquare
open Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*}
variable [CommRing K]
local notation "𝔰" => LieAlgebra.SpecialLinear.sl (Fin 3)

open LieAlgebra.SpecialLinear (single val_single)

private def pair (i j k l : Fin 3) (h : i ≠ j) (h' : k ≠ l) : 𝔰 K ⊗[K] 𝔰 K :=
  single i j h 1 ⊗ₜ[K] single k l h' 1

private theorem diagonal_sum_zero (X : 𝔰 K) :
    X.val 0 0 + X.val 1 1 + X.val 2 2 = 0 := by
  have h : Matrix.trace X.val = 0 := LieAlgebra.SpecialLinear.mem_sl_iff.mp X.property
  rw [Matrix.trace_fin_three] at h
  exact h

/-- The six off-diagonal matrix units, scaled by the entries of `X`. -/
private def offDiagPreimage (X : 𝔰 K) : 𝔰 K ⊗[K] 𝔰 K :=
  X.val 0 1 • pair 0 2 2 1 (by decide) (by decide) +
    X.val 0 2 • pair 0 1 1 2 (by decide) (by decide) +
    X.val 1 0 • pair 1 2 2 0 (by decide) (by decide) +
    X.val 1 2 • pair 1 0 0 2 (by decide) (by decide) +
    X.val 2 0 • pair 2 1 1 0 (by decide) (by decide) +
    X.val 2 1 • pair 2 0 0 1 (by decide) (by decide)

local macro "close_fin3" h:term : tactic =>
  `(tactic| (
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [tracelessAnticommutator_def, Fintype.card_fin, Matrix.mul_apply, Matrix.trace,
          Matrix.diag,
          Fin.sum_univ_succ, Matrix.single, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply,
          Matrix.smul_apply, smul_eq_mul] <;>
        first | (solve | ring) | linear_combination -$h))

/-- The Lie-bracket contraction onto the trace-zero three-by-three matrices is surjective
over any commutative ring. -/
theorem alternatingProductMap_surjective (K : Type*) [CommRing K] :
    Function.Surjective (alternatingProductMap K 3) := by
  intro X
  refine ⟨offDiagPreimage X + (X.val 0 0 • pair 0 2 2 0 (by decide) (by decide) +
    X.val 1 1 • pair 1 2 2 1 (by decide) (by decide)), ?_⟩
  have htrace := diagonal_sum_zero X
  apply Subtype.ext
  -- Express the subtype inclusion as a linear map so that it distributes over the preimage.
  change (𝔰 K).toSubmodule.subtype _ = X.val
  simp only [offDiagPreimage, pair, map_add, map_smul, Submodule.subtype_apply,
    alternatingProductMap_tmul, LieAlgebra.SpecialLinear.sl_bracket, val_single]
  close_fin3 htrace

/-- The traceless symmetric contraction onto the trace-zero three-by-three matrices is
surjective when three is nonzero in the scalar field. -/
theorem symmetricProductMap_surjective (K : Type*) [Field K] [NeZero (3 : K)] :
    Function.Surjective (symmetricProductMap K 3) := by
  intro X
  refine ⟨offDiagPreimage X + (X.val 0 0 •
    (pair 0 1 1 0 (by decide) (by decide) - pair 2 1 1 2 (by decide) (by decide)) +
    X.val 1 1 • (pair 1 0 0 1 (by decide) (by decide) - pair 2 0 0 2 (by decide) (by decide))),
    ?_⟩
  have htrace := diagonal_sum_zero X
  apply Subtype.ext
  -- Push the linear inclusion through the sum to evaluate each pair of matrix units.
  change (LieAlgebra.SpecialLinear.sl (Fin 3) K).toSubmodule.subtype _ = X.val
  simp only [offDiagPreimage, pair, map_add, map_sub, map_smul, Submodule.subtype_apply,
    symmetricProductMap_tmul, coe_symmetricProduct, val_single]
  close_fin3 htrace

end TauCeti.AdjointSquare
