/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.Cartan
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.SpecialLinear.Killing

/-!
# Classical examples of Cartan and reductive Cartan involutions

Certifies negative transpose as a Cartan involution on `sl n K`
(`LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`), shows the identity on `sl n K` is
not Cartan for nontrivial `n` (`LieAlgebra.SpecialLinear.not_isCartanInvolution_refl`), and shows
negative transpose on `gl n K` is a reductive Cartan involution
(`TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv`) but not a Cartan involution for
nonempty `n` (`TauCeti.not_isCartanInvolution_negTransposeLieEquiv`).
-/

public section

open Matrix LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace LieAlgebra.SpecialLinear

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of the special linear Lie algebra `sl n K`
over any ordered field `K`. -/
@[simp]
theorem isCartanInvolution_cartanInvolution {n : Type*} [Fintype n] [DecidableEq n] :
    (cartanInvolution n K).IsCartanInvolution := by
  rw [LieEquiv.isCartanInvolution_iff]
  exact ⟨cartanInvolution_cartanInvolution,
    fun _ hX ↦ killingForm_cartanInvolution_self_neg hX⟩

/-- For nontrivial `n`, the identity is not a Cartan involution of `sl n K` over any ordered field
`K` (the Killing form is positive on the diagonal matrix `Eᵢᵢ - Eⱼⱼ`). -/
theorem not_isCartanInvolution_refl {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n] :
    ¬ (LieEquiv.refl : sl n K ≃ₗ⁅K⁆ sl n K).IsCartanInvolution := by
  intro hrefl
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let H : sl n K := singleSubSingle i j 1
  have hHne : H ≠ 0 := fun h0 ↦ by
    simpa [H, val_singleSubSingle, hij.symm] using
      congrArg (fun M : sl n K ↦ (M : Matrix n n K) i i) h0
  have hsq : ((H : Matrix n n K) * (H : Matrix n n K)).trace = 2 := by
    simp [H, val_singleSubSingle, sub_mul, mul_sub, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
      one_add_one_eq_two]
  have hpos : 0 < killingForm K (sl n K) H H := by
    rw [killingForm_apply, hsq]
    have : (0 : K) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
    positivity
  exact (LieEquiv.isCartanInvolution_refl_iff.mp hrefl H hHne).not_gt hpos

end LieAlgebra.SpecialLinear

namespace TauCeti

/-- Negative transpose `X ↦ -Xᵀ` is a reductive Cartan involution of `gl n K = Matrix n n K` over
any ordered field `K`. -/
@[simp]
theorem isReductiveCartanInvolution_negTransposeLieEquiv {n : Type*} [Fintype n] [DecidableEq n] :
    (negTransposeLieEquiv n K).IsReductiveCartanInvolution := by
  by_cases hn : Nonempty n
  · let _ : Invertible (Fintype.card n : K) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    rw [LieEquiv.isReductiveCartanInvolution_iff]
    refine ⟨LieSubmodule.isCompl_toSubmodule.mp
        (isCompl_center_derivedSeries_one_matrix (R := K) (n := n)), fun _ ↦ by simp, ?_⟩
    let e := LieEquiv.ofSubalgebraEqIdeal (SpecialLinear.sl n K)
      (derivedSeries K (Matrix n n K) 1) (derivedSeries_one_toLieSubalgebra_eq_sl (R := K) (n := n))
    exact (SpecialLinear.isCartanInvolution_cartanInvolution (K := K)).of_intertwines e fun X ↦
      Subtype.ext (by simp [e])
  · have : IsEmpty n := not_nonempty_iff.mp hn
    have : IsLieAbelian (Matrix n n K) := ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
    exact LieEquiv.isReductiveCartanInvolution_iff_involutive_of_isLieAbelian.mpr fun _ ↦ by simp

end TauCeti

end OrderedField

section LinearOrder

variable {K : Type*} [Field K] [LinearOrder K]

namespace TauCeti

/-- For nonempty `n`, negative transpose on `gl n K` is not a Cartan involution in the semisimple
sense, because the scalar matrices form a nontrivial centre. -/
theorem not_isCartanInvolution_negTransposeLieEquiv {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] : ¬ (negTransposeLieEquiv n K).IsCartanInvolution :=
  fun hθ ↦ center_matrix_ne_bot K n hθ.center_eq_bot

end TauCeti

end LinearOrder
