/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.Symplectic.Cartan
public import Mathlib.Algebra.Lie.Classical
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.Sl2.Killing
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Concrete examples of Cartan involutions

This file exhibits concrete non-degenerate Cartan involutions, reductive Cartan involutions, and
non-examples on classical matrix Lie algebras:

* `LieAlgebra.Symplectic.isCartanInvolution_cartanInvolution`: negative transpose
  `X ↦ -Xᵀ` is a Cartan involution of the real symplectic Lie algebra `sp l ℝ` for every finite
  index type `l`.
* `TauCeti.slNegTransposeLieEquiv`: negative transpose `X ↦ -Xᵀ` as an involutive automorphism of
  `sl n R`, with `TauCeti.isCartanInvolution_slNegTransposeLieEquiv_finTwo` verifying that it is a
  Cartan involution of `sl (Fin 2) ℝ`.
* `TauCeti.not_isCartanInvolution_refl_slFinTwo`: the identity is not a Cartan involution of the
  non-compact Lie algebra `sl (Fin 2) ℝ`.
* `TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv_finTwo` and
  `TauCeti.not_isCartanInvolution_negTransposeLieEquiv_finTwo`: negative transpose on `gl₂(ℝ)` is
  a reductive Cartan involution but not a semisimple Cartan involution.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–§2.
-/

public section

open Matrix LieAlgebra

namespace LieAlgebra.Symplectic

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of the real symplectic Lie algebra
`sp l ℝ`. -/
theorem isCartanInvolution_cartanInvolution (l : Type*) [Fintype l] [DecidableEq l] :
    TauCeti.IsCartanInvolution (cartanInvolution l ℝ) :=
  TauCeti.isCartanInvolution_iff.mpr
    ⟨cartanInvolution_cartanInvolution, fun _ hX ↦
      neg_pos.mpr (killingForm_cartanInvolution_self_neg hX)⟩

end LieAlgebra.Symplectic

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

section SpecialLinear

variable (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]

/-- Negative transpose `X ↦ -Xᵀ` as an involutive Lie algebra automorphism of `sl n R`. -/
def slNegTransposeLieEquiv : SpecialLinear.sl n R ≃ₗ⁅R⁆ SpecialLinear.sl n R :=
  (negTransposeLieEquiv n R).ofSubalgebras (SpecialLinear.sl n R) (SpecialLinear.sl n R) (by
    ext X
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [SpecialLinear.mem_sl_iff] at hY ⊢
      rw [LieEquiv.coe_toLieHom, negTransposeLieEquiv_apply, trace_neg, trace_transpose, hY,
        neg_zero]
    · intro hX
      rw [SpecialLinear.mem_sl_iff] at hX
      refine ⟨-Xᵀ, ?_, ?_⟩
      · rw [SpecialLinear.mem_sl_iff, trace_neg, trace_transpose, hX, neg_zero]
      · simp)

variable {n R}

/-- The underlying matrix of `slNegTransposeLieEquiv n R X` is `-Xᵀ`. -/
@[simp]
theorem coe_slNegTransposeLieEquiv (X : SpecialLinear.sl n R) :
    (slNegTransposeLieEquiv n R X : Matrix n n R) = -(X : Matrix n n R)ᵀ := by
  simp [slNegTransposeLieEquiv]

/-- Applying `slNegTransposeLieEquiv` twice is the identity. -/
@[simp]
theorem slNegTransposeLieEquiv_apply_apply (X : SpecialLinear.sl n R) :
    slNegTransposeLieEquiv n R (slNegTransposeLieEquiv n R X) = X := by
  apply Subtype.ext
  simp

/-- `slNegTransposeLieEquiv` is its own inverse. -/
@[simp]
theorem slNegTransposeLieEquiv_symm :
    (slNegTransposeLieEquiv n R).symm = slNegTransposeLieEquiv n R := by
  apply LieEquiv.ext
  intro X
  rw [LieEquiv.symm_apply_eq, slNegTransposeLieEquiv_apply_apply]

/-- Fixed vectors of `slNegTransposeLieEquiv` are the skew-symmetric trace-zero matrices. -/
@[simp]
theorem slNegTransposeLieEquiv_eq_self_iff (X : SpecialLinear.sl n R) :
    slNegTransposeLieEquiv n R X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_slNegTransposeLieEquiv, neg_eq_iff_eq_neg]

/-- Negated vectors of `slNegTransposeLieEquiv` are the symmetric trace-zero matrices. -/
@[simp]
theorem slNegTransposeLieEquiv_eq_neg_iff (X : SpecialLinear.sl n R) :
    slNegTransposeLieEquiv n R X = -X ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_slNegTransposeLieEquiv]
  simp

/-- The fixed subalgebra of `slNegTransposeLieEquiv` consists of the skew-symmetric trace-zero
matrices. -/
theorem mem_fixedSubalgebra_slNegTransposeLieEquiv (X : SpecialLinear.sl n R) :
    X ∈ (slNegTransposeLieEquiv n R).toLieHom.fixedSubalgebra ↔
      (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  simp

/-- The `(-1)`-eigenspace `cartanP` of `slNegTransposeLieEquiv` consists of the symmetric
trace-zero matrices. -/
theorem mem_cartanP_slNegTransposeLieEquiv (X : SpecialLinear.sl n R) :
    X ∈ cartanP (slNegTransposeLieEquiv n R) ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  simp

end SpecialLinear

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of `sl (Fin 2) ℝ`. -/
theorem isCartanInvolution_slNegTransposeLieEquiv_finTwo :
    IsCartanInvolution (slNegTransposeLieEquiv (Fin 2) ℝ) := by
  rw [isCartanInvolution_iff]
  refine ⟨slNegTransposeLieEquiv_apply_apply, fun X hX ↦ ?_⟩
  rw [killingForm_slFinTwo_apply, coe_slNegTransposeLieEquiv, mul_neg, trace_neg, mul_neg, neg_neg]
  obtain ⟨i, j, hij⟩ : ∃ i j, (X : Matrix (Fin 2) (Fin 2) ℝ) i j ≠ 0 := by
    by_contra! h
    exact hX (Subtype.ext (Matrix.ext h))
  have htr : 0 < ((X : Matrix (Fin 2) (Fin 2) ℝ) * (X : Matrix (Fin 2) (Fin 2) ℝ)ᵀ).trace := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
        ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩
  positivity

/-- The identity is not a Cartan involution of the non-compact Lie algebra `sl (Fin 2) ℝ`. -/
theorem not_isCartanInvolution_refl_slFinTwo :
    ¬ IsCartanInvolution (LieEquiv.refl : SpecialLinear.sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆
      SpecialLinear.sl (Fin 2) ℝ) := by
  intro h
  have hne : slFinTwoBasis ℝ 2 ≠ 0 := (slFinTwoBasis ℝ).ne_zero 2
  have hpos := h.cartanBilinForm_pos hne
  have hk : killingForm ℝ (SpecialLinear.sl (Fin 2) ℝ) (slFinTwoBasis ℝ 2) (slFinTwoBasis ℝ 2) =
      8 := by
    simpa using killingForm_slFinTwoBasis (R := ℝ) 2 2
  rw [cartanBilinForm_apply, LieEquiv.refl_apply, hk] at hpos
  linarith

/-- Negative transpose `X ↦ -Xᵀ` is a reductive Cartan involution of `gl (Fin 2) ℝ`. -/
theorem isReductiveCartanInvolution_negTransposeLieEquiv_finTwo :
    IsReductiveCartanInvolution (negTransposeLieEquiv (Fin 2) ℝ) := by
  rw [isReductiveCartanInvolution_iff]
  refine ⟨fun X ↦ by simp, ?_⟩
  let e : SpecialLinear.sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆ derivedSeries ℝ (Matrix (Fin 2) (Fin 2) ℝ) 1 :=
    LieEquiv.ofEq (SpecialLinear.sl (Fin 2) ℝ) (derivedSeries ℝ (Matrix (Fin 2) (Fin 2) ℝ) 1)
      (by rw [derivedSeries_one_toLieSubalgebra_eq_sl])
  have hconj : ((e.symm.trans (slNegTransposeLieEquiv (Fin 2) ℝ)).trans e) =
      (negTransposeLieEquiv (Fin 2) ℝ).restrictDerived := by
    apply LieEquiv.ext
    intro X
    apply Subtype.ext
    simp only [LieEquiv.trans_apply, LieEquiv.coe_restrictDerived, negTransposeLieEquiv_apply]
    have he (Y : SpecialLinear.sl (Fin 2) ℝ) : (e Y : Matrix (Fin 2) (Fin 2) ℝ) = Y :=
      LieEquiv.ofEq_apply _ _ _ Y
    have he_symm : (e.symm X : Matrix (Fin 2) (Fin 2) ℝ) = X := by
      rw [← he, LieEquiv.apply_symm_apply]
    rw [he, coe_slNegTransposeLieEquiv, he_symm]
  rw [← hconj]
  exact isCartanInvolution_slNegTransposeLieEquiv_finTwo.conj e

/-- Negative transpose on `gl (Fin 2) ℝ` is not a semisimple Cartan involution because
`gl (Fin 2) ℝ` has nontrivial centre. -/
theorem not_isCartanInvolution_negTransposeLieEquiv_finTwo :
    ¬ IsCartanInvolution (negTransposeLieEquiv (Fin 2) ℝ) := by
  intro h
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ center ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    one_mem_center_matrix ℝ (Fin 2)
  rw [h.center_eq_bot] at h1
  simp at h1

end TauCeti
