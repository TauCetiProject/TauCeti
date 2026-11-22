/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.Cartan

import TauCeti.Algebra.Lie.SpecialLinear.Killing
import TauCeti.LinearAlgebra.Matrix.Trace.Positive

/-!
# Negative transpose is a Cartan involution of `sl n`

On the special linear Lie algebra `sl n R`, the twisted Killing form of the negative-transpose
involution `LieAlgebra.SpecialLinear.cartanInvolution` is `B_θ(X, Y) = 2 n trace (X * Yᵀ)`
(`LieAlgebra.SpecialLinear.twistedKillingForm_cartanInvolution_apply`) over every commutative ring
`R`.

Over any ordered field `K`, `trace (X * Xᵀ) > 0` for nonzero `X` makes `X ↦ -Xᵀ` a Cartan
involution of `sl n K` (`LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`), whereas
`LieEquiv.refl` is not a Cartan involution whenever `1 < Fintype.card n`
(`LieAlgebra.SpecialLinear.not_isCartanInvolution_refl`).

## Main results

* `LieAlgebra.SpecialLinear.twistedKillingForm_cartanInvolution_apply`: explicit formula for the
  twisted Killing form `B_θ(X, Y) = 2 n trace (X * Yᵀ)`.
* `LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`: `X ↦ -Xᵀ` is a Cartan
  involution of `sl n K` over every ordered field `K`.
* `LieAlgebra.SpecialLinear.not_isCartanInvolution_refl`: `LieEquiv.refl` is not a Cartan
  involution of `sl n K` when `1 < Fintype.card n`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–2.
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The twisted Killing form of `X ↦ -Xᵀ` on `sl n R` is `B_θ(X, Y) = 2 n trace (X * Yᵀ)`. -/
theorem twistedKillingForm_cartanInvolution_apply (X Y : sl n R) :
    (cartanInvolution n R).twistedKillingForm X Y =
      2 * Fintype.card n * ((X : Matrix n n R) * (Y : Matrix n n R)ᵀ).trace := by
  rw [LieEquiv.twistedKillingForm_apply, killingForm_apply, coe_cartanInvolution, mul_neg,
    trace_neg, mul_neg, neg_neg]

end CommRing

section OrderedField

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **`X ↦ -Xᵀ` is a Cartan involution of `sl n K`** over every ordered field `K`. -/
theorem isCartanInvolution_cartanInvolution :
    (cartanInvolution n K).IsCartanInvolution := by
  rw [LieEquiv.isCartanInvolution_iff]
  refine ⟨cartanInvolution_cartanInvolution, fun X hX ↦ ?_⟩
  rw [← neg_pos, ← LieEquiv.twistedKillingForm_apply, twistedKillingForm_cartanInvolution_apply]
  have hne : Nonempty n := not_isEmpty_iff.mp fun h ↦ by
    have := h
    exact hX (Subtype.ext (Subsingleton.elim _ _))
  have : (0 : K) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have htr : 0 < ((X : Matrix n n K) * (X : Matrix n n K)ᵀ).trace :=
    Matrix.trace_mul_transpose_pos fun h ↦ hX (Subtype.ext h)
  positivity

/-- The identity automorphism is **not** a Cartan involution of `sl n K` whenever
`1 < Fintype.card n` (in particular for `sl (Fin 2) K`): a nonzero diagonal trace-zero matrix
`h = E_{ii} - E_{jj}` lies in `cartanP` of `X ↦ -Xᵀ`, so `B(h, h) > 0` while `B_id(h, h) =
-B(h, h)`. -/
theorem not_isCartanInvolution_refl (hn : 1 < Fintype.card n) :
    ¬ (LieEquiv.refl : sl n K ≃ₗ⁅K⁆ sl n K).IsCartanInvolution := by
  intro hθ
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hn
  let H : sl n K := singleSubSingle i j (1 : K)
  have hH0 : H ≠ 0 := by
    intro h0
    have hentry := congrArg (fun M : sl n K ↦ (M : Matrix n n K) i i) h0
    simp [H, Matrix.single, hij.symm] at hentry
  have hH_symm : H ∈ (cartanInvolution n K).cartanP := by
    rw [mem_cartanP_cartanInvolution_iff]
    simp [H, val_singleSubSingle]
  have hpos : 0 < killingForm K (sl n K) H H :=
    isCartanInvolution_cartanInvolution.killingForm_apply_self_pos_of_mem_cartanP hH_symm hH0
  have hneg : killingForm K (sl n K) H H < 0 := by
    simpa only [LieEquiv.twistedKillingForm_refl, LinearMap.neg_apply, neg_pos] using
      hθ.twistedKillingForm_self_pos hH0
  exact lt_asymm hpos hneg

end OrderedField

end LieAlgebra.SpecialLinear
