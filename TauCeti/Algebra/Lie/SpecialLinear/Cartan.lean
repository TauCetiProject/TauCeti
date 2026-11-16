/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.TraceForm
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Killing

/-!
# Negative transpose and the Killing form on `sl n R`

The special linear Lie algebra `LieAlgebra.SpecialLinear.sl n R` of trace-zero matrices is stable
under transpose. Restricting `TauCeti.negTransposeLieEquiv` gives the involutive automorphism
`X ↦ -Xᵀ` (`LieAlgebra.SpecialLinear.cartanInvolution`), whose fixed and negated vectors are the
skew-symmetric and symmetric trace-zero matrices respectively.

Because `sl n R` is a Lie ideal of `Matrix n n R`, its Killing form over any principal ideal domain
is the restriction of `Matrix.killingForm_apply`:

`κ(X, Y) = 2 n trace (X * Y)`

where `n = Fintype.card n`. Composing with `θ Y = -Yᵀ` gives
`κ(X, θ Y) = -(2 n trace (X * Yᵀ))`, which is strictly negative for nonzero `X` over any ordered
principal ideal domain.

## Main definitions

* `LieAlgebra.SpecialLinear.cartanInvolution`: the involutive Lie automorphism `X ↦ -Xᵀ` of
  `sl n R`.

## Main results

* `LieAlgebra.SpecialLinear.killingForm_apply`: `κ(X, Y) = 2 n trace (X * Y)` on `sl n R` over a
  principal ideal domain.
* `LieAlgebra.SpecialLinear.killingForm_cartanInvolution_apply`:
  `κ(X, θ Y) = -(2 n trace (X * Yᵀ))`.
* `LieAlgebra.SpecialLinear.killingForm_cartanInvolution_self_neg`: `κ(X, θ X) < 0` for nonzero `X`
  over an ordered principal ideal domain.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter I and Chapter VI, §1.
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

variable (n R)

/-- The involutive Lie automorphism `X ↦ -Xᵀ` of the special linear Lie algebra. -/
def cartanInvolution : sl n R ≃ₗ⁅R⁆ sl n R :=
  (TauCeti.negTransposeLieEquiv n R).ofSubalgebras (sl n R) (sl n R) (by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, TauCeti.negTransposeLieEquiv_apply,
        mem_sl_iff, trace_neg, trace_transpose, mem_sl_iff.mp hY, neg_zero]
    · intro hX
      have hneg : -Xᵀ ∈ sl n R := by
        rw [mem_sl_iff, trace_neg, trace_transpose, mem_sl_iff.mp hX, neg_zero]
      exact ⟨-Xᵀ, hneg, by simp⟩)

variable {n R}

/-- The matrix value of the special linear involution is negative transpose. -/
@[simp]
theorem coe_cartanInvolution (X : sl n R) :
    (cartanInvolution n R X : Matrix n n R) = -(X : Matrix n n R)ᵀ := by
  simp [cartanInvolution]

/-- Applying the special linear involution twice gives the original vector. -/
@[simp]
theorem cartanInvolution_cartanInvolution (X : sl n R) :
    cartanInvolution n R (cartanInvolution n R X) = X := by
  apply Subtype.ext
  simp

/-- The special linear involution is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution n R).symm = cartanInvolution n R := by
  apply LieEquiv.ext
  intro X
  rw [LieEquiv.symm_apply_eq, cartanInvolution_cartanInvolution]

/-- Fixed vectors of the involution are the skew-symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_self_iff (X : sl n R) :
    cartanInvolution n R X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, neg_eq_iff_eq_neg]

/-- Negated vectors of the involution are the symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_neg_iff (X : sl n R) :
    cartanInvolution n R X = -X ↔ (X : Matrix n n R)ᵀ = X := by
  rw [← Subtype.coe_inj, coe_cartanInvolution]
  exact neg_inj

end CommRing

section PID

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R]

/-- **The Killing form of `sl n R`**: `κ(X, Y) = 2 n trace (X * Y)` over any principal ideal
domain. -/
theorem killingForm_apply (X Y : sl n R) :
    killingForm R (sl n R) X Y =
      2 * Fintype.card n * ((X : Matrix n n R) * Y).trace := by
  let e : sl n R ≃ₗ⁅R⁆ TauCeti.slIdeal R n :=
    LieEquiv.ofEq (sl n R) (TauCeti.slIdeal R n).toLieSubalgebra
      (congrArg SetLike.coe (TauCeti.slIdeal_toLieSubalgebra_eq_sl (R := R) (n := n)).symm)
  have h1 : killingForm R (sl n R) X Y = killingForm R (TauCeti.slIdeal R n) (e X) (e Y) :=
    (killingForm_of_equiv_apply e X Y).symm
  have h2 : killingForm R (TauCeti.slIdeal R n) (e X) (e Y) =
      killingForm R (Matrix n n R) X Y := by
    rw [LieIdeal.killingForm_eq]
    rfl
  rw [h1, h2, Matrix.killingForm_apply, mem_sl_iff.mp X.property, mem_sl_iff.mp Y.property]
  ring

/-- The Killing form of `sl n R` twisted by `θ Y = -Yᵀ`:
`κ(X, θ Y) = -(2 n trace (X * Yᵀ))`. -/
theorem killingForm_cartanInvolution_apply (X Y : sl n R) :
    killingForm R (sl n R) X (cartanInvolution n R Y) =
      -(2 * Fintype.card n * ((X : Matrix n n R) * (Y : Matrix n n R)ᵀ).trace) := by
  rw [killingForm_apply, coe_cartanInvolution, mul_neg, trace_neg, mul_neg]

end PID

section OrderedPID

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
  [IsPrincipalIdealRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **`θ X = -Xᵀ` satisfies `κ(X, θ X) < 0` on `sl n R`** over an ordered principal ideal domain
for every nonzero `X`. -/
theorem killingForm_cartanInvolution_self_neg {X : sl n R} (hX : X ≠ 0) :
    killingForm R (sl n R) X (cartanInvolution n R X) < 0 := by
  rw [killingForm_cartanInvolution_apply, neg_lt_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (X : Matrix n n R) i j ≠ 0 := by
    by_contra! h
    exact hX (Subtype.ext (Matrix.ext h))
  have : Nonempty n := ⟨i⟩
  have : (0 : R) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have htrace : 0 < ((X : Matrix n n R) * (X : Matrix n n R)ᵀ).trace := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
        ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩
  positivity

end OrderedPID

end LieAlgebra.SpecialLinear
