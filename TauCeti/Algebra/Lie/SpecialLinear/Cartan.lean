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
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Negative transpose and the Killing form on `sl n R`

Restricting `TauCeti.negTransposeLieEquiv` to `LieAlgebra.SpecialLinear.sl n R` yields `X ↦ -Xᵀ`
(`LieAlgebra.SpecialLinear.cartanInvolution`). Over a principal ideal domain `R`,
`κ(X, Y) = 2 n trace (X * Y)` (`LieAlgebra.SpecialLinear.killingForm_apply`), so
`κ(X, θ Y) = -(2 n trace (X * Yᵀ))` (`LieAlgebra.SpecialLinear.killingForm_cartanInvolution_apply`)
and `κ(X, θ X) < 0` for nonzero `X` over an ordered principal ideal domain
(`LieAlgebra.SpecialLinear.killingForm_cartanInvolution_self_neg`).

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
    cartanInvolution n R (cartanInvolution n R X) = X :=
  Subtype.ext (by simp)

/-- The special linear involution is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution n R).symm = cartanInvolution n R :=
  LieEquiv.ext fun X ↦ by rw [LieEquiv.symm_apply_eq, cartanInvolution_cartanInvolution]

/-- Fixed vectors of the involution are the skew-symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_self_iff (X : sl n R) :
    cartanInvolution n R X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, neg_eq_iff_eq_neg]

/-- Negated vectors of the involution are the symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_neg_iff (X : sl n R) :
    cartanInvolution n R X = -X ↔ (X : Matrix n n R)ᵀ = X := by
  rw [← Subtype.coe_inj, coe_cartanInvolution]; exact neg_inj

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
  have he (Z : sl n R) : (e Z : Matrix n n R) = Z := LieEquiv.ofEq_apply _ _ _ Z
  have h1 := (killingForm_of_equiv_apply e X Y).symm
  have h2 : killingForm R (TauCeti.slIdeal R n) (e X) (e Y) = killingForm R (Matrix n n R) X Y := by
    have hres := (congrArg (fun B ↦ B (e X) (e Y))
      (LieIdeal.killingForm_eq (R := R) (L := Matrix n n R) (I := TauCeti.slIdeal R n))).trans
      (LinearMap.domRestrict₁₂_apply (killingForm R (Matrix n n R)) _ _ (e X) (e Y))
    simpa only [he] using hres
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
  have hXmat : (X : Matrix n n R) ≠ 0 := fun h ↦ hX (Subtype.ext h)
  have : Nonempty n := by by_contra! h; exact hXmat (Matrix.ext fun i _ ↦ h.elim i)
  have : (0 : R) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have htrace := Matrix.trace_mul_transpose_self_pos hXmat
  positivity

end OrderedPID

end LieAlgebra.SpecialLinear
