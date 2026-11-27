/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
import TauCeti.Algebra.Lie.SpecialLinear.Killing
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Negative transpose and the Cartan involution on `sl n R`

Restricting `TauCeti.negTransposeLieEquiv` to `LieAlgebra.SpecialLinear.sl n R` yields `X ↦ -Xᵀ`
(`LieAlgebra.SpecialLinear.cartanInvolution`). Using `LieAlgebra.SpecialLinear.killingForm_apply`
(`κ(X, Y) = 2 n trace (X * Y)` over a principal ideal domain `R`), we obtain
`κ(X, θ Y) = -(2 n trace (X * Yᵀ))` (`LieAlgebra.SpecialLinear.killingForm_cartanInvolution_apply`)
and `κ(X, θ X) < 0` for nonzero `X` over an ordered principal ideal domain
(`LieAlgebra.SpecialLinear.killingForm_cartanInvolution_self_neg`).

Over an ordered field `K`, `LieAlgebra.SpecialLinear.cartanInvolution n K` is a Cartan
involution (`LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`). Specializing to
`n = Fin (r + 1)` and `K = ℝ` gives `TauCeti.specialLinearNegTranspose`, acting by `-1` on the
trace-zero diagonal matrices.

## Main results

* `LieAlgebra.SpecialLinear.cartanInvolution`,
  `LieAlgebra.SpecialLinear.killingForm_cartanInvolution_apply`,
  `LieAlgebra.SpecialLinear.killingForm_cartanInvolution_self_neg`,
  `LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`: the involution `X ↦ -Xᵀ` of
  `sl n R`, its twisted Killing form over an ordered PID, and its Cartan involution certificate
  over an ordered field.
* `TauCeti.specialLinearNegTranspose`, `TauCeti.isCartanInvolution_specialLinearNegTranspose`,
  `TauCeti.specialLinearNegTranspose_apply_of_mem_specialLinearDiagonal`: the Cartan involution
  `X ↦ -Xᵀ` of `𝔰𝔩_{r+1}(ℝ)` and its action on `specialLinearDiagonal r ℝ`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter I and Chapter VI, §§1–2 (Proposition 6.28).
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
    refine ⟨?_, fun hX ↦ ⟨-Xᵀ, neg_transpose_mem_sl hX, by simp⟩⟩
    · rintro ⟨Y, hY, rfl⟩
      simpa using neg_transpose_mem_sl hY)

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

section OrderedField

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of the special linear Lie algebra `sl n K`
over any ordered field `K`. -/
@[simp]
theorem isCartanInvolution_cartanInvolution :
    (cartanInvolution n K).IsCartanInvolution := by
  rw [LieEquiv.isCartanInvolution_iff]
  exact ⟨cartanInvolution_cartanInvolution,
    fun _ hX ↦ killingForm_cartanInvolution_self_neg hX⟩

end OrderedField

end LieAlgebra.SpecialLinear

namespace TauCeti

open LieAlgebra.SpecialLinear Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- The Cartan involution `X ↦ -Xᵀ` of `𝔰𝔩_{r+1}(ℝ)`. -/
def specialLinearNegTranspose : sl (Fin (r + 1)) ℝ ≃ₗ⁅ℝ⁆ sl (Fin (r + 1)) ℝ :=
  cartanInvolution (Fin (r + 1)) ℝ

variable {r}

/-- The Cartan involution `specialLinearNegTranspose` is `X ↦ -Xᵀ` on the underlying matrices. -/
@[simp]
theorem coe_specialLinearNegTranspose_apply (X : sl (Fin (r + 1)) ℝ) :
    ((specialLinearNegTranspose r X : sl (Fin (r + 1)) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
      -(X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)ᵀ :=
  coe_cartanInvolution X

variable (r) in
/-- `X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔩_{r+1}(ℝ)`. -/
theorem isCartanInvolution_specialLinearNegTranspose :
    (specialLinearNegTranspose r).IsCartanInvolution :=
  isCartanInvolution_cartanInvolution

/-- The Cartan involution acts on the trace-zero diagonal matrices by `-1`. -/
theorem specialLinearNegTranspose_apply_of_mem_specialLinearDiagonal {X : sl (Fin (r + 1)) ℝ}
    (hX : X ∈ specialLinearDiagonal r ℝ) : specialLinearNegTranspose r X = -X := by
  ext : 1
  rw [coe_specialLinearNegTranspose_apply, ((mem_specialLinearDiagonal_iff r ℝ X).mp hX).isSymm.eq,
    NegMemClass.coe_neg]

end TauCeti
