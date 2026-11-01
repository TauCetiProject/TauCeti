/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Linear extension of coordinate functions by zero

Mathlib's `Function.ExtendByZero.linearMap` along an injective index map is injective. Along
`Fin.castSucc` it views `R^N` as the coordinate hyperplane of `R^(N + 1)` with vanishing last
coordinate, and `Fin.init` inverts it. Along `Fin.succ` it is the coordinate shift
`e_i ↦ e_(i + 1)`, which together with the first basis vector `e₀ = Pi.single 0 1` splits
`R^(N + 1)`: every vector is its first coordinate times `e₀` plus the shift of its tail.
-/

public section

namespace Function.ExtendByZero

variable {R : Type*} [Semiring R]

/-- Extension by zero along an injective index map is injective. -/
theorem linearMap_injective {ι κ : Type*} {e : ι → κ} (he : Injective e) :
    Injective (linearMap R R e) :=
  extend_injective he (0 : κ → R)

variable {N : ℕ}

/-- Taking the initial segment undoes the extension by zero along `Fin.castSucc`. -/
@[simp]
theorem init_linearMap_castSucc (v : Fin N → R) :
    Fin.init (linearMap R R Fin.castSucc v) = v := by
  funext i
  simp [Fin.init, (Fin.castSucc_injective N).extend_apply]

/-- The extension by zero along `Fin.castSucc` vanishes at the last coordinate. -/
theorem linearMap_castSucc_last (v : Fin N → R) :
    linearMap R R Fin.castSucc v (Fin.last N) = 0 := by
  simp

/-- Every vector of `R^(N + 1)` is its first coordinate times `e₀` plus the shift of its tail. -/
theorem eq_smul_single_zero_add_linearMap_succ_tail (w : Fin (N + 1) → R) :
    w = w 0 • Pi.single 0 1 + linearMap R R Fin.succ (Fin.tail w) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp [(Fin.succ_injective N).extend_apply, Fin.tail]

end Function.ExtendByZero
