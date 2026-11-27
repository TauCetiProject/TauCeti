/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Hermite–Biehler functions

An entire function `H : ℂ → ℂ` is *Hermite–Biehler* when its reflection
`H#(z) = conj (H (conj z))` is strictly smaller than `H` in modulus on the open upper half-plane:
`|H#(z)| < |H(z)|` for `Im z > 0` (`TauCeti.IsHermiteBiehler`). Since `|H#(z)| = |H(conj z)|`,
the condition is stated as `‖H (conj z)‖ < ‖H z‖`.

These are the functions from which de Branges spaces and meromorphic inner functions are built.
The basic consequences recorded here are that a Hermite–Biehler function has no zeros in the
upper half-plane (`TauCeti.IsHermiteBiehler.ne_zero`) and that the quotient `H#/H` is bounded
by `1` there (`TauCeti.IsHermiteBiehler.norm_div_lt_one`). A constant function is not
Hermite–Biehler (`TauCeti.not_isHermiteBiehler_const`).

## References

* L. de Branges, *Hilbert spaces of entire functions*, Prentice–Hall, 1968.
* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open ComplexConjugate

namespace TauCeti

/-- An entire function `H` is **Hermite–Biehler** when its reflection `H#(z) = conj (H (conj z))`
satisfies `|H#(z)| < |H(z)|` for every `z` in the open upper half-plane. As
`|H#(z)| = |H(conj z)|`, the inequality is stated as `‖H (conj z)‖ < ‖H z‖`. -/
def IsHermiteBiehler (H : ℂ → ℂ) : Prop :=
  Differentiable ℂ H ∧ ∀ z : ℂ, 0 < z.im → ‖H (conj z)‖ < ‖H z‖

variable {H : ℂ → ℂ}

/-- The defining property of a Hermite–Biehler function: `H` is entire and
`‖H (conj z)‖ < ‖H z‖` for `Im z > 0`. -/
theorem isHermiteBiehler_iff :
    IsHermiteBiehler H ↔ Differentiable ℂ H ∧ ∀ z : ℂ, 0 < z.im → ‖H (conj z)‖ < ‖H z‖ :=
  Iff.rfl

namespace IsHermiteBiehler

/-- A Hermite–Biehler function is entire. -/
theorem differentiable (hH : IsHermiteBiehler H) : Differentiable ℂ H :=
  hH.1

/-- The defining inequality `|H#(z)| < |H(z)|` of a Hermite–Biehler function, for `Im z > 0`. -/
theorem norm_lt (hH : IsHermiteBiehler H) {z : ℂ} (hz : 0 < z.im) : ‖H (conj z)‖ < ‖H z‖ :=
  hH.2 z hz

/-- A Hermite–Biehler function has no zeros in the open upper half-plane. -/
theorem ne_zero (hH : IsHermiteBiehler H) {z : ℂ} (hz : 0 < z.im) : H z ≠ 0 :=
  norm_pos_iff.1 ((norm_nonneg _).trans_lt (hH.norm_lt hz))

/-- For a Hermite–Biehler function `H`, the quotient `H#/H` is bounded by `1` on the open upper
half-plane: `|H#(z) / H(z)| < 1` for `Im z > 0`. -/
theorem norm_div_lt_one (hH : IsHermiteBiehler H) {z : ℂ} (hz : 0 < z.im) :
    ‖conj (H (conj z)) / H z‖ < 1 := by
  rw [norm_div, RCLike.norm_conj, div_lt_one (norm_pos_iff.2 (hH.ne_zero hz))]
  exact hH.norm_lt hz

end IsHermiteBiehler

/-- A constant function is not Hermite–Biehler, since `|H#(z)| = |H(z)|` for a constant `H`. -/
theorem not_isHermiteBiehler_const (c : ℂ) : ¬ IsHermiteBiehler fun _ ↦ c := fun h ↦
  (h.norm_lt (z := Complex.I) (by simp)).false

end TauCeti
