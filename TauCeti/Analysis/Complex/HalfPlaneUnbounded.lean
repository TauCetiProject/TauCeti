/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Normed.Module.HalfSpace

/-!
# Points of large norm in a coordinate half-plane of `ℂ`

Each of the four inequalities `z.im < c`, `c < z.im`, `z.re < c` and `c < z.re` cuts out an open
half-plane of `ℂ` — two horizontal, two vertical — and each holds points of arbitrarily large
norm. These are the specialisations of `TauCeti.exists_apply_lt_and_lt_norm` and
`TauCeti.exists_lt_apply_and_lt_norm` to `Complex.reLm` and `Complex.imLm`.

This is what a winding-number vanishing argument needs: to transport a winding number through an
unbounded connected region one must exhibit, for each radius, a point of the region beyond it.

## Main results

* `Complex.reLm_ne_zero`, `Complex.imLm_ne_zero` — the two coordinate functionals of `ℂ` are
  nonzero.
* `TauCeti.exists_im_lt_and_lt_norm`, `TauCeti.exists_lt_im_and_lt_norm`,
  `TauCeti.exists_re_lt_and_lt_norm`, `TauCeti.exists_lt_re_and_lt_norm` — the four coordinate
  half-planes.
-/

public section

namespace Complex

/-- The imaginary part is not the zero functional. -/
@[simp] theorem imLm_ne_zero : (imLm : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h
  simpa using congrArg (fun ψ => ψ Complex.I) h

/-- The real part is not the zero functional. -/
@[simp] theorem reLm_ne_zero : (reLm : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h
  simpa using congrArg (fun ψ => ψ 1) h

end Complex

namespace TauCeti

/-- The open lower half-plane `{z | z.im < c}` contains points of arbitrarily large norm. -/
theorem exists_im_lt_and_lt_norm (c R : ℝ) : ∃ z : ℂ, z.im < c ∧ R < ‖z‖ :=
  exists_apply_lt_and_lt_norm Complex.imLm_ne_zero c R

/-- The open upper half-plane `{z | c < z.im}` contains points of arbitrarily large norm. -/
theorem exists_lt_im_and_lt_norm (c R : ℝ) : ∃ z : ℂ, c < z.im ∧ R < ‖z‖ :=
  exists_lt_apply_and_lt_norm Complex.imLm_ne_zero c R

/-- The open left half-plane `{z | z.re < c}` contains points of arbitrarily large norm. -/
theorem exists_re_lt_and_lt_norm (c R : ℝ) : ∃ z : ℂ, z.re < c ∧ R < ‖z‖ :=
  exists_apply_lt_and_lt_norm Complex.reLm_ne_zero c R

/-- The open right half-plane `{z | c < z.re}` contains points of arbitrarily large norm. -/
theorem exists_lt_re_and_lt_norm (c R : ℝ) : ∃ z : ℂ, c < z.re ∧ R < ‖z‖ :=
  exists_lt_apply_and_lt_norm Complex.reLm_ne_zero c R

end TauCeti
