/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.C1OffFinitePathOn
public import Mathlib.Topology.Path

/-!
# Paths that are `C¹` off a finite set

This file defines `C1OffFinitePath x y`, the unit-interval form of the `C1OffFinitePathOn`
carrier, wrapping Mathlib's `Path x y` (parametrized on `[0, 1]`) with the weak off-finite-set
smoothness conditions of `TauCeti.Analysis.Contour.C1OffFinitePathOn`.

Like its parent, this is a *carrier*, not the piecewise-`C¹` notion: it constrains the path only
on the open interiors between breakpoints. The Hungerbühler–Wasem piecewise-`C¹` curve and
immersion (`C¹` on each closed piece) are `ClosedPwC1Curve` / `ClosedPwC1Immersion`, which extend
this carrier.

## Main definitions

* `C1OffFinitePath x y` — a free-interval `C1OffFinitePathOn 0 1 zero_lt_one x y` bundled with
  a Mathlib `Path x y` whose `extend` agrees pointwise with `toFun` on `[0, 1]`.
  Differentiability and derivative continuity are inherited from the parent structure.

This is the unit-interval *carrier*: like `C1OffFinitePathOn`, it requires only differentiability
with a continuous derivative on the open interiors between breakpoints. The paper-faithful curve
and immersion types `ClosedPwC1Curve` / `ClosedPwC1Immersion` — genuinely `C¹` on each closed
piece, with (for the immersion) a non-vanishing derivative including the piece endpoints — are
defined in `TauCeti.Analysis.Contour.ClosedPwC1Immersion`, which extends this carrier.

## Design notes

`C1OffFinitePath` extends `C1OffFinitePathOn 0 1 zero_lt_one x y` (the free-interval form). The
bundled `Path x y` is kept as an explicit field because the `Path` API is heavily used by call
sites — in particular the coercion `γ t = γ.toPath.extend t` must remain stable. The witness
`toPath_extend_eq_toFun` ties the two forms together on `Icc 0 1`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Set Filter Topology

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

/-- A continuous path from `x` to `y` in a normed space, differentiable with a continuous
derivative off a finite set of breakpoints (the unit-interval carrier).

This bundles a free-interval `C1OffFinitePathOn 0 1 zero_lt_one x y` together with a Mathlib
`Path x y` whose `extend` agrees with the underlying function on `[0, 1]`. The off-finite-set
smoothness conditions are inherited from the parent; this is weaker than the piecewise-`C¹`
notion `ClosedPwC1Curve`. -/
@[ext]
structure C1OffFinitePath (x y : E) extends C1OffFinitePathOn 0 1 zero_lt_one x y where
  /-- The bundled Mathlib `Path x y`. Kept as a field so that `Path.extend`-based call sites can
  continue to use the `Path` API. -/
  toPath : Path x y
  /-- The extended path agrees with the underlying function on the closed unit interval. -/
  toPath_extend_eq_toFun : ∀ t ∈ Icc (0 : ℝ) 1, toPath.extend t = toFun t

namespace C1OffFinitePath

/-- The underlying function `ℝ → E` obtained by extending the path. -/
def extendedPath (γ : C1OffFinitePath x y) : ℝ → E := γ.toPath.extend

instance : CoeFun (C1OffFinitePath x y) fun _ => ℝ → E where
  coe := extendedPath

/-- The extended path is differentiable at every point of `(0, 1)` outside the partition. Same
statement as the inherited `differentiable_off` but phrased in terms of `toPath.extend` instead
of `toFun`; the two forms agree on `Icc 0 1` via `toPath_extend_eq_toFun`. -/
theorem differentiable_off_extend (γ : C1OffFinitePath x y) :
    ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ γ.partition → DifferentiableAt ℝ γ.toPath.extend t :=
  fun t ht htp => (γ.differentiable_off t ht htp).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu))

/-- The derivative of the extended path is continuous at every point of `(0, 1)` outside the
partition. Same statement as `deriv_continuous_off` but in terms of `toPath.extend`. -/
theorem deriv_continuous_off_extend (γ : C1OffFinitePath x y) :
    ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ γ.partition → ContinuousAt (deriv γ.toPath.extend) t :=
  fun t ht htp => (γ.deriv_continuous_off t ht htp).congr
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu)).deriv.symm

@[simp]
theorem apply_zero (γ : C1OffFinitePath x y) : γ 0 = x :=
  γ.toPath.extend_zero

@[simp]
theorem apply_one (γ : C1OffFinitePath x y) : γ 1 = y :=
  γ.toPath.extend_one

/-- The underlying extended path is continuous. -/
@[fun_prop]
theorem continuous (γ : C1OffFinitePath x y) : Continuous (γ : ℝ → E) :=
  γ.toPath.continuous_extend

end C1OffFinitePath

end TauCeti.Contour

end
