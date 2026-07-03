/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.ContinuousOn

/-!
# Paths that are `C¹` off a finite set (arbitrary interval)

This file defines `C1OffFinitePathOn a b hab x y`, the free-interval *carrier*: a continuous
function `ℝ → E` with `f a = x`, `f b = y`, continuous on `[a, b]`, that is differentiable with a
continuous derivative *away from* a finite set of breakpoints in `(a, b)`.

This is a deliberately weak regularity condition: it constrains the path only on the *open*
interiors between breakpoints and says nothing about one-sided derivative limits at a breakpoint,
so it is **not** the piecewise-`C¹` notion of Hungerbühler–Wasem. That faithful notion — genuine
`C¹` regularity on each *closed* piece — is `ClosedPwC1Curve`. `C1OffFinitePathOn` is the substrate
on which the generalized winding number and the Cauchy principal value are defined, as those need
only an integrable derivative.

The unit-interval form `C1OffFinitePath` (in `TauCeti.Analysis.Contour.C1OffFinitePath`) is
built on top of this by extending the domain to `ℝ` and bundling a Mathlib `Path x y`.

## Main definitions

* `C1OffFinitePathOn a b hab x y` — a continuous path from `x` to `y`, differentiable with a
  continuous derivative off a finite set of breakpoints. Its partition (the breakpoints) lives in
  the open interval `Ioo a b`; the endpoints `a` and `b` are never partition points.

## Design notes

This file deliberately does not depend on `Mathlib.Topology.Path`: a Mathlib `Path` is fixed
to the unit interval `[0, 1]`, whereas a free-interval path needs a raw `ℝ → E` continuous on
`Icc a b`. The unit-interval form recovers the `Path` API downstream.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Set Filter Topology

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous path from `x` to `y` on a free interval `[a, b]` in a normed space that is
differentiable with a continuous derivative off a finite set of breakpoints.

The smoothness conditions (differentiability and continuous derivative) hold at every point of
`(a, b)` outside a finite set of breakpoints; nothing is required at the breakpoints themselves
beyond continuity. This is weaker than the piecewise-`C¹` notion `ClosedPwC1Curve` (`C¹` on each
closed piece). The partition lives in the open interval `Ioo a b` — the endpoints `a` and `b` are
not partition points. -/
@[ext]
structure C1OffFinitePathOn (a b : ℝ) (hab : a < b) (x y : E) where
  /-- The underlying function `ℝ → E`. -/
  toFun : ℝ → E
  /-- The path starts at `x` (at parameter `a`). -/
  source : toFun a = x
  /-- The path ends at `y` (at parameter `b`). -/
  target : toFun b = y
  /-- The path is continuous on the closed interval `[a, b]`. -/
  continuous_toFun : ContinuousOn toFun (Icc a b)
  /-- The finite set of breakpoints, all lying in the open interval `(a, b)`. -/
  partition : Finset ℝ
  /-- All breakpoints lie in the open interval `(a, b)`. -/
  partition_subset : (partition : Set ℝ) ⊆ Ioo a b
  /-- `toFun` is differentiable at every point of `(a, b)` outside the partition. -/
  differentiable_off : ∀ t ∈ Ioo a b, t ∉ partition → DifferentiableAt ℝ toFun t
  /-- The derivative of `toFun` is continuous at every point of `(a, b)` outside the
  partition. -/
  deriv_continuous_off : ∀ t ∈ Ioo a b, t ∉ partition → ContinuousAt (deriv toFun) t

namespace C1OffFinitePathOn

variable {a b : ℝ} {hab : a < b} {x y : E}

instance : CoeFun (C1OffFinitePathOn a b hab x y) fun _ => ℝ → E where
  coe := C1OffFinitePathOn.toFun

end C1OffFinitePathOn

end TauCeti.Contour

end
