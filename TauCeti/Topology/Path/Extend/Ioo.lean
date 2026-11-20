/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Path
public import TauCeti.Topology.Order.ExtendIoo
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

/-!
# The path traced by a function on an open interval

A curve is often produced not as a `Path` but as a function `g : ℝ → X` defined on an *open*
interval `Ioo a b`, continuous there, and converging at each of the two ends. This file turns such
a function into an honest `Path` between its two limits, `Path.ofContinuousOnIoo`, and
records what its values are on the interior of the unit interval and what its range is.

The construction is the extension `TauCeti.extendIoo a b u v g` of `g` across the two ends of the
interval by the prescribed values `u` and `v` (`TauCeti/Topology/Order/ExtendIoo.lean`), composed
with the affine reparametrisation `AffineMap.lineMap a b : [0, 1] → [a, b]`. Because those two
values are *given* rather than recovered as limits, the continuity of the extension on `Icc a b`
(`TauCeti.continuousOn_Icc_extendIoo`) needs no separation assumption on `X`. Nothing else is
needed: the two endpoint limits are exactly the data that a `Path` between them requires.

When `X` is Hausdorff, the range is `closure (g '' Ioo a b)` rather than `g '' Ioo a b`: the path
traverses the closed interval, and the image of a compact set under a map continuous on it is the
closure of the image of the dense open part. So the closure of a curve given on an open interval
in a Hausdorff space is automatically path-connected, with the curve itself as the interior of the
traversal — which is what makes this construction useful, since the endpoints are in general *not*
values of `g`.

Whether the path is simple is not a matter of the extension but of `g` and of the endpoints. The
one step of that argument which is not a plain composition is order-theoretic and lives in
`TauCeti/Order/Interval/Set/Injective.lean`:
`TauCeti.eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo`, which a `Path` specializes through its
coercion, every point of `unitInterval` lying in `Icc 0 1`.

## Main declarations

* `Path.ofContinuousOnIoo` — the path traced by a function continuous on `Ioo a b` with a
  limit at each end, from the limit at `a` to the limit at `b`.
* `Path.ofContinuousOnIoo_apply` and
  `Path.ofContinuousOnIoo_apply_of_mem_Ioo` — its values, in general and on the interior.
* `Path.range_ofContinuousOnIoo` — its range in a Hausdorff space is `closure (g '' Ioo a b)`.

## Generality

The path is real, `AffineMap.lineMap` and `unitInterval` being so. The path and its values ask
nothing of `X` beyond a topology; only the range computation is Hausdorff, the image of a compact
set having to be closed there.
-/

public section

open Filter Set Topology
open scoped unitInterval

namespace Path

open TauCeti

variable {X : Type*} [TopologicalSpace X] {a b : ℝ} {u v : X} {g : ℝ → X}

/-- **The path traced by a function on an open interval.** If `g` is continuous on `Ioo a b`, tends
to `u` at `a` from the right and to `v` at `b` from the left, then `g` traverses a path from `u` to
`v`: the extension `TauCeti.extendIoo a b u v g` of `g` across the two ends, read along the affine
parametrisation `AffineMap.lineMap a b` of `Icc a b` by the unit interval.

Its values on the interior of the unit interval are those of `g`
(`Path.ofContinuousOnIoo_apply_of_mem_Ioo`) and, when `X` is Hausdorff, its range is
`closure (g '' Ioo a b)` (`Path.range_ofContinuousOnIoo`); the endpoints `u` and `v` need not
themselves be values of `g`. Compute with it through `Path.ofContinuousOnIoo_apply` rather than
through the definition. -/
noncomputable def ofContinuousOnIoo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) : Path u v where
  toFun t := extendIoo a b u v g (AffineMap.lineMap a b (t : ℝ))
  continuous_toFun :=
    (continuousOn_Icc_extendIoo hg hu hv).comp_continuous
      (by simp only [AffineMap.lineMap_apply_ring]; fun_prop)
      fun t => segment_eq_Icc hab.le ▸ lineMap_mem_segment ℝ a b t.2
  source' := by simp
  target' := by simp [hab]

/-- The path traced by `g` is the extension of `g` across the two ends of `Ioo a b`, read along the
affine parametrisation of `Icc a b` by the unit interval. -/
@[grind =]
theorem ofContinuousOnIoo_apply (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) (t : I) :
    ofContinuousOnIoo hab hg hu hv t = extendIoo a b u v g (AffineMap.lineMap a b (t : ℝ)) :=
  -- Parenthesised: a bare `rfl` would demand that the body of `ofContinuousOnIoo` be exposed.
  (rfl)

/-- **On the interior of the unit interval the path traced by `g` is `g` itself**, along the affine
parametrisation. The endpoints are excluded because there the values of `g` are unconstrained: they
need not be the limits `u` and `v`, which is what makes the construction more than a
reparametrisation. -/
@[simp, grind =]
theorem ofContinuousOnIoo_apply_of_mem_Ioo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) {t : I}
    (ht : t ∈ Ioo (0 : I) 1) :
    ofContinuousOnIoo hab hg hu hv t = g (AffineMap.lineMap a b (t : ℝ)) := by
  rw [ofContinuousOnIoo_apply, extendIoo_apply_of_mem_Ioo]
  exact openSegment_eq_Ioo hab ▸ lineMap_mem_openSegment ℝ a b (by simpa using ht)

/-- **The range of the path traced by `g` in a Hausdorff space is the closure of the curve.** In
particular the closure of a curve in a Hausdorff space, defined on an open interval and converging
at both ends, is path-connected. -/
theorem range_ofContinuousOnIoo [T2Space X] (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) :
    range (ofContinuousOnIoo hab hg hu hv) = closure (g '' Ioo a b) := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hparam : range (fun t : I => AffineMap.lineMap a b (t : ℝ)) = Icc a b := by
    rw [← image_eq_range, ← segment_eq_image_lineMap, segment_eq_Icc hab.le]
  have hcont : ContinuousOn (extendIoo a b u v g) (closure (Ioo a b)) :=
    hcl ▸ continuousOn_Icc_extendIoo hg hu hv
  have heq : EqOn (extendIoo a b u v g) g (Ioo a b) := fun _ hx => extendIoo_apply_of_mem_Ioo hx
  have hfun : ⇑(ofContinuousOnIoo hab hg hu hv)
      = extendIoo a b u v g ∘ fun t : I => AffineMap.lineMap a b (t : ℝ) :=
    funext (ofContinuousOnIoo_apply hab hg hu hv)
  rw [hfun, range_comp, hparam, ← hcl, image_closure_of_isCompact (hcl ▸ isCompact_Icc) hcont,
    heq.image_eq]

end Path
