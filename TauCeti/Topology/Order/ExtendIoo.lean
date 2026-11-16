/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed

/-!
# Extending a function on an open interval by prescribed end values

A function `g` on an open interval `Ioo a b` of a linear order is extended across both ends by
prescribed values `u` and `v`: `TauCeti.extendIoo a b u v g` is `g` on `Ioo a b`, `u` on `Iic a`
and, when `a < b`, `v` on `Ici b`. If `g` is continuous on `Ioo a b` and tends to `u` at `a` from
the right and to `v` at `b` from the left, the extension is continuous on `Icc a b`
(`TauCeti.continuousOn_Icc_extendIoo`).

Because the two end values are *given* rather than recovered as limits, that continuity needs no
separation assumption on the codomain, unlike Mathlib's `continuousOn_Icc_extendFrom_Ioo` for
`extendFrom`, which must locate the limits and so asks for a regular codomain, and
`eq_lim_at_left_extendFrom_Ioo`, which asks for a Hausdorff one.

## Main declarations

* `TauCeti.extendIoo` — a function on `Ioo a b`, extended across both ends by prescribed values,
  with `TauCeti.extendIoo_apply` its defining equation and `TauCeti.extendIoo_apply_of_mem_Ioo`,
  `TauCeti.extendIoo_apply_of_le_left` and `TauCeti.extendIoo_apply_of_left_lt_of_right_le`
  computing it on each branch.
* `TauCeti.continuousOn_Icc_extendIoo` — its continuity on `Icc a b`, degenerate intervals
  included.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X α : Type*} [LinearOrder α] {a b x : α} {u v : X} {g : α → X}

/-- **A function on an open interval, extended across both of its ends by prescribed values.**
`TauCeti.extendIoo a b u v g` agrees with `g` on `Ioo a b` and takes the value `u` on `Iic a`; when
`a < b` it takes the value `v` on `Ici b`, so that in particular it is `u` at `a` and `v` at `b`.
The two outer branches run over the whole of `Iic a` and `Ici b`, rather than over the endpoints
alone, so that the definition computes everywhere and carries no side condition. The
nondegeneracy `a < b` is not part of the definition, and is needed for the right-hand branch only:
if instead `b ≤ a`, the interval is empty and the extension is `u` on `Iic a` and `v` on `Ioi a`,
so that `b` itself is sent to `u`. The value is given at every point by
`TauCeti.extendIoo_apply`, and on each branch, degenerate intervals included, by
`TauCeti.extendIoo_apply_of_mem_Ioo`, `TauCeti.extendIoo_apply_of_le_left` and
`TauCeti.extendIoo_apply_of_left_lt_of_right_le`, whose hypotheses are exactly the three branch
conditions.

Mathlib's `extendFrom` instead *recovers* the end values as limits, which is why its continuity
theorem `continuousOn_Icc_extendFrom_Ioo` asks for a regular codomain and its identification
theorem `eq_lim_at_left_extendFrom_Ioo` for a Hausdorff one. Here the end values are given, and
`TauCeti.continuousOn_Icc_extendIoo` needs neither. -/
noncomputable def extendIoo (a b : α) (u v : X) (g : α → X) : α → X :=
  fun x => if x ≤ a then u else if b ≤ x then v else g x

/-- The defining equation of `TauCeti.extendIoo`, for case analysis at an arbitrary point. -/
@[grind =]
theorem extendIoo_apply :
    extendIoo a b u v g x = if x ≤ a then u else if b ≤ x then v else g x :=
  -- Parenthesised: a bare `rfl` would demand that the body of `extendIoo` be exposed.
  (rfl)

/-- Inside the open interval the extension is the function itself. -/
@[simp]
theorem extendIoo_apply_of_mem_Ioo (hx : x ∈ Ioo a b) : extendIoo a b u v g x = g x := by
  simp [extendIoo, hx.1.not_ge, hx.2.not_ge]

/-- At and below the left end the extension takes the prescribed value `u`. -/
@[simp]
theorem extendIoo_apply_of_le_left (hx : x ≤ a) : extendIoo a b u v g x = u := by
  simp [extendIoo, hx]

/-- Above the left end and at or above the right end the extension takes the prescribed value `v`.
These are exactly the conditions of the second branch, so together with
`TauCeti.extendIoo_apply_of_mem_Ioo` and `TauCeti.extendIoo_apply_of_le_left` this computes the
extension at every point, degenerate intervals included. -/
@[simp]
theorem extendIoo_apply_of_left_lt_of_right_le (hax : a < x) (hx : b ≤ x) :
    extendIoo a b u v g x = v := by
  simp [extendIoo, hax.not_ge, hx]

/-- **A function continuous on an open interval and converging at both ends extends continuously
to the closed interval.** The extension is `TauCeti.extendIoo` by the two limits; being handed
them, it asks nothing of `X` beyond a topology. No nondegeneracy `a < b` is assumed: otherwise
`Icc a b` has at most one point. -/
theorem continuousOn_Icc_extendIoo [TopologicalSpace α] [OrderClosedTopology α]
    [TopologicalSpace X] (hg : ContinuousOn g (Ioo a b)) (hu : Tendsto g (𝓝[>] a) (𝓝 u))
    (hv : Tendsto g (𝓝[<] b) (𝓝 v)) : ContinuousOn (extendIoo a b u v g) (Icc a b) := by
  rcases le_or_gt b a with hab | hab
  · exact (subsingleton_Icc_of_ge hab).continuousOn _
  have hleft : ContinuousWithinAt (extendIoo a b u v g) (Icc a b) a := by
    refine ContinuousWithinAt.mono ?_ Icc_subset_Ici_self
    rw [← insert_Ioi, continuousWithinAt_insert_self]
    have heq : g =ᶠ[𝓝[>] a] extendIoo a b u v g := by
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy using (extendIoo_apply_of_mem_Ioo hy).symm
    simpa only [ContinuousWithinAt, extendIoo_apply_of_le_left le_rfl] using hu.congr' heq
  have hright : ContinuousWithinAt (extendIoo a b u v g) (Icc a b) b := by
    refine ContinuousWithinAt.mono ?_ Icc_subset_Iic_self
    rw [← insert_Iio, continuousWithinAt_insert_self]
    have heq : g =ᶠ[𝓝[<] b] extendIoo a b u v g := by
      filter_upwards [Ioo_mem_nhdsLT hab] with y hy using (extendIoo_apply_of_mem_Ioo hy).symm
    simpa only [ContinuousWithinAt, extendIoo_apply_of_left_lt_of_right_le hab le_rfl] using
      hv.congr' heq
  intro x hx
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with rfl | rfl | hx
  · exact hleft
  · exact hright
  · have hmem : Ioo a b ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
    refine ContinuousAt.continuousWithinAt ((hg.continuousAt hmem).congr ?_)
    filter_upwards [hmem] with y hy using (extendIoo_apply_of_mem_Ioo hy).symm

end TauCeti
