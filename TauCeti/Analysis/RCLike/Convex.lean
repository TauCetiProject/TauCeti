/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Convexity of half-planes in an `RCLike` field

The open half-planes `{z | r < im z}` and `{z | im z < r}` of an `RCLike` field are convex over
`ℝ`. These are the `RCLike` counterparts of Mathlib's `Complex.convex_halfSpace_im_gt` and
`Complex.convex_halfSpace_im_lt`; over `ℝ`, where `im = 0`, each is either empty or everything.

## Main results

* `RCLike.convex_halfSpace_im_gt`, `RCLike.convex_halfSpace_im_lt`: the open half-planes above
  and below a horizontal line are convex.
-/

public section

namespace RCLike

variable {K : Type*} [RCLike K]

/-- The open half-plane above a horizontal line is convex. -/
theorem convex_halfSpace_im_gt (r : ℝ) : Convex ℝ {z : K | r < im z} :=
  convex_halfSpace_gt imLm.isLinear r

/-- The open half-plane below a horizontal line is convex. -/
theorem convex_halfSpace_im_lt (r : ℝ) : Convex ℝ {z : K | im z < r} :=
  convex_halfSpace_lt imLm.isLinear r

end RCLike
