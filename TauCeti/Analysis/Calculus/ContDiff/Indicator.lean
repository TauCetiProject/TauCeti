/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smoothness of an indicator function

Cutting a `Cⁿ` function `f` off along a set `s` keeps it `Cⁿ` when the cut happens where `f` is
already zero: if the topological support of `f` misses the frontier of `s`, the indicator
`s.indicator f` is `Cⁿ`. Near a point of the interior of `s` it is `f`, near a point outside the
closure of `s` it is `0`, and near a point outside `tsupport f` both `f` and the indicator vanish.
This is the smooth counterpart of Mathlib's `continuous_indicator`.

It is how a smooth compactly supported function on the whole space whose support stays away from
the frontier of an open set `Ω` is turned into a test function supported in `Ω`. Conversely, a
function that is `Cⁿ` on an open set `U` and vanishes on `U` off a closed subset of `U` extends by
zero to a `Cⁿ` function on the whole space.

## Main declarations

* `ContDiff.indicator_of_disjoint_frontier`: the indicator of a `Cⁿ` function along a set whose
  frontier misses its support is `Cⁿ`.
* `ContDiffOn.contDiff_indicator_of_isClosed`: the extension by zero off an open set `U` of a
  function that is `Cⁿ` on `U` and vanishes on `U` off a closed subset of `U` is `Cⁿ`.
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {s : Set E} {f : E → F}

/-- **Smoothness of an indicator.** If `f` is `Cⁿ` and its topological support misses the
frontier of `s`, then `s.indicator f` is `Cⁿ`. -/
theorem ContDiff.indicator_of_disjoint_frontier (hf : ContDiff 𝕜 n f)
    (hs : Disjoint (tsupport f) (frontier s)) : ContDiff 𝕜 n (s.indicator f) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ tsupport f
  · have hxf : x ∉ frontier s := hs.notMem_of_mem_left hx
    by_cases hxs : x ∈ closure s
    · -- A support point in the closure but off the frontier is interior: there the indicator
      -- is `f`.
      have hxi : x ∈ interior s := by
        by_contra hxi
        exact hxf ⟨hxs, hxi⟩
      exact hf.contDiffAt.congr_of_eventuallyEq <| mem_of_superset
        (isOpen_interior.mem_nhds hxi) fun y hy => indicator_of_mem (interior_subset hy) f
    · -- Outside the closure of `s` the indicator is `0`.
      exact contDiffAt_const.congr_of_eventuallyEq <| mem_of_superset
        (isClosed_closure.isOpen_compl.mem_nhds hxs) fun y hy =>
          indicator_of_notMem (fun hys => hy (subset_closure hys)) f
  · -- Outside the support both `f` and the indicator vanish near `x`.
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq <|
      (notMem_tsupport_iff_eventuallyEq.1 hx).mono fun y hy => indicator_apply_eq_zero.2 fun _ => hy

/-- **Extension by zero.** If `f` is `Cⁿ` on an open set `U` and vanishes on `U` off a closed set
`K ⊆ U`, then its extension by zero `U.indicator f` is `Cⁿ` on the whole space. -/
theorem ContDiffOn.contDiff_indicator_of_isClosed {U K : Set E} (hf : ContDiffOn 𝕜 n f U)
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hfK : U ∩ Function.support f ⊆ K) :
    ContDiff 𝕜 n (U.indicator f) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · -- On the open set `U` the indicator is `f`.
    exact (hf.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq <|
      mem_of_superset (hU.mem_nhds hx) fun y hy => indicator_of_mem hy f
  · -- Off `U`, hence off the closed set `K`, the indicator vanishes near `x`.
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq <|
      mem_of_superset (hK.isOpen_compl.mem_nhds fun h => hx (hKU h)) fun y hy =>
        indicator_apply_eq_zero.2 fun hyU => Function.notMem_support.1 fun h => hy (hfK ⟨hyU, h⟩)
