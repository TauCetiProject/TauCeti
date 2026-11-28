/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
import TauCeti.Algebra.Order.Ring.SchurInequality
import TauCeti.Analysis.Convex.Quasiconvex

/-!
# Schur's inequality with quasiconvex weights

Let `f` be quasiconvex on a set `s` of a linearly ordered field. For `x`, `y`, `z ∈ s` with
`0 ≤ f x`, `0 ≤ f y`, `0 ≤ f z`,

`0 ≤ f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y)`,

and if the three values of `f` are positive, equality holds exactly when `x = y = z`. This
extends Schur's inequality and its equality case (Mitrinović, *Analytic Inequalities*, §2.17,
Thm 1, p. 119), where the weights are the powers `x ^ t`, `y ^ t`, `z ^ t`. Monotone, antitone and
convex functions are quasiconvex, so this contains the forms of Schur's inequality with monotone,
antitone or convex weights. For `u ≤ v ≤ w` in `s`, quasiconvexity bounds the middle weight
`f v` by the larger of `f u` and `f w` (`QuasiconvexOn.le_max_of_mem_Icc`), which is the
hypothesis of the ring form `TauCeti.schur_inequality_of_mid_le`.

## Main results

* `QuasiconvexOn.schur_inequality`: Schur's inequality with nonnegative quasiconvex weights.
* `QuasiconvexOn.schur_inequality_eq_zero_iff`: for positive weights, equality holds exactly when
  `x = y = z`.
-/

public section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜}
  {x y z : 𝕜}

/-- **Schur's inequality** with quasiconvex weights: if `f` is quasiconvex on `s` and nonnegative
at `x`, `y`, `z ∈ s`, then `0 ≤ f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y)`.
-/
theorem QuasiconvexOn.schur_inequality (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ s) (hfx : 0 ≤ f x) (hfy : 0 ≤ f y) (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) :=
  TauCeti.schur_inequality_of_mid_le
    (fun _ hu _ _ _ hw huv hvw ↦ le_max_iff.1 (hf.le_max_of_mem_Icc hu hw ⟨huv, hvw⟩)) hx hy hz
    hfx hfy hfz

/-- The equality case of Schur's inequality with quasiconvex weights: if `f` is quasiconvex on
`s` and positive at `x`, `y`, `z ∈ s`, then
`f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y) = 0` exactly when `x = y = z`. -/
theorem QuasiconvexOn.schur_inequality_eq_zero_iff (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s)
    (hy : y ∈ s) (hz : z ∈ s) (hfx : 0 < f x) (hfy : 0 < f y) (hfz : 0 < f z) :
    f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 ↔
      x = y ∧ y = z :=
  TauCeti.schur_inequality_eq_zero_iff_of_mid_le
    (fun _ hu _ _ _ hw huv hvw ↦ le_max_iff.1 (hf.le_max_of_mem_Icc hu hw ⟨huv, hvw⟩)) hx hy hz
    hfx hfy hfz

end
