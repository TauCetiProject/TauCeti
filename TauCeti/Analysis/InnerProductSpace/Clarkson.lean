/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The pointwise Clarkson inequality

For `2 ≤ q` and vectors `a`, `b` of a normed group whose norm satisfies the parallelogram
identity (`InnerProductSpaceable`), in particular of any real or complex inner product space,

`‖a + b‖ ^ q + ‖a - b‖ ^ q ≤ 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q)`.

At `q = 2` this is the parallelogram identity, read as an inequality. For larger `q` it follows
from the parallelogram identity, superadditivity of `t ↦ t ^ (q / 2)` on `[0, ∞)`, and the power
mean inequality `(s + t) ^ r ≤ 2 ^ (r - 1) * (s ^ r + t ^ r)`. Integrating it gives Clarkson's
inequality for `Lᵖ` spaces, `2 ≤ p < ∞`, and with it their uniform convexity.

## Main statements

* `TauCeti.norm_add_rpow_add_norm_sub_rpow_le`: the pointwise Clarkson inequality.

## References

* J. A. Clarkson, *Uniformly convex spaces*, Trans. Amer. Math. Soc. 40 (1936), 396–414.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.10.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpaceable E]

/-- **The pointwise Clarkson inequality.** For `2 ≤ q` and vectors `a`, `b` of a normed group
satisfying the parallelogram identity,
`‖a + b‖ ^ q + ‖a - b‖ ^ q ≤ 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le {q : ℝ} (hq : 2 ≤ q) (a b : E) :
    ‖a + b‖ ^ q + ‖a - b‖ ^ q ≤ 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q) := by
  have hr : 1 ≤ q / 2 := by linarith
  have hsq (x : E) : ‖x‖ ^ q = (‖x‖ ^ 2) ^ (q / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    ring
  -- The power mean inequality for `t ↦ t ^ (q / 2)`, lifted from `ℝ≥0`.
  have hmean (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      (s + t) ^ (q / 2) ≤ 2 ^ (q / 2 - 1) * (s ^ (q / 2) + t ^ (q / 2)) := by
    lift s to NNReal using hs
    lift t to NNReal using ht
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow s t hr
  have hpar : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    simpa only [sq] using InnerProductSpaceable.parallelogram_identity a b
  calc ‖a + b‖ ^ q + ‖a - b‖ ^ q
      = (‖a + b‖ ^ 2) ^ (q / 2) + (‖a - b‖ ^ 2) ^ (q / 2) := by rw [hsq, hsq]
    _ ≤ (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2) ^ (q / 2) :=
      Real.add_rpow_le_rpow_add (by positivity) (by positivity) hr
    _ = 2 ^ (q / 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (q / 2) := by
      rw [hpar, Real.mul_rpow zero_le_two (by positivity)]
    _ ≤ 2 ^ (q / 2) * (2 ^ (q / 2 - 1) * ((‖a‖ ^ 2) ^ (q / 2) + (‖b‖ ^ 2) ^ (q / 2))) := by
      gcongr
      exact hmean _ _ (by positivity) (by positivity)
    _ = 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q) := by
      rw [← mul_assoc, ← Real.rpow_add zero_lt_two, hsq a, hsq b]
      ring_nf

end TauCeti
