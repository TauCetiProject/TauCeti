/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ClosedBall
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Torus
public import TauCeti.Analysis.Complex.ClosedAnnulus

/-!
# The Euler characteristic of a closed annulus

The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` in `ℂ` with `0 < r₁ ≤ r₂` is homeomorphic to `Circle × [r₁, r₂]`
by polar coordinates (`Complex.closedAnnulusHomeomorph`), so its Euler characteristic is
`χ(S¹) · χ([r₁, r₂]) = 0 · 1 = 0`. The degenerate closed annuli are closed balls or empty, so
closed annuli have finite CW type for all radii.

## Main declarations

* `TauCeti.finiteCWType_closedAnnulus`: every closed annulus in `ℂ` has finite CW type.
* `TauCeti.eulerChar_closedAnnulus`: a closed annulus with `0 < r₁ ≤ r₂` has `χ = 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Complex Metric Set

namespace TauCeti

variable {r₁ r₂ : ℝ}

/-- A closed annulus in `ℂ` has finite CW type: for `0 < r₁ ≤ r₂` it is homeomorphic to
`Circle × [r₁, r₂]`, for `r₁ ≤ 0 ≤ r₂` it is the closed ball of radius `r₂`, and otherwise it is
empty. -/
instance finiteCWType_closedAnnulus (r₁ r₂ : ℝ) : FiniteCWType (closedAnnulus r₁ r₂) := by
  rcases le_or_gt r₁ 0 with h₀ | h₀
  · have : closedAnnulus r₁ r₂ = closedBall 0 r₂ := by
      ext z
      rw [mem_closedAnnulus, mem_closedBall_zero_iff]
      exact ⟨And.right, fun h ↦ ⟨h₀.trans (norm_nonneg _), h⟩⟩
    rw [this]
    infer_instance
  rcases le_or_gt r₁ r₂ with h | h
  · have := (convex_Icc r₁ r₂).contractibleSpace (nonempty_Icc.2 h)
    exact (closedAnnulusHomeomorph h₀).finiteCWType
  · have : IsEmpty (closedAnnulus r₁ r₂) :=
      ⟨fun z ↦ (mem_closedAnnulus.1 z.2).1.trans (mem_closedAnnulus.1 z.2).2 |>.not_gt h⟩
    exact FiniteCWType.of_discreteTopology _

/-- A closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁ ≤ r₂` has Euler characteristic zero, that of
`Circle × [r₁, r₂]`. -/
@[simp]
theorem eulerChar_closedAnnulus (h₀ : 0 < r₁) (h : r₁ ≤ r₂) :
    eulerChar (closedAnnulus r₁ r₂) = 0 := by
  have := (convex_Icc r₁ r₂).contractibleSpace (nonempty_Icc.2 h)
  rw [(closedAnnulusHomeomorph h₀).eulerChar_eq, eulerChar_prod, eulerChar_circle, zero_mul]

end TauCeti
