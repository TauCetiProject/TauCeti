/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.Singular.LocalHomology.FixedPointIndex

/-!
# Regression examples: the fixed-point index of a degenerate fixed point

On `ℝ`, the map `x ↦ x + x³` has `0` as its only fixed point, and this fixed point is degenerate:
the derivative there is `1`, so `det (1 - Dφ(0)) = 0` and the signed count of nondegenerate fixed
points does not apply directly. The example computes its fixed-point index
`ContinuousMap.fixedPointIndex` as `-1`, through the homotopy `x ↦ x + x³ + t x`, `t ∈ [0, 1]`:

* every map of the homotopy has `0` as its only fixed point, so the fixed set of the homotopy is
  `[0, 1] × {0}`, which is compact, and `ContinuousMap.fixedPointIndex_eq_of_homotopy` applies;
* the end map `x ↦ x + x³ + x` has derivative `2` at `0`, so its index is
  `sign (1 - 2) = -1` by `ContinuousMap.fixedPointIndex_eq_sign_det`.
-/

open Set TopologicalSpace

-- The degenerate fixed point `0` of `x ↦ x + x³` on `ℝ` has fixed-point index `-1`.
example :
    (⟨fun x ↦ (x : ℝ) + (x : ℝ) ^ 3, by fun_prop⟩ : C((⊤ : Opens ℝ), ℝ)).fixedPointIndex = -1 := by
  let H : ContinuousMap.Homotopy
      (⟨fun x ↦ (x : ℝ) + (x : ℝ) ^ 3, by fun_prop⟩ : C((⊤ : Opens ℝ), ℝ))
      ⟨fun x ↦ (x : ℝ) + (x : ℝ) ^ 3 + x, by fun_prop⟩ :=
    { toFun := fun p ↦ (p.2 : ℝ) + (p.2 : ℝ) ^ 3 + (p.1 : ℝ) * p.2
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }
  -- A fixed point `x` of `x ↦ x + x³ + t x` satisfies `x (x² + t) = 0` with `t ≥ 0`, so `x = 0`.
  have hfix : ∀ (t : unitInterval) (x : (⊤ : Opens ℝ)),
      (x : ℝ) + (x : ℝ) ^ 3 + (t : ℝ) * x = x ↔ (x : ℝ) = 0 := by
    intro t x
    constructor
    · intro h
      have h' : (x : ℝ) * ((x : ℝ) ^ 2 + t) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h0 | h0
      · exact h0
      · nlinarith [sq_nonneg (x : ℝ), t.2.1]
    · intro h
      simp [h]
  have hH : {p : unitInterval × (⊤ : Opens ℝ) | H p = p.2} = univ ×ˢ {⟨0, trivial⟩} := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_univ, mem_singleton_iff, true_and, Subtype.ext_iff]
    exact hfix p.1 p.2
  rw [ContinuousMap.fixedPointIndex_eq_of_homotopy H (hH ▸ isCompact_univ.prod isCompact_singleton)]
  -- The derivative of `x ↦ x + x³ + x` at `0` is `2`, and `sign det (1 - 2) = -1`.
  have hd : HasDerivAt (fun x : ℝ ↦ x + x ^ 3 + x) 2 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).add ((hasDerivAt_id' (0 : ℝ)).pow 3)).add
      (hasDerivAt_id' (0 : ℝ))
    norm_num at this
    exact this
  have hdet : (ContinuousLinearMap.id ℝ ℝ - ContinuousLinearMap.toSpanSingleton ℝ 2).det = -1 := by
    rw [ContinuousLinearMap.det, LinearMap.det_ring]
    norm_num
  rw [ContinuousMap.fixedPointIndex_eq_sign_det (φ := fun x : ℝ ↦ x + x ^ 3 + x) (fun _ ↦ rfl)
    (x := ⟨0, trivial⟩) ?_ hd.hasFDerivAt (by rw [hdet]; norm_num), hdet]
  · simp
  · ext x
    simpa [Subtype.ext_iff] using hfix 1 x
