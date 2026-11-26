/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Morse.Sphere.Degenerate
import TauCeti.Geometry.Manifold.Morse.TwoCriticalPoints

/-!
# Examples: a sphere recognized from two degenerate critical points

Let `h` be the height function on the unit sphere `Sᵐ` of a real inner product space of
dimension `m + 1`, in the direction of a unit vector `v` (`TauCeti.sphereHeight`), and let
`f = h - h³ / 3`. The examples below check that `f` lies outside the reach of every argument
through nondegenerate normal forms, and that the sphere theorem for two possibly degenerate
critical points still recognizes `Sᵐ` from it.

* Its differential `(1 - h²) dh` vanishes exactly at the two poles
  (`TauCeti.criticalPoints_cubic_comp_sphereHeight`).
* In the stereographic chart centred at the north pole, with radial coordinate `r`,
  `f = 2 / 3 - r⁴ / 4 + O(r⁶)` (`TauCeti.cubic_comp_sphereHeight_chartAt_symm_sub_mem_Icc`), and
  symmetrically `f = -2 / 3 + r⁴ / 4 + O(r⁶)` at the south pole
  (`TauCeti.cubic_comp_sphereHeight_chartAt_neg_symm_sub_mem_Icc`). So both critical Hessians
  vanish, and in positive dimension `f` is not a Morse function
  (`TauCeti.not_isMorse_cubic_comp_sphereHeight`): Reeb's theorem for Morse functions
  (`TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`) does not apply.
* `f` has exactly two critical points (`TauCeti.totalCriticalCount_cubic_comp_sphereHeight`), so
  the sphere theorem for degenerate critical points
  (`TauCeti.nonempty_homeomorph_sphere_of_two_criticalPoints`) applies and identifies the sphere
  with the standard `Sᵐ`, in particular `S²` for `m = 2`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1 and Remark 1 after it.
-/

open Asymptotics Metric Module Topology
open scoped Manifold ContDiff

namespace TauCeti.Examples.SphereDegenerate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The differential `(1 - h²) dh` of `h - h³ / 3` vanishes exactly at the two poles. -/
example (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) = {v, -v} :=
  criticalPoints_cubic_comp_sphereHeight v

/-- Near the north pole, in the radial coordinate `r = ‖w‖` of the stereographic chart,
`h - h³ / 3 = 2 / 3 - r⁴ / 4 + O(r⁶)`. -/
example (v : sphere (0 : E) 1) :
    (fun w : EuclideanSpace ℝ (Fin n) ↦ ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v)
        ((chartAt (EuclideanSpace ℝ (Fin n)) v).symm w) - (2 / 3 - ‖w‖ ^ 4 / 4)) =O[𝓝 0]
      fun w ↦ ‖w‖ ^ 6 :=
  isBigO_of_le _ fun w ↦ by
    have h := cubic_comp_sphereHeight_chartAt_symm_sub_mem_Icc v w
    rw [Real.norm_eq_abs, abs_le, norm_pow, norm_norm]
    constructor <;> linarith [h.1, h.2, pow_nonneg (norm_nonneg w) 6]

/-- Near the south pole, in the radial coordinate `r = ‖w‖` of the stereographic chart,
`h - h³ / 3 = -2 / 3 + r⁴ / 4 + O(r⁶)`. -/
example (v : sphere (0 : E) 1) :
    (fun w : EuclideanSpace ℝ (Fin n) ↦ ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (-v)).symm w) - (-2 / 3 + ‖w‖ ^ 4 / 4)) =O[𝓝 0]
      fun w ↦ ‖w‖ ^ 6 :=
  isBigO_of_le _ fun w ↦ by
    have h := cubic_comp_sphereHeight_chartAt_neg_symm_sub_mem_Icc v w
    rw [Real.norm_eq_abs, abs_le, norm_pow, norm_norm]
    constructor <;> linarith [h.1, h.2, pow_nonneg (norm_nonneg w) 6]

/-- Both critical Hessians of `h - h³ / 3` vanish, so in positive dimension it is not a Morse
function and Reeb's theorem for Morse functions does not apply to it. -/
example (hn : n ≠ 0) (v : sphere (0 : E) 1) :
    criticalHessian (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) v = 0 ∧
      criticalHessian (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) (-v) = 0 ∧
      ¬IsMorse (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) :=
  ⟨criticalHessian_cubic_comp_sphereHeight_self v, criticalHessian_cubic_comp_sphereHeight_neg v,
    not_isMorse_cubic_comp_sphereHeight hn v⟩

/-- **The sphere theorem recognizes `Sᵐ` from `h - h³ / 3`.** The function has exactly two
critical points, both degenerate, and the sphere theorem for two possibly degenerate critical
points identifies the sphere with the standard `Sᵐ`. -/
example (v : sphere (0 : E) 1) :
    Nonempty (sphere (0 : E) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h := nonempty_homeomorph_sphere_of_two_criticalPoints (I := 𝓡 n)
    ((contDiff_id.sub ((contDiff_id.pow 3).div_const 3)).comp_contMDiff (contMDiff_sphereHeight v))
    (totalCriticalCount_cubic_comp_sphereHeight v)
  rwa [finrank_euclideanSpace_fin] at h

/-- **The case of `S²`.** On the unit sphere of `ℝ³`, the sphere theorem for degenerate critical
points applied to `h - h³ / 3` gives `S²`, although both critical points are degenerate. -/
example (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have h := nonempty_homeomorph_sphere_of_two_criticalPoints (I := 𝓡 2)
    ((contDiff_id.sub ((contDiff_id.pow 3).div_const 3)).comp_contMDiff (contMDiff_sphereHeight v))
    (totalCriticalCount_cubic_comp_sphereHeight v)
  rwa [finrank_euclideanSpace_fin] at h

end TauCeti.Examples.SphereDegenerate
