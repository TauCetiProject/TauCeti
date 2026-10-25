/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Hofer

/-!
# Normalizing a large differential by rescaling

Hofer point selection on a closed ball produces an affine rescaling whose differential has
norm one at the origin and norm at most two on a controlled ball. The radius of that ball
is bounded below by one quarter of the original radius times the original differential norm.
Thus a diverging radius--derivative product gives expanding domains with uniformly bounded
differentials, as needed when extracting bubbles from a sequence of maps.

The source is any real Banach space; compactness and finite dimensionality are unnecessary.
Only continuity of the differential on the original closed ball is assumed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.2 (rescaling at points with large derivative).
* Mathlib's `hofer`, following H. Hofer and C. Viterbo, *The Weinstein conjecture in the
  presence of holomorphic spheres*, supplies the point selection.
-/

public section

open Metric Set

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Select a nearby center and normalize the differential by a positive domain dilation.
The normalized differential is one at zero and at most two throughout the rescaled closed ball.
The rescaling stays inside the original ball, and its radius retains a quarter of the original
radius--derivative product. -/
theorem exists_pos_norm_fderiv_rescale_le {u : E → F} {x : E} {r : ℝ}
    (hr : 0 < r) (hu : ContinuousOn (fderiv ℝ u) (closedBall x r))
    (hx : 0 < ‖fderiv ℝ u x‖) :
    ∃ a : E, ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ dist a x ≤ r / 2 ∧
      r / 4 * ‖fderiv ℝ u x‖ ≤ R ∧ d * R ≤ r / 4 ∧
      MapsTo (fun z ↦ a + d • z) (closedBall 0 R) (closedBall x r) ∧
      ‖fderiv ℝ (fun z ↦ u (a + d • z)) 0‖ = 1 ∧
      ∀ z ∈ closedBall 0 R, ‖fderiv ℝ (fun w ↦ u (a + d • w)) z‖ ≤ 2 := by
  -- Apply Hofer on the complete closed ball, so no extension of the differential is needed.
  let X := closedBall x r
  have : CompleteSpace X := isClosed_closedBall.completeSpace_coe
  let x₀ : X := ⟨x, mem_closedBall_self hr.le⟩
  have hcont : Continuous (fun y : X ↦ ‖fderiv ℝ u y‖) :=
    (hu.comp_continuous continuous_subtype_val Subtype.coe_prop).norm
  obtain ⟨ε, hε, a, hεr, hax, hprod, hbound⟩ :=
    hofer x₀ (r / 4) (by positivity) hcont (fun _ ↦ norm_nonneg _)
  have hax' : dist (a : E) x ≤ r / 2 := by
    simpa only [Subtype.dist_eq, x₀, show 2 * (r / 4) = r / 2 by ring] using hax
  have hL : 0 < ‖fderiv ℝ u a‖ := by
    have hpos : 0 < r / 4 * ‖fderiv ℝ u x‖ := mul_pos (by positivity) hx
    exact pos_of_mul_pos_right (hpos.trans_le hprod) hε.le
  let d := ‖fderiv ℝ u a‖⁻¹
  let R := ε * ‖fderiv ℝ u a‖
  have hd : 0 < d := inv_pos.mpr hL
  have hR : 0 < R := mul_pos hε hL
  have hdR : d * R = ε := by dsimp [d, R]; field_simp
  -- The reciprocal differential norm normalizes the derivative and transports the controlled ball.
  have hnear (z : E) (hz : z ∈ closedBall 0 R) : dist (a + d • z) a ≤ ε := by
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hd.le]
    calc
      d * ‖z‖ ≤ d * R := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hd.le
      _ = ε := hdR
  have hmaps : MapsTo (fun z ↦ (a : E) + d • z) (closedBall 0 R) (closedBall x r) := by
    intro z hz
    apply mem_closedBall.mpr
    calc
      dist ((a : E) + d • z) x ≤ dist ((a : E) + d • z) a + dist (a : E) x :=
        dist_triangle _ _ _
      _ ≤ ε + r / 2 := add_le_add (hnear z hz) hax'
      _ ≤ r := by linarith
  have hderiv (z : E) : fderiv ℝ (fun w ↦ u ((a : E) + d • w)) z =
      d • fderiv ℝ u ((a : E) + d • z) := by
    rw [fderiv_comp_smul (f := fun w ↦ u ((a : E) + w)), fderiv_comp_add_left]
  refine ⟨a, d, R, hd, hR, hax', hprod, hdR ▸ hεr, hmaps, ?_, ?_⟩
  · rw [hderiv]
    simp [d, norm_smul, Real.norm_of_nonneg hd.le, hL.ne']
  · intro z hz
    have h := hbound ⟨(a : E) + d • z, hmaps hz⟩ (by
      simpa only [Subtype.dist_eq, dist_comm] using hnear z hz)
    rw [hderiv, norm_smul, Real.norm_of_nonneg hd.le]
    calc
      d * ‖fderiv ℝ u ((a : E) + d • z)‖ ≤ d * (2 * ‖fderiv ℝ u a‖) :=
        mul_le_mul_of_nonneg_left h hd.le
      _ = 2 := by dsimp [d]; field_simp

end TauCeti
