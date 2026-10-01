/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer

/-!
# The geodesic line through two points of the upper half-plane

`geodesicBetween z w` is a parametrised geodesic line with `z` at parameter `0` and `w` at
parameter `dist z w`. For distinct `z` and `w` it is the unique such line
(`eq_geodesicBetween_of_geodesicLine_eq`), because an element of `PSL(2, ℝ)` fixing two distinct
points is the identity, and so it transforms naturally under the action (`geodesicBetween_smul`).
For `z = w` the two conditions only fix the starting point, and `geodesicBetween z z` is an
arbitrary chosen line through `z`; every statement about direction therefore assumes `z ≠ w`.
Reparametrisation is right multiplication by the dilations `dilation s : z ↦ exp s * z`
(`geodesicLine_mul_dilation`) and by `pslS` (`geodesicLine_mul_pslS`); together they give the
reversed line `geodesicBetween w z`.

Source: Katok, *Fuchsian groups, geodesic flows on surfaces of constant negative curvature and
symbolic coding of geodesics*, Clay Math. Proc. 10 (2010), §3 p. 10 (Theorem 3.1 and the
remark after it: any two points of `ℍ` are joined by a unique geodesic).
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation dilation)

/-- A geodesic line from `z` to `w`: `z` sits at parameter `0` and `w` at parameter `dist z w`.
For `z ≠ w` this determines the line (`eq_geodesicBetween_of_geodesicLine_eq`); for `z = w` it is
an arbitrary chosen line through `z`. -/
def geodesicBetween (z w : ℍ) : PSL(2, ℝ) :=
  Classical.choose (exists_geodesicLine_zero_eq_and_dist_eq z w)

/-- The geodesic line from `z` to `w` starts at `z`. -/
@[simp]
theorem geodesicLine_geodesicBetween_zero (z w : ℍ) :
    geodesicLine (geodesicBetween z w) 0 = z :=
  (Classical.choose_spec (exists_geodesicLine_zero_eq_and_dist_eq z w)).1

/-- The geodesic line from `z` to `w` reaches `w` at parameter `dist z w`. -/
@[simp]
theorem geodesicLine_geodesicBetween_dist (z w : ℍ) :
    geodesicLine (geodesicBetween z w) (dist z w) = w :=
  (Classical.choose_spec (exists_geodesicLine_zero_eq_and_dist_eq z w)).2

/-- `z` lies on the geodesic line from `z` to `w`. -/
theorem mem_range_geodesicLine_geodesicBetween_left (z w : ℍ) :
    z ∈ Set.range (geodesicLine (geodesicBetween z w)) :=
  ⟨0, geodesicLine_geodesicBetween_zero z w⟩

/-- `w` lies on the geodesic line from `z` to `w`. -/
theorem mem_range_geodesicLine_geodesicBetween_right (z w : ℍ) :
    w ∈ Set.range (geodesicLine (geodesicBetween z w)) :=
  ⟨dist z w, geodesicLine_geodesicBetween_dist z w⟩

/-- **Uniqueness of the geodesic through two distinct points**: for `z ≠ w`, a parametrised
geodesic line with `z` at parameter `0` and `w` at parameter `dist z w` is `geodesicBetween z w`.
(For `z = w` the two conditions coincide and do not determine the line.) -/
theorem eq_geodesicBetween_of_geodesicLine_eq {g : PSL(2, ℝ)} {z w : ℍ} (hzw : z ≠ w)
    (h0 : geodesicLine g 0 = z) (hd : geodesicLine g (dist z w) = w) :
    g = geodesicBetween z w := by
  -- `(geodesicBetween z w)⁻¹ * g` fixes the two distinct points `I` and `i exp (dist z w)`
  have key : ∀ t : ℝ, geodesicLine g t = geodesicLine (geodesicBetween z w) t →
      ((geodesicBetween z w)⁻¹ * g) • geodesicLine 1 t = geodesicLine 1 t := by
    intro t ht
    have h1 := smul_geodesicLine (geodesicBetween z w) 1 t
    rw [mul_one] at h1
    rw [smul_geodesicLine, mul_one, ← smul_geodesicLine, ht, ← h1, inv_smul_smul]
  have h := eq_one_of_smul_eq_self_of_smul_eq_self
    (key 0 (by rw [h0, geodesicLine_geodesicBetween_zero]))
    (key (dist z w) (by rw [hd, geodesicLine_geodesicBetween_dist]))
    (fun h ↦ (dist_pos.2 hzw).ne' (geodesicLine_injective 1 h))
  rwa [inv_mul_eq_one, eq_comm] at h

/-- The geodesic line through two distinct points transforms naturally under the action. -/
theorem geodesicBetween_smul (h : PSL(2, ℝ)) {z w : ℍ} (hzw : z ≠ w) :
    geodesicBetween (h • z) (h • w) = h * geodesicBetween z w := by
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq ((MulAction.injective h).ne hzw) ?_ ?_
  · rw [← smul_geodesicLine, geodesicLine_geodesicBetween_zero]
  · rw [(isometry_smul ℍ h).dist_eq, ← smul_geodesicLine, geodesicLine_geodesicBetween_dist]

/-- The geodesic line from `w` back to `z` is the line from `z` to `w`, shifted to start at `w`
and reversed. -/
theorem geodesicBetween_swap {z w : ℍ} (hzw : z ≠ w) :
    geodesicBetween w z = geodesicBetween z w * ↑(dilation (dist z w)) * pslS := by
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq hzw.symm ?_ ?_
  · rw [geodesicLine_mul_pslS, neg_zero, geodesicLine_mul_dilation, add_zero,
      geodesicLine_geodesicBetween_dist]
  · rw [geodesicLine_mul_pslS, geodesicLine_mul_dilation, dist_comm, add_neg_cancel,
      geodesicLine_geodesicBetween_zero]

/-- The geodesic lines from `z` to `w` and from `w` to `z` have the same image. -/
theorem range_geodesicLine_geodesicBetween_swap (z w : ℍ) :
    Set.range (geodesicLine (geodesicBetween w z)) =
      Set.range (geodesicLine (geodesicBetween z w)) := by
  rcases eq_or_ne z w with rfl | hzw
  · rfl
  rw [geodesicBetween_swap hzw, range_geodesicLine_mul_pslS, range_geodesicLine_mul_dilation]

/-- Two distinct points of a geodesic line determine it: the geodesic line through them has the
same image. -/
theorem range_geodesicLine_geodesicBetween_of_mem {g : PSL(2, ℝ)} {z w : ℍ}
    (hz : z ∈ Set.range (geodesicLine g)) (hw : w ∈ Set.range (geodesicLine g)) (hzw : z ≠ w) :
    Set.range (geodesicLine (geodesicBetween z w)) = Set.range (geodesicLine g) := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := hw
  have hst : s ≠ t := fun h ↦ hzw (h ▸ rfl)
  rcases lt_or_gt_of_ne hst with h | h
  · have : geodesicBetween (geodesicLine g s) (geodesicLine g t) = g * ↑(dilation s) := by
      symm
      refine eq_geodesicBetween_of_geodesicLine_eq hzw ?_ ?_
      · rw [geodesicLine_mul_dilation, add_zero]
      · rw [geodesicLine_mul_dilation, dist_geodesicLine, abs_of_neg (by linarith)]
        congr 1
        ring
    rw [this, range_geodesicLine_mul_dilation]
  · have : geodesicBetween (geodesicLine g s) (geodesicLine g t) = g * ↑(dilation s) * pslS := by
      symm
      refine eq_geodesicBetween_of_geodesicLine_eq hzw ?_ ?_
      · rw [geodesicLine_mul_pslS, neg_zero, geodesicLine_mul_dilation, add_zero]
      · rw [geodesicLine_mul_pslS, geodesicLine_mul_dilation, dist_geodesicLine,
          abs_of_pos (by linarith)]
        congr 1
        ring
    rw [this, range_geodesicLine_mul_pslS, range_geodesicLine_mul_dilation]

/-- The geodesic line from `I` up the imaginary axis is the identity's. -/
theorem geodesicBetween_I_geodesicLine_one {d : ℝ} (hd : 0 < d) :
    geodesicBetween UpperHalfPlane.I (geodesicLine 1 d) = 1 := by
  have h0 : geodesicLine 1 0 = UpperHalfPlane.I := by rw [geodesicLine_zero, one_smul]
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq (fun h ↦ hd.ne ?_) h0 ?_
  · exact geodesicLine_injective 1 (h0.trans h)
  · rw [← h0, dist_geodesicLine, zero_sub, abs_neg, abs_of_pos hd]

/-- The geodesic line from `I` to any point is a rotation of the imaginary axis. -/
theorem exists_geodesicBetween_I_eq_rotation (z : ℍ) :
    ∃ θ : ℝ, geodesicBetween UpperHalfPlane.I z = ↑(rotation θ) :=
  exists_rotation_eq_of_smul_I_eq_I
    (by rw [← geodesicLine_zero, geodesicLine_geodesicBetween_zero])

end TauCeti.UpperHalfPlane
