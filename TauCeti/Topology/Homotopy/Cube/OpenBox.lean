/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Radius
public import TauCeti.Topology.Homotopy.Extension.Ball

/-!
# Radial deformation onto the bottom and sides of a cube cylinder

Projection from height two above the cube's centre gives a deformation `cubeLiftDeform`
from the bottom-and-sides subspace to each point of the cylinder, reaching that point at
`cubeLiftTime`. This time vanishes exactly on `cylinderExtensionDomain (Cube.boundary N)`.
The construction includes the zero-dimensional cube. It is the geometric input for relative
homotopy lifting along the bottom-and-sides inclusion of `I × Iᴺ`; the square (`N = Unit`)
is the open-box case. Its denominator and initial projection reuse the unit-ball radial projection
from `TauCeti.Topology.Homotopy.Extension.Ball` through
`cubeHomeomorphClosedBall`.

## References

* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
-/

public noncomputable section

open Set unitInterval

namespace TauCeti

variable {N : Type*} [Fintype N]

/-- The radial denominator for the bottom-and-sides projection. -/
def cubeLiftDen (x : I × (N → I)) : ℝ :=
  ballRadialDen (x.1, cubeHomeomorphClosedBall N x.2)

theorem cubeLiftDen_def (x : I × (N → I)) :
    cubeLiftDen x = max (2 - (x.1 : ℝ)) (2 * cubeRadius x.2) := by
  rw [cubeLiftDen, ballRadialDen_def, norm_cubeHomeomorphClosedBall]

theorem one_le_cubeLiftDen (x : I × (N → I)) : 1 ≤ cubeLiftDen x := by
  rw [cubeLiftDen_def]
  exact le_max_of_le_left (by linarith [x.1.2.2])

theorem cubeLiftDen_le_two (x : I × (N → I)) : cubeLiftDen x ≤ 2 := by
  rw [cubeLiftDen_def]
  exact max_le (by linarith [x.1.2.1]) (by linarith [cubeRadius_le_one x.2])

/-- Time at which the radial deformation reaches `x`. -/
def cubeLiftTime (x : I × (N → I)) : ℝ := 2 / cubeLiftDen x - 1

theorem cubeLiftTime_def (x : I × (N → I)) :
    cubeLiftTime x = 2 / cubeLiftDen x - 1 := (rfl)

theorem cubeLiftTime_mem (x : I × (N → I)) : cubeLiftTime x ∈ I := by
  have hd : 0 < cubeLiftDen x := lt_of_lt_of_le one_pos (one_le_cubeLiftDen x)
  constructor
  · rw [cubeLiftTime, sub_nonneg, le_div_iff₀ hd]
    linarith [cubeLiftDen_le_two x]
  · rw [cubeLiftTime, sub_le_iff_le_add, div_le_iff₀ hd]
    linarith [one_le_cubeLiftDen x]

theorem continuous_cubeLiftTime : Continuous (cubeLiftTime (N := N)) := by
  have hd : Continuous (cubeLiftDen (N := N)) := by
    have h : Continuous fun x : I × (N → I) ↦
        max (2 - (x.1 : ℝ)) (2 * cubeRadius x.2) :=
      (continuous_const.sub (by fun_prop)).max
        (continuous_const.mul (continuous_cubeRadius.comp continuous_snd))
    convert h using 1
    exact funext cubeLiftDen_def
  exact (continuous_const.div hd fun x ↦
    (lt_of_lt_of_le one_pos (one_le_cubeLiftDen x)).ne').sub continuous_const

@[simp]
theorem cubeLiftTime_eq_zero {x : I × (N → I)}
    (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) : cubeLiftTime x = 0 := by
  have hd : cubeLiftDen x = 2 := by
    refine le_antisymm (cubeLiftDen_le_two x) ?_
    rw [cubeLiftDen_def]
    rcases mem_cylinderExtensionDomain_iff.1 hx with ht | hz
    · exact le_max_of_le_left (by simp [ht])
    · exact le_max_of_le_right (by rw [(cubeRadius_eq_one_iff x.2).2 hz]; norm_num)
  simp [cubeLiftTime, hd]

/-- Run the radial segment from the bottom and sides, stopping when it reaches `x`. -/
def cubeLiftDeform (s : I) (x : I × (N → I)) : I × (N → I) :=
  let a := cubeLiftTime x - min (cubeLiftTime x) (s : ℝ)
  (projIcc 0 1 zero_le_one ((x.1 : ℝ) + a * (x.1 - 2)), cubeScale (1 + a) x.2)

theorem cubeLiftDeform_def (s : I) (x : I × (N → I)) :
    cubeLiftDeform s x =
      let a := cubeLiftTime x - min (cubeLiftTime x) (s : ℝ)
      (projIcc 0 1 zero_le_one ((x.1 : ℝ) + a * (x.1 - 2)), cubeScale (1 + a) x.2) := (rfl)

theorem continuous_cubeLiftDeform :
    Continuous fun y : I × (I × (N → I)) ↦ cubeLiftDeform y.1 y.2 := by
  have ht := continuous_cubeLiftTime.comp (continuous_snd :
    Continuous (Prod.snd : I × (I × (N → I)) → _))
  have ha : Continuous fun y : I × (I × (N → I)) ↦
      cubeLiftTime y.2 - min (cubeLiftTime y.2) (y.1 : ℝ) :=
    ht.sub (ht.min (by fun_prop))
  have hx : Continuous fun y : I × (I × (N → I)) ↦ (y.2.1 : ℝ) := by fun_prop
  exact (continuous_projIcc.comp (hx.add (ha.mul (hx.sub continuous_const)))).prodMk
    (continuous_cubeScale.comp ((continuous_const.add ha).prodMk (by fun_prop)))

@[simp]
theorem cubeLiftDeform_one (x : I × (N → I)) : cubeLiftDeform 1 x = x := by
  simp [cubeLiftDeform, min_eq_left (cubeLiftTime_mem x).2]

@[simp]
theorem cubeLiftDeform_of_mem (s : I) {x : I × (N → I)}
    (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) : cubeLiftDeform s x = x := by
  simp [cubeLiftDeform, cubeLiftTime_eq_zero hx, min_eq_left s.2.1]

@[simp]
theorem cubeLiftDeform_time (x : I × (N → I)) :
    cubeLiftDeform ⟨cubeLiftTime x, cubeLiftTime_mem x⟩ x = x := by
  simp [cubeLiftDeform]

theorem cubeLiftDeform_zero_mem (x : I × (N → I)) :
    cubeLiftDeform 0 x ∈ cylinderExtensionDomain (Cube.boundary N) := by
  have hd : 0 < cubeLiftDen x := lt_of_lt_of_le one_pos (one_le_cubeLiftDen x)
  have ht := (cubeLiftTime_mem x).1
  have ha : 1 + cubeLiftTime x = 2 / cubeLiftDen x := by rw [cubeLiftTime]; ring
  -- Transfer the ball projection's landing law; only the radial coordinate formulas differ.
  let p := (x.1, cubeHomeomorphClosedBall N x.2)
  have hden : ballRadialDen p = cubeLiftDen x := rfl
  have hp := ballRadialProjection_spec p
  have hnorm : ‖(ballRadialProjection p).2‖ =
      2 / cubeLiftDen x * cubeRadius x.2 := by
    rw [ballRadialProjection_def, hden, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos two_pos hd), norm_cubeHomeomorphClosedBall]
  have hs : 0 ≤ 2 / cubeLiftDen x := by positivity
  have hr : 2 / cubeLiftDen x * cubeRadius x.2 ≤ 1 := by
    rw [← hnorm]
    exact mem_closedBall_zero_iff.1 hp.2.1
  have htime : (x.1 : ℝ) + cubeLiftTime x * (x.1 - 2) =
      (ballRadialProjection p).1 := by
    rw [ballRadialProjection_def, hden, cubeLiftTime]
    dsimp only [p]
    ring
  simp only [cubeLiftDeform, Icc.coe_zero, min_eq_right ht, sub_zero,
    mem_cylinderExtensionDomain_iff]
  rcases hp.2.2 with h0 | hS
  · left
    rw [htime, h0]
    exact projIcc_left zero_le_one
  · right
    rw [← cubeRadius_eq_one_iff, ha, cubeRadius_cubeScale hs hr, ← hnorm]
    exact mem_sphere_zero_iff_norm.1 hS

theorem cubeLiftTime_eq_zero_iff (x : I × (N → I)) :
    cubeLiftTime x = 0 ↔ x ∈ cylinderExtensionDomain (Cube.boundary N) := by
  refine ⟨fun hx ↦ ?_, cubeLiftTime_eq_zero⟩
  have ht : (⟨cubeLiftTime x, cubeLiftTime_mem x⟩ : I) = 0 := Subtype.ext hx
  have he := cubeLiftDeform_time x
  rw [ht] at he
  exact he ▸ cubeLiftDeform_zero_mem x

/-- The initial radial projection of the top face lands on the bottom for radius at most
`1 / 2`, and otherwise rescales by the reciprocal radius. -/
theorem cubeLiftDeform_zero_one (z : N → I) :
    cubeLiftDeform 0 (1, z) =
      if cubeRadius z ≤ 1 / 2 then (0, cubeScale 2 z)
      else (projIcc 0 1 zero_le_one (2 - 1 / cubeRadius z),
        cubeScale (1 / cubeRadius z) z) := by
  have ht := (cubeLiftTime_mem ((1 : I), z)).1
  by_cases hz : cubeRadius z ≤ 1 / 2
  · have hd : cubeLiftDen ((1 : I), z) = 1 := by
      rw [cubeLiftDen_def]
      norm_num only [Icc.coe_one]
      exact max_eq_left (by linarith)
    rw [ite_eq_left hz]
    norm_num [cubeLiftDeform_def, cubeLiftTime_def, hd]
  · have hd : cubeLiftDen ((1 : I), z) = 2 * cubeRadius z := by
      rw [cubeLiftDen_def]
      norm_num only [Icc.coe_one]
      exact max_eq_right (by linarith)
    have he : 2 / (2 * cubeRadius z) = 1 / cubeRadius z := by ring
    rw [ite_eq_right hz]
    simp only [cubeLiftDeform_def, Icc.coe_zero, min_eq_right ht, sub_zero]
    rw [cubeLiftTime_def, hd, he]
    simp only [Icc.coe_one]
    have ha : (1 : ℝ) + (1 / cubeRadius z - 1) * (1 - 2) =
        2 - 1 / cubeRadius z := by ring
    rw [ha]
    congr 2
    ring

/-- Above radius `1 / 2`, the initial projection of the top face lies on a boundary side. -/
theorem cubeLiftDeform_zero_one_snd_mem_boundary {z : N → I} (hz : 1 / 2 < cubeRadius z) :
    (cubeLiftDeform 0 (1, z)).2 ∈ Cube.boundary N := by
  rw [cubeLiftDeform_zero_one, ite_eq_right (not_le_of_gt hz)]
  have hr : cubeRadius z ≠ 0 := ne_of_gt (lt_trans (by norm_num) hz)
  have hs : 0 ≤ 1 / cubeRadius z := le_of_lt (one_div_pos.2 (lt_trans (by norm_num) hz))
  apply (cubeRadius_eq_one_iff _).1
  rw [cubeRadius_cubeScale hs (by simp [hr]), one_div_mul_cancel hr]

omit [Fintype N] in
/-- For `x` in `{0} × I^(Option N) ∪ I × ∂I^(Option N)`, either `x.2 none ∈ {0, 1}`, or the point
obtained from `x.2` by replacing its `none` coordinate with `x.1` (via
`piOptionEquivProdHomeomorph`, after dropping `x.2 none`) lies in `∂I^(Option N)`. -/
theorem cases_of_mem_cylinderExtensionDomain_boundary
    {x : I × (Option N → I)} (hx : x ∈ cylinderExtensionDomain (Cube.boundary (Option N))) :
    (x.2 none = 0 ∨ x.2 none = 1) ∨
      (piOptionEquivProdHomeomorph fun _ : Option N => I).symm (x.1, fun i => x.2 (some i)) ∈
        Cube.boundary (Option N) := by
  rcases mem_cylinderExtensionDomain_iff.1 hx with hx | hx
  · exact .inr (piOptionEquivProdHomeomorph_symm_mem_boundary
      (Cube.mem_prodBoundary_iff.2 (.inl (.inl hx))))
  · rcases Cube.boundary_option_iff.1 hx with hx | hx
    · exact .inl hx
    · exact .inr (piOptionEquivProdHomeomorph_symm_mem_boundary
        (Cube.mem_prodBoundary_iff.2 (.inr hx)))

end TauCeti
