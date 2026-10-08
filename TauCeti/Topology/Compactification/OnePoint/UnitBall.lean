/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The closed unit ball with its boundary collapsed

In a real normed space `E`, the open unit ball is homeomorphic to `E` itself
(`OpenPartialHomeomorph.univUnitBall`).  This file sends the open unit ball onto `E ⊆ OnePoint E`
along that homeomorphism and every other point, in particular the boundary sphere of the closed
unit ball, to `∞`, as a partial equivalence
`TauCeti.unitBallToOnePoint : PartialEquiv E (OnePoint E)`:

* on the open ball it is `univUnitBall.symm` followed by the inclusion `E → OnePoint E`, a
  bijection onto the complement of `∞`;
* every point of norm at least one, in particular the whole boundary sphere, goes to `∞`;
* it is continuous on the closed unit ball (`TauCeti.continuousOn_unitBallToOnePoint`), and its
  inverse is continuous on the complement of `∞`
  (`TauCeti.continuousOn_unitBallToOnePoint_symm`).

Composed with a homeomorphism from `OnePoint E` to a sphere, this is a characteristic map of the
top cell of a sphere, in the shape Mathlib's classical CW complexes require.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.3.
-/

public section

noncomputable section

open Filter Metric OnePoint Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball of a real normed space `E` with its boundary collapsed to `∞`, as a
partial equivalence `E → OnePoint E` with source the open unit ball and target the complement of
`∞`.  A point `x` of norm less than one goes to `univUnitBall.symm x`, and every other point goes
to `∞`. -/
def unitBallToOnePoint : PartialEquiv E (OnePoint E) where
  toFun x := if ‖x‖ < 1 then ↑(OpenPartialHomeomorph.univUnitBall.symm x) else ∞
  invFun y := y.elim 0 OpenPartialHomeomorph.univUnitBall
  source := ball 0 1
  target := {∞}ᶜ
  map_source' x hx := by simp [mem_ball_zero_iff.1 hx]
  map_target' y hy := by
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hy
    | coe y => exact OpenPartialHomeomorph.univUnitBall.map_source (mem_univ y)
  left_inv' x hx := by
    simp only [mem_ball_zero_iff.1 hx, ↓reduceIte, elim_some]
    exact OpenPartialHomeomorph.univUnitBall.right_inv hx
  right_inv' y hy := by
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hy
    | coe y =>
      have hy := OpenPartialHomeomorph.univUnitBall.map_source (mem_univ y)
      simp only [elim_some, mem_ball_zero_iff.1 hy, ↓reduceIte]
      rw [OpenPartialHomeomorph.univUnitBall.left_inv (mem_univ y)]

@[simp]
theorem unitBallToOnePoint_source : (unitBallToOnePoint (E := E)).source = ball 0 1 :=
  (rfl)

@[simp]
theorem unitBallToOnePoint_target : (unitBallToOnePoint (E := E)).target = {∞}ᶜ :=
  (rfl)

@[simp]
theorem unitBallToOnePoint_apply_of_norm_lt {x : E} (hx : ‖x‖ < 1) :
    unitBallToOnePoint x = ↑(OpenPartialHomeomorph.univUnitBall.symm x) :=
  ite_eq_left hx

@[simp]
theorem unitBallToOnePoint_apply_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    unitBallToOnePoint x = ∞ :=
  ite_eq_right hx.not_gt

@[simp]
theorem unitBallToOnePoint_apply_eq_infty_iff {x : E} : unitBallToOnePoint x = ∞ ↔ 1 ≤ ‖x‖ := by
  refine ⟨fun h ↦ not_lt.1 fun hx ↦ ?_, unitBallToOnePoint_apply_of_one_le_norm⟩
  rw [unitBallToOnePoint_apply_of_norm_lt hx] at h
  exact coe_ne_infty _ h

@[simp]
theorem unitBallToOnePoint_symm_apply_coe (y : E) :
    unitBallToOnePoint.symm (y : OnePoint E) = OpenPartialHomeomorph.univUnitBall y :=
  (rfl)

@[simp]
theorem unitBallToOnePoint_symm_apply_infty : unitBallToOnePoint.symm (∞ : OnePoint E) = 0 :=
  (rfl)

/-- The boundary sphere of the unit ball is collapsed to `∞`. -/
theorem mapsTo_unitBallToOnePoint_sphere :
    MapsTo unitBallToOnePoint (sphere (0 : E) 1) {∞} := fun _ hx ↦
  unitBallToOnePoint_apply_of_one_le_norm (mem_sphere_zero_iff_norm.1 hx).ge

/-- The image of the open unit ball is the complement of `∞`. -/
theorem image_unitBallToOnePoint_ball :
    unitBallToOnePoint '' ball (0 : E) 1 = {∞}ᶜ := by
  rw [← unitBallToOnePoint_source, PartialEquiv.image_source_eq_target, unitBallToOnePoint_target]

/-- The image of the closed unit ball is all of `OnePoint E` when `E` is nontrivial: the open
ball covers the complement of `∞` and the boundary sphere goes to `∞`. -/
theorem image_unitBallToOnePoint_closedBall [Nontrivial E] :
    unitBallToOnePoint '' closedBall (0 : E) 1 = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  induction y using OnePoint.rec with
  | infty =>
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
    exact ⟨x, sphere_subset_closedBall hx, mapsTo_unitBallToOnePoint_sphere hx⟩
  | coe y =>
    obtain ⟨x, hx, hxy⟩ := image_unitBallToOnePoint_ball.ge (coe_ne_infty y)
    exact ⟨x, ball_subset_closedBall hx, hxy⟩

/-- The collapse is continuous on the closed unit ball: approaching the boundary sphere from
inside, `univUnitBall.symm` leaves every compact set. -/
theorem continuousOn_unitBallToOnePoint :
    ContinuousOn unitBallToOnePoint (closedBall (0 : E) 1) := by
  intro x hx
  rcases (mem_closedBall_zero_iff.1 hx).lt_or_eq with hx | hx
  · -- Inside the open ball the collapse agrees with `univUnitBall.symm` near `x`.
    refine (ContinuousAt.congr ?_ (eventuallyEq_of_mem (isOpen_ball.mem_nhds
      (mem_ball_zero_iff.2 hx)) fun y hy ↦
        (unitBallToOnePoint_apply_of_norm_lt (mem_ball_zero_iff.1 hy)).symm)).continuousWithinAt
    exact continuous_coe.continuousAt.comp
      (OpenPartialHomeomorph.univUnitBall.symm.continuousAt (mem_ball_zero_iff.2 hx))
  · -- At a boundary point, the preimage of a compact `s ⊆ E` lies in the compact set
    -- `univUnitBall '' s`, which misses the boundary point.
    rw [ContinuousWithinAt, unitBallToOnePoint_apply_of_one_le_norm hx.ge, Tendsto, le_nhds_infty]
    intro s _ hs
    rw [mem_map]
    have hK := hs.image_of_continuousOn
      (OpenPartialHomeomorph.univUnitBall.continuousOn.mono fun y _ ↦ mem_univ y)
    have hxK : x ∉ OpenPartialHomeomorph.univUnitBall '' s := by
      rintro ⟨y, -, rfl⟩
      exact (mem_ball_zero_iff.1 (OpenPartialHomeomorph.univUnitBall.map_source
        (mem_univ y))).ne hx
    filter_upwards [nhdsWithin_le_nhds (hK.isClosed.isOpen_compl.mem_nhds hxK)] with y hy
    by_cases hy1 : ‖y‖ < 1
    · rw [mem_preimage, unitBallToOnePoint_apply_of_norm_lt hy1]
      refine Or.inl ⟨_, fun hs ↦ hy ⟨_, hs, ?_⟩, rfl⟩
      exact OpenPartialHomeomorph.univUnitBall.right_inv (mem_ball_zero_iff.2 hy1)
    · exact Or.inr (unitBallToOnePoint_apply_of_one_le_norm (not_lt.1 hy1))

/-- The inverse of the collapse is continuous away from `∞`. -/
theorem continuousOn_unitBallToOnePoint_symm :
    ContinuousOn unitBallToOnePoint.symm (unitBallToOnePoint (E := E)).target := by
  rintro y hy
  induction y using OnePoint.rec with
  | infty => exact absurd rfl hy
  | coe y =>
    refine (continuousAt_coe.2 ?_).continuousWithinAt
    exact OpenPartialHomeomorph.univUnitBall.continuousAt (mem_univ y)

end TauCeti
