/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import TauCeti.Topology.Cone
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Cone coordinates for geometric vertex stars

The barycentric coordinates of a closed vertex star become coordinates on the cone over its
geometric link after deleting the apex coordinate.  This affine map and its basic properties are
shared by the piecewise-linear radial maps into stars and the radial ball models.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]
  {K : AbstractSimplicialComplex ι} {v : ι}

/-- Read a star as a cone by deleting its apex coordinate and recording the remaining mass. -/
def starToCone (v : ι) : (ι → ℝ) →ᴬ[ℝ] ((ι → ℝ) × ℝ) :=
  ((ContinuousLinearMap.id ℝ (ι → ℝ) -
      (ContinuousLinearMap.proj v).smulRight (Pi.single v 1)).toContinuousAffineMap).prod
    (ContinuousAffineMap.const ℝ (ι → ℝ) 1 -
      (ContinuousLinearMap.proj v).toContinuousAffineMap)

/-- The coordinate formula for `starToCone`. -/
@[simp]
theorem starToCone_apply (v : ι) (x : ι → ℝ) :
    starToCone v x = (x - x v • Pi.single v 1, 1 - x v) := (rfl)

/-- Away from the apex, `starToCone` is the link coordinate scaled by the cone height. -/
theorem starToCone_of_lt (x : closedStarRealization K {v}) (hx : x.1.1 v < 1) :
    starToCone v (x.1.1 : ι → ℝ) =
      ((1 - x.1.1 v) •
        ((starLinkProjection K v
          ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩).1.1 : ι → ℝ),
        1 - x.1.1 v) := by
  rw [starToCone_apply]
  congr 1
  ext j
  by_cases hj : j = v
  · simp [hj]
  · simp [starLinkProjection_apply, hj,
      ← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hx).ne']

/-- At the apex, `starToCone` is the cone apex. -/
theorem starToCone_of_not_lt (x : closedStarRealization K {v})
    (hx : ¬x.1.1 v < 1) : starToCone v (x.1.1 : ι → ℝ) = 0 := by
  have hv : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
  have he : x.1 = vertex K v := (Realization.eq_vertex_iff K x.1 v).mpr hv
  rw [starToCone_apply, he]
  ext j <;> simp [vertex_val, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The image of a closed star under `starToCone` lies in the cone over its link. -/
theorem starToCone_mem (x : closedStarRealization K {v}) :
    starToCone v (x.1.1 : ι → ℝ) ∈
      (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))).cone := by
  by_cases hx : x.1.1 v < 1
  · rw [starToCone_of_lt x hx]
    exact (smul_mem_cone_iff _ (sub_pos.mpr hx)).mpr (mem_range_self _)
  · rw [starToCone_of_not_lt x hx]
    exact zero_mem_cone _

end AbstractSimplicialComplex
