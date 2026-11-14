/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.NextCollision
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Time reversal and the inverse of the billiard map

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let
`B(s, v) = (t, w)` be its next-collision map on the strip `ℝ × (-1, 1)`
(`TauCeti.StrictConvexBilliardTable.nextCollision`): a ball leaving `χ(s)` with unit velocity `u` of
tangential component `v` next hits the boundary at `χ(t)`, `t ∈ (s, s + L)`, and `w = ⟪u, χ'(t)⟫`.

Billiard motion is reversible. Reflecting the tangential component, `ι(s, v) = (s, -v)`, turns the
outgoing velocity of the state `(t, w)` into the reversed incoming velocity `-u`
(`TauCeti.StrictConvexBilliardTable.outgoingDir_nextParam_neg_nextTangential`). Travelling back
along the same chord, the ball returns to `χ(s) = χ(s + L)` with tangential component `-v`:

`B(t, -w) = (s + L, -v)`

(`TauCeti.StrictConvexBilliardTable.nextParam_nextParam_neg_nextTangential`,
`TauCeti.StrictConvexBilliardTable.nextTangential_nextParam_neg_nextTangential`). The parameter
`s + L` rather than `s` appears because the next collision parameter always increases, by less than
one period. So `ι ∘ B ∘ ι ∘ B` is the deck translation `τ(s, v) = (s + L, v)`, and `B` is a
bijection of the strip with inverse `τ⁻¹ ∘ ι ∘ B ∘ ι`
(`TauCeti.StrictConvexBilliardTable.nextCollisionEquiv`).

Both `B` and its inverse commute with `τ`, so they descend to mutually inverse maps of the space of
collision states `AddCircle L × (-1, 1)`. This is the billiard map `β`
(`TauCeti.StrictConvexBilliardTable.billiardMap`), a bijection whose inverse is `ι ∘ β ∘ ι`
(`TauCeti.StrictConvexBilliardTable.billiardMap_symm_coe`).

The continuity and smoothness of `B` and of its inverse are not treated here.

## Main definitions

* `TauCeti.StrictConvexBilliardTable.nextCollisionEquiv`: the next-collision map as a bijection of
  `ℝ × (-1, 1)`.
* `TauCeti.StrictConvexBilliardTable.billiardMap`: the billiard map, a bijection of
  `AddCircle L × (-1, 1)`.

## Main results

* `TauCeti.StrictConvexBilliardTable.outgoingDir_nextParam_neg_nextTangential`: the reversed state
  leaves along `-u`.
* `TauCeti.StrictConvexBilliardTable.nextParam_nextParam_neg_nextTangential`,
  `TauCeti.StrictConvexBilliardTable.nextTangential_nextParam_neg_nextTangential`: time reversal,
  `B(t, -w) = (s + L, -v)`.
* `TauCeti.StrictConvexBilliardTable.nextCollisionEquiv_symm_apply`: the inverse of the
  next-collision map is `τ⁻¹ ∘ ι ∘ B ∘ ι`.
* `TauCeti.StrictConvexBilliardTable.billiardMap_coe`,
  `TauCeti.StrictConvexBilliardTable.billiardMap_symm_coe`: the billiard map is induced by the
  next-collision map, and its inverse is `ι ∘ β ∘ ι`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3 (the billiard ball map and its reversibility).
-/

public section

noncomputable section

open Function Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-! ### Time reversal -/

/-- The state at the next collision point with reversed tangential component leaves along the
reversed incoming velocity `-u`. -/
theorem outgoingDir_nextParam_neg_nextTangential {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.outgoingDir (χ.nextParam s v) (-χ.nextTangential s v) = -χ.outgoingDir s v := by
  rw [outgoingDir_neg, χ.outgoingDir_nextCollision hv, Submodule.reflection_singleton_apply,
    χ.norm_deriv, real_inner_comm, ← nextTangential_def]
  simp only [RCLike.ofReal_real_eq_id, id, one_pow, div_one]
  module

/-- Time reversal of the collision parameter: from the next collision point `χ(t)` with reversed
tangential component `-w`, the ball returns to `χ(s) = χ(s + L)`. -/
theorem nextParam_nextParam_neg_nextTangential {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.nextParam (χ.nextParam s v) (-χ.nextTangential s v) = s + χ.period := by
  have hw := χ.nextTangential_mem_Ioo (s := s) hv
  have ht := χ.nextParam_mem_Ioo (s := s) hv
  refine (χ.eq_nextParam_of_areaForm_eq_zero ⟨by linarith [hw.2], by linarith [hw.1]⟩
    ⟨ht.2, by linarith [ht.1]⟩ ?_).symm
  rw [χ.outgoingDir_nextParam_neg_nextTangential hv, χ.periodic, ← neg_sub, map_neg, map_neg,
    LinearMap.neg_apply, neg_neg]
  exact χ.areaForm_outgoingDir_sub_nextParam hv

/-- Time reversal of the tangential component: the reversed state arrives back at `χ(s)` with
tangential component `-v`. -/
theorem nextTangential_nextParam_neg_nextTangential {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.nextTangential (χ.nextParam s v) (-χ.nextTangential s v) = -v := by
  rw [nextTangential_def, χ.nextParam_nextParam_neg_nextTangential hv,
    χ.outgoingDir_nextParam_neg_nextTangential hv, χ.deriv_add_period, inner_neg_left,
    real_inner_comm, inner_deriv_outgoingDir]

/-! ### The next-collision map as a bijection of the strip -/

/-- The tangential component `-w` of the next collision of `(s, -v)` lies in `(-1, 1)`: it is the
tangential component of the state that the inverse of the next-collision map assigns to `(s, v)`. -/
theorem neg_nextTangential_neg_mem_Ioo (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    -χ.nextTangential s (-v) ∈ Ioo (-1 : ℝ) 1 := by
  have hw := χ.nextTangential_mem_Ioo (s := s) (v := -v) ⟨by linarith [v.2.2], by linarith [v.2.1]⟩
  exact ⟨by linarith [hw.2], by linarith [hw.1]⟩

/-- The next-collision map `(s, v) ↦ (t, w)` as a bijection of the strip `ℝ × (-1, 1)`. Its inverse
reverses time: it sends `(t, w)` to `(s - L, -v)`, where `(s, v)` is the next collision of
`(t, -w)`. -/
def nextCollisionEquiv : ℝ × Ioo (-1 : ℝ) 1 ≃ ℝ × Ioo (-1 : ℝ) 1 where
  toFun x := (χ.nextParam x.1 x.2, ⟨χ.nextTangential x.1 x.2, χ.nextTangential_mem_Ioo x.2.2⟩)
  invFun x := (χ.nextParam x.1 (-x.2) - χ.period,
    ⟨-χ.nextTangential x.1 (-x.2), χ.neg_nextTangential_neg_mem_Ioo x.1 x.2⟩)
  left_inv x := by
    ext
    · simp [χ.nextParam_nextParam_neg_nextTangential x.2.2]
    · simp [χ.nextTangential_nextParam_neg_nextTangential x.2.2]
  right_inv x := by
    have hv : -(x.2 : ℝ) ∈ Ioo (-1) 1 := ⟨by linarith [x.2.2.2], by linarith [x.2.2.1]⟩
    have hw := χ.neg_nextTangential_neg_mem_Ioo x.1 x.2
    -- The inverse moves the parameter back by one period; undo this by the deck translation.
    have hp := χ.nextParam_add_period (s := χ.nextParam x.1 (-x.2) - χ.period) hw
    have ht := χ.nextTangential_add_period (s := χ.nextParam x.1 (-x.2) - χ.period) hw
    rw [sub_add_cancel] at hp ht
    ext
    · simp only
      linarith [χ.nextParam_nextParam_neg_nextTangential (s := x.1) hv]
    · simp [← ht, χ.nextTangential_nextParam_neg_nextTangential hv]

/-- The bijection `nextCollisionEquiv` acts on the strip as the next-collision map. -/
@[simp]
theorem nextCollisionEquiv_apply (x : ℝ × Ioo (-1 : ℝ) 1) :
    χ.nextCollisionEquiv x =
      (χ.nextParam x.1 x.2, ⟨χ.nextTangential x.1 x.2, χ.nextTangential_mem_Ioo x.2.2⟩) := by
  rfl

/-- The inverse of the next-collision map `B` is `τ⁻¹ ∘ ι ∘ B ∘ ι`, where `ι(s, v) = (s, -v)` and
`τ(s, v) = (s + L, v)`. -/
@[simp]
theorem nextCollisionEquiv_symm_apply (x : ℝ × Ioo (-1 : ℝ) 1) :
    χ.nextCollisionEquiv.symm x = (χ.nextParam x.1 (-x.2) - χ.period,
      ⟨-χ.nextTangential x.1 (-x.2), χ.neg_nextTangential_neg_mem_Ioo x.1 x.2⟩) := by
  rfl

/-! ### The billiard map on the space of collision states -/

/-- The class in `AddCircle L × (-1, 1)` of the next collision of `(s, v)` depends only on the class
of `s`, since the next-collision map commutes with the deck translation. -/
theorem periodic_nextCollisionEquiv (v : Ioo (-1 : ℝ) 1) :
    Periodic (fun s : ℝ ↦
      Prod.map ((↑) : ℝ → AddCircle χ.period) id (χ.nextCollisionEquiv (s, v))) χ.period := by
  intro s
  simp [χ.nextParam_add_period v.2, χ.nextTangential_add_period v.2]

/-- The class in `AddCircle L × (-1, 1)` of the image of `(s, v)` under the inverse of the
next-collision map depends only on the class of `s`. -/
theorem periodic_nextCollisionEquiv_symm (v : Ioo (-1 : ℝ) 1) :
    Periodic (fun s : ℝ ↦
      Prod.map ((↑) : ℝ → AddCircle χ.period) id (χ.nextCollisionEquiv.symm (s, v))) χ.period := by
  intro s
  have hv : -(v : ℝ) ∈ Ioo (-1) 1 := ⟨by linarith [v.2.2], by linarith [v.2.1]⟩
  ext
  · simp only [nextCollisionEquiv_symm_apply, Prod.map_fst]
    rw [χ.nextParam_add_period hv, add_sub_cancel_right, ← AddCircle.coe_add_period (χ.period)
      (χ.nextParam s (-v) - χ.period), sub_add_cancel]
  · simp [χ.nextTangential_add_period hv]

/-- The billiard map `β` of the table on the space of collision states `AddCircle L × (-1, 1)`,
induced by the next-collision map on the strip `ℝ × (-1, 1)`
(`TauCeti.StrictConvexBilliardTable.billiardMap_coe`). It is a bijection, whose inverse is
induced by the inverse of the next-collision map. -/
def billiardMap : AddCircle χ.period × Ioo (-1 : ℝ) 1 ≃ AddCircle χ.period × Ioo (-1 : ℝ) 1 where
  toFun x := (χ.periodic_nextCollisionEquiv x.2).lift x.1
  invFun x := (χ.periodic_nextCollisionEquiv_symm x.2).lift x.1
  left_inv := by
    rintro ⟨θ, v⟩
    induction θ using QuotientAddGroup.induction_on with | H s => ?_
    simp only [Periodic.lift_coe, Prod.map_fst, Prod.map_snd, id]
    exact congrArg (Prod.map ((↑) : ℝ → AddCircle χ.period) id)
      (χ.nextCollisionEquiv.symm_apply_apply (s, v))
  right_inv := by
    rintro ⟨θ, v⟩
    induction θ using QuotientAddGroup.induction_on with | H s => ?_
    simp only [Periodic.lift_coe, Prod.map_fst, Prod.map_snd, id]
    exact congrArg (Prod.map ((↑) : ℝ → AddCircle χ.period) id)
      (χ.nextCollisionEquiv.apply_symm_apply (s, v))

/-- The billiard map sends the class of a state `(s, v)` of the strip to the class of its next
collision. -/
@[simp]
theorem billiardMap_coe (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    χ.billiardMap ((s : AddCircle χ.period), v) =
      ((χ.nextParam s v : AddCircle χ.period),
        ⟨χ.nextTangential s v, χ.nextTangential_mem_Ioo v.2⟩) := by
  simp [billiardMap]

/-- The inverse of the billiard map is `ι ∘ β ∘ ι`, where `ι([s], v) = ([s], -v)` reverses the
tangential component. -/
@[simp]
theorem billiardMap_symm_coe (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    χ.billiardMap.symm ((s : AddCircle χ.period), v) =
      ((χ.nextParam s (-v) : AddCircle χ.period),
        ⟨-χ.nextTangential s (-v), χ.neg_nextTangential_neg_mem_Ioo s v⟩) := by
  simp only [billiardMap, Equiv.coe_fn_symm_mk, Periodic.lift_coe, nextCollisionEquiv_symm_apply,
    Prod.map_apply, id]
  rw [← AddCircle.coe_add_period, sub_add_cancel]

end StrictConvexBilliardTable

end TauCeti
