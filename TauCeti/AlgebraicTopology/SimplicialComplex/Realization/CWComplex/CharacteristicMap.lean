/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball

/-!
# Characteristic maps of simplicial cells

An enumeration of the vertices of a face identifies its closed simplex with the closed unit
ball of `Fin n → ℝ`, with the sup norm used by Mathlib's classical CW complexes. The sphere
maps exactly onto the proper faces, and the open ball maps exactly onto the points whose
barycentric support is the whole face. These are the characteristic maps for the cell
structure on a weak geometric realization, including zero-dimensional cells.

The enumeration is an explicit argument: an ordered enumeration can therefore fix the
orientation used in cellular boundary formulas. The ambient complex may be infinite.
The maps compose `realizationTopHomeomorphPiClosedBall` with the face relabeling
`realizationTopHomeomorphFace`. Outside the closed ball the characteristic map takes the
value at the origin.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2 (simplices and polyhedra); A. Hatcher, *Algebraic Topology*, Chapter 0
(the cell structure of a simplicial complex).
-/

public section

noncomputable section

open Set Metric

namespace AbstractSimplicialComplex

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι) {n : ℕ}
  (f : Fin (n + 1) ↪ ι) (hf : Finset.univ.image f ∈ K)

private def simplexCharacteristicFun (x : Fin n → ℝ) : Realization K :=
  if hx : x ∈ closedBall 0 1 then (simplexClosedBallHomeomorph K f hf ⟨x, hx⟩).1
  else (simplexClosedBallHomeomorph K f hf ⟨0, by simp⟩).1

private theorem simplexCharacteristicFun_apply {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    simplexCharacteristicFun K f hf x = (simplexClosedBallHomeomorph K f hf ⟨x, hx⟩).1 :=
  dite_eq_left hx

private theorem simplexCharacteristicFun_apply_symm
    (y : {x : Realization K // x.1.support ⊆ Finset.univ.image f}) :
    simplexCharacteristicFun K f hf ((simplexClosedBallHomeomorph K f hf).symm y).1 = y.1 := by
  rw [simplexCharacteristicFun_apply K f hf ((simplexClosedBallHomeomorph K f hf).symm y).2,
    Subtype.coe_eta, Homeomorph.apply_symm_apply]

private theorem injOn_simplexCharacteristicFun_closedBall :
    InjOn (simplexCharacteristicFun K f hf) (closedBall 0 1) := by
  intro x hx y hy hxy
  rw [simplexCharacteristicFun_apply K f hf hx,
    simplexCharacteristicFun_apply K f hf hy] at hxy
  exact congrArg Subtype.val ((simplexClosedBallHomeomorph K f hf).injective (Subtype.ext hxy))

private theorem bijOn_simplexCharacteristicFun :
    BijOn (simplexCharacteristicFun K f hf) (ball 0 1)
      {x : Realization K | x.1.support = Finset.univ.image f} := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_ofPred_eq, simplexCharacteristicFun_apply K f hf (ball_subset_closedBall hx)]
    exact (simplexClosedBallHomeomorph_support_eq_iff K f hf _).mpr
      (mem_ball_zero_iff.mp hx)
  · exact (injOn_simplexCharacteristicFun_closedBall K f hf).mono ball_subset_closedBall
  · intro y hy
    exact ⟨_, mem_ball_zero_iff.mpr
      ((norm_simplexClosedBallHomeomorph_symm_lt_one_iff K f hf ⟨y, hy.le⟩).mpr hy),
      simplexCharacteristicFun_apply_symm K f hf ⟨y, hy.le⟩⟩

/-- The characteristic map of an enumerated simplicial cell. Its source is the sup-norm
open unit ball, and its target consists of the points whose support equals the face.
It is continuous on the closed ball and parametrizes all proper faces on the sphere. -/
def simplexCharacteristicMap : PartialEquiv (Fin n → ℝ) (Realization K) :=
  (bijOn_simplexCharacteristicFun K f hf).toPartialEquiv
    (simplexCharacteristicFun K f hf) (ball 0 1)
    {x : Realization K | x.1.support = Finset.univ.image f}

/-- The source of a simplicial characteristic map is the open unit ball. -/
@[simp]
theorem simplexCharacteristicMap_source :
    (simplexCharacteristicMap K f hf).source = ball 0 1 := (rfl)

/-- The open cell consists exactly of points with the enumerated face as their support. -/
@[simp]
theorem simplexCharacteristicMap_target :
    (simplexCharacteristicMap K f hf).target =
      {x : Realization K | x.1.support = Finset.univ.image f} := (rfl)

/-- On the closed ball the characteristic map agrees with the closed-simplex homeomorphism. -/
theorem simplexCharacteristicMap_apply {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    simplexCharacteristicMap K f hf x = (simplexClosedBallHomeomorph K f hf ⟨x, hx⟩).1 :=
  simplexCharacteristicFun_apply K f hf hx

/-- The characteristic map is injective on the closed ball. -/
theorem injOn_simplexCharacteristicMap_closedBall :
    InjOn (simplexCharacteristicMap K f hf) (closedBall 0 1) :=
  injOn_simplexCharacteristicFun_closedBall K f hf

/-- The characteristic map sends the inverse closed-simplex homeomorphism of a point back to
that point. -/
@[simp]
theorem simplexCharacteristicMap_apply_symm
    (y : {x : Realization K // x.1.support ⊆ Finset.univ.image f}) :
    simplexCharacteristicMap K f hf ((simplexClosedBallHomeomorph K f hf).symm y).1 = y.1 :=
  simplexCharacteristicFun_apply_symm K f hf y

/-- Outside the closed ball the characteristic map takes its value at the origin. -/
theorem simplexCharacteristicMap_apply_of_notMem_closedBall {x : Fin n → ℝ}
    (hx : x ∉ closedBall 0 1) :
    simplexCharacteristicMap K f hf x =
      (simplexClosedBallHomeomorph K f hf ⟨0, by simp⟩).1 :=
  dite_eq_right hx

/-- On the open cell, the inverse characteristic map is the inverse closed-simplex
homeomorphism followed by the inclusion into the ambient coordinate space. -/
theorem simplexCharacteristicMap_symm_apply {y : Realization K}
    (hy : y.1.support = Finset.univ.image f) :
    (simplexCharacteristicMap K f hf).symm y =
      ((simplexClosedBallHomeomorph K f hf).symm ⟨y, hy.le⟩).1 :=
  (((simplexCharacteristicMap K f hf).eq_symm_apply
    (mem_ball_zero_iff.mpr
      ((norm_simplexClosedBallHomeomorph_symm_lt_one_iff K f hf ⟨y, hy.le⟩).mpr hy)) hy).mpr
    (simplexCharacteristicMap_apply_symm K f hf ⟨y, hy.le⟩)).symm

/-- The characteristic map is continuous on its closed cell domain. -/
theorem continuousOn_simplexCharacteristicMap :
    ContinuousOn (simplexCharacteristicMap K f hf) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp (simplexClosedBallHomeomorph K f hf).continuous).congr
    (fun x => (simplexCharacteristicMap_apply K f hf x.2).symm)

/-- The inverse of a simplicial characteristic map is continuous on the open cell. -/
theorem continuousOn_simplexCharacteristicMap_symm :
    ContinuousOn (simplexCharacteristicMap K f hf).symm
      (simplexCharacteristicMap K f hf).target := by
  rw [simplexCharacteristicMap_target, continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun y : {y : Realization K |
      y.1.support = Finset.univ.image f} =>
      ((simplexClosedBallHomeomorph K f hf).symm ⟨y.1, y.2.le⟩).1) :=
    continuous_subtype_val.comp ((simplexClosedBallHomeomorph K f hf).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun y => y.2.le)))
  exact hc.congr (fun y => (simplexCharacteristicMap_symm_apply K f hf y.2).symm)

/-- The closed ball maps onto the whole closed simplex. -/
@[simp]
theorem image_simplexCharacteristicMap_closedBall :
    simplexCharacteristicMap K f hf '' closedBall 0 1 =
      {x : Realization K | x.1.support ⊆ Finset.univ.image f} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [simplexCharacteristicMap_apply K f hf hx]
    exact (simplexClosedBallHomeomorph K f hf ⟨x, hx⟩).2
  · intro hy
    exact ⟨_, ((simplexClosedBallHomeomorph K f hf).symm ⟨y, hy⟩).2,
      simplexCharacteristicMap_apply_symm K f hf ⟨y, hy⟩⟩

/-- The sphere maps onto exactly the proper faces of the closed simplex. -/
@[simp]
theorem image_simplexCharacteristicMap_sphere :
    simplexCharacteristicMap K f hf '' sphere 0 1 =
      {x : Realization K | x.1.support ⊂ Finset.univ.image f} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxc := sphere_subset_closedBall hx
    rw [simplexCharacteristicMap_apply K f hf hxc]
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨(simplexClosedBallHomeomorph K f hf ⟨x, hxc⟩).2,
        (simplexClosedBallHomeomorph_support_ne_iff K f hf _).mpr
          (mem_sphere_zero_iff_norm.mp hx)⟩
  · intro hy
    exact ⟨_, mem_sphere_zero_iff_norm.mpr
      ((norm_simplexClosedBallHomeomorph_symm_eq_one_iff K f hf ⟨y, hy.subset⟩).mpr hy),
      simplexCharacteristicMap_apply_symm K f hf ⟨y, hy.subset⟩⟩

end AbstractSimplicialComplex
