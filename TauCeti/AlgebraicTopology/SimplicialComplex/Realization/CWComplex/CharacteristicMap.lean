/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Characteristic maps of simplicial cells

An enumeration of the vertices of a face identifies its closed simplex with the closed unit
ball of `Fin n → ℝ`, with the sup norm used by Mathlib's classical CW complexes. The sphere
maps exactly onto the proper faces, and the open ball maps exactly onto the points whose
barycentric support is the whole face. These are the characteristic maps for the cell
structure on a weak geometric realization, including zero-dimensional cells.

The enumeration is an explicit argument: an ordered enumeration can therefore fix the
orientation used in cellular boundary formulas. The ambient complex may be infinite.
The maps use `realizationTopHomeomorphClosedBall`, injective relabeling of polyhedra, and
`ContinuousLinearEquiv.unitBallHomeomorph` to match the two ball norms. Outside the closed
ball the characteristic map takes the value at the origin.

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

private def enumeratedSimplexHomeomorph :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃ₜ
      {x : Realization K // x.1.support ⊆ Finset.univ.image f} := by
  let P := PreAbstractSimplicialComplex.simplex (Finset.univ : Finset (Fin (n + 1)))
  have hP : P = (⊤ : AbstractSimplicialComplex (Fin (n + 1))).toPreAbstractSimplicialComplex := by
    simp [P, PreAbstractSimplicialComplex.simplex_univ,
      AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
  have hL : P.map f ≤ K.toPreAbstractSimplicialComplex := by
    rw [PreAbstractSimplicialComplex.map_simplex]
    exact PreAbstractSimplicialComplex.simplex_le_iff.mpr (fun _ => hf)
  let r := P.relabelingHomeomorph f hP.le hL
  have hs : {x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) |
      x.1.support ∈ P} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    rw [hP]
    exact support_mem _ x
  have ht : {x : Realization K | x.1.support ∈ P.map f} =
      {x : Realization K | x.1.support ⊆ Finset.univ.image f} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [PreAbstractSimplicialComplex.map_simplex, PreAbstractSimplicialComplex.mem_simplex]
    exact and_iff_right (K.isRelLowerSet_faces.prop_of_mem (support_mem K x))
  exact (Homeomorph.Set.univ _).symm.trans
    ((Homeomorph.setCongr hs.symm).trans (r.trans (Homeomorph.setCongr ht)))

private theorem enumeratedSimplexHomeomorph_val
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    (enumeratedSimplexHomeomorph K f hf x).1.1 = Finsupp.mapDomain f x.1 := by
  -- The set-congruence transports preserve the underlying point.
  dsimp only [enumeratedSimplexHomeomorph, Homeomorph.trans_apply,
    Homeomorph.setCongr, Homeomorph.Set.univ, Equiv.Set.univ]
  exact PreAbstractSimplicialComplex.relabelingHomeomorph_val _ _ _ _ _

private def simplexBallModel (n : ℕ) :
    closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) :=
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  ((L.unitBallHomeomorph.image _).trans
    (Homeomorph.setCongr L.image_unitBallHomeomorph_closedBall)).trans
    (realizationTopHomeomorphClosedBall n).symm

private theorem simplexBallModel_support_ne_univ_iff
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexBallModel n x).1.support ≠ Finset.univ ↔ ‖x.1‖ = 1 := by
  rw [← realizationTopHomeomorphClosedBall_norm_eq_one_iff]
  simp only [simplexBallModel, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  exact ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff _

/-- The sup-norm closed unit ball parametrizes the closed simplex on an explicitly
enumerated face. Its boundary corresponds to the proper faces. -/
def simplexClosedBallHomeomorph :
    closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      {x : Realization K // x.1.support ⊆ Finset.univ.image f} :=
  (simplexBallModel n).trans (enumeratedSimplexHomeomorph K f hf)

/-- Barycentric coordinates are obtained from the fixed standard ball model by pushing
its coordinate vector along the vertex enumeration. -/
theorem simplexClosedBallHomeomorph_val (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexClosedBallHomeomorph K f hf x).1.1 =
      let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
      Finsupp.mapDomain f
        (((realizationTopHomeomorphClosedBall n).symm
          ⟨L.unitBallHomeomorph x.1, by
            simpa only [mem_closedBall_zero_iff,
              ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff] using x.2⟩).1) := by
  rw [simplexClosedBallHomeomorph, Homeomorph.trans_apply, enumeratedSimplexHomeomorph_val]
  -- The ball-model transports change only membership proofs.
  rfl

/-- The boundary sphere corresponds exactly to barycentric support smaller than the face. -/
theorem simplexClosedBallHomeomorph_support_ne_iff
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexClosedBallHomeomorph K f hf x).1.1.support ≠ Finset.univ.image f ↔ ‖x.1‖ = 1 := by
  rw [simplexClosedBallHomeomorph, Homeomorph.trans_apply, enumeratedSimplexHomeomorph_val,
    Finsupp.mapDomain_support_of_injective f.injective]
  rw [ne_eq, Finset.image_inj f.injective, ← ne_eq]
  exact simplexBallModel_support_ne_univ_iff x

/-- The open ball corresponds exactly to the points with full barycentric support. -/
@[simp]
theorem simplexClosedBallHomeomorph_support_eq_iff
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexClosedBallHomeomorph K f hf x).1.1.support = Finset.univ.image f ↔ ‖x.1‖ < 1 := by
  have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  have h := simplexClosedBallHomeomorph_support_ne_iff K f hf x
  grind

private def simplexCharacteristicFun (x : Fin n → ℝ) : Realization K :=
  if hx : x ∈ closedBall 0 1 then (simplexClosedBallHomeomorph K f hf ⟨x, hx⟩).1
  else (simplexClosedBallHomeomorph K f hf ⟨0, by simp⟩).1

private theorem simplexCharacteristicFun_apply {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    simplexCharacteristicFun K f hf x = (simplexClosedBallHomeomorph K f hf ⟨x, hx⟩).1 :=
  dite_eq_left hx

private theorem bijOn_simplexCharacteristicFun :
    BijOn (simplexCharacteristicFun K f hf) (ball 0 1)
      {x : Realization K | x.1.support = Finset.univ.image f} := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_ofPred_eq, simplexCharacteristicFun_apply K f hf (ball_subset_closedBall hx)]
    exact (simplexClosedBallHomeomorph_support_eq_iff K f hf _).mpr
      (mem_ball_zero_iff.mp hx)
  · intro x hx y hy hxy
    rw [simplexCharacteristicFun_apply K f hf (ball_subset_closedBall hx),
      simplexCharacteristicFun_apply K f hf (ball_subset_closedBall hy)] at hxy
    exact congrArg Subtype.val ((simplexClosedBallHomeomorph K f hf).injective
      (Subtype.ext hxy))
  · intro y hy
    let z := (simplexClosedBallHomeomorph K f hf).symm ⟨y, hy.le⟩
    have hz : z.1 ∈ ball 0 1 := by
      rw [mem_ball_zero_iff]
      apply (simplexClosedBallHomeomorph_support_eq_iff K f hf z).mp
      simpa [z] using hy
    exact ⟨z.1, hz, by simp [simplexCharacteristicFun_apply K f hf z.2, z]⟩

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

/-- Outside the closed ball the characteristic map takes its value at the origin. -/
theorem simplexCharacteristicMap_apply_of_not_mem_closedBall {x : Fin n → ℝ}
    (hx : x ∉ closedBall 0 1) :
    simplexCharacteristicMap K f hf x =
      (simplexClosedBallHomeomorph K f hf ⟨0, by simp⟩).1 :=
  dite_eq_right hx

/-- On the open cell, the inverse characteristic map is the inverse closed-simplex
homeomorphism followed by the inclusion into the ambient coordinate space. -/
theorem simplexCharacteristicMap_symm_apply {y : Realization K}
    (hy : y.1.support = Finset.univ.image f) :
    (simplexCharacteristicMap K f hf).symm y =
      ((simplexClosedBallHomeomorph K f hf).symm ⟨y, hy.le⟩).1 := by
  let z := (simplexClosedBallHomeomorph K f hf).symm ⟨y, hy.le⟩
  have hz : z.1 ∈ (simplexCharacteristicMap K f hf).source := by
    rw [simplexCharacteristicMap_source, mem_ball_zero_iff]
    apply (simplexClosedBallHomeomorph_support_eq_iff K f hf z).mp
    simpa [z] using hy
  have he : simplexCharacteristicMap K f hf z.1 = y := by
    simp [simplexCharacteristicMap_apply K f hf z.2, z]
  exact (congrArg (simplexCharacteristicMap K f hf).symm he).symm.trans
    ((simplexCharacteristicMap K f hf).left_inv hz)

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
    let z := (simplexClosedBallHomeomorph K f hf).symm ⟨y, hy⟩
    exact ⟨z.1, z.2, by simp [simplexCharacteristicMap_apply K f hf z.2, z]⟩

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
    let z := (simplexClosedBallHomeomorph K f hf).symm ⟨y, hy.subset⟩
    have hz : z.1 ∈ sphere 0 1 := by
      rw [mem_sphere_zero_iff_norm]
      apply (simplexClosedBallHomeomorph_support_ne_iff K f hf z).mp
      simpa [z] using hy.ne
    exact ⟨z.1, hz, by simp [simplexCharacteristicMap_apply K f hf z.2, z]⟩

end AbstractSimplicialComplex
