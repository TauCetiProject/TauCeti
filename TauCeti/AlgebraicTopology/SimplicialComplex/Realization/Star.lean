/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Radial coordinates on a vertex star

The closed star of a vertex is a cone on its link. Removing the apex gives a product of
that link with `[0, 1)`: the interval coordinate is the barycentric coordinate at the apex,
and the link coordinate is obtained by deleting that coordinate and normalizing the rest.
These coordinates are the radial part of the local models of triangulated manifolds.

The equivalence works for arbitrary vertex types. It is a homeomorphism whenever the weak
realization topology agrees with the coordinate topology, in particular for finite vertex types.
The geometric star and link are subsets of the original realization, so no extra vertices are
introduced into either local model.
An isolated vertex has empty link and empty punctured star, as the product formula requires.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2, “Pseudo-Radial Projection”, pp. 20–21 (the star is the cone on the link).
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι) (v : ι)

/-- The polyhedron of the closed star of `v`, inside the realization of `K`. -/
def geometricClosedStar : Set (Realization K) :=
  {x | x.1.support ∪ {v} ∈ K}

/-- The polyhedron of the link of `v`, inside the realization of `K`. -/
def geometricLink : Set (Realization K) :=
  {x | x.1 v = 0 ∧ x ∈ geometricClosedStar K v}

/-- Geometric closed-star membership is determined by adjoining the apex to the support. -/
@[simp]
theorem mem_geometricClosedStar (x : Realization K) :
    x ∈ geometricClosedStar K v ↔ x.1.support ∪ {v} ∈ K := (Iff.rfl)

/-- Geometric link membership is closed-star membership with zero apex coordinate. -/
@[simp]
theorem mem_geometricLink (x : Realization K) :
    x ∈ geometricLink K v ↔ x.1 v = 0 ∧ x ∈ geometricClosedStar K v := (Iff.rfl)

/-- The apex coordinate of a geometric link point is zero. -/
@[simp]
theorem geometricLink_apex (x : geometricLink K v) : x.1.1 v = 0 :=
  ((mem_geometricLink K v x.1).mp x.2).1

/-- Geometric closed-star membership is equivalent to the carrier being a closed-star face. -/
theorem mem_geometricClosedStar_iff (x : Realization K) :
    x ∈ geometricClosedStar K v ↔
      x.1.support ∈
      PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v} := by
  simp [geometricClosedStar, PreAbstractSimplicialComplex.mem_closedStar, support_mem]

/-- A point lies in the geometric link exactly when its carrier is a link face. -/
theorem mem_geometricLink_iff (x : Realization K) :
    x ∈ geometricLink K v ↔
      x.1.support ∈ PreAbstractSimplicialComplex.link K.toPreAbstractSimplicialComplex {v} := by
  simp [geometricLink, geometricClosedStar, PreAbstractSimplicialComplex.mem_link,
    support_mem, Finset.disjoint_singleton_right]

/-- The punctured geometric closed star, expressed by the apex coordinate being less than one. -/
def puncturedClosedStar : Set (Realization K) :=
  {x | x ∈ geometricClosedStar K v ∧ x.1 v < 1}

/-- Membership in the punctured closed star. -/
@[simp]
theorem mem_puncturedClosedStar (x : Realization K) :
    x ∈ puncturedClosedStar K v ↔ x ∈ geometricClosedStar K v ∧ x.1 v < 1 := (Iff.rfl)

private def normalizedLinkSimplex (x : puncturedClosedStar K v) : Convexity.StdSimplex ℝ ι := by
  let w : Convexity.StdSimplex ℝ ι :=
    ⟨x.1.1, Realization.nonneg K x.1, Realization.sum_eq_one K x.1⟩
  apply w.restrict {v}ᶜ
  by_contra h
  have hx : x.1.1 = Finsupp.single v (x.1.1 v) := by
    apply Finsupp.eq_single_iff.mpr
    refine ⟨?_, rfl⟩
    intro u hu
    by_contra huv
    exact h ⟨u, by simpa using huv, Finsupp.mem_support_iff.mp hu⟩
  have hsum := Realization.sum_eq_one K x.1
  rw [hx, Finsupp.sum_single_index (by simp)] at hsum
  exact (ne_of_lt x.2.2) hsum

private theorem normalizedLinkCoordinates_apply (x : puncturedClosedStar K v) (u : ι) :
    (normalizedLinkSimplex K v x).weights u =
      if u = v then 0 else (1 - x.1.1 v)⁻¹ * x.1.1 u := by
  have hfilter : x.1.1.filter (· ∈ ({v}ᶜ : Set ι)) = x.1.1.erase v := by
    ext u
    simp [Finsupp.filter_apply, Finsupp.erase_apply]
  have hsum := Finsupp.add_sum_erase' x.1.1 v (fun _ r => r) (fun _ => rfl)
  rw [Realization.sum_eq_one] at hsum
  have he : (x.1.1.erase v).sum (fun _ r => r) = 1 - x.1.1 v := by linarith
  simp only [normalizedLinkSimplex, Convexity.StdSimplex.weights_restrict]
  rw [hfilter, he]
  simp [Finsupp.erase_apply]

private theorem normalizedLinkCoordinates_support (x : puncturedClosedStar K v) :
    (normalizedLinkSimplex K v x).weights.support = x.1.1.support.erase v := by
  simp only [normalizedLinkSimplex, Convexity.StdSimplex.support_weights_restrict]
  ext u
  simp [and_comm]

private theorem normalizedLinkCoordinates_mem (x : puncturedClosedStar K v) :
    (normalizedLinkSimplex K v x).weights ∈ (standardGeometricComplex K).space := by
  classical
  have hne : (x.1.1.support.erase v).Nonempty := by
    rw [← normalizedLinkCoordinates_support K v x, Finsupp.support_nonempty_iff]
    intro hzero
    have hsum := (normalizedLinkSimplex K v x).total
    simp [hzero] at hsum
  have hface : x.1.1.support.erase v ∈ K :=
    K.isRelLowerSet_faces.mem_of_le (support_mem K x.1) (Finset.erase_subset _ _) hne
  apply mem_realization_iff.mpr
  refine ⟨_, hface, ?_⟩
  simp only [Finset.coe_image]
  rw [mem_standardSimplex_iff]
  exact ⟨(normalizedLinkSimplex K v x).nonneg, (normalizedLinkSimplex K v x).total,
    (normalizedLinkCoordinates_support K v x).le⟩

/-- Radial projection from a punctured vertex star onto its geometric link. -/
def starLinkProjection (x : puncturedClosedStar K v) : geometricLink K v :=
  ⟨⟨(normalizedLinkSimplex K v x).weights, normalizedLinkCoordinates_mem K v x⟩, by
    refine ⟨?_, ?_⟩
    · simp [normalizedLinkCoordinates_apply]
    · have hsub : (x.1.1.support.erase v) ∪ {v} ⊆ x.1.1.support ∪ {v} :=
        Finset.union_subset_union (Finset.erase_subset _ _) Finset.Subset.rfl
      simp only [geometricClosedStar, mem_ofPred_eq]
      rw [normalizedLinkCoordinates_support]
      exact K.isRelLowerSet_faces.mem_of_le x.2.1 hsub
        ((Finset.singleton_nonempty v).mono Finset.subset_union_right)⟩

/-- Barycentric coordinates of radial projection onto the link. -/
@[simp]
theorem starLinkProjection_apply (x : puncturedClosedStar K v) (w : ι) :
    (starLinkProjection K v x).1.1 w =
      if w = v then 0 else (1 - x.1.1 v)⁻¹ * x.1.1 w :=
  normalizedLinkCoordinates_apply K v x w

/-- Move from a link point towards the apex, with apex coordinate `t < 1`. -/
def starRay (y : geometricLink K v) (t : Ico (0 : ℝ) 1) : puncturedClosedStar K v := by
  classical
  let z : ι →₀ ℝ := (1 - t.1) • y.1.1 + Finsupp.single v t.1
  have hzv : z v = t.1 := by simp [z, y.2.1]
  have hsupport : z.support ⊆ y.1.1.support ∪ {v} := by
    apply Finsupp.support_add.trans
    exact Finset.union_subset_union Finsupp.support_smul (Finsupp.support_single_subset)
  have hzmem : z ∈ (standardGeometricComplex K).space := by
    apply mem_realization_iff.mpr
    refine ⟨y.1.1.support ∪ {v}, y.2.2, ?_⟩
    simp only [Finset.coe_image]
    rw [mem_standardSimplex_iff]
    refine ⟨?_, ?_, hsupport⟩
    · intro w
      have hs : 0 ≤ (Finsupp.single v t.1) w := by
        by_cases h : v = w <;> simp [h, t.2.1]
      exact add_nonneg (mul_nonneg (sub_pos.mpr t.2.2).le (Realization.nonneg K y.1 w)) hs
    · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index (by simp)]
      rw [Finsupp.sum_smul_index' (by simp)]
      simp only [smul_eq_mul]
      rw [← Finsupp.mul_sum, Realization.sum_eq_one]
      ring
  refine ⟨⟨z, hzmem⟩, ?_, by simpa [hzv] using t.2.2⟩
  exact K.isRelLowerSet_faces.mem_of_le y.2.2
    (Finset.union_subset_union hsupport Finset.Subset.rfl |>.trans (by simp))
    ((Finset.singleton_nonempty v).mono Finset.subset_union_right)

/-- Coordinates of a ray from the link to its star apex. -/
@[simp]
theorem starRay_apply (y : geometricLink K v) (t : Ico (0 : ℝ) 1) (w : ι) :
    (starRay K v y t).1.1 w = (1 - t.1) * y.1.1 w + if v = w then t.1 else 0 := by
  simp [starRay, Finsupp.single_apply]

/-- Radial projection recovers the link point of a ray. -/
@[simp]
theorem starLinkProjection_starRay (y : geometricLink K v) (t : Ico (0 : ℝ) 1) :
    starLinkProjection K v (starRay K v y t) = y := by
  apply Subtype.ext
  apply Subtype.ext
  ext w
  by_cases h : w = v
  · simp [h]
  · simp [starLinkProjection_apply, starRay_apply, h, Ne.symm h,
      ← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr t.2.2).ne']

/-- The ray determined by a point's radial projection and apex coordinate recovers that point. -/
@[simp]
theorem starRay_starLinkProjection (x : puncturedClosedStar K v) :
    starRay K v (starLinkProjection K v x)
      ⟨x.1.1 v, Realization.nonneg K x.1 v,
        ((mem_puncturedClosedStar K v x.1).mp x.2).2⟩ = x := by
  apply Subtype.ext
  apply Subtype.ext
  ext w
  by_cases h : w = v
  · simp [h]
  · simp [starRay_apply, starLinkProjection_apply, h, Ne.symm h,
      ← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr x.2.2).ne']

/-- The punctured closed star is the product of its geometric link and `[0, 1)`.
The interval coordinate is the coordinate at the apex. -/
def puncturedClosedStarEquiv :
    puncturedClosedStar K v ≃ geometricLink K v × Ico (0 : ℝ) 1 where
  toFun x := ⟨starLinkProjection K v x,
    ⟨x.1.1 v, Realization.nonneg K x.1 v, x.2.2⟩⟩
  invFun p := starRay K v p.1 p.2
  left_inv := starRay_starLinkProjection K v
  right_inv p := by
    apply Prod.ext
    · exact starLinkProjection_starRay K v p.1 p.2
    · exact Subtype.ext (by simp)

/-- The general radial equivalence records projection and the apex coordinate. -/
@[simp]
theorem puncturedClosedStarEquiv_apply (x : puncturedClosedStar K v) :
    puncturedClosedStarEquiv K v x =
      (starLinkProjection K v x, ⟨x.1.1 v, Realization.nonneg K x.1 v,
        ((mem_puncturedClosedStar K v x.1).mp x.2).2⟩) := (rfl)

/-- The inverse radial equivalence is the ray from the link to the apex. -/
@[simp]
theorem puncturedClosedStarEquiv_symm_apply (p : geometricLink K v × Ico (0 : ℝ) 1) :
    (puncturedClosedStarEquiv K v).symm p = starRay K v p.1 p.2 := (rfl)

/-- The coordinate description of the punctured star removes exactly the apex. -/
theorem puncturedClosedStar_eq_sdiff_vertex :
    puncturedClosedStar K v = geometricClosedStar K v \ {vertex K v} := by
  ext x
  simp only [mem_puncturedClosedStar, mem_sdiff, mem_singleton_iff,
    Realization.eq_vertex_iff]
  exact and_congr_right fun _ => lt_iff_le_and_ne.trans
    (by simp [Realization.le_one K x v])

/-- The whole closed star consists of the apex and the rays from its link.
This includes the case of an isolated vertex, where the ray family is empty. -/
theorem geometricClosedStar_eq_insert_range_starRay :
    geometricClosedStar K v = insert (vertex K v)
      (range (fun p : geometricLink K v × Ico (0 : ℝ) 1 => (starRay K v p.1 p.2).1)) := by
  ext x
  constructor
  · intro hx
    by_cases h : x = vertex K v
    · exact mem_insert_iff.mpr (Or.inl h)
    · have hx' : x ∈ puncturedClosedStar K v := by
        rw [puncturedClosedStar_eq_sdiff_vertex]
        exact ⟨hx, h⟩
      let x' : puncturedClosedStar K v := ⟨x, hx'⟩
      refine mem_insert_iff.mpr (Or.inr ⟨puncturedClosedStarEquiv K v x', ?_⟩)
      exact congrArg Subtype.val ((puncturedClosedStarEquiv K v).symm_apply_apply x')
  · rintro (rfl | ⟨p, rfl⟩)
    · simp only [mem_geometricClosedStar, vertex_val,
        Finsupp.support_single v one_ne_zero, Finset.union_self]
      exact K.singleton_mem v
    · exact ((mem_puncturedClosedStar K v _).mp (starRay K v p.1 p.2).2).1

/-- The coordinate at a vertex is continuous on the punctured star. -/
private theorem continuous_puncturedStar_coordinate (w : ι) :
    Continuous (fun x : puncturedClosedStar K v => x.1.1 w) :=
  (continuous_apply w).comp ((continuous_realization_coe K).comp continuous_subtype_val)

/-- Radial projection is continuous when the realization has its coordinate topology. -/
theorem continuous_starLinkProjection
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ))) :
    Continuous (starLinkProjection K v) := by
  apply Continuous.subtype_mk
  apply hK.continuous_iff.mpr
  apply continuous_pi
  intro w
  simp only [Function.comp_apply, normalizedLinkCoordinates_apply]
  have hc := continuous_puncturedStar_coordinate K v
  have hinv := (continuous_const.sub (hc v)).inv₀
    (fun x => (sub_pos.mpr x.2.2).ne')
  by_cases h : w = v
  · simp only [h, ↓reduceIte]
    exact continuous_const
  · simp only [h, ↓reduceIte]
    exact hinv.mul (hc w)

/-- The star rays vary continuously when the realization has its coordinate topology. -/
theorem continuous_starRay
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ))) :
    Continuous (fun p : geometricLink K v × Ico (0 : ℝ) 1 => starRay K v p.1 p.2) := by
  apply Continuous.subtype_mk
  apply hK.continuous_iff.mpr
  apply continuous_pi
  intro w
  have hc : Continuous (fun p : geometricLink K v × Ico (0 : ℝ) 1 => p.1.1.1 w) :=
    (continuous_apply w).comp ((continuous_realization_coe K).comp
      (continuous_subtype_val.comp continuous_fst))
  have ht : Continuous (fun p : geometricLink K v × Ico (0 : ℝ) 1 => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  simp only [Function.comp_apply, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  by_cases h : v = w
  · simp only [h, ↓reduceIte]
    exact ((continuous_const.sub ht).mul hc).add ht
  · simp only [h, ↓reduceIte]
    exact ((continuous_const.sub ht).mul hc).add continuous_const

/-- A vertex star with its apex removed is homeomorphic to its geometric link cross `[0, 1)`,
provided the realization has its coordinate topology. The homeomorphism uses radial barycentric
coordinates; `isClosedEmbedding_realization_coe` supplies the hypothesis for finite vertex types. -/
def puncturedClosedStarHomeomorph
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ))) :
    puncturedClosedStar K v ≃ₜ geometricLink K v × Ico (0 : ℝ) 1 where
  toEquiv := puncturedClosedStarEquiv K v
  continuous_toFun := (continuous_starLinkProjection K v hK).prodMk
    ((continuous_puncturedStar_coordinate K v v).subtype_mk _)
  continuous_invFun := continuous_starRay K v hK

/-- The forward homeomorphism records the radial projection and the apex coordinate. -/
@[simp]
theorem puncturedClosedStarHomeomorph_apply
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (x : puncturedClosedStar K v) :
    puncturedClosedStarHomeomorph K v hK x =
      (starLinkProjection K v x, ⟨x.1.1 v, Realization.nonneg K x.1 v,
        ((mem_puncturedClosedStar K v x.1).mp x.2).2⟩) := (rfl)

/-- The inverse homeomorphism takes a link point along its ray towards the apex. -/
@[simp]
theorem puncturedClosedStarHomeomorph_symm_apply
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (p : geometricLink K v × Ico (0 : ℝ) 1) :
    (puncturedClosedStarHomeomorph K v hK).symm p = starRay K v p.1 p.2 := (rfl)

end AbstractSimplicialComplex
