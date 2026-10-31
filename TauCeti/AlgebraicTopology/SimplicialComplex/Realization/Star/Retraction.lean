/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Open stars of full subcomplexes

Let `s` be a set of vertices of an abstract simplicial complex `K`. The full subcomplex of `K`
spanned by `s` consists of the faces all of whose vertices lie in `s`. Its polyhedron is the closed
set of points of the realization whose barycentric support lies in `s`; it is identified with the
realization of `K.restrict s` by `AbstractSimplicialComplex.restrictRealizationHomeomorph`.

The open star `openStarRealizationSet K s` consists of the points with a positive barycentric
coordinate at some vertex of `s`. It is the union of the open vertex stars of `s`, and an open
neighbourhood of the full subcomplex. Normalizing the part of the barycentric coordinates supported
on `s` gives a retraction `openStarRetraction` of the open star onto the full subcomplex. The
straight segment from a point to its normalized part stays in the closed simplex carrying the point
and in the open star. This gives `openStarDeformation`, a strong deformation retraction of the open
star onto the full subcomplex.

Every subcomplex is full after one barycentric subdivision, so this is the form in which simplicial
neighbourhood retractions apply to arbitrary subcomplexes. No finiteness or local finiteness is
assumed: continuity is checked on the traces of the open star in the closed simplex cylinders of
the weak realization.

## Main definitions

* `AbstractSimplicialComplex.openStarRealizationSet`: the open star of a set of vertices.
* `AbstractSimplicialComplex.openStarRetraction`: normalized restriction of barycentric
  coordinates, retracting the open star onto the full subcomplex.
* `AbstractSimplicialComplex.openStarDeformation`: the straight-line homotopy from the identity of
  the open star to this retraction, fixing the full subcomplex.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (full subcomplexes and simplicial neighbourhoods).
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike Convexity

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (s : Set ι)

/-- The open star of a set of vertices: the points of the realization with a positive barycentric
coordinate at some vertex of `s`. -/
def openStarRealizationSet : Set (Realization K) := {x | ∃ v ∈ s, 0 < x.1 v}

/-- Membership in the open star of a set of vertices. -/
@[simp]
theorem mem_openStarRealizationSet {x : Realization K} :
    x ∈ K.openStarRealizationSet s ↔ ∃ v ∈ s, 0 < x.1 v := Iff.rfl

/-- The open star of a set of vertices is the union of the open stars of its vertices. -/
theorem openStarRealizationSet_eq_biUnion :
    K.openStarRealizationSet s = ⋃ v ∈ s, K.openStarRealization v := by
  ext x
  simp

/-- The open star of a single vertex is its open vertex star. -/
@[simp]
theorem openStarRealizationSet_singleton (v : ι) :
    K.openStarRealizationSet {v} = K.openStarRealization v := by
  ext x
  simp

/-- The open star of a set of vertices is open in the weak topology. -/
theorem isOpen_openStarRealizationSet : IsOpen (K.openStarRealizationSet s) := by
  rw [openStarRealizationSet_eq_biUnion]
  exact isOpen_biUnion fun v _ => K.isOpen_openStarRealization v

/-- The polyhedron of the full subcomplex spanned by `s` lies in the open star of `s`. -/
theorem setOf_support_subset_subset_openStarRealizationSet :
    {x : Realization K | (x.1.support : Set ι) ⊆ s} ⊆ K.openStarRealizationSet s := by
  intro x hx
  obtain ⟨v, hv⟩ := K.isRelLowerSet_faces.prop_of_mem (support_mem K x)
  exact ⟨v, hx hv, Realization.pos_of_mem_support K x hv⟩

/-- The barycentric coordinates of a realization point, as a point of Mathlib's standard
simplex. -/
private def stdSimplex (x : Realization K) : StdSimplex ℝ ι :=
  ⟨x.1, Realization.nonneg K x, Realization.sum_eq_one K x⟩

private theorem stdSimplex_weights (x : Realization K) : (stdSimplex K x).weights = x.1 := (rfl)

/-- A point of Mathlib's standard simplex whose support is a face is a realization point. -/
private def ofStdSimplex (w : StdSimplex ℝ ι) (hw : w.weights.support ∈ K) : Realization K :=
  ⟨w.weights, TauCeti.mem_standardGeometricComplex_space_iff.mpr
    ⟨fun v => StdSimplex.weights_nonneg v, w.total, hw⟩⟩

private theorem ofStdSimplex_val (w : StdSimplex ℝ ι) (hw : w.weights.support ∈ K) :
    (ofStdSimplex K w hw).1 = w.weights := (rfl)

private theorem exists_stdSimplex_weights_ne_zero (x : K.openStarRealizationSet s) :
    ∃ v ∈ s, (stdSimplex K x.1).weights v ≠ 0 := by
  obtain ⟨v, hv, hpos⟩ := x.2
  exact ⟨v, hv, hpos.ne'⟩

/-- The part of the barycentric coordinates of a point of the open star supported on `s`,
normalized to total mass one. -/
private def normalizedPart (x : K.openStarRealizationSet s) : StdSimplex ℝ ι :=
  (stdSimplex K x.1).restrict s (exists_stdSimplex_weights_ne_zero K s x)

private theorem support_normalizedPart [DecidablePred (· ∈ s)]
    (x : K.openStarRealizationSet s) :
    (normalizedPart K s x).weights.support = x.1.1.support.filter (· ∈ s) :=
  StdSimplex.support_weights_restrict _ _ _

/-- On the full subcomplex, the normalized part of a point is the point itself. -/
private theorem normalizedPart_eq_stdSimplex (x : K.openStarRealizationSet s)
    (hx : (x.1.1.support : Set ι) ⊆ s) : normalizedPart K s x = stdSimplex K x.1 := by
  classical
  have hfilter : x.1.1.filter (· ∈ s) = x.1.1 :=
    (Finsupp.filter_eq_self_iff _ _).mpr fun v hv => hx (Finsupp.mem_support_iff.mpr hv)
  ext1
  rw [normalizedPart, StdSimplex.weights_restrict]
  simp only [stdSimplex_weights, hfilter, Realization.sum_eq_one, inv_one, one_smul]

/-- The point at time `t` of the segment from a point of the open star to its normalized part. -/
private def segment (t : unitInterval) (x : K.openStarRealizationSet s) : StdSimplex ℝ ι :=
  convexCombPair (1 - (t : ℝ)) t (sub_nonneg.2 t.2.2) t.2.1 (sub_add_cancel _ _)
    (stdSimplex K x.1) (normalizedPart K s x)

private theorem segment_weights (t : unitInterval) (x : K.openStarRealizationSet s) :
    (segment K s t x).weights =
      (1 - (t : ℝ)) • x.1.1 + (t : ℝ) • (normalizedPart K s x).weights :=
  StdSimplex.weights_convexCombPair ..

/-- The segment stays in the closed simplex carrying its starting point. -/
private theorem support_segment_subset (t : unitInterval) (x : K.openStarRealizationSet s) :
    (segment K s t x).weights.support ⊆ x.1.1.support := by
  classical
  rw [segment_weights]
  refine Finsupp.support_add.trans (Finset.union_subset Finsupp.support_smul
    (Finsupp.support_smul.trans ?_))
  rw [support_normalizedPart]
  exact Finset.filter_subset _ _

private theorem support_segment_mem (t : unitInterval) (x : K.openStarRealizationSet s) :
    (segment K s t x).weights.support ∈ K :=
  K.isRelLowerSet_faces.mem_of_le (support_mem K x.1) (support_segment_subset K s t x)
    (StdSimplex.support_weights_nonempty _)

/-- The segment stays in the open star: the coordinate at a vertex of `s` where the starting
point is positive stays positive. -/
private theorem ofStdSimplex_segment_mem (t : unitInterval) (x : K.openStarRealizationSet s) :
    ofStdSimplex K (segment K s t x) (support_segment_mem K s t x) ∈
      K.openStarRealizationSet s := by
  classical
  obtain ⟨v, hv, hpos⟩ := x.2
  have hr : 0 < (normalizedPart K s x).weights v := by
    refine (StdSimplex.weights_nonneg v).lt_of_ne' (Finsupp.mem_support_iff.mp ?_)
    rw [support_normalizedPart]
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hpos.ne', hv⟩
  refine ⟨v, hv, ?_⟩
  simp only [ofStdSimplex_val, segment_weights, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rcases t.2.1.eq_or_lt with h | h
  · simpa [← h] using hpos
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 t.2.2) hpos.le) (mul_pos h hr)

/-- The straight-line deformation of the open star, as a function of time and position. -/
private def deformation (p : unitInterval × K.openStarRealizationSet s) :
    K.openStarRealizationSet s :=
  ⟨ofStdSimplex K (segment K s p.1 p.2) (support_segment_mem K s p.1 p.2),
    ofStdSimplex_segment_mem K s p.1 p.2⟩

private theorem deformation_val (p : unitInterval × K.openStarRealizationSet s) :
    (deformation K s p).1.1 = (segment K s p.1 p.2).weights := (rfl)

/-- On a closed simplex, the mass of the coordinates supported on `s` is a finite sum over the
vertices of that simplex. -/
private theorem sum_filter_eq_sum [DecidablePred (· ∈ s)] {σ : Finset ι} (y : StandardSimplex σ) :
    ((y.1.filter (· ∈ s)).sum fun _ r => r) = ∑ v ∈ σ with v ∈ s, y.1 v := by
  have hsub : (y.1.filter (· ∈ s)).support ⊆ σ.filter (· ∈ s) := by
    rw [Finsupp.support_filter]
    exact Finset.filter_subset_filter _ (StandardSimplex.support_subset y)
  rw [Finsupp.sum_of_support_subset _ hsub _ fun _ _ => rfl]
  exact Finset.sum_congr rfl fun v hv =>
    Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hv).2

private theorem continuous_deformation : Continuous (deformation K s) := by
  classical
  refine continuous_induced_rng.mpr ?_
  refine (continuous_prod_subtype_iff_faceInclusion_of_isOpen
    (K.isOpen_openStarRealizationSet s)).mpr fun σ => ?_
  -- On the trace of the open star in a closed simplex, the deformation has explicit coordinates.
  let Y := faceInclusion K σ ⁻¹' K.openStarRealizationSet s
  have hcoord (v : ι) : Continuous fun p : unitInterval × Y => p.2.1.1 v := by
    have h : Continuous fun x : StandardSimplex σ.1 => (x.1 : ι → ℝ) := continuous_induced_dom
    exact (continuous_apply v).comp (h.comp (continuous_subtype_val.comp continuous_snd))
  have ht : Continuous fun p : unitInterval × Y => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hmass (p : unitInterval × Y) : ∑ v ∈ σ.1 with v ∈ s, p.2.1.1 v ≠ 0 := by
    obtain ⟨v, hv, hpos⟩ := p.2.2
    rw [faceInclusion_val] at hpos
    exact (Finset.sum_pos' (fun w _ => StandardSimplex.nonneg _ w) ⟨v, Finset.mem_filter.mpr
      ⟨StandardSimplex.support_subset _ (Finsupp.mem_support_iff.mpr hpos.ne'), hv⟩,
        hpos⟩).ne'
  have hinv : Continuous fun p : unitInterval × Y => (∑ v ∈ σ.1 with v ∈ s, p.2.1.1 v)⁻¹ :=
    (continuous_finsetSum _ fun v _ => hcoord v).inv₀ hmass
  have hweights (p : unitInterval × Y) (w : ι) :
      (segment K s p.1 ⟨faceInclusion K σ p.2, p.2.2⟩).weights w =
        (1 - (p.1 : ℝ)) * p.2.1.1 w + p.1 *
          ((∑ v ∈ σ.1 with v ∈ s, p.2.1.1 v)⁻¹ * if w ∈ s then p.2.1.1 w else 0) := by
    rw [segment_weights, normalizedPart, StdSimplex.weights_restrict]
    simp only [stdSimplex_weights, faceInclusion_val, sum_filter_eq_sum, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.filter_apply, smul_eq_mul]
  let G : unitInterval × Y → StandardSimplex σ.1 := fun p =>
    ⟨(segment K s p.1 ⟨faceInclusion K σ p.2, p.2.2⟩).weights, by
      rw [Finset.coe_image, mem_standardSimplex_iff]
      refine ⟨fun v => StdSimplex.weights_nonneg v, StdSimplex.total _,
        (support_segment_subset K s _ _).trans ?_⟩
      rw [faceInclusion_val]
      exact StandardSimplex.support_subset _⟩
  have hG : Continuous G := by
    refine continuous_induced_rng.mpr (continuous_pi fun w => ?_)
    simp only [Function.comp_apply, G, hweights]
    by_cases hw : w ∈ s
    · simp only [hw, ↓reduceIte]
      exact ((continuous_const.sub ht).mul (hcoord w)).add (ht.mul (hinv.mul (hcoord w)))
    · simp only [hw, ↓reduceIte, mul_zero, add_zero]
      exact (continuous_const.sub ht).mul (hcoord w)
  exact ((continuous_faceInclusion K σ).comp hG).congr fun p =>
    Subtype.ext (faceInclusion_val _ _ _)

private theorem support_normalizedPart_mem (x : K.openStarRealizationSet s) :
    (normalizedPart K s x).weights.support ∈ K := by
  classical
  refine K.isRelLowerSet_faces.mem_of_le (support_mem K x.1) ?_
    (StdSimplex.support_weights_nonempty _)
  rw [support_normalizedPart]
  exact Finset.filter_subset _ _

/-- At time one, the deformation reaches the normalized part. -/
private theorem deformation_one (x : K.openStarRealizationSet s) :
    (deformation K s (1, x)).1 = ofStdSimplex K (normalizedPart K s x)
      (support_normalizedPart_mem K s x) := by
  apply Subtype.ext
  rw [deformation_val, segment_weights, ofStdSimplex_val]
  simp

/-- The retraction of the open star of `s` onto the polyhedron of the full subcomplex spanned by
`s`: the coordinates supported on `s` are kept and normalized to total mass one. -/
def openStarRetraction :
    C(K.openStarRealizationSet s, {x : Realization K | (x.1.support : Set ι) ⊆ s}) where
  toFun x := ⟨ofStdSimplex K (normalizedPart K s x) (support_normalizedPart_mem K s x), by
    classical
    intro v hv
    rw [ofStdSimplex_val, Finset.mem_coe, support_normalizedPart] at hv
    exact (Finset.mem_filter.mp hv).2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp ((continuous_deformation K s).comp
      (continuous_const.prodMk continuous_id))).congr (deformation_one K s)

private theorem openStarRetraction_val (x : K.openStarRealizationSet s) :
    ((K.openStarRetraction s x : Realization K) : ι →₀ ℝ) = (normalizedPart K s x).weights :=
  (rfl)

/-- The coordinates of the retraction are the coordinates supported on `s`, divided by their
total mass. -/
theorem openStarRetraction_apply_coe [DecidablePred (· ∈ s)] (x : K.openStarRealizationSet s) :
    ((K.openStarRetraction s x : Realization K) : ι →₀ ℝ) =
      ((x.1.1.filter (· ∈ s)).sum fun _ r => r)⁻¹ • x.1.1.filter (· ∈ s) :=
  StdSimplex.weights_restrict _ _ (exists_stdSimplex_weights_ne_zero K s x)

/-- The retraction fixes the polyhedron of the full subcomplex. -/
@[simp]
theorem openStarRetraction_inclusion
    (x : {x : Realization K | (x.1.support : Set ι) ⊆ s}) :
    K.openStarRetraction s
      (Set.inclusion (K.setOf_support_subset_subset_openStarRealizationSet s) x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [openStarRetraction_val, normalizedPart_eq_stdSimplex K s _ x.2, stdSimplex_weights]

/-- **The open star of a full subcomplex deformation retracts onto it.** The homotopy moves a
point `x` of the open star of `s` along the straight segment `(1 - t) x + t r(x)` in its closed
carrier simplex, where `r` is `openStarRetraction`. It fixes the polyhedron of the full subcomplex
spanned by `s` at all times. -/
def openStarDeformation :
    (ContinuousMap.id (K.openStarRealizationSet s)).HomotopyRel
      ((ContinuousMap.inclusion (K.setOf_support_subset_subset_openStarRealizationSet s)).comp
        (K.openStarRetraction s))
      {x | ((x : Realization K).1.support : Set ι) ⊆ s} where
  toFun := deformation K s
  continuous_toFun := continuous_deformation K s
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [deformation_val, segment_weights]
    simp
  map_one_left x := Subtype.ext (deformation_one K s x)
  prop' t x hx := by
    apply Subtype.ext
    apply Subtype.ext
    rw [ContinuousMap.coe_mk, ContinuousMap.id_apply, deformation_val, segment_weights,
      normalizedPart_eq_stdSimplex K s x hx, stdSimplex_weights, ← add_smul,
      sub_add_cancel, one_smul]

/-- At time `t`, the deformation is the convex combination with weights `1 - t` and `t` of a
point and its retraction. -/
@[simp]
theorem openStarDeformation_apply_coe (t : unitInterval) (x : K.openStarRealizationSet s) :
    ((K.openStarDeformation s (t, x) : Realization K) : ι →₀ ℝ) =
      (1 - (t : ℝ)) • x.1.1 + (t : ℝ) • ((K.openStarRetraction s x : Realization K) : ι →₀ ℝ) :=
  segment_weights K s t x

end AbstractSimplicialComplex
