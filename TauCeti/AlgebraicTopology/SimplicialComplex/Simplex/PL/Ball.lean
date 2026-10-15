/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.Geometry.Manifold.PLGroupoid.Simplex.Ball

/-!
# Half-space PL charts on the weak realization of a solid simplex

The weak realization of the standard `(n + 1)`-simplex has a PL atlas with model the
half-space in `(Fin n → ℝ) × ℝ`. Its vertex-chart domains are exactly the open stars.
Dropping the last barycentric coordinate and reindexing the others identifies the
realization with the coordinate simplex; the existing polyhedral half-space charts
then flatten its corners. Proper-face support is equivalent to normal coordinate zero
on each chart source. These give the solid standard simplex models for transporting
PL charts along simplicial subdivisions.

The construction reuses `realizationTopHomeomorphCoordinateSimplex`, the ambient
`simplexBoundaryCoordinateMap`, and `coordinateSimplexHalfSpaceChart`.
Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Chapters 1–2 (simplices and polyhedral local models).
-/

public noncomputable section

open Set TauCeti
open scoped Manifold

namespace AbstractSimplicialComplex

/-- Barycentric coordinates for the solid simplex, with one retained coordinate singled
out to supply the normal direction in its half-space charts. -/
private def realizationTopHomeomorphOptionCoordinateSimplex (n : ℕ) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) ≃ₜ
      coordinateSimplex (Option (Fin n)) :=
  (realizationTopHomeomorphCoordinateSimplex (n + 1)).trans
    ((simplexCoordinateReindex n).subtype fun x => (simplexCoordinateReindex_mem_iff n x).symm)

/-- The coordinate comparison reads the ambient barycentric linear map. -/
@[simp] private theorem realizationTopHomeomorphOptionCoordinateSimplex_apply (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) (i : Option (Fin n)) :
    (realizationTopHomeomorphOptionCoordinateSimplex n x).1 i =
      simplexBoundaryCoordinateMap n x.1 i := by
  simp [realizationTopHomeomorphOptionCoordinateSimplex,
    realizationTopHomeomorphCoordinateSimplex_apply, simplexBoundaryCoordinateMap_apply,
    simplexCoordinateReindex_apply]

/-- The inverse comparison restores every retained coordinate. -/
@[simp] private theorem realizationTopHomeomorphOptionCoordinateSimplex_symm_castSucc (n : ℕ)
    (y : coordinateSimplex (Option (Fin n))) (i : Fin (n + 1)) :
    ((realizationTopHomeomorphOptionCoordinateSimplex n).symm y).1 i.castSucc =
      y.1 (finSuccEquivLast i) := by
  simp only [realizationTopHomeomorphOptionCoordinateSimplex, Homeomorph.symm_trans_apply,
    realizationTopHomeomorphCoordinateSimplex_symm_castSucc]
  -- Expose the subtype inverse's ambient value to use the public reindexing equation.
  change (simplexCoordinateReindex n).symm y.1 i = y.1 (finSuccEquivLast i)
  simpa only [Homeomorph.apply_symm_apply, Equiv.symm_apply_apply] using
    (simplexCoordinateReindex_apply n ((simplexCoordinateReindex n).symm y.1)
      (finSuccEquivLast i)).symm

/-- The omitted barycentric coordinate is the missing mass. -/
@[simp] private theorem realizationTopHomeomorphOptionCoordinateSimplex_symm_last (n : ℕ)
    (y : coordinateSimplex (Option (Fin n))) :
    ((realizationTopHomeomorphOptionCoordinateSimplex n).symm y).1 (Fin.last (n + 1)) =
      1 - ∑ i, y.1 i := by
  simp only [realizationTopHomeomorphOptionCoordinateSimplex, Homeomorph.symm_trans_apply,
    realizationTopHomeomorphCoordinateSimplex_symm_last]
  -- Expose the subtype inverse's ambient value to reindex the sum with the public equation.
  change 1 - ∑ i, (simplexCoordinateReindex n).symm y.1 i = 1 - ∑ i, y.1 i
  have h := finSuccEquivLast.symm.sum_comp ((simplexCoordinateReindex n).symm y.1)
  simp only [← simplexCoordinateReindex_apply, Homeomorph.apply_symm_apply] at h
  exact congrArg (1 - ·) h.symm

/-- The solid simplex vertex chart, expressed on the actual weak realization. -/
def simplexHalfSpacePLChart (n : ℕ) (v : Option (Option (Fin n))) :
    OpenPartialHomeomorph (Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))))
      {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} :=
  (realizationTopHomeomorphOptionCoordinateSimplex n).transOpenPartialHomeomorph
    (coordinateSimplexHalfSpaceChart v)

/-- Each chart has precisely the open star of its indexing vertex as source.
`none` indexes the omitted vertex; `some i` indexes the retained vertex corresponding to `i`. -/
@[simp] theorem simplexHalfSpacePLChart_source (n : ℕ) (v : Option (Option (Fin n))) :
    (simplexHalfSpacePLChart n v).source =
      openStarRealization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))
        (v.elim (Fin.last (n + 1)) (fun i => (finSuccEquivLast.symm i).castSucc)) := by
  ext x
  rw [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_source,
    coordinateSimplexHalfSpaceChart_source]
  cases v with
  | none =>
    simp only [coordinateSimplexHalfSpaceChartSource_none, mem_preimage, mem_ofPred_eq,
      Option.elim_none]
    have hret : (∑ i, (realizationTopHomeomorphOptionCoordinateSimplex n x).1 i) =
        ∑ j : Fin (n + 1), x.1 j.castSucc := by
      simp only [realizationTopHomeomorphOptionCoordinateSimplex_apply,
        simplexBoundaryCoordinateMap_apply]
      exact finSuccEquivLast.symm.sum_comp (fun j => x.1 j.castSucc)
    rw [hret]
    simpa only [realizationTopHomeomorphCoordinateSimplex_apply] using
      (mem_openStarRealization_top_last_iff_sum_lt_one (n + 1) x).symm
  | some i =>
    simp only [coordinateSimplexHalfSpaceChartSource_some, mem_preimage, mem_ofPred_eq,
      mem_openStarRealization, Option.elim_some,
      realizationTopHomeomorphOptionCoordinateSimplex_apply, simplexBoundaryCoordinateMap_apply]

/-- All solid simplex vertex charts have the same open half-space target. -/
@[simp] theorem simplexHalfSpacePLChart_target (n : ℕ) (v : Option (Option (Fin n))) :
    (simplexHalfSpacePLChart n v).target =
      {q | ∑ i, (coordinateSimplexHalfSpaceMap none).symm q.1 i < 1} := by
  rw [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_target,
    coordinateSimplexHalfSpaceChart_target]

/-- The chart's ambient coordinates are given by the existing polyhedral flattening map. -/
@[simp] theorem coe_simplexHalfSpacePLChart_apply (n : ℕ) (v : Option (Option (Fin n)))
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) :
    (simplexHalfSpacePLChart n v x).1 =
      coordinateSimplexHalfSpaceMap v (simplexBoundaryCoordinateMap n x.1) := by
  simp only [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_apply,
    Function.comp_apply, coe_coordinateSimplexHalfSpaceChart_apply]
  congr 1
  ext i
  exact realizationTopHomeomorphOptionCoordinateSimplex_apply n x i

/-- On the target the inverse chart recovers the retained barycentric coordinates. -/
theorem simplexHalfSpacePLChart_symm_castSucc (n : ℕ) (v : Option (Option (Fin n)))
    {q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}}
    (hq : q ∈ (simplexHalfSpacePLChart n v).target) (i : Fin (n + 1)) :
    ((simplexHalfSpacePLChart n v).symm q).1 i.castSucc =
      (coordinateSimplexHalfSpaceMap v).symm q.1 (finSuccEquivLast i) := by
  simp only [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Function.comp_apply, realizationTopHomeomorphOptionCoordinateSimplex_symm_castSucc]
  rw [coe_coordinateSimplexHalfSpaceChart_symm_apply v hq]

/-- The omitted inverse barycentric coordinate is the missing mass of the ambient inverse. -/
theorem simplexHalfSpacePLChart_symm_last (n : ℕ) (v : Option (Option (Fin n)))
    {q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}}
    (hq : q ∈ (simplexHalfSpacePLChart n v).target) :
    ((simplexHalfSpacePLChart n v).symm q).1 (Fin.last (n + 1)) =
      1 - ∑ i, (coordinateSimplexHalfSpaceMap v).symm q.1 i := by
  simp only [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Function.comp_apply, realizationTopHomeomorphOptionCoordinateSimplex_symm_last]
  rw [coe_coordinateSimplexHalfSpaceChart_symm_apply v hq]

/-- On a vertex chart's source, proper-face support is exactly normal coordinate zero. -/
theorem support_ne_univ_iff_simplexHalfSpacePLChart_snd_eq_zero (n : ℕ)
    (v : Option (Option (Fin n)))
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))))
    (hx : x ∈ (simplexHalfSpacePLChart n v).source) :
    x.1.support ≠ Finset.univ ↔ (simplexHalfSpacePLChart n v x).1.2 = 0 := by
  let y := realizationTopHomeomorphOptionCoordinateSimplex n x
  have hy : y ∈ coordinateSimplexHalfSpaceChartSource v := by
    simpa only [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_source,
      coordinateSimplexHalfSpaceChart_source, mem_preimage] using hx
  simp only [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_apply,
    Function.comp_apply]
  rw [← mem_frontier_coordinateSimplex_iff_halfSpaceChart_snd_eq_zero v y hy,
    ← realizationTopHomeomorphCoordinateSimplex_mem_frontier_iff (n + 1) x,
    mem_frontier_coordinateSimplex, mem_frontier_coordinateSimplex]
  have hsum : (∑ i, y.1 i) =
      ∑ j : Fin (n + 1), (realizationTopHomeomorphCoordinateSimplex (n + 1) x).1 j := by
    simp only [y, realizationTopHomeomorphOptionCoordinateSimplex_apply,
      simplexBoundaryCoordinateMap_apply, realizationTopHomeomorphCoordinateSimplex_apply]
    exact finSuccEquivLast.symm.sum_comp (fun j => x.1 j.castSucc)
  simp only [iff_true_intro ((mem_coordinateSimplex _ _).mp
      (realizationTopHomeomorphCoordinateSimplex (n + 1) x).2),
    iff_true_intro ((mem_coordinateSimplex _ _).mp y.2), true_and]
  rw [hsum]
  exact or_congr (finSuccEquivLast.exists_congr fun i => by simp [y]) Iff.rfl

/-- Coordinate changes have finite affine decompositions in the ambient half-space model. -/
theorem isPiecewiseAffineOn_simplexHalfSpacePLChart_transition (n : ℕ)
    (v w : Option (Option (Fin n))) :
    let I := modelWithCornersHalfSpace (Fin n → ℝ)
    let e := (simplexHalfSpacePLChart n v).symm.trans (simplexHalfSpacePLChart n w)
    IsPiecewiseAffineOn (I ∘ e ∘ I.symm) (I.symm ⁻¹' e.source ∩ range I) := by
  refine ((isPiecewiseAffineOn_coordinateSimplexHalfSpaceChart_transition v w).mono ?_).congr ?_
  · intro y hy
    simpa only [simplexHalfSpacePLChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Homeomorph.transOpenPartialHomeomorph_target,
      Homeomorph.transOpenPartialHomeomorph_symm_apply,
      Homeomorph.transOpenPartialHomeomorph_source, Function.comp_apply, mem_inter_iff,
      mem_preimage, Homeomorph.apply_symm_apply] using hy
  · intro y hy
    simp only [simplexHalfSpacePLChart, mfld_simps]
    simp

/-- The finite vertex atlas on the solid simplex's weak realization. -/
@[instance_reducible] def simplexHalfSpacePLChartedSpace (n : ℕ) :
    ChartedSpace {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}
      (Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) where
  atlas := range (simplexHalfSpacePLChart n)
  chartAt x := simplexHalfSpacePLChart n (Classical.choose
    (exists_mem_coordinateSimplexHalfSpaceChartSource
      (realizationTopHomeomorphOptionCoordinateSimplex n x)))
  mem_chart_source x := by
    rw [simplexHalfSpacePLChart, Homeomorph.transOpenPartialHomeomorph_source,
      coordinateSimplexHalfSpaceChart_source]
    exact Classical.choose_spec (exists_mem_coordinateSimplexHalfSpaceChartSource
      (realizationTopHomeomorphOptionCoordinateSimplex n x))
  chart_mem_atlas _ := mem_range_self _

/-- The atlas consists exactly of the prescribed half-space vertex charts. -/
@[simp] theorem simplexHalfSpacePLChartedSpace_atlas (n : ℕ) :
    @atlas {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} _
      (Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) _
      (simplexHalfSpacePLChartedSpace n) = range (simplexHalfSpacePLChart n) := (rfl)

/-- The weak realization of the solid standard `(n + 1)`-simplex is a PL manifold
with boundary, with its barycentric open-star atlas. The case `n = 0` is the segment. -/
theorem realizationTopHalfSpace_hasGroupoid (n : ℕ) :
    letI := simplexHalfSpacePLChartedSpace n
    HasGroupoid (Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))))
      (PLGroupoid (modelWithCornersHalfSpace (Fin n → ℝ))) := by
  let := simplexHalfSpacePLChartedSpace n
  constructor
  rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
  rw [mem_PLGroupoid_iff]
  constructor
  · exact (isPiecewiseAffineOn_simplexHalfSpacePLChart_transition n v w).isPLOn
  · simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, ← OpenPartialHomeomorph.symm_source] using
      (isPiecewiseAffineOn_simplexHalfSpacePLChart_transition n w v).isPLOn

end AbstractSimplicialComplex
