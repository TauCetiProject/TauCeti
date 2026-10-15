/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex
public import TauCeti.Geometry.Manifold.PLGroupoid.Simplex.Boundary

/-!
# PL charts on the weak realization of a simplex boundary

The boundary of the standard `(n + 1)`-simplex carries a PL atlas on its weak realization.
The charts drop the last barycentric coordinate, reindex the remaining coordinates, and
apply the polyhedral vertex charts of the coordinate simplex boundary. Thus these are
charts of the simplicial polyhedron itself, with explicit ambient affine coordinate maps,
rather than charts transported through a round sphere.

The affine identification with the coordinate frontier supplies the standard PL sphere
model used when transporting local charts along stellar equivalences. The construction
includes the two-point zero-sphere, with zero-dimensional chart model.

Reuse the weak realization's closed-subcomplex embedding, the coordinate-simplex
homeomorphism and shared ambient coordinate maps from `Simplex.Ball`, and the existing
polyhedral boundary atlas.
Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Chapters 1–2.
-/

public noncomputable section

open Set TauCeti
open scoped Manifold

namespace AbstractSimplicialComplex

/-- The weak boundary realization is identified with the geometric coordinate frontier by
an affine barycentric formula. Unlike a radial sphere identification, this map is PL. -/
def realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex (n : ℕ) :
    Realization (standardSuccSimplexBoundary n) ≃ₜ
      frontier (coordinateSimplex (Option (Fin n))) := by
  let K := standardSuccSimplexBoundary n
  let hK : K ≤ (⊤ : AbstractSimplicialComplex (Fin (n + 2))) := le_top
  let r := (isClosedEmbedding_realizationMap hK).isEmbedding.toHomeomorph
  let e := realizationTopHomeomorphCoordinateSimplex (n + 1)
  have hfront (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) :
      x ∈ range (realizationMap hK) ↔ (e x).1 ∈ frontier (coordinateSimplex (Fin (n + 1))) := by
    rw [mem_range_realizationMap, realizationTopHomeomorphCoordinateSimplex_mem_frontier_iff]
    simp only [K, mem_standardSuccSimplexBoundary_iff, Finset.ssubset_univ_iff]
    exact and_iff_right
      ((⊤ : AbstractSimplicialComplex (Fin (n + 2))).isRelLowerSet_faces.prop_of_mem
        (support_mem _ x))
  let b := e.subtype (p := fun x => x ∈ range (realizationMap hK))
    (q := fun y => y.1 ∈ frontier (coordinateSimplex (Fin (n + 1)))) hfront
  let flat : {y : coordinateSimplex (Fin (n + 1)) //
      y.1 ∈ frontier (coordinateSimplex (Fin (n + 1)))} ≃ₜ
      frontier (coordinateSimplex (Fin (n + 1))) := {
    toFun := fun y => ⟨y.1.1, y.2⟩
    invFun := fun y =>
      ⟨⟨y.1, (mem_coordinateSimplex _ _).mpr
        ((mem_frontier_coordinateSimplex _ _).mp y.2).1⟩, y.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let a := simplexCoordinateReindex n
  have hpre : a ⁻¹' coordinateSimplex (Option (Fin n)) = coordinateSimplex (Fin (n + 1)) :=
    Set.ext (simplexCoordinateReindex_mem_iff n)
  have hf := a.preimage_frontier (coordinateSimplex (Option (Fin n)))
  rw [hpre] at hf
  exact r.trans (b.trans (flat.trans (a.subtype fun x => (Set.ext_iff.mp hf x).symm)))

/-- The frontier identification reads the ambient linear coordinate map. -/
@[simp] theorem realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_apply
    (n : ℕ) (x : Realization (standardSuccSimplexBoundary n)) (i : Option (Fin n)) :
    (realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n x).1 i =
      simplexBoundaryCoordinateMap n x.1 i := by
  simp [realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex,
    realizationTopHomeomorphCoordinateSimplex_apply, realizationMap_val,
    simplexBoundaryCoordinateMap_apply, simplexCoordinateReindex_apply]

/-- The inverse frontier identification restores every retained coordinate. -/
@[simp] theorem realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_symm_castSucc
    (n : ℕ) (y : frontier (coordinateSimplex (Option (Fin n)))) (i : Fin (n + 1)) :
    ((realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n).symm y).1 i.castSucc =
      y.1 (finSuccEquivLast i) := by
  have h := congrArg (fun z : frontier (coordinateSimplex (Option (Fin n))) =>
    z.1 (finSuccEquivLast i))
    ((realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n).apply_symm_apply y)
  simpa only [realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_apply,
    simplexBoundaryCoordinateMap_apply, Equiv.symm_apply_apply] using h

/-- The discarded barycentric coordinate is the missing coordinate mass. -/
@[simp] theorem realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_symm_last
    (n : ℕ) (y : frontier (coordinateSimplex (Option (Fin n)))) :
    ((realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n).symm y).1
        (Fin.last (n + 1)) = 1 - ∑ i, y.1 i := by
  have h := Realization.sum_eq_one (standardSuccSimplexBoundary n)
    ((realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n).symm y)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
  simp only [realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_symm_castSucc] at h
  rw [finSuccEquivLast.sum_comp] at h
  linarith

/-- A PL vertex chart on the weak simplex boundary, obtained from its affine frontier
identification and a polyhedral vertex chart. -/
def simplexBoundaryPLChart (n : ℕ) (v : Option (Option (Fin n))) :
    OpenPartialHomeomorph (Realization (standardSuccSimplexBoundary n)) (Fin n → ℝ) :=
  (realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n).transOpenPartialHomeomorph
    (coordinateSimplexBoundaryChart v)

/-- The polyhedral chart region is exactly the open star of its indexing vertex.
`none` indexes the discarded vertex, and `some i` indexes the retained vertex corresponding
to `i`. This identifies the chart domains combinatorially for transport along subdivisions. -/
@[simp] theorem simplexBoundaryPLChart_source (n : ℕ) (v : Option (Option (Fin n))) :
    (simplexBoundaryPLChart n v).source = openStarRealization (standardSuccSimplexBoundary n)
      (v.elim (Fin.last (n + 1)) (fun i => (finSuccEquivLast.symm i).castSucc)) := by
  ext x
  rw [simplexBoundaryPLChart, Homeomorph.transOpenPartialHomeomorph_source,
    coordinateSimplexBoundaryChart_source]
  cases v with
  | none =>
    simp only [coordinateSimplexBoundaryChartSource_none, mem_preimage, mem_ofPred_eq,
      mem_openStarRealization, Option.elim_none]
    have hsum := Realization.sum_eq_one (standardSuccSimplexBoundary n) x
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at hsum
    have hret : (∑ i, (realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n x).1 i) =
        ∑ j : Fin (n + 1), x.1 j.castSucc := by
      simp only [realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_apply,
        simplexBoundaryCoordinateMap_apply]
      exact finSuccEquivLast.symm.sum_comp (fun j => x.1 j.castSucc)
    rw [hret]
    constructor <;> intro h <;> linarith
  | some i =>
    simp only [coordinateSimplexBoundaryChartSource_some, mem_preimage, mem_ofPred_eq,
      mem_openStarRealization, Option.elim_some,
      realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_apply,
      simplexBoundaryCoordinateMap_apply]

/-- All vertex charts have the same open flat target. -/
@[simp] theorem simplexBoundaryPLChart_target (n : ℕ) (v : Option (Option (Fin n))) :
    (simplexBoundaryPLChart n v).target =
      {y | ∑ i, coordinateSimplexBoundaryLift y i < 1} := by
  rw [simplexBoundaryPLChart, Homeomorph.transOpenPartialHomeomorph_target,
    coordinateSimplexBoundaryChart_target]

/-- The chart formula is affine in the ambient barycentric coordinates. -/
@[simp] theorem simplexBoundaryPLChart_apply (n : ℕ) (v : Option (Option (Fin n)))
    (x : Realization (standardSuccSimplexBoundary n)) :
    simplexBoundaryPLChart n v x =
      coordinateSimplexBoundaryChartProjection v (simplexBoundaryCoordinateMap n x.1) := by
  simp only [simplexBoundaryPLChart, Homeomorph.transOpenPartialHomeomorph_apply,
    Function.comp_apply, coordinateSimplexBoundaryChart_apply]
  congr 1
  ext i
  exact realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_apply n x i

/-- On the chart target, inverse coordinates use the polyhedral PL lift. -/
theorem simplexBoundaryPLChart_symm_castSucc (n : ℕ) (v : Option (Option (Fin n)))
    {y : Fin n → ℝ} (hy : ∑ i, coordinateSimplexBoundaryLift y i < 1) (i : Fin (n + 1)) :
    ((simplexBoundaryPLChart n v).symm y).1 i.castSucc =
      coordinateSimplexBoundaryChartLift v y (finSuccEquivLast i) := by
  simp only [simplexBoundaryPLChart, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Function.comp_apply,
    realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_symm_castSucc]
  rw [coe_coordinateSimplexBoundaryChart_symm_apply v hy]

/-- The inverse chart recovers the discarded coordinate as the missing mass of the PL lift. -/
theorem simplexBoundaryPLChart_symm_last (n : ℕ) (v : Option (Option (Fin n)))
    {y : Fin n → ℝ} (hy : ∑ i, coordinateSimplexBoundaryLift y i < 1) :
    ((simplexBoundaryPLChart n v).symm y).1 (Fin.last (n + 1)) =
      1 - ∑ i, coordinateSimplexBoundaryChartLift v y i := by
  simp only [simplexBoundaryPLChart, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Function.comp_apply,
    realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex_symm_last]
  rw [coe_coordinateSimplexBoundaryChart_symm_apply v hy]

/-- Transition maps of the weak boundary charts are piecewise affine, including at vertices. -/
theorem isPiecewiseAffineOn_simplexBoundaryPLChart_transition (n : ℕ)
    (v w : Option (Option (Fin n))) :
    IsPiecewiseAffineOn ((simplexBoundaryPLChart n v).symm.trans (simplexBoundaryPLChart n w))
      ((simplexBoundaryPLChart n v).symm.trans (simplexBoundaryPLChart n w)).source := by
  refine ((isPiecewiseAffineOn_coordinateSimplexBoundaryChart_transition v w).mono ?_).congr ?_
  · intro y hy
    simpa only [simplexBoundaryPLChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Homeomorph.transOpenPartialHomeomorph_target,
      Homeomorph.transOpenPartialHomeomorph_symm_apply,
      Homeomorph.transOpenPartialHomeomorph_source, Function.comp_apply, mem_inter_iff,
      mem_preimage, Homeomorph.apply_symm_apply] using hy
  · intro y hy
    simp only [simplexBoundaryPLChart, mfld_simps]
    simp

/-- The finite vertex atlas on the weak realization of a standard simplex boundary. -/
@[instance_reducible] def simplexBoundaryPLChartedSpace (n : ℕ) :
    ChartedSpace (Fin n → ℝ) (Realization (standardSuccSimplexBoundary n)) where
  atlas := range (simplexBoundaryPLChart n)
  chartAt x := simplexBoundaryPLChart n (Classical.choose
    (exists_mem_coordinateSimplexBoundaryChartSource
      (realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n x)))
  mem_chart_source x := by
    rw [simplexBoundaryPLChart, Homeomorph.transOpenPartialHomeomorph_source,
      coordinateSimplexBoundaryChart_source]
    exact Classical.choose_spec (exists_mem_coordinateSimplexBoundaryChartSource
      (realizationStandardSuccSimplexBoundaryHomeomorphCoordinateSimplex n x))
  chart_mem_atlas _ := mem_range_self _

/-- The atlas consists exactly of the prescribed vertex charts. -/
@[simp] theorem simplexBoundaryPLChartedSpace_atlas (n : ℕ) :
    @atlas (Fin n → ℝ) _ (Realization (standardSuccSimplexBoundary n)) _
      (simplexBoundaryPLChartedSpace n) = range (simplexBoundaryPLChart n) := (rfl)

/-- The weak realization of the boundary of the standard `(n + 1)`-simplex is a PL
`n`-manifold, with the affine barycentric vertex atlas. -/
theorem realizationStandardSuccSimplexBoundary_hasGroupoid (n : ℕ) :
    letI := simplexBoundaryPLChartedSpace n
    HasGroupoid (Realization (standardSuccSimplexBoundary n)) (PLGroupoid 𝓘(ℝ, Fin n → ℝ)) := by
  let := simplexBoundaryPLChartedSpace n
  constructor
  rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
  rw [mem_PLGroupoid_iff]
  constructor
  · simpa only [mfld_simps] using
      (isPiecewiseAffineOn_simplexBoundaryPLChart_transition n v w).isPLOn
  · simpa only [mfld_simps, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using
      (isPiecewiseAffineOn_simplexBoundaryPLChart_transition n w v).isPLOn

end AbstractSimplicialComplex
