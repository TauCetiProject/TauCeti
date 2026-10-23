/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL.Simplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.PL.Ball

/-!
# PL half-space charts at vertices with ball links

A vertex with a combinatorial `n`-ball as link has a chart on its entire open star,
modelled on the half-space in `(Fin n → ℝ) × ℝ`. Both directions have ambient PL
coordinate formulas. The vertex maps to zero on the boundary of the half-space.

The closed-star simplex identification carries the vertex to the last simplex vertex.
Restricting the standard simplex chart at that vertex therefore gives a chart on the
open star, including all its boundary points. These are the boundary charts needed to
pass from combinatorial manifolds to chart-based PL manifolds.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapters 2–3 (polyhedral charts and combinatorial manifolds).
-/

public noncomputable section

open AbstractSimplicialComplex Set TauCeti Topology
open scoped Manifold

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

/-- A closed-star identification carrying the open star onto the source of a model chart
restricts to an actual chart of the ambient weak realization. -/
private theorem exists_chart_of_closedStar
    {H : Type*} [TopologicalSpace H] [Nonempty H]
    (φ : closedStarRealization K {v} ≃ₜ
      Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))))
    (a : OpenPartialHomeomorph
      (Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) H)
    (hs : ∀ x : closedStarRealization K {v},
      φ x ∈ a.source ↔ x.1 ∈ openStarRealization K v) :
    ∃ c : OpenPartialHomeomorph (Realization K) H,
      c.source = openStarRealization K v ∧ c.target = a.target ∧
      (∀ x : openStarRealization K v,
        c x.1 = a (φ ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩)) ∧
      ∀ y ∈ a.target, c.symm y = (φ.symm (a.symm y)).1 := by
  let e : openStarRealization K v ≃ₜ a.source := {
    toFun x := ⟨φ ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩,
      (hs _).mpr x.2⟩
    invFun y := ⟨(φ.symm y.1).1, (hs _).mp (by simpa only [φ.apply_symm_apply] using y.2)⟩
    left_inv x := by simp
    right_inv y := by simp
    continuous_toFun := (φ.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp
      (φ.symm.continuous.comp continuous_subtype_val)).subtype_mk _ }
  let b := e.trans a.toHomeomorphSourceTarget
  let : Nonempty a.target := ⟨b ⟨vertex K v, by simp [vertex_val]⟩⟩
  let t := a.open_target.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : a.target → H)
  let c := (b.toOpenPartialHomeomorph.trans t).lift_openEmbedding
    (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [c, t]
  · simp [c, t]
  · intro x
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    simp [b, t, e]
  · intro y hy
    simp only [c, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply]
    have ht : t.symm y = (⟨y, hy⟩ : a.target) :=
      Subtype.ext (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (Subtype.val : a.target → H) a.open_target.isOpenEmbedding_subtypeVal
        ⟨⟨y, hy⟩, rfl⟩)
    rw [ht]
    simp [b, e]

/-- A combinatorial-ball vertex link supplies a PL half-space chart on the entire open
vertex star. Its forward formula is PL on the closed star, and its inverse formula is PL
on the model coordinates of the chart target. The vertex lies at zero in the half-space. -/
theorem IsCombinatorialBall.exists_openPartialHomeomorph_openStar_isPL
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2},
      c.source = openStarRealization K v ∧
      c.target = (simplexHalfSpacePLChart n none).target ∧
      (c (vertex K v)).1 = 0 ∧
      ∃ f : (ι → ℝ) → (Fin n → ℝ) × ℝ,
      ∃ g : ((Fin n → ℝ) × ℝ) → (ι → ℝ),
        IsPLOn f (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn g ((modelWithCornersHalfSpace (Fin n → ℝ)).symm ⁻¹' c.target ∩
          range (modelWithCornersHalfSpace (Fin n → ℝ))) ∧
        (∀ x ∈ c.source, f (x.1 : ι → ℝ) = (c x).1) ∧
        ∀ y ∈ c.target, g y.1 = ((c.symm y).1 : ι → ℝ) := by
  -- Restrict the closed-star simplex model to its last-vertex chart.
  let : Nonempty {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} := ⟨⟨0, by simp⟩⟩
  obtain ⟨φ, hapex, hheight, F, G, hF, hG, hFφ, hGφ⟩ :=
    h.exists_homeomorph_closedStarRealization_top
  let a := simplexHalfSpacePLChart n none
  have hs (x : closedStarRealization K {v}) :
      φ x ∈ a.source ↔ x.1 ∈ openStarRealization K v := by
    simp only [a, simplexHalfSpacePLChart_source, Option.elim_none,
      mem_openStarRealization, hheight]
  obtain ⟨c, hcs, hct, hc, hci⟩ := exists_chart_of_closedStar φ a hs
  -- Compose the old PL formulas with the simplex chart and its ambient inverse.
  let P := simplexBoundaryCoordinateMap n
  let R := simplexBoundaryCoordinateLift n
  let A := coordinateSimplexHalfSpaceMap (ι := Fin n) none
  let f := A ∘ P ∘ F
  let g := G ∘ R ∘ A.symm
  have hg_eq (y : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}) (hy : y ∈ a.target) :
      g y.1 = ((c.symm y).1 : ι → ℝ) := by
    rw [hci y hy]
    simp only [g, Function.comp_apply]
    rw [← coe_simplexHalfSpacePLChart_symm_apply n none hy]
    simpa only [φ.apply_symm_apply] using hGφ (φ.symm (a.symm y))
  refine ⟨c, hcs, hct, ?_, f, g, ?_, ?_, ?_, ?_⟩
  · have hv : vertex K v ∈ openStarRealization K v := by simp [vertex_val]
    rw [hc ⟨vertex K v, hv⟩]
    apply coe_simplexHalfSpacePLChart_none_eq_zero
    have he : (⟨vertex K v, K.openStarRealization_subset_closedStarRealization v hv⟩ :
        closedStarRealization K {v}) = starApex K v := Subtype.ext (starApex_val K v).symm
    rw [he]
    exact hapex
  · exact (isPiecewiseAffineOn_coordinateSimplexHalfSpaceMap none).isPLOn.comp
      ((isPLOn_continuousAffineMap P.toContinuousAffineMap univ).comp hF
        (mapsTo_univ _ _)) (mapsTo_univ _ _)
  · -- Model points in the target are sent back into the actual standard simplex.
    let s := (modelWithCornersHalfSpace (Fin n → ℝ)).symm ⁻¹' c.target ∩
      range (modelWithCornersHalfSpace (Fin n → ℝ))
    have hmap : MapsTo (R ∘ A.symm) s
        (range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
          (y.1 : Fin (n + 2) → ℝ)) := by
      intro z hz
      have hnonneg : 0 ≤ z.2 := by simpa using hz.2
      let y := (modelWithCornersHalfSpace (Fin n → ℝ)).symm z
      have hy : y ∈ a.target := hct ▸ hz.1
      refine ⟨a.symm y, ?_⟩
      simpa only [a, R, A, y, Function.comp_apply,
        coe_modelWithCornersHalfSpace_symm_apply _ hnonneg] using
          coe_simplexHalfSpacePLChart_symm_apply n none hy
    exact hG.comp
      (((isPLOn_continuousAffineMap R univ).comp
        (isPiecewiseAffineOn_coordinateSimplexHalfSpaceMap_symm none).isPLOn
        (mapsTo_univ _ _)).mono (subset_univ _)) hmap
  · intro x hx
    have hx' : x ∈ openStarRealization K v := hcs ▸ hx
    rw [hc ⟨x, hx'⟩, coe_simplexHalfSpacePLChart_apply]
    exact congrArg (fun z => A (P z))
      (hFφ ⟨x, K.openStarRealization_subset_closedStarRealization v hx'⟩)
  · intro y hy
    exact hg_eq y (hct ▸ hy)

end PreAbstractSimplicialComplex
