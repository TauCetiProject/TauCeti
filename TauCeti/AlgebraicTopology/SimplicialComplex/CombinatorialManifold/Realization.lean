/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Star
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.PL
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.PL
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic

/-!
# Geometric balls and spheres from combinatorial complexes

The weak polyhedron of a combinatorial `n`-ball or `n`-sphere is PL-homeomorphic to its standard
simplicial model and homeomorphic to the Euclidean closed ball or unit sphere. The ball result
identifies the closed vertex stars used to construct manifold charts, while the sphere result
identifies the spherical links at interior vertices. The topological results concern the actual
subpolyhedron of an arbitrary ambient realization, so unused ambient vertices contribute no extra
points.

Intrinsic stellar equivalence supplies the PL homeomorphism to a simplex or simplex boundary, and
injective relabeling replaces its arbitrary finite vertex labels by canonical `Fin` labels while
preserving ambient PL coordinate formulas. The standard models then supply the Euclidean closed
ball or sphere. No finiteness assumption on the ambient complex or its vertex type is required;
finiteness follows from the combinatorial ball or sphere hypothesis.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (stellar equivalence and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {P : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {n : ℕ}

/-! ### PL standard models -/

/-- A combinatorial ball is PL-homeomorphic to a simplex of the prescribed dimension. -/
theorem IsCombinatorialBall.exists_plHomeomorphic_simplex
    [DecidableEq ι] (h : IsCombinatorialBall P n) :
    ∃ V : Finset ι, V.card = n + 1 ∧ PLHomeomorphic P (simplex V) := by
  have hfin := h.finite_faces
  obtain ⟨V, hV, hPV⟩ := isCombinatorialBall_iff.mp h
  exact ⟨V, hV, hPV.plHomeomorphic hfin⟩

/-- A combinatorial sphere is PL-homeomorphic to the boundary of a simplex of the prescribed
dimension. -/
theorem IsCombinatorialSphere.exists_plHomeomorphic_simplexBoundary
    [DecidableEq ι] (h : IsCombinatorialSphere P n) :
    ∃ V : Finset ι, V.card = n + 2 ∧ PLHomeomorphic P (simplexBoundary V) := by
  have hfin := h.finite_faces
  obtain ⟨V, hV, hPV⟩ := isCombinatorialSphere_iff.mp h
  exact ⟨V, hV, hPV.plHomeomorphic hfin⟩

/-- A combinatorial ball has the PL homeomorphism type of the simplex on a canonical finite
vertex type. This removes the arbitrary labels from `exists_plHomeomorphic_simplex`, which is
useful when transporting the standard simplex charts. -/
theorem IsCombinatorialBall.plHomeomorphic_standardSimplex
    [DecidableEq ι] (h : IsCombinatorialBall P n) :
    PLHomeomorphic P (simplex (Finset.univ : Finset (Fin (n + 1)))) := by
  obtain ⟨V, hV, hP⟩ := h.exists_plHomeomorphic_simplex
  let e : V ≃ Fin (n + 1) := Finset.equivFinOfCardEq hV
  let j : V ↪ ι := Function.Embedding.subtype (· ∈ V)
  let S : PreAbstractSimplicialComplex V := simplex Finset.univ
  have hj : S.map j = simplex V := by
    simp only [S, map_simplex]
    congr 1
    ext v
    simp [j]
  have he : S.map e.toEmbedding = simplex (Finset.univ : Finset (Fin (n + 1))) := by
    simp only [S, map_simplex]
    congr 1
    exact Finset.image_univ_equiv e
  have hleft : PLHomeomorphic (simplex V) S := by
    rw [← hj]
    exact (PLHomeomorphic.relabeling S j).symm
  have hright : PLHomeomorphic S (simplex (Finset.univ : Finset (Fin (n + 1)))) := by
    rw [← he]
    exact PLHomeomorphic.relabeling S e.toEmbedding
  exact hP.trans (hleft.trans hright)

/-- A combinatorial sphere has the PL homeomorphism type of the boundary of the simplex on a
canonical finite vertex type. This is the standard link model used by PL vertex charts. -/
theorem IsCombinatorialSphere.plHomeomorphic_standardSimplexBoundary
    [DecidableEq ι] (h : IsCombinatorialSphere P n) :
    PLHomeomorphic P (simplexBoundary (Finset.univ : Finset (Fin (n + 2)))) := by
  obtain ⟨V, hV, hP⟩ := h.exists_plHomeomorphic_simplexBoundary
  let e : V ≃ Fin (n + 2) := Finset.equivFinOfCardEq hV
  let j : V ↪ ι := Function.Embedding.subtype (· ∈ V)
  let S : PreAbstractSimplicialComplex V := simplexBoundary Finset.univ
  have hj : S.map j = simplexBoundary V := by
    simp only [S, map_simplexBoundary]
    congr 1
    ext v
    simp [j]
  have he : S.map e.toEmbedding =
      simplexBoundary (Finset.univ : Finset (Fin (n + 2))) := by
    simp only [S, map_simplexBoundary]
    congr 1
    exact Finset.image_univ_equiv e
  have hleft : PLHomeomorphic (simplexBoundary V) S := by
    rw [← hj]
    exact (PLHomeomorphic.relabeling S j).symm
  have hright : PLHomeomorphic S
      (simplexBoundary (Finset.univ : Finset (Fin (n + 2)))) := by
    rw [← he]
    exact PLHomeomorphic.relabeling S e.toEmbedding
  exact hP.trans (hleft.trans hright)

/-- A combinatorial ball has a PL homeomorphism to the realization of the standard simplex,
with ambient PL coordinate formulas in both directions. -/
theorem IsCombinatorialBall.exists_homeomorph_standardSimplex
    [DecidableEq ι] (h : IsCombinatorialBall P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ P} ≃ₜ
        Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))),
      ∃ f : (ι → ℝ) → (Fin (n + 1) → ℝ), ∃ g : (Fin (n + 1) → ℝ) → (ι → ℝ),
        TauCeti.IsPLOn f (Set.range fun x : {x : Realization A // x.1.support ∈ P} =>
          (x.1.1 : ι → ℝ)) ∧
        TauCeti.IsPLOn g (Set.range fun y :
          Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) =>
            (y.1 : Fin (n + 1) → ℝ)) ∧
        (∀ x, f (x.1.1 : ι → ℝ) = (e x).1) ∧
        ∀ y, g (y.1 : Fin (n + 1) → ℝ) = (e.symm y).1.1 := by
  have hPL := h.plHomeomorphic_standardSimplex
  rw [simplex_univ, ← top_toPreAbstractSimplicialComplex] at hPL
  exact hPL.exists_homeomorph_realization hA

/-- A combinatorial sphere has a PL homeomorphism to the realization of the standard simplex
boundary, with ambient PL coordinate formulas in both directions. -/
theorem IsCombinatorialSphere.exists_homeomorph_standardSimplexBoundary
    [DecidableEq ι] (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ P} ≃ₜ
        Realization (standardSuccSimplexBoundary n),
      ∃ f : (ι → ℝ) → (Fin (n + 2) → ℝ), ∃ g : (Fin (n + 2) → ℝ) → (ι → ℝ),
        TauCeti.IsPLOn f (Set.range fun x : {x : Realization A // x.1.support ∈ P} =>
          (x.1.1 : ι → ℝ)) ∧
        TauCeti.IsPLOn g (Set.range fun y : Realization (standardSuccSimplexBoundary n) =>
          (y.1 : Fin (n + 2) → ℝ)) ∧
        (∀ x, f (x.1.1 : ι → ℝ) = (e x).1) ∧
        ∀ y, g (y.1 : Fin (n + 2) → ℝ) = (e.symm y).1.1 := by
  have hPL := h.plHomeomorphic_standardSimplexBoundary
  rw [← standardSuccSimplexBoundary_toPreAbstractSimplicialComplex] at hPL
  exact hPL.exists_homeomorph_realization hA

/-! ### Topological standard models -/

/-- A combinatorial `n`-ball has a weak polyhedron homeomorphic to the Euclidean closed `n`-ball.

The ambient complex may contain unused vertices. They are removed by the weak-polyhedron subtype. -/
theorem IsCombinatorialBall.nonempty_homeomorph_closedBall
    [DecidableEq ι] (h : IsCombinatorialBall P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplex_closedBall hV (le_top _)
  exact ⟨(topRealizationHomeomorph P hA).symm.trans (s.trans t)⟩

/-- A combinatorial `n`-sphere has a weak polyhedron homeomorphic to the unit `n`-sphere,
inside any ambient realization containing it. This includes the two-point zero-sphere. -/
theorem IsCombinatorialSphere.nonempty_homeomorph_sphere [DecidableEq ι]
    (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  classical
  let r := topRealizationHomeomorph P hA
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplexBoundary_sphere hV (le_top _)
  exact ⟨r.symm.trans (s.trans t)⟩

/-! ### Vertex-star ball models -/

/-- The weak polyhedron of a vertex's closed star in a combinatorial `n`-manifold is homeomorphic
to the Euclidean closed `n`-ball, providing the local closed-ball model for its vertex charts.

The statement uses the weak realization topology and allows an arbitrary ambient vertex type;
unused ambient vertices contribute no points. -/
theorem IsCombinatorialManifold.nonempty_homeomorph_closedStar_closedBall
    [DecidableEq ι] (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex n)
    {v : ι} (hv : ({v} : Finset ι) ∈ K) :
    Nonempty (closedStarRealization K {v} ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let P : PreAbstractSimplicialComplex ι :=
    closedStar K.toPreAbstractSimplicialComplex {v}
  let e : ι ↪ ι ⊕ ι := TauCeti.partitionEmbedding (· ∈ ({v} : Finset ι))
  let L : AbstractSimplicialComplex (ι ⊕ ι) := ⊤
  have hP : P.map e ≤ L.toPreAbstractSimplicialComplex := le_top _
  have hball : IsCombinatorialBall (P.map e) n := by
    simpa only [P, e] using h.isCombinatorialBall_map_closedStar hv
  obtain ⟨b⟩ := hball.nonempty_homeomorph_closedBall hP
  let r := P.relabelingHomeomorph e (PreAbstractSimplicialComplex.closedStar_le) hP
  have hset : (K.closedStarRealization {v} : Set (Realization K)) =
      {x : Realization K | x.1.support ∈ P} := by
    ext x
    simp only [P, mem_closedStarRealization, Set.mem_ofPred_eq]
  exact ⟨(Homeomorph.setCongr hset).trans (r.trans b)⟩

end PreAbstractSimplicialComplex
