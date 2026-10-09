/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere

/-!
# Geometric balls and spheres from combinatorial complexes

The weak polyhedron of a combinatorial `n`-ball or `n`-sphere is homeomorphic to the Euclidean
closed ball or unit sphere. The ball result identifies the closed vertex stars used to construct
manifold charts, while the sphere result identifies the spherical links at interior vertices. Both
results concern the actual subpolyhedron of an arbitrary ambient realization, so unused ambient
vertices contribute no extra points.

Intrinsic stellar equivalence supplies the homeomorphism to a simplex or simplex boundary, and the
standard models supply the Euclidean closed ball or sphere. Injective relabeling changes the
ambient realization without changing the topology of the polyhedron. No finiteness assumption on
the ambient complex or its vertex type is required; finiteness follows from the combinatorial
ball or sphere hypothesis.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (stellar equivalence and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {P : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {n : ℕ}

private theorem nonempty_homeomorph_simplex_closedBall {V : Finset ι}
    (hV : V.card = n + 1) (hA : simplex V ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ simplex V} ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  let e := (Finset.equivFinOfCardEq hV).symm
  let f : Fin (n + 1) ↪ ι := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ V))
  have himage : (Finset.univ : Finset (Fin (n + 1))).image f = V := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hv
      exact ⟨e.symm ⟨v, hv⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  let P := simplex (Finset.univ : Finset (Fin (n + 1)))
  have hP : P = (⊤ : AbstractSimplicialComplex (Fin (n + 1))).toPreAbstractSimplicialComplex := by
    change simplex (Finset.univ : Finset (Fin (n + 1))) = _
    rw [simplex_univ, AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
  have hmap : P.map f = simplex V := by
    ext σ
    rw [PreAbstractSimplicialComplex.faces_map]
    change (∃ τ, τ ∈ P ∧ Finset.image f τ = σ) ↔ σ ∈ simplex V
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      have hτ' := PreAbstractSimplicialComplex.mem_simplex.mp hτ
      apply PreAbstractSimplicialComplex.mem_simplex.mpr
      exact ⟨hτ'.1.image f, by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
        rw [← hxy]
        simp [f]⟩
    · intro hσ
      obtain ⟨hne, hsub⟩ := PreAbstractSimplicialComplex.mem_simplex.mp hσ
      have hsub' : σ ⊆ Finset.image f Finset.univ := by simpa [himage] using hsub
      obtain ⟨τ, hτ, hτf⟩ := Finset.subset_image_iff.mp hsub'
      have hτne : τ.Nonempty := by
        by_contra hτempty
        have hτzero : τ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hτempty
        subst τ
        have hσzero : σ = ∅ := by simpa using hτf.symm
        simp [hσzero] at hne
      exact ⟨τ, PreAbstractSimplicialComplex.mem_simplex.mpr ⟨hτne, hτ⟩, hτf⟩
  let r := P.relabelingHomeomorph f hP.le (by rw [hmap]; exact hA)
  let s : {x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) // x.1.support ∈ P} ≃ₜ
      Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) :=
    (Homeomorph.setCongr (Set.eq_univ_of_forall fun x => by
      rw [hP]
      exact AbstractSimplicialComplex.support_mem _ x)).trans
      (Homeomorph.Set.univ _)
  exact ⟨(Homeomorph.setCongr (by rw [hmap])).trans
    (r.symm.trans (s.trans (AbstractSimplicialComplex.realizationTopHomeomorphClosedBall n)))⟩

/-- A combinatorial `n`-ball has a weak polyhedron homeomorphic to the Euclidean closed `n`-ball.

The ambient complex may contain unused vertices. They are removed by the weak-polyhedron subtype;
the proof then transports the standard-simplex model across relabeling and stellar moves. -/
theorem IsCombinatorialBall.nonempty_homeomorph_closedBall
    [DecidableEq ι] (h : IsCombinatorialBall P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplex_closedBall hV (by
    exact fun _ hσ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      ((simplex V).isRelLowerSet_faces.prop_of_mem hσ))
  have htop (Q : PreAbstractSimplicialComplex ι) :
      Q ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex :=
    fun _ hσ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (Q.isRelLowerSet_faces.prop_of_mem hσ)
  have r : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ P} ≃ₜ
      {x : Realization A // x.1.support ∈ P} := by
    have hid : P.map (Function.Embedding.refl ι) = P := by
      simpa only [Function.Embedding.coe_refl] using (map_id (K := P))
    exact (P.relabelingHomeomorph (Function.Embedding.refl ι) (htop P)
      (by rw [hid]; exact hA)).trans
      (Homeomorph.setCongr (by rw [hid]))
  exact ⟨r.symm.trans (s.trans t)⟩

/-- A combinatorial `n`-sphere has a weak polyhedron homeomorphic to the unit `n`-sphere,
inside any ambient realization containing it. This includes the two-point zero-sphere. -/
theorem IsCombinatorialSphere.nonempty_homeomorph_sphere [DecidableEq ι]
    (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  classical
  have htop (Q : PreAbstractSimplicialComplex ι) :
      Q ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex :=
    fun _ hσ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (Q.isRelLowerSet_faces.prop_of_mem hσ)
  have r : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ P} ≃ₜ
      {x : Realization A // x.1.support ∈ P} := by
    have hid : P.map (Function.Embedding.refl ι) = P := by
      simpa only [Function.Embedding.coe_refl] using (map_id (K := P))
    exact (P.relabelingHomeomorph (Function.Embedding.refl ι) (htop P)
      (by rw [hid]; exact hA)).trans
      (Homeomorph.setCongr (by rw [hid]))
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplexBoundary_sphere hV (htop _)
  exact ⟨r.symm.trans (s.trans t)⟩

end PreAbstractSimplicialComplex
