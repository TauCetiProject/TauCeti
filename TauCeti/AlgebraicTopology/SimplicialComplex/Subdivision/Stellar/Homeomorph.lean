/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Stellar subdivisions preserve the weak polyhedron

Placing a new vertex at the barycenter of the starred face gives a homeomorphism from the
polyhedron of a stellar subdivision to the original polyhedron. Consequently a finite sequence of
stellar moves and inverse moves preserves the homeomorphism type of a polyhedron. These
identifications provide the topological part of the local sphere and ball models used in
triangulated manifolds; piecewise-linear regularity is a separate assertion.

No finiteness or local-finiteness hypothesis is needed, and the topology is the weak topology
throughout. For a complex that is not locally finite this differs from the coordinate topology,
so the homeomorphism is not obtained by transporting coordinates: continuity in each direction is
tested on closed simplices, each of which lies in a finite part of the complex.

A precomplex can omit vertices, so its polyhedron is the subset of an ambient weak realization
whose supports are its faces. The single-move theorem allows any ambient complex containing
both precomplexes. The sequence theorem uses the full complex as a common ambient space.

Applied to the closed star of a nonempty face, starred at a vertex fresh for that closed star,
the homeomorphism exhibits the closed star as a simplicial cone on its barycentre
(`exists_homeomorph_stellarSubdivision_closedStar`). The starred closed star is a cone with
apex the new vertex (`isCone_stellarSubdivision_closedStar`), and the apex maps to the face
barycentre (`AbstractSimplicialComplex.stellarSubdivisionLinearMap_single_eq_faceBarycenter`).
The open apex star corresponds to the points whose carriers contain the face. The cone link,
identified combinatorially with `closedStar K σ ⊓ deletion K σ` by
`link_stellarSubdivision_closedStar_singleton`, corresponds to the part of the closed star
avoiding the face and is fixed pointwise. This boundary is the base of the cone, not the
ambient topological frontier. The closed star is a neighbourhood of the open apex star relative
to the polyhedron of the original precomplex (`setOf_support_mem_closedStar_mem_nhds`, in
`Realization.Star.Basic`), but it need not be one in the ambient weak realization.

The construction uses the bijective barycentric map of `Stellar.Realization`, the closed-simplex
continuity criterion of `Realization.Subcomplex`, and, on finite parts, the compact subpolyhedron
and coordinate-embedding theorems of `Realization.Finite`. Intrinsic stellar equivalences are
transported through the relabeling homeomorphisms from `Realization.Relabel`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 2 (starrings, stellar equivalence and conical neighbourhoods).
-/

public section

noncomputable section

open Set Topology AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- The finite case of `exists_homeomorph_stellarSubdivision`: both polyhedra are compact,
so the continuous barycentric bijection is a homeomorphism. -/
private theorem exists_homeomorph_stellarSubdivision_of_finite (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ K)
    (hfin : K.faces.Finite) (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision K σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ K},
      ∀ x, (e x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 := by
  classical
  let S := {x : Realization A | x.1.support ∈ stellarSubdivision K σ v}
  let T := {x : Realization A | x.1.support ∈ K}
  have hcompactS : IsCompact S := A.isCompact_setOf_support_mem hS
    (finite_faces_stellarSubdivision hfin)
  have hcompactT : IsCompact T := A.isCompact_setOf_support_mem hK hfin
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcompactS
  have hsource (x : S) :
      x.1.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (stellarSubdivision K σ v)).space :=
    Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
      ⟨Realization.nonneg A x.1, Realization.sum_eq_one A x.1, x.2⟩
  -- Convert normalized coordinates in either precomplex into the containing realization.
  have hmem (P : PreAbstractSimplicialComplex ι) (hP : P ≤ A.toPreAbstractSimplicialComplex)
      (y : ι →₀ ℝ) (hy : y ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) P).space) :
      y ∈ (standardGeometricComplex A).space ∧ y.support ∈ P := by
    obtain ⟨h₁, h₂, h₃⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy
    exact ⟨TauCeti.mem_standardGeometricComplex_space_iff.mpr ⟨h₁, h₂, hP h₃⟩, h₃⟩
  have hb := bijOn_stellarSubdivisionLinearMap hσ hv
  let f : S → T := fun x =>
    ⟨⟨Finset.stellarSubdivisionLinearMap σ v x.1.1,
      (hmem K hK _ (hb.mapsTo (hsource x))).1⟩,
      (hmem K hK _ (hb.mapsTo (hsource x))).2⟩
  have hfval (x : S) : (f x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 :=
    rfl
  -- Restrict the existing point-set bijection to these two subpolyhedra.
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply hb.injOn (hsource x) (hsource y)
      simpa only [hfval] using congrArg (fun z : T => z.1.1) hxy
    · intro y
      have hy := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
        ⟨Realization.nonneg A y.1, Realization.sum_eq_one A y.1, y.2⟩
      obtain ⟨x, hx, hxy⟩ := hb.surjOn hy
      obtain ⟨hxA, hxface⟩ := hmem _ hS x hx
      refine ⟨⟨⟨x, hxA⟩, hxface⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (hfval _).trans hxy
  -- Compact subpolyhedra carry their coordinate topology. Every output coordinate is an
  -- affine expression in two input coordinates, so the restricted barycentric map is continuous.
  have hc : Continuous f := by
    apply (A.isClosedEmbedding_realization_coe_restrict hcompactT).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro i
    have hcoord (j : ι) : Continuous (fun x : S => x.1.1 j) :=
      ((continuous_apply j).comp (continuous_realization_coe A)).comp continuous_subtype_val
    simp only [Function.comp_def, hfval, Finset.stellarSubdivisionLinearMap_apply]
    exact (hcoord i).add ((hcoord v).mul continuous_const)
  let e := (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed hc hc.isClosedMap
  exact ⟨e, hfval⟩

/-- The barycentric identification of a stellar subdivision is a homeomorphism for the weak
subpolyhedron topologies. The new vertex goes to the barycenter of `σ` and the old vertices are
fixed, as specified by the underlying linear map. The complex may be infinite and need not be
locally finite. -/
theorem exists_homeomorph_stellarSubdivision (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision K σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ K},
      ∀ x, (e x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 := by
  classical
  -- Continuity in each direction is tested on closed simplices. A closed simplex of either
  -- complex lies in the finite part of `K` on its vertices together with `σ`, where the
  -- compactness argument of the finite case gives a homeomorphism agreeing with the global map.
  -- The finite part of `K` on the vertices of a finite set `W ⊇ σ`, and its starring.
  have hsub (W : Finset ι) : K ⊓ simplex W ≤ K := inf_le_left
  have hsubS (W : Finset ι) :
      stellarSubdivision (K ⊓ simplex W) σ v ≤ stellarSubdivision K σ v :=
    stellarSubdivision_mono (hsub W)
  have hlocal (W : Finset ι) (hW : σ ⊆ W) :
      ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision (K ⊓ simplex W) σ v} ≃ₜ
          {x : Realization A // x.1.support ∈ K ⊓ simplex W},
        ∀ x, (e x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 :=
    exists_homeomorph_stellarSubdivision_of_finite
      (mem_inf.mpr ⟨hσ, mem_simplex.mpr ⟨(K.isRelLowerSet_faces hσ).1, hW⟩⟩)
      (fun h => hv (mem_inf.mp h).1)
      ((finite_faces_simplex W).subset fun _ hτ => (mem_inf.mp hτ).2)
      ((hsub W).trans hK) ((hsubS W).trans hS)
  choose e he using hlocal
  -- The global barycentric bijection.
  have hb := bijOn_stellarSubdivisionLinearMap hσ hv
  have hspace (P : PreAbstractSimplicialComplex ι) (x : {x : Realization A // x.1.support ∈ P}) :
      x.1.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) P).space :=
    Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
      ⟨Realization.nonneg A x.1, Realization.sum_eq_one A x.1, x.2⟩
  have hmem (y : ι →₀ ℝ) (hy : y ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      y ∈ (standardGeometricComplex A).space ∧ y.support ∈ K := by
    obtain ⟨h₁, h₂, h₃⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy
    exact ⟨TauCeti.mem_standardGeometricComplex_space_iff.mpr ⟨h₁, h₂, hK h₃⟩, h₃⟩
  let f : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v} →
      {x : Realization A // x.1.support ∈ K} := fun x =>
    ⟨⟨Finset.stellarSubdivisionLinearMap σ v x.1.1, (hmem _ (hb.mapsTo (hspace _ x))).1⟩,
      (hmem _ (hb.mapsTo (hspace _ x))).2⟩
  have hfval (x : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v}) :
      (f x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 := rfl
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (Subtype.ext (hb.injOn (hspace _ x) (hspace _ y)
      (by simpa only [hfval] using congrArg (fun z => z.1.1) hxy)))
  -- On each finite part, `f` agrees with the finite homeomorphism.
  have hcompat (W : Finset ι) (hW : σ ⊆ W)
      (x : {x : Realization A // x.1.support ∈ stellarSubdivision (K ⊓ simplex W) σ v}) :
      f ⟨x.1, hsubS W x.2⟩ = ⟨(e W hW x).1, (mem_inf.mp (e W hW x).2).1⟩ :=
    Subtype.ext (Subtype.ext (he W hW x).symm)
  have hsurj : Function.Surjective f := by
    intro y
    have hW : σ ⊆ y.1.1.support ∪ σ := Finset.subset_union_right
    let y' : {x : Realization A // x.1.support ∈ K ⊓ simplex (y.1.1.support ∪ σ)} :=
      ⟨y.1, mem_inf.mpr ⟨y.2, mem_simplex.mpr ⟨(K.isRelLowerSet_faces y.2).1,
        Finset.subset_union_left⟩⟩⟩
    refine ⟨⟨((e _ hW).symm y').1, hsubS _ ((e _ hW).symm y').2⟩, ?_⟩
    rw [hcompat _ hW, Homeomorph.apply_symm_apply]
  let F := Equiv.ofBijective f ⟨hinj, hsurj⟩
  -- Each closed simplex of `K` lies in the finite part spanned by its vertices and `σ`.
  have hsimplex (τ W : Finset ι) (hτ : τ ∈ K) (hτW : τ ⊆ W) : τ ∈ K ⊓ simplex W :=
    mem_inf.mpr ⟨hτ, mem_simplex.mpr ⟨(K.isRelLowerSet_faces hτ).1, hτW⟩⟩
  have hincT (W : Finset ι) :
      Continuous fun y : {x : Realization A // x.1.support ∈ K ⊓ simplex W} =>
        (⟨y.1, (mem_inf.mp y.2).1⟩ : {x : Realization A // x.1.support ∈ K}) :=
    continuous_subtype_val.subtype_mk _
  have hincS (W : Finset ι) :
      Continuous fun y : {x : Realization A //
          x.1.support ∈ stellarSubdivision (K ⊓ simplex W) σ v} =>
        (⟨y.1, hsubS W y.2⟩ : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v}) :=
    continuous_subtype_val.subtype_mk _
  have hcont : Continuous f := by
    refine (continuous_subtype_iff_faceInclusion hS).mpr fun τ hτ => ?_
    have hW : σ ⊆ τ.erase v ∪ σ := Finset.subset_union_right
    -- A stellar simplex is a stellar simplex of the finite part on `τ.erase v ∪ σ`.
    have hτW : τ ∈ stellarSubdivision (K ⊓ simplex (τ.erase v ∪ σ)) σ v := by
      rcases mem_stellarSubdivision_iff.mp hτ with ⟨hvτ, hτK, hστ⟩ | ⟨hvτ, hστ, hτK⟩
      · refine mem_stellarSubdivision_iff.mpr (Or.inl ⟨hvτ, hsimplex _ _ hτK ?_, hστ⟩)
        rw [Finset.erase_eq_of_notMem hvτ]
        exact Finset.subset_union_left
      · exact mem_stellarSubdivision_iff.mpr
          (Or.inr ⟨hvτ, hστ, hsimplex _ _ hτK Finset.Subset.rfl⟩)
    have hSW := (hsubS (τ.erase v ∪ σ)).trans hS
    refine ((hincT _).comp ((e _ hW).continuous.comp
      ((continuous_faceInclusion A ⟨τ, hSW hτW⟩).subtype_mk
        (support_faceInclusion_mem hSW hτW)))).congr fun x => ?_
    exact (hcompat _ hW _).symm
  have hcontSymm : Continuous F.symm := by
    refine (continuous_subtype_iff_faceInclusion hK).mpr fun ρ hρ => ?_
    have hW : σ ⊆ ρ ∪ σ := Finset.subset_union_right
    have hρW : ρ ∈ K ⊓ simplex (ρ ∪ σ) := hsimplex _ _ hρ Finset.subset_union_left
    have hKW := (hsub (ρ ∪ σ)).trans hK
    refine ((hincS _).comp ((e _ hW).symm.continuous.comp
      ((continuous_faceInclusion A ⟨ρ, hKW hρW⟩).subtype_mk
        (support_faceInclusion_mem hKW hρW)))).congr fun x => ?_
    refine (F.symm_apply_eq.mpr ((hcompat _ hW _).trans (Subtype.ext ?_)).symm).symm
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  exact ⟨{ toEquiv := F, continuous_toFun := hcont, continuous_invFun := hcontSymm }, hfval⟩

/-- The starred closed star of a face is identified with the original closed star in the weak
topology. This starred complex is a simplicial cone with apex the new vertex
(`isCone_stellarSubdivision_closedStar`), and the cone apex maps by the barycentric stellar map
to the face barycentre. The open apex star maps exactly to carriers containing the face; the
cone link maps to the boundary subpolyhedron, and that boundary is fixed pointwise. The
containing realization may have arbitrary unused vertices. -/
theorem exists_homeomorph_stellarSubdivision_closedStar (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ closedStar K σ)
    (hK : closedStar K σ ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision (closedStar K σ) σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision (closedStar K σ) σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ closedStar K σ},
      (∀ x, (e x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1) ∧
      (∀ x, 0 < x.1.1 v ↔ σ ⊆ (e x).1.1.support) ∧
      (∀ x, x.1.1.support ∈ link (stellarSubdivision (closedStar K σ) σ v) {v} ↔
        (e x).1.1.support ∈ deletion K σ) ∧
      (∀ x, x.1.1.support ∈ link (stellarSubdivision (closedStar K σ) σ v) {v} →
        (e x).1 = x.1) := by
  have hσstar : σ ∈ closedStar K σ := by simp [hσ]
  have hcone := isCone_stellarSubdivision_closedStar (v := v) hσ
  obtain ⟨e, he⟩ := exists_homeomorph_stellarSubdivision hσstar hv hK hS
  have hopen (x) : 0 < x.1.1 v ↔ σ ⊆ (e x).1.1.support := by
    rw [he]
    exact (subset_support_stellarSubdivisionLinearMap_iff (Realization.nonneg A x.1) x.2).symm
  have hzero (x : {x : Realization A // x.1.support ∈ stellarSubdivision (closedStar K σ) σ v}) :
      x.1.1 v = 0 ↔ (e x).1.1.support ∈ deletion K σ := by
    rw [mem_deletion]
    have hface := closedStar_le (e x).2
    have hnonneg := Realization.nonneg A x.1 v
    rw [← hopen]
    exact ⟨fun hz => ⟨hface, by linarith⟩, fun h => by linarith [h.2]⟩
  refine ⟨e, he, hopen, ?_, ?_⟩
  · intro x
    rw [mem_link, Finset.disjoint_singleton_right, Finsupp.notMem_support_iff]
    have hinsert := hcone.insert_mem x.2
    simpa only [x.2, true_and, Finset.union_singleton, hinsert, and_true] using hzero x
  · intro x hx
    have hxv : x.1.1 v = 0 := Finsupp.notMem_support_iff.mp
      (Finset.disjoint_singleton_right.mp (mem_link.mp hx).2.1)
    apply Subtype.ext
    rw [he]
    ext i
    simp [Finset.stellarSubdivisionLinearMap_apply, hxv]

/-- Stellar equivalent precomplexes have homeomorphic weak polyhedra. The subtypes exclude every
unused vertex, even though their common ambient complex contains all vertices. -/
theorem StellarEquivalent.nonempty_homeomorph (h : StellarEquivalent K L) :
    Nonempty ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L}) := by
  have hle (P : PreAbstractSimplicialComplex ι) :
      P ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex :=
    fun _ hτ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (P.isRelLowerSet_faces.prop_of_mem hτ)
  refine h.induction_on (P := fun A B => Nonempty
      ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
        {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ B}))
    (fun P Q hPQ => ?_) (fun _ => ⟨Homeomorph.refl _⟩)
    (fun _ _ ⟨e⟩ => ⟨e.symm⟩) (fun _ _ _ ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩)
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hPQ
  obtain ⟨e, -⟩ := exists_homeomorph_stellarSubdivision hσ hv (hle P) (hle _)
  exact ⟨e.symm⟩

private noncomputable def topRelabelingHomeomorph {κ : Type*} [DecidableEq κ]
    (P : PreAbstractSimplicialComplex ι) (f : ι ↪ κ) :
    {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ P} ≃ₜ
      {y : Realization (⊤ : AbstractSimplicialComplex κ) // y.1.support ∈ P.map f} :=
  P.relabelingHomeomorph f
    (fun _ hτ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (P.isRelLowerSet_faces.prop_of_mem hτ))
    (fun _ hτ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (P.map f |>.isRelLowerSet_faces.prop_of_mem hτ))

/-- Intrinsic stellar equivalence gives homeomorphic weak polyhedra even when the two complexes
use different vertex labels. The two relabelings in the definition are removed by the canonical
homeomorphisms of `Realization.Relabel`. -/
theorem StellarEquivalentUpToRelabeling.nonempty_homeomorph
    (h : StellarEquivalentUpToRelabeling K L) :
    Nonempty ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L}) := by
  refine h.induction_on (P := fun A B => Nonempty
      ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
        {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ B}))
    (fun P Q f g he => ?_) (fun _ => ⟨Homeomorph.refl _⟩)
    (fun _ _ ⟨e⟩ => ⟨e.symm⟩) (fun _ _ _ ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩)
  obtain ⟨e⟩ := he.nonempty_homeomorph
  exact ⟨(topRelabelingHomeomorph P f).trans (e.trans (topRelabelingHomeomorph Q g).symm)⟩

end PreAbstractSimplicialComplex
