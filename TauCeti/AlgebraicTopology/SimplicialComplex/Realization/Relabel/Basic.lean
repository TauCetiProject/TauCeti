/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex
public import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Relabeling polyhedra with unused vertices

Injective relabeling of a precomplex induces a homeomorphism of its polyhedron. The polyhedra
carry the subspace topologies of arbitrary ambient weak realizations containing the respective
complexes. Thus the result applies to links and stellar moves, which can omit ambient vertices,
and to embeddings into enlarged vertex types. No finiteness assumption is needed.

The forward map pushes barycentric coordinates along the vertex embedding; its inverse pulls
coordinates back. Continuity is tested on closed simplices using the weak subcomplex topology.
In particular, changing the ambient complex leaves the topology of the actual polyhedron intact.
These identifications transport intrinsic combinatorial sphere and ball models to geometric
link models without adjoining unwanted isolated points.
An explicit enumeration of a face identifies the realization of the full simplex on the
enumerating type with the closed simplex of that face.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (polyhedra and simplicial maps).

The construction uses Mathlib's `Finsupp.lcomapDomain` and the affine simplex maps of
`TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map`.
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {α β : Type*} [DecidableEq β]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}

variable (P : PreAbstractSimplicialComplex α) (f : α ↪ β)
  (hK : P ≤ K.toPreAbstractSimplicialComplex)
  (hL : P.map f ≤ L.toPreAbstractSimplicialComplex)

private def relabelingForward (x : {x : Realization K // x.1.support ∈ P}) :
    {y : Realization L // y.1.support ∈ P.map f} :=
  let σ : Face (P.map f) := ⟨x.1.1.support.image f, mem_map_iff.mpr ⟨_, x.2, rfl⟩⟩
  let z : StandardSimplex x.1.1.support := ⟨x.1.1, by
    simpa only [carrier_val] using mem_convexHull_carrier K x.1⟩
  ⟨faceInclusion L ⟨σ.1, hL σ.2⟩ (StandardSimplex.map z f),
    support_faceInclusion_mem hL σ.2 _⟩

private theorem relabelingForward_val (x : {x : Realization K // x.1.support ∈ P}) :
    (relabelingForward P f hL x).1.1 = Finsupp.mapDomain f x.1.1 := by
  simp only [relabelingForward, faceInclusion_val, StandardSimplex.map_val]

include hK in
private theorem exists_relabelingBackward (y : {y : Realization L // y.1.support ∈ P.map f}) :
    ∃ x : {x : Realization K // x.1.support ∈ P},
      x.1.1 = Finsupp.comapDomain f y.1.1 f.injective.injOn := by
  obtain ⟨σ, hσ, heq⟩ := mem_map_iff.mp y.2
  let z : StandardSimplex (σ.image f) := ⟨y.1.1, by
    rw [heq]
    simpa only [carrier_val] using mem_convexHull_carrier L y.1⟩
  exact ⟨⟨faceInclusion K ⟨σ, hK hσ⟩ (StandardSimplex.comap (f := f) z),
    support_faceInclusion_mem hK hσ _⟩, by
      simp only [faceInclusion_val, StandardSimplex.comap_val]; rfl⟩

private def relabelingBackward (y : {y : Realization L // y.1.support ∈ P.map f}) :
    {x : Realization K // x.1.support ∈ P} :=
  (exists_relabelingBackward P f hK y).choose

private theorem relabelingBackward_val (y : {y : Realization L // y.1.support ∈ P.map f}) :
    (relabelingBackward P f hK y).1.1 = Finsupp.comapDomain f y.1.1 f.injective.injOn :=
  (exists_relabelingBackward P f hK y).choose_spec

include hK in
private theorem continuous_relabelingForward : Continuous (relabelingForward (K := K) P f hL) := by
  apply continuous_subtype_iff_faceInclusion hK |>.mpr
  intro σ hσ
  have hc : Continuous (fun z : StandardSimplex σ =>
      (⟨faceInclusion L ⟨σ.image f, hL (mem_map_iff.mpr ⟨σ, hσ, rfl⟩)⟩
        (StandardSimplex.map z f),
        support_faceInclusion_mem hL (mem_map_iff.mpr ⟨σ, hσ, rfl⟩) _⟩ :
          {y : Realization L // y.1.support ∈ P.map f})) :=
    ((continuous_faceInclusion L ⟨σ.image f,
      hL (mem_map_iff.mpr ⟨σ, hσ, rfl⟩)⟩).comp
      (StandardSimplex.continuous_map f (σ := σ))).subtype_mk
        (fun z => support_faceInclusion_mem hL (mem_map_iff.mpr ⟨σ, hσ, rfl⟩) _)
  convert hc using 1
  funext x
  apply Subtype.ext
  apply Subtype.ext
  simp only [Function.comp_apply, relabelingForward_val, faceInclusion_val,
    StandardSimplex.map_val]

include hL in
private theorem continuous_relabelingBackward :
    Continuous (relabelingBackward (L := L) P f hK) := by
  apply continuous_subtype_iff_faceInclusion hL |>.mpr
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := mem_map_iff.mp hτ
  have hc : Continuous (fun z : StandardSimplex (σ.image f) =>
      (⟨faceInclusion K ⟨σ, hK hσ⟩ (StandardSimplex.comap (f := f) z),
        support_faceInclusion_mem hK hσ _⟩ :
          {x : Realization K // x.1.support ∈ P})) :=
    ((continuous_faceInclusion K ⟨σ, hK hσ⟩).comp
      (StandardSimplex.continuous_comap f (σ := σ))).subtype_mk
        (fun z => support_faceInclusion_mem hK hσ _)
  convert hc using 1
  funext y
  apply Subtype.ext
  apply Subtype.ext
  simp only [Function.comp_apply, relabelingBackward_val, faceInclusion_val,
    StandardSimplex.comap_val]

/-- An injective relabeling identifies the actual polyhedra of a precomplex and its image,
inside any ambient weak realizations containing them. Vertices unused by the precomplex
contribute no points. -/
def relabelingHomeomorph
    (hK : P ≤ K.toPreAbstractSimplicialComplex)
    (hL : P.map f ≤ L.toPreAbstractSimplicialComplex) :
    {x : Realization K // x.1.support ∈ P} ≃ₜ
      {y : Realization L // y.1.support ∈ P.map f} where
  toFun := relabelingForward P f hL
  invFun := relabelingBackward P f hK
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [relabelingBackward_val, relabelingForward_val]
    exact Finsupp.comapDomain_mapDomain f f.injective _
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rw [relabelingForward_val, relabelingBackward_val]
    apply Finsupp.mapDomain_comapDomain f f.injective
    obtain ⟨σ, -, heq⟩ := mem_map_iff.mp y.2
    intro b hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (heq.symm ▸ hb)
    exact mem_range_self a
  continuous_toFun := continuous_relabelingForward P f hK hL
  continuous_invFun := continuous_relabelingBackward P f hK hL

/-- Every precomplex is contained in the top abstract simplicial complex. -/
theorem le_top (Q : PreAbstractSimplicialComplex ι) :
    Q ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex :=
  fun _ hσ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
    (Q.isRelLowerSet_faces.prop_of_mem hσ)

/-- Changing the ambient abstract complex does not change the polyhedron of a precomplex. -/
noncomputable def topRealizationHomeomorph
    (P : PreAbstractSimplicialComplex ι)
    {A : AbstractSimplicialComplex ι}
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ P} ≃ₜ
      {x : Realization A // x.1.support ∈ P} := by
  classical
  have hid : P.map (Function.Embedding.refl ι) = P := by
    simpa only [Function.Embedding.coe_refl] using (map_id (K := P))
  exact (P.relabelingHomeomorph (Function.Embedding.refl ι) (le_top P)
    (by rw [hid]; exact hA)).trans
    (Homeomorph.setCongr
      (s := {x : Realization A | x.1.support ∈ P.map (Function.Embedding.refl ι)})
      (t := {x : Realization A | x.1.support ∈ P}) (by rw [hid]))

/-- An injective relabeling carrying the underlying precomplex of `K` onto `R` identifies the
realization of `K` with the polyhedron of `R`, inside any ambient weak realization containing
`R`. -/
def realizationRelabelingHomeomorph {R : PreAbstractSimplicialComplex β}
    (hmap : P.map f = R) (hP : P = K.toPreAbstractSimplicialComplex)
    (hR : R ≤ L.toPreAbstractSimplicialComplex) :
    Realization K ≃ₜ {y : Realization L // y.1.support ∈ R} :=
  ((Homeomorph.Set.univ _).symm.trans
    (Homeomorph.setCongr (s := Set.univ) (t := {x : Realization K | x.1.support ∈ P})
      (Set.eq_univ_of_forall fun x => by
        rw [hP]
        exact AbstractSimplicialComplex.support_mem _ x).symm)).trans
    ((P.relabelingHomeomorph f hP.le (by rw [hmap]; exact hR)).trans
      (Homeomorph.setCongr (s := {x : Realization L | x.1.support ∈ P.map f})
        (t := {x : Realization L | x.1.support ∈ R}) (by rw [hmap])))

/-- A finite precomplex on `V` has the realization of its model on `Fin m` as a homeomorphic
polyhedron. The witness is existential because the finite enumeration of `V` is noncanonical. -/
theorem nonempty_finsetRelabelingHomeomorph
    {ι : Type*} {A : AbstractSimplicialComplex ι} {V : Finset ι} {m : ℕ}
    {K : AbstractSimplicialComplex (Fin m)}
    {P : PreAbstractSimplicialComplex (Fin m)} {R : PreAbstractSimplicialComplex ι}
    [DecidableEq ι]
    (hV : V.card = m)
    (hmap : ∀ (f : Fin m ↪ ι), (Finset.univ : Finset (Fin m)).image f = V → P.map f = R)
    (hP : P = K.toPreAbstractSimplicialComplex)
    (hR : R ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ R} ≃ₜ Realization K) := by
  classical
  let e := (Finset.equivFinOfCardEq hV).symm
  let f : Fin m ↪ ι := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ V))
  have himage : (Finset.univ : Finset (Fin m)).image f = V := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hv
      exact ⟨e.symm ⟨v, hv⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  exact ⟨(P.realizationRelabelingHomeomorph f (hmap f himage) hP hR).symm⟩

/-- Relabeling pushes forward the finitely supported barycentric coordinate vector. -/
@[simp]
theorem relabelingHomeomorph_val
    (x : {x : Realization K // x.1.support ∈ P}) :
    (P.relabelingHomeomorph f hK hL x).1.1 = Finsupp.mapDomain f x.1.1 :=
  relabelingForward_val P f hL x

/-- Inverse relabeling pulls back the barycentric coordinate vector. -/
@[simp]
theorem relabelingHomeomorph_symm_val
    (y : {y : Realization L // y.1.support ∈ P.map f}) :
    ((P.relabelingHomeomorph f hK hL).symm y).1.1 =
      Finsupp.comapDomain f y.1.1 f.injective.injOn :=
  relabelingBackward_val P f hK y

/-- The relabeling of a realization pushes forward the barycentric coordinate vector. -/
@[simp]
theorem realizationRelabelingHomeomorph_val {R : PreAbstractSimplicialComplex β}
    (hmap : P.map f = R) (hP : P = K.toPreAbstractSimplicialComplex)
    (hR : R ≤ L.toPreAbstractSimplicialComplex) (x : Realization K) :
    (P.realizationRelabelingHomeomorph f hmap hP hR x).1.1 = Finsupp.mapDomain f x.1 := by
  -- The set-congruence transports preserve the underlying point.
  simp only [realizationRelabelingHomeomorph, Homeomorph.trans_apply,
    Homeomorph.setCongr_apply]
  exact relabelingHomeomorph_val P f hP.le (by rw [hmap]; exact hR) _

/-- The inverse relabeling of a realization pulls back the barycentric coordinate vector. -/
@[simp]
theorem realizationRelabelingHomeomorph_symm_val {R : PreAbstractSimplicialComplex β}
    (hmap : P.map f = R) (hP : P = K.toPreAbstractSimplicialComplex)
    (hR : R ≤ L.toPreAbstractSimplicialComplex) (y : {y : Realization L // y.1.support ∈ R}) :
    ((P.realizationRelabelingHomeomorph f hmap hP hR).symm y).1 =
      Finsupp.comapDomain f y.1.1 f.injective.injOn := by
  -- The set-congruence transports preserve the underlying point.
  simp only [realizationRelabelingHomeomorph, Homeomorph.symm_trans_apply,
    TauCeti.Homeomorph.setCongr_symm_apply]
  exact relabelingHomeomorph_symm_val P f hP.le (by rw [hmap]; exact hR) _

section Ambient

variable [DecidableEq α] {K' L' : AbstractSimplicialComplex α}

/-- Changing the containing weak realization preserves the polyhedron of a precomplex
and its barycentric coordinates. No finiteness assumption is needed. -/
def ambientHomeomorph
    (hK : P ≤ K'.toPreAbstractSimplicialComplex)
    (hL : P ≤ L'.toPreAbstractSimplicialComplex) :
    {x : Realization K' // x.1.support ∈ P} ≃ₜ
      {x : Realization L' // x.1.support ∈ P} := by
  have hmap : P.map (Function.Embedding.refl α) = P := by
    rw [Function.Embedding.coe_refl]
    exact PreAbstractSimplicialComplex.map_id
  exact (P.relabelingHomeomorph (Function.Embedding.refl α) hK
    (by simpa only [hmap] using hL)).trans
    (Homeomorph.setCongr
      (s := {x : Realization L' | x.1.support ∈ P.map (Function.Embedding.refl α)})
      (t := {x : Realization L' | x.1.support ∈ P}) (by rw [hmap]))

/-- Changing the ambient complex leaves the barycentric coordinate vector unchanged. -/
@[simp]
theorem ambientHomeomorph_val
    (hK : P ≤ K'.toPreAbstractSimplicialComplex)
    (hL : P ≤ L'.toPreAbstractSimplicialComplex)
    (x : {x : Realization K' // x.1.support ∈ P}) :
    (P.ambientHomeomorph hK hL x).1.1 = x.1.1 := by
  -- `erw` reduces the `SetLike` coercions identifying the intermediate subtype.
  erw [ambientHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  simp

end Ambient

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

open PreAbstractSimplicialComplex

variable {α ι : Type*} [Fintype α] [DecidableEq ι] (K : AbstractSimplicialComplex ι)
  (f : α ↪ ι) (hf : Finset.univ.image f ∈ K)

/-- An enumeration of a face of `K` identifies the realization of the full simplex on the
enumerating type with the closed simplex of that face in the weak realization of `K`. -/
def realizationTopHomeomorphFace :
    Realization (⊤ : AbstractSimplicialComplex α) ≃ₜ
      {x : Realization K // x.1.support ⊆ Finset.univ.image f} :=
  ((simplex (Finset.univ : Finset α)).realizationRelabelingHomeomorph f
    (map_simplex _) (by rw [simplex_univ, top_toPreAbstractSimplicialComplex])
    (simplex_le_iff.mpr fun _ => hf)).trans
    (Homeomorph.setCongr
      (s := {x : Realization K | x.1.support ∈ simplex (Finset.univ.image f)})
      (t := {x : Realization K | x.1.support ⊆ Finset.univ.image f}) (by
      ext x
      -- The set-congruence goal is membership in two set comprehensions; expose their
      -- predicates before applying the criterion for membership in a simplex.
      change x.1.support ∈ simplex _ ↔ x.1.support ⊆ _
      rw [mem_simplex]
      exact and_iff_right (K.isRelLowerSet_faces.prop_of_mem (support_mem K x))))

/-- The face homeomorphism pushes forward the barycentric coordinate vector. -/
@[simp]
theorem realizationTopHomeomorphFace_val (x : Realization (⊤ : AbstractSimplicialComplex α)) :
    (realizationTopHomeomorphFace K f hf x).1.1 = Finsupp.mapDomain f x.1 := by
  -- The set-congruence transport preserves the underlying point.
  rw [realizationTopHomeomorphFace, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  exact realizationRelabelingHomeomorph_val _ f (map_simplex _)
    (by rw [simplex_univ, top_toPreAbstractSimplicialComplex]) (simplex_le_iff.mpr fun _ => hf) x

/-- The inverse face homeomorphism pulls back the barycentric coordinate vector. -/
@[simp]
theorem realizationTopHomeomorphFace_symm_val
    (y : {x : Realization K // x.1.support ⊆ Finset.univ.image f}) :
    ((realizationTopHomeomorphFace K f hf).symm y).1 =
      Finsupp.comapDomain f y.1.1 f.injective.injOn := by
  -- The set-congruence transport preserves the underlying point.
  rw [realizationTopHomeomorphFace, Homeomorph.symm_trans_apply,
    TauCeti.Homeomorph.setCongr_symm_apply]
  exact realizationRelabelingHomeomorph_symm_val _ f (map_simplex _)
    (by rw [simplex_univ, top_toPreAbstractSimplicialComplex]) (simplex_le_iff.mpr fun _ => hf) _

end AbstractSimplicialComplex
