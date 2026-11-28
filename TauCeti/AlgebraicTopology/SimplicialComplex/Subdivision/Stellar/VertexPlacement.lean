/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.SimplexMove
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Link
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Relabel

/-!
# Placing vertices at arbitrary points via stellar subdivision

Any finite subset `S` of the realization `Realization K` of a simplicial complex `K` becomes the
image of a set of vertices of some complex `K'` homeomorphic to `Realization K`, preserving vertex
finiteness and combinatorial manifold dimension.

For a single point `x`, if `x` is already a vertex of `K`, no change is required. Otherwise `x`
lies in the open simplex spanned by its support `σ = x.val.support` of cardinality `1 < σ.card`.
Starring `σ` at a fresh vertex `none : Option ι` yields an abstract simplicial complex
`K.stellarSubdivisionOption hσ hgt` on `Option ι` together with a canonical homeomorphism
`K.stellarSubdivisionOptionHomeomorph hσ hgt :`
`Realization (K.stellarSubdivisionOption hσ hgt) ≃ₜ Realization K` sending `vertex none` to the
barycenter of `σ` and fixing all original vertices. Composing with
`AbstractSimplicialComplex.simplexMoveHomeomorph`, which moves the barycenter of `σ` to `x` and
fixes all vertices of `K`, gives a complex `K'` and a homeomorphism
`Realization K' ≃ₜ Realization K` whose vertex images contain `x` and every original vertex.
Iterating over any finite set `S` yields a complex `K'` and homeomorphism in which every point
of `S` is a vertex image.

## Main definitions

* `AbstractSimplicialComplex.stellarSubdivisionOption`: starring a face `σ` of `K` with
  `1 < σ.card` at the fresh vertex `none : Option ι`.
* `AbstractSimplicialComplex.stellarSubdivisionOptionHomeomorph`: canonical homeomorphism from the
  realization of `stellarSubdivisionOption` to `Realization K`, sending `none` to the barycenter
  of `σ` and `some w` to `K.vertex w`.

## Main results

* `AbstractSimplicialComplex.exists_homeomorph_vertex_image`: single-point vertex placement,
  preserving vertex finiteness and combinatorial manifold dimension.
* `AbstractSimplicialComplex.exists_homeomorph_finset_vertex_image` and
  `AbstractSimplicialComplex.exists_homeomorph_vertex_image_of_finite`: finite-set vertex
  placement.
* `AbstractSimplicialComplex.exists_homeomorph_vertex_image_of_homeomorph`: finite-set vertex
  placement transported along a homeomorphism `Realization K ≃ₜ X`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (starrings and subdivisions).
-/

public section

noncomputable section

open Set Finset

namespace AbstractSimplicialComplex

section StellarOption

variable {ι : Type u} [DecidableEq ι] (K : AbstractSimplicialComplex ι) {σ : Finset ι}

private theorem notMem_map_some_singleton :
    ({none} : Finset (Option ι)) ∉
      K.toPreAbstractSimplicialComplex.map Function.Embedding.some := by
  intro hmem
  obtain ⟨τ, -, hτ⟩ := PreAbstractSimplicialComplex.mem_map_iff.mp hmem
  have hmem' : (none : Option ι) ∈ τ.image some := hτ.symm ▸ Finset.mem_singleton_self none
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hmem'
  exact Option.some_ne_none w hw

private theorem map_some_mem_of_mem (hσ : σ ∈ K) :
    σ.map Function.Embedding.some ∈
      K.toPreAbstractSimplicialComplex.map Function.Embedding.some :=
  PreAbstractSimplicialComplex.mem_map_iff.mpr
    ⟨σ, hσ, by simp [Finset.map_eq_image]⟩

/-- The abstract simplicial complex on `Option ι` obtained by embedding `K` along `some` and
starring a face `σ` with `1 < σ.card` at the fresh vertex `none`. -/
def stellarSubdivisionOption (hσ : σ ∈ K) (hgt : 1 < σ.card) :
    AbstractSimplicialComplex (Option ι) :=
  let Kopt := K.toPreAbstractSimplicialComplex.map Function.Embedding.some
  let σopt := σ.map Function.Embedding.some
  { PreAbstractSimplicialComplex.stellarSubdivision Kopt σopt none with
    singleton_mem := fun u => by
      rcases u with _ | w
      · exact PreAbstractSimplicialComplex.singleton_mem_stellarSubdivision_iff.mpr
          (K.map_some_mem_of_mem hσ)
      · refine (PreAbstractSimplicialComplex.mem_stellarSubdivision_iff_of_notMem
          (by simp)).mpr ⟨?_, ?_⟩
        · exact PreAbstractSimplicialComplex.mem_map_iff.mpr
            ⟨{w}, K.singleton_mem w, by simp⟩
        · intro hsub
          have hle : σ.card ≤ 1 := by
            have h1 := Finset.card_le_card hsub
            simpa [σopt] using h1
          exact absurd hle (by omega) }

@[simp]
private theorem stellarSubdivisionOption_toPreAbstractSimplicialComplex
    (hσ : σ ∈ K) (hgt : 1 < σ.card) :
    (K.stellarSubdivisionOption hσ hgt).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.stellarSubdivision
        (K.toPreAbstractSimplicialComplex.map Function.Embedding.some)
        (σ.map Function.Embedding.some) none :=
  (rfl)

/-- Starring a face with `1 < σ.card` at `none : Option ι` preserves combinatorial manifold
dimension. -/
theorem isCombinatorialManifold_stellarSubdivisionOption (hσ : σ ∈ K) (hgt : 1 < σ.card)
    {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold
      K.toPreAbstractSimplicialComplex n) :
    PreAbstractSimplicialComplex.IsCombinatorialManifold
      (K.stellarSubdivisionOption hσ hgt).toPreAbstractSimplicialComplex n := by
  have hKopt : PreAbstractSimplicialComplex.IsCombinatorialManifold
      (K.toPreAbstractSimplicialComplex.map Function.Embedding.some) n :=
    (PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff
      (Option.some_injective (α := ι))).mpr hK
  exact hKopt.stellarSubdivision (K.notMem_map_some_singleton)

private def stellarSubdivisionOptionData (hσ : σ ∈ K) (hgt : 1 < σ.card) :
    { e : Realization (K.stellarSubdivisionOption hσ hgt) ≃ₜ Realization K //
      (e ((K.stellarSubdivisionOption hσ hgt).vertex none)).val =
        faceBarycenter K ⟨σ, hσ⟩ ∧
      ∀ w : ι, e ((K.stellarSubdivisionOption hσ hgt).vertex (some w)) = K.vertex w } := by
  let K' := K.stellarSubdivisionOption hσ hgt
  let Kopt := K.toPreAbstractSimplicialComplex.map Function.Embedding.some
  let σopt := σ.map Function.Embedding.some
  let P := PreAbstractSimplicialComplex.stellarSubdivision Kopt σopt none
  let top := (⊤ : AbstractSimplicialComplex (Option ι))
  have hmapP : K'.toPreAbstractSimplicialComplex.map (Function.Embedding.refl (Option ι)) = P := by
    rw [Function.Embedding.coe_refl, PreAbstractSimplicialComplex.map_id,
      stellarSubdivisionOption_toPreAbstractSimplicialComplex]
  let r1 : Realization K' ≃ₜ {z : Realization top // z.val.support ∈ P} :=
    K'.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
      (Function.Embedding.refl _) hmapP rfl (PreAbstractSimplicialComplex.le_top P)
  let estPair := Classical.choose
    (PreAbstractSimplicialComplex.exists_homeomorph_stellarSubdivision
      (A := top) (K.map_some_mem_of_mem hσ) (K.notMem_map_some_singleton)
      (PreAbstractSimplicialComplex.le_top Kopt) (PreAbstractSimplicialComplex.le_top P))
  have hest : ∀ x,
      (estPair x).val.val = Finset.stellarSubdivisionLinearMap σopt none x.val.val :=
    Classical.choose_spec
      (PreAbstractSimplicialComplex.exists_homeomorph_stellarSubdivision
        (A := top) (K.map_some_mem_of_mem hσ) (K.notMem_map_some_singleton)
        (PreAbstractSimplicialComplex.le_top Kopt) (PreAbstractSimplicialComplex.le_top P))
  let r2 : Realization K ≃ₜ {z : Realization top // z.val.support ∈ Kopt} :=
    K.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
      Function.Embedding.some rfl rfl (PreAbstractSimplicialComplex.le_top Kopt)
  refine ⟨r1.trans (estPair.trans r2.symm), ?_, ?_⟩
  · let b : Realization K :=
      ⟨faceBarycenter K ⟨σ, hσ⟩,
        mem_realization_iff.2 ⟨σ, hσ, faceBarycenter_mem K ⟨σ, hσ⟩⟩⟩
    have hstnone : (estPair (r1 (K'.vertex none))).val.val = (r2 b).val.val := by
      rw [hest]
      have hr1 : (r1 (K'.vertex none)).val.val = Finsupp.single none 1 := by
        dsimp only [r1]
        rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
        simp
      rw [hr1, Finset.stellarSubdivisionLinearMap_single]
      dsimp only [r2]
      rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
      ext u
      rcases u with _ | w
      · have hnotin :
            (none : Option ι) ∉ Set.range (Function.Embedding.some : ι ↪ Option ι) := by
          rintro ⟨w, hw⟩
          exact Option.some_ne_none w hw
        rw [Finsupp.mapDomain_of_notMem_range _ _ hnotin]
        simp [σopt, Finset.sum_apply]
      · rw [← Function.Embedding.some_apply,
          Finsupp.mapDomain_apply_of_injective Function.Embedding.some.injective]
        dsimp only [b]
        rw [faceBarycenter_apply]
        by_cases hw : w ∈ σ <;>
          simp [σopt, Finset.sum_apply, Finsupp.single_apply, hw]
    have hr2b : r2.symm (estPair (r1 (K'.vertex none))) = b :=
      r2.symm_apply_eq.mpr (Subtype.ext (Subtype.ext hstnone))
    exact congrArg Subtype.val hr2b
  · intro w
    have hstw : (estPair (r1 (K'.vertex (some w)))).val.val = (r2 (K.vertex w)).val.val := by
      rw [hest]
      have hr1 : (r1 (K'.vertex (some w))).val.val = Finsupp.single (some w) 1 := by
        dsimp only [r1]
        rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
        simp
      rw [hr1, Finset.stellarSubdivisionLinearMap_single_of_ne (by simp)]
      dsimp only [r2]
      rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
      simp
    exact r2.symm_apply_eq.mpr (Subtype.ext (Subtype.ext hstw))

/-- Canonical homeomorphism from `Realization (K.stellarSubdivisionOption hσ hgt)` to
`Realization K`, sending `vertex none` to the barycenter of `σ` and `vertex (some w)` to
`K.vertex w`. -/
def stellarSubdivisionOptionHomeomorph (hσ : σ ∈ K) (hgt : 1 < σ.card) :
    Realization (K.stellarSubdivisionOption hσ hgt) ≃ₜ Realization K :=
  (K.stellarSubdivisionOptionData hσ hgt).val

/-- `stellarSubdivisionOptionHomeomorph` sends the new vertex `none` to the barycenter of `σ`. -/
@[simp]
theorem stellarSubdivisionOptionHomeomorph_vertex_none (hσ : σ ∈ K) (hgt : 1 < σ.card) :
    (K.stellarSubdivisionOptionHomeomorph hσ hgt
      ((K.stellarSubdivisionOption hσ hgt).vertex none)).val = faceBarycenter K ⟨σ, hσ⟩ :=
  (K.stellarSubdivisionOptionData hσ hgt).property.1

/-- `stellarSubdivisionOptionHomeomorph` sends each original vertex `some w` to `K.vertex w`. -/
@[simp]
theorem stellarSubdivisionOptionHomeomorph_vertex_some (hσ : σ ∈ K) (hgt : 1 < σ.card) (w : ι) :
    K.stellarSubdivisionOptionHomeomorph hσ hgt
      ((K.stellarSubdivisionOption hσ hgt).vertex (some w)) = K.vertex w :=
  (K.stellarSubdivisionOptionData hσ hgt).property.2 w

end StellarOption

section VertexPlacement

/-- Given any point `x` in `Realization K`, there exist a complex `K'` (constructed by a single
stellar subdivision when `x` is not already a vertex) and a homeomorphism
`e : Realization K' ≃ₜ Realization K` preserving vertex finiteness and combinatorial manifold
dimension whose vertex images include `x` and every vertex of `K`. -/
theorem exists_homeomorph_vertex_image {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) (x : Realization K) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      (∃ u : ι', e (K'.vertex u) = x) ∧
      (∀ w : ι, ∃ w' : ι', e (K'.vertex w') = K.vertex w) := by
  classical
  have hσK : x.val.support ∈ K := support_mem K x
  have hne : x.val.support.Nonempty := K.isRelLowerSet_faces.prop_of_mem hσK
  by_cases hcard : x.val.support.card = 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    exact ⟨ι, inferInstance, K, Homeomorph.refl _, id, fun _ h => h,
      ⟨v, (Realization.eq_vertex_of_support_eq K x hv).symm⟩, fun w => ⟨w, rfl⟩⟩
  · have hgt : 1 < x.val.support.card :=
      lt_of_le_of_ne (Finset.card_pos.mpr hne) (Ne.symm hcard)
    let K' := K.stellarSubdivisionOption hσK hgt
    let est := K.stellarSubdivisionOptionHomeomorph hσK hgt
    let b : Realization K :=
      ⟨faceBarycenter K ⟨x.val.support, hσK⟩,
        mem_realization_iff.2 ⟨x.val.support, hσK, faceBarycenter_mem K ⟨x.val.support, hσK⟩⟩⟩
    have hb : b.val.support = x.val.support :=
      support_faceBarycenter K ⟨x.val.support, hσK⟩
    let move := K.simplexMoveHomeomorph b x hb rfl
    refine ⟨Option ι, inferInstance, K', est.trans move, fun _ => inferInstance,
      fun _ hK => K.isCombinatorialManifold_stellarSubdivisionOption hσK hgt hK,
      ⟨none, ?_⟩, fun w => ⟨some w, ?_⟩⟩
    · have hest : est (K'.vertex none) = b :=
        Subtype.ext (K.stellarSubdivisionOptionHomeomorph_vertex_none hσK hgt)
      simp [hest, move]
    · rw [Homeomorph.trans_apply]
      dsimp only [est, move]
      rw [K.stellarSubdivisionOptionHomeomorph_vertex_some hσK hgt w,
        K.simplexMoveHomeomorph_vertex b x hb rfl hgt w]

/-- Given any finite set of points `S : Finset (Realization K)`, there exist a complex `K'` on the
same universe as `ι` and a homeomorphism `e : Realization K' ≃ₜ Realization K` preserving vertex
finiteness and combinatorial manifold dimension such that every point of `S` is the `e`-image of a
vertex of `K'`. -/
theorem exists_homeomorph_finset_vertex_image {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) (S : Finset (Realization K)) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      (∀ s ∈ S, ∃ u : ι', e (K'.vertex u) = s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨ι, inferInstance, K, Homeomorph.refl _, id, fun _ h => h, fun _ h => by simp at h⟩
  | @insert x S₀ _ ih =>
    obtain ⟨ι₀, _, K₀, e₀, hfin₀, hman₀, hvert₀⟩ := ih
    obtain ⟨ι₁, _, K₁, e₁, hfin₁, hman₁, ⟨u, hu⟩, hkeep⟩ :=
      exists_homeomorph_vertex_image K₀ (e₀.symm x)
    refine ⟨ι₁, inferInstance, K₁, e₁.trans e₀, hfin₁ ∘ hfin₀,
      fun n h => hman₁ n (hman₀ n h), fun s hs => ?_⟩
    rcases Finset.mem_insert.mp hs with rfl | hs₀
    · exact ⟨u, by simp [hu]⟩
    · obtain ⟨w, hw⟩ := hvert₀ s hs₀
      obtain ⟨w', hw'⟩ := hkeep w
      exact ⟨w', by simp [hw', hw]⟩

/-- Given any finite subset `S : Set (Realization K)`, there exist a complex `K'`, a
homeomorphism `e : Realization K' ≃ₜ Realization K`, and a vertex subset `V : Set ι'` whose
vertex image under `e` equals `S`, preserving vertex finiteness and combinatorial manifold
dimension. -/
theorem exists_homeomorph_vertex_image_of_finite {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) {S : Set (Realization K)} (hS : S.Finite) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K) (V : Set ι'),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      e '' (K'.vertex '' V) = S := by
  obtain ⟨ι', _, K', e, hfin, hman, hvert⟩ :=
    exists_homeomorph_finset_vertex_image K hS.toFinset
  refine ⟨ι', inferInstance, K', e, {u : ι' | e (K'.vertex u) ∈ S}, hfin, hman, ?_⟩
  ext s
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact hu
  · intro hs
    obtain ⟨u, hu⟩ := hvert s (hS.mem_toFinset.mpr hs)
    exact ⟨K'.vertex u, ⟨u, by simpa [hu] using hs, rfl⟩, hu⟩

/-- Transporting `exists_homeomorph_vertex_image_of_finite` along a homeomorphism
`e : Realization K ≃ₜ X`: any finite subset `S : Set X` is the vertex image under some complex
`K'` and homeomorphism `e' : Realization K' ≃ₜ X`, preserving vertex finiteness and combinatorial
manifold dimension. -/
theorem exists_homeomorph_vertex_image_of_homeomorph {ι : Type u} [DecidableEq ι]
    {X : Type*} [TopologicalSpace X] (K : AbstractSimplicialComplex ι)
    (e : Realization K ≃ₜ X) {S : Set X} (hS : S.Finite) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e' : Realization K' ≃ₜ X) (V : Set ι'),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      e' '' (K'.vertex '' V) = S := by
  obtain ⟨ι', _, K', e₀, V, hfin, hman, hV⟩ :=
    K.exists_homeomorph_vertex_image_of_finite (hS.preimage e.injective.injOn)
  refine ⟨ι', inferInstance, K', e₀.trans e, V, hfin, hman, ?_⟩
  rw [← Set.image_preimage_eq S e.surjective, ← hV]
  ext y
  simp [Homeomorph.trans_apply]

end VertexPlacement

end AbstractSimplicialComplex
