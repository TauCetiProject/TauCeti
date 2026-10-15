/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Indexed joins of abstract simplicial complexes

For a family of types `A : ι → Type*`, the indexed join is the abstract simplicial complex on
`Σ i, A i` whose faces are the nonempty finite sets containing at most one vertex over each
index.  We give its face and barycentric-coordinate descriptions, its functoriality in the
family, and the inclusions of the subjoins supported on finite sets of indices.

## Main definitions

* `TauCeti.indexedJoin`: the join of a type-valued family.
* `TauCeti.indexedJoinMap`: the simplicial map induced by maps of the family members.
* `TauCeti.finiteSubjoin`: the join restricted to a finite set of indices.
* `TauCeti.finiteSubjoinInclusion`: the simplicial inclusion into the full indexed join.
-/

public section

noncomputable section

open Set
open AbstractSimplicialComplex

namespace TauCeti

universe u v w z

variable {ι : Type u} {A : ι → Type v} {B : ι → Type w} {C : ι → Type z}

attribute [local instance] Classical.decEq

/-- The indexed join of a family of types.  Its vertices are pairs `⟨i, a⟩`, and a nonempty
finite set is a face exactly when it contains at most one vertex with each first coordinate. -/
def indexedJoin (A : ι → Type v) : AbstractSimplicialComplex (Σ i, A i) where
  faces := {σ | σ.Nonempty ∧ Set.InjOn Sigma.fst (σ : Set (Σ i, A i))}
  isRelLowerSet_faces := by
    rintro σ ⟨hσne, hσinj⟩
    refine ⟨hσne, fun τ hτσ hτne => ⟨hτne, hσinj.mono ?_⟩⟩
    simpa only [Finset.coe_subset] using hτσ
  singleton_mem v := by
    refine ⟨Finset.singleton_nonempty v, ?_⟩
    intro x hx y hy _
    simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm

/-- A finite set is a face of the indexed join exactly when it is nonempty and its vertices
have pairwise distinct indices. -/
@[simp]
theorem mem_indexedJoin_iff {σ : Finset (Σ i, A i)} :
    σ ∈ indexedJoin A ↔ σ.Nonempty ∧ Set.InjOn Sigma.fst (σ : Set (Σ i, A i)) :=
  Iff.rfl

/-- The number of indices represented by a face of an indexed join is its number of vertices. -/
theorem card_image_fst_eq_of_mem_indexedJoin {σ : Finset (Σ i, A i)}
    (hσ : σ ∈ indexedJoin A) : (σ.image Sigma.fst).card = σ.card := by
  rw [Finset.card_image_iff.mpr (mem_indexedJoin_iff.mp hσ).2]

/-- Maps between corresponding members of two families induce a simplicial map of their indexed
joins. -/
def indexedJoinMap (f : ∀ i, A i → B i) :
    PreAbstractSimplicialComplex.SimplicialMap
      (indexedJoin A).toPreAbstractSimplicialComplex
      (indexedJoin B).toPreAbstractSimplicialComplex where
  toFun v := ⟨v.1, f v.1 v.2⟩
  map_face' := by
    intro σ hσ
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex] at hσ ⊢
    rw [mem_indexedJoin_iff] at hσ
    refine mem_indexedJoin_iff.mpr ⟨hσ.1.image _, ?_⟩
    rw [Finset.coe_image]
    exact Set.InjOn.image_of_comp
      (f := fun v : (Σ i, A i) => (⟨v.1, f v.1 v.2⟩ : Σ i, B i)) (g := Sigma.fst)
      (fun x hx y hy hxy => hσ.2 hx hy hxy)

/-- The vertex function underlying the simplicial map of indexed joins. -/
@[simp]
theorem indexedJoinMap_apply (f : ∀ i, A i → B i) (v : Σ i, A i) :
    indexedJoinMap f v = ⟨v.1, f v.1 v.2⟩ :=
  (rfl)

/-- The identity family map induces the identity simplicial map of an indexed join. -/
@[simp]
theorem indexedJoinMap_id :
    indexedJoinMap (fun _ => id) =
      PreAbstractSimplicialComplex.SimplicialMap.id
        (indexedJoin A).toPreAbstractSimplicialComplex := by
  apply PreAbstractSimplicialComplex.SimplicialMap.ext
  funext v
  calc
    (indexedJoinMap (fun _ => id)).toFun v = indexedJoinMap (fun _ => id) v := rfl
    _ = ⟨v.1, v.2⟩ := indexedJoinMap_apply _ v
    _ = (PreAbstractSimplicialComplex.SimplicialMap.id
        (indexedJoin A).toPreAbstractSimplicialComplex).toFun v := by
      exact (PreAbstractSimplicialComplex.SimplicialMap.id_apply
        (K := (indexedJoin A).toPreAbstractSimplicialComplex) v).symm

/-- Indexed-join maps preserve composition of maps between family members. -/
@[simp]
theorem indexedJoinMap_comp (g : ∀ i, B i → C i) (f : ∀ i, A i → B i) :
    indexedJoinMap (fun i => g i ∘ f i) =
      (indexedJoinMap g).comp (indexedJoinMap f) := by
  apply PreAbstractSimplicialComplex.SimplicialMap.ext
  funext v
  calc
    (indexedJoinMap (fun i => g i ∘ f i)).toFun v =
        indexedJoinMap (fun i => g i ∘ f i) v := rfl
    _ = ⟨v.1, g v.1 (f v.1 v.2)⟩ := indexedJoinMap_apply _ v
    _ = ((indexedJoinMap g).comp (indexedJoinMap f)).toFun v := by
      symm
      calc
        ((indexedJoinMap g).comp (indexedJoinMap f)).toFun v =
            (indexedJoinMap g).comp (indexedJoinMap f) v := rfl
        _ = indexedJoinMap g (indexedJoinMap f v) :=
          PreAbstractSimplicialComplex.SimplicialMap.comp_apply _ _ _
        _ = ⟨v.1, g v.1 (f v.1 v.2)⟩ := by
          rw [indexedJoinMap_apply, indexedJoinMap_apply]

attribute [-instance] Sigma.instDecidableEqSigma instDecidableEqSigma in
/-- Barycentric-coordinate characterization of the realization of an indexed join.  Besides the
usual nonnegativity and sum-one conditions, the nonzero coordinates have distinct indices. -/
theorem mem_indexedJoin_realization_iff {x : (Σ i, A i) →₀ ℝ} :
    x ∈ (indexedJoin A).standardGeometricComplex.space ↔
      (∀ v, 0 ≤ x v) ∧ x.sum (fun _ r => r) = 1 ∧
        ∀ v w, x v ≠ 0 → x w ≠ 0 → v.1 = w.1 → v = w := by
  rw [AbstractSimplicialComplex.standardGeometricComplex,
    Geometry.SimplicialComplex.mem_space_onFinsupp_iff,
    AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex, mem_indexedJoin_iff]
  constructor
  · rintro ⟨hnonneg, hsum, -, hinj⟩
    exact ⟨hnonneg, hsum, fun v w hv hw hvw => hinj
      (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hw) hvw⟩
  · rintro ⟨hnonneg, hsum, hunique⟩
    have hsupp : x.support.Nonempty := by
      apply Finsupp.support_nonempty_iff.mpr
      rintro rfl
      simp at hsum
    have hinj : Set.InjOn Sigma.fst (x.support : Set (Σ i, A i)) :=
      fun v hv w hw hvw => hunique v w (Finsupp.mem_support_iff.mp hv)
        (Finsupp.mem_support_iff.mp hw) hvw
    exact ⟨hnonneg, hsum, hsupp, hinj⟩

/-- The carrier of a point in an indexed join contains at most one vertex over each index. -/
theorem realization_support_injOn_fst (x : (indexedJoin A).Realization) :
    Set.InjOn Sigma.fst (x.1.support : Set (Σ i, A i)) :=
  (mem_indexedJoin_iff.mp ((indexedJoin A).support_mem x)).2

/-- Two different vertices over the same index cannot both have nonzero barycentric coordinate in
the realization of an indexed join. -/
theorem realization_apply_eq_zero_of_fst_eq {x : (indexedJoin A).Realization}
    {v w : Σ i, A i} (hvw : v.1 = w.1) (hne : v ≠ w) : x.1 v = 0 ∨ x.1 w = 0 := by
  by_cases hv : x.1 v = 0
  · exact Or.inl hv
  · refine Or.inr (not_ne_iff.mp fun hw => ?_)
    exact hne (realization_support_injOn_fst x
      (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hw) hvw)

/-- The subjoin of a family supported on a finite set of indices. -/
def finiteSubjoin (A : ι → Type v) (s : Finset ι) :
    AbstractSimplicialComplex (Σ i : s, A i.1) :=
  indexedJoin fun i : s => A i.1

/-- A face of a finite subjoin is a nonempty set of vertices with distinct underlying indices. -/
@[simp]
theorem mem_finiteSubjoin_iff {s : Finset ι} {σ : Finset (Σ i : s, A i.1)} :
    σ ∈ finiteSubjoin A s ↔
      σ.Nonempty ∧ Set.InjOn (fun v => v.1.1) (σ : Set (Σ i : s, A i.1)) := by
  rw [finiteSubjoin, mem_indexedJoin_iff]
  constructor
  · rintro ⟨hne, hinj⟩
    exact ⟨hne, fun x hx y hy hxy => hinj hx hy (Subtype.ext hxy)⟩
  · rintro ⟨hne, hinj⟩
    exact ⟨hne, fun x hx y hy hxy => hinj hx hy (congrArg Subtype.val hxy)⟩

/-- The canonical simplicial inclusion of a finite subjoin into the full indexed join. -/
def finiteSubjoinInclusion (A : ι → Type v) (s : Finset ι) :
    PreAbstractSimplicialComplex.SimplicialMap
      (finiteSubjoin A s).toPreAbstractSimplicialComplex
      (indexedJoin A).toPreAbstractSimplicialComplex where
  toFun v := ⟨v.1.1, v.2⟩
  map_face' := by
    intro σ hσ
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex] at hσ ⊢
    rw [mem_finiteSubjoin_iff] at hσ
    refine mem_indexedJoin_iff.mpr ⟨hσ.1.image _, ?_⟩
    rw [Finset.coe_image]
    exact Set.InjOn.image_of_comp
      (f := fun v : (Σ i : s, A i.1) => (⟨v.1.1, v.2⟩ : Σ i, A i)) (g := Sigma.fst)
      (fun x hx y hy hxy => hσ.2 hx hy hxy)

/-- The finite-subjoin inclusion sends a labelled vertex to the same labelled vertex in the full
join. -/
@[simp]
theorem finiteSubjoinInclusion_apply (A : ι → Type v) (s : Finset ι)
    (v : Σ i : s, A i.1) : finiteSubjoinInclusion A s v = ⟨v.1.1, v.2⟩ :=
  (rfl)

/-- The finite-subjoin inclusion is injective on vertices. -/
theorem finiteSubjoinInclusion_injective (A : ι → Type v) (s : Finset ι) :
    Function.Injective (finiteSubjoinInclusion A s) := by
  intro x y hxy
  apply Sigma.ext (Subtype.ext (congrArg Sigma.fst hxy))
  exact (Sigma.mk.inj_iff.mp hxy).2

/-- The continuous inclusion of the realization of a finite subjoin into the realization of the
full indexed join. -/
def finiteSubjoinRealizationInclusion (A : ι → Type v) (s : Finset ι) :
    C((finiteSubjoin A s).Realization, (indexedJoin A).Realization) :=
  (finiteSubjoinInclusion A s).realizationMap

/-- The realization inclusion pushes barycentric coordinates forward along the vertex inclusion.
-/
@[simp]
theorem finiteSubjoinRealizationInclusion_val (A : ι → Type v) (s : Finset ι)
    (x : (finiteSubjoin A s).Realization) :
    (finiteSubjoinRealizationInclusion A s x : (Σ i, A i) →₀ ℝ) =
      Finsupp.mapDomain (finiteSubjoinInclusion A s) x.1 := by
  rw [finiteSubjoinRealizationInclusion,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val]

/-- The realization map of a finite-subjoin inclusion is injective. -/
theorem finiteSubjoinRealizationInclusion_injective (A : ι → Type v) (s : Finset ι) :
    Function.Injective (finiteSubjoinRealizationInclusion A s) :=
  (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_injective_iff
    (finiteSubjoinInclusion A s)).mpr (finiteSubjoinInclusion_injective A s)

/-- The realization inclusion of a finite subjoin sends each vertex to the corresponding vertex
of the full indexed join. -/
@[simp]
theorem finiteSubjoinRealizationInclusion_vertex (A : ι → Type v) (s : Finset ι)
    (v : Σ i : s, A i.1) :
    finiteSubjoinRealizationInclusion A s ((finiteSubjoin A s).vertex v) =
      (indexedJoin A).vertex ⟨v.1.1, v.2⟩ := by
  rw [finiteSubjoinRealizationInclusion,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_vertex,
    finiteSubjoinInclusion_apply]

end TauCeti
