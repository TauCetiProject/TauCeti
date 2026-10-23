/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.IsCone
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction

/-!
# Indexed joins of abstract simplicial complexes

For a family of types `A : ι → Type*`, the indexed join is the abstract simplicial complex on
`Σ i, A i` whose faces are the nonempty finite sets containing at most one vertex over each
index.  We give its face and barycentric-coordinate descriptions, its functoriality in the
family, and the inclusions of the subjoins supported on finite sets of indices.  Finally,
adjoining a vertex over a fresh index makes a finite vertex restriction of the join a cone.

## Main definitions

* `TauCeti.indexedJoin`: the join of a type-valued family.
* `TauCeti.indexedJoinMap`: maps induced by injective changes of indices and family maps.
* `TauCeti.finiteSubjoin`: the join restricted to a finite set of indices.
* `TauCeti.subjoinInclusion`: the simplicial inclusion of the join on a subset of indices.

## Main results

* `TauCeti.isCone_restrict_indexedJoin_insert`: adjoining a vertex over a fresh index makes a
  finite vertex restriction of an indexed join a cone.
-/

public section

noncomputable section

open Set
open AbstractSimplicialComplex

namespace TauCeti

universe u v w z u₁ u₂

variable {ι : Type u} {κ : Type u₁} {μ : Type u₂}
  {A : ι → Type v} {B : κ → Type w} {C : μ → Type z}

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

/-- Two vertices of a face of an indexed join with the same index are equal. -/
theorem eq_of_mem_indexedJoin {σ : Finset (Σ i, A i)} (hσ : σ ∈ indexedJoin A)
    {v w : Σ i, A i} (hv : v ∈ σ) (hw : w ∈ σ) (h : v.1 = w.1) : v = w :=
  (mem_indexedJoin_iff.mp hσ).2 hv hw h

/-- An injective map of indices and maps of the family members induce a simplicial map of
indexed joins. The maps of the family members need not be injective. -/
def indexedJoinMap (e : ι → κ) (he : Function.Injective e) (f : ∀ i, A i → B (e i)) :
    PreAbstractSimplicialComplex.SimplicialMap
      (indexedJoin A).toPreAbstractSimplicialComplex
      (indexedJoin B).toPreAbstractSimplicialComplex where
  toFun := Sigma.map e f
  map_face' := by
    intro σ hσ
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex] at hσ ⊢
    refine mem_indexedJoin_iff.mpr ⟨hσ.1.image _, ?_⟩
    intro v hv w hw heq
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg (Sigma.map e f) (eq_of_mem_indexedJoin hσ hv' hw' (he heq))

/-- The vertex function underlying an indexed-join map. -/
@[simp]
theorem indexedJoinMap_apply (e : ι → κ) (he : Function.Injective e)
    (f : ∀ i, A i → B (e i)) (v : Σ i, A i) :
    indexedJoinMap e he f v = ⟨e v.1, f v.1 v.2⟩ :=
  (rfl)

/-- The identity on indices and family members induces the identity simplicial map. -/
@[simp]
theorem indexedJoinMap_id :
    indexedJoinMap id Function.injective_id (fun _ x => x) =
      PreAbstractSimplicialComplex.SimplicialMap.id
        (indexedJoin A).toPreAbstractSimplicialComplex := by
  apply DFunLike.ext
  intro v
  simp

/-- Indexed-join maps preserve composition of injective index maps and family maps. -/
@[simp]
theorem indexedJoinMap_comp (e : ι → κ) (he : Function.Injective e)
    (g : κ → μ) (hg : Function.Injective g) (h : ∀ j, B j → C (g j))
    (f : ∀ i, A i → B (e i)) :
    indexedJoinMap (g ∘ e) (hg.comp he) (fun i x => h (e i) (f i x)) =
      (indexedJoinMap g hg h).comp (indexedJoinMap e he f) := by
  apply DFunLike.ext
  intro v
  simp

attribute [-instance] Sigma.instDecidableEqSigma instDecidableEqSigma in
/-- Barycentric-coordinate characterization of the realization of an indexed join.  Besides the
usual nonnegativity and sum-one conditions, the nonzero coordinates have distinct indices. -/
theorem mem_indexedJoin_realization_iff {x : (Σ i, A i) →₀ ℝ} :
    x ∈ (indexedJoin A).standardGeometricComplex.space ↔
      (∀ v, 0 ≤ x v) ∧ x.sum (fun _ r => r) = 1 ∧
        ∀ v w, x v ≠ 0 → x w ≠ 0 → v.1 = w.1 → v = w := by
  rw [mem_standardGeometricComplex_space_iff, mem_indexedJoin_iff]
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
abbrev finiteSubjoin (A : ι → Type v) (s : Finset ι) :
    AbstractSimplicialComplex (Σ i : s, A i.1) :=
  indexedJoin fun i : s => A i.1

/-- A face of a finite subjoin is a nonempty set of vertices with distinct underlying indices. -/
theorem mem_finiteSubjoin_iff {s : Finset ι} {σ : Finset (Σ i : s, A i.1)} :
    σ ∈ finiteSubjoin A s ↔
      σ.Nonempty ∧ Set.InjOn (fun v => v.1.1) (σ : Set (Σ i : s, A i.1)) := by
  rw [finiteSubjoin, mem_indexedJoin_iff]
  constructor
  · rintro ⟨hne, hinj⟩
    exact ⟨hne, fun x hx y hy hxy => hinj hx hy (Subtype.ext hxy)⟩
  · rintro ⟨hne, hinj⟩
    exact ⟨hne, fun x hx y hy hxy => hinj hx hy (congrArg Subtype.val hxy)⟩

/-- The simplicial inclusion of the subjoin on any subset of indices into the full join. -/
def subjoinInclusion (A : ι → Type v) (s : Set ι) :
    PreAbstractSimplicialComplex.SimplicialMap
      (indexedJoin fun i : s => A i).toPreAbstractSimplicialComplex
      (indexedJoin A).toPreAbstractSimplicialComplex :=
  indexedJoinMap Subtype.val Subtype.val_injective (fun _ => id)

/-- A subjoin inclusion preserves the labelled vertex. -/
@[simp]
theorem subjoinInclusion_apply (A : ι → Type v) (s : Set ι)
    (v : Σ i : s, A i) : subjoinInclusion A s v = ⟨v.1.1, v.2⟩ :=
  (rfl)

/-- The subjoin inclusion is injective on vertices. -/
theorem subjoinInclusion_injective (A : ι → Type v) (s : Set ι) :
    Function.Injective (subjoinInclusion A s) :=
  Subtype.val_injective.sigma_map (fun _ => Function.injective_id)

/-- The continuous inclusion of the realization of a finite subjoin into the realization of the
full indexed join. -/
def finiteSubjoinRealizationInclusion (A : ι → Type v) (s : Finset ι) :
    C((finiteSubjoin A s).Realization, (indexedJoin A).Realization) :=
  (subjoinInclusion A s).realizationMap

/-- The realization inclusion pushes barycentric coordinates forward along the vertex inclusion.
-/
@[simp]
theorem finiteSubjoinRealizationInclusion_val (A : ι → Type v) (s : Finset ι)
    (x : (finiteSubjoin A s).Realization) :
    (finiteSubjoinRealizationInclusion A s x : (Σ i, A i) →₀ ℝ) =
      Finsupp.mapDomain (subjoinInclusion A s) x.1 := by
  rw [finiteSubjoinRealizationInclusion,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val]

/-- The realization map of a finite-subjoin inclusion is injective. -/
theorem finiteSubjoinRealizationInclusion_injective (A : ι → Type v) (s : Finset ι) :
    Function.Injective (finiteSubjoinRealizationInclusion A s) :=
  (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_injective_iff
    (subjoinInclusion A s)).mpr (subjoinInclusion_injective A s)

/-- The realization inclusion of a finite subjoin sends each vertex to the corresponding vertex
of the full indexed join. -/
@[simp]
theorem finiteSubjoinRealizationInclusion_vertex (A : ι → Type v) (s : Finset ι)
    (v : Σ i : s, A i.1) :
    finiteSubjoinRealizationInclusion A s ((finiteSubjoin A s).vertex v) =
      (indexedJoin A).vertex ⟨v.1.1, v.2⟩ := by
  apply Subtype.ext
  simp only [finiteSubjoinRealizationInclusion_val, AbstractSimplicialComplex.vertex_val,
    Finsupp.mapDomain_single, subjoinInclusion_apply]

section IsCone

attribute [-instance] Sigma.instDecidableEqSigma instDecidableEqSigma

/-- Adjoining a vertex over an index absent from a finite vertex set makes the corresponding
restriction of an indexed join a cone. -/
theorem isCone_restrict_indexedJoin_insert (V : Finset (Σ i, A i)) (i : ι) (a : A i)
    (hi : i ∉ V.image Sigma.fst) :
    PreAbstractSimplicialComplex.IsCone
      ((indexedJoin A).restrict ((V : Set (Σ i, A i)) ∪ {⟨i, a⟩})).toPreAbstractSimplicialComplex
      ⟨⟨i, a⟩, Set.mem_union_right _ (Set.mem_singleton _)⟩ := by
  refine ⟨singleton_mem _ _, fun σ hσ => ?_⟩
  rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
    mem_restrict_iff] at hσ ⊢
  rw [Finset.image_insert]
  by_cases hv : (⟨i, a⟩ : Σ i, A i) ∈ σ.image Subtype.val
  · rwa [Finset.insert_eq_of_mem hv]
  rw [mem_indexedJoin_iff] at hσ ⊢
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.coe_insert, Set.injOn_insert (Finset.mem_coe.not.mpr hv)]
  refine ⟨hσ.2, ?_⟩
  rintro ⟨w, hw, hwi⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  rcases u.2 with huV | hua
  · exact hi (Finset.mem_image.mpr ⟨u, huV, hwi⟩)
  · exact hv (Finset.mem_image.mpr ⟨u, hu, hua⟩)

end IsCone

end TauCeti
