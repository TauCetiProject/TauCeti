/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Joins of discrete families

The join of a family of discrete sets has vertices `Σ i, A i`. Its faces are nonempty finite
sets containing at most one vertex at each index. We construct this abstract complex, describe
its barycentric coordinates, and give the simplicial maps induced by maps of families and by
inclusions of subsets of indices. The realization uses the weak topology, not the topology
induced by a norm on the coordinate vectors.

Taking the index type to be `ℕ` gives the countable join used in Milnor's construction of
classifying spaces.

The construction follows J. Milnor, *Construction of universal bundles, II*, Ann. of Math.
63 (1956). It uses Mathlib's `AbstractSimplicialComplex` and the weak realization and simplicial
realization maps in `TauCeti.AlgebraicTopology.SimplicialComplex.Realization`.
-/

public section

open AbstractSimplicialComplex
open PreAbstractSimplicialComplex (SimplicialMap)

namespace TauCeti.SimplicialComplex

variable {I : Type*} (A : I → Type*)

/-- The join of discrete sets indexed by `I`: a face contains at most one vertex at each index.
In particular, taking `I = ℕ` gives the countable join. -/
def joinComplex : AbstractSimplicialComplex (Σ i, A i) where
  faces := {σ | σ.Nonempty ∧ Set.InjOn Sigma.fst (σ : Set (Σ i, A i))}
  isRelLowerSet_faces := by
    rintro σ ⟨hne, hinj⟩
    exact ⟨hne, fun _ hsub hne' => ⟨hne', hinj.mono hsub⟩⟩
  singleton_mem v := ⟨Finset.singleton_nonempty v, by simp⟩

/-- Faces are precisely the nonempty finite sets meeting every index at most once. -/
@[simp]
theorem mem_joinComplex_iff {σ : Finset (Σ i, A i)} :
    σ ∈ joinComplex A ↔ σ.Nonempty ∧ Set.InjOn Sigma.fst (σ : Set (Σ i, A i)) :=
  Iff.rfl

/-- Two vertices of a face at the same index are equal. -/
theorem eq_of_mem_joinComplex {σ : Finset (Σ i, A i)} (hσ : σ ∈ joinComplex A)
    {v w : Σ i, A i} (hv : v ∈ σ) (hw : w ∈ σ) (h : v.1 = w.1) : v = w :=
  (mem_joinComplex_iff A).mp hσ |>.2 hv hw h

variable {A} {B C : I → Type*}

/-- Maps of the discrete families induce a simplicial map, preserving the index of each vertex.
No injectivity assumption is required on the family maps. -/
def joinComplexMap [DecidableEq (Σ i, B i)] (f : ∀ i, A i → B i) :
    SimplicialMap (joinComplex A).toPreAbstractSimplicialComplex
      (joinComplex B).toPreAbstractSimplicialComplex where
  toFun := Sigma.map id f
  map_face' := by
    intro σ hσ
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex] at hσ ⊢
    refine ⟨Finset.image_nonempty.mpr hσ.1, ?_⟩
    intro v hv w hw heq
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg (fun v : Σ i, A i => (⟨v.1, f v.1 v.2⟩ : Σ i, B i))
      (eq_of_mem_joinComplex A hσ hv' hw' heq)

@[simp]
theorem joinComplexMap_apply [DecidableEq (Σ i, B i)] (f : ∀ i, A i → B i)
    (v : Σ i, A i) : joinComplexMap f v = ⟨v.1, f v.1 v.2⟩ :=
  (rfl)

/-- The identity family map induces the identity simplicial map. -/
@[simp]
theorem joinComplexMap_id [DecidableEq (Σ i, A i)] :
    joinComplexMap (fun _ x => x) =
      SimplicialMap.id (joinComplex A).toPreAbstractSimplicialComplex := by
  apply DFunLike.ext
  intro v
  simp

/-- The family construction respects composition strictly. -/
@[simp]
theorem joinComplexMap_comp [DecidableEq (Σ i, B i)] [DecidableEq (Σ i, C i)]
    (g : ∀ i, B i → C i) (f : ∀ i, A i → B i) :
    (joinComplexMap g).comp (joinComplexMap f) = joinComplexMap (fun i x => g i (f i x)) := by
  apply DFunLike.ext
  intro v
  simp

variable (A)

/-- The inclusion of the subjoin on a subset of indices. Taking a finite subset gives the
finite-index subjoins of the countable join. -/
def subjoinInclusion [DecidableEq (Σ i, A i)] (s : Set I) :
    SimplicialMap (joinComplex (fun i : s => A i)).toPreAbstractSimplicialComplex
      (joinComplex A).toPreAbstractSimplicialComplex where
  toFun := Sigma.map Subtype.val (fun _ => id)
  map_face' := by
    intro σ hσ
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex] at hσ ⊢
    refine ⟨Finset.image_nonempty.mpr hσ.1, ?_⟩
    intro v hv w hw heq
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg (fun v : Σ i : s, A i => (⟨v.1.1, v.2⟩ : Σ i, A i))
      (eq_of_mem_joinComplex _ hσ hv' hw' (Subtype.ext heq))

@[simp]
theorem subjoinInclusion_apply [DecidableEq (Σ i, A i)] (s : Set I)
    (v : Σ i : s, A i) : subjoinInclusion A s v = ⟨v.1.1, v.2⟩ :=
  (rfl)

/-- Subjoin inclusions are injective on vertices. -/
theorem subjoinInclusion_injective [DecidableEq (Σ i, A i)] (s : Set I) :
    Function.Injective (subjoinInclusion A s) :=
  Subtype.val_injective.sigma_map (fun _ => Function.injective_id)

/-- Barycentric coordinates of the join are nonnegative, sum to one, and have at most one
nonzero coordinate at each index. -/
@[simp]
theorem mem_joinComplex_realization_iff {x : (Σ i, A i) →₀ ℝ} :
    x ∈ (standardGeometricComplex (joinComplex A)).space ↔
      (∀ v, 0 ≤ x v) ∧ x.sum (fun _ r => r) = 1 ∧
        Set.InjOn Sigma.fst (x.support : Set (Σ i, A i)) := by
  classical
  -- Match the classical vertex equality used by the standard simplex coordinate API.
  let : DecidableEq (Σ i, A i) := Classical.decEq _
  constructor
  · intro hx
    let y : Realization (joinComplex A) := ⟨x, hx⟩
    exact ⟨Realization.nonneg _ y, Realization.sum_eq_one _ y,
      (mem_joinComplex_iff A).mp (support_mem _ y) |>.2⟩
  · rintro ⟨hnonneg, hsum, hinj⟩
    have hne : x.support.Nonempty := by
      apply Finsupp.support_nonempty_iff.mpr
      intro hzero
      simp [hzero] at hsum
    apply mem_realization_iff.mpr
    refine ⟨x.support, (mem_joinComplex_iff A).mpr ⟨hne, hinj⟩, ?_⟩
    rw [Finset.coe_image, mem_standardSimplex_iff]
    exact ⟨hnonneg, hsum, Finset.Subset.rfl⟩

end TauCeti.SimplicialComplex
