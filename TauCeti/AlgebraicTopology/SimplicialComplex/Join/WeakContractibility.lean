/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Indexed
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Cone
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction

/-!
# Weak contractibility of indexed joins

Every map from a compact space into an indexed join uses only finitely many vertices.  If
nonempty members occur at infinitely many indices, a vertex over an unused index turns that
finite restriction into a cone.  This gives a nullhomotopy of the map inside the full join.

## Main results

* `TauCeti.isCone_restrict_indexedJoin_insert`: adjoining a vertex over a fresh index makes a
  finite vertex restriction of an indexed join a cone.
* `TauCeti.ContinuousMap.exists_homotopy_to_const_to_indexedJoin`: every map with compact image
  to such an indexed join contracts in a way that preserves its fibers.
* `TauCeti.ContinuousMap.nullhomotopic_to_indexedJoin`: the resulting nullhomotopy statement.
-/

public section

noncomputable section

open Set Topology
open AbstractSimplicialComplex

namespace TauCeti

universe u v w

variable {ι : Type u} {A : ι → Type v}

attribute [local instance] Classical.decEq
attribute [-instance] Sigma.instDecidableEqSigma instDecidableEqSigma

private def restrictSubsetMap (K : AbstractSimplicialComplex (Σ i, A i))
    {s t : Set (Σ i, A i)} (hst : s ⊆ t) :
    PreAbstractSimplicialComplex.SimplicialMap
      (K.restrict s).toPreAbstractSimplicialComplex
      (K.restrict t).toPreAbstractSimplicialComplex where
  toFun x := ⟨x, hst x.2⟩
  map_face' := by
    intro σ hσ
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
      mem_restrict_iff] at hσ ⊢
    have himage :
        (σ.image (fun x : s => (⟨x.1, hst x.2⟩ : t))).image Subtype.val =
          σ.image Subtype.val := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro x hx
      rfl
    rw [himage]
    exact hσ

/-- Adjoining a vertex over an index absent from a finite vertex set makes the corresponding
restriction of an indexed join a cone. -/
theorem isCone_restrict_indexedJoin_insert (V : Finset (Σ i, A i)) (i : ι) (a : A i)
    (hi : i ∉ V.image Sigma.fst) :
    PreAbstractSimplicialComplex.IsCone
      ((indexedJoin A).restrict ((V : Set (Σ i, A i)) ∪ {⟨i, a⟩})).toPreAbstractSimplicialComplex
      ⟨⟨i, a⟩, Set.mem_union_right _ (Set.mem_singleton _)⟩ := by
  let v : Σ i, A i := ⟨i, a⟩
  let S : Set (Σ i, A i) := (V : Set (Σ i, A i)) ∪ {v}
  let vS : S := ⟨v, Set.mem_union_right _ (Set.mem_singleton _)⟩
  change PreAbstractSimplicialComplex.IsCone
    ((indexedJoin A).restrict S).toPreAbstractSimplicialComplex vS
  refine ⟨(indexedJoin A).restrict S |>.singleton_mem vS, ?_⟩
  intro σ hσ
  rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
    mem_restrict_iff] at hσ ⊢
  rw [Finset.image_insert]
  change insert v (σ.image Subtype.val) ∈ indexedJoin A
  by_cases hv : v ∈ σ.image Subtype.val
  · rw [Finset.insert_eq_of_mem hv]
    exact hσ
  rw [mem_indexedJoin_iff] at hσ ⊢
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.coe_insert]
  intro x hx y hy hxy
  rw [Set.mem_insert_iff] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · exfalso
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hwS : (w : Σ i, A i) ∈ S := w.2
      rcases hwS with hwV | hwv
      · apply hi
        exact Finset.mem_image.mpr ⟨w, hwV, hxy.symm⟩
      · apply hv
        have hwv' : (w : Σ i, A i) = v := by simpa [v] using hwv
        exact Finset.mem_image.mpr ⟨w, hw, hwv'⟩
  · rcases hy with rfl | hy
    · exfalso
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      have hwS : (w : Σ i, A i) ∈ S := w.2
      rcases hwS with hwV | hwv
      · apply hi
        exact Finset.mem_image.mpr ⟨w, hwV, hxy⟩
      · apply hv
        have hwv' : (w : Σ i, A i) = v := by simpa [v] using hwv
        exact Finset.mem_image.mpr ⟨w, hw, hwv'⟩
    · exact hσ.2 hx hy hxy

namespace ContinuousMap

variable {X : Type w} [TopologicalSpace X]

/-- Every continuous map with compact image into an indexed join contracts when nonempty family
members occur at infinitely many indices.  The contraction preserves fibers of the original
map; in particular, a subset on which the map is constant traces a single path during the
homotopy. -/
theorem exists_homotopy_to_const_to_indexedJoin
    (f : C(X, (indexedJoin A).Realization))
    (hf : IsCompact (Set.range f))
    (hA : {i | Nonempty (A i)}.Infinite) :
    ∃ y, ∃ H : f.Homotopy (ContinuousMap.const X y),
      ∀ t x x', f x = f x' → H (t, x) = H (t, x') := by
  let K := indexedJoin A
  obtain ⟨V, g, hg⟩ := K.exists_finite_restrict_factorization f hf
  obtain ⟨i, hiA, hiV⟩ := hA.exists_notMem_finset (V.image Sigma.fst)
  obtain ⟨a⟩ := hiA
  let S : Set (Σ i, A i) := (V : Set (Σ i, A i)) ∪ {⟨i, a⟩}
  have hVS : (V : Set (Σ i, A i)) ⊆ S := Set.subset_union_left
  let e := restrictSubsetMap K hVS
  let q : C(X, (K.restrict S).Realization) := e.realizationMap.comp g
  have hcone : PreAbstractSimplicialComplex.IsCone
      (K.restrict S).toPreAbstractSimplicialComplex
      ⟨⟨i, a⟩, Set.mem_union_right _ (Set.mem_singleton _)⟩ :=
    isCone_restrict_indexedJoin_insert V i a hiV
  have he : (K.restrictInclusion S).realizationMap.comp e.realizationMap =
      (K.restrictInclusion (V : Set (Σ i, A i))).realizationMap := by
    rw [← PreAbstractSimplicialComplex.SimplicialMap.realizationMap_comp]
    congr 1
    apply PreAbstractSimplicialComplex.SimplicialMap.ext
    funext x
    calc
      ((K.restrictInclusion S).comp e).toFun x = K.restrictInclusion S (e x) :=
        PreAbstractSimplicialComplex.SimplicialMap.comp_apply _ _ x
      _ = (e x).1 := congrFun (K.coe_restrictInclusion S) (e x)
      _ = x.1 := by rfl
      _ = K.restrictInclusion (V : Set (Σ i, A i)) x :=
        (congrFun (K.coe_restrictInclusion (V : Set (Σ i, A i))) x).symm
  have hf : (K.restrictInclusion S).realizationMap.comp q = f := by
    change (K.restrictInclusion S).realizationMap.comp (e.realizationMap.comp g) = f
    rw [← ContinuousMap.comp_assoc, he, hg]
  let vS : S := ⟨⟨i, a⟩, Set.mem_union_right _ (Set.mem_singleton _)⟩
  let j := (K.restrictInclusion S).realizationMap
  let y := j ((K.restrict S).vertex vS)
  let H : f.Homotopy (ContinuousMap.const X y) := {
    toFun p := j (coneContraction hcone (p.1, q p.2))
    continuous_toFun := by fun_prop
    map_zero_left x := by
      dsimp only [j]
      calc
        _ = (K.restrictInclusion S).realizationMap (q x) :=
          congrArg (K.restrictInclusion S).realizationMap
            ((coneContraction hcone).map_zero_left (q x))
        _ = f x := by
          simpa only [ContinuousMap.comp_apply] using DFunLike.congr_fun hf x
    map_one_left x := by
      dsimp only [j, y]
      calc
        _ = (K.restrictInclusion S).realizationMap ((K.restrict S).vertex vS) :=
          congrArg (K.restrictInclusion S).realizationMap
            ((coneContraction hcone).map_one_left (q x)) }
  refine ⟨y, H, ?_⟩
  intro t x x' hxx'
  have hqxx' : q x = q x' := by
    apply (K.isClosedEmbedding_restrictInclusion_realizationMap S).injective
    rw [← ContinuousMap.comp_apply, hf, ← ContinuousMap.comp_apply, hf, hxx']
  change j (coneContraction hcone (t, q x)) =
    j (coneContraction hcone (t, q x'))
  rw [hqxx']

/-- Every continuous map with compact image into an indexed join is nullhomotopic when
nonempty family members occur at infinitely many indices. -/
theorem nullhomotopic_to_indexedJoin
    (f : C(X, (indexedJoin A).Realization))
    (hf : IsCompact (Set.range f))
    (hA : {i | Nonempty (A i)}.Infinite) : f.Nullhomotopic := by
  obtain ⟨y, H, -⟩ := exists_homotopy_to_const_to_indexedJoin f hf hA
  exact ⟨y, ⟨H⟩⟩

end ContinuousMap

end TauCeti
