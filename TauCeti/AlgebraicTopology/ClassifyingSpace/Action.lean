/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CountableJoin
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The free action on Milnor's countable join

A group `G` acts on the vertices `⟨i, h⟩` of the countable join of copies of `G` by left
multiplication of the label, `g • ⟨i, h⟩ = ⟨i, g * h⟩`. This relabelling is a simplicial
automorphism of the join, so it extends affinely over each simplex to an action of `G` on
`universalGSpace G` by homeomorphisms. In barycentric coordinates,
`(g • x) ⟨i, h⟩ = x ⟨i, g⁻¹ * h⟩`.

The action is free, and it has the local disjointness asked of the domain of a quotient covering
map. The open star of a vertex `v`, the set of points whose `v`-coordinate is positive, is carried
by `g` onto the open star of `⟨v.1, g * v.2⟩`. If `g ≠ 1` these are open stars of two distinct
vertices over the same index, and they are disjoint because the carrier of a point of a join
contains at most one vertex over each index.

## Main definitions

* `TauCeti.instMulActionUniversalGSpace`: the action of `G` on `universalGSpace G`.

## Main results

* `TauCeti.universalGSpace_smul_apply`: the action on barycentric coordinates.
* `TauCeti.instContinuousConstSMulUniversalGSpace`: each translation is continuous.
* `TauCeti.smul_mem_openStarRealization_universalGSpace_iff`: translation permutes open stars.
* `TauCeti.eq_one_of_image_smul_openStarRealization_inter_nonempty`: the translates of an open
  star by distinct group elements are disjoint.
* `TauCeti.instIsCancelSMulUniversalGSpace`: the action is free.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open AbstractSimplicialComplex

namespace TauCeti

universe u

variable {G : Type u} [Group G]

/-- A group acts on Milnor's countable join of copies of itself through the simplicial
automorphisms `⟨i, h⟩ ↦ ⟨i, g * h⟩`, extended affinely over each simplex. -/
instance instSMulUniversalGSpace : SMul G (universalGSpace G) where
  smul g :=
    -- `indexedJoinMap` is typed with the classical decidable equality of its vertex type, which
    -- over `ℕ` is not the instance found by default, so both factors are made classical here.
    letI : DecidableEq ℕ := Classical.decEq ℕ
    letI : DecidableEq G := Classical.decEq G
    (indexedJoinMap (A := fun _ : ℕ => G) (B := fun _ : ℕ => G)
      id Function.injective_id (fun _ h => g * h)).realizationMap

/-- Translation pushes barycentric coordinates forward along left multiplication of labels. -/
theorem universalGSpace_smul_val (g : G) (x : universalGSpace G) :
    ((g • x : universalGSpace G) : (Σ _ : ℕ, G) →₀ ℝ) =
      Finsupp.mapDomain (fun v => ⟨v.1, g * v.2⟩) x.1 := by
  -- Match the classical decidable equality fixed in `instSMulUniversalGSpace`.
  let : DecidableEq ℕ := Classical.decEq ℕ
  let : DecidableEq G := Classical.decEq G
  exact (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val
    (indexedJoinMap (A := fun _ : ℕ => G) (B := fun _ : ℕ => G)
      id Function.injective_id (fun _ h => g * h)) x).trans
    (congrArg (Finsupp.mapDomain · x.1)
      (funext (indexedJoinMap_apply (A := fun _ : ℕ => G) (B := fun _ : ℕ => G)
        id Function.injective_id (fun _ h => g * h))))

/-- The barycentric coordinate of a translate at a vertex is the coordinate of the original point
at the vertex obtained by translating the label back. -/
@[simp]
theorem universalGSpace_smul_apply (g : G) (x : universalGSpace G) (v : Σ _ : ℕ, G) :
    (g • x : universalGSpace G).1 v = x.1 ⟨v.1, g⁻¹ * v.2⟩ := by
  have hinj : Function.Injective fun w : Σ _ : ℕ, G => (⟨w.1, g * w.2⟩ : Σ _ : ℕ, G) :=
by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    simpa using h
  rw [universalGSpace_smul_val]
  simpa using Finsupp.mapDomain_apply_of_injective hinj x.1 ⟨v.1, g⁻¹ * v.2⟩

/-- The action of a group on Milnor's countable join of copies of itself by relabelling
vertices. -/
instance instMulActionUniversalGSpace : MulAction G (universalGSpace G) where
  one_smul x := Subtype.ext <| Finsupp.ext fun v => by simp
  mul_smul g h x := Subtype.ext <| Finsupp.ext fun v => by simp [mul_assoc]

/-- Translation sends a vertex of the countable join to the vertex with translated label. -/
@[simp]
theorem universalGSpace_smul_vertex (g : G) (v : Σ _ : ℕ, G) :
    g • (indexedJoin fun _ : ℕ => G).vertex v =
      (indexedJoin fun _ : ℕ => G).vertex ⟨v.1, g * v.2⟩ :=
  Subtype.ext <| by rw [universalGSpace_smul_val, vertex_val, vertex_val, Finsupp.mapDomain_single]

/-- Translating the base point of the countable join gives the vertex over index zero labelled by
the translating element. -/
theorem smul_universalGSpaceBasepoint (g : G) :
    g • universalGSpaceBasepoint G = (indexedJoin fun _ : ℕ => G).vertex ⟨0, g⟩ :=
  Subtype.ext <| by
    rw [universalGSpace_smul_val, universalGSpaceBasepoint_val, vertex_val,
      Finsupp.mapDomain_single, mul_one]

/-- Each translation of Milnor's countable join is continuous. -/
instance instContinuousConstSMulUniversalGSpace :
    ContinuousConstSMul G (universalGSpace G) where
  continuous_const_smul g :=
    letI : DecidableEq ℕ := Classical.decEq ℕ
    letI : DecidableEq G := Classical.decEq G
    (indexedJoinMap (A := fun _ : ℕ => G) (B := fun _ : ℕ => G)
      id Function.injective_id (fun _ h => g * h)).realizationMap.continuous

/-- A translate lies in the open star of a vertex exactly when the original point lies in the open
star of the vertex with translated-back label. -/
theorem smul_mem_openStarRealization_universalGSpace_iff (g : G) (x : universalGSpace G)
    (v : Σ _ : ℕ, G) :
    g • x ∈ (indexedJoin fun _ : ℕ => G).openStarRealization v ↔
      x ∈ (indexedJoin fun _ : ℕ => G).openStarRealization ⟨v.1, g⁻¹ * v.2⟩ := by
  simp only [mem_openStarRealization, universalGSpace_smul_apply]

/-- The translates of the open star of a vertex by distinct group elements are disjoint: a point
of the countable join cannot have positive coordinates at two distinct vertices over the same
index. -/
theorem eq_one_of_image_smul_openStarRealization_inter_nonempty (g : G) (v : Σ _ : ℕ, G)
    (h : ((g • ·) '' (indexedJoin fun _ : ℕ => G).openStarRealization v ∩
      (indexedJoin fun _ : ℕ => G).openStarRealization v).Nonempty) : g = 1 := by
  obtain ⟨_, ⟨y, hy, rfl⟩, hgy⟩ := h
  rw [smul_mem_openStarRealization_universalGSpace_iff, mem_openStarRealization] at hgy
  rw [mem_openStarRealization] at hy
  by_contra hg
  have hne : (⟨v.1, g⁻¹ * v.2⟩ : Σ _ : ℕ, G) ≠ v := fun hv =>
    hg (inv_eq_one.mp (mul_eq_right.mp (congrArg Sigma.snd hv)))
  rcases realization_apply_eq_zero_of_fst_eq (x := y) (v := ⟨v.1, g⁻¹ * v.2⟩) (w := v) rfl hne
    with h0 | h0
  · exact hgy.ne' h0
  · exact hy.ne' h0

/-- The action of a group on Milnor's countable join of copies of itself is free. -/
instance instIsCancelSMulUniversalGSpace : IsCancelSMul G (universalGSpace G) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun g x hgx => by
    obtain ⟨v, hv⟩ := (indexedJoin fun _ : ℕ => G).exists_mem_openStarRealization x
    exact eq_one_of_image_smul_openStarRealization_inter_nonempty g v
      ⟨x, ⟨x, hv, hgx⟩, hv⟩

end TauCeti

namespace MonoidHom

open TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- The map of Milnor total spaces induced by a homomorphism is equivariant for that
homomorphism. -/
@[simp]
theorem universalGSpaceMap_smul (φ : G →* H) (g : G) (x : universalGSpace G) :
    φ.universalGSpaceMap (g • x) = φ g • φ.universalGSpaceMap x := by
  apply Subtype.ext
  simp only [universalGSpaceMap_val, universalGSpace_smul_val, ← Finsupp.mapDomain_comp]
  congr 1
  funext v
  simp

end MonoidHom
