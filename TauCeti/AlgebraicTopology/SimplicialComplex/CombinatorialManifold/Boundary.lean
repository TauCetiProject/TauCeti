/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Link
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Link

/-!
# The boundary of a combinatorial manifold

A vertex of a combinatorial `(n + 1)`-manifold is an interior vertex when its link is a
combinatorial `n`-sphere and a boundary vertex when its link is a combinatorial `n`-ball; more
generally, a face `σ` of a combinatorial manifold lies in the boundary precisely when `link K σ` is
a combinatorial ball. This file defines the boundary subcomplex `K.boundary` of a
`PreAbstractSimplicialComplex` and proves that the boundary of a combinatorial `(n + 1)`-manifold is
a closed combinatorial `n`-manifold: in dimension `1` its vertex links are void (`0`-manifold), in
higher dimensions `n + 2` every vertex link in `K.boundary` is a combinatorial `n`-sphere, and in
every dimension `K.boundary.boundary = ⊥`.

To define `K.boundary` as a `PreAbstractSimplicialComplex` without bundling a manifold hypothesis
into the carrier, its faces are the faces `σ ∈ K` all of whose nonempty subsets `τ ⊆ σ` have
combinatorial-ball links in `K`. Downward closure is then immediate for arbitrary precomplexes,
while on any combinatorial manifold the subface condition is automatic: if `τ ⊂ σ` had a spherical
link, then `link K σ = link (link K τ) (σ \ τ)` would also be a combinatorial sphere
(`IsCombinatorialSphere.isCombinatorialSphere_link`), contradicting
`IsCombinatorialSphere.not_isCombinatorialBall`.

Boundary formation commutes with injective relabelings (`map_boundary`) and with stellar subdivision
at a fresh vertex (`IsCombinatorialManifold.boundary_stellarSubdivision`). Combined with
`(simplex V).boundary = simplexBoundary V`, this shows that the boundary of a combinatorial
`(n + 1)`-ball is a combinatorial `n`-sphere (`IsCombinatorialBall.isCombinatorialSphere_boundary`).
Since `link K.boundary {v} = (link K {v}).boundary` at every vertex `v`
(`IsCombinatorialManifold.link_boundary_singleton`), the manifold structure of `K.boundary` follows
immediately from the ball link of each boundary vertex `v` in `K`.

## Main definitions

* `PreAbstractSimplicialComplex.boundary`: the boundary subcomplex of faces whose nonempty subfaces
  have combinatorial-ball links.

## Main results

* `PreAbstractSimplicialComplex.singleton_mem_boundary_iff` and
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.mem_boundary_iff`: vertex and face
  characterizations of boundary membership.
* `PreAbstractSimplicialComplex.boundary_simplex` and
  `PreAbstractSimplicialComplex.IsCombinatorialSphere.boundary_eq_bot`: boundaries of standard
  simplices and combinatorial spheres.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.boundary_stellarSubdivision` and
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.stellarEquivalentUpToRelabeling_boundary`:
  interaction of the boundary with stellar moves and intrinsic stellar equivalence.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialSphere_boundary`: the boundary of
  a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.link_boundary_singleton`: at every vertex,
  the link in the boundary is the boundary of the link.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.isCombinatorialManifold_boundary`,
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.isCombinatorialSphere_link_boundary`, and
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.boundary_boundary_eq_bot`: the boundary of a
  combinatorial `(n + 1)`-manifold is a closed combinatorial `n`-manifold.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.mem_boundary_iff_exists_ridge`: a face of a
  combinatorial `(n + 1)`-manifold lies in the boundary iff it is contained in a codimension-one
  face whose link is a single vertex.

## References

* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320, Proposition 3.3.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

section General

variable {ι : Type*} [DecidableEq ι]
  {K L : PreAbstractSimplicialComplex ι} {σ τ : Finset ι} {v : ι} {n : ℕ}

/-- The **combinatorial boundary** of a pre-abstract simplicial complex: the subcomplex of faces
`σ ∈ K` all of whose nonempty subsets have combinatorial-ball links in `K`. On a combinatorial
manifold the condition on proper subsets is automatic (`IsCombinatorialManifold.mem_boundary_iff`),
so `σ ∈ K.boundary` means simply that `σ ∈ K` and `link K σ` is a combinatorial ball. -/
def boundary (K : PreAbstractSimplicialComplex ι) : PreAbstractSimplicialComplex ι where
  faces := {σ | σ ∈ K ∧ ∀ ⦃τ⦄, τ.Nonempty → τ ⊆ σ → ∃ k, IsCombinatorialBall (link K τ) k}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, hsub⟩
    refine ⟨(K.isRelLowerSet_faces hσ).1, fun {ρ} hρσ hρ =>
      ⟨(K.isRelLowerSet_faces hσ).2 hρσ hρ, fun _ hτ hτρ => hsub hτ (hτρ.trans hρσ)⟩⟩

/-- Defining characterization of membership in the boundary subcomplex. -/
theorem mem_boundary_def :
    σ ∈ K.boundary ↔
      σ ∈ K ∧ ∀ ⦃τ⦄, τ.Nonempty → τ ⊆ σ → ∃ k, IsCombinatorialBall (link K τ) k :=
  (Iff.rfl)

/-- The boundary of a complex is a subcomplex. -/
theorem boundary_le : K.boundary ≤ K :=
  fun _ hσ => (mem_boundary_def.mp hσ).1

/-- A vertex belongs to the boundary precisely when it is a vertex of `K` whose link is a
combinatorial ball. -/
@[simp]
theorem singleton_mem_boundary_iff :
    ({v} : Finset ι) ∈ K.boundary ↔
      ({v} : Finset ι) ∈ K ∧ ∃ k, IsCombinatorialBall (link K {v}) k := by
  rw [mem_boundary_def]
  refine ⟨fun ⟨hv, h⟩ => ⟨hv, h (singleton_nonempty v) Subset.rfl⟩, fun ⟨hv, hb⟩ => ⟨hv, ?_⟩⟩
  intro τ hτne hτsub
  obtain rfl := hτne.subset_singleton_iff.mp hτsub
  exact hb

/-- The void complex has void boundary. -/
@[simp]
theorem boundary_bot : (⊥ : PreAbstractSimplicialComplex ι).boundary = ⊥ :=
  eq_bot_iff.mpr (boundary_le (K := ⊥))

/-- An injective vertex map commutes with taking the boundary subcomplex. -/
@[simp]
theorem map_boundary {κ : Type*} [DecidableEq κ] (f : ι → κ) (hf : Function.Injective f) :
    K.boundary.map f = (K.map f).boundary := by
  refine SetLike.ext fun ω => ?_
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨hσK, hsub⟩ := mem_boundary_def.mp hσ
    refine mem_boundary_def.mpr ⟨mem_map_iff.mpr ⟨σ, hσK, rfl⟩, fun ρ hρne hρsub => ?_⟩
    obtain ⟨τ, hτσ, rfl⟩ := subset_image_iff.mp hρsub
    obtain ⟨k, hk⟩ := hsub (image_nonempty.mp hρne) hτσ
    refine ⟨k, ?_⟩
    rw [← map_link f hf, isCombinatorialBall_map_iff f hf]
    exact hk
  · intro hω
    obtain ⟨hωK, hsub⟩ := mem_boundary_def.mp hω
    obtain ⟨σ, hσK, rfl⟩ := mem_map_iff.mp hωK
    refine mem_map_iff.mpr ⟨σ, mem_boundary_def.mpr ⟨hσK, fun τ hτne hτσ => ?_⟩, rfl⟩
    obtain ⟨k, hk⟩ := hsub (hτne.image f) (image_subset_image hτσ)
    rw [← map_link f hf, isCombinatorialBall_map_iff f hf] at hk
    exact ⟨k, hk⟩

/-- On a combinatorial manifold, a face belongs to the boundary if and only if its link is a
combinatorial ball; the ball-link condition on proper nonempty faces is automatic. -/
theorem IsCombinatorialManifold.mem_boundary_iff (hK : IsCombinatorialManifold K n) :
    σ ∈ K.boundary ↔ σ ∈ K ∧ ∃ k, IsCombinatorialBall (link K σ) k := by
  rw [mem_boundary_def]
  refine ⟨fun ⟨hσ, h⟩ => ⟨hσ, h (K.isRelLowerSet_faces hσ).1 Subset.rfl⟩,
    fun ⟨hσ, k, hball⟩ => ⟨hσ, fun τ hτne hτσ => ?_⟩⟩
  have hσcard : σ.card ≤ n := by
    have hle := hK.isPure.card_le hσ
    have hne : σ.card ≠ n + 1 := fun hc => hball.ne_bot ((hK.link_eq_bot_iff hσ).mpr hc)
    omega
  have hτK : τ ∈ K := (K.isRelLowerSet_faces hσ).2 hτσ hτne
  have hτcard : τ.card ≤ n := (card_le_card hτσ).trans hσcard
  by_cases hτeq : τ = σ
  · exact hτeq ▸ ⟨k, hball⟩
  · rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hτK hτcard with hs | hb
    · have hρne : (σ \ τ).Nonempty := sdiff_nonempty.mpr fun h => hτeq (Subset.antisymm hτσ h)
      have hρmem : σ \ τ ∈ link K τ := mem_link_nonempty.mpr
        ⟨hρne, sdiff_disjoint, by rwa [sdiff_union_of_subset hτσ]⟩
      have hρcard : (σ \ τ).card ≤ n - τ.card := by
        rw [card_sdiff_of_subset hτσ]
        omega
      have hs_σ := hs.isCombinatorialSphere_link hρmem hρcard
      rw [link_link disjoint_sdiff_self_right, union_sdiff_of_subset hτσ] at hs_σ
      exact (hs_σ.not_isCombinatorialBall hball).elim
    · exact ⟨n - τ.card, hb⟩

/-- On a combinatorial `n`-manifold, a face `σ` belongs to the boundary if and only if `σ ∈ K`,
`σ.card ≤ n`, and `link K σ` is a combinatorial `(n - σ.card)`-ball. -/
theorem IsCombinatorialManifold.mem_boundary_iff_isCombinatorialBall
    (hK : IsCombinatorialManifold K n) :
    σ ∈ K.boundary ↔ σ ∈ K ∧ σ.card ≤ n ∧ IsCombinatorialBall (link K σ) (n - σ.card) := by
  rw [hK.mem_boundary_iff]
  refine ⟨fun ⟨hσ, k, hball⟩ => ?_, fun ⟨hσ, _, hball⟩ => ⟨hσ, n - σ.card, hball⟩⟩
  have hσcard : σ.card ≤ n := by
    have hle := hK.isPure.card_le hσ
    have hne : σ.card ≠ n + 1 := fun hc => hball.ne_bot ((hK.link_eq_bot_iff hσ).mpr hc)
    omega
  have hkeq : k = n - σ.card := by
    have hd₁ := hball.dimension_eq
    have hd₂ := hK.dimension_link hσ hσcard
    exact_mod_cast hd₁.symm.trans hd₂
  exact ⟨hσ, hσcard, hkeq ▸ hball⟩

/-- In a combinatorial `(n + 1)`-manifold, a vertex belongs to the boundary if and only if its
link is a combinatorial `n`-ball. -/
theorem IsCombinatorialManifold.singleton_mem_boundary_succ_iff
    (hK : IsCombinatorialManifold K (n + 1)) :
    ({v} : Finset ι) ∈ K.boundary ↔ ({v} : Finset ι) ∈ K ∧ IsCombinatorialBall (link K {v}) n := by
  simpa using hK.mem_boundary_iff_isCombinatorialBall (σ := {v})

/-- A non-maximal face of a combinatorial `n`-manifold lies outside the boundary if and only if
its link is a combinatorial `(n - σ.card)`-sphere. -/
theorem IsCombinatorialManifold.notMem_boundary_iff_isCombinatorialSphere
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    σ ∉ K.boundary ↔ IsCombinatorialSphere (link K σ) (n - σ.card) := by
  rw [hK.mem_boundary_iff]
  rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard with hs | hb
  · exact ⟨fun _ => hs, fun _ ⟨_, _, hball⟩ => hs.not_isCombinatorialBall hball⟩
  · exact ⟨fun hnot => (hnot ⟨hσ, _, hb⟩).elim, fun hs => (hs.not_isCombinatorialBall hb).elim⟩

/-- A zero-dimensional combinatorial manifold has void boundary. -/
theorem IsCombinatorialManifold.boundary_eq_bot_zero (hK : IsCombinatorialManifold K 0) :
    K.boundary = ⊥ := by
  refine eq_bot_iff.mpr fun σ hσ => ?_
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces (boundary_le hσ)).1
  obtain ⟨_, _, hbv⟩ := singleton_mem_boundary_iff.mp (singleton_mem_of_mem hσ hv)
  exact hbv.ne_bot
    (isCombinatorialManifold_zero_iff.mp hK (singleton_mem_of_mem (boundary_le hσ) hv))

/-- Every combinatorial sphere has void boundary. -/
theorem IsCombinatorialSphere.boundary_eq_bot (hK : IsCombinatorialSphere K n) :
    K.boundary = ⊥ := by
  cases n with
  | zero => exact hK.isCombinatorialManifold.boundary_eq_bot_zero
  | succ n =>
    refine eq_bot_iff.mpr fun σ hσ => ?_
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces (boundary_le hσ)).1
    obtain ⟨hvK, _, hball⟩ := singleton_mem_boundary_iff.mp (singleton_mem_of_mem hσ hv)
    exact (hK.isCombinatorialSphere_link_singleton hvK).not_isCombinatorialBall hball

/-- The boundary of any standard simplex is its `simplexBoundary`, including the empty and
one-vertex cases. -/
@[simp]
theorem boundary_simplex (V : Finset ι) : (simplex V).boundary = simplexBoundary V := by
  by_cases hle : V.card ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain rfl := card_eq_zero.mp h0
      simp
    · obtain ⟨v, rfl⟩ := card_eq_one.mp h1
      rw [simplexBoundary_singleton]
      exact (isCombinatorialManifold_simplex h1).boundary_eq_bot_zero
  · have hM : IsCombinatorialManifold (simplex V) (V.card - 1) :=
      isCombinatorialManifold_simplex (by omega)
    refine SetLike.ext fun σ => ?_
    rw [hM.mem_boundary_iff, mem_simplex, mem_simplexBoundary]
    constructor
    · rintro ⟨⟨hne, hsub⟩, _, hball⟩
      refine ⟨hne, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => ?_⟩⟩
      subst heq
      exact hball.ne_bot link_simplex_self
    · rintro ⟨hne, hproper⟩
      refine ⟨⟨hne, hproper.subset⟩, (V \ σ).card - 1, ?_⟩
      rw [link_simplex hproper.subset]
      have : 1 ≤ (V \ σ).card := card_pos.mpr (sdiff_nonempty.mpr hproper.not_superset)
      exact isCombinatorialBall_simplex (by omega)

/-- The boundary of a standard simplex boundary is void. -/
@[simp]
theorem boundary_simplexBoundary (V : Finset ι) : (simplexBoundary V).boundary = ⊥ := by
  by_cases hle : V.card ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain rfl := card_eq_zero.mp h0
      simp
    · obtain ⟨v, rfl⟩ := card_eq_one.mp h1
      simp
  · exact (isCombinatorialSphere_simplexBoundary (n := V.card - 2) (by omega)).boundary_eq_bot

/-! ### Stellar moves on the boundary -/

private theorem link_stellarSubdivision_insert_map_eq_join
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) {ρ : Finset ι}
    (hvρ : v ∉ ρ) (hnot : ¬ σ ⊆ ρ) (hρσ : ρ ∪ σ ∈ K) :
    (link (stellarSubdivision K σ v) (insert v ρ)).map (TauCeti.partitionEmbedding (· ∈ σ)) =
      join (simplexBoundary (σ \ ρ)) (link K (ρ ∪ σ)) := by
  let e := TauCeti.partitionEmbedding (· ∈ σ)
  rw [link_stellarSubdivision_insert hv hvρ, map_link e e.injective,
    map_closedStar_inf_deletion_eq_join hσ, image_partitionEmbedding]
  have hf₁ : ρ.filter (· ∈ σ) = ρ ∩ σ := filter_mem_eq_inter
  have hf₂ : ρ.filter (fun x => x ∉ σ) = ρ \ σ := filter_notMem_eq_sdiff
  rw [hf₁, hf₂]
  have hs : ρ ∩ σ = ∅ ∨ ρ ∩ σ ∈ simplexBoundary σ := by
    by_cases h : ρ ∩ σ = ∅
    · exact Or.inl h
    · exact Or.inr (mem_simplexBoundary.mpr ⟨nonempty_iff_ne_empty.mpr h,
        Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_right, fun heq =>
          hnot (heq ▸ inter_subset_left)⟩⟩)
  have ht : ρ \ σ = ∅ ∨ ρ \ σ ∈ link K σ := by
    by_cases h : ρ \ σ = ∅
    · exact Or.inl h
    · exact Or.inr (mem_link_nonempty.mpr ⟨nonempty_iff_ne_empty.mpr h,
        sdiff_disjoint, by rwa [sdiff_union_self_eq_union]⟩)
  rw [link_join hs ht, link_simplexBoundary inter_subset_right, sdiff_inter_self_right,
    link_link disjoint_sdiff_self_right, union_comm σ (ρ \ σ), sdiff_union_self_eq_union]

private theorem exists_isCombinatorialBall_join_simplexBoundary_iff
    {W : Finset ι} {M : PreAbstractSimplicialComplex ι} (hWne : W.Nonempty)
    (hM : M = ⊥ ∨ ∃ q, IsCombinatorialSphere M q ∨ IsCombinatorialBall M q) :
    (∃ k, IsCombinatorialBall (join (simplexBoundary W) M) k) ↔
      ∃ q, IsCombinatorialBall M q := by
  have hpos : 1 ≤ W.card := card_pos.mpr hWne
  rcases eq_or_lt_of_le hpos with h1 | hgt1
  · obtain ⟨w, rfl⟩ := card_eq_one.mp h1.symm
    simp only [simplexBoundary_singleton, bot_join,
      isCombinatorialBall_map_iff Sum.inr Sum.inr_injective]
  · have hsW : IsCombinatorialSphere (simplexBoundary W) (W.card - 2) :=
      isCombinatorialSphere_simplexBoundary (by omega)
    constructor
    · rintro ⟨k, hball⟩
      rcases hM with rfl | ⟨q, hsM | hbM⟩
      · rw [join_bot] at hball
        exact ((hsW.map Sum.inl Sum.inl_injective).not_isCombinatorialBall hball).elim
      · exact ((hsW.join hsM).not_isCombinatorialBall hball).elim
      · exact ⟨q, hbM⟩
    · rintro ⟨q, hbM⟩
      exact ⟨W.card - 2 + q + 1, hsW.join_ball hbM⟩

private theorem boundary_stellarSubdivision_succ_of_mem {m : ℕ}
    (hK : IsCombinatorialManifold K (m + 1)) (hσK : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    (stellarSubdivision K σ v).boundary = stellarSubdivision K.boundary σ v := by
  have hB : IsCombinatorialManifold (stellarSubdivision K σ v) (m + 1) :=
    hK.stellarSubdivision hv
  refine SetLike.ext fun τ => ?_
  by_cases hvτ : v ∈ τ
  · rw [← insert_erase hvτ]
    have hvρ : v ∉ τ.erase v := notMem_erase v τ
    rw [hB.mem_boundary_iff, insert_mem_stellarSubdivision_iff hvρ,
      insert_mem_stellarSubdivision_iff hvρ, hK.mem_boundary_iff]
    refine ⟨fun ⟨⟨hnot, hρσ⟩, hball⟩ => ⟨hnot, hρσ, ?_⟩,
      fun ⟨hnot, hρσ, hball⟩ => ⟨⟨hnot, hρσ⟩, ?_⟩⟩
    all_goals
      have hM : link K (τ.erase v ∪ σ) = ⊥ ∨ ∃ q,
          IsCombinatorialSphere (link K (τ.erase v ∪ σ)) q ∨
            IsCombinatorialBall (link K (τ.erase v ∪ σ)) q := by
        rcases eq_or_lt_of_le (hK.isPure.card_le hρσ) with htop | hlt
        · exact Or.inl ((hK.link_eq_bot_iff hρσ).mpr htop)
        · exact Or.inr ⟨m + 1 - (τ.erase v ∪ σ).card,
            hK.isCombinatorialSphere_or_isCombinatorialBall_link hρσ (by omega)⟩
      have hemb := (TauCeti.partitionEmbedding (· ∈ σ)).injective
      have hiff : (∃ k, IsCombinatorialBall (link (stellarSubdivision K σ v)
          (insert v (τ.erase v))) k) ↔
            ∃ q, IsCombinatorialBall (link K (τ.erase v ∪ σ)) q := by
        refine (exists_congr fun k => (isCombinatorialBall_map_iff _ hemb).symm).trans ?_
        rw [link_stellarSubdivision_insert_map_eq_join hσK hv hvρ hnot hρσ]
        exact exists_isCombinatorialBall_join_simplexBoundary_iff (sdiff_nonempty.mpr hnot) hM
    · exact hiff.mp hball
    · exact hiff.mpr hball
  · rw [hB.mem_boundary_iff, mem_stellarSubdivision_iff_of_notMem hvτ,
      mem_stellarSubdivision_iff_of_notMem hvτ, hK.mem_boundary_iff]
    refine ⟨fun ⟨⟨hτK, hnot⟩, k, hball⟩ => ⟨⟨hτK, ?_⟩, hnot⟩,
      fun ⟨⟨hτK, k, hball⟩, hnot⟩ => ⟨⟨hτK, hnot⟩, ?_⟩⟩
    · have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
        (fun h => hv (link_le h)) hvτ (sdiff_nonempty.mpr hnot)).stellarEquivalentUpToRelabeling
      exact ⟨k, hball.of_stellarEquivalentUpToRelabeling he⟩
    · have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
        (fun h => hv (link_le h)) hvτ
        (sdiff_nonempty.mpr hnot)).symm.stellarEquivalentUpToRelabeling
      exact ⟨k, hball.of_stellarEquivalentUpToRelabeling he⟩

/-- Boundary formation commutes with stellar subdivision at a fresh vertex on any combinatorial
manifold. This holds whether `σ` lies in the boundary, in the interior, outside `K`, or is empty. -/
theorem IsCombinatorialManifold.boundary_stellarSubdivision
    (hK : IsCombinatorialManifold K n) (hv : ({v} : Finset ι) ∉ K) :
    (PreAbstractSimplicialComplex.stellarSubdivision K σ v).boundary =
      PreAbstractSimplicialComplex.stellarSubdivision K.boundary σ v := by
  have hv' : ({v} : Finset ι) ∉ K.boundary := fun h => hv (boundary_le h)
  by_cases hσ0 : σ = ∅
  · subst hσ0
    simp
  have hσne : σ.Nonempty := nonempty_iff_ne_empty.mpr hσ0
  by_cases hσK : σ ∈ K
  · cases n with
    | zero =>
      have hB : IsCombinatorialManifold
          (PreAbstractSimplicialComplex.stellarSubdivision K σ v) 0 := hK.stellarSubdivision hv
      rw [hK.boundary_eq_bot_zero, hB.boundary_eq_bot_zero,
        stellarSubdivision_eq_self_of_notMem (Set.notMem_empty _) hσne (Set.notMem_empty _)]
    | succ m => exact boundary_stellarSubdivision_succ_of_mem hK hσK hv
  · have hσb : σ ∉ K.boundary := fun h => hσK (boundary_le h)
    rw [stellarSubdivision_eq_self_of_notMem hv hσne hσK,
      stellarSubdivision_eq_self_of_notMem hv' hσne hσb]

/-- Starring a combinatorial manifold away from its boundary leaves the boundary unchanged. -/
theorem IsCombinatorialManifold.boundary_stellarSubdivision_of_notMem
    (hK : IsCombinatorialManifold K n) (hv : ({v} : Finset ι) ∉ K)
    (hσne : σ.Nonempty) (hσ : σ ∉ K.boundary) :
    (PreAbstractSimplicialComplex.stellarSubdivision K σ v).boundary = K.boundary := by
  rw [hK.boundary_stellarSubdivision hv,
    stellarSubdivision_eq_self_of_notMem (fun h => hv (boundary_le h)) hσne hσ]

/-- Same-type stellar equivalence between combinatorial manifolds induces stellar equivalence of
their boundaries. -/
theorem IsCombinatorialManifold.stellarEquivalent_boundary
    (hK : IsCombinatorialManifold K n) (he : StellarEquivalent K L) :
    StellarEquivalent K.boundary L.boundary := by
  let Motive : PreAbstractSimplicialComplex ι → PreAbstractSimplicialComplex ι → Prop :=
    fun X Y => (IsCombinatorialManifold X n ↔ IsCombinatorialManifold Y n) ∧
      (IsCombinatorialManifold X n → StellarEquivalent X.boundary Y.boundary)
  suffices h : Motive K L from h.2 hK
  apply he.induction_on
  · intro A B hm
    refine ⟨hm.stellarEquivalent.isCombinatorialManifold_iff, fun hA => ?_⟩
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hm
    rw [hA.boundary_stellarSubdivision hv]
    by_cases hσb : σ ∈ A.boundary
    · exact stellarEquivalent_stellarSubdivision hσb fun h => hv (boundary_le h)
    · rw [stellarSubdivision_eq_self_of_notMem (fun h => hv (boundary_le h))
        (A.isRelLowerSet_faces hσ).1 hσb]
  · exact fun _ => ⟨Iff.rfl, fun _ => .refl _⟩
  · exact fun _ _ ih => ⟨ih.1.symm, fun hB => (ih.2 (ih.1.mpr hB)).symm⟩
  · exact fun _ _ _ ih₁ ih₂ => ⟨ih₁.1.trans ih₂.1, fun hA => (ih₁.2 hA).trans (ih₂.2 (ih₁.1.mp hA))⟩

/-- Intrinsic stellar equivalence between combinatorial manifolds induces intrinsic stellar
equivalence of their boundaries. -/
theorem IsCombinatorialManifold.stellarEquivalentUpToRelabeling_boundary
    (hK : IsCombinatorialManifold K n) (he : StellarEquivalentUpToRelabeling K L) :
    StellarEquivalentUpToRelabeling K.boundary L.boundary := by
  let Motive : PreAbstractSimplicialComplex ι → PreAbstractSimplicialComplex ι → Prop :=
    fun X Y => (IsCombinatorialManifold X n ↔ IsCombinatorialManifold Y n) ∧
      (IsCombinatorialManifold X n → StellarEquivalentUpToRelabeling X.boundary Y.boundary)
  suffices h : Motive K L from h.2 hK
  apply he.induction_on
  · intro A B f g hab
    have hfg := StellarEquivalentUpToRelabeling.of_common_relabeling f g hab
    refine ⟨hfg.isCombinatorialManifold_iff,
      fun hA => StellarEquivalentUpToRelabeling.of_common_relabeling f g ?_⟩
    rw [map_boundary f f.injective, map_boundary g g.injective]
    exact (hA.map f f.injective).stellarEquivalent_boundary hab
  · exact fun _ => ⟨Iff.rfl, fun _ => .refl _⟩
  · exact fun _ _ ih => ⟨ih.1.symm, fun hB => (ih.2 (ih.1.mpr hB)).symm⟩
  · exact fun _ _ _ ih₁ ih₂ => ⟨ih₁.1.trans ih₂.1, fun hA => (ih₁.2 hA).trans (ih₂.2 (ih₁.1.mp hA))⟩

/-- The boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere. -/
theorem IsCombinatorialBall.isCombinatorialSphere_boundary (hK : IsCombinatorialBall K (n + 1)) :
    IsCombinatorialSphere K.boundary n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp hK
  refine isCombinatorialSphere_iff.mpr ⟨V, hV, ?_⟩
  rw [← boundary_simplex V]
  exact hK.isCombinatorialManifold.stellarEquivalentUpToRelabeling_boundary he

/-! ### The boundary is a closed combinatorial manifold -/

/-- At any vertex of a combinatorial manifold, the link in the boundary is the boundary of its
link in the manifold (both sides are `⊥` when `{v} ∉ K.boundary`). -/
theorem IsCombinatorialManifold.link_boundary_singleton (hK : IsCombinatorialManifold K n) :
    link K.boundary {v} = (link K {v}).boundary := by
  have hlv : IsCombinatorialManifold (link K {v}) (n - 1) := by
    by_cases hvK : ({v} : Finset ι) ∈ K
    · cases n with
      | zero =>
        rw [isCombinatorialManifold_zero_iff.mp hK hvK]
        simp
      | succ m =>
        exact (isCombinatorialManifold_succ_iff.mp hK hvK).elim
          IsCombinatorialSphere.isCombinatorialManifold
          IsCombinatorialBall.isCombinatorialManifold
    · have hbot : link K {v} = ⊥ := eq_bot_iff.mpr fun ρ hρ => hvK
        (singleton_mem_of_mem (mem_link_nonempty.mp hρ).2.2
          (mem_union_right _ (mem_singleton_self v)))
      rw [hbot]
      simp
  refine SetLike.ext fun ρ => ?_
  rw [mem_link_nonempty, hK.mem_boundary_iff, hlv.mem_boundary_iff, mem_link_nonempty]
  constructor
  · rintro ⟨hne, hdis, hface, k, hball⟩
    refine ⟨⟨hne, hdis, hface⟩, k, ?_⟩
    rwa [link_link hdis.symm, singleton_union, ← union_singleton]
  · rintro ⟨⟨hne, hdis, hface⟩, k, hball⟩
    refine ⟨hne, hdis, hface, k, ?_⟩
    rwa [link_link hdis.symm, singleton_union, ← union_singleton] at hball

/-- Every vertex link in the boundary of a combinatorial `(n + 2)`-manifold is a combinatorial
`n`-sphere. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_link_boundary
    (hK : IsCombinatorialManifold K (n + 2)) (hv : ({v} : Finset ι) ∈ K.boundary) :
    IsCombinatorialSphere (link K.boundary {v}) n := by
  rw [hK.link_boundary_singleton]
  exact (hK.singleton_mem_boundary_succ_iff.mp hv).2.isCombinatorialSphere_boundary

/-- **The boundary of a combinatorial `(n + 1)`-manifold is a combinatorial `n`-manifold.** -/
theorem IsCombinatorialManifold.isCombinatorialManifold_boundary
    (hK : IsCombinatorialManifold K (n + 1)) :
    IsCombinatorialManifold K.boundary n := by
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun v hv => ?_
    rw [hK.link_boundary_singleton]
    exact (hK.singleton_mem_boundary_succ_iff.mp hv).2.isCombinatorialManifold.boundary_eq_bot_zero
  | succ m =>
    exact isCombinatorialManifold_succ_iff.mpr fun v hv =>
      Or.inl (hK.isCombinatorialSphere_link_boundary hv)

/-- The boundary of a combinatorial manifold has void boundary (`∂² = ∅`). -/
theorem IsCombinatorialManifold.boundary_boundary_eq_bot (hK : IsCombinatorialManifold K n) :
    K.boundary.boundary = ⊥ := by
  cases n with
  | zero => simp [hK.boundary_eq_bot_zero]
  | succ m =>
    cases m with
    | zero => exact hK.isCombinatorialManifold_boundary.boundary_eq_bot_zero
    | succ k =>
      refine eq_bot_iff.mpr fun σ hσ => ?_
      obtain ⟨v, hv⟩ := (K.boundary.isRelLowerSet_faces (boundary_le hσ)).1
      have hv_b : ({v} : Finset ι) ∈ K.boundary := singleton_mem_of_mem (boundary_le hσ) hv
      obtain ⟨-, _, hball⟩ := singleton_mem_boundary_iff.mp (singleton_mem_of_mem hσ hv)
      exact (hK.isCombinatorialSphere_link_boundary hv_b).not_isCombinatorialBall hball

/-- The boundary of a combinatorial `(n + 1)`-manifold is pure of dimension `n`. -/
theorem IsCombinatorialManifold.isPure_boundary (hK : IsCombinatorialManifold K (n + 1)) :
    IsPure K.boundary n :=
  hK.isCombinatorialManifold_boundary.isPure

/-- The boundary of a combinatorial `(n + 1)`-manifold has dimension at most `n`. -/
theorem IsCombinatorialManifold.dimension_boundary_le (hK : IsCombinatorialManifold K (n + 1)) :
    dimension K.boundary ≤ (n : WithBot ℕ∞) :=
  hK.isCombinatorialManifold_boundary.dimension_le

/-- A nonvoid boundary of a combinatorial `(n + 1)`-manifold has dimension `n`. -/
theorem IsCombinatorialManifold.dimension_boundary_eq (hK : IsCombinatorialManifold K (n + 1))
    (hb : K.boundary ≠ ⊥) :
    dimension K.boundary = (n : WithBot ℕ∞) :=
  hK.isCombinatorialManifold_boundary.dimension_eq hb

/-- A face of a combinatorial `(n + 1)`-manifold lies in the boundary if and only if it is a
nonempty subset of a codimension-one face (`τ.card = n + 1`) whose link is a single vertex, i.e.
a ridge contained in a unique top-dimensional simplex of `K`. -/
theorem IsCombinatorialManifold.mem_boundary_iff_exists_ridge
    (hK : IsCombinatorialManifold K (n + 1)) :
    σ ∈ K.boundary ↔
      ∃ τ ∈ K, σ.Nonempty ∧ σ ⊆ τ ∧ τ.card = n + 1 ∧ ∃ w, link K τ = simplex {w} := by
  constructor
  · intro hσ
    obtain ⟨τ, hτ, hστ, hτcard⟩ := hK.isPure_boundary.exists_coface hσ
    obtain ⟨hτK, -, hball⟩ := hK.mem_boundary_iff_isCombinatorialBall.mp hτ
    rw [hτcard, Nat.sub_self, isCombinatorialBall_zero_iff] at hball
    exact ⟨τ, hτK, (K.boundary.isRelLowerSet_faces hσ).1, hστ, hτcard, hball⟩
  · rintro ⟨τ, hτK, hσne, hστ, _, w, hlink⟩
    have hτb : τ ∈ K.boundary :=
      hK.mem_boundary_iff.mpr ⟨hτK, 0, hlink ▸ isCombinatorialBall_simplex (by simp)⟩
    exact (K.boundary.isRelLowerSet_faces hτb).2 hστ hσne

end General

end PreAbstractSimplicialComplex
