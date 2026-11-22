/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Link
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional

/-!
# The boundary of a combinatorial manifold

For a simplicial precomplex `K`, `PreAbstractSimplicialComplex.manifoldBoundary K` consists of the
faces `σ ∈ K` whose nonempty subfaces all have combinatorial-ball links in `K`. Phrasing the face
condition universally over nonempty subfaces makes `manifoldBoundary K` downward closed with no
assumptions on `K`, while at vertices `{v}` it immediately reduces to `link K {v}` being a
combinatorial ball.

When `K` is a combinatorial `n`-manifold, links of combinatorial spheres are again combinatorial
spheres (`IsCombinatorialSphere.isCombinatorialSphere_link`), so a face with a ball link cannot
contain any subface with a sphere link. Consequently, membership of `σ` in `manifoldBoundary K`
reduces to the single condition that `link K σ` is a combinatorial `(n - σ.card)`-ball, and the
boundary construction commutes with links (`IsCombinatorialManifold.link_manifoldBoundary`),
stellar subdivisions, and intrinsic stellar equivalence.

Applying these commutation properties to the standard simplex and its boundary shows that the
boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere, the boundary of a
combinatorial `n`-sphere is void, and the boundary of any combinatorial `(n + 1)`-manifold is a
combinatorial `n`-manifold whose own boundary is void.

## Main definitions

* `PreAbstractSimplicialComplex.manifoldBoundary K`: the boundary subcomplex of `K`.

## Main results

* `PreAbstractSimplicialComplex.manifoldBoundary_simplex` and
  `PreAbstractSimplicialComplex.manifoldBoundary_simplexBoundary`: `manifoldBoundary (simplex V) =
  simplexBoundary V` and `manifoldBoundary (simplexBoundary V) = ⊥`.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.mem_manifoldBoundary_iff`: in a
  combinatorial `n`-manifold `K`, a finset `σ` lies in `manifoldBoundary K` if and only if
  `σ ∈ K` and `link K σ` is a combinatorial `(n - σ.card)`-ball.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.link_manifoldBoundary` and
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.manifoldBoundary_stellarSubdivision`:
  `manifoldBoundary` commutes with links and with stellar subdivision at any fresh vertex.
* `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.manifoldBoundary`: intrinsic
  stellar equivalence between combinatorial manifolds induces intrinsic stellar equivalence between
  their boundaries.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialSphere_manifoldBoundary`: the
  boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.manifoldBoundary_eq_bot`: the boundary of a
  combinatorial `n`-sphere is void.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.isCombinatorialManifold_manifoldBoundary`
  and `PreAbstractSimplicialComplex.IsCombinatorialManifold.manifoldBoundary_manifoldBoundary`:
  the boundary of a combinatorial `(n + 1)`-manifold is a combinatorial `n`-manifold, and taking
  the boundary twice on any combinatorial manifold yields `⊥`.
* `IsCombinatorialManifold.mem_manifoldBoundary_iff_exists_link_eq_simplex_singleton`: in a
  combinatorial `(n + 1)`-manifold, boundary faces are precisely the nonempty subsets of
  codimension-one faces whose link is a single vertex.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

section General

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι} {v : ι}

/-- The **boundary** of a simplicial precomplex `K`: the faces `σ ∈ K` every nonempty subface `τ`
of which has a combinatorial-ball link in `K`.

Quantifying over all nonempty subfaces makes the face collection downward closed unconditionally.
When `K` is a combinatorial `n`-manifold, downward propagation of ball links reduces membership to
the single condition `IsCombinatorialBall (link K σ) (n - σ.card)`
(`IsCombinatorialManifold.mem_manifoldBoundary_iff`). -/
def manifoldBoundary (K : PreAbstractSimplicialComplex ι) : PreAbstractSimplicialComplex ι where
  faces := {σ | σ ∈ K ∧ ∀ ⦃τ : Finset ι⦄, τ.Nonempty → τ ⊆ σ →
    ∃ d, IsCombinatorialBall (link K τ) d}
  isRelLowerSet_faces := fun {_} hσ =>
    ⟨(K.isRelLowerSet_faces hσ.1).1,
      fun {_} hτσ hτ => ⟨(K.isRelLowerSet_faces hσ.1).2 hτσ hτ,
        fun {_} hρne hρτ => hσ.2 hρne (hρτ.trans hτσ)⟩⟩

/-- Defining characterization of faces in `manifoldBoundary K`. -/
theorem mem_manifoldBoundary_iff :
    σ ∈ manifoldBoundary K ↔
      σ ∈ K ∧ ∀ ⦃τ : Finset ι⦄, τ.Nonempty → τ ⊆ σ → ∃ d, IsCombinatorialBall (link K τ) d :=
  Iff.rfl

/-- The boundary of `K` is a subcomplex of `K`. -/
theorem manifoldBoundary_le : manifoldBoundary K ≤ K :=
  fun _ hσ => (mem_manifoldBoundary_iff.mp hσ).1

/-- A vertex belongs to `manifoldBoundary K` exactly when its link in `K` is a combinatorial
ball. -/
theorem singleton_mem_manifoldBoundary_iff :
    ({v} : Finset ι) ∈ manifoldBoundary K ↔ ∃ d, IsCombinatorialBall (link K {v}) d := by
  rw [mem_manifoldBoundary_iff]
  refine ⟨fun ⟨_, hall⟩ => hall (Finset.singleton_nonempty v) Finset.Subset.rfl, fun ⟨d, hb⟩ => ?_⟩
  refine ⟨mem_of_link_ne_bot (Finset.singleton_nonempty v) hb.ne_bot, fun {τ} hτne hτsub => ?_⟩
  obtain rfl : τ = {v} := (Finset.subset_singleton_iff.mp hτsub).resolve_left hτne.ne_empty
  exact ⟨d, hb⟩

/-- The boundary of the void precomplex is void. -/
@[simp]
theorem manifoldBoundary_bot : manifoldBoundary (⊥ : PreAbstractSimplicialComplex ι) = ⊥ :=
  eq_bot_iff.mpr (manifoldBoundary_le (K := ⊥))

/-- Injective vertex relabeling commutes with `manifoldBoundary`. -/
@[simp]
theorem map_manifoldBoundary {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) :
    (manifoldBoundary K).map f = manifoldBoundary (K.map f) := by
  refine SetLike.ext fun ω => ?_
  rw [mem_map_iff, mem_manifoldBoundary_iff]
  refine ⟨fun ⟨σ, ⟨hσK, hall⟩, hσω⟩ => hσω ▸ ⟨mem_map_iff.mpr ⟨σ, hσK, rfl⟩,
    fun {τ'} hτ'ne hτ'sub => ?_⟩, fun ⟨hωK, hall⟩ => ?_⟩
  · obtain ⟨τ, hτσ, rfl⟩ := Finset.subset_image_iff.mp hτ'sub
    obtain ⟨d, hb⟩ := hall (Finset.image_nonempty.mp hτ'ne) hτσ
    exact ⟨d, map_link f hf ▸ hb.map f hf⟩
  · obtain ⟨σ, hσK, rfl⟩ := mem_map_iff.mp hωK
    refine ⟨σ, ⟨hσK, fun {τ} hτne hτσ => ?_⟩, rfl⟩
    obtain ⟨d, hb⟩ := hall (hτne.image f) (Finset.image_subset_image hτσ)
    exact ⟨d, IsCombinatorialBall.of_map hf (map_link f hf ▸ hb)⟩

/-- The manifold boundary of an abstract simplex is its simplex boundary, including the empty and
one-vertex cases where both sides are `⊥`. -/
@[simp]
theorem manifoldBoundary_simplex (V : Finset ι) :
    manifoldBoundary (simplex V) = simplexBoundary V := by
  refine SetLike.ext fun σ => ?_
  rw [mem_manifoldBoundary_iff, mem_simplexBoundary_iff_mem_simplex_ne]
  constructor
  · rintro ⟨hσ, hall⟩
    refine ⟨hσ, fun hσV => ?_⟩
    subst hσV
    obtain ⟨_, hb⟩ := hall (mem_simplex.mp hσ).1 Finset.Subset.rfl
    exact hb.ne_bot link_simplex_self
  · rintro ⟨hσ, hne⟩
    obtain ⟨_, hσV⟩ := mem_simplex.mp hσ
    refine ⟨hσ, fun {τ} _ hτσ => ?_⟩
    have hτV : τ ⊆ V := hτσ.trans hσV
    have hlt : τ.card < V.card :=
      Finset.card_lt_card (hτσ.trans_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hσV, hne⟩))
    exact ⟨V.card - 1 - τ.card, isCombinatorialBall_link_simplex (n := V.card - 1)
      (by omega) hτV (by omega)⟩

/-- The manifold boundary of a simplex boundary is void. -/
@[simp]
theorem manifoldBoundary_simplexBoundary (V : Finset ι) :
    manifoldBoundary (simplexBoundary V) = ⊥ := by
  refine eq_bot_iff.mpr fun σ ⟨hσsb, hall⟩ => ?_
  obtain ⟨hσne, hσV⟩ := mem_simplexBoundary.mp hσsb
  obtain ⟨_, hb⟩ := hall hσne Finset.Subset.rfl
  rw [link_simplexBoundary hσV.subset] at hb
  by_cases h2 : 2 ≤ (V \ σ).card
  · exact (isCombinatorialSphere_simplexBoundary (n := (V \ σ).card - 2)
      (by omega)).not_isCombinatorialBall hb
  · rcases (by omega : (V \ σ).card = 0 ∨ (V \ σ).card = 1) with h0 | h1
    · exact hb.ne_bot (by rw [Finset.card_eq_zero.mp h0, simplexBoundary_empty])
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
      exact hb.ne_bot (by rw [hw, simplexBoundary_singleton])

end General

/-! ### Face characterization and link commutation on combinatorial manifolds -/

section ManifoldFaces

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι} {v : ι} {n d : ℕ}

/-- In a combinatorial `n`-manifold, if a finset `σ` has a combinatorial-ball link, then every
nonempty subset `τ ⊆ σ` has a combinatorial `(n - τ.card)`-ball link. -/
theorem IsCombinatorialManifold.isCombinatorialBall_link_of_subset
    (hK : IsCombinatorialManifold K n)
    (hb : IsCombinatorialBall (link K σ) d) (hτne : τ.Nonempty) (hτσ : τ ⊆ σ) :
    IsCombinatorialBall (link K τ) (n - τ.card) := by
  have hσ : σ ∈ K := mem_of_link_ne_bot (hτne.mono hτσ) hb.ne_bot
  have hσcard : σ.card ≤ n := hK.card_le_of_link_ne_bot hb.ne_bot
  refine (hK.isCombinatorialSphere_or_isCombinatorialBall_link
    ((K.isRelLowerSet_faces hσ).2 hτσ hτne) ((Finset.card_le_card hτσ).trans hσcard)).resolve_left
    fun hs => ?_
  rcases (σ \ τ).eq_empty_or_nonempty with hdiff | hdiff
  · exact hs.not_isCombinatorialBall
      ((Finset.Subset.antisymm hτσ (Finset.sdiff_eq_empty_iff_subset.mp hdiff)) ▸ hb)
  · have hrem : σ \ τ ∈ link K τ := mem_link_nonempty.mpr
      ⟨hdiff, Finset.sdiff_disjoint, by rwa [Finset.sdiff_union_of_subset hτσ]⟩
    have hsRem := hs.isCombinatorialSphere_link hrem
      (by rw [Finset.card_sdiff_of_subset hτσ]; omega)
    rw [link_link Finset.sdiff_disjoint.symm, Finset.union_sdiff_of_subset hτσ] at hsRem
    exact hsRem.not_isCombinatorialBall hb

/-- In a combinatorial `n`-manifold, a finset belongs to `manifoldBoundary K` exactly when it is a
face of `K` whose link is a combinatorial ball of some dimension. -/
theorem IsCombinatorialManifold.mem_manifoldBoundary_iff_exists_isCombinatorialBall
    (hK : IsCombinatorialManifold K n) :
    σ ∈ manifoldBoundary K ↔ σ ∈ K ∧ ∃ d, IsCombinatorialBall (link K σ) d := by
  rw [PreAbstractSimplicialComplex.mem_manifoldBoundary_iff]
  refine ⟨fun ⟨hσ, hall⟩ => ⟨hσ, hall (K.isRelLowerSet_faces hσ).1 Finset.Subset.rfl⟩,
    fun ⟨hσ, _, hb⟩ => ⟨hσ, fun {τ} hτne hτσ =>
      ⟨n - τ.card, hK.isCombinatorialBall_link_of_subset hb hτne hτσ⟩⟩⟩

/-- In a combinatorial `n`-manifold, a finset `σ` belongs to `manifoldBoundary K` if and only if
`σ ∈ K` and `link K σ` is a combinatorial `(n - σ.card)`-ball.

This holds in every dimension `n`, including `n = 0` and top-dimensional faces `σ.card = n + 1`,
where `link K σ = ⊥` cannot be a combinatorial ball. -/
theorem IsCombinatorialManifold.mem_manifoldBoundary_iff
    (hK : IsCombinatorialManifold K n) :
    σ ∈ manifoldBoundary K ↔ σ ∈ K ∧ IsCombinatorialBall (link K σ) (n - σ.card) := by
  rw [hK.mem_manifoldBoundary_iff_exists_isCombinatorialBall]
  refine ⟨fun ⟨hσ, _, hb⟩ =>
    ⟨hσ, hK.isCombinatorialBall_link_of_subset hb (K.isRelLowerSet_faces hσ).1
      Finset.Subset.rfl⟩,
    fun ⟨hσ, hb⟩ => ⟨hσ, n - σ.card, hb⟩⟩

/-- A zero-dimensional combinatorial manifold has void boundary. -/
theorem IsCombinatorialManifold.manifoldBoundary_eq_bot_of_zero
    (hK : IsCombinatorialManifold K 0) :
    manifoldBoundary K = ⊥ := by
  refine eq_bot_iff.mpr fun σ hσ => ?_
  obtain ⟨hσK, hb⟩ := hK.mem_manifoldBoundary_iff.mp hσ
  obtain ⟨v, rfl⟩ := dimension_le_zero_iff.mp hK.dimension_le σ hσK
  exact hb.ne_bot (isCombinatorialManifold_zero_iff.mp hK hσK)

/-- In a combinatorial `(n + 1)`-manifold, a vertex belongs to `manifoldBoundary K` if and only if
its link in `K` is a combinatorial `n`-ball. -/
theorem IsCombinatorialManifold.singleton_mem_manifoldBoundary_iff
    (hK : IsCombinatorialManifold K (n + 1)) :
    ({v} : Finset ι) ∈ manifoldBoundary K ↔ IsCombinatorialBall (link K {v}) n := by
  rw [hK.mem_manifoldBoundary_iff, Finset.card_singleton, Nat.add_sub_cancel]
  exact ⟨And.right, fun hb => ⟨mem_of_link_ne_bot (Finset.singleton_nonempty v) hb.ne_bot, hb⟩⟩

/-- A face `σ` with `σ.card ≤ n` in a combinatorial `n`-manifold avoids `manifoldBoundary K`
if and only if its link is a combinatorial `(n - σ.card)`-sphere. -/
theorem IsCombinatorialManifold.notMem_manifoldBoundary_iff
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    σ ∉ manifoldBoundary K ↔ IsCombinatorialSphere (link K σ) (n - σ.card) := by
  rw [hK.mem_manifoldBoundary_iff]
  exact ⟨fun hnot => (hK.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard).resolve_right
    fun hb => hnot ⟨hσ, hb⟩,
    fun hs ⟨_, hb⟩ => hs.not_isCombinatorialBall hb⟩

/-- Taking the link of any finset `σ` in a combinatorial manifold commutes with taking the
manifold boundary. -/
theorem IsCombinatorialManifold.link_manifoldBoundary
    (hK : IsCombinatorialManifold K n) (σ : Finset ι) :
    link (manifoldBoundary K) σ = manifoldBoundary (link K σ) := by
  refine SetLike.ext fun ρ => ?_
  rw [mem_link_nonempty, hK.mem_manifoldBoundary_iff_exists_isCombinatorialBall,
    (hK.isCombinatorialManifold_link σ).mem_manifoldBoundary_iff_exists_isCombinatorialBall,
    mem_link_nonempty]
  constructor
  · rintro ⟨hne, hdis, hface, d, hb⟩
    exact ⟨⟨hne, hdis, hface⟩, d, by rwa [link_link hdis.symm, Finset.union_comm]⟩
  · rintro ⟨⟨hne, hdis, hface⟩, d, hb⟩
    exact ⟨hne, hdis, hface, d, by rwa [link_link hdis.symm, Finset.union_comm] at hb⟩

end ManifoldFaces

/-! ### Commutation with stellar subdivision and stellar equivalence -/

section StellarInvariance

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

private theorem mem_manifoldBoundary_stellarSubdivision_iff_of_notMem {τ : Finset ι}
    (hK : IsCombinatorialManifold K n) (hv : ({v} : Finset ι) ∉ K) (hvτ : v ∉ τ) :
    τ ∈ manifoldBoundary (stellarSubdivision K σ v) ↔ τ ∈ manifoldBoundary K ∧ ¬ σ ⊆ τ := by
  rw [(hK.stellarSubdivision hv).mem_manifoldBoundary_iff_exists_isCombinatorialBall,
    mem_stellarSubdivision_iff_of_notMem hvτ,
    hK.mem_manifoldBoundary_iff_exists_isCombinatorialBall, and_right_comm]
  refine and_congr_left fun havoid => and_congr_right fun _ => exists_congr fun _ => ?_
  exact (stellarEquivalent_link_stellarSubdivision_of_notMem (fun h => hv (link_le h)) hvτ
    (Finset.sdiff_nonempty.mpr havoid)).symm.isCombinatorialBall_iff

private theorem insert_mem_manifoldBoundary_stellarSubdivision_iff {ρ : Finset ι}
    (hK : IsCombinatorialManifold K n) (hv : ({v} : Finset ι) ∉ K) (hvρ : v ∉ ρ) :
    insert v ρ ∈ manifoldBoundary (stellarSubdivision K σ v) ↔
      ¬ σ ⊆ ρ ∧ ρ ∪ σ ∈ manifoldBoundary K := by
  rw [(hK.stellarSubdivision hv).mem_manifoldBoundary_iff_exists_isCombinatorialBall,
    insert_mem_stellarSubdivision_iff hvρ,
    hK.mem_manifoldBoundary_iff_exists_isCombinatorialBall, and_assoc]
  refine and_congr_right fun havoid => and_congr_right fun hunion => ?_
  have hmap := map_link_stellarSubdivision_insert_eq_join hv havoid hunion
  have hev (d : ℕ) : IsCombinatorialBall (link (stellarSubdivision K σ v) (insert v ρ)) d ↔
      IsCombinatorialBall (join (simplexBoundary (σ \ ρ)) (link K (ρ ∪ σ))) d :=
    (isCombinatorialBall_map_iff (partitionEmbedding (· ∈ σ)).injective).symm.trans
      (by rw [hmap])
  simp_rw [hev]
  have hpos : 1 ≤ (σ \ ρ).card := Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr havoid)
  by_cases h1 : (σ \ ρ).card = 1
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    rw [hu, simplexBoundary_singleton, bot_join]
    exact exists_congr fun _ => isCombinatorialBall_map_iff Sum.inr_injective
  · have hsb : IsCombinatorialSphere (simplexBoundary (σ \ ρ)) ((σ \ ρ).card - 2) :=
      isCombinatorialSphere_simplexBoundary (by omega)
    by_cases hbot : link K (ρ ∪ σ) = ⊥
    · rw [hbot, join_bot]
      exact ⟨fun ⟨_, hb⟩ => absurd hb (hsb.map Sum.inl Sum.inl_injective).not_isCombinatorialBall,
        fun ⟨_, hb⟩ => absurd rfl hb.ne_bot⟩
    · rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hunion
          (hK.card_le_of_link_ne_bot hbot) with hslk | hblk
      · exact ⟨fun ⟨_, hb⟩ => absurd hb (hsb.join hslk).not_isCombinatorialBall,
          fun ⟨_, hb⟩ => absurd hb hslk.not_isCombinatorialBall⟩
      · exact ⟨fun _ => ⟨_, hblk⟩, fun _ => ⟨_, hsb.join_ball hblk⟩⟩

/-- Taking the manifold boundary of a combinatorial manifold commutes with starring any finset `σ`
at a fresh vertex `v`. -/
theorem IsCombinatorialManifold.manifoldBoundary_stellarSubdivision
    (hK : IsCombinatorialManifold K n) (hv : ({v} : Finset ι) ∉ K) (σ : Finset ι) :
    manifoldBoundary (PreAbstractSimplicialComplex.stellarSubdivision K σ v) =
      PreAbstractSimplicialComplex.stellarSubdivision (manifoldBoundary K) σ v := by
  refine SetLike.ext fun τ => ?_
  by_cases hvτ : v ∈ τ
  · rw [← Finset.insert_erase hvτ,
      insert_mem_manifoldBoundary_stellarSubdivision_iff hK hv (Finset.notMem_erase v τ),
      insert_mem_stellarSubdivision_iff (Finset.notMem_erase v τ)]
  · rw [mem_manifoldBoundary_stellarSubdivision_iff_of_notMem hK hv hvτ,
      mem_stellarSubdivision_iff_of_notMem hvτ]

/-- Starring a nonempty finset `σ ∉ manifoldBoundary K` of a combinatorial manifold at a fresh
vertex leaves `manifoldBoundary K` unchanged. -/
theorem IsCombinatorialManifold.manifoldBoundary_stellarSubdivision_of_notMem
    (hK : IsCombinatorialManifold K n) (hσne : σ.Nonempty) (hσbd : σ ∉ manifoldBoundary K)
    (hv : ({v} : Finset ι) ∉ K) :
    manifoldBoundary (PreAbstractSimplicialComplex.stellarSubdivision K σ v) =
      manifoldBoundary K := by
  rw [hK.manifoldBoundary_stellarSubdivision hv σ,
    stellarSubdivision_eq_self_of_notMem (fun h => hv (manifoldBoundary_le h)) hσne hσbd]

/-- Stellar equivalence between combinatorial manifolds induces stellar equivalence between their
boundaries. -/
theorem StellarEquivalent.manifoldBoundary (he : StellarEquivalent K L)
    (hK : IsCombinatorialManifold K n) :
    StellarEquivalent (PreAbstractSimplicialComplex.manifoldBoundary K)
      (PreAbstractSimplicialComplex.manifoldBoundary L) := by
  revert hK
  induction he using StellarEquivalent.induction with
  | rel A _ hm =>
      intro hA
      obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hm
      rw [hA.manifoldBoundary_stellarSubdivision hv σ]
      exact stellarEquivalent_stellarSubdivision_of_nonempty (A.isRelLowerSet_faces hσ).1
        fun h => hv (manifoldBoundary_le h)
  | refl _ => exact fun _ => .refl _
  | symm _ _ hAB ih =>
      exact fun hB => (ih (hAB.stellarEquivalentUpToRelabeling.isCombinatorialManifold_iff.mpr
        hB)).symm
  | trans _ _ _ hAB _ ih₁ ih₂ =>
      exact fun hA => (ih₁ hA).trans
        (ih₂ (hAB.stellarEquivalentUpToRelabeling.isCombinatorialManifold_iff.mp hA))

/-- Intrinsic stellar equivalence up to relabeling between combinatorial manifolds induces
intrinsic stellar equivalence between their boundaries. -/
theorem StellarEquivalentUpToRelabeling.manifoldBoundary
    (he : StellarEquivalentUpToRelabeling K L) (hK : IsCombinatorialManifold K n) :
    StellarEquivalentUpToRelabeling (PreAbstractSimplicialComplex.manifoldBoundary K)
      (PreAbstractSimplicialComplex.manifoldBoundary L) := by
  revert hK
  induction he using StellarEquivalentUpToRelabeling.induction with
  | rel _ _ f g hfg =>
      intro hA
      have hebd := hfg.manifoldBoundary (hA.map f f.injective)
      rw [← map_manifoldBoundary f f.injective, ← map_manifoldBoundary g g.injective] at hebd
      exact StellarEquivalentUpToRelabeling.of_common_relabeling f g hebd
  | refl _ => exact fun _ => .refl _
  | symm _ _ hAB ih => exact fun hB => (ih (hAB.isCombinatorialManifold_iff.mpr hB)).symm
  | trans _ _ _ hAB _ ih₁ ih₂ =>
      exact fun hA => (ih₁ hA).trans (ih₂ (hAB.isCombinatorialManifold_iff.mp hA))

end StellarInvariance

/-! ### Boundaries of balls, spheres, and combinatorial manifolds -/

section BoundaryManifold

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

/-- A combinatorial zero-ball has void boundary. -/
theorem IsCombinatorialBall.manifoldBoundary_eq_bot_of_zero (h : IsCombinatorialBall K 0) :
    manifoldBoundary K = ⊥ :=
  h.isCombinatorialManifold.manifoldBoundary_eq_bot_of_zero

/-- The boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere. -/
theorem IsCombinatorialBall.isCombinatorialSphere_manifoldBoundary
    (h : IsCombinatorialBall K (n + 1)) :
    IsCombinatorialSphere (manifoldBoundary K) n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  have hebd := he.manifoldBoundary h.isCombinatorialManifold
  rw [manifoldBoundary_simplex] at hebd
  exact hebd.isCombinatorialSphere_iff.mpr (isCombinatorialSphere_simplexBoundary hV)

/-- The boundary of a combinatorial `n`-sphere is void. -/
theorem IsCombinatorialSphere.manifoldBoundary_eq_bot (h : IsCombinatorialSphere K n) :
    manifoldBoundary K = ⊥ := by
  obtain ⟨V, -, he⟩ := isCombinatorialSphere_iff.mp h
  have hebd := he.manifoldBoundary h.isCombinatorialManifold
  rw [manifoldBoundary_simplexBoundary] at hebd
  exact dimension_eq_bot_iff.mp (hebd.dimension_eq.symm.trans dimension_bot)

/-- The link in `manifoldBoundary K` of any boundary face `σ` with `σ.card ≤ n` in a combinatorial
`(n + 1)`-manifold is a combinatorial `(n - σ.card)`-sphere. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_link_manifoldBoundary
    (hK : IsCombinatorialManifold K (n + 1)) (hσ : σ ∈ manifoldBoundary K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link (manifoldBoundary K) σ) (n - σ.card) := by
  obtain ⟨_, hb⟩ := hK.mem_manifoldBoundary_iff.mp hσ
  rw [(by omega : n + 1 - σ.card = (n - σ.card) + 1)] at hb
  rw [hK.link_manifoldBoundary]
  exact hb.isCombinatorialSphere_manifoldBoundary

/-- Every vertex link in the boundary of a combinatorial `(n + 2)`-manifold is a combinatorial
`n`-sphere. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_link_manifoldBoundary_singleton
    (hK : IsCombinatorialManifold K (n + 2)) (hv : ({v} : Finset ι) ∈ manifoldBoundary K) :
    IsCombinatorialSphere (link (manifoldBoundary K) {v}) n := by
  simpa using hK.isCombinatorialSphere_link_manifoldBoundary hv (by simp)

/-- **The boundary of a combinatorial `(n + 1)`-manifold is a combinatorial `n`-manifold.** -/
theorem IsCombinatorialManifold.isCombinatorialManifold_manifoldBoundary
    (hK : IsCombinatorialManifold K (n + 1)) :
    IsCombinatorialManifold (manifoldBoundary K) n := by
  cases n with
  | zero =>
      refine isCombinatorialManifold_zero_iff.mpr fun v hv => ?_
      rw [hK.link_manifoldBoundary,
        (hK.singleton_mem_manifoldBoundary_iff.mp hv).manifoldBoundary_eq_bot_of_zero]
  | succ _ =>
      exact isCombinatorialManifold_succ_iff.mpr fun _ hv =>
        Or.inl (hK.isCombinatorialSphere_link_manifoldBoundary_singleton hv)

/-- A combinatorial `(n + 1)`-manifold has void boundary if and only if every vertex link is a
combinatorial `n`-sphere. -/
theorem IsCombinatorialManifold.manifoldBoundary_eq_bot_iff
    (hK : IsCombinatorialManifold K (n + 1)) :
    manifoldBoundary K = ⊥ ↔
      ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → IsCombinatorialSphere (link K {v}) n := by
  refine ⟨fun hbot _ hv => (hK.notMem_manifoldBoundary_iff hv (by simp)).mp
      (by rw [hbot]; exact id),
    fun hall => eq_bot_iff.mpr fun σ hσ => ?_⟩
  obtain ⟨v, hv⟩ := ((manifoldBoundary K).isRelLowerSet_faces hσ).1
  have hvbd : ({v} : Finset ι) ∈ manifoldBoundary K := singleton_mem_of_mem hσ hv
  exact (hall (manifoldBoundary_le hvbd)).not_isCombinatorialBall
    (hK.singleton_mem_manifoldBoundary_iff.mp hvbd)

/-- The boundary of the boundary of any combinatorial manifold is void. -/
theorem IsCombinatorialManifold.manifoldBoundary_manifoldBoundary
    (hK : IsCombinatorialManifold K n) :
    manifoldBoundary (manifoldBoundary K) = ⊥ :=
  match n with
  | 0 => by rw [hK.manifoldBoundary_eq_bot_of_zero, manifoldBoundary_bot]
  | 1 => hK.isCombinatorialManifold_manifoldBoundary.manifoldBoundary_eq_bot_of_zero
  | _ + 2 => hK.isCombinatorialManifold_manifoldBoundary.manifoldBoundary_eq_bot_iff.mpr
      fun _ hv => hK.isCombinatorialSphere_link_manifoldBoundary_singleton hv

/-- A nonvoid boundary of a combinatorial `(n + 1)`-manifold has dimension `n`. -/
theorem IsCombinatorialManifold.dimension_manifoldBoundary
    (hK : IsCombinatorialManifold K (n + 1)) (hne : manifoldBoundary K ≠ ⊥) :
    dimension (manifoldBoundary K) = (n : WithBot ℕ∞) :=
  hK.isCombinatorialManifold_manifoldBoundary.dimension_eq hne

/-- In a combinatorial `(n + 1)`-manifold, a finset lies in `manifoldBoundary K` if and only if it
is a nonempty subset of a codimension-one face `τ ∈ K` (`τ.card = n + 1`) whose link is a single
vertex. -/
theorem IsCombinatorialManifold.mem_manifoldBoundary_iff_exists_link_eq_simplex_singleton
    (hK : IsCombinatorialManifold K (n + 1)) :
    σ ∈ manifoldBoundary K ↔
      σ.Nonempty ∧ ∃ τ ∈ K, σ ⊆ τ ∧ τ.card = n + 1 ∧ ∃ w, link K τ = simplex {w} := by
  refine ⟨fun hσ => ?_, fun ⟨hσne, τ, hτK, hστ, hτcard, w, hlink⟩ => ?_⟩
  · obtain ⟨τ, hτbd, hστ, hτcard⟩ :=
      hK.isCombinatorialManifold_manifoldBoundary.isPure.exists_coface hσ
    obtain ⟨hτK, hb⟩ := hK.mem_manifoldBoundary_iff.mp hτbd
    exact ⟨((manifoldBoundary K).isRelLowerSet_faces hσ).1, τ, hτK, hστ, hτcard,
      isCombinatorialBall_zero_iff.mp (by rwa [hτcard, Nat.sub_self] at hb)⟩
  · exact ((manifoldBoundary K).isRelLowerSet_faces (hK.mem_manifoldBoundary_iff.mpr
      ⟨hτK, by rw [hτcard, Nat.sub_self]; exact isCombinatorialBall_zero_iff.mpr ⟨w, hlink⟩⟩)).2
      hστ hσne

end BoundaryManifold

end PreAbstractSimplicialComplex
