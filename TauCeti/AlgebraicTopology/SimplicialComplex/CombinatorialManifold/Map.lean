/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import Mathlib.Data.Set.Card
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Pure
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional
import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Link
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Relabeling

/-!
# Relabeling combinatorial balls, spheres, and manifolds

An injective map of ambient vertex types both preserves and reflects combinatorial balls,
combinatorial spheres, and combinatorial manifolds of a given dimension, across arbitrary vertex
universes. This allows local models described using disjoint tagged vertex types, such as joins and
stellar closed-star decompositions, to be transported back to the original complex without fixing
vertex universes or retaining auxiliary tag maps in theorem statements.

Forward transport for balls and spheres uses `StellarEquivalentUpToRelabeling.map`. Reflection uses
`stellarEquivalentUpToRelabeling_map_iff` once a standard model of the required cardinality is
realized inside the source vertex type: for balls a top-dimensional face supplies `n + 1` vertices,
and for spheres a top-dimensional face cannot exhaust the complex (distinguished from a simplex in
positive dimension by `IsCombinatorialSphere.encard_faces_link_eq_two`, the closed-pseudomanifold
invariant that every codimension-1 face has a two-vertex link). Since injective maps commute with
vertex links (`map_link`), manifold invariance follows for arbitrary — possibly infinite —
complexes.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialSphere.encard_faces_link_eq_two`: every codimension-1
  face of a combinatorial `(n + 1)`-sphere has a two-face link.
* `PreAbstractSimplicialComplex.isCombinatorialBall_map_iff`: injective vertex maps preserve and
  reflect combinatorial `n`-balls.
* `PreAbstractSimplicialComplex.isCombinatorialSphere_map_iff`: injective vertex maps preserve and
  reflect combinatorial `n`-spheres.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.map` and
  `PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff`: injective vertex maps preserve
  and reflect combinatorial `n`-manifolds.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (stellar equivalence, combinatorial balls, spheres, and manifolds).
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

section TwoCofacets

/-- Every codimension-1 face (`card = m + 1`) of `X` has a link with exactly two faces. -/
private def HasTwoCofacets (m : ℕ) {α : Type*} [DecidableEq α]
    (X : PreAbstractSimplicialComplex α) : Prop :=
  ∀ ρ ∈ X, ρ.card = m + 1 → (link X ρ).faces.encard = 2

private theorem hasTwoCofacets_map_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    {X : PreAbstractSimplicialComplex α} {m : ℕ} (g : α → β) (hg : Function.Injective g) :
    HasTwoCofacets m (X.map g) ↔ HasTwoCofacets m X := by
  constructor
  · intro h ρ hρ hcard
    have h2 := h (ρ.image g) (mem_map_iff.mpr ⟨ρ, hρ, rfl⟩)
      (by rw [card_image_of_injective ρ hg, hcard])
    rwa [← map_link g hg, faces_map, (image_injective hg).encard_image] at h2
  · intro h τ hτ hcard
    obtain ⟨ρ, hρ, rfl⟩ := mem_map_iff.mp hτ
    rw [← map_link g hg, faces_map, (image_injective hg).encard_image]
    exact h ρ hρ (by rwa [card_image_of_injective ρ hg] at hcard)

private theorem hasTwoCofacets_stellarSubdivision {α : Type*} [DecidableEq α]
    {A : PreAbstractSimplicialComplex α} {π : Finset α} {v : α} {m : ℕ}
    (hPure : IsPure A (m + 1)) (hA : HasTwoCofacets m A) (hπ : π ∈ A)
    (hv : ({v} : Finset α) ∉ A) :
    HasTwoCofacets m (stellarSubdivision A π v) := by
  intro τ hτ hcard
  by_cases hvτ : v ∈ τ
  · let ω := τ.erase v
    have hvω : v ∉ ω := notMem_erase v τ
    have hτeq : insert v ω = τ := insert_erase hvτ
    obtain ⟨hnot, hface⟩ := (insert_mem_stellarSubdivision_iff hvω).mp (hτeq.symm ▸ hτ)
    have hωcard : ω.card = m := by
      dsimp only [ω]
      rw [card_erase_of_mem hvτ, hcard]
      rfl
    have hjoin : (link (stellarSubdivision A π v) τ).map (partitionEmbedding (· ∈ π)) =
        join (simplexBoundary (π \ ω)) (link A (ω ∪ π)) := by
      rw [← hτeq, link_stellarSubdivision_insert hv hvω]
      exact map_link_closedStar_inf_deletion_eq_join hπ hnot hface
    have hcard_union : (ω ∪ π).card = m + (π \ ω).card := by
      rw [← union_sdiff_self_eq_union, card_union_of_disjoint disjoint_sdiff_self_right, hωcard]
    have hpos : 1 ≤ (π \ ω).card := card_pos.mpr (sdiff_nonempty.mpr hnot)
    have htop : (ω ∪ π).card ≤ m + 2 := hPure.card_le hface
    have h12 : (π \ ω).card = 1 ∨ (π \ ω).card = 2 := by omega
    rw [← (image_injective (partitionEmbedding (· ∈ π)).injective).encard_image,
      ← faces_map, hjoin]
    rcases h12 with h1 | h2
    · obtain ⟨x, hx⟩ := card_eq_one.mp h1
      rw [hx, simplexBoundary_singleton, bot_join, faces_map,
        (image_injective Sum.inr_injective).encard_image]
      exact hA (ω ∪ π) hface (by omega)
    · obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp h2
      have hbot : link A (ω ∪ π) = ⊥ := (hPure.link_eq_bot_iff hface).mpr (by omega)
      rw [hpair, hbot, join_bot, faces_map, (image_injective Sum.inl_injective).encard_image,
        faces_simplexBoundary_pair hxy]
      exact Set.encard_pair (by simpa using hxy)
  · obtain ⟨hτA, hnot⟩ := (mem_stellarSubdivision_iff_of_notMem hvτ).mp hτ
    have he := stellarEquivalent_link_stellarSubdivision_of_notMem
      (fun h => hv (link_le h)) hvτ (sdiff_nonempty.mpr hnot)
    have hdim : dimension (link A τ) ≤ 0 := by
      rw [hPure.dimension_link hτA (by omega)]
      simp [hcard]
    rw [he.encard_faces_eq_of_dimension_le_zero hdim]
    exact hA τ hτA hcard

private theorem hasTwoCofacets_of_stellarSubdivision {α : Type*} [DecidableEq α]
    {A : PreAbstractSimplicialComplex α} {π : Finset α} {v : α} {m : ℕ}
    (hPure : IsPure A (m + 1)) (hsub : HasTwoCofacets m (stellarSubdivision A π v))
    (hπ : π ∈ A) (hv : ({v} : Finset α) ∉ A) :
    HasTwoCofacets m A := by
  intro ρ hρ hcard
  have hvρ : v ∉ ρ := notMem_of_singleton_notMem hv hρ
  by_cases hπρ : π ⊆ ρ
  · obtain ⟨x, hx⟩ := (A.isRelLowerSet_faces hπ).1
    have hmem := insert_erase_mem_stellarSubdivision hρ hvρ hπρ hx
    have hv_er : v ∉ ρ.erase x := fun h => hvρ (mem_of_mem_erase h)
    have hnot : ¬ π ⊆ ρ.erase x := fun h => notMem_erase x ρ (h hx)
    have hunion : ρ.erase x ∪ π = ρ :=
      (erase_union_of_mem hx ρ).trans (union_eq_left.mpr hπρ)
    have hsdiff : π \ ρ.erase x = {x} := by
      rw [sdiff_erase hx, sdiff_eq_empty_iff_subset.mpr hπρ, insert_empty_eq]
    have hjoin : (link (stellarSubdivision A π v) (insert v (ρ.erase x))).map
        (partitionEmbedding (· ∈ π)) = (link A ρ).map Sum.inr := by
      rw [link_stellarSubdivision_insert hv hv_er,
        map_link_closedStar_inf_deletion_eq_join hπ hnot (hunion.symm ▸ hρ),
        hsdiff, hunion, simplexBoundary_singleton, bot_join]
    have hcard' : (insert v (ρ.erase x)).card = m + 1 := by
      rw [card_insert_of_notMem hv_er, card_erase_of_mem (hπρ hx)]
      omega
    have h2 := hsub (insert v (ρ.erase x)) hmem hcard'
    rwa [← (image_injective (partitionEmbedding (· ∈ π)).injective).encard_image,
      ← faces_map, hjoin, faces_map, (image_injective Sum.inr_injective).encard_image] at h2
  · have he := stellarEquivalent_link_stellarSubdivision_of_notMem
      (fun h => hv (link_le h)) hvρ (sdiff_nonempty.mpr hπρ)
    have hdim : dimension (link A ρ) ≤ 0 := by
      rw [hPure.dimension_link hρ (by omega)]
      simp [hcard]
    rw [← he.encard_faces_eq_of_dimension_le_zero hdim]
    exact hsub ρ ((mem_stellarSubdivision_iff_of_notMem hvρ).mpr ⟨hρ, hπρ⟩) hcard

private theorem isPure_and_hasTwoCofacets_iff_of_stellarEquivalent
    {α : Type*} [DecidableEq α] {X Y : PreAbstractSimplicialComplex α} {m : ℕ}
    (h : StellarEquivalent X Y) :
    (IsPure X (m + 1) ∧ HasTwoCofacets m X) ↔ (IsPure Y (m + 1) ∧ HasTwoCofacets m Y) := by
  refine h.induction_on
    (P := fun A B => (IsPure A (m + 1) ∧ HasTwoCofacets m A) ↔
      (IsPure B (m + 1) ∧ HasTwoCofacets m B))
    ?_ (fun _ => Iff.rfl) (fun _ _ ih => ih.symm) (fun _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
  intro C D hmove
  obtain ⟨π, v, hπ, hv, rfl⟩ := isStellarMove_iff.mp hmove
  refine ⟨fun ⟨hp, hc⟩ => ⟨hp.stellarSubdivision hv,
      hasTwoCofacets_stellarSubdivision hp hc hπ hv⟩,
    fun ⟨hp, hc⟩ => ?_⟩
  have hpC : IsPure C (m + 1) := (isPure_stellarSubdivision_iff hπ hv).mp hp
  exact ⟨hpC, hasTwoCofacets_of_stellarSubdivision hpC hc hπ hv⟩

private theorem isPure_and_hasTwoCofacets_iff_of_stellarEquivalentUpToRelabeling
    {α : Type*} [DecidableEq α] {X Y : PreAbstractSimplicialComplex α} {m : ℕ}
    (h : StellarEquivalentUpToRelabeling X Y) :
    (IsPure X (m + 1) ∧ HasTwoCofacets m X) ↔ (IsPure Y (m + 1) ∧ HasTwoCofacets m Y) := by
  refine h.induction_on
    (P := fun A B => (IsPure A (m + 1) ∧ HasTwoCofacets m A) ↔
      (IsPure B (m + 1) ∧ HasTwoCofacets m B))
    ?_ (fun _ => Iff.rfl) (fun _ _ ih => ih.symm) (fun _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
  intro A B f g he
  exact (and_congr (isPure_map_iff f f.injective) (hasTwoCofacets_map_iff f f.injective)).symm.trans
    ((isPure_and_hasTwoCofacets_iff_of_stellarEquivalent he).trans
      (and_congr (isPure_map_iff g g.injective) (hasTwoCofacets_map_iff g g.injective)))

/-- Every codimension-1 face (`ρ.card = n + 1`) of a combinatorial `(n + 1)`-sphere has a link
consisting of exactly two vertices (`(link K ρ).faces.encard = 2`). -/
theorem IsCombinatorialSphere.encard_faces_link_eq_two {ι : Type*} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {ρ : Finset ι} {n : ℕ}
    (hK : IsCombinatorialSphere K (n + 1)) (hρ : ρ ∈ K) (hcard : ρ.card = n + 1) :
    (link K ρ).faces.encard = 2 := by
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hK
  have hVB : IsPure (simplexBoundary V) (n + 1) ∧ HasTwoCofacets n (simplexBoundary V) := by
    refine ⟨isPure_simplexBoundary hV, fun σ hσ hσcard => ?_⟩
    have hσV : σ ⊆ V := (mem_simplexBoundary.mp hσ).2.subset
    have hcard_sdiff : (V \ σ).card = 2 := by
      rw [card_sdiff_of_subset hσV, hV, hσcard]
      omega
    obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp hcard_sdiff
    rw [link_simplexBoundary hσV, hpair, faces_simplexBoundary_pair hxy]
    exact Set.encard_pair (by simpa using hxy)
  exact ((isPure_and_hasTwoCofacets_iff_of_stellarEquivalentUpToRelabeling he).mpr hVB).2 ρ hρ hcard

private theorem not_isCombinatorialSphere_simplex_succ {α : Type*} [DecidableEq α]
    {W : Finset α} {m : ℕ} (hW : W.card = m + 2) :
    ¬ IsCombinatorialSphere (simplex W) (m + 1) := by
  intro hS
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < W.card)
  have hcard_er : (W.erase x).card = m + 1 := by
    rw [card_erase_of_mem hx, hW]
    omega
  have her_mem : W.erase x ∈ simplex W :=
    mem_simplex.mpr ⟨card_pos.mp (by omega), erase_subset x W⟩
  have h2 := hS.encard_faces_link_eq_two her_mem hcard_er
  rw [link_simplex (erase_subset x W), sdiff_erase_self hx, faces_simplex_singleton,
    Set.encard_singleton] at h2
  exact (by decide : (1 : ℕ∞) ≠ 2) h2

end TwoCofacets

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : PreAbstractSimplicialComplex ι} {n : ℕ}

/-- Injectively relabeling a combinatorial ball preserves its dimension and ball structure. -/
theorem IsCombinatorialBall.map (h : IsCombinatorialBall K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialBall (K.map f) n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  refine isCombinatorialBall_iff.mpr ⟨V.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective V hf, hV]
  · simpa only [map_simplex] using he.map f hf

/-- An injective vertex map preserves and reflects combinatorial `n`-balls across arbitrary vertex
universes. -/
@[simp]
theorem isCombinatorialBall_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialBall (K.map f) n ↔ IsCombinatorialBall K n := by
  refine ⟨fun h => ?_, fun h => h.map f hf⟩
  obtain ⟨ω, hω, -⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr h.ne_bot)
  obtain ⟨τ, hτ, -, hτcard⟩ := h.isPure.exists_coface hω
  obtain ⟨V, -, rfl⟩ := mem_map_iff.mp hτ
  have hVcard : V.card = n + 1 := by rwa [card_image_of_injective V hf] at hτcard
  obtain ⟨W, hWcard, he⟩ := isCombinatorialBall_iff.mp h
  have he' : StellarEquivalentUpToRelabeling (K.map f) ((simplex V).map f) := by
    rw [map_simplex]
    exact he.trans (stellarEquivalentUpToRelabeling_simplex_of_card_eq (hWcard.trans hτcard.symm))
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  exact isCombinatorialBall_iff.mpr
    ⟨V, hVcard, (stellarEquivalentUpToRelabeling_map_iff f hf hKfin).mp he'⟩

/-- Injectively relabeling a combinatorial sphere preserves its dimension and sphere structure. -/
theorem IsCombinatorialSphere.map (h : IsCombinatorialSphere K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialSphere (K.map f) n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  refine isCombinatorialSphere_iff.mpr ⟨V.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective V hf, hV]
  · have hmap : (simplexBoundary V).map f = simplexBoundary (V.image f) := by
      simpa only [Function.Embedding.coeFn_mk] using map_simplexBoundary V ⟨f, hf⟩
    rw [← hmap]
    exact he.map f hf

/-- An injective vertex map preserves and reflects combinatorial `n`-spheres across arbitrary
vertex universes. -/
@[simp]
theorem isCombinatorialSphere_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialSphere (K.map f) n ↔ IsCombinatorialSphere K n := by
  refine ⟨fun h => ?_, fun h => h.map f hf⟩
  have hexV : ∃ V : Finset ι, V.card = n + 2 := by
    cases n with
    | zero =>
      obtain ⟨a, b, hab, heq⟩ := isCombinatorialSphere_zero_iff.mp h
      have ha : ({a} : Finset κ) ∈ K.map f := by
        rw [heq]
        exact singleton_mem_simplexBoundary.mpr ⟨mem_insert_self a {b},
          fun h' => hab (mem_singleton.mp (h' ▸ mem_insert_of_mem (mem_singleton_self b))).symm⟩
      have hb : ({b} : Finset κ) ∈ K.map f := by
        rw [heq]
        exact singleton_mem_simplexBoundary.mpr ⟨mem_insert_of_mem (mem_singleton_self b),
          fun h' => hab (mem_singleton.mp (h' ▸ mem_insert_self a {b}))⟩
      obtain ⟨u, _, rfl⟩ := singleton_mem_map_iff.mp ha
      obtain ⟨w, _, rfl⟩ := singleton_mem_map_iff.mp hb
      exact ⟨{u, w}, card_pair fun h' => hab (congrArg f h')⟩
    | succ m =>
      obtain ⟨ω, hω, -⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr h.ne_bot)
      obtain ⟨τ, hτ, -, hτcard⟩ := h.isPure.exists_coface hω
      obtain ⟨σ, hσ, rfl⟩ := mem_map_iff.mp hτ
      have hσcard : σ.card = m + 2 := by rwa [card_image_of_injective σ hf] at hτcard
      have hnotall : ¬ ∀ ρ ∈ K, ρ ⊆ σ := by
        intro hall
        have hKeq : K = simplex σ := SetLike.ext fun ρ =>
          ⟨fun hρ => mem_simplex.mpr ⟨(K.isRelLowerSet_faces hρ).1, hall ρ hρ⟩,
            fun hρ => (K.isRelLowerSet_faces hσ).2 (mem_simplex.mp hρ).2 (mem_simplex.mp hρ).1⟩
        rw [hKeq, map_simplex] at h
        exact not_isCombinatorialSphere_simplex_succ hτcard h
      push Not at hnotall
      obtain ⟨ρ, _, hnot⟩ := hnotall
      obtain ⟨w, _, hwσ⟩ := not_subset.mp hnot
      exact ⟨insert w σ, by rw [card_insert_of_notMem hwσ, hσcard]⟩
  obtain ⟨V, hVcard⟩ := hexV
  obtain ⟨W, hWcard, he⟩ := isCombinatorialSphere_iff.mp h
  have hmap : (simplexBoundary V).map f = simplexBoundary (V.image f) := by
    simpa only [Function.Embedding.coeFn_mk] using map_simplexBoundary V ⟨f, hf⟩
  have hVfcard : (V.image f).card = n + 2 := by rw [card_image_of_injective V hf, hVcard]
  have he' : StellarEquivalentUpToRelabeling (K.map f) ((simplexBoundary V).map f) := by
    rw [hmap]
    exact he.trans
      (stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq (hWcard.trans hVfcard.symm))
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  exact isCombinatorialSphere_iff.mpr
    ⟨V, hVcard, (stellarEquivalentUpToRelabeling_map_iff f hf hKfin).mp he'⟩

/-- An injective vertex map preserves and reflects combinatorial `n`-manifolds (without any
finiteness assumption on the complex). -/
@[simp]
theorem isCombinatorialManifold_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialManifold (K.map f) n ↔ IsCombinatorialManifold K n := by
  cases n with
  | zero =>
    simp only [isCombinatorialManifold_zero_iff]
    have hbot (L : PreAbstractSimplicialComplex ι) : L.map f = ⊥ ↔ L = ⊥ := by
      rw [← dimension_eq_bot_iff, dimension_map_of_injective f hf, dimension_eq_bot_iff]
    constructor
    · intro h v hv
      have hl := h (singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩)
      rwa [← image_singleton f v, ← map_link f hf, hbot] at hl
    · intro h y hy
      obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hy
      rw [← image_singleton f v, ← map_link f hf, hbot]
      exact h hv
  | succ m =>
    simp only [isCombinatorialManifold_succ_iff]
    constructor
    · intro h v hv
      have hl := h (singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩)
      rwa [← image_singleton f v, ← map_link f hf, isCombinatorialSphere_map_iff f hf,
        isCombinatorialBall_map_iff f hf] at hl
    · intro h y hy
      obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hy
      rw [← image_singleton f v, ← map_link f hf, isCombinatorialSphere_map_iff f hf,
        isCombinatorialBall_map_iff f hf]
      exact h hv

/-- Injectively relabeling a combinatorial `n`-manifold preserves its manifold structure. -/
theorem IsCombinatorialManifold.map (h : IsCombinatorialManifold K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialManifold (K.map f) n :=
  (isCombinatorialManifold_map_iff f hf).mpr h

end PreAbstractSimplicialComplex
