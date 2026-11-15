/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Relabel
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Combinatorial
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Facet

/-!
# Links of faces in combinatorial manifolds

A combinatorial `n`-manifold is defined by its vertex links: each is a combinatorial
`(n - 1)`-sphere or ball. This file proves that then the link of *every* face `σ` is a
combinatorial sphere or ball, of dimension `n - σ.card`
(`IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`), that
combinatorial balls and spheres are themselves combinatorial manifolds
(`IsCombinatorialBall.isCombinatorialManifold`, `IsCombinatorialSphere.isCombinatorialManifold`),
and that being a combinatorial manifold is invariant under stellar moves and intrinsic stellar
equivalence (`isCombinatorialManifold_stellarSubdivision_iff`,
`StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff`). All names are in the namespace
`PreAbstractSimplicialComplex`.

The three statements are proved together, by induction on the dimension.

* Face links. For a face `σ ∋ w`, the link of `σ` is the link of `σ \ {w}` inside the link of
  `w`, which is a combinatorial `(n - 1)`-sphere or ball, hence, by the lower-dimensional case, a
  combinatorial `(n - 1)`-manifold.
* Stellar moves. Starring `σ` at a fresh vertex `v` replaces the link of each old vertex `w` by a
  starring of its old link, or leaves it alone, so inverse stellar moves preserve manifolds with
  no further input. The new vertex has as link the join of the boundary of `σ`, a combinatorial
  sphere, with the link of `σ` (`map_closedStar_inf_deletion_eq_join`); by the face-link step
  this is a combinatorial sphere or ball of the right dimension. The case of a singleton `σ`,
  where the new vertex just renames `w`, is separate.
* Balls and spheres. The standard simplex and the boundary of a simplex are combinatorial
  manifolds, and the manifold property is invariant under stellar moves and, by
  `PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff`, under injective relabelings.

## Main results

* `IsCombinatorialManifold.of_stellarSubdivision`: an inverse stellar move preserves
  combinatorial manifolds.
* `isCombinatorialSphere_or_isCombinatorialBall_link_stellarSubdivision_singleton`: the link of
  the new vertex after starring a face with a sphere-or-ball link.
* `IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`: the link of a face
  in a combinatorial manifold is a combinatorial sphere or ball.
* `IsCombinatorialBall.isCombinatorialManifold` and `IsCombinatorialSphere.isCombinatorialManifold`.
* `IsCombinatorialManifold.stellarSubdivision`: a stellar move preserves combinatorial manifolds.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (links in combinatorial manifolds, balls and spheres).
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320, Section 2.
-/

public section

universe u

open Finset TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι} {σ : Finset ι}
  {v : ι} {n : ℕ}

/-! ### Inverse stellar moves -/

/-- **Inverse stellar moves preserve combinatorial manifolds.** If starring a face of `K` at a
fresh vertex gives a combinatorial `n`-manifold, then `K` is a combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.of_stellarSubdivision (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ K) (h : IsCombinatorialManifold (stellarSubdivision K σ v) n) :
    IsCombinatorialManifold K n := by
  -- Every vertex link of `K` is stellar equivalent to a vertex link of the subdivision.
  have key : ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → ∃ u, ({u} : Finset ι) ∈ stellarSubdivision K σ v ∧
      StellarEquivalent (link K {w}) (link (stellarSubdivision K σ v) {u}) := by
    intro w hw
    have hvw : v ∉ ({w} : Finset ι) := notMem_singleton.mpr fun h => hv (h ▸ hw)
    by_cases hσw : σ = {w}
    · -- Starring a vertex renames it: the new vertex has the old link.
      subst hσw
      refine ⟨v, singleton_mem_stellarSubdivision_iff.mpr hσ, ?_⟩
      rw [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton]
    · have hsub : ¬ σ ⊆ {w} := fun h => hσw ((K.isRelLowerSet_faces hσ).1.subset_singleton_iff.mp h)
      refine ⟨w, (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsub⟩, ?_⟩
      rw [link_stellarSubdivision_of_notMem hvw]
      by_cases hmem : σ \ {w} ∈ link K {w}
      · exact stellarEquivalent_stellarSubdivision hmem (notMem_link_of_notMem hv)
      · rw [stellarSubdivision_eq_self_of_notMem (notMem_link_of_notMem hv)
          (sdiff_nonempty.mpr hsub) hmem]
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
    obtain ⟨u, hu, he⟩ := key hw
    by_contra hne
    exact he.symm.ne_bot hne (isCombinatorialManifold_zero_iff.mp h hu)
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
    obtain ⟨u, hu, he⟩ := key hw
    exact (isCombinatorialManifold_succ_iff.mp h hu).imp
      (·.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling)
      (·.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling)

/-! ### The link of the new vertex -/

/-- **The link of a new stellar vertex.** Starring a face `σ` with `k + 2` vertices whose link is
a combinatorial `m`-sphere or ball gives a new vertex whose link, the join of the boundary of `σ`
with the link of `σ`, is a combinatorial `(k + m + 1)`-sphere or ball. -/
theorem isCombinatorialSphere_or_isCombinatorialBall_link_stellarSubdivision_singleton
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) {k m : ℕ} (hk : σ.card = k + 2)
    (hlink : IsCombinatorialSphere (link K σ) m ∨ IsCombinatorialBall (link K σ) m) :
    IsCombinatorialSphere (link (stellarSubdivision K σ v) {v}) (k + m + 1) ∨
      IsCombinatorialBall (link (stellarSubdivision K σ v) {v}) (k + m + 1) := by
  have hf := (partitionEmbedding (· ∈ σ)).injective
  rw [link_stellarSubdivision_singleton hv, ← isCombinatorialSphere_map_iff hf,
    ← isCombinatorialBall_map_iff hf, map_closedStar_inf_deletion_eq_join hσ]
  have hbd : IsCombinatorialSphere (simplexBoundary σ) k := isCombinatorialSphere_simplexBoundary hk
  exact hlink.imp hbd.join hbd.join_ball

/-- A stellar move preserves a combinatorial `n`-manifold once the link of the starred face is
known to be a combinatorial sphere or ball of the expected dimension. -/
private theorem IsCombinatorialManifold.stellarSubdivision_of_link
    (h : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hlink : σ.card ≤ n → IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card)) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n := by
  have hpos := (K.isRelLowerSet_faces hσ).1.card_pos
  have hle : σ.card ≤ n + 1 := by
    have h₁ : σ.card - 1 ≤ n := by exact_mod_cast (le_dimension hσ).trans h.dimension_le
    omega
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply h.stellarSubdivision_succ hv
    obtain ⟨w, rfl⟩ | ⟨k, hk⟩ : (∃ w, σ = {w}) ∨ ∃ k, σ.card = k + 2 := by
      rcases Nat.lt_or_ge σ.card 2 with h₂ | h₂
      · exact Or.inl (card_eq_one.mp (by omega))
      · exact Or.inr ⟨σ.card - 2, by omega⟩
    · rw [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton]
      exact isCombinatorialManifold_succ_iff.mp h hσ
    · have hm : k + (m + 1 - σ.card) + 1 = m := by omega
      rw [← hm]
      exact isCombinatorialSphere_or_isCombinatorialBall_link_stellarSubdivision_singleton hσ hv
        hk (hlink (by omega))
  · exact h.stellarSubdivision_of_card hσ heq hv

/-! ### Links of faces -/

/-- The link of a face of a combinatorial `n`-manifold is a combinatorial sphere or ball, given
that combinatorial balls and spheres of lower dimension are combinatorial manifolds. -/
private theorem link_of_forall_lt
    (hM : ∀ m < n, ∀ L : PreAbstractSimplicialComplex ι,
      IsCombinatorialSphere L m ∨ IsCombinatorialBall L m → IsCombinatorialManifold L m)
    (h : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) := by
  induction n generalizing K σ with
  | zero => exact absurd hcard (by have := (K.isRelLowerSet_faces hσ).1.card_pos; omega)
  | succ m ih =>
    obtain ⟨w, hw⟩ := (K.isRelLowerSet_faces hσ).1
    have hlw := isCombinatorialManifold_succ_iff.mp h (singleton_mem_of_mem hσ hw)
    by_cases hτ : σ.erase w = ∅
    · have hσw : σ = {w} := by rw [← insert_erase hw, hτ, insert_empty]
      subst hσw
      simpa using hlw
    · -- The link of `σ` is the link of `σ \ {w}` in the link of `w`.
      have hτlink : σ.erase w ∈ link K {w} := mem_link_nonempty.mpr
        ⟨nonempty_iff_ne_empty.mpr hτ, disjoint_singleton_right.mpr (notMem_erase w σ),
          by rwa [union_singleton, insert_erase hw]⟩
      have hpos : 0 < σ.card := card_pos.mpr ⟨w, hw⟩
      have hcard' : (σ.erase w).card ≤ m := by rw [card_erase_of_mem hw]; omega
      have hlink := ih (fun k hk => hM k (by omega)) (hM m (by omega) _ hlw) hτlink hcard'
      rwa [link_link (disjoint_singleton_left.mpr (notMem_erase w σ)), singleton_union,
        insert_erase hw, card_erase_of_mem hw, show m - (σ.card - 1) = m + 1 - σ.card by omega]
        at hlink

/-! ### Balls and spheres are manifolds -/

/-- Intrinsic stellar equivalence preserves and reflects combinatorial `n`-manifolds, given that
combinatorial balls and spheres of lower dimension are combinatorial manifolds. -/
private theorem isCombinatorialManifold_iff_of_forall_lt
    (hM : ∀ m < n, ∀ {α : Type u} [DecidableEq α] (L : PreAbstractSimplicialComplex α),
      IsCombinatorialSphere L m ∨ IsCombinatorialBall L m → IsCombinatorialManifold L m)
    (h : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n := by
  have hse {β : Type u} [DecidableEq β] {A B : PreAbstractSimplicialComplex β}
      (hAB : StellarEquivalent A B) :
      IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n := by
    refine hAB.induction_on
      (P := fun A B => IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n)
      (fun A B hAB => ?_) (fun _ => Iff.rfl) (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h')
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hAB
    exact ⟨fun h => h.stellarSubdivision_of_link hσ hv fun hcard =>
      link_of_forall_lt (fun m hm L hL => hM m hm L hL) h hσ hcard,
      IsCombinatorialManifold.of_stellarSubdivision hσ hv⟩
  refine h.induction_on
    (P := fun A B => IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n)
    (fun A B f g he => ?_) (fun _ => Iff.rfl) (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h')
  exact (isCombinatorialManifold_map_iff f.injective).symm.trans
    ((hse he).trans (isCombinatorialManifold_map_iff g.injective))

/-- Combinatorial `n`-balls and `n`-spheres are combinatorial `n`-manifolds, over every vertex
type in a fixed universe. -/
private theorem isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall
    (n : ℕ) {α : Type u} [DecidableEq α] (L : PreAbstractSimplicialComplex α)
    (hL : IsCombinatorialSphere L n ∨ IsCombinatorialBall L n) : IsCombinatorialManifold L n := by
  induction n using Nat.strong_induction_on generalizing α with
  | _ n ihn =>
  rcases hL with hs | hb
  · obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hs
    exact (isCombinatorialManifold_iff_of_forall_lt (fun m hm _ _ L hL => ihn m hm L hL) he).mpr
      (isCombinatorialManifold_simplexBoundary hV)
  · obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp hb
    exact (isCombinatorialManifold_iff_of_forall_lt (fun m hm _ _ L hL => ihn m hm L hL) he).mpr
      (isCombinatorialManifold_simplex hV)

/-- **A combinatorial `n`-sphere is a combinatorial `n`-manifold**: the link of each of its
vertices is a combinatorial `(n - 1)`-sphere or ball. -/
theorem IsCombinatorialSphere.isCombinatorialManifold (h : IsCombinatorialSphere K n) :
    IsCombinatorialManifold K n :=
  isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall n K (Or.inl h)

/-- **A combinatorial `n`-ball is a combinatorial `n`-manifold**: the link of each of its
vertices is a combinatorial `(n - 1)`-sphere or ball. -/
theorem IsCombinatorialBall.isCombinatorialManifold (h : IsCombinatorialBall K n) :
    IsCombinatorialManifold K n :=
  isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall n K (Or.inr h)

/-- **The link of a face of a combinatorial manifold.** In a combinatorial `n`-manifold, the link
of a face `σ` with at most `n` vertices is a combinatorial `(n - σ.card)`-sphere or ball. Faces
with `n + 1` vertices have void link (`IsCombinatorialManifold.link_eq_bot_iff`). -/
theorem IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link
    (h : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) :=
  link_of_forall_lt (fun m _ L hL =>
    isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall m L hL) h hσ hcard

/-! ### Stellar invariance -/

/-- **Stellar moves preserve combinatorial manifolds**: starring a face of a combinatorial
`n`-manifold at a fresh vertex gives a combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.stellarSubdivision (h : IsCombinatorialManifold K n)
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n :=
  h.stellarSubdivision_of_link hσ hv fun hcard =>
    h.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard

/-- Starring a face at a fresh vertex preserves and reflects combinatorial manifolds. -/
theorem isCombinatorialManifold_stellarSubdivision_iff (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n ↔ IsCombinatorialManifold K n :=
  ⟨.of_stellarSubdivision hσ hv, fun h => h.stellarSubdivision hσ hv⟩

/-- Intrinsically stellar equivalent complexes are combinatorial `n`-manifolds together. -/
theorem StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff
    (h : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  isCombinatorialManifold_iff_of_forall_lt (fun m _ _ _ L hL =>
    isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall m L hL) h

end PreAbstractSimplicialComplex
