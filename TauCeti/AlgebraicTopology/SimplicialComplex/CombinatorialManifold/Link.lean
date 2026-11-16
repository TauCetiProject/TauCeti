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

A combinatorial `n`-manifold is defined by its vertex links: for positive `n` each is a
combinatorial `(n - 1)`-sphere or ball, and for `n = 0` each is void. This file proves that then
the link of every face `σ` with at most `n` vertices is a combinatorial sphere or ball, of
dimension `n - σ.card` (`IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`;
faces with `n + 1` vertices have void link), that combinatorial balls and spheres are themselves
combinatorial manifolds
(`IsCombinatorialBall.isCombinatorialManifold`, `IsCombinatorialSphere.isCombinatorialManifold`),
and that being a combinatorial manifold is invariant under stellar moves and intrinsic stellar
equivalence (`isCombinatorialManifold_stellarSubdivision_iff`,
`StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff`). All names are in the namespace
`PreAbstractSimplicialComplex`.

The three statements are proved together, by induction on the dimension.

* Face links. For a face `σ ∋ w` with at most `n` vertices, the link of `σ` is the link of
  `σ \ {w}` inside the link of `w`, which is a combinatorial `(n - 1)`-sphere or ball, hence, by
  the lower-dimensional case, a combinatorial `(n - 1)`-manifold.
* Stellar moves. Starring `σ` at a fresh vertex `v` replaces the link of each old vertex `w` by a
  starring of its old link, or leaves it alone, so inverse stellar moves preserve manifolds with
  no further input (`IsCombinatorialManifold.of_stellarSubdivision`). When `σ` has at most `n`
  vertices, the new vertex has as link the join of the boundary of `σ`, a combinatorial sphere,
  with the link of `σ` (`map_closedStar_inf_deletion_eq_join`), or, for a singleton `σ = {w}`,
  just the link of `w`; by the face-link step this is a combinatorial sphere or ball of the right
  dimension. A top-dimensional face (`σ.card = n + 1`) is separate, since its link is void
  (`IsCombinatorialManifold.stellarSubdivision_of_card`).
* Balls and spheres. The standard simplex and the boundary of a simplex are combinatorial
  manifolds, and the manifold property is invariant under stellar moves and, by
  `PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff`, under injective relabelings.

## Main results

* `isCombinatorialSphere_closedStar_inf_deletion` and `isCombinatorialBall_closedStar_inf_deletion`:
  `closedStar K σ ⊓ deletion K σ` is a combinatorial sphere, respectively ball, when the link of
  `σ` is.
* `isCombinatorialSphere_link_stellarSubdivision_singleton` and
  `isCombinatorialBall_link_stellarSubdivision_singleton`: the link of the new vertex after
  starring a face whose link is a combinatorial sphere, respectively ball.
* `IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`: the link of a face
  with at most `n` vertices in a combinatorial `n`-manifold is a combinatorial sphere or ball.
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

/-! ### The link of the new vertex -/

/-- Let `σ` have `k + 1` vertices and a link that is a combinatorial `m`-sphere. Then
`closedStar K σ ⊓ deletion K σ`, the join of the boundary of `σ` with the link of `σ`, is a
combinatorial `(k + m)`-sphere. For a singleton `σ = {w}` it is just the link of `w`. -/
theorem isCombinatorialSphere_closedStar_inf_deletion {k m : ℕ} (hk : σ.card = k + 1)
    (hlink : IsCombinatorialSphere (link K σ) m) :
    IsCombinatorialSphere (closedStar K σ ⊓ deletion K σ) (k + m) := by
  cases k with
  | zero =>
    obtain ⟨w, rfl⟩ := card_eq_one.mp hk
    rwa [closedStar_inf_deletion_singleton, Nat.zero_add]
  | succ k =>
    have hσ : σ ∈ K := by
      by_contra hσ
      exact hlink.ne_bot (link_eq_bot_of_notMem (card_pos.mp (by omega)) hσ)
    have hf := (partitionEmbedding (· ∈ σ)).injective
    rw [← isCombinatorialSphere_map_iff hf, map_closedStar_inf_deletion_eq_join hσ,
      Nat.add_right_comm]
    exact (isCombinatorialSphere_simplexBoundary hk).join hlink

/-- Let `σ` have `k + 1` vertices and a link that is a combinatorial `m`-ball. Then
`closedStar K σ ⊓ deletion K σ`, the join of the boundary of `σ` with the link of `σ`, is a
combinatorial `(k + m)`-ball. For a singleton `σ = {w}` it is just the link of `w`. -/
theorem isCombinatorialBall_closedStar_inf_deletion {k m : ℕ} (hk : σ.card = k + 1)
    (hlink : IsCombinatorialBall (link K σ) m) :
    IsCombinatorialBall (closedStar K σ ⊓ deletion K σ) (k + m) := by
  cases k with
  | zero =>
    obtain ⟨w, rfl⟩ := card_eq_one.mp hk
    rwa [closedStar_inf_deletion_singleton, Nat.zero_add]
  | succ k =>
    have hσ : σ ∈ K := by
      by_contra hσ
      exact hlink.ne_bot (link_eq_bot_of_notMem (card_pos.mp (by omega)) hσ)
    have hf := (partitionEmbedding (· ∈ σ)).injective
    rw [← isCombinatorialBall_map_iff hf, map_closedStar_inf_deletion_eq_join hσ,
      Nat.add_right_comm]
    exact (isCombinatorialSphere_simplexBoundary hk).join_ball hlink

/-- **The link of a new stellar vertex, interior case.** Starring a set `σ` with `k + 1`
vertices whose link is a combinatorial `m`-sphere gives a new vertex whose link, the join of the
boundary of `σ` with the link of `σ`, is a combinatorial `(k + m)`-sphere. For a singleton
`σ = {w}` the link of the new vertex is just the link of `w`. -/
theorem isCombinatorialSphere_link_stellarSubdivision_singleton (hv : ({v} : Finset ι) ∉ K)
    {k m : ℕ} (hk : σ.card = k + 1) (hlink : IsCombinatorialSphere (link K σ) m) :
    IsCombinatorialSphere (link (stellarSubdivision K σ v) {v}) (k + m) := by
  rw [link_stellarSubdivision_singleton hv]
  exact isCombinatorialSphere_closedStar_inf_deletion hk hlink

/-- **The link of a new stellar vertex, boundary case.** Starring a set `σ` with `k + 1`
vertices whose link is a combinatorial `m`-ball gives a new vertex whose link, the join of the
boundary of `σ` with the link of `σ`, is a combinatorial `(k + m)`-ball. For a singleton
`σ = {w}` the link of the new vertex is just the link of `w`. -/
theorem isCombinatorialBall_link_stellarSubdivision_singleton (hv : ({v} : Finset ι) ∉ K)
    {k m : ℕ} (hk : σ.card = k + 1) (hlink : IsCombinatorialBall (link K σ) m) :
    IsCombinatorialBall (link (stellarSubdivision K σ v) {v}) (k + m) := by
  rw [link_stellarSubdivision_singleton hv]
  exact isCombinatorialBall_closedStar_inf_deletion hk hlink

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
    have hk : σ.card = σ.card - 1 + 1 := by omega
    have hm : σ.card - 1 + (m + 1 - σ.card) = m := by omega
    rw [← hm]
    exact (hlink (by omega)).imp (isCombinatorialSphere_link_stellarSubdivision_singleton hv hk)
      (isCombinatorialBall_link_stellarSubdivision_singleton hv hk)
  · exact h.stellarSubdivision_of_card hσ heq hv

/-! ### Links of faces -/

/-- The link of a face with at most `n` vertices of a combinatorial `n`-manifold is a
combinatorial sphere or ball, given that combinatorial balls and spheres of lower dimension are
combinatorial manifolds. -/
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
      .of_stellarSubdivision (A.isRelLowerSet_faces hσ).1 hv⟩
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

/-- **A combinatorial `n`-sphere is a combinatorial `n`-manifold**: for positive `n` the link of
each of its vertices is a combinatorial `(n - 1)`-sphere or ball, and for `n = 0` it is void. -/
theorem IsCombinatorialSphere.isCombinatorialManifold (h : IsCombinatorialSphere K n) :
    IsCombinatorialManifold K n :=
  isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall n K (Or.inl h)

/-- **A combinatorial `n`-ball is a combinatorial `n`-manifold**: for positive `n` the link of
each of its vertices is a combinatorial `(n - 1)`-sphere or ball, and for `n = 0` it is void. -/
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

/-- **Stellar moves preserve combinatorial manifolds**: starring a combinatorial `n`-manifold at
a fresh vertex gives a combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.stellarSubdivision (h : IsCombinatorialManifold K n)
    (hv : ({v} : Finset ι) ∉ K) : IsCombinatorialManifold (stellarSubdivision K σ v) n := by
  by_cases hσK : σ ∈ K
  · exact h.stellarSubdivision_of_link hσK hv fun hcard =>
      h.isCombinatorialSphere_or_isCombinatorialBall_link hσK hcard
  rcases σ.eq_empty_or_nonempty with rfl | hσ
  · -- Starring at the empty set gives the void complex, which has no vertices.
    rw [stellarSubdivision_empty]
    cases n
    · exact isCombinatorialManifold_zero_iff.mpr fun _ hw => hw.elim
    · exact isCombinatorialManifold_succ_iff.mpr fun _ hw => hw.elim
  · rwa [stellarSubdivision_eq_self_of_notMem hv hσ hσK]

/-- Starring a nonempty set at a fresh vertex preserves and reflects combinatorial manifolds. -/
@[simp]
theorem isCombinatorialManifold_stellarSubdivision_iff (hσ : σ.Nonempty)
    (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n ↔ IsCombinatorialManifold K n :=
  ⟨.of_stellarSubdivision hσ hv, fun h => h.stellarSubdivision hv⟩

/-- Intrinsically stellar equivalent complexes are combinatorial `n`-manifolds together. -/
theorem StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff
    (h : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  isCombinatorialManifold_iff_of_forall_lt (fun m _ _ _ L hL =>
    isCombinatorialManifold_of_isCombinatorialSphere_or_isCombinatorialBall m L hL) h

end PreAbstractSimplicialComplex
