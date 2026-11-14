/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Map
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Pure
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional
import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Combinatorial
import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Facet
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Relabeling

/-!
# Higher-face links and stellar invariance of combinatorial manifolds

In a combinatorial `n`-manifold `K`, not only every vertex link, but the link of every face
`σ ∈ K` with `σ.card ≤ n` is a combinatorial `(n - σ.card)`-sphere or `(n - σ.card)`-ball. Using
this face-link classification, starring *any* face `σ ∈ K` at a fresh vertex `{v} ∉ K` — and
inversely, undoing any stellar move — preserves `IsCombinatorialManifold · n`. Together with
relabeling invariance (`isCombinatorialManifold_map_iff`), `IsCombinatorialManifold · n` is
invariant under `StellarEquivalent` and `StellarEquivalentUpToRelabeling` (without any finiteness
assumption on the complex), so every combinatorial `n`-ball and every combinatorial `n`-sphere is a
combinatorial `n`-manifold.

Following Lickorish (*Simplicial moves on complexes and manifolds*, §3), these results are proved
by a simultaneous strong induction on the dimension `n` without appealing to Newman's theorem on
complements of top-dimensional subballs:

1. Inverse stellar moves reflect `IsCombinatorialManifold · n` unconditionally: surviving old
   vertices away from the starred face have stellar-equivalent links before and after starring, and
   when the starred face is itself a vertex `{w}`, its old link equals the new apex link.
2. Assuming combinatorial `k`-balls and `k`-spheres are combinatorial `k`-manifolds for all `k < n`,
   peeling one vertex `u ∈ σ` expresses `link K σ = link (link K {u}) (σ.erase u)` inside the
   `(n - 1)`-manifold `link K {u}`, classifying all non-maximal face links in dimension `n`.
3. For a stellar move at `σ ∈ K` (`2 ≤ σ.card ≤ n`), the new apex link is injectively relabeled to
   `join (simplexBoundary σ) (link K σ)` (`map_closedStar_inf_deletion_eq_join`), which is a sphere
   or ball by `IsCombinatorialSphere.join` / `IsCombinatorialSphere.join_ball` and reflects along
   `partitionEmbedding` via `isCombinatorialSphere_map_iff` / `isCombinatorialBall_map_iff`.
4. Stellar invariance at dimension `n` then transports `isCombinatorialManifold_simplex` and
   `isCombinatorialManifold_simplexBoundary` to arbitrary combinatorial `n`-balls and `n`-spheres.

In a combinatorial `n`-sphere, no non-maximal face link can be a ball — a ball link would supply a
codimension-1 face whose link does not have two vertices, contradicting
`IsCombinatorialSphere.encard_faces_link_eq_two` — so every non-maximal face link is a sphere, and
spherical links in any complex propagate upward along face inclusions.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialManifold.of_stellarSubdivision`,
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.stellarSubdivision`, and
  `PreAbstractSimplicialComplex.isCombinatorialManifold_stellarSubdivision_iff`: forward and
  inverse stellar moves preserve combinatorial `n`-manifolds at arbitrary faces.
* `PreAbstractSimplicialComplex.StellarEquivalent.isCombinatorialManifold_iff` and
  `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff`:
  stellar equivalence and intrinsic stellar equivalence preserve combinatorial `n`-manifolds.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialManifold` and
  `PreAbstractSimplicialComplex.IsCombinatorialSphere.isCombinatorialManifold`: combinatorial
  `n`-balls and `n`-spheres are combinatorial `n`-manifolds.
* `IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`:
  every face `σ ∈ K` (`σ.card ≤ n`) in a combinatorial `n`-manifold has a sphere or ball link of
  dimension `n - σ.card`.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.isCombinatorialSphere_link`: every face
  `σ ∈ K` with `σ.card ≤ n` in a combinatorial `n`-sphere has a sphere link of dimension
  `n - σ.card`.
* `PreAbstractSimplicialComplex.isCombinatorialSphere_link_of_subset`: if `τ ⊆ σ` (`σ ∈ K`,
  `σ.card ≤ n`) and `link K τ` is a combinatorial `(n - τ.card)`-sphere, so is `link K σ`.

## References

* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320, §3.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

section InverseMove

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

/-- Inverse stellar subdivision reflects `IsCombinatorialManifold`: if starring `σ ∈ K` at a fresh
vertex `{v} ∉ K` produces a combinatorial `n`-manifold, then `K` was already a combinatorial
`n`-manifold. -/
theorem IsCombinatorialManifold.of_stellarSubdivision
    (h : IsCombinatorialManifold (stellarSubdivision K σ v) n) (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ K) : IsCombinatorialManifold K n := by
  have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
    have hvw : v ∉ ({w} : Finset ι) := notMem_of_singleton_notMem hv hw
    by_cases hsub : σ ⊆ {w}
    · obtain rfl := hσne.subset_singleton_iff.mp hsub
      have hvmem : ({v} : Finset ι) ∈ stellarSubdivision K {w} v :=
        singleton_mem_stellarSubdivision_iff.mpr hw
      have hbot := isCombinatorialManifold_zero_iff.mp h hvmem
      rwa [link_stellarSubdivision_singleton hv,
        closedStar_singleton_inf_deletion_singleton] at hbot
    · have hw' : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
        (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsub⟩
      have he := stellarEquivalent_link_stellarSubdivision_of_notMem
        (notMem_link_of_notMem hv) hvw (sdiff_nonempty.mpr hsub)
      apply dimension_eq_bot_iff.mp
      rw [← he.dimension_eq, isCombinatorialManifold_zero_iff.mp h hw', dimension_bot]
  | succ m =>
    refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
    have hvw : v ∉ ({w} : Finset ι) := notMem_of_singleton_notMem hv hw
    by_cases hsub : σ ⊆ {w}
    · obtain rfl := hσne.subset_singleton_iff.mp hsub
      have hvmem : ({v} : Finset ι) ∈ stellarSubdivision K {w} v :=
        singleton_mem_stellarSubdivision_iff.mpr hw
      have hlink := isCombinatorialManifold_succ_iff.mp h hvmem
      rwa [link_stellarSubdivision_singleton hv,
        closedStar_singleton_inf_deletion_singleton] at hlink
    · have hw' : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
        (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsub⟩
      have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
        (notMem_link_of_notMem hv) hvw (sdiff_nonempty.mpr hsub)).stellarEquivalentUpToRelabeling
      exact (isCombinatorialManifold_succ_iff.mp h hw').imp
        (IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling he)
        (IsCombinatorialBall.of_stellarEquivalentUpToRelabeling he)

end InverseMove

section MutualInduction

universe u

private def BallsAndSpheresManifoldAt (k : ℕ) : Prop :=
  ∀ {α : Type u} [DecidableEq α] {X : PreAbstractSimplicialComplex α},
    (IsCombinatorialBall X k → IsCombinatorialManifold X k) ∧
      (IsCombinatorialSphere X k → IsCombinatorialManifold X k)

private theorem link_sphere_or_ball_of_ih {n : ℕ}
    (ih : ∀ k < n, BallsAndSpheresManifoldAt.{u} k) :
    ∀ (c : ℕ) {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α},
      IsCombinatorialManifold K n → σ ∈ K → σ.card = c + 1 → c + 1 ≤ n →
        IsCombinatorialSphere (link K σ) (n - σ.card) ∨
          IsCombinatorialBall (link K σ) (n - σ.card)
  | 0, _, _, _, _, hK, hσ, hcard, _ => by
    obtain ⟨u, rfl⟩ := card_eq_one.mp hcard
    cases n with
    | zero => omega
    | succ m =>
      simpa only [card_singleton, Nat.add_sub_cancel] using
        isCombinatorialManifold_succ_iff.mp hK hσ
  | d + 1, α, _, K, σ, hK, hσ, hcard, hle => by
    cases n with
    | zero => omega
    | succ m =>
      obtain ⟨u, hu⟩ := (K.isRelLowerSet_faces hσ).1
      have huK : ({u} : Finset α) ∈ K := singleton_mem_of_mem hσ hu
      have hm_lt : m < m + 1 := Nat.lt_succ_self m
      have hlu : IsCombinatorialManifold (link K {u}) m := by
        rcases isCombinatorialManifold_succ_iff.mp hK huK with hs | hb
        · exact (ih m hm_lt).2 hs
        · exact (ih m hm_lt).1 hb
      have her_card : (σ.erase u).card = d + 1 := by
        rw [card_erase_of_mem hu, hcard]
        rfl
      have her_mem : σ.erase u ∈ link K {u} := by
        refine mem_link_nonempty.mpr ⟨card_pos.mp (by omega),
          disjoint_singleton_right.mpr (notMem_erase u σ), ?_⟩
        rwa [union_singleton, insert_erase hu]
      have hrec := link_sphere_or_ball_of_ih (fun k hk => ih k (hk.trans hm_lt)) d
        hlu her_mem her_card (by omega)
      have hlink_eq : link (link K {u}) (σ.erase u) = link K σ := by
        rw [link_link (disjoint_singleton_left.mpr (notMem_erase u σ)),
          singleton_union, insert_erase hu]
      have hdim_eq : m - (σ.erase u).card = m + 1 - σ.card := by omega
      rwa [hlink_eq, hdim_eq] at hrec

private theorem stellarSubdivision_of_ih {n : ℕ}
    (ih : ∀ k < n, BallsAndSpheresManifoldAt.{u} k)
    {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α} {v : α}
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hv : ({v} : Finset α) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n := by
  have hcard_le : σ.card ≤ n + 1 := hK.isPure.card_le hσ
  have hcard_pos : 1 ≤ σ.card := card_pos.mpr (K.isRelLowerSet_faces hσ).1
  by_cases htop : σ.card = n + 1
  · exact hK.stellarSubdivision_of_card hσ htop hv
  · have hle_n : σ.card ≤ n := by omega
    by_cases h1 : σ.card = 1
    · obtain ⟨u, rfl⟩ := card_eq_one.mp h1
      rw [stellarSubdivision_singleton u hv]
      exact hK.map _ (Equiv.swap u v).injective
    · cases n with
      | zero => omega
      | succ m =>
        have h2 : 2 ≤ σ.card := by omega
        have hbdry : IsCombinatorialSphere (simplexBoundary σ) (σ.card - 2) :=
          isCombinatorialSphere_simplexBoundary (by omega)
        have hlink := link_sphere_or_ball_of_ih ih (σ.card - 1) hK hσ (by omega) (by omega)
        have hdim : (σ.card - 2) + (m + 1 - σ.card) + 1 = m := by omega
        have hnew : IsCombinatorialSphere (link (stellarSubdivision K σ v) {v}) m ∨
            IsCombinatorialBall (link (stellarSubdivision K σ v) {v}) m := by
          rw [link_stellarSubdivision_singleton hv,
            ← isCombinatorialSphere_map_iff _ (partitionEmbedding (· ∈ σ)).injective,
            ← isCombinatorialBall_map_iff _ (partitionEmbedding (· ∈ σ)).injective,
            map_closedStar_inf_deletion_eq_join hσ]
          rcases hlink with hs | hb
          · exact Or.inl (hdim ▸ hbdry.join hs)
          · exact Or.inr (hdim ▸ hbdry.join_ball hb)
        exact hK.stellarSubdivision_succ hv hnew

private theorem isCombinatorialManifold_iff_of_stellarEquivalent_of_ih {n : ℕ}
    (ih : ∀ k < n, BallsAndSpheresManifoldAt.{u} k)
    {α : Type u} [DecidableEq α] {A B : PreAbstractSimplicialComplex α}
    (he : StellarEquivalent A B) :
    IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n := by
  refine he.induction_on (P := fun A B => IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n)
    ?_ (fun _ => Iff.rfl) (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
  intro C D hmove
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hmove
  exact ⟨fun hC => stellarSubdivision_of_ih ih hC hσ hv,
    fun hD => hD.of_stellarSubdivision hσ hv⟩

private theorem isCombinatorialManifold_iff_of_stellarEquivalentUpToRelabeling_of_ih {n : ℕ}
    (ih : ∀ k < n, BallsAndSpheresManifoldAt.{u} k)
    {α : Type u} [DecidableEq α] {A B : PreAbstractSimplicialComplex α}
    (h : StellarEquivalentUpToRelabeling A B) :
    IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n := by
  refine h.induction_on (P := fun A B => IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n)
    ?_ (fun _ => Iff.rfl) (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
  intro C D f g he
  exact (isCombinatorialManifold_map_iff f f.injective).symm.trans
    ((isCombinatorialManifold_iff_of_stellarEquivalent_of_ih ih he).trans
      (isCombinatorialManifold_map_iff g g.injective))

private theorem ballsAndSpheresManifoldAt : ∀ n : ℕ, BallsAndSpheresManifoldAt.{u} n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro α _ X
    constructor
    · intro hB
      obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp hB
      exact (isCombinatorialManifold_iff_of_stellarEquivalentUpToRelabeling_of_ih ih he).mpr
        (isCombinatorialManifold_simplex hV)
    · intro hS
      obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hS
      exact (isCombinatorialManifold_iff_of_stellarEquivalentUpToRelabeling_of_ih ih he).mpr
        (isCombinatorialManifold_simplexBoundary hV)

end MutualInduction

section MainResults

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι} {v : ι} {n : ℕ}

/-- Every combinatorial `n`-ball is a combinatorial `n`-manifold. -/
theorem IsCombinatorialBall.isCombinatorialManifold (h : IsCombinatorialBall K n) :
    IsCombinatorialManifold K n :=
  (ballsAndSpheresManifoldAt n).1 h

/-- Every combinatorial `n`-sphere is a combinatorial `n`-manifold. -/
theorem IsCombinatorialSphere.isCombinatorialManifold (h : IsCombinatorialSphere K n) :
    IsCombinatorialManifold K n :=
  (ballsAndSpheresManifoldAt n).2 h

/-- In a combinatorial `n`-manifold `K`, the link of every face `σ ∈ K` with `σ.card ≤ n` is a
combinatorial `(n - σ.card)`-sphere or `(n - σ.card)`-ball. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) := by
  have hpos : 1 ≤ σ.card := card_pos.mpr (K.isRelLowerSet_faces hσ).1
  exact link_sphere_or_ball_of_ih (fun k _ => ballsAndSpheresManifoldAt k)
    (σ.card - 1) hK hσ (by omega) (by omega)

/-- In a combinatorial `n`-ball `K`, the link of every face `σ ∈ K` with `σ.card ≤ n` is a
combinatorial `(n - σ.card)`-sphere or `(n - σ.card)`-ball. -/
theorem IsCombinatorialBall.isCombinatorialSphere_or_isCombinatorialBall_link
    (hK : IsCombinatorialBall K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) :=
  hK.isCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard

/-- Starring any face `σ ∈ K` of a combinatorial `n`-manifold at a fresh vertex `{v} ∉ K` produces
a combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.stellarSubdivision
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (PreAbstractSimplicialComplex.stellarSubdivision K σ v) n :=
  stellarSubdivision_of_ih (fun k _ => ballsAndSpheresManifoldAt k) hK hσ hv

/-- A stellar subdivision at a face `σ ∈ K` and fresh vertex `{v} ∉ K` preserves and reflects
`IsCombinatorialManifold · n`. -/
@[simp]
theorem isCombinatorialManifold_stellarSubdivision_iff (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n ↔ IsCombinatorialManifold K n :=
  ⟨fun h => h.of_stellarSubdivision hσ hv, fun h => h.stellarSubdivision hσ hv⟩

/-- Same-type stellar equivalence preserves and reflects combinatorial `n`-manifolds (without any
finiteness assumption on the complexes). -/
theorem StellarEquivalent.isCombinatorialManifold_iff (h : StellarEquivalent K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  isCombinatorialManifold_iff_of_stellarEquivalent_of_ih
    (fun k _ => ballsAndSpheresManifoldAt k) h

/-- Intrinsic stellar equivalence up to relabeling preserves and reflects combinatorial
`n`-manifolds (without any finiteness assumption on the complexes). -/
theorem StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff
    (h : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  isCombinatorialManifold_iff_of_stellarEquivalentUpToRelabeling_of_ih
    (fun k _ => ballsAndSpheresManifoldAt k) h

end MainResults

section SphereLinks

/-- In a combinatorial `n`-sphere `K`, the link of every face `σ ∈ K` with `σ.card ≤ n` is a
combinatorial `(n - σ.card)`-sphere. -/
theorem IsCombinatorialSphere.isCombinatorialSphere_link
    {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {n : ℕ}
    (hK : IsCombinatorialSphere K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) := by
  rcases hK.isCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard
    with hs | hb
  · exact hs
  · have hpos : 1 ≤ σ.card := card_pos.mpr (K.isRelLowerSet_faces hσ).1
    cases n with
    | zero => omega
    | succ m =>
      cases hd : m + 1 - σ.card with
      | zero =>
        rw [hd, isCombinatorialBall_zero_iff] at hb
        obtain ⟨w, hw⟩ := hb
        have h2 := hK.encard_faces_link_eq_two hσ (by omega)
        rw [hw, faces_simplex_singleton, Set.encard_singleton] at h2
        exact ((by decide : (1 : ℕ∞) ≠ 2) h2).elim
      | succ k =>
        rw [hd] at hb
        obtain ⟨ρ, hρ, hρcard, hne2⟩ := hb.exists_encard_faces_link_ne_two
        obtain ⟨_, hdis, hρσ⟩ := mem_link_nonempty.mp hρ
        have hcard_union : (σ ∪ ρ).card = m + 1 := by
          rw [card_union_of_disjoint hdis.symm]; omega
        rw [link_link hdis.symm] at hne2
        exact (hne2 (hK.encard_faces_link_eq_two (union_comm ρ σ ▸ hρσ) hcard_union)).elim

/-- Spherical face links propagate upward in any precomplex: if `τ ⊆ σ` with `σ ∈ K`,
`σ.card ≤ n`, and `link K τ` is a combinatorial `(n - τ.card)`-sphere, then `link K σ` is a
combinatorial `(n - σ.card)`-sphere. -/
theorem isCombinatorialSphere_link_of_subset
    {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {τ σ : Finset ι} {n : ℕ}
    (hτσ : τ ⊆ σ) (hσ : σ ∈ K) (hcard : σ.card ≤ n)
    (hτS : IsCombinatorialSphere (link K τ) (n - τ.card)) :
    IsCombinatorialSphere (link K σ) (n - σ.card) := by
  by_cases heq : τ = σ
  · subst heq; exact hτS
  · have hle_card : τ.card ≤ σ.card := card_le_card hτσ
    have hsdiff_ne : (σ \ τ).Nonempty :=
      sdiff_nonempty.mpr fun hsub => heq (Subset.antisymm hτσ hsub)
    have hmem : σ \ τ ∈ link K τ := by
      refine mem_link_nonempty.mpr ⟨hsdiff_ne, disjoint_sdiff_self_left, ?_⟩
      rwa [sdiff_union_of_subset hτσ]
    have hcard_sdiff : (σ \ τ).card ≤ n - τ.card := by
      rw [card_sdiff_of_subset hτσ]
      omega
    have hS := hτS.isCombinatorialSphere_link hmem hcard_sdiff
    have hlink_eq : link (link K τ) (σ \ τ) = link K σ := by
      rw [link_link disjoint_sdiff_self_right, union_sdiff_of_subset hτσ]
    have hdim_eq : n - τ.card - (σ \ τ).card = n - σ.card := by
      rw [card_sdiff_of_subset hτσ]
      omega
    rwa [hlink_eq, hdim_eq] at hS

end SphereLinks

end PreAbstractSimplicialComplex
