/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Relabel
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Facet
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional

/-!
# Face links and stellar invariance of combinatorial manifolds

Every combinatorial `n`-sphere and combinatorial `n`-ball is a combinatorial `n`-manifold, the link
of any non-maximal face `σ` of a combinatorial `n`-sphere is a combinatorial `(n - σ.card)`-sphere,
the link of any non-maximal face `σ` of a combinatorial `n`-manifold is a combinatorial
`(n - σ.card)`-sphere or `(n - σ.card)`-ball, and being a combinatorial `n`-manifold is invariant
under stellar subdivision and intrinsic stellar equivalence.

When starring a face `σ ∈ K` at a fresh vertex `v`, the link of `v` in the subdivision is
`closedStar K σ ⊓ deletion K σ`, which after vertex tagging is `join (simplexBoundary σ) (link K σ)`
(`map_closedStar_inf_deletion_eq_join`). By strong induction on dimension, `link K σ` is already a
combinatorial sphere or ball, its join with `simplexBoundary σ` is a combinatorial sphere or ball of
dimension `n - 1`, and `CombinatorialManifold.Relabel` reflects that classification back across the
vertex tagging to discharge the new-vertex link condition in `Subdivision.Stellar.Manifold`.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialSphere.isCombinatorialSphere_link`: non-maximal face
  links in a combinatorial `n`-sphere are combinatorial `(n - σ.card)`-spheres.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.isCombinatorialManifold`: every combinatorial
  `n`-sphere is a combinatorial `n`-manifold.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.stellarSubdivision`: starring at any fresh
  vertex preserves a combinatorial `n`-manifold.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.of_stellarEquivalentUpToRelabeling` and
  `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff`:
  intrinsic stellar equivalence preserves and reflects combinatorial `n`-manifolds.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialManifold`: every combinatorial
  `n`-ball is a combinatorial `n`-manifold.
* `IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link` and
  `IsCombinatorialManifold.isCombinatorialManifold_link`: non-maximal face links in a combinatorial
  `n`-manifold are combinatorial `(n - σ.card)`-spheres or `(n - σ.card)`-balls, and arbitrary
  links `link K σ` are combinatorial `(n - σ.card)`-manifolds.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.isCombinatorialBall_closedStar`: the closed
  star of every face in a combinatorial `n`-manifold is a combinatorial `n`-ball.

## References

* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320, Propositions 3.1–3.2.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

universe u

section VertexLinkInvariance

private def AllVertexLinks
    (Q : ∀ {α : Type u} [DecidableEq α], PreAbstractSimplicialComplex α → Prop)
    {ι : Type u} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) : Prop :=
  ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → Q (link K {w})

private theorem allVertexLinks_map_iff
    {Q : ∀ {α : Type u} [DecidableEq α], PreAbstractSimplicialComplex α → Prop}
    (hQ_map : ∀ {α β : Type u} [DecidableEq α] [DecidableEq β]
      {M : PreAbstractSimplicialComplex α} (f : α → β),
      Function.Injective f → (Q (M.map f) ↔ Q M))
    {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    {K : PreAbstractSimplicialComplex ι} (f : ι → κ) (hf : Function.Injective f) :
    AllVertexLinks Q (K.map f) ↔ AllVertexLinks Q K := by
  constructor
  · intro h v hv
    have hs := h (singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩)
    rwa [← image_singleton, ← map_link f hf, hQ_map f hf] at hs
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hw
    rw [← image_singleton, ← map_link f hf, hQ_map f hf]
    exact h hv

private theorem allVertexLinks_stellarSubdivision
    {Q : ∀ {α : Type u} [DecidableEq α], PreAbstractSimplicialComplex α → Prop}
    (hQ_se : ∀ {α : Type u} [DecidableEq α] {M N : PreAbstractSimplicialComplex α},
      StellarEquivalent M N → Q N → Q M)
    {ι : Type u} [DecidableEq ι] {A : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}
    (hA : AllVertexLinks Q A) (hv : ({v} : Finset ι) ∉ A)
    (hnew : ({v} : Finset ι) ∈ stellarSubdivision A σ v →
      Q (link (stellarSubdivision A σ v) {v})) :
    AllVertexLinks Q (stellarSubdivision A σ v) := by
  intro w hw
  by_cases hwv : w = v
  · exact hwv ▸ hnew (hwv ▸ hw)
  · have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
    obtain ⟨hwA, havoid⟩ := (mem_stellarSubdivision_iff_of_notMem hvw).mp hw
    exact hQ_se (stellarEquivalent_link_stellarSubdivision_of_notMem
      (notMem_link_of_notMem hv) hvw (sdiff_nonempty.mpr havoid)).symm (hA hwA)

private theorem allVertexLinks_of_stellarSubdivision
    {Q : ∀ {α : Type u} [DecidableEq α], PreAbstractSimplicialComplex α → Prop}
    (hQ_se : ∀ {α : Type u} [DecidableEq α] {M N : PreAbstractSimplicialComplex α},
      StellarEquivalent M N → Q N → Q M)
    {ι : Type u} [DecidableEq ι] {A : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}
    (hB : AllVertexLinks Q (stellarSubdivision A σ v))
    (hσ : σ ∈ A) (hv : ({v} : Finset ι) ∉ A) :
    AllVertexLinks Q A := by
  intro w hw
  obtain ⟨u, hu, he⟩ := exists_stellarEquivalent_link_stellarSubdivision hσ hv hw
  exact hQ_se he (hB hu)

private theorem allVertexLinks_of_stellarEquivalentUpToRelabeling
    {Q : ∀ {α : Type u} [DecidableEq α], PreAbstractSimplicialComplex α → Prop}
    (hQ_map : ∀ {α β : Type u} [DecidableEq α] [DecidableEq β]
      {M : PreAbstractSimplicialComplex α} (f : α → β),
      Function.Injective f → (Q (M.map f) ↔ Q M))
    (hQ_se : ∀ {α : Type u} [DecidableEq α] {M N : PreAbstractSimplicialComplex α},
      StellarEquivalent M N → Q N → Q M)
    (hfwd : ∀ {α : Type u} [DecidableEq α] {A : PreAbstractSimplicialComplex α}
      {σ : Finset α} {v : α},
      AllVertexLinks Q A → σ ∈ A → ({v} : Finset α) ∉ A →
        AllVertexLinks Q (stellarSubdivision A σ v))
    {ι : Type u} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
    (he : StellarEquivalentUpToRelabeling K L) (hL : AllVertexLinks Q L) :
    AllVertexLinks Q K := by
  suffices hiff : ∀ {α : Type u} [DecidableEq α] {P R : PreAbstractSimplicialComplex α},
      StellarEquivalent P R → (AllVertexLinks Q P ↔ AllVertexLinks Q R) by
    have hKL : AllVertexLinks Q K ↔ AllVertexLinks Q L := by
      apply he.induction_on
      · intro A B f g hab
        exact (allVertexLinks_map_iff hQ_map f f.injective).symm.trans
          ((hiff hab).trans (allVertexLinks_map_iff hQ_map g g.injective))
      · exact fun _ => Iff.rfl
      · exact fun _ _ h => h.symm
      · exact fun _ _ _ h₁ h₂ => h₁.trans h₂
    exact hKL.mpr hL
  intro α _ P R hPR
  apply hPR.induction_on
  · intro A B hm
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hm
    exact ⟨fun hA => hfwd hA hσ hv,
      fun hB => allVertexLinks_of_stellarSubdivision hQ_se hB hσ hv⟩
  · exact fun _ => Iff.rfl
  · exact fun _ _ h => h.symm
  · exact fun _ _ _ h₁ h₂ => h₁.trans h₂

end VertexLinkInvariance

section SphericalLinks

private abbrev HasSphericalVertexLinks {ι : Type u} [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) : Prop :=
  AllVertexLinks (fun M => IsCombinatorialSphere M n) K

private theorem hasSphericalVertexLinks_isCombinatorialManifold {ι : Type u} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (h : HasSphericalVertexLinks K n) :
    IsCombinatorialManifold K (n + 1) :=
  isCombinatorialManifold_succ_iff.mpr fun _ hw => Or.inl (h hw)

private theorem isCombinatorialSphere_link_of_spherical_ih {m : ℕ}
    (ih : ∀ k < m, ∀ {α : Type u} [DecidableEq α] {M : PreAbstractSimplicialComplex α},
      IsCombinatorialSphere M (k + 1) → HasSphericalVertexLinks M k)
    {k : ℕ} (hk : k ≤ m) {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
    (hK : HasSphericalVertexLinks K k) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card ≤ k + 1) :
    IsCombinatorialSphere (link K σ) (k + 1 - σ.card) := by
  induction σ using Finset.induction_on generalizing k K with
  | empty => exact ((K.isRelLowerSet_faces hσ).1.ne_empty rfl).elim
  | insert u τ huτ ihτ =>
    by_cases hτ : τ = ∅
    · subst hτ
      simpa using hK (by simpa using hσ)
    · have hτne : τ.Nonempty := nonempty_iff_ne_empty.mpr hτ
      have hτpos : 1 ≤ τ.card := card_pos.mpr hτne
      have hcard_ins : (insert u τ).card = τ.card + 1 := card_insert_of_notMem huτ
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have huK : ({u} : Finset ι) ∈ K := singleton_mem_of_mem hσ (mem_insert_self u τ)
      have hτlink : τ ∈ link K {u} := mem_link_nonempty.mpr
        ⟨hτne, disjoint_singleton_right.mpr huτ, by rwa [union_singleton]⟩
      have hs := ihτ (by omega : k' ≤ m) (ih k' (by omega) (hK huK)) hτlink (by omega)
      rwa [link_link (disjoint_singleton_left.mpr huτ), singleton_union,
        show k' + 1 - τ.card = k' + 1 + 1 - (insert u τ).card by omega] at hs

private theorem hasSphericalVertexLinks_stellarSubdivision {n : ℕ}
    (ih : ∀ k < n, ∀ {α : Type u} [DecidableEq α] {M : PreAbstractSimplicialComplex α},
      IsCombinatorialSphere M (k + 1) → HasSphericalVertexLinks M k)
    {ι : Type u} [DecidableEq ι] {A : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}
    (hA : HasSphericalVertexLinks A n) (hσ : σ ∈ A) (hv : ({v} : Finset ι) ∉ A) :
    HasSphericalVertexLinks (stellarSubdivision A σ v) n := by
  refine allVertexLinks_stellarSubdivision
    (fun he hs => hs.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling)
    hA hv fun _ => ?_
  rw [link_stellarSubdivision_singleton hv]
  have hA_man := hasSphericalVertexLinks_isCombinatorialManifold hA
  have hle : σ.card ≤ n + 2 := hA_man.isPure.card_le hσ
  have hpos : 1 ≤ σ.card := card_pos.mpr (A.isRelLowerSet_faces hσ).1
  rcases eq_or_lt_of_le hpos with h1 | hgt1
  · obtain ⟨u, rfl⟩ := card_eq_one.mp h1.symm
    rw [closedStar_singleton_inf_deletion_singleton]
    exact hA hσ
  · rcases eq_or_lt_of_le hle with htop | hlt
    · rw [closedStar_inf_deletion_eq_simplexBoundary_of_link_eq_bot hσ
        ((hA_man.link_eq_bot_iff hσ).mpr htop)]
      exact isCombinatorialSphere_simplexBoundary htop
    · have hs_bdry : IsCombinatorialSphere (simplexBoundary σ) (σ.card - 2) :=
        isCombinatorialSphere_simplexBoundary (by omega)
      have hs_lk : IsCombinatorialSphere (link A σ) (n + 1 - σ.card) :=
        isCombinatorialSphere_link_of_spherical_ih ih le_rfl hA hσ (by omega)
      have hjoin : IsCombinatorialSphere (join (simplexBoundary σ) (link A σ)) n := by
        simpa [show σ.card - 2 + (n + 1 - σ.card) + 1 = n by omega] using hs_bdry.join hs_lk
      rw [← map_closedStar_inf_deletion_eq_join hσ] at hjoin
      exact IsCombinatorialSphere.of_map _ (TauCeti.partitionEmbedding (· ∈ σ)).injective hjoin

private theorem hasSphericalVertexLinks_of_stellarEquivalentUpToRelabeling {n : ℕ}
    (ih : ∀ k < n, ∀ {α : Type u} [DecidableEq α] {M : PreAbstractSimplicialComplex α},
      IsCombinatorialSphere M (k + 1) → HasSphericalVertexLinks M k)
    {ι : Type u} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
    (he : StellarEquivalentUpToRelabeling K L) (hL : HasSphericalVertexLinks L n) :
    HasSphericalVertexLinks K n :=
  allVertexLinks_of_stellarEquivalentUpToRelabeling
    (fun f hf => isCombinatorialSphere_map_iff f hf)
    (fun hse hs => hs.of_stellarEquivalentUpToRelabeling hse.stellarEquivalentUpToRelabeling)
    (fun hA hσ hv => hasSphericalVertexLinks_stellarSubdivision ih hA hσ hv)
    he hL

private theorem isCombinatorialSphere_hasSphericalVertexLinks :
    ∀ (n : ℕ) {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι},
      IsCombinatorialSphere K (n + 1) → HasSphericalVertexLinks K n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ι _ K hK
    obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hK
    refine hasSphericalVertexLinks_of_stellarEquivalentUpToRelabeling ih he fun w hw => ?_
    have hwV : {w} ⊆ V := singleton_subset_iff.mpr (singleton_mem_simplexBoundary.mp hw).1
    simpa using isCombinatorialSphere_link_simplexBoundary hV hwV (by simp)

/-- Every vertex link in a combinatorial `(n + 1)`-sphere is a combinatorial `n`-sphere. -/
theorem IsCombinatorialSphere.isCombinatorialSphere_link_singleton {ι : Type u} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (hK : IsCombinatorialSphere K (n + 1))
    {w : ι} (hw : ({w} : Finset ι) ∈ K) :
    IsCombinatorialSphere (link K {w}) n :=
  isCombinatorialSphere_hasSphericalVertexLinks n hK hw

/-- The link of any non-maximal face `σ` of a combinatorial `n`-sphere is a combinatorial
`(n - σ.card)`-sphere. -/
theorem IsCombinatorialSphere.isCombinatorialSphere_link {ι : Type u} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (hK : IsCombinatorialSphere K n)
    {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) := by
  have : 1 ≤ σ.card := card_pos.mpr (K.isRelLowerSet_faces hσ).1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact isCombinatorialSphere_link_of_spherical_ih
    (fun k _ _ _ _ hs => isCombinatorialSphere_hasSphericalVertexLinks k hs)
    le_rfl (isCombinatorialSphere_hasSphericalVertexLinks m hK) hσ hcard

/-- Every combinatorial `n`-sphere is a combinatorial `n`-manifold. -/
theorem IsCombinatorialSphere.isCombinatorialManifold {ι : Type u} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (hK : IsCombinatorialSphere K n) :
    IsCombinatorialManifold K n := by
  cases n with
  | zero => exact isCombinatorialManifold_zero_iff_dimension_le_zero.mpr hK.dimension_eq.le
  | succ n =>
    exact hasSphericalVertexLinks_isCombinatorialManifold
      (isCombinatorialSphere_hasSphericalVertexLinks n hK)

end SphericalLinks

section ManifoldInvariance

private theorem isCombinatorialSphere_or_isCombinatorialBall_link_of_ih {m : ℕ}
    (ih : ∀ k ≤ m, ∀ {α : Type u} [DecidableEq α] {M : PreAbstractSimplicialComplex α},
      IsCombinatorialBall M k → IsCombinatorialManifold M k)
    {k : ℕ} (hk : k ≤ m + 1) {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
    (hK : IsCombinatorialManifold K k) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card ≤ k) :
    IsCombinatorialSphere (link K σ) (k - σ.card) ∨
      IsCombinatorialBall (link K σ) (k - σ.card) := by
  induction σ using Finset.induction_on generalizing k K with
  | empty => exact ((K.isRelLowerSet_faces hσ).1.ne_empty rfl).elim
  | insert u τ huτ ihτ =>
    have : 1 ≤ (insert u τ).card := card_pos.mpr (insert_nonempty u τ)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    by_cases hτ : τ = ∅
    · subst hτ
      simpa using isCombinatorialManifold_succ_iff.mp hK (by simpa using hσ)
    · have hτne : τ.Nonempty := nonempty_iff_ne_empty.mpr hτ
      have : 1 ≤ τ.card := card_pos.mpr hτne
      have : (insert u τ).card = τ.card + 1 := card_insert_of_notMem huτ
      have huK : ({u} : Finset ι) ∈ K := singleton_mem_of_mem hσ (mem_insert_self u τ)
      have hτlink : τ ∈ link K {u} := mem_link_nonempty.mpr
        ⟨hτne, disjoint_singleton_right.mpr huτ, by rwa [union_singleton]⟩
      have hlu : IsCombinatorialManifold (link K {u}) k' :=
        (isCombinatorialManifold_succ_iff.mp hK huK).elim
          IsCombinatorialSphere.isCombinatorialManifold
          (ih k' (by omega))
      have hres := ihτ (by omega : k' ≤ m + 1) hlu hτlink (by omega)
      rwa [link_link (disjoint_singleton_left.mpr huτ), singleton_union,
        show k' - τ.card = k' + 1 - (insert u τ).card by omega] at hres

private theorem isCombinatorialManifold_stellarSubdivision_succ_aux {n : ℕ}
    (ih : ∀ k ≤ n, ∀ {α : Type u} [DecidableEq α] {M : PreAbstractSimplicialComplex α},
      IsCombinatorialBall M k → IsCombinatorialManifold M k)
    {ι : Type u} [DecidableEq ι] {A : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}
    (hA : IsCombinatorialManifold A (n + 1)) (hσ : σ ∈ A) (hv : ({v} : Finset ι) ∉ A) :
    IsCombinatorialManifold (stellarSubdivision A σ v) (n + 1) := by
  have hle : σ.card ≤ n + 2 := hA.isPure.card_le hσ
  have hpos : 1 ≤ σ.card := card_pos.mpr (A.isRelLowerSet_faces hσ).1
  rcases eq_or_lt_of_le hpos with h1 | hgt1
  · obtain ⟨u, rfl⟩ := card_eq_one.mp h1.symm
    apply hA.stellarSubdivision_succ hv
    rw [link_stellarSubdivision_singleton hv, closedStar_singleton_inf_deletion_singleton]
    exact isCombinatorialManifold_succ_iff.mp hA hσ
  · rcases eq_or_lt_of_le hle with htop | hlt
    · exact hA.stellarSubdivision_of_card hσ htop hv
    · apply hA.stellarSubdivision_succ hv
      rw [link_stellarSubdivision_singleton hv]
      have hs_bdry : IsCombinatorialSphere (simplexBoundary σ) (σ.card - 2) :=
        isCombinatorialSphere_simplexBoundary (by omega)
      have hemb := (TauCeti.partitionEmbedding (· ∈ σ)).injective
      rcases isCombinatorialSphere_or_isCombinatorialBall_link_of_ih ih le_rfl hA hσ (by omega)
          with hslk | hblk
      · left
        have hjoin : IsCombinatorialSphere (join (simplexBoundary σ) (link A σ)) n := by
          simpa [show σ.card - 2 + (n + 1 - σ.card) + 1 = n by omega] using hs_bdry.join hslk
        rw [← map_closedStar_inf_deletion_eq_join hσ] at hjoin
        exact IsCombinatorialSphere.of_map _ hemb hjoin
      · right
        have hjoin : IsCombinatorialBall (join (simplexBoundary σ) (link A σ)) n := by
          simpa [show σ.card - 2 + (n + 1 - σ.card) + 1 = n by omega] using hs_bdry.join_ball hblk
        rw [← map_closedStar_inf_deletion_eq_join hσ] at hjoin
        exact IsCombinatorialBall.of_map _ hemb hjoin

private theorem isCombinatorialManifold_of_stellarEquivalentUpToRelabeling_all :
    ∀ (n : ℕ) {ι : Type u} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι},
      StellarEquivalentUpToRelabeling K L → IsCombinatorialManifold L n →
        IsCombinatorialManifold K n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ι _ K L he hL
    cases n with
    | zero =>
      rw [isCombinatorialManifold_zero_iff_dimension_le_zero] at hL ⊢
      rwa [← he.dimension_eq]
    | succ m =>
      have ih_ball : ∀ k ≤ m, ∀ {α : Type u} [DecidableEq α] {M : PreAbstractSimplicialComplex α},
          IsCombinatorialBall M k → IsCombinatorialManifold M k := by
        intro k hk α _ M hM
        obtain ⟨V, hV, heM⟩ := isCombinatorialBall_iff.mp hM
        exact ih k (by omega) heM (isCombinatorialManifold_simplex hV)
      exact isCombinatorialManifold_succ_iff.mpr <|
        allVertexLinks_of_stellarEquivalentUpToRelabeling
          (Q := fun M => IsCombinatorialSphere M m ∨ IsCombinatorialBall M m)
          (fun f hf =>
            or_congr (isCombinatorialSphere_map_iff f hf) (isCombinatorialBall_map_iff f hf))
          (fun hse h =>
            have hse' := hse.stellarEquivalentUpToRelabeling
            h.imp (IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling hse')
              (IsCombinatorialBall.of_stellarEquivalentUpToRelabeling hse'))
          (fun hA hσ hv => isCombinatorialManifold_succ_iff.mp <|
            isCombinatorialManifold_stellarSubdivision_succ_aux ih_ball
              (isCombinatorialManifold_succ_iff.mpr hA) hσ hv)
          he (isCombinatorialManifold_succ_iff.mp hL)

/-- Being a combinatorial `n`-manifold transfers along an intrinsic stellar equivalence. -/
theorem IsCombinatorialManifold.of_stellarEquivalentUpToRelabeling {ι : Type u} [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (he : StellarEquivalentUpToRelabeling K L) (hL : IsCombinatorialManifold L n) :
    IsCombinatorialManifold K n :=
  isCombinatorialManifold_of_stellarEquivalentUpToRelabeling_all n he hL

/-- Intrinsic stellar equivalence preserves and reflects combinatorial `n`-manifolds. -/
theorem StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff {ι : Type u} [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (he : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  ⟨fun hK => hK.of_stellarEquivalentUpToRelabeling he.symm,
    fun hL => hL.of_stellarEquivalentUpToRelabeling he⟩

/-- Same-type stellar equivalence transfers combinatorial `n`-manifolds. -/
theorem IsCombinatorialManifold.of_stellarEquivalent {ι : Type u} [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (he : StellarEquivalent K L) (hL : IsCombinatorialManifold L n) :
    IsCombinatorialManifold K n :=
  hL.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling

/-- Same-type stellar equivalence preserves and reflects combinatorial `n`-manifolds. -/
theorem StellarEquivalent.isCombinatorialManifold_iff {ι : Type u} [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (he : StellarEquivalent K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  he.stellarEquivalentUpToRelabeling.isCombinatorialManifold_iff

/-- Starring any vertex set at a fresh vertex preserves a combinatorial `n`-manifold. This covers
actual faces, nonempty non-faces (which leave the complex unchanged), and the empty set (which
produces the void complex). -/
theorem IsCombinatorialManifold.stellarSubdivision {ι : Type u} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι} {n : ℕ}
    (hK : IsCombinatorialManifold K n) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (PreAbstractSimplicialComplex.stellarSubdivision K σ v) n := by
  by_cases hσne : σ = ∅
  · subst hσne
    simp
  · by_cases hσ : σ ∈ K
    · exact hK.of_stellarEquivalent (stellarEquivalent_stellarSubdivision hσ hv).symm
    · rwa [stellarSubdivision_eq_self_of_notMem hv (nonempty_iff_ne_empty.mpr hσne) hσ]

/-- Every combinatorial `n`-ball is a combinatorial `n`-manifold. -/
theorem IsCombinatorialBall.isCombinatorialManifold {ι : Type u} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (hK : IsCombinatorialBall K n) :
    IsCombinatorialManifold K n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp hK
  exact (isCombinatorialManifold_simplex hV).of_stellarEquivalentUpToRelabeling he

/-- The link of any non-maximal face `σ` of a combinatorial `n`-manifold is a combinatorial
`(n - σ.card)`-sphere or `(n - σ.card)`-ball. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link
    {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {n : ℕ}
    (hK : IsCombinatorialManifold K n) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) :=
  isCombinatorialSphere_or_isCombinatorialBall_link_of_ih
    (fun _ _ _ _ _ hb => hb.isCombinatorialManifold) (Nat.le_succ n) hK hσ hcard

/-- For any vertex set `σ`, the link `link K σ` in a combinatorial `n`-manifold is a combinatorial
`(n - σ.card)`-manifold (vacuously void when `σ` is a facet or a nonempty non-face, and `K` itself
when `σ = ∅`). -/
theorem IsCombinatorialManifold.isCombinatorialManifold_link
    {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {n : ℕ}
    (hK : IsCombinatorialManifold K n) (σ : Finset ι) :
    IsCombinatorialManifold (link K σ) (n - σ.card) := by
  by_cases hσ0 : σ = ∅
  · subst hσ0
    simpa using hK
  have hσne : σ.Nonempty := nonempty_iff_ne_empty.mpr hσ0
  by_cases hσ : σ ∈ K
  · rcases eq_or_lt_of_le (hK.isPure.card_le hσ) with htop | hlt
    · rw [(hK.link_eq_bot_iff hσ).mpr htop]
      exact isCombinatorialManifold_bot _
    · exact (hK.isCombinatorialSphere_or_isCombinatorialBall_link hσ (by omega)).elim
        IsCombinatorialSphere.isCombinatorialManifold
        IsCombinatorialBall.isCombinatorialManifold
  · have hbot : link K σ = ⊥ := eq_bot_iff.mpr fun ρ hρ =>
      hσ ((K.isRelLowerSet_faces (mem_link_nonempty.mp hρ).2.2).2 subset_union_right hσne)
    rw [hbot]
    exact isCombinatorialManifold_bot _

/-- The link of any non-maximal face `σ` of a combinatorial `n`-ball is a combinatorial
`(n - σ.card)`-sphere or `(n - σ.card)`-ball. -/
theorem IsCombinatorialBall.isCombinatorialSphere_or_isCombinatorialBall_link
    {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {n : ℕ}
    (hK : IsCombinatorialBall K n) {σ : Finset ι} (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) :=
  hK.isCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard

/-- The closed star of every face in a combinatorial `n`-manifold is a combinatorial `n`-ball. -/
theorem IsCombinatorialManifold.isCombinatorialBall_closedStar
    {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {n : ℕ}
    (hK : IsCombinatorialManifold K n) {σ : Finset ι} (hσ : σ ∈ K) :
    IsCombinatorialBall (closedStar K σ) n := by
  have hle : σ.card ≤ n + 1 := hK.isPure.card_le hσ
  have hpos : 1 ≤ σ.card := card_pos.mpr (K.isRelLowerSet_faces hσ).1
  rcases eq_or_lt_of_le hle with htop | hlt
  · rw [closedStar_eq_simplex_of_link_eq_bot hσ ((hK.link_eq_bot_iff hσ).mpr htop)]
    exact isCombinatorialBall_simplex htop
  · have hb_simp : IsCombinatorialBall (simplex σ) (σ.card - 1) :=
      isCombinatorialBall_simplex (by omega)
    have hemb := (TauCeti.partitionEmbedding (· ∈ σ)).injective
    rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hσ (by omega) with hslk | hblk
    · have hjoin : IsCombinatorialBall (join (simplex σ) (link K σ)) n := by
        simpa [map_join_swap, show (n - σ.card) + (σ.card - 1) + 1 = n by omega] using
          (hslk.join_ball hb_simp).map Sum.swap (Equiv.sumComm ι ι).injective
      rw [← map_closedStar_eq_join hσ] at hjoin
      exact IsCombinatorialBall.of_map _ hemb hjoin
    · have hjoin : IsCombinatorialBall (join (simplex σ) (link K σ)) n := by
        simpa [show (σ.card - 1) + (n - σ.card) + 1 = n by omega] using hb_simp.join hblk
      rw [← map_closedStar_eq_join hσ] at hjoin
      exact IsCombinatorialBall.of_map _ hemb hjoin

end ManifoldInvariance

end PreAbstractSimplicialComplex
