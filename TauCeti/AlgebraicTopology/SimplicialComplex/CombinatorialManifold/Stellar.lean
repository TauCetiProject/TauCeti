/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Star
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Facet

/-!
# Stellar invariance and higher-face links of combinatorial manifolds

This file establishes injective-relabeling reflection, higher-face link classification, and full
stellar invariance for combinatorial manifolds:

* **Injective relabeling invariance** (`isCombinatorialSphere_map_iff`,
  `isCombinatorialManifold_map_iff`): an injective map of vertex types preserves and reflects
  combinatorial spheres and combinatorial manifolds of a given dimension.
* **Higher-face link classification**
  (`IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`): for every face
  `σ` of cardinality `k ≤ n` in a combinatorial `n`-manifold `K`, `link K σ` is a combinatorial
  `(n - k)`-sphere or `(n - k)`-ball.
* **Stellar subdivision and stellar equivalence invariance**
  (`isCombinatorialManifold_stellarSubdivision_iff`,
  `StellarEquivalent.isCombinatorialManifold_iff`,
  `StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff`): starring a face at a fresh
  vertex, as well as arbitrary stellar equivalence up to relabeling, preserves and reflects
  combinatorial manifolds in all dimensions.
* **Balls and spheres are combinatorial manifolds**
  (`IsCombinatorialBall.isCombinatorialManifold`,
  `IsCombinatorialSphere.isCombinatorialManifold`).

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

universe u

variable {ι κ : Type*}

/-! ### Injective relabeling reflection for spheres and manifolds -/

/-- An injective vertex relabeling preserves and reflects combinatorial spheres. -/
@[simp]
theorem isCombinatorialSphere_map_iff [DecidableEq ι] [DecidableEq κ]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} {f : ι → κ} (hf : Function.Injective f) :
    IsCombinatorialSphere (K.map f) n ↔ IsCombinatorialSphere K n := by
  refine ⟨fun hs => ?_, fun hs => hs.map f hf⟩
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp hs.finite_faces
  have hdim : dimension K = (n : WithBot ℕ∞) :=
    (dimension_map_of_injective f hf).symm.trans hs.dimension_eq
  obtain ⟨σ, hσK, hσcard⟩ := exists_face_card_eq_of_dimension_eq hdim
  have hex : ∃ v : ι, v ∉ σ := by
    by_contra! hall
    have hKeq : K = simplex σ := le_antisymm
      (fun τ hτ => mem_simplex.mpr ⟨(K.isRelLowerSet_faces hτ).1, fun x _ => hall x⟩)
      (simplex_le_iff.mpr fun _ => hσK)
    exact hs.not_isCombinatorialBall (hKeq ▸ (isCombinatorialBall_simplex hσcard).map f hf)
  obtain ⟨v, hvσ⟩ := hex
  let V : Finset ι := insert v σ
  have hVcard : V.card = n + 2 := by rw [Finset.card_insert_of_notMem hvσ, hσcard]
  obtain ⟨W, hWcard, heW⟩ := isCombinatorialSphere_iff.mp hs
  have hVW : W.card = (V.image f).card := by
    rw [Finset.card_image_of_injective V hf, hVcard, hWcard]
  have hmapBdy : (simplexBoundary V).map f = simplexBoundary (V.image f) := by
    simpa only [Function.Embedding.coeFn_mk] using map_simplexBoundary V ⟨f, hf⟩
  have heVf : StellarEquivalentUpToRelabeling (K.map f) ((simplexBoundary V).map f) := by
    rw [hmapBdy]
    exact heW.trans (stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq hVW)
  exact isCombinatorialSphere_iff.mpr
    ⟨V, hVcard, (stellarEquivalentUpToRelabeling_map_iff hKfin hf).mp heVf⟩

/-- An injective vertex relabeling preserves and reflects combinatorial manifolds. -/
@[simp]
theorem isCombinatorialManifold_map_iff [DecidableEq ι] [DecidableEq κ]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} {f : ι → κ} (hf : Function.Injective f) :
    IsCombinatorialManifold (K.map f) n ↔ IsCombinatorialManifold K n := by
  cases n with
  | zero =>
      simp only [isCombinatorialManifold_zero_iff, singleton_mem_map_iff,
        forall_exists_index, and_imp]
      have hbot {P : PreAbstractSimplicialComplex ι} : P.map f = ⊥ ↔ P = ⊥ := by
        rw [← dimension_eq_bot_iff, dimension_map_of_injective f hf, dimension_eq_bot_iff]
      refine ⟨fun h v hv => ?_, fun h _ v hv hfv => ?_⟩
      · have := h v hv rfl
        rwa [← Finset.image_singleton f v, ← map_link f hf, hbot] at this
      · subst hfv
        rw [← Finset.image_singleton f v, ← map_link f hf, hbot]
        exact h hv
  | succ n =>
      simp only [isCombinatorialManifold_succ_iff, singleton_mem_map_iff,
        forall_exists_index, and_imp]
      refine ⟨fun h v hv => ?_, fun h _ v hv hfv => ?_⟩
      · have := h v hv rfl
        rwa [← Finset.image_singleton f v, ← map_link f hf,
          isCombinatorialSphere_map_iff hf, isCombinatorialBall_map_iff hf] at this
      · subst hfv
        rw [← Finset.image_singleton f v, ← map_link f hf,
          isCombinatorialSphere_map_iff hf, isCombinatorialBall_map_iff hf]
        exact h hv

/-! ### Inverse stellar subdivision on combinatorial manifolds -/

/-- Inverse stellar move for combinatorial manifolds: if starring a face `σ ∈ K` at a fresh vertex
`v` produces a combinatorial `n`-manifold, then `K` was already a combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.of_stellarSubdivision [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι} {n : ℕ}
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hL : IsCombinatorialManifold (stellarSubdivision K σ v) n) :
    IsCombinatorialManifold K n := by
  cases n with
  | zero =>
      refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
      have hvw : v ∉ ({w} : Finset ι) := by
        simp only [Finset.mem_singleton]; rintro rfl; exact hv hw
      by_cases hsub : σ ⊆ {w}
      · have hσw : σ = {w} := ((K.isRelLowerSet_faces hσ).1).subset_singleton_iff.mp hsub
        subst hσw
        have hbot := isCombinatorialManifold_zero_iff.mp hL
          (singleton_mem_stellarSubdivision_iff.mpr hw)
        rwa [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton] at hbot
      · have hwL : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
          (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsub⟩
        have he := stellarEquivalent_link_stellarSubdivision_of_notMem
          (notMem_link_of_notMem hv) hvw (Finset.sdiff_nonempty.mpr hsub)
        apply dimension_eq_bot_iff.mp
        rw [← he.dimension_eq, isCombinatorialManifold_zero_iff.mp hL hwL, dimension_bot]
  | succ n =>
      refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
      have hvw : v ∉ ({w} : Finset ι) := by
        simp only [Finset.mem_singleton]; rintro rfl; exact hv hw
      by_cases hsub : σ ⊆ {w}
      · have hσw : σ = {w} := ((K.isRelLowerSet_faces hσ).1).subset_singleton_iff.mp hsub
        subst hσw
        have hlink := isCombinatorialManifold_succ_iff.mp hL
          (singleton_mem_stellarSubdivision_iff.mpr hw)
        rwa [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton] at hlink
      · have hwL : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
          (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsub⟩
        have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
          (notMem_link_of_notMem hv) hvw (Finset.sdiff_nonempty.mpr hsub)
            ).stellarEquivalentUpToRelabeling
        exact (isCombinatorialManifold_succ_iff.mp hL hwL).imp
          (IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling he)
          (IsCombinatorialBall.of_stellarEquivalentUpToRelabeling he)

/-! ### Simultaneous induction across dimensions: face links, stellar moves, balls, and spheres -/

private def ManifoldStep (n : ℕ) : Prop :=
  (∀ {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α},
    IsCombinatorialManifold K n → σ ∈ K → σ.card ≤ n →
      IsCombinatorialSphere (link K σ) (n - σ.card) ∨
        IsCombinatorialBall (link K σ) (n - σ.card)) ∧
  (∀ {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α} {v : α},
    IsCombinatorialManifold K n → σ ∈ K → ({v} : Finset α) ∉ K →
      IsCombinatorialManifold (stellarSubdivision K σ v) n) ∧
  (∀ {α : Type u} [DecidableEq α] {K L : PreAbstractSimplicialComplex α},
    StellarEquivalentUpToRelabeling K L →
      (IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n)) ∧
  (∀ {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α},
    (IsCombinatorialSphere K n → IsCombinatorialManifold K n) ∧
      (IsCombinatorialBall K n → IsCombinatorialManifold K n))

private theorem close_manifoldStep_from_subdivision {n : ℕ}
    (hlink : ∀ {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α},
      IsCombinatorialManifold K n → σ ∈ K → σ.card ≤ n →
        IsCombinatorialSphere (link K σ) (n - σ.card) ∨
          IsCombinatorialBall (link K σ) (n - σ.card))
    (hsub : ∀ {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α}
      {v : α}, IsCombinatorialManifold K n → σ ∈ K → ({v} : Finset α) ∉ K →
        IsCombinatorialManifold (stellarSubdivision K σ v) n) :
    ManifoldStep.{u} n := by
  have hstellar : ∀ {α : Type u} [DecidableEq α] {K L : PreAbstractSimplicialComplex α},
      StellarEquivalent K L → (IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n) := by
    intro α _ K L hKL
    apply hKL.induction_on
    · intro A B hmove
      obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hmove
      exact ⟨fun hA => hsub hA hσ hv, IsCombinatorialManifold.of_stellarSubdivision hσ hv⟩
    · intro _; rfl
    · intro _ _ ih; exact ih.symm
    · intro _ _ _ ih₁ ih₂; exact ih₁.trans ih₂
  have hrel : ∀ {α : Type u} [DecidableEq α] {K L : PreAbstractSimplicialComplex α},
      StellarEquivalentUpToRelabeling K L →
        (IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n) := by
    intro α _ K L hKL
    apply hKL.induction_on
    · intro A B f g he
      exact (isCombinatorialManifold_map_iff f.injective).symm.trans
        ((hstellar he).trans (isCombinatorialManifold_map_iff g.injective))
    · intro _; rfl
    · intro _ _ ih; exact ih.symm
    · intro _ _ _ ih₁ ih₂; exact ih₁.trans ih₂
  refine ⟨hlink, hsub, hrel, fun {α} _ {K} => ⟨fun hs => ?_, fun hb => ?_⟩⟩
  · obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hs
    exact (hrel he).mpr (isCombinatorialManifold_simplexBoundary hV)
  · obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp hb
    exact (hrel he).mpr (isCombinatorialManifold_simplex hV)

private theorem manifoldStep_link_succ {n : ℕ} (ih : ManifoldStep.{u} n)
    {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α}
    (hK : IsCombinatorialManifold K (n + 1)) (hσ : σ ∈ K) (hcard : σ.card ≤ n + 1) :
    IsCombinatorialSphere (link K σ) (n + 1 - σ.card) ∨
      IsCombinatorialBall (link K σ) (n + 1 - σ.card) := by
  obtain ⟨w, hwσ⟩ := (K.isRelLowerSet_faces hσ).1
  have hwK : ({w} : Finset α) ∈ K := singleton_mem_of_mem hσ hwσ
  rcases eq_or_ne (σ.erase w) ∅ with hempty | hne
  · have hσw : σ = {w} := by
      rw [← Finset.insert_erase hwσ, hempty, Finset.insert_empty]
    subst hσw
    simpa only [Finset.card_singleton, Nat.add_sub_cancel] using
      isCombinatorialManifold_succ_iff.mp hK hwK
  · have hτne : (σ.erase w).Nonempty := Finset.nonempty_of_ne_empty hne
    have hdis : Disjoint ({w} : Finset α) (σ.erase w) :=
      Finset.disjoint_singleton_left.mpr (Finset.notMem_erase w σ)
    have hτlink : σ.erase w ∈ link K {w} :=
      mem_link_nonempty.mpr ⟨hτne, hdis.symm, by
        rwa [Finset.union_singleton, Finset.insert_erase hwσ]⟩
    have hMlink : IsCombinatorialManifold (link K {w}) n :=
      (isCombinatorialManifold_succ_iff.mp hK hwK).elim ih.2.2.2.1 ih.2.2.2.2
    have hcard_erase := Finset.card_erase_of_mem hwσ
    have hcard_pos := Finset.card_pos.mpr ⟨w, hwσ⟩
    have hpeel : link K σ = link (link K {w}) (σ.erase w) := by
      rw [link_link hdis, Finset.singleton_union, Finset.insert_erase hwσ]
    have hdim_eq : n - (σ.erase w).card = n + 1 - σ.card := by omega
    rw [hpeel, ← hdim_eq]
    exact ih.1 hMlink hτlink (by omega)

private theorem manifoldStep_subdivision_succ {n : ℕ}
    (hlink : ∀ {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α},
      IsCombinatorialManifold K (n + 1) → σ ∈ K → σ.card ≤ n + 1 →
        IsCombinatorialSphere (link K σ) (n + 1 - σ.card) ∨
          IsCombinatorialBall (link K σ) (n + 1 - σ.card))
    {α : Type u} [DecidableEq α] {K : PreAbstractSimplicialComplex α} {σ : Finset α} {v : α}
    (hK : IsCombinatorialManifold K (n + 1)) (hσ : σ ∈ K) (hv : ({v} : Finset α) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) (n + 1) := by
  have hcard_le : σ.card ≤ n + 2 := by
    have : σ.card - 1 ≤ n + 1 := by exact_mod_cast dimension_le_iff.mp hK.dimension_le σ hσ
    omega
  have hcard_pos : 1 ≤ σ.card := Finset.card_pos.mpr (K.isRelLowerSet_faces hσ).1
  rcases eq_or_lt_of_le hcard_le with htop | hlt
  · exact hK.stellarSubdivision_of_card hσ htop hv
  · rcases eq_or_lt_of_le hcard_pos with h1 | h2
    · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1.symm
      apply hK.stellarSubdivision_succ hv
      rw [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton]
      exact isCombinatorialManifold_succ_iff.mp hK hσ
    · apply hK.stellarSubdivision_succ hv
      have hσbdy : IsCombinatorialSphere (simplexBoundary σ) (σ.card - 2) :=
        isCombinatorialSphere_simplexBoundary (by omega)
      have hdim_join : (σ.card - 2) + (n + 1 - σ.card) + 1 = n := by omega
      have hjoin :
          IsCombinatorialSphere (join (simplexBoundary σ) (link K σ)) n ∨
            IsCombinatorialBall (join (simplexBoundary σ) (link K σ)) n := by
        rw [← hdim_join]
        exact (hlink hK hσ (by omega)).imp hσbdy.join hσbdy.join_ball
      have hmap_eq :
          (link (stellarSubdivision K σ v) {v}).map (partitionEmbedding (· ∈ σ)) =
            join (simplexBoundary σ) (link K σ) := by
        rw [link_stellarSubdivision_singleton hv, map_closedStar_inf_deletion_eq_join hσ]
      rw [← hmap_eq, isCombinatorialSphere_map_iff (partitionEmbedding _).injective,
        isCombinatorialBall_map_iff (partitionEmbedding _).injective] at hjoin
      exact hjoin

private theorem manifoldStep (n : ℕ) : ManifoldStep.{u} n := by
  induction n with
  | zero =>
      refine close_manifoldStep_from_subdivision ?_ ?_
      · intro α _ K σ _ hσ hcard
        have := Finset.card_pos.mpr (K.isRelLowerSet_faces hσ).1
        omega
      · intro α _ K σ v hK hσ hv
        obtain ⟨w, rfl⟩ := dimension_le_zero_iff.mp hK.dimension_le σ hσ
        exact hK.stellarSubdivision_of_card hσ (Finset.card_singleton w) hv
  | succ n ih =>
      exact close_manifoldStep_from_subdivision
        (manifoldStep_link_succ ih)
        (manifoldStep_subdivision_succ (manifoldStep_link_succ ih))

/-- For every non-maximal face `σ` (`σ.card ≤ n`) in a combinatorial `n`-manifold `K`,
`link K σ` is a combinatorial `(n - σ.card)`-sphere or `(n - σ.card)`-ball. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {n : ℕ}
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) :=
  (manifoldStep n).1 hK hσ hcard

/-- Starring any face of a combinatorial `n`-manifold at a fresh vertex yields another
combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.stellarSubdivision [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι} {n : ℕ}
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n :=
  (manifoldStep n).2.1 hK hσ hv

/-- Starring a face at a fresh vertex preserves and reflects combinatorial manifolds. -/
@[simp]
theorem isCombinatorialManifold_stellarSubdivision_iff [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι} {n : ℕ}
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n ↔ IsCombinatorialManifold K n :=
  ⟨IsCombinatorialManifold.of_stellarSubdivision hσ hv,
    fun hK => hK.stellarSubdivision hσ hv⟩

/-- Intrinsic stellar equivalence preserves and reflects combinatorial manifolds. -/
theorem StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (h : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  (manifoldStep n).2.2.1 h

/-- Same-type stellar equivalence preserves and reflects combinatorial manifolds. -/
theorem StellarEquivalent.isCombinatorialManifold_iff [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (h : StellarEquivalent K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  h.stellarEquivalentUpToRelabeling.isCombinatorialManifold_iff

/-- Being a combinatorial manifold transfers along an intrinsic stellar equivalence. -/
theorem IsCombinatorialManifold.of_stellarEquivalentUpToRelabeling [DecidableEq ι]
    {K L : PreAbstractSimplicialComplex ι} {n : ℕ}
    (h : StellarEquivalentUpToRelabeling K L) (hL : IsCombinatorialManifold L n) :
    IsCombinatorialManifold K n :=
  h.isCombinatorialManifold_iff.mpr hL

/-- Every combinatorial `n`-sphere is a combinatorial `n`-manifold. -/
theorem IsCombinatorialSphere.isCombinatorialManifold [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (h : IsCombinatorialSphere K n) :
    IsCombinatorialManifold K n :=
  (manifoldStep n).2.2.2.1 h

/-- Every combinatorial `n`-ball is a combinatorial `n`-manifold. -/
theorem IsCombinatorialBall.isCombinatorialManifold [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ} (h : IsCombinatorialBall K n) :
    IsCombinatorialManifold K n :=
  (manifoldStep n).2.2.2.2 h

end PreAbstractSimplicialComplex
