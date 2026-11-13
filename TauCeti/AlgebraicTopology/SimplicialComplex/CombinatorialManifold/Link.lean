/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Pure
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Manifold

/-!
# Higher-face links and stellar invariance of combinatorial manifolds

In a combinatorial `n`-manifold, not only vertex links but the link of every face `σ` with
`σ.card ≤ n` is a combinatorial `(n - σ.card)`-sphere or `(n - σ.card)`-ball. Together with the
join decomposition of closed-star boundaries (`Join.Star`), this classifies the link of the new
vertex in any stellar subdivision of a combinatorial manifold and completes full invariance of
`IsCombinatorialManifold` under stellar moves and intrinsic stellar equivalence. In particular,
every combinatorial `n`-ball and every combinatorial `n`-sphere is a combinatorial `n`-manifold,
and every face below top dimension in a combinatorial `n`-sphere has a combinatorial sphere link.

Because higher-face link classification in dimension `n`, stellar invariance of combinatorial
`n`-manifolds, and the manifold property of balls and spheres in dimensions `< n` depend mutually
on one another across dimension, they are established together here and then exposed as separate
public theorems.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialManifold` and
  `PreAbstractSimplicialComplex.IsCombinatorialSphere.isCombinatorialManifold`: combinatorial
  `n`-balls and `n`-spheres are combinatorial `n`-manifolds.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold` link classification
  (`isCombinatorialSphere_or_isCombinatorialBall_link`):
  the link of a face `σ` with `σ.card ≤ n` in a combinatorial `n`-manifold is a combinatorial
  `(n - σ.card)`-sphere or `(n - σ.card)`-ball.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.isCombinatorialManifold_link`: the link of
  any finset `σ` in a combinatorial `n`-manifold is a combinatorial `(n - σ.card)`-manifold.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.isCombinatorialSphere_link`: the link of a
  face `σ` with `σ.card ≤ n` in a combinatorial `n`-sphere is a combinatorial
  `(n - σ.card)`-sphere.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.stellarSubdivision_iff` and
  `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff`:
  stellar subdivision and intrinsic stellar equivalence preserve and reflect combinatorial
  manifolds.

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

/-- The void precomplex is vacuously a combinatorial `n`-manifold in every dimension. -/
@[simp]
theorem isCombinatorialManifold_bot {ι : Type*} [DecidableEq ι] {n : ℕ} :
    IsCombinatorialManifold (⊥ : PreAbstractSimplicialComplex ι) n := by
  cases n with
  | zero => exact isCombinatorialManifold_zero_iff.mpr fun _ hv => hv.elim
  | succ _ => exact isCombinatorialManifold_succ_iff.mpr fun _ hv => hv.elim

/-- Backward invariance of combinatorial manifolds along a stellar move: if starring `σ ∈ K` at a
fresh vertex `v` yields a combinatorial `n`-manifold, then `K` was already a combinatorial
`n`-manifold. -/
theorem IsCombinatorialManifold.of_stellarSubdivision {ι : Type*} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι} {n : ℕ}
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hsub : IsCombinatorialManifold (stellarSubdivision K σ v) n) :
    IsCombinatorialManifold K n := by
  have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
  cases n with
  | zero =>
      refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
      by_cases hsubw : σ ⊆ {w}
      · obtain rfl : σ = {w} := (Finset.subset_singleton_iff.mp hsubw).resolve_left hσne.ne_empty
        have hvmem : ({v} : Finset ι) ∈ stellarSubdivision K {w} v :=
          singleton_mem_stellarSubdivision_iff.mpr hw
        have hbot := isCombinatorialManifold_zero_iff.mp hsub hvmem
        rwa [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton] at hbot
      · have hwmem : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
          (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsubw⟩
        have hbot := isCombinatorialManifold_zero_iff.mp hsub hwmem
        have he := stellarEquivalent_link_stellarSubdivision_of_notMem
          (notMem_link_of_notMem hv) hvw (Finset.sdiff_nonempty.mpr hsubw)
        exact dimension_eq_bot_iff.mp (by rw [← he.dimension_eq, hbot, dimension_bot])
  | succ m =>
      refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
      by_cases hsubw : σ ⊆ {w}
      · obtain rfl : σ = {w} := (Finset.subset_singleton_iff.mp hsubw).resolve_left hσne.ne_empty
        have hvmem : ({v} : Finset ι) ∈ stellarSubdivision K {w} v :=
          singleton_mem_stellarSubdivision_iff.mpr hw
        have hlink := isCombinatorialManifold_succ_iff.mp hsub hvmem
        rwa [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton] at hlink
      · have hwmem : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
          (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsubw⟩
        have hlink := isCombinatorialManifold_succ_iff.mp hsub hwmem
        have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
          (notMem_link_of_notMem hv) hvw
          (Finset.sdiff_nonempty.mpr hsubw)).stellarEquivalentUpToRelabeling
        exact hlink.imp
          (IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling he)
          (IsCombinatorialBall.of_stellarEquivalentUpToRelabeling he)

private theorem forall_isCombinatorialSphere_link_of_stellarSubdivision {ι : Type*}
    [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι} {m : ℕ}
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hsub : ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ stellarSubdivision K σ v →
      IsCombinatorialSphere (link (stellarSubdivision K σ v) {w}) m) :
    ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → IsCombinatorialSphere (link K {w}) m := by
  have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
  intro w hw
  have hwv : w ≠ v := fun h => hv (h ▸ hw)
  have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
  by_cases hsubw : σ ⊆ {w}
  · obtain rfl : σ = {w} := (Finset.subset_singleton_iff.mp hsubw).resolve_left hσne.ne_empty
    have hvmem : ({v} : Finset ι) ∈ stellarSubdivision K {w} v :=
      singleton_mem_stellarSubdivision_iff.mpr hw
    have hlink := hsub hvmem
    rwa [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton] at hlink
  · have hwmem : ({w} : Finset ι) ∈ stellarSubdivision K σ v :=
      (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsubw⟩
    have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
      (notMem_link_of_notMem hv) hvw
      (Finset.sdiff_nonempty.mpr hsubw)).stellarEquivalentUpToRelabeling
    exact IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling he (hsub hwmem)

private def ManifoldDimStep (n : ℕ) : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι),
    (IsCombinatorialBall K n → IsCombinatorialManifold K n) ∧
    (IsCombinatorialSphere K n → IsCombinatorialManifold K n) ∧
    ∀ m, n = m + 1 → IsCombinatorialSphere K n →
      ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → IsCombinatorialSphere (link K {v}) m

private theorem link_face_of_lt_step {n : ℕ} (ih : ∀ d < n, ManifoldDimStep.{u} d) :
    ∀ (k : ℕ) {d : ℕ} (_hd : d ≤ n) {ι : Type u} [DecidableEq ι]
      {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} (_hσ : σ ∈ K)
      (_hcard : σ.card = k + 1) (_hle : k + 1 ≤ d),
      (IsCombinatorialManifold K d →
        IsCombinatorialSphere (link K σ) (d - (k + 1)) ∨
          IsCombinatorialBall (link K σ) (d - (k + 1))) ∧
      (∀ m, d = m + 1 →
        (∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → IsCombinatorialSphere (link K {w}) m) →
        IsCombinatorialSphere (link K σ) (d - (k + 1)))
  | 0, d, _, _, _, K, σ, hσ, hcard, hle => by
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      cases d with
      | zero => omega
      | succ m =>
          refine ⟨fun hK => ?_, fun m' hm' hall => ?_⟩
          · simpa using isCombinatorialManifold_succ_iff.mp hK hσ
          · obtain rfl : m = m' := Nat.succ.inj hm'
            simpa using hall hσ
  | k + 1, d, hd, ι, _, K, σ, hσ, hcard, hle => by
      cases d with
      | zero => omega
      | succ m =>
          have hmn : m < n := by omega
          obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
          have hvK : ({v} : Finset ι) ∈ K := singleton_mem_of_mem hσ hv
          let τ : Finset ι := σ.erase v
          have hτcard : τ.card = k + 1 := by
            rw [Finset.card_erase_of_mem hv, hcard]
            rfl
          have hτne : τ.Nonempty := Finset.card_pos.mp (by omega)
          have hdis : Disjoint ({v} : Finset ι) τ :=
            Finset.disjoint_singleton_left.mpr (Finset.notMem_erase v σ)
          have hunion : τ ∪ {v} = σ := by
            rw [Finset.union_singleton, Finset.insert_erase hv]
          have hτmem : τ ∈ link K {v} :=
            mem_link_nonempty.mpr ⟨hτne, hdis.symm, hunion ▸ hσ⟩
          have hlinkeq : link K σ = link (link K {v}) τ := by
            rw [← hunion, Finset.union_comm, ← link_link hdis]
          have hsubeq : m + 1 - (k + 2) = m - (k + 1) := by omega
          have hrec := link_face_of_lt_step ih k (Nat.le_of_lt hmn) hτmem hτcard (by omega)
          refine ⟨fun hK => ?_, fun m' hm' hall => ?_⟩
          · have hLman : IsCombinatorialManifold (link K {v}) m := by
              rcases isCombinatorialManifold_succ_iff.mp hK hvK with hs | hb
              · exact (ih m hmn (link K {v})).2.1 hs
              · exact (ih m hmn (link K {v})).1 hb
            rw [hlinkeq, hsubeq]
            exact hrec.1 hLman
          · obtain rfl : m = m' := Nat.succ.inj hm'
            have hs : IsCombinatorialSphere (link K {v}) m := hall hvK
            cases m with
            | zero => omega
            | succ r =>
                have hallL := (ih (r + 1) hmn (link K {v})).2.2 r rfl hs
                rw [hlinkeq, hsubeq]
                exact hrec.2 r rfl hallL

private theorem stellarSubdivision_of_lt_step {n : ℕ} (ih : ∀ d < n, ManifoldDimStep.{u} d)
    {ι : Type u} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    (IsCombinatorialManifold K n → IsCombinatorialManifold (stellarSubdivision K σ v) n) ∧
    (∀ m, n = m + 1 →
      (∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → IsCombinatorialSphere (link K {w}) m) →
      ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ stellarSubdivision K σ v →
        IsCombinatorialSphere (link (stellarSubdivision K σ v) {w}) m) := by
  cases n with
  | zero =>
      refine ⟨fun hK => ?_, fun m hm => nomatch hm⟩
      obtain ⟨u, rfl⟩ := dimension_le_zero_iff.mp hK.dimension_le σ hσ
      refine hK.stellarSubdivision_zero ?_
      rw [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton]
      exact isCombinatorialManifold_zero_iff.mp hK hσ
  | succ m =>
      have hnew (hK : IsCombinatorialManifold K (m + 1)) :
          ((∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → IsCombinatorialSphere (link K {w}) m) →
            IsCombinatorialSphere (closedStar K σ ⊓ deletion K σ) m) ∧
          (IsCombinatorialSphere (closedStar K σ ⊓ deletion K σ) m ∨
            IsCombinatorialBall (closedStar K σ ⊓ deletion K σ) m) := by
        have hσpos : 1 ≤ σ.card := Finset.card_pos.mpr (K.isRelLowerSet_faces hσ).1
        have hσmax : σ.card ≤ m + 2 := by
          have hle := (le_dimension hσ).trans hK.dimension_le
          have hle' : σ.card - 1 ≤ m + 1 := by exact_mod_cast hle
          omega
        by_cases h1 : σ.card = 1
        · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp h1
          rw [closedStar_inf_deletion_singleton]
          exact ⟨fun hall => hall hσ, isCombinatorialManifold_succ_iff.mp hK hσ⟩
        · by_cases htop : σ.card = m + 2
          · have hbot : link K σ = ⊥ := (hK.link_eq_bot_iff hσ).mpr htop
            rw [closedStar_inf_deletion_eq_simplexBoundary_of_link_eq_bot hσ hbot]
            have hs := isCombinatorialSphere_simplexBoundary htop
            exact ⟨fun _ => hs, Or.inl hs⟩
          · have h2 : 2 ≤ σ.card := by omega
            have hsb : IsCombinatorialSphere (simplexBoundary σ) (σ.card - 2) :=
              isCombinatorialSphere_simplexBoundary (by omega)
            have hstep := link_face_of_lt_step ih (σ.card - 1) le_rfl hσ (by omega) (by omega)
            have hdim : σ.card - 2 + (m + 1 - (σ.card - 1 + 1)) + 1 = m := by omega
            have mkSphere (hslk : IsCombinatorialSphere (link K σ)
                (m + 1 - (σ.card - 1 + 1))) :
                IsCombinatorialSphere (closedStar K σ ⊓ deletion K σ) m := by
              refine IsCombinatorialSphere.of_map (partitionEmbedding (· ∈ σ))
                (partitionEmbedding (· ∈ σ)).injective ?_
              rw [map_closedStar_inf_deletion_eq_join hσ, ← hdim]
              exact hsb.join hslk
            refine ⟨fun hall => mkSphere (hstep.2 m rfl hall), ?_⟩
            rcases hstep.1 hK with hslk | hblk
            · exact Or.inl (mkSphere hslk)
            · refine Or.inr (IsCombinatorialBall.of_map (partitionEmbedding (· ∈ σ))
                (partitionEmbedding (· ∈ σ)).injective ?_)
              rw [map_closedStar_inf_deletion_eq_join hσ, ← hdim]
              exact hsb.join_ball hblk
      refine ⟨fun hK => hK.stellarSubdivision_succ hv
        (by rw [link_stellarSubdivision_singleton hv]; exact (hnew hK).2),
        fun m' hm' hall => ?_⟩
      obtain rfl : m = m' := Nat.succ.inj hm'
      have hK : IsCombinatorialManifold K (m + 1) :=
        isCombinatorialManifold_succ_iff.mpr fun w hw => Or.inl (hall hw)
      intro w hw
      by_cases hwv : w = v
      · subst hwv
        rw [link_stellarSubdivision_singleton hv]
        exact (hnew hK).1 hall
      · have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
        obtain ⟨hwK, havoid⟩ := (mem_stellarSubdivision_iff_of_notMem hvw).mp hw
        have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
          (notMem_link_of_notMem hv) hvw
          (Finset.sdiff_nonempty.mpr havoid)).symm.stellarEquivalentUpToRelabeling
        exact IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling he (hall hwK)

private theorem stellarEquivalent_of_lt_step {n : ℕ} (ih : ∀ d < n, ManifoldDimStep.{u} d)
    {ι : Type u} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
    (he : StellarEquivalent K L) :
    (IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n) ∧
    (∀ m, n = m + 1 →
      ((∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → IsCombinatorialSphere (link K {w}) m) ↔
        (∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ L → IsCombinatorialSphere (link L {w}) m))) := by
  apply StellarEquivalent.induction_on he
  · intro X Y hm
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hm
    have hfwd := stellarSubdivision_of_lt_step ih hσ hv
    exact ⟨⟨hfwd.1, IsCombinatorialManifold.of_stellarSubdivision hσ hv⟩,
      fun m hm' => ⟨hfwd.2 m hm', forall_isCombinatorialSphere_link_of_stellarSubdivision hσ hv⟩⟩
  · intro _
    exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩
  · intro _ _ hrec
    exact ⟨hrec.1.symm, fun m hm => (hrec.2 m hm).symm⟩
  · intro _ _ _ h₁ h₂
    exact ⟨h₁.1.trans h₂.1, fun m hm => (h₁.2 m hm).trans (h₂.2 m hm)⟩

private theorem forall_isCombinatorialSphere_link_map_iff {ι : Type u} {κ : Type*}
    [DecidableEq ι] [DecidableEq κ] {K : PreAbstractSimplicialComplex ι} {m : ℕ}
    (f : ι → κ) (hf : Function.Injective f) :
    (∀ ⦃y : κ⦄, ({y} : Finset κ) ∈ K.map f → IsCombinatorialSphere (link (K.map f) {y}) m) ↔
      (∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → IsCombinatorialSphere (link K {v}) m) := by
  constructor
  · intro hall v hv
    have hfv : ({f v} : Finset κ) ∈ K.map f := singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩
    have hs := hall hfv
    rw [← Finset.image_singleton f v, ← map_link f hf] at hs
    exact IsCombinatorialSphere.of_map f hf hs
  · intro hall _ hy
    obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hy
    rw [← Finset.image_singleton f v, ← map_link f hf]
    exact (hall hv).map f hf

private theorem manifoldDimStep (n : ℕ) : ManifoldDimStep.{u} n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro ι _ K
      refine ⟨fun hb => ?_, fun hs => ?_, fun m hm hs => ?_⟩
      · obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp hb
        obtain ⟨f, g, hfg⟩ := he.exists_common_relabeling hb.finite_faces
        rw [← IsCombinatorialManifold.map_iff_of_injective f f.injective,
          (stellarEquivalent_of_lt_step ih hfg).1,
          IsCombinatorialManifold.map_iff_of_injective g g.injective]
        exact isCombinatorialManifold_simplex hV
      · obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hs
        obtain ⟨f, g, hfg⟩ := he.exists_common_relabeling hs.finite_faces
        rw [← IsCombinatorialManifold.map_iff_of_injective f f.injective,
          (stellarEquivalent_of_lt_step ih hfg).1,
          IsCombinatorialManifold.map_iff_of_injective g g.injective]
        exact isCombinatorialManifold_simplexBoundary hV
      · subst hm
        obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp hs
        obtain ⟨f, g, hfg⟩ := he.exists_common_relabeling hs.finite_faces
        rw [← forall_isCombinatorialSphere_link_map_iff f f.injective,
          (stellarEquivalent_of_lt_step ih hfg).2 m rfl,
          forall_isCombinatorialSphere_link_map_iff g g.injective]
        intro v hv
        have hvV : v ∈ V := (singleton_mem_simplexBoundary.mp hv).1
        simpa using isCombinatorialSphere_link_simplexBoundary hV
          (Finset.singleton_subset_iff.mpr hvV) (by simp)

/-! ### Balls, spheres, and higher-face links -/

section PublicAPI

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

/-- Every combinatorial `n`-ball is a combinatorial `n`-manifold. -/
theorem IsCombinatorialBall.isCombinatorialManifold (h : IsCombinatorialBall K n) :
    IsCombinatorialManifold K n :=
  (manifoldDimStep n K).1 h

/-- Every combinatorial `n`-sphere is a combinatorial `n`-manifold. -/
theorem IsCombinatorialSphere.isCombinatorialManifold (h : IsCombinatorialSphere K n) :
    IsCombinatorialManifold K n :=
  (manifoldDimStep n K).2.1 h

/-- Every vertex link in a positive-dimensional combinatorial sphere is a combinatorial sphere one
dimension down. -/
theorem IsCombinatorialSphere.isCombinatorialSphere_link_singleton
    (h : IsCombinatorialSphere K (n + 1)) (hv : ({v} : Finset ι) ∈ K) :
    IsCombinatorialSphere (link K {v}) n :=
  (manifoldDimStep (n + 1) K).2.2 n rfl h hv

/-- In a combinatorial `n`-manifold, the link of every face `σ` with `σ.card ≤ n` is a
combinatorial `(n - σ.card)`-sphere or `(n - σ.card)`-ball. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) ∨
      IsCombinatorialBall (link K σ) (n - σ.card) := by
  have hpos : 1 ≤ σ.card := Finset.card_pos.mpr (K.isRelLowerSet_faces hσ).1
  have h := (link_face_of_lt_step (fun d _ => manifoldDimStep d)
    (σ.card - 1) le_rfl hσ (by omega) (by omega)).1 hK
  rwa [Nat.sub_add_cancel hpos] at h

/-- If every vertex link of `K` is a combinatorial `n`-sphere, then the link of every face `σ ∈ K`
with `σ.card ≤ n + 1` is a combinatorial `(n + 1 - σ.card)`-sphere. -/
theorem isCombinatorialSphere_link_of_forall_singleton
    (hall : ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → IsCombinatorialSphere (link K {w}) n)
    (hσ : σ ∈ K) (hcard : σ.card ≤ n + 1) :
    IsCombinatorialSphere (link K σ) (n + 1 - σ.card) := by
  have hpos : 1 ≤ σ.card := Finset.card_pos.mpr (K.isRelLowerSet_faces hσ).1
  have h := (link_face_of_lt_step (fun d _ => manifoldDimStep d)
    (σ.card - 1) le_rfl hσ (by omega) (by omega)).2 n rfl hall
  rwa [Nat.sub_add_cancel hpos] at h

/-- In a combinatorial `n`-sphere, the link of every face `σ` with `σ.card ≤ n` is a combinatorial
`(n - σ.card)`-sphere. -/
theorem IsCombinatorialSphere.isCombinatorialSphere_link
    (hK : IsCombinatorialSphere K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    IsCombinatorialSphere (link K σ) (n - σ.card) := by
  have hpos : 1 ≤ σ.card := Finset.card_pos.mpr (K.isRelLowerSet_faces hσ).1
  cases n with
  | zero => omega
  | succ m =>
      exact isCombinatorialSphere_link_of_forall_singleton
        (fun _ hw => hK.isCombinatorialSphere_link_singleton hw) hσ hcard

/-- The link of any finset `σ` in a combinatorial `n`-manifold is a combinatorial
`(n - σ.card)`-manifold.

No membership or cardinality hypothesis on `σ` is required: `σ = ∅` gives `K` itself, while a
top-dimensional face or a nonempty non-face has void link. -/
theorem IsCombinatorialManifold.isCombinatorialManifold_link
    (hK : IsCombinatorialManifold K n) (σ : Finset ι) :
    IsCombinatorialManifold (link K σ) (n - σ.card) := by
  by_cases hempty : σ = ∅
  · subst hempty
    simpa using hK
  · by_cases hσ : σ ∈ K
    · by_cases hcard : σ.card ≤ n
      · rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hσ hcard with hs | hb
        · exact hs.isCombinatorialManifold
        · exact hb.isCombinatorialManifold
      · have hle := (le_dimension hσ).trans hK.dimension_le
        have hle' : σ.card - 1 ≤ n := by exact_mod_cast hle
        have htop : σ.card = n + 1 := by omega
        rw [(hK.link_eq_bot_iff hσ).mpr htop]
        exact isCombinatorialManifold_bot
    · have hbot : link K σ = ⊥ := by
        refine eq_bot_iff.mpr fun ρ hρ => ?_
        obtain ⟨-, -, hface⟩ := mem_link_nonempty.mp hρ
        exact hσ ((K.isRelLowerSet_faces hface).2 Finset.subset_union_right
          (Finset.nonempty_iff_ne_empty.mpr hempty))
      rw [hbot]
      exact isCombinatorialManifold_bot

/-! ### Stellar subdivision and stellar equivalence of combinatorial manifolds -/

/-- Starring any face of a combinatorial `n`-manifold at a fresh vertex yields another
combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.stellarSubdivision (hK : IsCombinatorialManifold K n)
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (PreAbstractSimplicialComplex.stellarSubdivision K σ v) n :=
  (stellarSubdivision_of_lt_step (fun d _ => manifoldDimStep d) hσ hv).1 hK

/-- Starring a face at a fresh vertex preserves and reflects combinatorial `n`-manifolds. -/
theorem IsCombinatorialManifold.stellarSubdivision_iff
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (PreAbstractSimplicialComplex.stellarSubdivision K σ v) n ↔
      IsCombinatorialManifold K n :=
  ⟨IsCombinatorialManifold.of_stellarSubdivision hσ hv, fun hK => hK.stellarSubdivision hσ hv⟩

/-- Stellar equivalence preserves and reflects combinatorial `n`-manifolds. -/
theorem StellarEquivalent.isCombinatorialManifold_iff (he : StellarEquivalent K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n :=
  (stellarEquivalent_of_lt_step (fun d _ => manifoldDimStep d) he).1

/-- Intrinsic stellar equivalence up to relabeling preserves and reflects combinatorial
`n`-manifolds, including infinite complexes. -/
theorem StellarEquivalentUpToRelabeling.isCombinatorialManifold_iff
    (he : StellarEquivalentUpToRelabeling K L) :
    IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n := by
  apply StellarEquivalentUpToRelabeling.induction_on he
  · intro A B f g hfg
    exact (IsCombinatorialManifold.map_iff_of_injective f f.injective).symm.trans
      (hfg.isCombinatorialManifold_iff.trans
        (IsCombinatorialManifold.map_iff_of_injective g g.injective))
  · intro _
    rfl
  · intro _ _ ih
    exact ih.symm
  · intro _ _ _ ih₁ ih₂
    exact ih₁.trans ih₂

/-- Being a combinatorial `n`-manifold transfers along an intrinsic stellar equivalence. -/
theorem IsCombinatorialManifold.of_stellarEquivalentUpToRelabeling
    (he : StellarEquivalentUpToRelabeling K L) (hL : IsCombinatorialManifold L n) :
    IsCombinatorialManifold K n :=
  he.isCombinatorialManifold_iff.mpr hL

end PublicAPI

end PreAbstractSimplicialComplex
