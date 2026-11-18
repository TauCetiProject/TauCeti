/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Boundary.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Link

/-!
# Stellar invariance of the combinatorial boundary

Starring any set `σ` at a fresh vertex `v` commutes with `manifoldBoundary`:
`manifoldBoundary (stellarSubdivision K σ v) d = stellarSubdivision (manifoldBoundary K d) σ v`.
Consequently `manifoldBoundary` preserves stellar equivalence and intrinsic stellar equivalence up
to relabeling, with no dimension or finiteness hypothesis on the ambient complexes.

Evaluating on the standard simplex and simplex boundary models immediately yields the boundary
classifications for combinatorial balls and spheres: the combinatorial boundary of a combinatorial
`(n + 1)`-ball is a combinatorial `n`-sphere, and the combinatorial boundary of a combinatorial
`n`-sphere is void.

## Main results

* `PreAbstractSimplicialComplex.manifoldBoundary_stellarSubdivision`: `manifoldBoundary` commutes
  with `stellarSubdivision` at a fresh vertex.
* `PreAbstractSimplicialComplex.StellarEquivalent.manifoldBoundary` and
  `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.manifoldBoundary`: stellar
  equivalences induce stellar equivalences on combinatorial boundaries.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialSphere_manifoldBoundary`: the
  combinatorial boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.manifoldBoundary_eq_bot`: the combinatorial
  boundary of a combinatorial `n`-sphere is void.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.mem_manifoldBoundary_of_link` and
  `IsCombinatorialBall.singleton_mem_manifoldBoundary`: faces (and in particular vertices) with
  ball links lie in `manifoldBoundary`, without assuming the ambient complex is a manifold.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {α β σ τ ω : Finset ι} {v : ι} {d m n : ℕ}

/-! ### Boundary ridges under stellar subdivision -/

private theorem isCombinatorialBall_zero_link_stellarSubdivision_iff_of_notMem
    (hv : ({v} : Finset ι) ∉ K) (hvτ : v ∉ τ) (hnot : ¬ σ ⊆ τ) :
    IsCombinatorialBall (link (stellarSubdivision K σ v) τ) 0 ↔
      IsCombinatorialBall (link K τ) 0 := by
  have he := stellarEquivalent_link_stellarSubdivision_of_notMem
    (fun h => hv (link_le h)) hvτ (sdiff_nonempty.mpr hnot)
  exact ⟨.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling,
    .of_stellarEquivalentUpToRelabeling he.symm.stellarEquivalentUpToRelabeling⟩

private theorem singleton_mem_link_stellarSubdivision_insert_of_sdiff
    {x y : ι} (hv : ({v} : Finset ι) ∉ K) (hvω : v ∉ ω) (hunionK : ω ∪ σ ∈ K)
    (hx : x ∈ σ \ ω) (hy : y ∈ σ \ ω) (hxy : x ≠ y) :
    ({x} : Finset ι) ∈ link (stellarSubdivision K σ v) (insert v ω) := by
  obtain ⟨hxσ, hxω⟩ := mem_sdiff.mp hx
  obtain ⟨hyσ, hyω⟩ := mem_sdiff.mp hy
  have hvx : v ≠ x := fun h =>
    notMem_of_singleton_notMem hv hunionK (h ▸ mem_union_right _ hxσ)
  have hvxω : v ∉ insert x ω := by simp [hvx, hvω]
  refine mem_link_nonempty.mpr ⟨singleton_nonempty x,
    disjoint_singleton_left.mpr (by simp [hvx.symm, hxω]), ?_⟩
  rw [singleton_union, insert_comm]
  refine (insert_mem_stellarSubdivision_iff hvxω).mpr ⟨fun hsub => ?_, ?_⟩
  · rcases mem_insert.mp (hsub hyσ) with rfl | hyω'
    · exact hxy rfl
    · exact hyω hyω'
  · rwa [insert_union, insert_eq_self.mpr (mem_union_right _ hxσ)]

private theorem insert_mem_and_isCombinatorialBall_zero_link_stellarSubdivision_iff
    (hv : ({v} : Finset ι) ∉ K) (hvω : v ∉ ω) :
    (insert v ω ∈ stellarSubdivision K σ v ∧
        IsCombinatorialBall (link (stellarSubdivision K σ v) (insert v ω)) 0) ↔
      ∃ u ∈ σ, u ∉ ω ∧ σ ⊆ insert u ω ∧ insert u ω ∈ K ∧
        IsCombinatorialBall (link K (insert u ω)) 0 := by
  constructor
  · rintro ⟨hmem, hball⟩
    obtain ⟨hnot, hunionK⟩ := (insert_mem_stellarSubdivision_iff hvω).mp hmem
    have hpos : 0 < (σ \ ω).card := card_pos.mpr (sdiff_nonempty.mpr hnot)
    have hle1 : (σ \ ω).card ≤ 1 := by
      by_contra! hlt
      obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := one_lt_card.mp hlt
      have hm₁ := singleton_mem_link_stellarSubdivision_insert_of_sdiff hv hvω hunionK hu₁ hu₂ hne
      have hm₂ :=
        singleton_mem_link_stellarSubdivision_insert_of_sdiff hv hvω hunionK hu₂ hu₁ hne.symm
      obtain ⟨z, hlink⟩ := isCombinatorialBall_zero_iff.mp hball
      rw [hlink, mem_simplex, singleton_subset_iff, mem_singleton] at hm₁ hm₂
      exact hne (hm₁.2.trans hm₂.2.symm)
    obtain ⟨u, hu⟩ := card_eq_one.mp (show (σ \ ω).card = 1 by omega)
    obtain ⟨huσ, huω⟩ := mem_sdiff.mp (hu ▸ mem_singleton_self u)
    have hσu : σ ⊆ insert u ω := by
      rw [← union_singleton, ← hu, union_sdiff_self_eq_union]
      exact subset_union_right
    have huK : insert u ω ∈ K := by
      rwa [← union_singleton, ← hu, union_sdiff_self_eq_union]
    rw [link_stellarSubdivision_insert_eq_of_sdiff_eq_singleton hv hvω hu] at hball
    exact ⟨u, huσ, huω, hσu, huK, hball⟩
  · rintro ⟨u, huσ, huω, hσu, huK, hball⟩
    have hu : σ \ ω = {u} := by
      ext x
      simp only [mem_sdiff, mem_singleton]
      refine ⟨fun ⟨hxσ, hxω⟩ => ?_, fun h => h ▸ ⟨huσ, huω⟩⟩
      rcases mem_insert.mp (hσu hxσ) with rfl | hxω'
      · rfl
      · exact absurd hxω' hxω
    have hunion : ω ∪ σ = insert u ω := by
      rw [← union_sdiff_self_eq_union, hu, union_singleton]
    refine ⟨(insert_mem_stellarSubdivision_iff hvω).mpr ⟨fun h => huω (h huσ), hunion ▸ huK⟩, ?_⟩
    rwa [link_stellarSubdivision_insert_eq_of_sdiff_eq_singleton hv hvω hu]

private theorem insert_mem_manifoldBoundary_stellarSubdivision_iff
    (hv : ({v} : Finset ι) ∉ K) (hσne : σ.Nonempty) (hvβ : v ∉ β) :
    insert v β ∈ manifoldBoundary (stellarSubdivision K σ v) (m + 1) ↔
      insert v β ∈ stellarSubdivision (manifoldBoundary K (m + 1)) σ v := by
  rw [mem_manifoldBoundary_succ_iff, insert_mem_stellarSubdivision_iff hvβ,
    mem_manifoldBoundary_succ_iff]
  constructor
  · rintro ⟨-, τ', hτ'B, hτ'card, hball, hsub⟩
    have hvτ' : v ∈ τ' := hsub (mem_insert_self v β)
    set ω := τ'.erase v
    have hvω : v ∉ ω := notMem_erase v τ'
    have hτ'eq : insert v ω = τ' := insert_erase hvτ'
    have hωcard : ω.card = m := by
      rw [card_erase_of_mem hvτ', hτ'card]
      omega
    have hβω : β ⊆ ω := subset_erase.mpr ⟨(subset_insert v β).trans hsub, hvβ⟩
    rw [← hτ'eq] at hτ'B hball
    obtain ⟨u, huσ, huω, hσu, huK, huball⟩ :=
      (insert_mem_and_isCombinatorialBall_zero_link_stellarSubdivision_iff hv hvω).mp ⟨hτ'B, hball⟩
    refine ⟨fun h => huω (hβω (h huσ)), hσne.mono subset_union_right, insert u ω, huK,
      by rw [card_insert_of_notMem huω, hωcard], huball,
      union_subset (hβω.trans (subset_insert u ω)) hσu⟩
  · rintro ⟨hnot, -, τ, hτK, hτcard, hball, hsub⟩
    obtain ⟨u, huσ, huβ⟩ := not_subset.mp hnot
    have hστ : σ ⊆ τ := subset_union_right.trans hsub
    have huτ : u ∈ τ := hστ huσ
    set ω := τ.erase u
    have hvτ : v ∉ τ := notMem_of_singleton_notMem hv hτK
    have hvω : v ∉ ω := fun h => hvτ (mem_of_mem_erase h)
    have huω : u ∉ ω := notMem_erase u τ
    have hτeq : insert u ω = τ := insert_erase huτ
    have hωcard : ω.card = m := by
      rw [card_erase_of_mem huτ, hτcard]
      omega
    obtain ⟨hmemB, hballB⟩ :=
      (insert_mem_and_isCombinatorialBall_zero_link_stellarSubdivision_iff hv hvω).mpr
        ⟨u, huσ, huω, hτeq.symm ▸ hστ, hτeq.symm ▸ hτK, hτeq.symm ▸ hball⟩
    exact ⟨insert_nonempty v β, insert v ω, hmemB, by rw [card_insert_of_notMem hvω, hωcard],
      hballB, insert_subset_insert v (subset_erase.mpr ⟨subset_union_left.trans hsub, huβ⟩)⟩

private theorem mem_manifoldBoundary_stellarSubdivision_iff_of_notMem
    (hv : ({v} : Finset ι) ∉ K) (hσne : σ.Nonempty) (hvα : v ∉ α) :
    α ∈ manifoldBoundary (stellarSubdivision K σ v) (m + 1) ↔
      α ∈ stellarSubdivision (manifoldBoundary K (m + 1)) σ v := by
  constructor
  · intro hα
    obtain ⟨hne, τ', hτ'B, hτ'card, hball, hsub⟩ := mem_manifoldBoundary_succ_iff.mp hα
    by_cases hvτ' : v ∈ τ'
    · have hins : insert v α ∈ stellarSubdivision (manifoldBoundary K (m + 1)) σ v :=
        (insert_mem_manifoldBoundary_stellarSubdivision_iff hv hσne hvα).mp
          (mem_manifoldBoundary_succ_iff.mpr
            ⟨insert_nonempty v α, τ', hτ'B, hτ'card, hball, insert_subset hvτ' hsub⟩)
      exact ((stellarSubdivision (manifoldBoundary K (m + 1)) σ v).isRelLowerSet_faces hins).2
        (subset_insert v α) hne
    · obtain ⟨hτ'K, hnot⟩ := (mem_stellarSubdivision_iff_of_notMem hvτ').mp hτ'B
      have hballK :=
        (isCombinatorialBall_zero_link_stellarSubdivision_iff_of_notMem hv hvτ' hnot).mp hball
      exact (mem_stellarSubdivision_iff_of_notMem hvα).mpr
        ⟨mem_manifoldBoundary_succ_iff.mpr ⟨hne, τ', hτ'K, hτ'card, hballK, hsub⟩,
          fun h => hnot (h.trans hsub)⟩
  · intro hα
    obtain ⟨hαB, hnotα⟩ := (mem_stellarSubdivision_iff_of_notMem hvα).mp hα
    obtain ⟨hne, τ, hτK, hτcard, hball, hsub⟩ := mem_manifoldBoundary_succ_iff.mp hαB
    by_cases hστ : σ ⊆ τ
    · have hins : insert v α ∈ manifoldBoundary (stellarSubdivision K σ v) (m + 1) :=
        (insert_mem_manifoldBoundary_stellarSubdivision_iff hv hσne hvα).mpr
          ((insert_mem_stellarSubdivision_iff hvα).mpr
            ⟨hnotα, mem_manifoldBoundary_succ_iff.mpr
              ⟨hne.mono subset_union_left, τ, hτK, hτcard, hball, union_subset hsub hστ⟩⟩)
      exact ((manifoldBoundary (stellarSubdivision K σ v) (m + 1)).isRelLowerSet_faces hins).2
        (subset_insert v α) hne
    · have hvτ : v ∉ τ := notMem_of_singleton_notMem hv hτK
      exact mem_manifoldBoundary_succ_iff.mpr
        ⟨hne, τ, (mem_stellarSubdivision_iff_of_notMem hvτ).mpr ⟨hτK, hστ⟩, hτcard,
          (isCombinatorialBall_zero_link_stellarSubdivision_iff_of_notMem hv hvτ hστ).mpr hball,
          hsub⟩

/-! ### Stellar subdivision and stellar equivalence -/

/-- Starring at a fresh vertex commutes with taking the combinatorial boundary. -/
@[simp]
theorem manifoldBoundary_stellarSubdivision (hv : ({v} : Finset ι) ∉ K) :
    manifoldBoundary (stellarSubdivision K σ v) d =
      stellarSubdivision (manifoldBoundary K d) σ v := by
  cases d with
  | zero => rw [manifoldBoundary_zero, manifoldBoundary_zero, stellarSubdivision_bot]
  | succ m =>
    rcases σ.eq_empty_or_nonempty with rfl | hσne
    · rw [stellarSubdivision_empty, manifoldBoundary_bot, stellarSubdivision_empty]
    · refine SetLike.ext fun α => ?_
      by_cases hvα : v ∈ α
      · rw [← insert_erase hvα]
        exact insert_mem_manifoldBoundary_stellarSubdivision_iff hv hσne (notMem_erase v α)
      · exact mem_manifoldBoundary_stellarSubdivision_iff_of_notMem hv hσne hvα

/-- Same-type stellar equivalence induces same-type stellar equivalence of combinatorial
boundaries. -/
theorem StellarEquivalent.manifoldBoundary (h : StellarEquivalent K L) :
    StellarEquivalent (PreAbstractSimplicialComplex.manifoldBoundary K d)
      (PreAbstractSimplicialComplex.manifoldBoundary L d) := by
  apply h.induction_on
  · intro A B hmove
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hmove
    rw [manifoldBoundary_stellarSubdivision hv]
    have hvB : ({v} : Finset ι) ∉ PreAbstractSimplicialComplex.manifoldBoundary A d :=
      fun h => hv (manifoldBoundary_le h)
    by_cases hσB : σ ∈ PreAbstractSimplicialComplex.manifoldBoundary A d
    · exact stellarEquivalent_stellarSubdivision hσB hvB
    · rw [stellarSubdivision_eq_self_of_notMem hvB (A.isRelLowerSet_faces hσ).1 hσB]
  · exact fun _ => .refl _
  · exact fun _ _ ih => ih.symm
  · exact fun _ _ _ ih₁ ih₂ => ih₁.trans ih₂

/-- Intrinsic stellar equivalence up to relabeling induces intrinsic stellar equivalence of
combinatorial boundaries. -/
theorem StellarEquivalentUpToRelabeling.manifoldBoundary
    (h : StellarEquivalentUpToRelabeling K L) :
    StellarEquivalentUpToRelabeling (PreAbstractSimplicialComplex.manifoldBoundary K d)
      (PreAbstractSimplicialComplex.manifoldBoundary L d) := by
  apply h.induction_on
  · intro A B f g he
    apply of_common_relabeling f g
    simpa only [map_manifoldBoundary _ f.injective, map_manifoldBoundary _ g.injective] using
      he.manifoldBoundary (d := d)
  · exact fun _ => .refl _
  · exact fun _ _ ih => ih.symm
  · exact fun _ _ _ ih₁ ih₂ => ih₁.trans ih₂

/-! ### Combinatorial balls and spheres -/

/-- The combinatorial boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere. -/
theorem IsCombinatorialBall.isCombinatorialSphere_manifoldBoundary
    (h : IsCombinatorialBall K (n + 1)) :
    IsCombinatorialSphere (manifoldBoundary K (n + 1)) n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  have heB := he.manifoldBoundary (d := n + 1)
  rw [manifoldBoundary_simplex hV] at heB
  exact isCombinatorialSphere_iff.mpr ⟨V, hV, heB⟩

/-- The combinatorial boundary of a positive-dimensional combinatorial ball is nonvoid. -/
theorem IsCombinatorialBall.manifoldBoundary_ne_bot (h : IsCombinatorialBall K (n + 1)) :
    manifoldBoundary K (n + 1) ≠ ⊥ :=
  h.isCombinatorialSphere_manifoldBoundary.ne_bot

/-- The combinatorial boundary of a combinatorial `n`-sphere is void. -/
theorem IsCombinatorialSphere.manifoldBoundary_eq_bot (h : IsCombinatorialSphere K n) :
    manifoldBoundary K n = ⊥ := by
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  have heB := he.manifoldBoundary (d := n)
  rw [manifoldBoundary_simplexBoundary hV] at heB
  by_contra hne
  exact (heB.ne_bot_iff.mp hne) rfl

/-- Any nonempty finset `σ` of cardinality at most `d` whose link in `K` is a combinatorial
`(d - σ.card)`-ball belongs to `manifoldBoundary K d`, with no manifold hypothesis on `K`. -/
theorem IsCombinatorialBall.mem_manifoldBoundary_of_link (hσ : σ.Nonempty) (hcard : σ.card ≤ d)
    (hb : IsCombinatorialBall (link K σ) (d - σ.card)) :
    σ ∈ manifoldBoundary K d := by
  have hpos : 1 ≤ σ.card := card_pos.mpr hσ
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rcases eq_or_lt_of_le hcard with heq | hlt
  · rw [heq, Nat.sub_self] at hb
    refine (mem_manifoldBoundary_of_card_eq heq).mpr ⟨?_, hb⟩
    by_contra hnot
    exact hb.ne_bot (link_eq_bot_of_notMem hσ hnot)
  · obtain ⟨k, hk⟩ : ∃ k, m + 1 - σ.card = k + 1 := ⟨m - σ.card, by omega⟩
    rw [hk] at hb
    by_contra hnot
    have hbot := link_eq_bot_of_notMem hσ hnot
    rw [link_manifoldBoundary, hk] at hbot
    exact hb.manifoldBoundary_ne_bot hbot

/-- Any vertex whose link in `K` is a combinatorial `n`-ball belongs to
`manifoldBoundary K (n + 1)`, with no manifold hypothesis on `K`. -/
theorem IsCombinatorialBall.singleton_mem_manifoldBoundary
    (hb : IsCombinatorialBall (link K {v}) n) :
    ({v} : Finset ι) ∈ manifoldBoundary K (n + 1) := by
  apply IsCombinatorialBall.mem_manifoldBoundary_of_link (singleton_nonempty v) (by simp)
  simpa using hb

end PreAbstractSimplicialComplex
