/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Neighborhood
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Union
public import TauCeti.Topology.OpenPartialHomeomorph.ClosedBall

/-!
# Local homology of a compact subset of a manifold

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `A ⊆ M` be compact. This file proves that
the local homology `Hₖ(M, M ∖ A)` (`TauCeti.localHomology`) with coefficients in a module
vanishes above the dimension (`TauCeti.isZero_localHomology_of_isCompact`), and that in degree
`n` a class is determined by its restrictions `Hₙ(M, M ∖ A) ⟶ Hₙ(M, M ∖ {x})` to the points of
`A` (`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero` and
`TauCeti.localHomology_ext_of_isCompact`). This is the uniqueness half of the statement that a
compatible family of local classes `αₓ ∈ Hₙ(M, M ∖ {x})`, `x ∈ A`, comes from a unique class of
`Hₙ(M, M ∖ A)`, which for `A = M` compact produces fundamental classes; existence is not proved
here. For compact `M` itself, `A = M` shows that the singular homology `Hₖ(M)` vanishes for
`k > n` (`TauCeti.isZero_singularHomology_of_compactSpace`).

## Main results

* `TauCeti.isZero_localHomology_of_isCompact`: `Hₖ(M, M ∖ A) = 0` for compact `A` and `k > n`.
* `TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`: a class of `Hₙ(M, M ∖ A)` whose
  restriction to every point of `A` vanishes is zero.
* `TauCeti.localHomology_ext_of_isCompact`: two classes of `Hₙ(M, M ∖ A)` with the same
  restrictions to the points of `A` are equal.
* `TauCeti.isZero_singularHomology_of_compactSpace`: `Hₖ(M) = 0` for compact `M` and `k > n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27 and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology

universe w v u

namespace TauCeti

section Module

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) (n : ℕ) {M : Type w} [TopologicalSpace M]

/-
The main results are proved by induction on the shape of `A`, carried by the relative
Mayer–Vietoris sequence `Hₖ₊₁(M, M ∖ (A ∩ B)) ⟶ Hₖ(M, M ∖ (A ∪ B)) ⟶ Hₖ(M, M ∖ A) ⊞ Hₖ(M, M ∖ B)`
of two closed sets.

* **Unions.** If the first term vanishes, the second map is a monomorphism
  (`TauCeti.isZero_localHomology_union`, `TauCeti.localHomology_hom_ext_of_union`), so both
  statements pass from `A` and `B` to `A ∪ B` once `Hₖ(M, M ∖ (A ∩ B))` vanishes above the
  dimension.
* **Finite unions of convex sets in a chart.** These are the finite-union case of the lemma
  (`TauCeti.isZero_localHomology_symm_image_iUnion`,
  `TauCeti.localHomology_symm_image_iUnion_hom_ext`).
* **Compact sets in a chart.** A class of `Hₖ(M, M ∖ A)` is the restriction of a class of
  `Hₖ(M, M ∖ U)` for a neighbourhood `U` of `A`
  (`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq`), and between `A` and `U` lies a
  finite union of closed balls of the chart centred at points of `A`. On each ball, restriction
  to its centre is an isomorphism.
* **Compact sets.** A compact set is a finite union of compact sets each lying in the source of
  a chart, and the intersection of two such pieces lies in a chart again.
-/

/-- The conclusion of Hatcher's Lemma 3.27 for a set `S`, apart from existence: local homology
along `S` vanishes above degree `n`, and a class in degree `n` is zero once its restriction to
every point of `S` is. -/
private structure Detects (S : Set M) : Prop where
  isZero : ∀ k, n < k → IsZero (localHomology N S k)
  eq_zero : ∀ α : (localHomology N S n : ModuleCat.{w} Λ),
    (∀ x (hx : x ∈ S), localHomologyRestriction N (singleton_subset_iff.2 hx) n α = 0) → α = 0

private lemma detects_empty : Detects N n (∅ : Set M) :=
  ⟨fun k _ ↦ isZero_localHomology_empty N k, fun _ _ ↦
    (ModuleCat.subsingleton_of_isZero (isZero_localHomology_empty N n)).elim _ _⟩

/-- In module coefficients, a class restricting to zero on `S` and on `T` vanishes, under the
hypotheses of `TauCeti.localHomology_hom_ext_of_union`. -/
private lemma eq_zero_of_union {S T : Set M} (hS : IsClosed S) (hT : IsClosed T) {k : ℕ}
    (h : IsZero (localHomology N (S ∩ T) (k + 1)))
    (α : (localHomology N (S ∪ T) k : ModuleCat.{w} Λ))
    (hαS : localHomologyRestriction N subset_union_left k α = 0)
    (hαT : localHomologyRestriction N subset_union_right k α = 0) : α = 0 := by
  have := localHomology_hom_ext_of_union hS hT h
    (f := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ
      (localHomology N (S ∪ T) k : ModuleCat.{w} Λ) α)) (g := 0) ?_ ?_
  · exact (LinearMap.toSpanSingleton_eq_zero_iff Λ _).1 congr(ModuleCat.Hom.hom $this)
  all_goals
    ext1
    rw [zero_comp]
    refine (LinearMap.comp_toSpanSingleton _ _).trans
      ((LinearMap.toSpanSingleton_eq_zero_iff Λ _).2 ?_)
  exacts [hαS, hαT]

/-- **The union step.** The conclusion passes from closed sets `S` and `T` to `S ∪ T`, provided
local homology along `S ∩ T` vanishes above degree `n`. -/
private lemma Detects.union {S T : Set M} (hS' : Detects N n S) (hT' : Detects N n T)
    (hS : IsClosed S) (hT : IsClosed T) (hST : ∀ k, n < k → IsZero (localHomology N (S ∩ T) k)) :
    Detects N n (S ∪ T) := by
  refine ⟨fun k hk ↦ isZero_localHomology_union hS hT (hS'.isZero k hk) (hT'.isZero k hk)
    (hST _ (by lia)), fun α hα ↦ eq_zero_of_union N hS hT (hST _ (by lia)) α ?_ ?_⟩
  · refine hS'.eq_zero _ fun x hx ↦ ?_
    rw [localHomologyRestriction_comp_apply]
    exact hα x (Or.inl hx)
  · refine hT'.eq_zero _ fun x hx ↦ ?_
    rw [localHomologyRestriction_comp_apply]
    exact hα x (Or.inr hx)

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [T2Space M] {n}

/-- **The compactness step.** The conclusion holds for a compact subset of the source of a chart.
A class along `A` is restricted from a finite union `K` of closed balls of the chart centred at
points of `A`, and restriction from each ball to its centre is an isomorphism. -/
private lemma detects_of_subset_source (hn : finrank ℝ E = n) (φ : OpenPartialHomeomorph M E)
    {A : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source) : Detects N n A := by
  have key (k : ℕ) (α : (localHomology N A k : ModuleCat.{w} Λ)) :
      ∃ (t : Finset M) (r : M → ℝ), (∀ a ∈ t, a ∈ A ∧ 0 < r a ∧
        closedBall (φ a) (r a) ⊆ φ.target) ∧
        ∃ (hAK : A ⊆ φ.symm '' ⋃ a ∈ t, closedBall (φ a) (r a))
          (β : (localHomology N (φ.symm '' ⋃ a ∈ t, closedBall (φ a) (r a)) k :
            ModuleCat.{w} Λ)), localHomologyRestriction N hAK k β = α := by
    obtain ⟨U, hU, β, rfl⟩ := exists_mem_nhdsSet_localHomologyRestriction_eq N k α
    obtain ⟨t, r, ht, hAt⟩ := φ.exists_finset_closedBall_cover hA hAφ hU
    have hKU : φ.symm '' ⋃ a ∈ t, closedBall (φ a) (r a) ⊆ U := by
      rw [image_iUnion₂]
      exact iUnion₂_subset fun a ha ↦ (ht a ha).2.2.2
    exact ⟨t, r, fun a ha ↦ ⟨(ht a ha).1, (ht a ha).2.1, (ht a ha).2.2.1⟩, hAt,
      localHomologyRestriction N hKU k β, localHomologyRestriction_comp_apply N _ _ k β⟩
  have hK (t : Finset M) (r : M → ℝ) (ht : ∀ a ∈ t, closedBall (φ a) (r a) ⊆ φ.target) :
      Detects N n (φ.symm '' ⋃ a ∈ t, closedBall (φ a) (r a)) := by
    rw [← iUnion_subtype (· ∈ t) fun a ↦ closedBall (φ a) (r a)]
    have hconv (a : t) := convex_closedBall (φ a) (r a)
    have hcpt (a : t) := isCompact_closedBall (φ a) (r a)
    have hφ (a : t) := ht a a.2
    refine ⟨fun k hk ↦ isZero_localHomology_symm_image_iUnion N φ hn hconv hcpt hφ hk,
      fun α hα ↦ ?_⟩
    have := localHomology_symm_image_iUnion_hom_ext N φ hn hconv hcpt hφ
      (g₁ := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ
        (localHomology N (φ.symm '' ⋃ a : t, closedBall (φ a) (r a)) n : ModuleCat.{w} Λ) α))
      (g₂ := 0) fun x hx ↦ ?_
    · exact (LinearMap.toSpanSingleton_eq_zero_iff Λ _).1 congr(ModuleCat.Hom.hom $this)
    ext1
    rw [zero_comp]
    exact (LinearMap.comp_toSpanSingleton _ _).trans
      ((LinearMap.toSpanSingleton_eq_zero_iff Λ _).2 (hα x hx))
  refine ⟨fun k hk ↦ ?_, fun α hα ↦ ?_⟩
  · have h (α : (localHomology N A k : ModuleCat.{w} Λ)) : α = 0 := by
      obtain ⟨t, r, ht, hAK, β, rfl⟩ := key k α
      rw [(ModuleCat.subsingleton_of_isZero ((hK t r fun a ha ↦ (ht a ha).2.2).isZero k
        hk)).elim β 0, map_zero]
    rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun α β ↦ (h α).trans (h β).symm⟩
  · obtain ⟨t, r, ht, hAK, β, rfl⟩ := key n α
    refine (congrArg _ ((hK t r fun a ha ↦ (ht a ha).2.2).eq_zero β fun y hy ↦ ?_)).trans
      (map_zero _)
    -- `y` lies in the ball about some `a ∈ A`, along which restriction to `a` is injective.
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hz
    obtain ⟨haA, hr, hrφ⟩ := ht a ha
    have hBK : φ.symm '' closedBall (φ a) (r a) ⊆ φ.symm '' ⋃ a ∈ t, closedBall (φ a) (r a) :=
      image_mono (subset_iUnion₂ (s := fun a (_ : a ∈ t) ↦ closedBall (φ a) (r a)) a ha)
    have hstar : StarConvex ℝ (φ a) (closedBall (φ a) (r a)) :=
      (convex_closedBall _ _).starConvex (mem_closedBall_self hr.le)
    have hiso := isIso_localHomologyRestriction_symm_image N φ hstar (isCompact_closedBall _ _)
      hrφ (hAφ haA) (mem_closedBall_self hr.le) n
    have hzero : localHomologyRestriction N hBK n β = 0 := by
      refine (ModuleCat.mono_iff_injective _).1 (@IsIso.mono_of_iso _ _ _ _ _ hiso) ?_
      rw [map_zero, localHomologyRestriction_comp_apply,
        ← localHomologyRestriction_comp_apply N (singleton_subset_iff.2 haA) hAK]
      exact hα a haA
    rw [← localHomologyRestriction_comp_apply N (singleton_subset_iff.2 (mem_image_of_mem _ hza))
      hBK, hzero, map_zero]

/-- The conclusion holds for a finite union of compact sets, each lying in the source of the
chart at some point. -/
private lemma detects_biUnion [ChartedSpace E M] (hn : finrank ℝ E = n) (t : Finset M)
    (D : M → Set M) (hD : ∀ a ∈ t, IsCompact (D a)) (hDφ : ∀ a ∈ t, D a ⊆ (chartAt E a).source) :
    Detects N n (⋃ a ∈ t, D a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using detects_empty N n
  | insert b t hb ih =>
    have hDt : IsCompact (⋃ a ∈ t, D a) :=
      t.finite_toSet.isCompact_biUnion fun a ha ↦ hD a (Finset.mem_insert_of_mem ha)
    have hb' := t.mem_insert_self b
    rw [Finset.set_biUnion_insert]
    exact (detects_of_subset_source N hn _ (hD b hb') (hDφ b hb')).union N n
      (ih (fun a ha ↦ hD a (Finset.mem_insert_of_mem ha))
        fun a ha ↦ hDφ a (Finset.mem_insert_of_mem ha))
      (hD b hb').isClosed hDt.isClosed
      (detects_of_subset_source N hn _ ((hD b hb').inter_right hDt.isClosed)
        (inter_subset_left.trans (hDφ b hb'))).isZero

/-- The conclusion holds for every compact set: it is a finite union of compact sets each lying
in the source of a chart. -/
private lemma detects_of_isCompact [ChartedSpace E M] (hn : finrank ℝ E = n) {A : Set M}
    (hA : IsCompact A) : Detects N n A := by
  have := ChartedSpace.locallyCompactSpace E M
  choose K hK hxK hKφ using fun a : M ↦
    exists_compact_subset (chartAt E a).open_source (mem_chart_source E a)
  obtain ⟨t, -, hAt⟩ := hA.elim_nhds_subcover (fun a ↦ interior (K a))
    fun a _ ↦ isOpen_interior.mem_nhds (hxK a)
  have hAeq : A = ⋃ a ∈ t, A ∩ K a := by
    refine subset_antisymm (fun x hx ↦ ?_) (iUnion₂_subset fun _ _ ↦ inter_subset_left)
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hAt hx)
    exact mem_iUnion₂.2 ⟨a, ha, hx, interior_subset hxa⟩
  rw [hAeq]
  exact detects_biUnion N hn t _ (fun a _ ↦ hA.inter_right (hK a).isClosed)
    fun a _ ↦ inter_subset_right.trans (hKφ a)

variable [ChartedSpace E M] {A : Set M}

/-- **Local homology of a compact set vanishes above the dimension.** For a compact subset `A` of
a Hausdorff space modelled on a real normed space of dimension `n`, `Hₖ(M, M ∖ A) = 0` for
`k > n`. This is Hatcher's Lemma 3.27(b). -/
theorem isZero_localHomology_of_isCompact (hn : finrank ℝ E = n) (hA : IsCompact A) {k : ℕ}
    (hk : n < k) : IsZero (localHomology N A k) :=
  (detects_of_isCompact N hn hA).isZero k hk

/-- **A local homology class of a compact set is detected at its points.** For a compact subset
`A` of a Hausdorff space modelled on a real normed space of dimension `n`, a class of
`Hₙ(M, M ∖ A)` whose restriction to `Hₙ(M, M ∖ {x})` vanishes for every `x ∈ A` is zero. -/
theorem eq_zero_of_forall_localHomologyRestriction_eq_zero (hn : finrank ℝ E = n)
    (hA : IsCompact A) (α : (localHomology N A n : ModuleCat.{w} Λ))
    (hα : ∀ x (hx : x ∈ A), localHomologyRestriction N (singleton_subset_iff.2 hx) n α = 0) :
    α = 0 :=
  (detects_of_isCompact N hn hA).eq_zero α hα

/-- **Uniqueness of local homology classes of a compact set.** For a compact subset `A` of a
Hausdorff space modelled on a real normed space of dimension `n`, two classes of
`Hₙ(M, M ∖ A)` with the same restrictions to `Hₙ(M, M ∖ {x})` for every `x ∈ A` are equal. This
is the uniqueness part of Hatcher's Lemma 3.27(a). -/
theorem localHomology_ext_of_isCompact (hn : finrank ℝ E = n) (hA : IsCompact A)
    {α β : (localHomology N A n : ModuleCat.{w} Λ)}
    (h : ∀ x (hx : x ∈ A), localHomologyRestriction N (singleton_subset_iff.2 hx) n α =
      localHomologyRestriction N (singleton_subset_iff.2 hx) n β) :
    α = β :=
  sub_eq_zero.1 (eq_zero_of_forall_localHomologyRestriction_eq_zero N hn hA _ fun x hx ↦ by
    rw [map_sub, h x hx, sub_self])

/-- **The homology of a compact manifold vanishes above the dimension.** For a compact Hausdorff
space modelled on a real normed space of dimension `n`, `Hₖ(M) = 0` for `k > n`: it is the local
homology `Hₖ(M, M ∖ M)`. -/
theorem isZero_singularHomology_of_compactSpace [CompactSpace M] (hn : finrank ℝ E = n) {k : ℕ}
    (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  have h := isZero_localHomology_of_isCompact N hn (isCompact_univ (X := M)) hk
  rw [localHomology, compl_univ] at h
  have : IsEmpty (TopPair.ofSubset (∅ : Set (TopCat.of M))).snd :=
    inferInstanceAs (IsEmpty (∅ : Set M))
  have hπ := asIso ((TopPair.ofSubset (∅ : Set (TopCat.of M))).singularHomologyπ N k)
  exact h.of_iso hπ

end Module

end TauCeti
