/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Instances.Shrink

/-!
# Compact subsets of colimits in `TopCat`

A space built as a sequential colimit of `T1` spaces along injective maps, such as the skeletal
filtration of the realization of a simplicial space, carries the final topology of its stages.
This file shows that compact subsets of such a colimit cannot spread over infinitely many stages,
and that the final topology is compactly generated as soon as the stages are.

* In the colimit of any diagram of `T1` spaces, a set whose preimage in every stage is finite is
  closed (`TauCeti.TopCat.isClosed_of_forall_finite_preimage`); since the same holds for all of
  its subsets, it is discrete (`TauCeti.TopCat.isDiscrete_of_forall_finite_preimage`).
* For a sequence of `T1` spaces along injective maps, every compact subset of the colimit lies in
  the image of one stage (`TauCeti.TopCat.exists_subset_range_ι_of_isCompact`). If the maps from
  the stages to the colimit are embeddings, every continuous map from a compact space into the
  colimit therefore factors continuously through one stage
  (`TauCeti.TopCat.exists_lift_of_compactSpace`). This supplies the compact-support hypothesis
  of `TauCeti.isColimitMapCoconeToSSet` and `TauCeti.isColimitMapCoconeSingularHomology`, so
  that singular chains and singular homology of such a colimit are computed stagewise.
* A colimit of compactly generated spaces in `TopCat` is compactly generated
  (`TauCeti.TopCat.uCompactlyGeneratedSpace_of_isColimit`), so such a colimit needs no
  replacement of its topology by the associated compactly generated one.
* The ordinary product of two sequential colimits of `u`-small compact Hausdorff spaces along
  embeddings in `TopCat` is `u`-compactly generated
  (`TauCeti.TopCat.uCompactlyGeneratedSpace_prod_of_isColimit`).

For the compactness statement, a compact set `K` meeting points outside every stage contains a
sequence of points `x k` lying in a stage of strictly increasing index `n (k + 1)` but outside the
stage of index `n k`. Every stage meets the set of these points in finitely many of them, so the
set is closed and discrete in the colimit, and as a closed subset of `K` it is compact, hence
finite, which is impossible.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition A.1, that a compact subset of a CW complex meets only finitely many cells.
* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.4, on compact spaces and sequential colimits of `T1` spaces.
-/

public section

open CategoryTheory Limits Topology Set

universe w w' v u

namespace TauCeti.TopCat

section Colimit

variable {J : Type w} [Category.{w'} J] {F : J ⥤ TopCat.{u}} {c : Cocone F}

/-- In the colimit of a diagram of `T1` spaces in `TopCat`, a set meeting every stage in
finitely many points is closed. -/
theorem isClosed_of_forall_finite_preimage [∀ j, T1Space (F.obj j)] (hc : IsColimit c)
    {S : Set c.pt} (hS : ∀ j, (c.ι.app j ⁻¹' S).Finite) : IsClosed S :=
  (TopCat.isClosed_iff_of_isColimit _ hc S).2 fun j ↦ (hS j).isClosed

/-- In the colimit of a diagram of `T1` spaces in `TopCat`, a set meeting every stage in
finitely many points is discrete. -/
theorem isDiscrete_of_forall_finite_preimage [∀ j, T1Space (F.obj j)] (hc : IsColimit c)
    {S : Set c.pt} (hS : ∀ j, (c.ι.app j ⁻¹' S).Finite) : IsDiscrete S :=
  isDiscrete_iff_forall_mem_exists_isClosed.2 fun t ht ↦
    ⟨t, isClosed_of_forall_finite_preimage hc fun j ↦ (hS j).subset (preimage_mono ht),
      inter_eq_left.2 ht⟩

/-- A colimit of compactly generated spaces in `TopCat` is compactly generated. -/
theorem uCompactlyGeneratedSpace_of_isColimit [∀ j, UCompactlyGeneratedSpace.{v} (F.obj j)]
    (hc : IsColimit c) : UCompactlyGeneratedSpace.{v} c.pt :=
  uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ (TopCat.isClosed_iff_of_isColimit _ hc s).2
    fun j ↦ UCompactlyGeneratedSpace.isClosed fun S f ↦ hs S ((c.ι.app j).hom.comp f)

end Colimit

section Sequential

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- In a sequential colimit of `T1` spaces in `TopCat` along injective maps, every compact subset
lies in the image of a single stage. -/
theorem exists_subset_range_ι_of_isCompact
    (hF : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    [∀ n, T1Space (F.obj n)] (hc : IsColimit c) {K : Set c.pt} (hK : IsCompact K) :
    ∃ n, K ⊆ range (c.ι.app n) := by
  by_contra! h
  -- For each stage `n`, a point `pt n` of `K` outside stage `n`, and a stage `next n` containing
  -- it, as the stages cover the colimit; necessarily `n < next n`.
  choose pt hptK hpt using fun n ↦ not_subset.1 (h n)
  choose next hnext using fun n ↦ iUnion_eq_univ_iff.1 (iUnion_range_ι_of_isColimit hc) (pt n)
  have hlt (n : ℕ) : n < next n := by
    by_contra! hle
    exact hpt n (monotone_range_ι c hle (hnext n))
  -- Iterating `next` gives strictly increasing stages `idx k`, and points `x k` outside stage
  -- `idx k` but inside stage `idx (k + 1)`.
  let idx (k : ℕ) : ℕ := next^[k] 0
  have hidx_succ (k : ℕ) : idx (k + 1) = next (idx k) := Function.iterate_succ_apply' next k 0
  have hidx : StrictMono idx := strictMono_nat_of_lt_succ fun k ↦ hidx_succ k ▸ hlt (idx k)
  let x (k : ℕ) : c.pt := pt (idx k)
  have hx {k n : ℕ} (hk : x k ∈ range (c.ι.app n)) : idx k < n := by
    by_contra! hle
    exact hpt _ (monotone_range_ι c hle hk)
  have hle {j k : ℕ} (hjk : x j = x k) : k ≤ j :=
    Nat.lt_succ_iff.1 <| hidx.lt_iff_lt.1 <| hx <| hjk ▸ hidx_succ j ▸ hnext (idx j)
  have hinj : Function.Injective x := fun j k hjk ↦ le_antisymm (hle hjk.symm) (hle hjk)
  -- Stage `n` meets the points `x k` only for `k < n`, so their set is closed and discrete.
  have hfin (n : ℕ) : (c.ι.app n ⁻¹' range x).Finite := by
    refine (((finite_Iio n).image x).preimage
      (injective_ι_of_isColimit (fun _ _ f ↦ hF (leOfHom f)) hc n).injOn).subset ?_
    rintro y ⟨k, hk⟩
    exact ⟨k, (hidx.id_le k).trans_lt (hx ⟨y, hk.symm⟩), hk⟩
  have hcpt : IsCompact (range x) :=
    hK.of_isClosed_subset (isClosed_of_forall_finite_preimage hc hfin)
      (range_subset_iff.2 fun k ↦ hptK _)
  exact infinite_range_of_injective hinj
    (hcpt.finite (isDiscrete_of_forall_finite_preimage hc hfin))

/-- In a sequential colimit of `T1` spaces in `TopCat` whose maps from the stages are embeddings,
every continuous map from a compact space factors continuously through a single stage. -/
theorem exists_lift_of_compactSpace [∀ n, T1Space (F.obj n)] (hc : IsColimit c)
    (hι : ∀ n, IsEmbedding (c.ι.app n)) {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : C(X, c.pt)) : ∃ n, ∃ g' : C(X, F.obj n), (c.ι.app n).hom.comp g' = g := by
  have hF ⦃i j : ℕ⦄ (hij : i ≤ j) : Function.Injective (F.map (homOfLE hij)) :=
    Function.Injective.of_comp (f := c.ι.app j) <| by
      rw [← TopCat.coe_comp, c.w]
      exact (hι i).injective
  obtain ⟨n, hn⟩ := exists_subset_range_ι_of_isCompact hF hc (isCompact_range g.continuous)
  choose f hf using fun p ↦ hn ⟨p, rfl⟩
  have hfg : c.ι.app n ∘ f = g := funext hf
  exact ⟨n, ⟨f, (hι n).isInducing.continuous_iff.2 (hfg ▸ g.continuous)⟩,
    ContinuousMap.ext hf⟩

/-- The product of two sequential colimits of `u`-small compact Hausdorff spaces along embeddings in
`TopCat` is `u`-compactly generated in the ordinary product topology. -/
theorem uCompactlyGeneratedSpace_prod_of_isColimit
    {F₁ : ℕ ⥤ TopCat.{w}} {F₂ : ℕ ⥤ TopCat.{w}}
    [∀ n, CompactSpace (F₁.obj n)] [∀ n, T2Space (F₁.obj n)]
    [∀ n, CompactSpace (F₂.obj n)] [∀ n, T2Space (F₂.obj n)]
    [∀ n, Small.{u} (F₁.obj n)] [∀ n, Small.{u} (F₂.obj n)]
    {c₁ : Cocone F₁} {c₂ : Cocone F₂} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (hι₁ : ∀ n, IsEmbedding (c₁.ι.app n)) (hι₂ : ∀ n, IsEmbedding (c₂.ι.app n)) :
    UCompactlyGeneratedSpace.{u} (c₁.pt × c₂.pt) := by
  refine uCompactlyGeneratedSpace_of_isOpen fun U hU ↦ isOpen_iff_forall_mem_open.2 ?_
  rintro ⟨x₀, y₀⟩ hxy₀
  let A (n : ℕ) : Set c₁.pt := range (c₁.ι.app n)
  let B (n : ℕ) : Set c₂.pt := range (c₂.ι.app n)
  have (n : ℕ) : CompactSpace (A n) :=
    (hι₁ n).toHomeomorph.compactSpace
  have (n : ℕ) : T2Space (A n) :=
    (hι₁ n).toHomeomorph.t2Space
  have (n : ℕ) : CompactSpace (B n) :=
    (hι₂ n).toHomeomorph.compactSpace
  have (n : ℕ) : T2Space (B n) :=
    (hι₂ n).toHomeomorph.t2Space
  -- On every stage product `A n × B n`, the trace of `U` is open via a `CompHaus.{u}` test map.
  have hU_stage (n : ℕ) :
      IsOpen (Prod.map ((↑) : A n → c₁.pt) ((↑) : B n → c₂.pt) ⁻¹' U) := by
    let pmap := (c₁.ι.app n).hom.prodMap (c₂.ι.app n).hom
    let eShrink := Shrink.homeomorph.{u, w} (F₁.obj n × F₂.obj n)
    have : CompactSpace (Shrink.{u} (F₁.obj n × F₂.obj n)) := eShrink.compactSpace
    have : T2Space (Shrink.{u} (F₁.obj n × F₂.obj n)) := eShrink.t2Space
    let f : C(CompHaus.of (Shrink.{u} (F₁.obj n × F₂.obj n)), c₁.pt × c₂.pt) :=
      pmap.comp ⟨eShrink.symm, eShrink.symm.continuous⟩
    have hfU : IsOpen (f ⁻¹' U) := hU _ f
    have hpre : IsOpen (pmap ⁻¹' U) := by
      convert eShrink.continuous.isOpen_preimage _ hfU using 1
      ext x
      simp [f, Homeomorph.symm_apply_apply]
    let e₁ := (hι₁ n).toHomeomorph
    let e₂ := (hι₂ n).toHomeomorph
    let hrange := e₁.prodCongr e₂
    have heq : hrange.symm ⁻¹' (pmap ⁻¹' U) =
        Prod.map ((↑) : A n → c₁.pt) ((↑) : B n → c₂.pt) ⁻¹' U := by
      ext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have ha' : c₁.ι.app n (e₁.symm ⟨a, ha⟩) = a :=
        congrArg Subtype.val (e₁.apply_symm_apply ⟨a, ha⟩)
      have hb' : c₂.ι.app n (e₂.symm ⟨b, hb⟩) = b :=
        congrArg Subtype.val (e₂.apply_symm_apply ⟨b, hb⟩)
      simp [pmap, hrange, ha', hb']
    rw [← heq]
    exact hrange.symm.continuous.isOpen_preimage _ hpre
  obtain ⟨n₁, hn₁⟩ := mem_iUnion.1 (iUnion_range_ι_of_isColimit hc₁ ▸ mem_univ x₀)
  obtain ⟨n₂, hn₂⟩ := mem_iUnion.1 (iUnion_range_ι_of_isColimit hc₂ ▸ mem_univ y₀)
  let n₀ := max n₁ n₂
  have hx₀ : x₀ ∈ A n₀ := monotone_range_ι c₁ (le_max_left n₁ n₂) hn₁
  have hy₀ : y₀ ∈ B n₀ := monotone_range_ι c₂ (le_max_right n₁ n₂) hn₂
  -- Stagewise invariant at `n = n₀ + k`: open `V ⊆ K ⊆ A n` and `W ⊆ L ⊆ B n`.
  let Inv (k : ℕ) (d : Set c₁.pt × Set c₁.pt × Set c₂.pt × Set c₂.pt) : Prop :=
    let V := d.1; let K := d.2.1; let W := d.2.2.1; let L := d.2.2.2
    x₀ ∈ V ∧ y₀ ∈ W ∧ V ⊆ K ∧ K ⊆ A (n₀ + k) ∧ W ⊆ L ∧
      L ⊆ B (n₀ + k) ∧
      IsOpen (((↑) : A (n₀ + k) → c₁.pt) ⁻¹' V) ∧ IsCompact K ∧
      IsOpen (((↑) : B (n₀ + k) → c₂.pt) ⁻¹' W) ∧ IsCompact L ∧ K ×ˢ L ⊆ U
  have hbase : ∃ d, Inv 0 d := by
    obtain ⟨V₀', W₀', hV₀', hW₀', hx₀V', hy₀W', hV₀'W₀'⟩ :=
      isOpen_prod_iff.1 (hU_stage n₀) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ hxy₀
    obtain ⟨V₀, hV₀, hx₀V₀, hclV₀⟩ :=
      normal_exists_closure_subset isClosed_singleton hV₀' (singleton_subset_iff.2 hx₀V')
    obtain ⟨W₀, hW₀, hy₀W₀, hclW₀⟩ :=
      normal_exists_closure_subset isClosed_singleton hW₀' (singleton_subset_iff.2 hy₀W')
    refine ⟨(Subtype.val '' V₀, Subtype.val '' closure V₀,
      Subtype.val '' W₀, Subtype.val '' closure W₀), ?_⟩
    have hK : IsCompact (Subtype.val '' closure V₀) :=
      (IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _)).image
        continuous_subtypeVal
    have hL : IsCompact (Subtype.val '' closure W₀) :=
      (IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _)).image
        continuous_subtypeVal
    have hV_eq : ((↑) : A (n₀ + 0) → c₁.pt) ⁻¹' (Subtype.val '' V₀) = V₀ := by
      ext ⟨x, hx⟩
      exact ⟨fun ⟨⟨a, _⟩, ha, h⟩ ↦ (Subtype.ext h) ▸ ha,
        fun hxV ↦ ⟨⟨x, hx⟩, hxV, rfl⟩⟩
    have hW_eq : ((↑) : B (n₀ + 0) → c₂.pt) ⁻¹' (Subtype.val '' W₀) = W₀ := by
      ext ⟨y, hy⟩
      exact ⟨fun ⟨⟨b, _⟩, hb, h⟩ ↦ (Subtype.ext h) ▸ hb,
        fun hyW ↦ ⟨⟨y, hy⟩, hyW, rfl⟩⟩
    refine ⟨⟨⟨x₀, hx₀⟩, hx₀V₀ rfl, rfl⟩,
      ⟨⟨y₀, hy₀⟩, hy₀W₀ rfl, rfl⟩,
      image_mono subset_closure, Subtype.coe_image_subset _ _,
      image_mono subset_closure, Subtype.coe_image_subset _ _,
      ?_, hK, ?_, hL, ?_⟩
    · dsimp only; rwa [hV_eq]
    · dsimp only; rwa [hW_eq]
    · rintro ⟨x, y⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      exact hV₀'W₀' (mk_mem_prod (hclV₀ ha) (hclW₀ hb))
  have hstep : ∀ (k : ℕ) (d : Set c₁.pt × Set c₁.pt × Set c₂.pt × Set c₂.pt),
      Inv k d → ∃ d', Inv (k + 1) d' ∧ d.1 ⊆ d'.1 ∧ d.2.2.1 ⊆ d'.2.2.1 := by
    rintro k ⟨V, K, W, L⟩ ⟨hxV, hyW, hVK, hKA, hWL, hLB, -, hKc, -, hLc, hKL⟩
    let n' := n₀ + (k + 1)
    have hAmono : A (n₀ + k) ⊆ A n' :=
      monotone_range_ι c₁ (Nat.add_le_add_left k.le_succ n₀)
    have hBmono : B (n₀ + k) ⊆ B n' :=
      monotone_range_ι c₂ (Nat.add_le_add_left k.le_succ n₀)
    have hK'c : IsCompact (((↑) : A n' → c₁.pt) ⁻¹' K) :=
      IsInducing.subtypeVal.isCompact_preimage' hKc (by
        rw [Subtype.range_coe_subtype]; exact hKA.trans hAmono)
    have hL'c : IsCompact (((↑) : B n' → c₂.pt) ⁻¹' L) :=
      IsInducing.subtypeVal.isCompact_preimage' hLc (by
        rw [Subtype.range_coe_subtype]; exact hLB.trans hBmono)
    have hsub : (((↑) : A n' → c₁.pt) ⁻¹' K) ×ˢ (((↑) : B n' → c₂.pt) ⁻¹' L) ⊆
        Prod.map ((↑) : A n' → c₁.pt) ((↑) : B n' → c₂.pt) ⁻¹' U := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact hKL (mk_mem_prod ha hb)
    obtain ⟨V', W', hV', hW', hKV', hLW', hVW'⟩ :=
      generalized_tube_lemma hK'c hL'c (hU_stage n') hsub
    obtain ⟨V'', hV'', hKV'', hclV''⟩ :=
      normal_exists_closure_subset hK'c.isClosed hV' hKV'
    obtain ⟨W'', hW'', hLW'', hclW''⟩ :=
      normal_exists_closure_subset hL'c.isClosed hW' hLW'
    have hK' : IsCompact (Subtype.val '' closure V'') :=
      (IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _)).image
        continuous_subtypeVal
    have hL' : IsCompact (Subtype.val '' closure W'') :=
      (IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _)).image
        continuous_subtypeVal
    have hKV_sub : K ⊆ Subtype.val '' V'' := fun x hx ↦
      ⟨⟨x, hAmono (hKA hx)⟩, hKV'' hx, rfl⟩
    have hLW_sub : L ⊆ Subtype.val '' W'' := fun y hy ↦
      ⟨⟨y, hBmono (hLB hy)⟩, hLW'' hy, rfl⟩
    have hV'_eq : ((↑) : A (n₀ + (k + 1)) → c₁.pt) ⁻¹' (Subtype.val '' V'') = V'' := by
      ext ⟨x, hx⟩
      exact ⟨fun ⟨⟨a, _⟩, ha, h⟩ ↦ (Subtype.ext h) ▸ ha,
        fun hxV ↦ ⟨⟨x, hx⟩, hxV, rfl⟩⟩
    have hW'_eq : ((↑) : B (n₀ + (k + 1)) → c₂.pt) ⁻¹' (Subtype.val '' W'') = W'' := by
      ext ⟨y, hy⟩
      exact ⟨fun ⟨⟨b, _⟩, hb, h⟩ ↦ (Subtype.ext h) ▸ hb,
        fun hyW ↦ ⟨⟨y, hy⟩, hyW, rfl⟩⟩
    refine ⟨(Subtype.val '' V'', Subtype.val '' closure V'',
      Subtype.val '' W'', Subtype.val '' closure W''), ⟨?_, ?_⟩⟩
    · refine ⟨hKV_sub (hVK hxV), hLW_sub (hWL hyW), image_mono subset_closure,
        Subtype.coe_image_subset _ _, image_mono subset_closure, Subtype.coe_image_subset _ _,
        ?_, hK', ?_, hL', ?_⟩
      · dsimp only; rwa [hV'_eq]
      · dsimp only; rwa [hW'_eq]
      · rintro ⟨x, y⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
        exact hVW' (mk_mem_prod (hclV'' ha) (hclW'' hb))
    · exact ⟨hVK.trans hKV_sub, hWL.trans hLW_sub⟩
  let seq : (k : ℕ) → { d // Inv k d } := Nat.rec ⟨hbase.choose, hbase.choose_spec⟩
    fun k d ↦ ⟨(hstep k d.val d.property).choose, (hstep k d.val d.property).choose_spec.1⟩
  have hseqV_mono : Monotone fun k ↦ (seq k).val.1 :=
    monotone_nat_of_le_succ fun k ↦ (hstep k (seq k).val (seq k).property).choose_spec.2.1
  have hseqW_mono : Monotone fun k ↦ (seq k).val.2.2.1 :=
    monotone_nat_of_le_succ fun k ↦ (hstep k (seq k).val (seq k).property).choose_spec.2.2
  let V := ⋃ k, (seq k).val.1
  let W := ⋃ k, (seq k).val.2.2.1
  have hV_open : IsOpen V := by
    rw [TopCat.isOpen_iff_of_isColimit _ hc₁]
    intro m
    choose O hO_open hO_eq using fun k ↦ isOpen_induced_iff.1 (seq k).property.2.2.2.2.2.2.1
    have hpre : c₁.ι.app m ⁻¹' V = ⋃ (k : ℕ) (_ : m ≤ k), c₁.ι.app m ⁻¹' O k := by
      ext z
      simp only [V, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨max m k, le_max_left m k, ?_⟩
        have hz_mem := hseqV_mono (le_max_right m k) hk
        have hzA : c₁.ι.app m z ∈ A (n₀ + max m k) :=
          monotone_range_ι c₁ (Nat.le_trans (le_max_left m k) (Nat.le_add_left _ _)) ⟨z, rfl⟩
        have hz_pre :
            ⟨c₁.ι.app m z, hzA⟩ ∈
              ((↑) : A (n₀ + max m k) → c₁.pt) ⁻¹' O (max m k) := by
          rw [hO_eq (max m k)]
          exact hz_mem
        exact hz_pre
      · rintro ⟨k, hmk, hk⟩
        have hzA : c₁.ι.app m z ∈ A (n₀ + k) :=
          monotone_range_ι c₁ (hmk.trans (Nat.le_add_left _ _)) ⟨z, rfl⟩
        have hz_pre :
            ⟨c₁.ι.app m z, hzA⟩ ∈
              ((↑) : A (n₀ + k) → c₁.pt) ⁻¹' (seq k).val.1 := by
          rw [← hO_eq k]
          exact hk
        exact ⟨k, hz_pre⟩
    rw [hpre]
    exact isOpen_iUnion fun k ↦
      isOpen_iUnion fun _ ↦ (hO_open k).preimage (c₁.ι.app m).hom.continuous
  have hW_open : IsOpen W := by
    rw [TopCat.isOpen_iff_of_isColimit _ hc₂]
    intro m
    choose O hO_open hO_eq using fun k ↦
      isOpen_induced_iff.1 (seq k).property.2.2.2.2.2.2.2.2.1
    have hpre : c₂.ι.app m ⁻¹' W = ⋃ (k : ℕ) (_ : m ≤ k), c₂.ι.app m ⁻¹' O k := by
      ext z
      simp only [W, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨max m k, le_max_left m k, ?_⟩
        have hz_mem := hseqW_mono (le_max_right m k) hk
        have hzB : c₂.ι.app m z ∈ B (n₀ + max m k) :=
          monotone_range_ι c₂ (Nat.le_trans (le_max_left m k) (Nat.le_add_left _ _)) ⟨z, rfl⟩
        have hz_pre :
            ⟨c₂.ι.app m z, hzB⟩ ∈
              ((↑) : B (n₀ + max m k) → c₂.pt) ⁻¹' O (max m k) := by
          rw [hO_eq (max m k)]
          exact hz_mem
        exact hz_pre
      · rintro ⟨k, hmk, hk⟩
        have hzB : c₂.ι.app m z ∈ B (n₀ + k) :=
          monotone_range_ι c₂ (hmk.trans (Nat.le_add_left _ _)) ⟨z, rfl⟩
        have hz_pre :
            ⟨c₂.ι.app m z, hzB⟩ ∈
              ((↑) : B (n₀ + k) → c₂.pt) ⁻¹' (seq k).val.2.2.1 := by
          rw [← hO_eq k]
          exact hk
        exact ⟨k, hz_pre⟩
    rw [hpre]
    exact isOpen_iUnion fun k ↦
      isOpen_iUnion fun _ ↦ (hO_open k).preimage (c₂.ι.app m).hom.continuous
  refine ⟨V ×ˢ W, ?_, hV_open.prod hW_open,
    ⟨mem_iUnion.2 ⟨0, (seq 0).property.1⟩, mem_iUnion.2 ⟨0, (seq 0).property.2.1⟩⟩⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨k₁, hk₁⟩ := mem_iUnion.1 hx
  obtain ⟨k₂, hk₂⟩ := mem_iUnion.1 hy
  let k := max k₁ k₂
  exact (seq k).property.2.2.2.2.2.2.2.2.2.2 <|
    mk_mem_prod ((seq k).property.2.2.1 (hseqV_mono (le_max_left k₁ k₂) hk₁))
      ((seq k).property.2.2.2.2.1 (hseqW_mono (le_max_right k₁ k₂) hk₂))

end Sequential

end TauCeti.TopCat
