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
  closed (`CategoryTheory.Limits.IsColimit.isClosed_of_forall_finite_preimage`), and since the
  same holds for all of its subsets, it is discrete
  (`TauCeti.TopCat.isDiscrete_of_forall_finite_preimage`).
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
finitely many points is discrete. -/
theorem isDiscrete_of_forall_finite_preimage [∀ j, T1Space (F.obj j)] (hc : IsColimit c)
    {S : Set c.pt} (hS : ∀ j, (c.ι.app j ⁻¹' S).Finite) : IsDiscrete S :=
  isDiscrete_iff_forall_mem_exists_isClosed.2 fun t ht ↦
    ⟨t, hc.isClosed_of_forall_finite_preimage fun j ↦ (hS j).subset (preimage_mono ht),
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
    hK.of_isClosed_subset (hc.isClosed_of_forall_finite_preimage hfin)
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

private structure ProdChainInv {F₁ F₂ : ℕ ⥤ TopCat.{w}} (c₁ : Cocone F₁) (c₂ : Cocone F₂)
    (x₀ : c₁.pt) (y₀ : c₂.pt) (U : Set (c₁.pt × c₂.pt)) (n : ℕ) where
  V : Set c₁.pt
  K : Set c₁.pt
  W : Set c₂.pt
  L : Set c₂.pt
  mem_V : x₀ ∈ V
  mem_W : y₀ ∈ W
  V_subset_K : V ⊆ K
  K_subset_range : K ⊆ range (c₁.ι.app n)
  W_subset_L : W ⊆ L
  L_subset_range : L ⊆ range (c₂.ι.app n)
  isOpen_V : IsOpen ((Subtype.val : range (c₁.ι.app n) → c₁.pt) ⁻¹' V)
  isCompact_K : IsCompact K
  isOpen_W : IsOpen ((Subtype.val : range (c₂.ι.app n) → c₂.pt) ⁻¹' W)
  isCompact_L : IsCompact L
  prod_subset : K ×ˢ L ⊆ U

private def ProdChainInv.ofStage {F₁ F₂ : ℕ ⥤ TopCat.{w}} {c₁ : Cocone F₁} {c₂ : Cocone F₂}
    {x₀ : c₁.pt} {y₀ : c₂.pt} {U : Set (c₁.pt × c₂.pt)} {n : ℕ}
    [CompactSpace (range (c₁.ι.app n))] [CompactSpace (range (c₂.ι.app n))]
    {V'' V' : Set (range (c₁.ι.app n))} {W'' W' : Set (range (c₂.ι.app n))}
    (hV'' : IsOpen V'') (hW'' : IsOpen W'')
    (hx₀ : x₀ ∈ Subtype.val '' V'') (hy₀ : y₀ ∈ Subtype.val '' W'')
    (hclV'' : closure V'' ⊆ V') (hclW'' : closure W'' ⊆ W')
    (hVW' : V' ×ˢ W' ⊆ Prod.map (Subtype.val : range (c₁.ι.app n) → c₁.pt)
      (Subtype.val : range (c₂.ι.app n) → c₂.pt) ⁻¹' U) :
    ProdChainInv c₁ c₂ x₀ y₀ U n where
  V := Subtype.val '' V''
  K := Subtype.val '' closure V''
  W := Subtype.val '' W''
  L := Subtype.val '' closure W''
  mem_V := hx₀
  mem_W := hy₀
  V_subset_K := image_mono subset_closure
  K_subset_range := Subtype.coe_image_subset _ _
  W_subset_L := image_mono subset_closure
  L_subset_range := Subtype.coe_image_subset _ _
  isOpen_V := by rwa [Set.preimage_image_eq _ Subtype.val_injective]
  isCompact_K := isClosed_closure.isCompact.image continuous_subtypeVal
  isOpen_W := by rwa [Set.preimage_image_eq _ Subtype.val_injective]
  isCompact_L := isClosed_closure.isCompact.image continuous_subtypeVal
  prod_subset := by
    rintro ⟨x, y⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    exact hVW' (mk_mem_prod (hclV'' ha) (hclW'' hb))

private theorem isOpen_stage_trace_prod
    {F₁ F₂ : ℕ ⥤ TopCat.{w}} [∀ n, CompactSpace (F₁.obj n)] [∀ n, T2Space (F₁.obj n)]
    [∀ n, CompactSpace (F₂.obj n)] [∀ n, T2Space (F₂.obj n)]
    [∀ n, Small.{u} (F₁.obj n)] [∀ n, Small.{u} (F₂.obj n)]
    {c₁ : Cocone F₁} {c₂ : Cocone F₂}
    (hι₁ : ∀ n, IsEmbedding (c₁.ι.app n)) (hι₂ : ∀ n, IsEmbedding (c₂.ι.app n))
    {U : Set (c₁.pt × c₂.pt)}
    (hU : ∀ (K : CompHaus.{u}) (f : C(K, c₁.pt × c₂.pt)), IsOpen (f ⁻¹' U)) (n : ℕ) :
    IsOpen (Prod.map (Subtype.val : range (c₁.ι.app n) → c₁.pt)
      (Subtype.val : range (c₂.ι.app n) → c₂.pt) ⁻¹' U) := by
  let pmap := (c₁.ι.app n).hom.prodMap (c₂.ι.app n).hom
  let eShrink := Shrink.homeomorph.{u, w} (F₁.obj n × F₂.obj n)
  have : CompactSpace (Shrink.{u} (F₁.obj n × F₂.obj n)) := eShrink.compactSpace
  have : T2Space (Shrink.{u} (F₁.obj n × F₂.obj n)) := eShrink.t2Space
  let f : C(CompHaus.of (Shrink.{u} (F₁.obj n × F₂.obj n)), c₁.pt × c₂.pt) :=
    pmap.comp ⟨eShrink.symm, eShrink.symm.continuous⟩
  have hpre : IsOpen (pmap ⁻¹' U) := by
    convert eShrink.continuous.isOpen_preimage _ (hU _ f) using 1
    ext x
    simp [f, Homeomorph.symm_apply_apply]
  let e₁ := (hι₁ n).toHomeomorph
  let e₂ := (hι₂ n).toHomeomorph
  let hrange := e₁.prodCongr e₂
  have heq : hrange.symm ⁻¹' (pmap ⁻¹' U) =
      Prod.map (Subtype.val : range (c₁.ι.app n) → c₁.pt)
        (Subtype.val : range (c₂.ι.app n) → c₂.pt) ⁻¹' U := by
    ext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have ha' : c₁.ι.app n (e₁.symm ⟨a, ha⟩) = a :=
      congrArg Subtype.val (e₁.apply_symm_apply ⟨a, ha⟩)
    have hb' : c₂.ι.app n (e₂.symm ⟨b, hb⟩) = b :=
      congrArg Subtype.val (e₂.apply_symm_apply ⟨b, hb⟩)
    simp [pmap, hrange, ha', hb']
  rw [← heq]
  exact hrange.symm.continuous.isOpen_preimage _ hpre

private theorem exists_prodChainInv_zero
    {F₁ F₂ : ℕ ⥤ TopCat.{w}} {c₁ : Cocone F₁} {c₂ : Cocone F₂}
    {x₀ : c₁.pt} {y₀ : c₂.pt} {U : Set (c₁.pt × c₂.pt)} (n₀ : ℕ)
    [CompactSpace (range (c₁.ι.app n₀))] [T2Space (range (c₁.ι.app n₀))]
    [CompactSpace (range (c₂.ι.app n₀))] [T2Space (range (c₂.ι.app n₀))]
    (hx₀ : x₀ ∈ range (c₁.ι.app n₀)) (hy₀ : y₀ ∈ range (c₂.ι.app n₀)) (hxy₀ : (x₀, y₀) ∈ U)
    (hU_stage : IsOpen (Prod.map (Subtype.val : range (c₁.ι.app n₀) → c₁.pt)
      (Subtype.val : range (c₂.ι.app n₀) → c₂.pt) ⁻¹' U)) :
    Nonempty (ProdChainInv c₁ c₂ x₀ y₀ U n₀) := by
  obtain ⟨V₀', W₀', hV₀', hW₀', hx₀V', hy₀W', hV₀'W₀'⟩ :=
    isOpen_prod_iff.1 hU_stage ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ hxy₀
  obtain ⟨V₀, hV₀, hx₀V₀, hclV₀⟩ :=
    normal_exists_closure_subset isClosed_singleton hV₀' (singleton_subset_iff.2 hx₀V')
  obtain ⟨W₀, hW₀, hy₀W₀, hclW₀⟩ :=
    normal_exists_closure_subset isClosed_singleton hW₀' (singleton_subset_iff.2 hy₀W')
  exact ⟨ProdChainInv.ofStage hV₀ hW₀ ⟨⟨x₀, hx₀⟩, hx₀V₀ rfl, rfl⟩
    ⟨⟨y₀, hy₀⟩, hy₀W₀ rfl, rfl⟩ hclV₀ hclW₀ hV₀'W₀'⟩

private theorem exists_prodChainInv_succ
    {F₁ F₂ : ℕ ⥤ TopCat.{w}} {c₁ : Cocone F₁} {c₂ : Cocone F₂}
    {x₀ : c₁.pt} {y₀ : c₂.pt} {U : Set (c₁.pt × c₂.pt)} {n n' : ℕ} (hle : n ≤ n')
    [CompactSpace (range (c₁.ι.app n'))] [T2Space (range (c₁.ι.app n'))]
    [CompactSpace (range (c₂.ι.app n'))] [T2Space (range (c₂.ι.app n'))]
    (hU_stage : IsOpen (Prod.map (Subtype.val : range (c₁.ι.app n') → c₁.pt)
      (Subtype.val : range (c₂.ι.app n') → c₂.pt) ⁻¹' U))
    (d : ProdChainInv c₁ c₂ x₀ y₀ U n) :
    ∃ d' : ProdChainInv c₁ c₂ x₀ y₀ U n', d.V ⊆ d'.V ∧ d.W ⊆ d'.W := by
  have hAmono : range (c₁.ι.app n) ⊆ range (c₁.ι.app n') := monotone_range_ι c₁ hle
  have hBmono : range (c₂.ι.app n) ⊆ range (c₂.ι.app n') := monotone_range_ι c₂ hle
  have hK'c : IsCompact ((Subtype.val : range (c₁.ι.app n') → c₁.pt) ⁻¹' d.K) :=
    IsInducing.subtypeVal.isCompact_preimage' d.isCompact_K (by
      rw [Subtype.range_coe_subtype]; exact d.K_subset_range.trans hAmono)
  have hL'c : IsCompact ((Subtype.val : range (c₂.ι.app n') → c₂.pt) ⁻¹' d.L) :=
    IsInducing.subtypeVal.isCompact_preimage' d.isCompact_L (by
      rw [Subtype.range_coe_subtype]; exact d.L_subset_range.trans hBmono)
  have hsub : ((Subtype.val : range (c₁.ι.app n') → c₁.pt) ⁻¹' d.K) ×ˢ
      ((Subtype.val : range (c₂.ι.app n') → c₂.pt) ⁻¹' d.L) ⊆
      Prod.map (Subtype.val : range (c₁.ι.app n') → c₁.pt)
        (Subtype.val : range (c₂.ι.app n') → c₂.pt) ⁻¹' U :=
    fun ⟨a, b⟩ ⟨ha, hb⟩ ↦ d.prod_subset (mk_mem_prod ha hb)
  obtain ⟨V', W', hV', hW', hKV', hLW', hVW'⟩ :=
    generalized_tube_lemma hK'c hL'c hU_stage hsub
  obtain ⟨V'', hV'', hKV'', hclV''⟩ :=
    normal_exists_closure_subset hK'c.isClosed hV' hKV'
  obtain ⟨W'', hW'', hLW'', hclW''⟩ :=
    normal_exists_closure_subset hL'c.isClosed hW' hLW'
  have hKV_sub : d.K ⊆ Subtype.val '' V'' := fun x hx ↦
    ⟨⟨x, hAmono (d.K_subset_range hx)⟩, hKV'' hx, rfl⟩
  have hLW_sub : d.L ⊆ Subtype.val '' W'' := fun y hy ↦
    ⟨⟨y, hBmono (d.L_subset_range hy)⟩, hLW'' hy, rfl⟩
  exact ⟨ProdChainInv.ofStage hV'' hW'' (hKV_sub (d.V_subset_K d.mem_V))
    (hLW_sub (d.W_subset_L d.mem_W)) hclV'' hclW'' hVW',
    d.V_subset_K.trans hKV_sub, d.W_subset_L.trans hLW_sub⟩

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
  have (n : ℕ) : CompactSpace (range (c₁.ι.app n)) := (hι₁ n).toHomeomorph.compactSpace
  have (n : ℕ) : T2Space (range (c₁.ι.app n)) := (hι₁ n).toHomeomorph.t2Space
  have (n : ℕ) : CompactSpace (range (c₂.ι.app n)) := (hι₂ n).toHomeomorph.compactSpace
  have (n : ℕ) : T2Space (range (c₂.ι.app n)) := (hι₂ n).toHomeomorph.t2Space
  have hU_stage := isOpen_stage_trace_prod hι₁ hι₂ hU
  obtain ⟨n₁, hn₁⟩ := mem_iUnion.1 (iUnion_range_ι_of_isColimit hc₁ ▸ mem_univ x₀)
  obtain ⟨n₂, hn₂⟩ := mem_iUnion.1 (iUnion_range_ι_of_isColimit hc₂ ▸ mem_univ y₀)
  let n₀ := max n₁ n₂
  obtain ⟨d₀⟩ := exists_prodChainInv_zero n₀ (monotone_range_ι c₁ (le_max_left n₁ n₂) hn₁)
    (monotone_range_ι c₂ (le_max_right n₁ n₂) hn₂) hxy₀ (hU_stage n₀)
  have hstep (k : ℕ) (d : ProdChainInv c₁ c₂ x₀ y₀ U (n₀ + k)) :=
    exists_prodChainInv_succ (Nat.add_le_add_left k.le_succ n₀) (hU_stage (n₀ + (k + 1))) d
  let seq : (k : ℕ) → ProdChainInv c₁ c₂ x₀ y₀ U (n₀ + k) :=
    Nat.rec d₀ fun k d ↦ (hstep k d).choose
  have hseqV_mono : Monotone fun k ↦ (seq k).V :=
    monotone_nat_of_le_succ fun k ↦ (hstep k (seq k)).choose_spec.1
  have hseqW_mono : Monotone fun k ↦ (seq k).W :=
    monotone_nat_of_le_succ fun k ↦ (hstep k (seq k)).choose_spec.2
  have hV_open := isOpen_iUnion_of_isColimit hc₁ n₀ (fun k ↦ (seq k).V) hseqV_mono
    fun k ↦ (seq k).isOpen_V
  have hW_open := isOpen_iUnion_of_isColimit hc₂ n₀ (fun k ↦ (seq k).W) hseqW_mono
    fun k ↦ (seq k).isOpen_W
  refine ⟨(⋃ k, (seq k).V) ×ˢ (⋃ k, (seq k).W), ?_, hV_open.prod hW_open,
    ⟨mem_iUnion.2 ⟨0, (seq 0).mem_V⟩, mem_iUnion.2 ⟨0, (seq 0).mem_W⟩⟩⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨k₁, hk₁⟩ := mem_iUnion.1 hx
  obtain ⟨k₂, hk₂⟩ := mem_iUnion.1 hy
  let k := max k₁ k₂
  exact (seq k).prod_subset <| mk_mem_prod
    ((seq k).V_subset_K (hseqV_mono (le_max_left k₁ k₂) hk₁))
    ((seq k).W_subset_L (hseqW_mono (le_max_right k₁ k₂) hk₂))

end Sequential

end TauCeti.TopCat
