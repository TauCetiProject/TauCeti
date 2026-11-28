/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Separation.Regular
public import TauCeti.Topology.Sets.Opens

/-!
# Operations on compact exhaustions and compact exhaustions of open sets

A sigma-compact open subset of a locally compact space has a monotone sequence of compact
subsets that exhausts it in the sense that every compact subset lies in one of them
(`IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset`).

Conversely, compact subsets `Kₙ ⊆ U` of the ambient space with `Kₙ ⊆ interior Kₙ₊₁` that cover
a subset `U` trace a compact exhaustion of the subspace `U` (`CompactExhaustion.subtype`); such
a `U` is open (`TauCeti.isOpen_of_subset_interior_succ`).

In an R₁ space, a locally compact σ-compact open set is the union of an increasing sequence of
open sets with compact closures inside it (`IsOpen.exists_iUnion_isOpen_isCompact_closure`).
Both hypotheses on the open set are also necessary for such an exhaustion.
For an open set `Ω` bundled as `Opens`, the same exhaustion covers the subspace `Ω`
(`TopologicalSpace.Opens.exists_monotone_isCompact_closure_iUnion_eq`), can be chosen with the
closure of each set inside the next
(`TopologicalSpace.Opens.exists_isCompact_closure_subset_succ_iUnion_eq`), and then eventually
contains every open set whose closure is compact and contained in `Ω`
(`TopologicalSpace.Opens.exists_isCompact_closure_subset_succ_forall_exists_le`). An open set of a
second-countable locally compact space, such as a proper pseudometric space, is locally compact
and σ-compact: for `Ω : Opens X` the instance `TopologicalSpace.Opens.instLocallyCompactSpace`
lets Lean find both there.

Also supplements `Mathlib.Topology.Compactness.SigmaCompact` with
`CompactExhaustion.sigmaCompactSpace`, `weaklyLocallyCompactSpace`, `instPartialOrder`,
`instSemilatticeSup` (`⊔`), `supSeq`, `supImage`, `supPreimage`, and
`CompactExhaustion.complOfCofinalNhdsSet`.
-/

public section

open Set Topology

/-- A sigma-compact open subset `Ω` of a locally compact space has a monotone sequence of
compact subsets of `Ω` such that every compact subset of `Ω` lies in one of them. -/
theorem IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {Ω : Set X} [SigmaCompactSpace Ω] (hΩ : IsOpen Ω) :
    ∃ L : ℕ → Set X, (∀ m, IsCompact (L m)) ∧ (∀ m, L m ⊆ Ω) ∧ Monotone L ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ m, K ⊆ L m := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let Kx : CompactExhaustion Ω := CompactExhaustion.choice Ω
  refine ⟨fun m => (↑) '' Kx m, fun m => (Kx.isCompact m).image continuous_subtypeVal,
    fun m => ?_, fun m m' h => image_mono (Kx.subset h), fun K hK hKΩ => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.property
  · have hK' : IsCompact (((↑) : Ω → X) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
    obtain ⟨m, hm⟩ := Kx.exists_superset_of_isCompact hK'
    exact ⟨m, fun x hx => ⟨⟨x, hKΩ hx⟩, hm hx, rfl⟩⟩

/-- **Exhaustion of an open set.** In an R₁ space, a locally compact σ-compact open set `U` is the
union of an increasing sequence of open sets `V n` whose closures are compact subsets of `U`. -/
theorem IsOpen.exists_iUnion_isOpen_isCompact_closure {X : Type*} [TopologicalSpace X] [R1Space X]
    {U : Set X} [WeaklyLocallyCompactSpace U] [SigmaCompactSpace U] (hU : IsOpen U) :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ (∀ n, IsCompact (closure (V n))) ∧
      (∀ n, closure (V n) ⊆ U) ∧ Monotone V ∧ ⋃ n, V n = U := by
  let K : CompactExhaustion U := CompactExhaustion.choice U
  -- `V n` is the interior of `K n` in the subspace `U`, viewed in `X`; it lies in the compact
  -- subset `(↑) '' K n` of `U`.
  have hK (n : ℕ) : IsCompact (((↑) : U → X) '' K n) := (K.isCompact n).image continuous_subtypeVal
  have hVK (n : ℕ) : ((↑) : U → X) '' interior (K n) ⊆ (↑) '' K n := image_mono interior_subset
  refine ⟨fun n ↦ (↑) '' interior (K n), fun n ↦ hU.isOpenMap_subtypeVal _ isOpen_interior,
    fun n ↦ (hK n).closure_of_subset (hVK n), fun n ↦ (closure_mono (hVK n)).trans
      ((hK n).closure_subset_of_isOpen hU (Subtype.coe_image_subset _ _)),
    fun m n hmn ↦ image_mono (interior_mono (K.subset hmn)), ?_⟩
  -- Every point of `U` lies in the interior of the next set after the one it first enters.
  have hint : ⋃ n, interior (K n) = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨K.find x + 1, K.subset_interior_succ _ (K.mem_find x)⟩
  rw [← image_iUnion, hint, image_univ, Subtype.range_coe]

namespace TauCeti

/-- A subset `U` covered by subsets `Kₙ ⊆ U` with `Kₙ ⊆ interior Kₙ₊₁` is open: it is the union of
the interiors of the `Kₙ`. -/
theorem isOpen_of_subset_interior_succ {X : Type*} [TopologicalSpace X] {U : Set X}
    {K : ℕ → Set X} (hKU : ∀ n, K n ⊆ U) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : U ⊆ ⋃ n, K n) : IsOpen U := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcover hx)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hsub n hn)) (hKU (n + 1))

end TauCeti

namespace CompactExhaustion

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any space admitting a compact exhaustion is `σ`-compact. -/
theorem sigmaCompactSpace (K : CompactExhaustion X) : SigmaCompactSpace X :=
  SigmaCompactSpace_iff_exists_compact_covering.2 ⟨K, K.isCompact, K.iUnion_eq⟩

/-- Any space admitting a compact exhaustion is weakly locally compact. -/
theorem weaklyLocallyCompactSpace (K : CompactExhaustion X) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x := let ⟨n, hn⟩ := K.exists_mem_nhds x; ⟨K n, K.isCompact n, hn⟩

/-- Pointwise inclusion order on compact exhaustions of the same space. -/
instance instPartialOrder : PartialOrder (CompactExhaustion X) :=
  PartialOrder.lift (fun K : CompactExhaustion X ↦ (K : ℕ → Set X)) DFunLike.coe_injective

theorem le_def {K₁ K₂ : CompactExhaustion X} : K₁ ≤ K₂ ↔ ∀ n, K₁ n ⊆ K₂ n := Iff.rfl

section SupSeq
variable (K : CompactExhaustion X) (S : ℕ → Set X) (hK : ∀ n, IsCompact (S n))
  (hS : ∀ n, S n ⊆ interior (S (n + 1)))

/-- Pointwise union of a compact exhaustion `K` with a sequence `S` of compact sets satisfying
`S n ⊆ interior (S (n + 1))`. -/
def supSeq : CompactExhaustion X where
  toFun n := K n ∪ S n
  isCompact' n := (K.isCompact n).union (hK n)
  subset_interior_succ' n := union_subset
    ((K.subset_interior_succ n).trans (interior_mono subset_union_left))
    ((hS n).trans (interior_mono subset_union_right))
  iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K.iUnion_eq

@[simp] lemma supSeq_apply (n : ℕ) : K.supSeq S hK hS n = K n ∪ S n := (rfl)
lemma subset_supSeq_left (n : ℕ) : K n ⊆ K.supSeq S hK hS n := subset_union_left
lemma subset_supSeq_right (n : ℕ) : S n ⊆ K.supSeq S hK hS n := subset_union_right
lemma le_supSeq_left : K ≤ K.supSeq S hK hS := fun _ ↦ subset_union_left
lemma supSeq_le_iff {K' : CompactExhaustion X} :
    K.supSeq S hK hS ≤ K' ↔ K ≤ K' ∧ ∀ n, S n ⊆ K' n :=
  ⟨fun h ↦ ⟨(K.le_supSeq_left S hK hS).trans h,
    fun n ↦ (K.subset_supSeq_right S hK hS n).trans (h n)⟩,
    fun ⟨h₁, h₂⟩ n ↦ union_subset (h₁ n) (h₂ n)⟩
lemma supSeq_le {K' : CompactExhaustion X} (h₁ : K ≤ K') (h₂ : ∀ n, S n ⊆ K' n) :
    K.supSeq S hK hS ≤ K' :=
  (K.supSeq_le_iff S hK hS).2 ⟨h₁, h₂⟩
end SupSeq

/-- Pointwise union of two compact exhaustions of the same space, as a join-semilattice. -/
instance instSemilatticeSup : SemilatticeSup (CompactExhaustion X) where
  sup K₁ K₂ := supSeq K₁ K₂ K₂.isCompact K₂.subset_interior_succ
  le_sup_left K₁ K₂ := K₁.le_supSeq_left K₂ K₂.isCompact K₂.subset_interior_succ
  le_sup_right K₁ K₂ n := K₁.subset_supSeq_right K₂ K₂.isCompact K₂.subset_interior_succ n
  sup_le K₁ K₂ _ h₁ h₂ := K₁.supSeq_le K₂ K₂.isCompact K₂.subset_interior_succ h₁ h₂

@[simp] lemma sup_apply (K₁ K₂ : CompactExhaustion X) (n : ℕ) : (K₁ ⊔ K₂) n = K₁ n ∪ K₂ n :=
  K₁.supSeq_apply K₂ K₂.isCompact K₂.subset_interior_succ n
lemma subset_sup_left (K₁ K₂ : CompactExhaustion X) (n : ℕ) : K₁ n ⊆ (K₁ ⊔ K₂) n :=
  K₁.subset_supSeq_left K₂ K₂.isCompact K₂.subset_interior_succ n
lemma subset_sup_right (K₁ K₂ : CompactExhaustion X) (n : ℕ) : K₂ n ⊆ (K₁ ⊔ K₂) n :=
  K₁.subset_supSeq_right K₂ K₂.isCompact K₂.subset_interior_succ n

section SupImage
variable (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f) (hfo : IsOpenMap f)
  (K_Y : CompactExhaustion Y)
/-- Enlarge `K_X` by the images of `K_Y` along a continuous open map `f : Y → X`. -/
def supImage : CompactExhaustion X :=
  supSeq K_X (fun n ↦ f '' K_Y n) (fun n ↦ (K_Y.isCompact n).image hfc) fun n ↦
    (image_mono (K_Y.subset_interior_succ n)).trans (hfo.image_interior_subset _)
@[simp] lemma supImage_apply (n : ℕ) : K_X.supImage hfc hfo K_Y n = K_X n ∪ f '' K_Y n :=
  K_X.supSeq_apply _ _ _ n
lemma subset_supImage_left (n : ℕ) : K_X n ⊆ K_X.supImage hfc hfo K_Y n :=
  K_X.subset_supSeq_left _ _ _ n
lemma image_subset_supImage (n : ℕ) : f '' K_Y n ⊆ K_X.supImage hfc hfo K_Y n := by
  rw [supImage_apply]; exact subset_union_right
lemma le_supImage_left : K_X ≤ K_X.supImage hfc hfo K_Y := K_X.le_supSeq_left _ _ _
lemma supImage_le_iff {K' : CompactExhaustion X} :
    K_X.supImage hfc hfo K_Y ≤ K' ↔ K_X ≤ K' ∧ ∀ n, f '' K_Y n ⊆ K' n :=
  K_X.supSeq_le_iff _ _ _
lemma supImage_le {K' : CompactExhaustion X} (h₁ : K_X ≤ K') (h₂ : ∀ n, f '' K_Y n ⊆ K' n) :
    K_X.supImage hfc hfo K_Y ≤ K' :=
  (K_X.supImage_le_iff hfc hfo K_Y).2 ⟨h₁, h₂⟩
end SupImage

section SupPreimage
variable (K_X : CompactExhaustion X) {f : X → Y} (hf : IsProperMap f) (K_Y : CompactExhaustion Y)
/-- Enlarge `K_X` by the preimages of `K_Y` along a proper map `f : X → Y`. -/
def supPreimage : CompactExhaustion X :=
  supSeq K_X (fun n ↦ f ⁻¹' K_Y n) (fun n ↦ hf.isCompact_preimage (K_Y.isCompact n)) fun n ↦
    (preimage_mono (K_Y.subset_interior_succ n)).trans
      (preimage_interior_subset_interior_preimage hf.continuous)
@[simp] lemma supPreimage_apply (n : ℕ) : K_X.supPreimage hf K_Y n = K_X n ∪ f ⁻¹' K_Y n :=
  K_X.supSeq_apply _ _ _ n
lemma subset_supPreimage_left (n : ℕ) : K_X n ⊆ K_X.supPreimage hf K_Y n :=
  K_X.subset_supSeq_left _ _ _ n
lemma preimage_subset_supPreimage (n : ℕ) : f ⁻¹' K_Y n ⊆ K_X.supPreimage hf K_Y n := by
  rw [supPreimage_apply]; exact subset_union_right
/-- A proper map `f` carries the complement of each stage of `K_X.supPreimage hf K_Y` into the
complement of the corresponding stage of `K_Y`. -/
lemma mapsTo_compl_supPreimage (n : ℕ) :
    MapsTo f (K_X.supPreimage hf K_Y n)ᶜ (K_Y n)ᶜ :=
  fun _ hx hfx ↦ hx (K_X.preimage_subset_supPreimage hf K_Y n hfx)
lemma le_supPreimage_left : K_X ≤ K_X.supPreimage hf K_Y := K_X.le_supSeq_left _ _ _
lemma supPreimage_le_iff {K' : CompactExhaustion X} :
    K_X.supPreimage hf K_Y ≤ K' ↔ K_X ≤ K' ∧ ∀ n, f ⁻¹' K_Y n ⊆ K' n :=
  K_X.supSeq_le_iff _ _ _
lemma supPreimage_le {K' : CompactExhaustion X} (h₁ : K_X ≤ K') (h₂ : ∀ n, f ⁻¹' K_Y n ⊆ K' n) :
    K_X.supPreimage hf K_Y ≤ K' :=
  (K_X.supPreimage_le_iff hf K_Y).2 ⟨h₁, h₂⟩
end SupPreimage

section Subtype
variable (U : Set X) (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n)) (hKU : ∀ n, K n ⊆ U)
  (hsub : ∀ n, K n ⊆ interior (K (n + 1))) (hcover : U ⊆ ⋃ n, K n)

/-- Compact subsets `Kₙ ⊆ U` of the ambient space with `Kₙ ⊆ interior Kₙ₊₁` that cover `U` trace
the compact exhaustion `n ↦ U ∩ Kₙ` of the subspace `U`. -/
-- The body is exposed so that its sets unfold to the preimages `Subtype.val ⁻¹' Kₙ`: pairs and
-- chain complexes built from the exhaustion must agree with those built from these preimages up to
-- definitional equality, as in the twisted relative chains of `U` and of `X`.
@[expose]
def subtype : CompactExhaustion U where
  toFun n := Subtype.val ⁻¹' K n
  isCompact' n := Subtype.isCompact_iff.2 <| by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 (hKU n)]
    exact hK n
  subset_interior_succ' n := (preimage_mono (hsub n)).trans
    (preimage_interior_subset_interior_preimage continuous_subtypeVal)
  iUnion_eq' := eq_univ_of_forall fun x ↦ by simpa using hcover x.property

@[simp]
theorem subtype_apply (n : ℕ) :
    CompactExhaustion.subtype U K hK hKU hsub hcover n = Subtype.val ⁻¹' K n :=
  (rfl)
end Subtype

section CofinalNeighborhoods

variable {A : Set X} [hComp : CompactSpace X] [hT2 : T2Space X] (hA : IsClosed A)
  {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
  (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
include hComp hT2 hA hU_open hAU hU_cofinal

/-- Compact exhaustion of `X \ A` from a countable cofinal open neighbourhood family of closed `A`
in a compact Hausdorff space `X`. -/
noncomputable def complOfCofinalNhdsSet : CompactExhaustion (Aᶜ : Set X) :=
  CompactExhaustion.subtype Aᶜ
    (fun n ↦ (U (TauCeti.shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n))ᶜ)
    (fun n ↦ (hU_open _).isClosed_compl.isCompact)
    (fun n ↦ compl_subset_compl.2 (hAU _))
    (fun n ↦ by
      rw [interior_compl]
      exact compl_subset_compl.2 <|
        (TauCeti.closure_apply_shrinkingNhdsSetIndex_succ_subset_inter
          hA hU_open hAU hU_cofinal n).trans inter_subset_left)
    (fun y hy ↦ mem_iUnion.2 <|
      let ⟨n, hn⟩ := hU_cofinal isClosed_singleton.isOpen_compl
        fun _ ha (hy' : _ = y) ↦ hy (hy' ▸ ha)
      ⟨n, fun hyU ↦ hn
        (TauCeti.apply_shrinkingNhdsSetIndex_subset hA hU_open hAU hU_cofinal n hyU) rfl⟩)

@[simp] lemma complOfCofinalNhdsSet_apply (n : ℕ) :
    complOfCofinalNhdsSet hA hU_open hAU hU_cofinal n =
      Subtype.val ⁻¹' (U (TauCeti.shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n))ᶜ := (rfl)

lemma image_subtypeVal_complOfCofinalNhdsSet (n : ℕ) :
    (Subtype.val : (Aᶜ : Set X) → X) '' complOfCofinalNhdsSet hA hU_open hAU hU_cofinal n =
      (U (TauCeti.shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n))ᶜ :=
  image_preimage_eq_iff.2 (Subtype.range_coe.symm ▸ compl_subset_compl.2 (hAU _))

lemma compl_image_subtypeVal_complOfCofinalNhdsSet (n : ℕ) :
    ((Subtype.val : (Aᶜ : Set X) → X) '' complOfCofinalNhdsSet hA hU_open hAU hU_cofinal n)ᶜ =
      U (TauCeti.shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n) := by
  rw [image_subtypeVal_complOfCofinalNhdsSet, compl_compl]

end CofinalNeighborhoods

end CompactExhaustion

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X] [R1Space X]

/-- **Exhaustion of an open set by opens.** In an R₁ space, a locally compact σ-compact open set `Ω`
is the union of an increasing sequence of open sets `V n` whose closures are compact
subsets of `Ω`; the traces of the `V n` on the subspace `Ω` cover it. -/
theorem exists_monotone_isCompact_closure_iUnion_eq (Ω : Opens X) [WeaklyLocallyCompactSpace Ω]
    [SigmaCompactSpace Ω] :
    ∃ V : ℕ → Opens X, (∀ n, IsCompact (closure (V n : Set X))) ∧
      (∀ n, closure (V n : Set X) ⊆ Ω) ∧ Monotone V ∧ ⋃ n, (V n : Set X) = Ω ∧
      ⋃ n, ((↑) : Ω → X) ⁻¹' (V n : Set X) = univ := by
  obtain ⟨V, hVo, hVc, hVΩ, hVmono, hVU⟩ := Ω.isOpen.exists_iUnion_isOpen_isCompact_closure
  refine ⟨fun n ↦ ⟨V n, hVo n⟩, hVc, hVΩ, fun _ _ h ↦ hVmono h, hVU, ?_⟩
  simp only [← preimage_iUnion, Opens.coe_mk, hVU]
  exact Subtype.coe_preimage_self _

/-- **Nested exhaustion of an open set.** In an R₁ space, a locally compact σ-compact open set `Ω`
is the union of a sequence of open sets `V n` with compact closures, the closure of each
lying in the next. It is a subsequence of the exhaustion
`TopologicalSpace.Opens.exists_monotone_isCompact_closure_iUnion_eq`. -/
theorem exists_isCompact_closure_subset_succ_iUnion_eq (Ω : Opens X) [WeaklyLocallyCompactSpace Ω]
    [SigmaCompactSpace Ω] :
    ∃ V : ℕ → Opens X, (∀ n, IsCompact (closure (V n : Set X))) ∧
      (∀ n, closure (V n : Set X) ⊆ V (n + 1)) ∧ ⋃ n, (V n : Set X) = Ω := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  -- Each closure lies in a strictly later set of the exhaustion.
  have hg : ∀ m, ∃ N, m < N ∧ closure (V m : Set X) ⊆ V N := fun m => by
    obtain ⟨N, hN⟩ := (hVc m).elim_directed_cover (fun n => (V n : Set X))
      (fun n => (V n).isOpen) ((hVΩ m).trans hVU.symm.subset)
      (Monotone.directed_le fun _ _ h => SetLike.coe_subset_coe.2 (hVmono h))
    exact ⟨max N (m + 1), by omega, hN.trans (SetLike.coe_subset_coe.2 (hVmono (le_max_left ..)))⟩
  choose g hgm hgV using hg
  have hle : ∀ n, n ≤ g^[n] 0 := fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans_lt (hgm _)
  refine ⟨fun n => V (g^[n] 0), fun n => hVc _, fun n => ?_, subset_antisymm
    (iUnion_subset fun n => hVU ▸ subset_iUnion (fun n => (V n : Set X)) _)
    (hVU.symm.subset.trans (iUnion_mono fun n => SetLike.coe_subset_coe.2 (hVmono (hle n))))⟩
  simpa only [Function.iterate_succ_apply'] using hgV (g^[n] 0)

/-- **Nested exhaustion of an open set absorbing relatively compact opens.** In an R₁ space, a
locally compact σ-compact open set `Ω` has an exhaustion by open sets `V n` with compact
closures inside `Ω`, the closure of each lying in the next, such that every open set `W` whose
closure is compact and contained in `Ω` lies in some `V n`. -/
theorem exists_isCompact_closure_subset_succ_forall_exists_le (Ω : Opens X)
    [WeaklyLocallyCompactSpace Ω] [SigmaCompactSpace Ω] :
    ∃ V : ℕ → Opens X, (∀ n, IsCompact (closure (V n : Set X))) ∧
      (∀ n, closure (V n : Set X) ⊆ V (n + 1)) ∧ (∀ n, closure (V n : Set X) ⊆ Ω) ∧
      ∀ W : Opens X, IsCompact (closure (W : Set X)) →
        closure (W : Set X) ⊆ Ω → ∃ n, W ≤ V n := by
  obtain ⟨V, hVc, hVsucc, hVU⟩ := Ω.exists_isCompact_closure_subset_succ_iUnion_eq
  have hVmono : Monotone V := monotone_nat_of_le_succ fun n =>
    SetLike.coe_subset_coe.1 (subset_closure.trans (hVsucc n))
  refine ⟨V, hVc, hVsucc, fun n =>
    (hVsucc n).trans (hVU ▸ subset_iUnion (fun n => (V n : Set X)) (n + 1)),
    fun W hWc hWΩ => ?_⟩
  obtain ⟨n, hn⟩ := hWc.elim_directed_cover (fun n => (V n : Set X)) (fun n => (V n).isOpen)
    (hWΩ.trans hVU.symm.subset)
    (Monotone.directed_le fun _ _ h => SetLike.coe_subset_coe.2 (hVmono h))
  exact ⟨n, SetLike.coe_subset_coe.1 (subset_closure.trans hn)⟩

end TopologicalSpace.Opens
