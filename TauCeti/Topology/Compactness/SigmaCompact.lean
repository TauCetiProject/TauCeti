/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# Operations on compact exhaustions and compact exhaustions of open sets

Supplements `Mathlib.Topology.Compactness.SigmaCompact` with `CompactExhaustion.sigmaCompactSpace`,
`weaklyLocallyCompactSpace`, `instMax` (`⊔`), `supImage`, `supPreimage`,
`CompactExhaustion.complOfCofinalNhds` (via `TauCeti.cofinalNhdsIndex`),
`CompactExhaustion.subtype`, and `TauCeti.isOpen_of_subset_interior_succ`.
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

namespace CompactExhaustion

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any space admitting a compact exhaustion is `σ`-compact. -/
theorem sigmaCompactSpace (K : CompactExhaustion X) : SigmaCompactSpace X :=
  SigmaCompactSpace_iff_exists_compact_covering.2 ⟨K, K.isCompact, K.iUnion_eq⟩

/-- Any space admitting a compact exhaustion is weakly locally compact. -/
theorem weaklyLocallyCompactSpace (K : CompactExhaustion X) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x := let ⟨n, hn⟩ := K.exists_mem_nhds x; ⟨K n, K.isCompact n, hn⟩

private def supSeq (K : CompactExhaustion X) (S : ℕ → Set X) (hK : ∀ n, IsCompact (S n))
    (hS : ∀ n, S n ⊆ interior (S (n + 1))) : CompactExhaustion X where
  toFun n := K n ∪ S n
  isCompact' n := (K.isCompact n).union (hK n)
  subset_interior_succ' n := union_subset
    ((K.subset_interior_succ n).trans (interior_mono subset_union_left))
    ((hS n).trans (interior_mono subset_union_right))
  iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K.iUnion_eq

/-- Pointwise union of two compact exhaustions of the same space. -/
instance instMax : Max (CompactExhaustion X) where
  max K₁ K₂ :=
    { toFun n := K₁ n ∪ K₂ n
      isCompact' n := (K₁.isCompact n).union (K₂.isCompact n)
      subset_interior_succ' n := union_subset
        ((K₁.subset_interior_succ n).trans (interior_mono subset_union_left))
        ((K₂.subset_interior_succ n).trans (interior_mono subset_union_right))
      iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K₁.iUnion_eq }
@[simp] lemma sup_apply (K₁ K₂ : CompactExhaustion X) (n : ℕ) : (K₁ ⊔ K₂) n = K₁ n ∪ K₂ n := (rfl)
lemma subset_sup_left (K₁ K₂ : CompactExhaustion X) (n : ℕ) : K₁ n ⊆ (K₁ ⊔ K₂) n :=
  subset_union_left
lemma subset_sup_right (K₁ K₂ : CompactExhaustion X) (n : ℕ) : K₂ n ⊆ (K₁ ⊔ K₂) n :=
  subset_union_right

section SupImage
variable (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f) (hfo : IsOpenMap f)
  (K_Y : CompactExhaustion Y)
/-- Enlarge `K_X` by the images of `K_Y` along a continuous open map `f : Y → X`. -/
def supImage : CompactExhaustion X :=
  supSeq K_X (fun n ↦ f '' K_Y n) (fun n ↦ (K_Y.isCompact n).image hfc) fun n ↦
    (image_mono (K_Y.subset_interior_succ n)).trans <|
      (hfo _ isOpen_interior).subset_interior_iff.2 (image_mono interior_subset)
@[simp] lemma supImage_apply (n : ℕ) : K_X.supImage hfc hfo K_Y n = K_X n ∪ f '' K_Y n := (rfl)
lemma subset_supImage_left (n : ℕ) : K_X n ⊆ K_X.supImage hfc hfo K_Y n := subset_union_left
lemma image_subset_supImage (n : ℕ) : f '' K_Y n ⊆ K_X.supImage hfc hfo K_Y n := subset_union_right
end SupImage

section SupPreimage
variable (K_X : CompactExhaustion X) {f : X → Y} (hf : IsProperMap f) (K_Y : CompactExhaustion Y)
/-- Enlarge `K_X` by the preimages of `K_Y` along a proper map `f : X → Y`. -/
def supPreimage : CompactExhaustion X :=
  supSeq K_X (fun n ↦ f ⁻¹' K_Y n) (fun n ↦ hf.isCompact_preimage (K_Y.isCompact n)) fun n ↦
    (preimage_mono (K_Y.subset_interior_succ n)).trans <|
      (isOpen_interior.preimage hf.continuous).subset_interior_iff.2 (preimage_mono interior_subset)
@[simp] lemma supPreimage_apply (n : ℕ) : K_X.supPreimage hf K_Y n = K_X n ∪ f ⁻¹' K_Y n := (rfl)
lemma subset_supPreimage_left (n : ℕ) : K_X n ⊆ K_X.supPreimage hf K_Y n := subset_union_left
lemma preimage_subset_supPreimage (n : ℕ) : f ⁻¹' K_Y n ⊆ K_X.supPreimage hf K_Y n :=
  subset_union_right
end SupPreimage

end CompactExhaustion

namespace TauCeti

/-- A subset `U` covered by subsets `Kₙ ⊆ U` with `Kₙ ⊆ interior Kₙ₊₁` is open: it is the union of
the interiors of the `Kₙ`. -/
theorem isOpen_of_subset_interior_succ {X : Type*} [TopologicalSpace X] {U : Set X}
    {K : ℕ → Set X} (hKU : ∀ n, K n ⊆ U) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : U ⊆ ⋃ n, K n) : IsOpen U := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcover hx)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hsub n hn)) (hKU (n + 1))

section CofinalNeighborhoods

variable {X : Type*} [TopologicalSpace X] [hNorm : NormalSpace X] {A : Set X} (hA : IsClosed A)
  {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
  (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
include hNorm hA hU_open hAU hU_cofinal

private lemma exists_closure_subset_inter (k m : ℕ) : ∃ j, closure (U j) ⊆ U k ∩ U m := by
  obtain ⟨W, hW_open, hAW, hW_cl⟩ := normal_exists_closure_subset hA
    ((hU_open k).inter (hU_open m)) (subset_inter (hAU k) (hAU m))
  exact let ⟨j, hj⟩ := hU_cofinal hW_open hAW; ⟨j, (closure_mono hj).trans hW_cl⟩

/-- Shrinking index sequence extracted from a countable cofinal open neighbourhood family of `A`. -/
noncomputable def cofinalNhdsIndex : ℕ → ℕ
  | 0 => 0
  | n + 1 => (exists_closure_subset_inter hA hU_open hAU hU_cofinal
      (cofinalNhdsIndex n) (n + 1)).choose
@[simp] lemma cofinalNhdsIndex_zero : cofinalNhdsIndex hA hU_open hAU hU_cofinal 0 = 0 := (rfl)
lemma closure_apply_cofinalNhdsIndex_succ_subset_inter (n : ℕ) :
    closure (U (cofinalNhdsIndex hA hU_open hAU hU_cofinal (n + 1))) ⊆
      U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) ∩ U (n + 1) :=
  (exists_closure_subset_inter hA hU_open hAU hU_cofinal _ (n + 1)).choose_spec
lemma apply_cofinalNhdsIndex_subset : ∀ n, U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) ⊆ U n
  | 0 => Subset.rfl
  | n + 1 => subset_closure.trans <|
      (closure_apply_cofinalNhdsIndex_succ_subset_inter hA hU_open hAU hU_cofinal n).trans
        inter_subset_right

end CofinalNeighborhoods

end TauCeti

namespace CompactExhaustion

section CofinalNeighborhoods

private lemma image_subtypeVal_preimage_compl {X : Type*} {A B : Set X} (hAB : A ⊆ B) :
    (Subtype.val : (Aᶜ : Set X) → X) '' (Subtype.val ⁻¹' Bᶜ) = Bᶜ :=
  image_preimage_eq_iff.2 (Subtype.range_coe.symm ▸ compl_subset_compl.2 hAB)

variable {X : Type*} [TopologicalSpace X] [hComp : CompactSpace X] [hT2 : T2Space X] {A : Set X}
  (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
  (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
include hComp hT2 hA hU_open hAU hU_cofinal

/-- Compact exhaustion of `X \ A` from a countable cofinal open neighbourhood family of closed `A`
in a compact Hausdorff space `X`. -/
noncomputable def complOfCofinalNhds : CompactExhaustion (Aᶜ : Set X) where
  toFun n := Subtype.val ⁻¹' (U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ
  isCompact' n := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_subtypeVal_preimage_compl (hAU _)]
    exact (hU_open _).isClosed_compl.isCompact
  subset_interior_succ' n :=
    (preimage_mono (compl_subset_compl.2 <|
      (TauCeti.closure_apply_cofinalNhdsIndex_succ_subset_inter hA hU_open hAU hU_cofinal n).trans
        inter_subset_left)).trans <|
      (isClosed_closure.isOpen_compl.preimage continuous_subtypeVal).subset_interior_iff.2
        (preimage_mono (compl_subset_compl.2 subset_closure))
  iUnion_eq' := eq_univ_iff_forall.2 fun y ↦ mem_iUnion.2 <|
    let ⟨n, hn⟩ := hU_cofinal isClosed_singleton.isOpen_compl
      fun _ ha (hy : _ = y.val) ↦ y.property (hy ▸ ha)
    ⟨n, fun hyU ↦ hn (TauCeti.apply_cofinalNhdsIndex_subset hA hU_open hAU hU_cofinal n hyU) rfl⟩
@[simp] lemma complOfCofinalNhds_apply (n : ℕ) :
    complOfCofinalNhds hA hU_open hAU hU_cofinal n =
      Subtype.val ⁻¹' (U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ := (rfl)
lemma image_subtypeVal_complOfCofinalNhds (n : ℕ) :
    (Subtype.val : (Aᶜ : Set X) → X) '' complOfCofinalNhds hA hU_open hAU hU_cofinal n =
      (U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ :=
  image_subtypeVal_preimage_compl (hAU _)
lemma compl_image_subtypeVal_complOfCofinalNhds (n : ℕ) :
    ((Subtype.val : (Aᶜ : Set X) → X) '' complOfCofinalNhds hA hU_open hAU hU_cofinal n)ᶜ =
      U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n) := by
  rw [image_subtypeVal_complOfCofinalNhds, compl_compl]

end CofinalNeighborhoods

variable {X : Type*} [TopologicalSpace X] (U : Set X) (K : ℕ → Set X)
  (hK : ∀ n, IsCompact (K n)) (hKU : ∀ n, K n ⊆ U) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
  (hcover : U ⊆ ⋃ n, K n)

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

end CompactExhaustion
