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

This file supplements `Mathlib.Topology.Compactness.SigmaCompact` with general-purpose operations
and constructions on `CompactExhaustion`:

* `IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset`: a `σ`-compact
  open subset of a locally compact space has a monotone sequence of compact subsets exhausting every
  compact subset.
* `CompactExhaustion.sigmaCompactSpace` and `CompactExhaustion.weaklyLocallyCompactSpace`: any space
  admitting a compact exhaustion is `σ`-compact and weakly locally compact.
* `CompactExhaustion.instMax` (`⊔`), `CompactExhaustion.supImage`, and
  `CompactExhaustion.supPreimage`: pointwise union of compact exhaustions, enlargement along a
  continuous open map, and enlargement by preimages along a proper map.
* `TauCeti.cofinalNhdsIndex` and `CompactExhaustion.complOfCofinalNhds`: in a compact Hausdorff
  space `X`, a countable cofinal family of open neighbourhoods of a closed subset `A` yields a
  compact exhaustion of `Aᶜ`.
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
  refine ⟨fun m => (↑) '' Kx m, fun m => (Kx.isCompact m).image continuous_subtype_val,
    fun m => ?_, fun m m' h => image_mono (Kx.subset h), fun K hK hKΩ => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hK' : IsCompact (((↑) : Ω → X) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
    obtain ⟨m, hm⟩ := Kx.exists_superset_of_isCompact hK'
    exact ⟨m, fun x hx => ⟨⟨x, hKΩ hx⟩, hm hx, rfl⟩⟩

namespace CompactExhaustion

section Operations

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any space admitting a compact exhaustion is `σ`-compact. -/
theorem sigmaCompactSpace (K : CompactExhaustion X) : SigmaCompactSpace X :=
  SigmaCompactSpace_iff_exists_compact_covering.2 ⟨K, K.isCompact, K.iUnion_eq⟩

/-- Any space admitting a compact exhaustion is weakly locally compact. -/
theorem weaklyLocallyCompactSpace (K : CompactExhaustion X) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x := let ⟨n, hn⟩ := K.exists_mem_nhds x; ⟨K n, K.isCompact n, hn⟩

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

/-- Enlarge a compact exhaustion of `X` by the images of a compact exhaustion of `Y` along a
continuous open map `f : Y → X`. -/
def supImage (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f) (hfo : IsOpenMap f)
    (K_Y : CompactExhaustion Y) : CompactExhaustion X where
  toFun n := K_X n ∪ f '' K_Y n
  isCompact' n := (K_X.isCompact n).union ((K_Y.isCompact n).image hfc)
  subset_interior_succ' n := union_subset
    ((K_X.subset_interior_succ n).trans (interior_mono subset_union_left)) <|
    (image_mono (K_Y.subset_interior_succ n)).trans <|
      (hfo _ isOpen_interior).subset_interior_iff.2
        ((image_mono interior_subset).trans subset_union_right)
  iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K_X.iUnion_eq

@[simp]
lemma supImage_apply (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f)
    (hfo : IsOpenMap f) (K_Y : CompactExhaustion Y) (n : ℕ) :
    K_X.supImage hfc hfo K_Y n = K_X n ∪ f '' K_Y n := (rfl)

lemma subset_supImage_left (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f)
    (hfo : IsOpenMap f) (K_Y : CompactExhaustion Y) (n : ℕ) :
    K_X n ⊆ K_X.supImage hfc hfo K_Y n := subset_union_left

lemma image_subset_supImage (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f)
    (hfo : IsOpenMap f) (K_Y : CompactExhaustion Y) (n : ℕ) :
    f '' K_Y n ⊆ K_X.supImage hfc hfo K_Y n := subset_union_right

/-- Enlarge a compact exhaustion of `X` by the preimages of a compact exhaustion of `Y` along a
proper map `f : X → Y`. -/
def supPreimage (K_X : CompactExhaustion X) {f : X → Y} (hf : IsProperMap f)
    (K_Y : CompactExhaustion Y) : CompactExhaustion X where
  toFun n := K_X n ∪ f ⁻¹' K_Y n
  isCompact' n := (K_X.isCompact n).union (hf.isCompact_preimage (K_Y.isCompact n))
  subset_interior_succ' n := union_subset
    ((K_X.subset_interior_succ n).trans (interior_mono subset_union_left)) <|
    (preimage_mono (K_Y.subset_interior_succ n)).trans <|
      (isOpen_interior.preimage hf.continuous).subset_interior_iff.2
        ((preimage_mono interior_subset).trans subset_union_right)
  iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K_X.iUnion_eq

@[simp]
lemma supPreimage_apply (K_X : CompactExhaustion X) {f : X → Y} (hf : IsProperMap f)
    (K_Y : CompactExhaustion Y) (n : ℕ) :
    K_X.supPreimage hf K_Y n = K_X n ∪ f ⁻¹' K_Y n := (rfl)

lemma subset_supPreimage_left (K_X : CompactExhaustion X) {f : X → Y} (hf : IsProperMap f)
    (K_Y : CompactExhaustion Y) (n : ℕ) :
    K_X n ⊆ K_X.supPreimage hf K_Y n := subset_union_left

lemma preimage_subset_supPreimage (K_X : CompactExhaustion X) {f : X → Y} (hf : IsProperMap f)
    (K_Y : CompactExhaustion Y) (n : ℕ) :
    f ⁻¹' K_Y n ⊆ K_X.supPreimage hf K_Y n := subset_union_right

end Operations

end CompactExhaustion

namespace TauCeti

section CofinalNeighborhoods

private lemma exists_closure_subset_inter {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (k m : ℕ) : ∃ j, closure (U j) ⊆ U k ∩ U m := by
  obtain ⟨W, hW_open, hAW, hW_cl⟩ := normal_exists_closure_subset hA
    ((hU_open k).inter (hU_open m)) (subset_inter (hAU k) (hAU m))
  exact let ⟨j, hj⟩ := hU_cofinal hW_open hAW; ⟨j, (closure_mono hj).trans hW_cl⟩

/-- Shrinking index sequence extracted from a countable cofinal family `U` of open neighbourhoods
of a closed set `A` in a normal space. -/
noncomputable def cofinalNhdsIndex {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (exists_closure_subset_inter hA hU_open hAU hU_cofinal
      (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) (n + 1)).choose

@[simp]
lemma cofinalNhdsIndex_zero {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) :
    cofinalNhdsIndex hA hU_open hAU hU_cofinal 0 = 0 := (rfl)

lemma closure_apply_cofinalNhdsIndex_succ_subset_inter {X : Type*} [TopologicalSpace X]
    [NormalSpace X] {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    closure (U (cofinalNhdsIndex hA hU_open hAU hU_cofinal (n + 1))) ⊆
      U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) ∩ U (n + 1) :=
  (exists_closure_subset_inter hA hU_open hAU hU_cofinal _ (n + 1)).choose_spec

lemma apply_cofinalNhdsIndex_subset {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) :
    ∀ n, U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) ⊆ U n
  | 0 => Subset.rfl
  | n + 1 => subset_closure.trans
      ((closure_apply_cofinalNhdsIndex_succ_subset_inter hA hU_open hAU hU_cofinal n).trans
        inter_subset_right)

end CofinalNeighborhoods

end TauCeti

namespace CompactExhaustion

section CofinalNeighborhoods

private lemma image_subtypeVal_preimage_compl {X : Type*} {A B : Set X} (hAB : A ⊆ B) :
    (Subtype.val : (Aᶜ : Set X) → X) '' (Subtype.val ⁻¹' Bᶜ) = Bᶜ :=
  image_preimage_eq_iff.2 (Subtype.range_coe.symm ▸ compl_subset_compl.2 hAB)

/-- **Compact exhaustion of `X \ A` from a countable cofinal open neighbourhood family of `A`.**
In a compact Hausdorff space `X`, a countable cofinal family `U` of open neighbourhoods of a closed
subset `A` yields a shrinking subsequence whose complements form a compact exhaustion of `Aᶜ`. -/
noncomputable def complOfCofinalNhds {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) :
    CompactExhaustion (Aᶜ : Set X) where
  toFun n := Subtype.val ⁻¹' (U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ
  isCompact' n := by
    let φ := TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
      image_subtypeVal_preimage_compl (hAU (φ n))]
    exact (hU_open (φ n)).isClosed_compl.isCompact
  subset_interior_succ' n :=
    (preimage_mono (compl_subset_compl.2 <|
      (TauCeti.closure_apply_cofinalNhdsIndex_succ_subset_inter hA hU_open hAU hU_cofinal n).trans
        inter_subset_left)).trans <|
      (isClosed_closure.isOpen_compl.preimage continuous_subtype_val).subset_interior_iff.2
        (preimage_mono (compl_subset_compl.2 subset_closure))
  iUnion_eq' := eq_univ_iff_forall.2 fun y ↦ mem_iUnion.2 <|
    let ⟨n, hn⟩ := hU_cofinal isClosed_singleton.isOpen_compl
      fun _ ha (hy : _ = y.1) ↦ y.2 (hy ▸ ha)
    ⟨n, fun hyU ↦ hn (TauCeti.apply_cofinalNhdsIndex_subset hA hU_open hAU hU_cofinal n hyU) rfl⟩

@[simp]
lemma complOfCofinalNhds_apply {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    complOfCofinalNhds hA hU_open hAU hU_cofinal n =
      Subtype.val ⁻¹' (U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ := (rfl)

lemma image_subtypeVal_complOfCofinalNhds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    (Subtype.val : (Aᶜ : Set X) → X) '' complOfCofinalNhds hA hU_open hAU hU_cofinal n =
      (U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ := by
  rw [complOfCofinalNhds_apply, image_subtypeVal_preimage_compl (hAU _)]

lemma compl_image_subtypeVal_complOfCofinalNhds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    ((Subtype.val : (Aᶜ : Set X) → X) ''
        complOfCofinalNhds hA hU_open hAU hU_cofinal n)ᶜ =
      U (TauCeti.cofinalNhdsIndex hA hU_open hAU hU_cofinal n) := by
  rw [image_subtypeVal_complOfCofinalNhds, compl_compl]

end CofinalNeighborhoods

end CompactExhaustion
