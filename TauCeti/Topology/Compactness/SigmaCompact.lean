/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
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
* `CompactExhaustion.sup` (`⊔`) and `CompactExhaustion.supImage`: pointwise union of compact
  exhaustions and enlargement along a continuous open map.
* `CompactExhaustion.complOfCofinalNhds`: in a compact Hausdorff space `X`, a countable cofinal
  family of open neighbourhoods of a closed subset `A` yields a compact exhaustion of `Aᶜ`.
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
  exists_compact_mem_nhds x :=
    let ⟨n, hn⟩ := K.exists_mem_nhds x
    ⟨K n, K.isCompact n, hn⟩

/-- Pointwise union of two compact exhaustions of the same space. -/
def sup (K₁ K₂ : CompactExhaustion X) : CompactExhaustion X where
  toFun n := K₁ n ∪ K₂ n
  isCompact' n := (K₁.isCompact n).union (K₂.isCompact n)
  subset_interior_succ' n :=
    union_subset
      ((K₁.subset_interior_succ n).trans (interior_mono subset_union_left))
      ((K₂.subset_interior_succ n).trans (interior_mono subset_union_right))
  iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K₁.iUnion_eq

instance instMax : Max (CompactExhaustion X) := ⟨sup⟩

@[simp]
lemma sup_apply (K₁ K₂ : CompactExhaustion X) (n : ℕ) :
    (K₁ ⊔ K₂) n = K₁ n ∪ K₂ n :=
  (rfl)

lemma subset_sup_left (K₁ K₂ : CompactExhaustion X) (n : ℕ) :
    K₁ n ⊆ (K₁ ⊔ K₂) n :=
  subset_union_left

lemma subset_sup_right (K₁ K₂ : CompactExhaustion X) (n : ℕ) :
    K₂ n ⊆ (K₁ ⊔ K₂) n :=
  subset_union_right

/-- Enlarge a compact exhaustion of `X` by the images of a compact exhaustion of `Y` along a
continuous open map `f : Y → X`. Openness of `f` ensures `f '' K_Y n ⊆ interior (f '' K_Y (n + 1))`.
-/
def supImage (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f) (hfo : IsOpenMap f)
    (K_Y : CompactExhaustion Y) : CompactExhaustion X where
  toFun n := K_X n ∪ f '' K_Y n
  isCompact' n := (K_X.isCompact n).union ((K_Y.isCompact n).image hfc)
  subset_interior_succ' n := by
    refine union_subset ((K_X.subset_interior_succ n).trans (interior_mono subset_union_left)) ?_
    calc f '' K_Y n
      _ ⊆ f '' interior (K_Y (n + 1)) := image_mono (K_Y.subset_interior_succ n)
      _ ⊆ interior (K_X (n + 1) ∪ f '' K_Y (n + 1)) :=
        (hfo _ isOpen_interior).subset_interior_iff.2
          ((image_mono interior_subset).trans subset_union_right)
  iUnion_eq' := eq_univ_of_subset (iUnion_mono fun _ ↦ subset_union_left) K_X.iUnion_eq

@[simp]
lemma supImage_apply (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f)
    (hfo : IsOpenMap f) (K_Y : CompactExhaustion Y) (n : ℕ) :
    K_X.supImage hfc hfo K_Y n = K_X n ∪ f '' K_Y n :=
  (rfl)

lemma subset_supImage_left (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f)
    (hfo : IsOpenMap f) (K_Y : CompactExhaustion Y) (n : ℕ) :
    K_X n ⊆ K_X.supImage hfc hfo K_Y n :=
  subset_union_left

lemma image_subset_supImage (K_X : CompactExhaustion X) {f : Y → X} (hfc : Continuous f)
    (hfo : IsOpenMap f) (K_Y : CompactExhaustion Y) (n : ℕ) :
    f '' K_Y n ⊆ K_X.supImage hfc hfo K_Y n :=
  subset_union_right

end Operations

section CofinalNeighborhoods

private lemma exists_closure_subset_inter {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (k m : ℕ) :
    ∃ j, closure (U j) ⊆ U k ∩ U m := by
  obtain ⟨W, hW_open, hAW, hW_cl⟩ := normal_exists_closure_subset hA
    ((hU_open k).inter (hU_open m)) (subset_inter (hAU k) (hAU m))
  obtain ⟨j, hj⟩ := hU_cofinal hW_open hAW
  exact ⟨j, (closure_mono hj).trans hW_cl⟩

/-- Shrinking index sequence extracted from a countable cofinal family `U` of open neighbourhoods
of a closed set `A` in a normal space, satisfying
`closure (U (cofinalNhdsIndex ... (n + 1))) ⊆ U (cofinalNhdsIndex ... n) ∩ U (n + 1)`. -/
noncomputable def cofinalNhdsIndex {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) :
    ℕ → ℕ
  | 0 => 0
  | n + 1 => (exists_closure_subset_inter hA hU_open hAU hU_cofinal
      (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) (n + 1)).choose

lemma closure_cofinalNhdsIndex_succ_subset {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    closure (U (cofinalNhdsIndex hA hU_open hAU hU_cofinal (n + 1))) ⊆
      U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) ∩ U (n + 1) :=
  (exists_closure_subset_inter hA hU_open hAU hU_cofinal
    (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) (n + 1)).choose_spec

lemma cofinalNhdsIndex_subset_self {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n))
    (hAU : ∀ n, A ⊆ U n) (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) ⊆ U n := by
  cases n with
  | zero => exact Subset.rfl
  | succ n =>
    exact subset_closure.trans
      ((closure_cofinalNhdsIndex_succ_subset hA hU_open hAU hU_cofinal n).trans inter_subset_right)

/-- **Compact exhaustion of `X \ A` from a countable cofinal open neighbourhood family of `A`.**
In a compact Hausdorff (hence normal) space `X`, a countable cofinal family `U` of open
neighbourhoods of a closed subset `A` admits a shrinking subsequence `U (φ n)` whose complements
`(U (φ n))ᶜ` form a compact exhaustion of `Aᶜ`. -/
noncomputable def complOfCofinalNhds {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A : Set X} (hA : IsClosed A) {U : ℕ → Set X}
    (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) :
    CompactExhaustion (Aᶜ : Set X) where
  toFun n := Subtype.val ⁻¹' (U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n))ᶜ
  isCompact' n := by
    let φ := cofinalNhdsIndex hA hU_open hAU hU_cofinal
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
    rw [image_preimage_eq_iff.2]
    · exact (hU_open (φ n)).isClosed_compl.isCompact
    · rw [Subtype.range_coe]
      exact compl_subset_compl.2 (hAU (φ n))
  subset_interior_succ' n := by
    let φ := cofinalNhdsIndex hA hU_open hAU hU_cofinal
    have hcl : closure (U (φ (n + 1))) ⊆ U (φ n) :=
      (closure_cofinalNhdsIndex_succ_subset hA hU_open hAU hU_cofinal n).trans inter_subset_left
    exact (preimage_mono (compl_subset_compl.2 hcl)).trans <|
      (isClosed_closure.isOpen_compl.preimage continuous_subtype_val).subset_interior_iff.2
        (preimage_mono (compl_subset_compl.2 subset_closure))
  iUnion_eq' := by
    refine eq_univ_iff_forall.2 fun y ↦ mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := hU_cofinal isClosed_singleton.isOpen_compl
      fun a ha (hy : a = y.1) ↦ y.2 (hy ▸ ha)
    exact ⟨n, fun hyU ↦ hn (cofinalNhdsIndex_subset_self hA hU_open hAU hU_cofinal n hyU) rfl⟩

@[simp]
lemma compl_image_subtypeVal_complOfCofinalNhds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : Set X} (hA : IsClosed A) {U : ℕ → Set X}
    (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W) (n : ℕ) :
    ((Subtype.val : (Aᶜ : Set X) → X) ''
        complOfCofinalNhds hA hU_open hAU hU_cofinal n)ᶜ =
      U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) := by
  let φ := cofinalNhdsIndex hA hU_open hAU hU_cofinal
  have himg : (Subtype.val : (Aᶜ : Set X) → X) '' (Subtype.val ⁻¹' (U (φ n))ᶜ) = (U (φ n))ᶜ := by
    rw [image_preimage_eq_iff, Subtype.range_coe]
    exact compl_subset_compl.2 (hAU (φ n))
  exact (congrArg compl himg).trans (compl_compl (U (φ n)))

end CofinalNeighborhoods

end CompactExhaustion
