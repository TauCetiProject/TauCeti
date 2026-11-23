/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Topology.Sets.Opens

/-!
# Compact exhaustions of open sets

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
-/

public section

open Set

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
