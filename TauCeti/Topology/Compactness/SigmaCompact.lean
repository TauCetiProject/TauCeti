/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Compact exhaustions of open sets

A sigma-compact open subset of a locally compact space has a monotone sequence of compact
subsets that exhausts it in the sense that every compact subset lies in one of them
(`IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset`).

Conversely, compact subsets `Kₙ ⊆ U` of the ambient space with `Kₙ ⊆ interior Kₙ₊₁` that cover
a subset `U` trace a compact exhaustion of the subspace `U` (`CompactExhaustion.subtype`); such
a `U` is open (`TauCeti.isOpen_of_subset_interior_succ`).
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
