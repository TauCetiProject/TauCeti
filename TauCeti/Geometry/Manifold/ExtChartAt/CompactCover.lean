/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Compact intersections and product-tube chart covers

This file provides two helpers on top of `TauCeti.Geometry.Manifold.ExtChartAt`:

* `TauCeti.isCompact_inter_preimage_extChartAt_symm`: intersecting a compact subset of an extended
  chart target with the preimage of a closed set under the inverse chart gives a compact set.
* `TauCeti.exists_finite_precompact_chart_cover_of_isOpen_prod`: finite open chart covers with
  compact coordinate bounds refining a product-tube open neighborhood `C ×ˢ K ⊆ W` and an open
  neighborhood `K ⊆ V`.
-/

public section

open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- For a compact subset `S` of an extended chart target and a closed subset `K` of the manifold,
the points of `S` mapped into `K` by the inverse chart form a compact set. -/
theorem isCompact_inter_preimage_extChartAt_symm (α : M) {S : Set E} {K : Set M}
    (hS : IsCompact S) (hSt : S ⊆ (extChartAt I α).target) (hK : IsClosed K) :
    IsCompact (S ∩ (extChartAt I α).symm ⁻¹' K) :=
  hS.of_isClosed_subset
    (((continuousOn_extChartAt_symm α).mono hSt).preimage_isClosed_of_isClosed hS.isClosed hK)
    Set.inter_subset_left

/-- Given compact sets `C ⊆ X` and `K ⊆ M` with `C ×ˢ K ⊆ W` for an open set `W ⊆ X × M`, and an
open set `V ⊆ M` containing `K`, there is a finite open chart cover
`u i ⊆ V ∩ (extChartAt I (α i)).source` of `K` with compact coordinate bounds
`b i ⊆ (extChartAt I (α i)).target` such that `(extChartAt I (α i)).symm '' b i ⊆ V` and
`C ×ˢ ((extChartAt I (α i)).symm '' b i) ⊆ W`. -/
theorem exists_finite_precompact_chart_cover_of_isOpen_prod [LocallyCompactSpace H]
    {X : Type*} [TopologicalSpace X] {C : Set X} {K : Set M} {W : Set (X × M)} {V : Set M}
    (hC : IsCompact C) (hK : IsCompact K) (hW : IsOpen W) (hCKW : C ×ˢ K ⊆ W)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ (n : ℕ) (α : Fin n → M) (u : Fin n → Set M) (b : Fin n → Set E),
      (∀ i, IsOpen (u i) ∧ u i ⊆ V ∧ u i ⊆ (extChartAt I (α i)).source ∧
        IsCompact (b i) ∧ b i ⊆ (extChartAt I (α i)).target ∧
        (extChartAt I (α i)).symm '' b i ⊆ V ∧
        C ×ˢ ((extChartAt I (α i)).symm '' b i) ⊆ W ∧
        (extChartAt I (α i)) '' u i ⊆ b i) ∧
      K ⊆ ⋃ i, u i := by
  obtain ⟨U₁, U₂, -, hU₂, hCU₁, hKU₂, hprod⟩ := generalized_tube_lemma hC hK hW hCKW
  obtain ⟨n, -, α, u, b, hcov, hsK⟩ := exists_finite_precompact_chart_cover_of_isOpen_cover (I := I)
    hK (V := fun _ : Unit ↦ U₂ ∩ V) (fun _ ↦ hU₂.inter hV)
    fun x hx ↦ Set.mem_iUnion.2 ⟨(), hKU₂ hx, hKV hx⟩
  refine ⟨n, α, u, b, fun i ↦ ?_, hsK⟩
  have hi := hcov i
  refine ⟨hi.2.1, hi.2.2.1.trans Set.inter_subset_right, hi.2.2.2.1, hi.2.2.2.2.1,
    hi.2.2.2.2.2.1, ?_, ?_, hi.2.2.2.2.2.2.2⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hi.2.2.2.2.2.2.1 hy).2
  · rintro ⟨p, _⟩ ⟨hp, y, hy, rfl⟩
    exact hprod ⟨hCU₁ hp, (hi.2.2.2.2.2.2.1 hy).1⟩

end TauCeti
