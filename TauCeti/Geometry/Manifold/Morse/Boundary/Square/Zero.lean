/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Compactification
import TauCeti.Geometry.Manifold.Boundary.OneDimensional
import TauCeti.Geometry.Manifold.Morse.Boundary.Gluing

/-!
# The mod-two Morse boundary squares to zero

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. This file proves that the mod-two Morse
boundary `∂` of `TauCeti.Geometry.Manifold.Morse.Boundary.Basic` satisfies `∂ ∘ ∂ = 0`, so that
the critical points of `f` with this boundary form a chain complex over `ZMod 2`.

By `IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff`, it suffices that between any two
critical points `p` and `r` the broken index-two trajectories are even in number. Record the
trajectories from `p` to `r` by their points on two levels `c₁` and `c₂` separating the
intermediate critical values, as in `TauCeti.Geometry.Manifold.Morse.Boundary.Compactification`.
The closure of the unbroken trajectory pairs in `M × M` is compact, it consists of the unbroken
pairs and finitely many broken ones, and it is locally homeomorphic to an open subset of `ℝ` at the
unbroken pairs. The gluing theorem
`IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet` gives every broken pair a
neighbourhood among the unbroken pairs homeomorphic to a half-open interval `[0, δ)`. Since the
other broken pairs are isolated, this is a neighbourhood in the compactified space
(`IsMorseSmale.exists_nhds_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs`). The compactified
space is therefore a compact one-dimensional manifold whose boundary is the set of broken
trajectories, which has an even number of points by
`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `exists_nhds_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs`: a broken trajectory has a
  neighbourhood in the compactified space of index-two trajectories homeomorphic to `[0, δ)`.
* `even_ncard_morseBrokenTrajectorySet`: the broken index-two trajectories between two critical
  points are even in number.
* `morseBoundary_comp_morseBoundary_eq_zero`, `morseBoundary_morseBoundary`: the mod-two Morse
  boundary squares to zero.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (the compactified space of index-two trajectories is a compact manifold with boundary
  whose boundary is the set of broken trajectories) and Chapter 4 (`∂ ∘ ∂ = 0`).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Boundary charts of the compactified space of index-two trajectories.** Let the levels
`f r < c₂ < c₁ < f p` separate every critical value strictly between `f r` and `f p` from `f r`
and `f p`. Then every broken trajectory pair in the closure of the trajectory pairs from `p` to
`r` on the levels `c₁` and `c₂` has a neighbourhood in that closure homeomorphic to a half-open
interval `[0, δ)`, with the broken pair corresponding to `0`. -/
theorem exists_nhds_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs {p r : M} {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁)
    {x : closure (hX.morseTrajectoryPairs p r c₁ c₂)}
    (hx : (x : M × M) ∈ hX.morseBrokenTrajectoryPairs p r c₁ c₂) :
    ∃ N ∈ 𝓝 x, ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : closure (hX.morseTrajectoryPairs p r c₁ c₂)) = x := by
  obtain ⟨⟨a₁, a₂⟩, ha⟩ := x
  dsimp only at hx
  obtain ⟨q, hq, hpq, hqr, ha₁, rfl, ha₂, rfl⟩ := hX.mem_morseBrokenTrajectoryPairs.1 hx
  set P := hX.morseTrajectoryPairs p r (f a₁) (f a₂)
  have hfin := h.finite_morseBrokenTrajectoryPairs hf (p := p) (r := r) (f a₁) (f a₂)
  have hcl := h.closure_morseTrajectoryPairs_subset hf (by omega) hr₂ h₂₁ h₁p hgap
  -- The gluing theorem gives a half-open arc `N` in `M × M` among the unbroken pairs.
  obtain ⟨N, δ, hδ, e, he₀, hNS, hNnhds⟩ :=
    h.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet hf hpq hqr ha₁ ha₂
  have hS : {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} = P :=
    Set.ext fun _ ↦ hX.mem_morseTrajectoryPairs.symm
  rw [hS] at hNS hNnhds
  have hNcl : N ⊆ closure P := hNS.trans (insert_subset_iff.2 ⟨ha, subset_closure⟩)
  -- Near `(a₁, a₂)` the compactified space has no other broken pair, so `N` is a neighbourhood
  -- of `(a₁, a₂)` in the compactified space.
  have hV : (hX.morseBrokenTrajectoryPairs p r (f a₁) (f a₂) \ {(a₁, a₂)})ᶜ ∈ 𝓝 (a₁, a₂) :=
    (hfin.sdiff.isClosed.isOpen_compl).mem_nhds fun hmem ↦ hmem.2 rfl
  have hN : N ∈ 𝓝[closure P] (a₁, a₂) := by
    rw [← nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hV)]
    refine nhdsWithin_mono _ (fun w hw ↦ ?_) hNnhds
    rcases hcl hw.1 with hwP | hwB
    · exact mem_insert_of_mem _ hwP
    · exact mem_insert_iff.2 (Or.inl (by simpa [hwB] using hw.2))
  -- Lift the arc to the compactified space.
  let g : Ico (0 : ℝ) δ → closure P := fun s ↦ ⟨e s, hNcl (e s).2⟩
  have hg : IsEmbedding g := by
    have he : IsEmbedding fun s ↦ (e s : M × M) := IsEmbedding.subtypeVal.comp e.isEmbedding
    exact IsEmbedding.subtypeVal.of_comp_iff.1 he
  refine ⟨range g, mem_of_superset (preimage_coe_mem_nhds_subtype.2 hN) ?_, δ, hδ,
    hg.toHomeomorph, Subtype.ext he₀⟩
  rintro w (hw : (w : M × M) ∈ N)
  exact ⟨e.symm ⟨w, hw⟩, Subtype.ext (by simp [g])⟩

include h hf in
/-- **Broken trajectories come in pairs.** Under the Morse–Smale condition, the number of broken
index-two trajectories between two critical points is even. They are the endpoints of the
compactified space of index-two trajectories, a compact space that is locally homeomorphic to a
half-open interval at them and to an open subset of `ℝ` elsewhere. -/
theorem even_ncard_morseBrokenTrajectorySet (p r : criticalPoints 𝓘(ℝ, E) f) :
    Even (hX.morseBrokenTrajectorySet p r).ncard := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  rcases (hX.morseBrokenTrajectorySet p r).eq_empty_or_nonempty with hempty | ⟨⟨q, z₁, z₂⟩, hx⟩
  · simp [hempty]
  -- A broken trajectory forces `ind p = ind r + 2` and `f r < f p`.
  obtain ⟨hpq, hqr, hz₁, hz₂⟩ := hX.mem_morseBrokenTrajectorySet.1 hx
  have hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2 := by omega
  have hrp : f r < f p :=
    (hX.value_lt_of_mem_morseTrajectorySlice hdf (fun he ↦ by rw [he] at hqr; omega) hz₂).trans
      (hX.value_lt_of_mem_morseTrajectorySlice hdf (fun he ↦ by rw [he] at hpq; omega) hz₁)
  obtain ⟨c₁, c₂, hr₂, h₂₁, h₁p, hgap⟩ := hf.exists_lt_lt_forall_mem_Ioo hrp
  rw [← hX.ncard_morseBrokenTrajectoryPairs hdf p r hr₂ h₁p hgap]
  set P := hX.morseTrajectoryPairs p r c₁ c₂
  -- Every broken pair is a limit of unbroken ones.
  rw [← ncard_preimage_of_injective_subset_range Subtype.val_injective
    ((h.morseBrokenTrajectoryPairs_subset_closure hf p r c₁ c₂).trans
      Subtype.range_coe.superset)]
  -- The compactified space is compact and locally a half-line at the broken pairs.
  have : CompactSpace (closure P) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  refine even_ncard_of_forall_exists_homeomorph_Ico (F := ℝ) (Module.finrank_self ℝ)
    (fun x hx ↦ h.exists_nhds_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs hf hr₂ h₂₁ h₁p
      hgap hx) fun x hx ↦ ?_
  have hxP : (x : M × M) ∈ P :=
    (h.closure_morseTrajectoryPairs_subset hf hind hr₂ h₂₁ h₁p hgap x.2).resolve_right hx
  exact h.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs hf hind hr₂ h₂₁ h₁p hgap x.2 hxP

/-- **`∂² = 0`.** The mod-two Morse boundary of a Morse function on a compact manifold, for a
Morse–Smale adapted pseudo-gradient, squares to zero. -/
theorem morseBoundary_comp_morseBoundary_eq_zero :
    h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 :=
  (h.morseBoundary_comp_morseBoundary_eq_zero_iff hf).2 (h.even_ncard_morseBrokenTrajectorySet hf)

/-- **`∂² = 0`**, applied to a chain. -/
@[simp]
theorem morseBoundary_morseBoundary (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    h.morseBoundary hf (h.morseBoundary hf c) = 0 :=
  LinearMap.congr_fun (h.morseBoundary_comp_morseBoundary_eq_zero hf) c

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
