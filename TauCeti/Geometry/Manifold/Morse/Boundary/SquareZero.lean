/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Compactification
import TauCeti.Geometry.Manifold.Boundary.OneDimensional
import TauCeti.Geometry.Manifold.Morse.Gluing.Broken

/-!
# The mod-two Morse boundary squares to zero

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. This file proves that the mod-two Morse
boundary `IsMorseSmale.morseBoundary` satisfies `∂ ∘ ∂ = 0`.

By `IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff`, this amounts to showing that
between any two critical points `p` and `r` there is an even number of broken index-two
trajectories. Record trajectories from `p` to `r` by their points on two levels `c₁` and `c₂`
separating the intermediate critical values, as in
`TauCeti.Geometry.Manifold.Morse.Boundary.Compactification`. The closure of the unbroken pairs in
`M × M` is a compact Hausdorff space, and:

* each of its points is an unbroken or a broken pair
  (`IsMorseSmale.closure_morseTrajectoryPairs_subset`), and there are finitely many broken pairs;
* each unbroken pair has a neighbourhood homeomorphic to an open subset of `ℝ`
  (`IsMorseSmale.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs`);
* each broken pair has a neighbourhood homeomorphic to a half-open interval `[0, δ)`, with the
  broken pair at `0`, by the gluing theorem
  `IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`.

So the broken pairs are the endpoints of a compact one-dimensional manifold with boundary, and
there is an even number of them (`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`). They are
as many as the broken trajectories (`ncard_morseBrokenTrajectoryPairs`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `even_ncard_morseBrokenTrajectoryPairs`: on two separating levels, there is an even number of
  broken index-two trajectory pairs.
* `even_ncard_morseBrokenTrajectorySet`: between any two critical points there is an even number
  of broken index-two trajectories.
* `morseBoundary_comp_morseBoundary`, `morseBoundary_morseBoundary`: the mod-two Morse boundary
  squares to zero.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (the compactified space of index-two trajectories as a manifold with boundary) and
  Chapter 4 (the proof that `∂ ∘ ∂ = 0`).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Broken pairs are endpoints of the compactified space.** Each broken pair `w` has a
neighbourhood in the closure of the unbroken pairs homeomorphic to a half-open interval `[0, ε)`,
with `w` at `0`. -/
private theorem exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁)
    {w : M × M} (hw : w ∈ closure (hX.morseTrajectoryPairs p r c₁ c₂))
    (hwB : w ∈ hX.morseBrokenTrajectoryPairs p r c₁ c₂) :
    ∃ N ∈ 𝓝 (⟨w, hw⟩ : closure (hX.morseTrajectoryPairs p r c₁ c₂)),
      ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N), (e ⟨0, left_mem_Ico.2 hε⟩ :
        closure (hX.morseTrajectoryPairs p r c₁ c₂)) = ⟨w, hw⟩ := by
  set S := hX.morseTrajectoryPairs p r c₁ c₂
  set B := hX.morseBrokenTrajectoryPairs p r c₁ c₂
  obtain ⟨a₁, a₂⟩ := w
  obtain ⟨q, hq, hpq, hqr, ha₁, hac₁, ha₂, hac₂⟩ := hX.mem_morseBrokenTrajectoryPairs.1 hwB
  -- The gluing theorem gives a half-open neighbourhood among the unbroken pairs.
  obtain ⟨N, δ, hδ, e, he₀, hNS, hN⟩ :=
    h.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet hf hp hq hr hpq hqr ha₁ ha₂
  simp only [hac₁, hac₂, ← hX.mem_morseTrajectoryPairs, ofPred_mem_eq] at hNS hN
  -- Near `(a₁, a₂)`, the compactified space adds no other broken pair to the unbroken ones.
  have hU : (B \ {(a₁, a₂)})ᶜ ∈ 𝓝 (a₁, a₂) :=
    ((h.finite_morseBrokenTrajectoryPairs hf hp hr c₁ c₂).sdiff.isClosed.isOpen_compl).mem_nhds
      (by simp)
  have hloc : closure S ∩ (B \ {(a₁, a₂)})ᶜ = insert (a₁, a₂) S ∩ (B \ {(a₁, a₂)})ᶜ := by
    refine Subset.antisymm (fun x ⟨hxS, hxU⟩ ↦ ⟨?_, hxU⟩) fun x ⟨hxS, hxU⟩ ↦ ⟨?_, hxU⟩
    · rcases h.closure_morseTrajectoryPairs_subset hf hp hr hind hr₂ h₂₁ h₁p hgap hxS with
        hx | hx
      · exact Or.inr hx
      · exact Or.inl (of_not_not fun hne ↦ hxU ⟨hx, hne⟩)
    · rcases hxS with rfl | hx
      exacts [hw, subset_closure hx]
  rw [← nhdsWithin_eq_nhdsWithin' hU hloc] at hN
  -- Read the neighbourhood inside the compactified space.
  have hNc : N ⊆ range ((↑) : closure S → M × M) := by
    rw [Subtype.range_coe]
    exact hNS.trans (insert_subset hw subset_closure)
  let e' := IsEmbedding.subtypeVal.homeomorphOfSubsetRange hNc
  refine ⟨(↑) ⁻¹' N, ?_, δ, hδ, e.trans e'.symm, ?_⟩
  · rw [mem_nhds_subtype_iff_nhdsWithin, Subtype.image_preimage_coe]
    exact inter_mem self_mem_nhdsWithin hN
  · have := congrArg Subtype.val (e'.apply_symm_apply (e ⟨0, left_mem_Ico.2 hδ⟩))
    rw [IsEmbedding.homeomorphOfSubsetRange_apply_coe, he₀] at this
    exact Subtype.ext this

include h hf in
/-- **Broken trajectories come in pairs.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every critical value strictly
between `f r` and `f p` from `f r` and `f p`. Then the pairs of points on these levels of the
trajectories from `p` to `r` broken once are even in number: they are the endpoints of the
compactified space of index-two trajectories, a compact one-dimensional manifold with boundary. -/
theorem even_ncard_morseBrokenTrajectoryPairs {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    Even (hX.morseBrokenTrajectoryPairs p r c₁ c₂).ncard := by
  set S := hX.morseTrajectoryPairs p r c₁ c₂
  set B := hX.morseBrokenTrajectoryPairs p r c₁ c₂
  -- Every broken pair is a limit of unbroken ones.
  have hBS : B ⊆ closure S := by
    rintro ⟨a₁, a₂⟩ hw
    obtain ⟨q, hq, hpq, hqr, ha₁, hac₁, ha₂, hac₂⟩ := hX.mem_morseBrokenTrajectoryPairs.1 hw
    have := h.mem_closure_of_mem_unstableSet_inter_stableSet hf hp hq hr hpq hqr ha₁ ha₂
    simpa only [hac₁, hac₂, ← hX.mem_morseTrajectoryPairs, ofPred_mem_eq] using this
  have : CompactSpace (closure S) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  -- In the compactified space, the broken pairs are the points with a half-open model.
  have heven : Even ((↑) ⁻¹' B : Set (closure S)).ncard := by
    refine even_ncard_of_forall_exists_homeomorph_Ico (F := ℝ) (Module.finrank_self ℝ)
      (fun w hw ↦ h.exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs hf hp hr hind hr₂
        h₂₁ h₁p hgap w.2 hw) fun w hw ↦ ?_
    exact h.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs hf hp hr hind hr₂ h₂₁ h₁p hgap w.2
      ((h.closure_morseTrajectoryPairs_subset hf hp hr hind hr₂ h₂₁ h₁p hgap w.2).resolve_right hw)
  rwa [ncard_preimage_of_injective_subset_range Subtype.val_injective
    (by rwa [Subtype.range_coe])] at heven

include h hf in
/-- **Broken trajectories come in pairs.** Between any two critical points of a Morse function
on a compact manifold, with a Morse–Smale adapted pseudo-gradient, there is an even number of
broken index-two trajectories. -/
theorem even_ncard_morseBrokenTrajectorySet (p r : criticalPoints 𝓘(ℝ, E) f) :
    Even (hX.morseBrokenTrajectorySet p r).ncard := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  by_cases hpr : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2 ∧
    f r < f p
  · obtain ⟨c₁, c₂, hr₂, h₂₁, h₁p, hgap⟩ := hf.exists_lt_lt_forall_mem_Ioo hpr.2
    rw [← hX.ncard_morseBrokenTrajectoryPairs hdf p r hr₂ h₁p hgap]
    exact h.even_ncard_morseBrokenTrajectoryPairs hf
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2) (mem_criticalPoints_iff_mfderiv_eq_zero.1 r.2)
      hpr.1 hr₂ h₂₁ h₁p hgap
  · -- Otherwise there is no broken trajectory: the index drops by one and `f` drops strictly
    -- along each component.
    suffices hX.morseBrokenTrajectorySet p r = ∅ by simp [this]
    refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := hX.mem_morseBrokenTrajectorySet.1 hx
    refine hpr ⟨?_, ?_⟩
    · omega
    · have hpq' : (p : M) ≠ x.1 := fun he ↦ by rw [he] at hpq; omega
      have hqr' : (x.1 : M) ≠ r := fun he ↦ by rw [he] at hqr; omega
      exact (hX.value_lt_of_mem_morseTrajectorySlice hdf hqr' hz₂).trans
        (hX.value_lt_of_mem_morseTrajectorySlice hdf hpq' hz₁)

include h hf in
/-- **The mod-two Morse boundary squares to zero.** For a Morse function on a compact manifold
and a Morse–Smale adapted pseudo-gradient, `∂ ∘ ∂ = 0`. -/
theorem morseBoundary_comp_morseBoundary : h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 :=
  (h.morseBoundary_comp_morseBoundary_eq_zero_iff hf).2 (h.even_ncard_morseBrokenTrajectorySet hf)

include h hf in
/-- **The boundary of a boundary is zero.** The pointwise form of
`morseBoundary_comp_morseBoundary`: every chain `c` satisfies `∂ (∂ c) = 0`. -/
@[simp]
theorem morseBoundary_morseBoundary (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    h.morseBoundary hf (h.morseBoundary hf c) = 0 :=
  LinearMap.congr_fun (h.morseBoundary_comp_morseBoundary hf) c

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
