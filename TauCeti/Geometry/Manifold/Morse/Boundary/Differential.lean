/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Gluing
import TauCeti.Geometry.Manifold.Boundary.OneDimensional

/-!
# The mod-two Morse boundary squares to zero

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
field adapted to `f` satisfying the Morse–Smale condition. This file proves that the mod-two Morse
boundary `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary` satisfies `∂ ∘ ∂ = 0`.

By `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff`,
this amounts to showing that, between critical points `p` and `r` with `ind p = ind r + 2`, the
broken trajectories are even in number. Record the trajectories from `p` to `r` by their points
on two levels `c₁` and `c₂` separating the intermediate critical values, as in
`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPairs`. The closure of the unbroken pairs in
`M × M` is a compact Hausdorff space in which

* every unbroken pair has a neighbourhood homeomorphic to an open subset of `ℝ`
  (`IsMorseSmale.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs`), and
* every broken pair has a neighbourhood homeomorphic to a half-open interval `[0, δ)`, sending
  `0` to it (`IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`, together
  with the finiteness of the broken pairs, which isolates each of them from the others).

So the broken pairs are the endpoints of a compact one-dimensional manifold with boundary, and
there is an even number of them (`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `even_ncard_morseBrokenTrajectoryPairs`: the broken index-two trajectories recorded on two
  levels are even in number.
* `even_ncard_morseBrokenTrajectorySet`: between any two critical points the broken index-two
  trajectories are even in number.
* `morseBoundary_comp_morseBoundary`: the mod-two Morse boundary squares to zero.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (the compactified space of index-two trajectories is a compact manifold with boundary
  whose boundary consists of the broken trajectories) and Chapter 4 (`∂ ∘ ∂ = 0`).
-/

public section

open Set Topology
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
/-- **A broken trajectory is an endpoint of the compactified space.** Under the hypotheses of
`closure_morseTrajectoryPairs`, every broken trajectory pair `w` has a neighbourhood in the
closure of the unbroken pairs homeomorphic to a half-open interval `[0, δ)`, with `w`
corresponding to `0`. -/
theorem exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁)
    {w : M × M} (hw : w ∈ closure (hX.morseTrajectoryPairs p r c₁ c₂))
    (hwB : w ∈ hX.morseBrokenTrajectoryPairs p r c₁ c₂) :
    ∃ N ∈ 𝓝 (⟨w, hw⟩ : closure (hX.morseTrajectoryPairs p r c₁ c₂)),
      ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
        (e ⟨0, left_mem_Ico.2 hδ⟩ : closure (hX.morseTrajectoryPairs p r c₁ c₂)) = ⟨w, hw⟩ := by
  set S := hX.morseTrajectoryPairs p r c₁ c₂ with hSdef
  set B := hX.morseBrokenTrajectoryPairs p r c₁ c₂
  obtain ⟨a₁, a₂⟩ := w
  obtain ⟨q, hq, hpq, hqr, ha₁, hc₁, ha₂, hc₂⟩ := hX.mem_morseBrokenTrajectoryPairs.1 hwB
  simp only at ha₁ hc₁ ha₂ hc₂
  obtain ⟨N, δ, hδ, e, he₀, hN, hNw⟩ :=
    h.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet hf hp hq hr hpq hqr ha₁ ha₂
  -- The unbroken trajectories in the gluing theorem are those recorded on the levels `c₁, c₂`.
  have hS : {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} = S := by
    ext w
    rw [hSdef, mem_morseTrajectoryPairs, mem_ofPred_eq, hc₁, hc₂]
  rw [hS] at hN hNw
  -- Near `(a₁, a₂)`, the compactified space adds no broken pair other than `(a₁, a₂)`.
  have hloc : 𝓝[closure S] (a₁, a₂) ≤ 𝓝[insert (a₁, a₂) S] (a₁, a₂) := by
    have hfar : (B \ {(a₁, a₂)})ᶜ ∈ 𝓝 (a₁, a₂) :=
      ((h.finite_morseBrokenTrajectoryPairs hf hp hr c₁ c₂).sdiff.isClosed.isOpen_compl).mem_nhds
        (by simp)
    refine nhdsWithin_le_of_mem (mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨_, hfar, fun x ⟨hxB, hxK⟩ ↦ ?_⟩)
    rcases h.closure_morseTrajectoryPairs_subset hf hp hr hind hr₂ h₂₁ h₁p hgap hxK with hx | hx
    · exact Or.inr hx
    · exact Or.inl (not_not.1 fun hne ↦ hxB ⟨hx, hne⟩)
  -- The half-open arc, viewed in the compactified space.
  let g : Ico (0 : ℝ) δ → closure S := codRestrict (Subtype.val ∘ e) (closure S) fun s ↦
    insert_subset hw subset_closure (hN (e s).2)
  have hg : IsEmbedding g := (IsEmbedding.subtypeVal.comp e.isEmbedding).codRestrict _ _
  have hrange : (↑) '' range g = N := by
    rw [← range_comp]
    exact (range_comp Subtype.val e).trans (by rw [e.range_coe, image_univ, Subtype.range_coe])
  refine ⟨range g, mem_nhds_subtype_iff_nhdsWithin.2 (hrange ▸ hloc hNw), δ, hδ, hg.toHomeomorph,
    Subtype.ext he₀⟩

include h hf in
/-- **Broken trajectories come in pairs.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every critical value
strictly between `f r` and `f p` from `f r` and `f p`. Then the trajectories from `p` to `r`
broken once, recorded by their points on these levels, are even in number. -/
theorem even_ncard_morseBrokenTrajectoryPairs {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    Even (hX.morseBrokenTrajectoryPairs p r c₁ c₂).ncard := by
  set S := hX.morseTrajectoryPairs p r c₁ c₂
  have : CompactSpace (closure S) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  -- Count the broken pairs inside the compactified space.
  rw [← ncard_preimage_of_injective_subset_range (f := ((↑) : closure S → M × M))
    Subtype.val_injective
    (by rw [Subtype.range_coe]; exact h.morseBrokenTrajectoryPairs_subset_closure hf p r c₁ c₂)]
  refine even_ncard_of_forall_exists_homeomorph_Ico (F := ℝ) (Module.finrank_self ℝ)
    (fun w hw ↦ h.exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs hf hp hr hind hr₂ h₂₁
      h₁p hgap w.2 hw) fun w hw ↦ ?_
  exact h.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs hf hp hr hind hr₂ h₂₁ h₁p hgap w.2
    ((h.closure_morseTrajectoryPairs_subset hf hp hr hind hr₂ h₂₁ h₁p hgap w.2).resolve_right hw)

include h hf in
/-- **Broken index-two trajectories come in pairs.** Between any two critical points `p` and `r`,
the broken index-two trajectories `morseBrokenTrajectorySet p r` are even in number. -/
theorem even_ncard_morseBrokenTrajectorySet (p r : criticalPoints 𝓘(ℝ, E) f) :
    Even (hX.morseBrokenTrajectorySet p r).ncard := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  rcases (hX.morseBrokenTrajectorySet p r).eq_empty_or_nonempty with h0 | ⟨⟨q, z₁, z₂⟩, hx⟩
  · simp [h0]
  -- A broken trajectory forces `ind p = ind r + 2` and `f r < f p`.
  obtain ⟨hpq, hqr, hz₁, hz₂⟩ := hX.mem_morseBrokenTrajectorySet.1 hx
  have hne {a b : M} (h : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1) :
      a ≠ b := by
    rintro rfl; omega
  have hlt : f r < f p :=
    (hX.value_lt_of_mem_morseTrajectorySlice hdf (hne hqr) hz₂).trans
      (hX.value_lt_of_mem_morseTrajectorySlice hdf (hne hpq) hz₁)
  obtain ⟨c₁, c₂, hr₂, h₂₁, h₁p, hgap⟩ := hf.exists_lt_lt_forall_mem_Ioo hlt
  rw [← hX.ncard_morseBrokenTrajectoryPairs hdf p r hr₂ h₁p hgap]
  exact h.even_ncard_morseBrokenTrajectoryPairs hf (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 r.2) (by omega) hr₂ h₂₁ h₁p hgap

/-- **The mod-two Morse boundary squares to zero.** For a Morse function on a compact
boundaryless manifold and a Morse–Smale adapted pseudo-gradient, `∂ ∘ ∂ = 0`. -/
theorem morseBoundary_comp_morseBoundary : h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 :=
  (h.morseBoundary_comp_morseBoundary_eq_zero_iff hf).2 (h.even_ncard_morseBrokenTrajectorySet hf)

/-- **The mod-two Morse boundary squares to zero**, applied to a chain. -/
@[simp]
theorem morseBoundary_morseBoundary (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    h.morseBoundary hf (h.morseBoundary hf c) = 0 :=
  LinearMap.congr_fun (h.morseBoundary_comp_morseBoundary hf) c

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
