/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Compactification
public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken

/-!
# Broken index-two trajectories are limits of unbroken ones

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `r` critical points with
`ind p = ind r + 2`. Record trajectories from `p` to `r` by their points on two levels `c₁` and
`c₂`, as in `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPairs`. The compactified space of
these trajectories is the closure of the unbroken pairs in `M × M`, and
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryPairs_subset` shows that it
adds only broken pairs. This file proves the converse: every trajectory broken once, at a
critical point `q` of intermediate index, is a limit of unbroken trajectories. So the points the
compactification adds are exactly the broken trajectories.

The converse is the gluing theorem at a broken trajectory,
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet`,
restated for the sets `morseTrajectoryPairs` and `morseBrokenTrajectoryPairs`.

The half-open gluing arc of `IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`
also moves into the compactified space: since the broken pairs are finite, each of them has a
neighbourhood there homeomorphic to `[0, δ)`, so it is a boundary point.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseBrokenTrajectoryPairs_subset_closure`: every broken pair is a limit of unbroken pairs.
* `closure_morseTrajectoryPairs`: the compactified space is the union of the unbroken and the
  broken pairs.
* `closure_diff_morseTrajectoryPairs`: the points the compactification adds are exactly the
  broken pairs.
* `exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs`: every broken pair has a
  neighbourhood in the compactified space homeomorphic to a half-open interval `[0, δ)`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
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
/-- **Broken trajectories are limits of unbroken ones.** Let `p` and `r` be critical points whose
Morse indices differ by two. Every pair of points on the levels `c₁` and `c₂` of a trajectory from
`p` to `r` broken once, at a critical point of intermediate index, is a limit of pairs of points
on these levels of unbroken trajectories from `p` to `r`. -/
theorem morseBrokenTrajectoryPairs_subset_closure (p r : M) (c₁ c₂ : ℝ) :
    hX.morseBrokenTrajectoryPairs p r c₁ c₂ ⊆ closure (hX.morseTrajectoryPairs p r c₁ c₂) := by
  rintro ⟨y₁, y₂⟩ hw
  simp only [mem_morseBrokenTrajectoryPairs] at hw
  obtain ⟨q, -, hpq, hqr, hy₁, rfl, hy₂, rfl⟩ := hw
  exact closure_mono (fun w hw ↦ hX.mem_morseTrajectoryPairs.2 hw)
    (h.mem_closure_of_mem_unstableSet_inter_stableSet hf hpq hqr hy₁ hy₂)

include h hf in
/-- **The compactified space of index-two trajectories.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every critical value
strictly between `f r` and `f p` from `f r` and `f p`. The closure of the pairs of points on these
levels of trajectories from `p` to `r` consists of these pairs together with the pairs of points
of trajectories broken once, at a critical point of intermediate index. -/
theorem closure_morseTrajectoryPairs {p r : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    closure (hX.morseTrajectoryPairs p r c₁ c₂) =
      hX.morseTrajectoryPairs p r c₁ c₂ ∪ hX.morseBrokenTrajectoryPairs p r c₁ c₂ :=
  (h.closure_morseTrajectoryPairs_subset hf hind hr₂ h₂₁ h₁p hgap).antisymm
    (union_subset subset_closure (h.morseBrokenTrajectoryPairs_subset_closure hf p r c₁ c₂))

include h hf in
/-- **The compactification adds exactly the broken trajectories.** Under the hypotheses of
`closure_morseTrajectoryPairs`, the points of the closure of the unbroken trajectory pairs that are
not unbroken pairs are the broken trajectory pairs. -/
theorem closure_diff_morseTrajectoryPairs {p r : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    closure (hX.morseTrajectoryPairs p r c₁ c₂) \ hX.morseTrajectoryPairs p r c₁ c₂ =
      hX.morseBrokenTrajectoryPairs p r c₁ c₂ := by
  rw [h.closure_morseTrajectoryPairs hf hind hr₂ h₂₁ h₁p hgap, union_sdiff_left,
    (hX.disjoint_morseTrajectoryPairs_morseBrokenTrajectoryPairs p r c₁ c₂).symm.sdiff_eq_left]

include h hf in
/-- **A broken trajectory is an endpoint of the compactified space.** Under the hypotheses of
`closure_morseTrajectoryPairs`, every broken trajectory pair `w` has a neighbourhood in the
closure of the unbroken pairs homeomorphic to a half-open interval `[0, δ)`, with `w`
corresponding to `0`. -/
theorem exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs {p r : M}
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
  obtain ⟨q, -, hpq, hqr, ha₁, hc₁, ha₂, hc₂⟩ := hX.mem_morseBrokenTrajectoryPairs.1 hwB
  simp only at ha₁ hc₁ ha₂ hc₂
  obtain ⟨N, δ, hδ, e, he₀, hN, hNw⟩ :=
    h.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet hf hpq hqr ha₁ ha₂
  -- The unbroken trajectories in the gluing theorem are those recorded on the levels `c₁, c₂`.
  have hS : {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} = S := by
    ext w
    rw [hSdef, mem_morseTrajectoryPairs, mem_ofPred_eq, hc₁, hc₂]
  rw [hS] at hN hNw
  -- Near `(a₁, a₂)`, the compactified space adds no broken pair other than `(a₁, a₂)`.
  have hloc : 𝓝[closure S] (a₁, a₂) ≤ 𝓝[insert (a₁, a₂) S] (a₁, a₂) := by
    have hfar : (B \ {(a₁, a₂)})ᶜ ∈ 𝓝 (a₁, a₂) :=
      ((h.finite_morseBrokenTrajectoryPairs hf c₁ c₂).sdiff.isClosed.isOpen_compl).mem_nhds
        (by simp)
    refine nhdsWithin_le_of_mem (mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨_, hfar, fun x ⟨hxB, hxK⟩ ↦ ?_⟩)
    rcases h.closure_morseTrajectoryPairs_subset hf hind hr₂ h₂₁ h₁p hgap hxK with hx | hx
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

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
