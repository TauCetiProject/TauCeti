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
  `0` to it (`IsMorseSmale.exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs`).

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

open Set
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
/-- **Broken trajectories come in pairs.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every critical value
strictly between `f r` and `f p` from `f r` and `f p`. Then the trajectories from `p` to `r`
broken once, recorded by their points on these levels, are even in number. -/
theorem even_ncard_morseBrokenTrajectoryPairs {p r : M}
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
    (fun w hw ↦ h.exists_homeomorph_Ico_of_mem_morseBrokenTrajectoryPairs hf hind hr₂ h₂₁ h₁p
      hgap w.2 hw) fun w hw ↦ ?_
  exact h.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs hf hind hr₂ h₂₁ h₁p hgap w.2
    ((h.closure_morseTrajectoryPairs_subset hf hind hr₂ h₂₁ h₁p hgap w.2).resolve_right hw)

include h hf in
/-- **Broken index-two trajectories come in pairs.** Between any two critical points `p` and `r`,
the broken index-two trajectories `morseBrokenTrajectorySet p r` are even in number. -/
theorem even_ncard_morseBrokenTrajectorySet (p r : criticalPoints 𝓘(ℝ, E) f) :
    Even (hX.morseBrokenTrajectorySet p r).ncard := by
  rcases (hX.morseBrokenTrajectorySet p r).eq_empty_or_nonempty with h0 | ⟨⟨q, z₁, z₂⟩, hx⟩
  · simp [h0]
  -- A broken trajectory forces `ind p = ind r + 2` and `f r < f p`.
  obtain ⟨hpq, hqr, hz₁, hz₂⟩ := hX.mem_morseBrokenTrajectorySet.1 hx
  have hne {a b : M} (h : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1) :
      a ≠ b := by
    rintro rfl; omega
  have hlt : f r < f p :=
    (hX.value_lt_of_mem_morseTrajectorySlice (hne hqr) hz₂).trans
      (hX.value_lt_of_mem_morseTrajectorySlice (hne hpq) hz₁)
  obtain ⟨c₁, c₂, hr₂, h₂₁, h₁p, hgap⟩ := hf.exists_lt_lt_forall_mem_Ioo hlt
  rw [← hX.ncard_morseBrokenTrajectoryPairs p r hr₂ h₁p hgap]
  exact h.even_ncard_morseBrokenTrajectoryPairs hf (by omega) hr₂ h₂₁ h₁p hgap

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
