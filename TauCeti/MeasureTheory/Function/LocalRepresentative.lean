/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.MeasureTheory.Function.Gluing

/-!
# Gluing local `Cⁿ` representatives

A function that agrees almost everywhere near each point of a set `Ω` with a `Cⁿ` function
agrees almost everywhere on all of `Ω` with a single function that is `Cⁿ` on `Ω`. The set `Ω`
is arbitrary; the typical case is an open domain.
Two local representatives are continuous and agree almost everywhere on their common open
domain, so for a measure that charges every nonempty open set they agree everywhere there. In a
second-countable space every set is Lindelöf, so they glue to one representative on `Ω`
(`IsLindelof.exists_ae_eq_and_eqOn_of_forall_ae_eq_continuousOn`).

This is how regularity proved locally, for instance by multiplying a Sobolev function by cutoffs,
becomes regularity of one representative on the whole domain. The case `n = 0` glues continuous
representatives.

The same argument shows that `Cⁿ` representatives are unique together with their derivatives,
also at points outside the interior of the set, provided the set lies in the closure of its
interior (as a half-disc `Ω ∩ {0 ≤ im}` does up to the real axis).

## Main results

* `TauCeti.exists_contDiffOn_ae_eq_of_locally`: local `Cⁿ` representatives glue to a `Cⁿ`
  representative on `Ω`.
* `TauCeti.eqOn_iteratedFDeriv_of_ae_eq`: two `Cⁿ` representatives on a set lying in the closure
  of its interior have the same derivatives of every order `i ≤ n` on that set.
-/

public section

open MeasureTheory Set Filter Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace E] [SecondCountableTopology E]
  {μ : Measure E} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞} {u : E → F} {Ω : Set E}

/-- **Gluing local `Cⁿ` representatives.** If near each point of the set `Ω` the function `u`
agrees almost everywhere with a function that is `Cⁿ` on a neighbourhood of that point, then `u`
agrees almost everywhere on `Ω` with a single function that is `Cⁿ` on `Ω`. The measure must charge
every nonempty open set. -/
theorem exists_contDiffOn_ae_eq_of_locally
    (h : ∀ x ∈ Ω, ∃ U ∈ 𝓝 x, ∃ g : E → F, ContDiffOn 𝕜 n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : E → F, ContDiffOn 𝕜 n g Ω ∧ u =ᵐ[μ.restrict Ω] g := by
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → F, ContDiffOn 𝕜 n g U ∧ u =ᵐ[μ.restrict U] g := fun x hx ↦ by
    obtain ⟨U, hU, g, hg, hug⟩ := h x hx
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose! U hUo hxU g hg hug using h'
  -- The continuous local representatives agree on overlaps and glue to one representative.
  obtain ⟨G, huG, hG⟩ := IsLindelof.exists_ae_eq_and_eqOn_of_forall_ae_eq_continuousOn
    (HereditarilyLindelofSpace.isLindelof Ω) (μ := μ) hUo hxU
    (fun x hx ↦ (hg x hx).continuousOn) hug
  refine ⟨G, contDiffOn_of_locally_contDiffOn fun x hx ↦ ⟨U x, hUo x hx, hxU x hx, ?_⟩,
    ae_restrict_of_ae huG⟩
  exact ((hg x hx).mono inter_subset_right).congr fun y hy ↦ hG x hx ⟨hy.2, hy.1⟩

omit [SecondCountableTopology E] in
/-- **`Cⁿ` representatives are unique, with their derivatives.** Let `U` lie in the closure of
its interior. If `g₁` and `g₂` are `Cⁿ` on open sets containing `U` and agree almost everywhere on
`U`, then their derivatives of every order `i ≤ n` agree at every point of `U`, including the
points of `U` outside its interior. The measure must charge every nonempty open set. -/
theorem eqOn_iteratedFDeriv_of_ae_eq {U V₁ V₂ : Set E} {g₁ g₂ : E → F}
    (hU : U ⊆ closure (interior U)) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hUV₁ : U ⊆ V₁)
    (hUV₂ : U ⊆ V₂) (hg₁ : ContDiffOn 𝕜 n g₁ V₁) (hg₂ : ContDiffOn 𝕜 n g₂ V₂)
    (h : g₁ =ᵐ[μ.restrict U] g₂) {i : ℕ} (hi : i ≤ n) :
    EqOn (iteratedFDeriv 𝕜 i g₁) (iteratedFDeriv 𝕜 i g₂) U := by
  set O := V₁ ∩ V₂
  have hO : IsOpen O := hV₁.inter hV₂
  set W := O ∩ interior U
  have hW : IsOpen W := hO.inter isOpen_interior
  have hWU : W ⊆ U := fun _ hz => interior_subset hz.2
  -- On the open set `W` the two maps are continuous and equal almost everywhere, hence equal, and
  -- so are their derivatives.
  have heq : EqOn g₁ g₂ W := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset hWU h) hW (hg₁.continuousOn.mono fun _ hz => hz.1.1)
    (hg₂.continuousOn.mono fun _ hz => hz.1.2)
  have hD : EqOn (iteratedFDeriv 𝕜 i g₁) (iteratedFDeriv 𝕜 i g₂) W := fun z hz =>
    ((heq.eventuallyEq_of_mem (hW.mem_nhds hz)).iteratedFDeriv 𝕜 i).eq_of_nhds
  -- The derivatives are continuous on `U`, which lies in the closure of `W`.
  exact hD.of_subset_closure ((ContinuousOn.continuousOn_iteratedFDeriv hg₁ hV₁ hi).mono hUV₁)
    ((ContinuousOn.continuousOn_iteratedFDeriv hg₂ hV₂ hi).mono hUV₂) hWU fun z hz =>
      hO.inter_closure ⟨⟨hUV₁ hz, hUV₂ hz⟩, hU hz⟩

end TauCeti
