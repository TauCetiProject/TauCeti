/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Calculus.ContDiff.Gluing

/-!
# Gluing local `Cⁿ` representatives

A function that agrees almost everywhere near each point of a set `Ω` with a `Cⁿ` function
agrees almost everywhere on all of `Ω` with a single function that is `Cⁿ` on `Ω`. The set `Ω`
is arbitrary; the typical case is an open domain.
Two local representatives are continuous and agree almost everywhere on their common open
domain, so for a measure that charges every nonempty open set they agree everywhere there
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The value at `y` of any representative near `y`
therefore defines the glued function on `Ω` (`TauCeti.exists_contDiffOn_eqOn_of_locally`);
outside `Ω` it is `u` itself, so its exceptional set lies in `Ω`. Second countability turns the
local almost everywhere equalities into a global one (`MeasureTheory.measure_null_of_locally_null`).

This is how regularity proved locally, for instance by multiplying a Sobolev function by cutoffs,
becomes regularity of one representative on the whole domain. The case `n = 0` glues continuous
representatives.

## Main results

* `TauCeti.exists_contDiffOn_ae_eq_of_locally`: local `Cⁿ` representatives glue to a `Cⁿ`
  representative on `Ω`.
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
  have h' : ∀ x : Ω, ∃ U, IsOpen U ∧ x.1 ∈ U ∧
      ∃ g : E → F, ContDiffOn 𝕜 n g U ∧ u =ᵐ[μ.restrict U] g := by
    intro x
    obtain ⟨U, hU, g, hg, hug⟩ := h x x.2
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose U hUo hxU g hg hug using h'
  -- Two representatives are continuous and agree almost everywhere on their common open domain,
  -- hence agree everywhere there, so they glue. Outside `Ω` the glued function is `u` itself.
  have hgg (x y : Ω) : EqOn (g x) (g y) (U x ∩ U y) :=
    Measure.eqOn_open_of_ae_eq (μ := μ)
      ((EventuallyEq.symm <| ae_restrict_of_ae_restrict_of_subset inter_subset_left (hug x)).trans
        (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug y)))
      ((hUo x).inter (hUo y)) ((hg x).continuousOn.mono inter_subset_left)
      ((hg y).continuousOn.mono inter_subset_right)
  obtain ⟨G, hGc, hG, hGu⟩ := exists_contDiffOn_eqOn_of_locally hUo
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxU _⟩) hg
    (fun x y ↦ (hgg x y).mono (inter_subset_inter_left _ inter_subset_right)) u
  have hΩ : ∀ y, u y ≠ G y → y ∈ Ω := fun y hy => by
    by_contra hyΩ
    exact hy (hGu hyΩ).symm
  refine ⟨G, hGc, ae_restrict_of_ae <| ae_iff.2 ?_⟩
  -- Near `x ∈ Ω` the glued function is `g x`, which equals `u` almost everywhere on `U x`.
  refine measure_null_of_locally_null _ fun x hx => ?_
  have hxΩ := hΩ x hx
  refine ⟨_, inter_mem_nhdsWithin _ ((hUo ⟨x, hxΩ⟩).mem_nhds (hxU _)),
    measure_mono_null ?_ (ae_iff.1 (ae_imp_of_ae_restrict (hug ⟨x, hxΩ⟩)))⟩
  rintro y ⟨hy, hyU⟩
  exact not_imp.2 ⟨hyU, by rwa [← hG _ ⟨hΩ y hy, hyU⟩]⟩

end TauCeti
