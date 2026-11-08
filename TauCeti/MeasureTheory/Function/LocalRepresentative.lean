/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Gluing local `Cⁿ` representatives

A function that agrees almost everywhere near each point of a set `Ω` with a `Cⁿ` function
agrees almost everywhere on all of `Ω` with a single function that is `Cⁿ` on `Ω`. The set `Ω`
is arbitrary; the typical case is an open domain.
Two local representatives are continuous and agree almost everywhere on their common open
domain, so for a measure that charges every nonempty open set they agree everywhere there
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The value at `y` of any representative near `y`
therefore defines the glued function on `Ω`; outside `Ω` it is `u` itself, so its exceptional
set lies in `Ω`. Second countability turns the local almost everywhere equalities into a global
one (`MeasureTheory.measure_null_of_locally_null`).

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
  classical
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → F, ContDiffOn 𝕜 n g U ∧ u =ᵐ[μ.restrict U] g := by
    intro x hx
    obtain ⟨U, hU, g, hg, hug⟩ := h x hx
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose! U hUo hxU g hg hug using h'
  -- Two representatives are continuous and agree almost everywhere on their common open domain,
  -- hence agree everywhere there; so the representative at `y` agrees with the one near `x`.
  -- Outside `Ω` the glued function is `u` itself.
  obtain ⟨G, hGΩ, hGu⟩ : ∃ G : E → F, (∀ y ∈ Ω, G y = g y y) ∧ ∀ y ∉ Ω, G y = u y :=
    ⟨Ω.piecewise (fun y => g y y) u, fun _ => piecewise_eq_of_mem _ _ _,
      fun _ => piecewise_eq_of_notMem _ _ _⟩
  have hG : ∀ x ∈ Ω, EqOn G (g x) (Ω ∩ U x) := fun x hx y hy => by
    rw [hGΩ y hy.1]
    exact Measure.eqOn_open_of_ae_eq (f := g y) (g := g x)
      ((EventuallyEq.symm <| ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (hug y hy.1)).trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug x hx)))
      ((hUo y hy.1).inter (hUo x hx)) ((hg y hy.1).continuousOn.mono inter_subset_left)
      ((hg x hx).continuousOn.mono inter_subset_right) ⟨hxU y hy.1, hy.2⟩
  have hΩ : ∀ y, u y ≠ G y → y ∈ Ω := fun y hy => by
    by_contra hyΩ
    exact hy (hGu y hyΩ).symm
  refine ⟨G, contDiffOn_of_locally_contDiffOn fun x hx =>
    ⟨U x, hUo x hx, hxU x hx, ((hg x hx).mono inter_subset_right).congr (hG x hx)⟩, ?_⟩
  refine ae_restrict_of_ae <| ae_iff.2 ?_
  -- Near `x ∈ Ω` the glued function is `g x`, which equals `u` almost everywhere on `U x`.
  refine measure_null_of_locally_null _ fun x hx => ?_
  have hxΩ := hΩ x hx
  refine ⟨_, inter_mem_nhdsWithin _ ((hUo x hxΩ).mem_nhds (hxU x hxΩ)),
    measure_mono_null ?_ (ae_iff.1 (ae_imp_of_ae_restrict (hug x hxΩ)))⟩
  rintro y ⟨hy, hyU⟩
  exact not_imp.2 ⟨hyU, by rwa [← hG x hxΩ ⟨hΩ y hy, hyU⟩]⟩

end TauCeti
