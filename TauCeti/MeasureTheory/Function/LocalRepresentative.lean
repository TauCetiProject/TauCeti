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

A function that agrees almost everywhere near each point of an open set `Ω` with a `Cⁿ`
function agrees almost everywhere on all of `Ω` with a single function that is `Cⁿ` on `Ω`.
Two local representatives are continuous and agree almost everywhere on their common open
domain, so for a measure that charges every nonempty open set they agree everywhere there
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The value at `y` of any representative near `y`
therefore defines the glued function, and second countability turns the local almost everywhere
equalities into a global one (`MeasureTheory.measure_null_of_locally_null`).

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
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology E] {μ : Measure E} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞}
  {u : E → F} {Ω : Set E}

/-- **Gluing local `Cⁿ` representatives.** If near each point of the open set `Ω` the function `u`
agrees almost everywhere with a function that is `Cⁿ` on a neighbourhood of that point, then `u`
agrees almost everywhere on `Ω` with a single function that is `Cⁿ` on `Ω`. The measure must
charge every nonempty open set. -/
theorem exists_contDiffOn_ae_eq_of_locally (hΩ : IsOpen Ω)
    (h : ∀ x ∈ Ω, ∃ U ∈ 𝓝 x, ∃ g : E → F, ContDiffOn 𝕜 n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : E → F, ContDiffOn 𝕜 n g Ω ∧ u =ᵐ[μ.restrict Ω] g := by
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → F, ContDiffOn 𝕜 n g U ∧ u =ᵐ[μ.restrict U] g := by
    intro x hx
    obtain ⟨U, hU, g, hg, hug⟩ := h x hx
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose! U hUo hxU g hg hug using h'
  -- The representative near `y` agrees with the one near `x` wherever both are defined.
  have hagree : ∀ x ∈ Ω, ∀ y ∈ Ω, EqOn (g x) (g y) (U x ∩ U y) := by
    intro x hx y hy
    have hx' : u =ᵐ[μ.restrict (U x ∩ U y)] g x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hug x hx)
    have hy' : u =ᵐ[μ.restrict (U x ∩ U y)] g y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug y hy)
    exact Measure.eqOn_open_of_ae_eq (hx'.symm.trans hy') ((hUo x hx).inter (hUo y hy))
      ((hg x hx).continuousOn.mono inter_subset_left)
      ((hg y hy).continuousOn.mono inter_subset_right)
  have hG : ∀ x ∈ Ω, EqOn (fun y => g y y) (g x) (Ω ∩ U x) := fun x hx y hy =>
    hagree y hy.1 x hx ⟨hxU y hy.1, hy.2⟩
  refine ⟨fun y => g y y, contDiffOn_of_locally_contDiffOn fun x hx =>
    ⟨U x, hUo x hx, hxU x hx, ((hg x hx).mono inter_subset_right).congr (hG x hx)⟩, ?_⟩
  rw [EventuallyEq, ae_restrict_iff' hΩ.measurableSet, ae_iff]
  -- Near `x ∈ Ω` the glued function is `g x`, which equals `u` almost everywhere on `U x`.
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨hxΩ, -⟩ := not_imp.1 hx
  have hnull := ae_iff.1 ((ae_restrict_iff' (hUo x hxΩ).measurableSet).1 (hug x hxΩ))
  refine ⟨_, inter_mem_nhdsWithin _ ((hUo x hxΩ).mem_nhds (hxU x hxΩ)),
    measure_mono_null ?_ hnull⟩
  rintro y ⟨hy, hyU⟩
  obtain ⟨hyΩ, hne⟩ := not_imp.1 hy
  exact not_imp.2 ⟨hyU, by rwa [← hG x hxΩ ⟨hyΩ, hyU⟩]⟩

end TauCeti
