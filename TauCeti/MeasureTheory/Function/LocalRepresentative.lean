/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Gluing local `Cⁿ` representatives

A function that agrees almost everywhere near each point of a set `Ω` with a `Cⁿ` function
agrees almost everywhere on all of `Ω` with a single function that is `Cⁿ` on `Ω`. The set `Ω`
is arbitrary; the typical case is an open domain.
Two local representatives are continuous and agree almost everywhere on their common open
domain, so for a measure that charges every nonempty open set they agree everywhere there
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The value at `y` of any representative near `y`
therefore defines the glued function on `Ω`; outside `Ω` it is `u` itself, so its exceptional
set lies in `Ω`. On any Lindelöf subset (in particular, any subset of a second-countable space),
a countable subcover turns the local almost everywhere equalities into a global one.

This is how regularity proved locally, for instance by multiplying a Sobolev function by cutoffs,
becomes regularity of one representative on the whole domain. The case `n = 0` glues continuous
representatives.

The same argument shows that `Cⁿ` representatives are unique together with their derivatives,
also at points outside the interior of the set, provided the set lies in the closure of its
interior (as a half-disc `Ω ∩ {0 ≤ im}` does up to the real axis).

## Main results

* `TauCeti.exists_eqOn_ae_eq_of_locally`: local continuous representatives on a Lindelöf subset
  satisfying a monotone local property glue to a representative agreeing with a witness near each
  point.
* `TauCeti.exists_contDiffOn_ae_eq_of_locally`: local `Cⁿ` representatives glue to a `Cⁿ`
  representative on `Ω`.
* `TauCeti.eqOn_iteratedFDeriv_of_ae_eq`: two `Cⁿ` representatives on a set lying in the closure
  of its interior have the same derivatives of every order `i ≤ n` on that set.
-/

public section

open MeasureTheory Set Filter Topology

namespace TauCeti

/-- **Gluing local continuous representatives on a Lindelöf subset.** If near each point of a
Lindelöf set `Ω` the function `u` agrees almost everywhere with a function satisfying a local
property `P` (monotone under shrinking and implying continuity on the patch), then `u` agrees
almost everywhere on `Ω` with a single function `G` that agrees on `Ω ∩ U` with a `P`-witness
on an open neighbourhood `U` of each point of `Ω`. The measure must charge every nonempty open
set. -/
theorem exists_eqOn_ae_eq_of_locally
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [TopologicalSpace β] [T2Space β]
    {μ : Measure α} [μ.IsOpenPosMeasure] {u : α → β} {Ω : Set α} (hΩ : IsLindelof Ω)
    {P : Set α → (α → β) → Prop}
    (hP_mono : ∀ {s t : Set α} {g : α → β}, s ⊆ t → P t g → P s g)
    (hP_cont : ∀ {s : Set α} {g : α → β}, P s g → ContinuousOn g s)
    (h : ∀ x ∈ Ω, ∃ U ∈ 𝓝 x, ∃ g : α → β, P U g ∧ u =ᵐ[μ.restrict U] g) :
    ∃ G : α → β,
      (∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ g : α → β, P U g ∧ EqOn G g (Ω ∩ U)) ∧
      u =ᵐ[μ.restrict Ω] G := by
  classical
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : α → β, P U g ∧ u =ᵐ[μ.restrict U] g := by
    intro x hx
    obtain ⟨U, hU, g, hg, hug⟩ := h x hx
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hP_mono interior_subset hg, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose! U hUo hxU g hg hug using h'
  -- Two representatives are continuous and agree almost everywhere on their common open domain,
  -- hence agree everywhere there; so the representative at `y` agrees with the one near `x`.
  -- Outside `Ω` the glued function is `u` itself.
  let G : α → β := fun y ↦ if hy : y ∈ Ω then g y hy y else u y
  have hGΩ : ∀ y (hy : y ∈ Ω), G y = g y hy y := fun y hy ↦ dite_eq_left hy
  have hGu : ∀ y ∉ Ω, G y = u y := fun y hy ↦ dite_eq_right hy
  have hG : ∀ x (hx : x ∈ Ω), EqOn G (g x hx) (Ω ∩ U x) := fun x hx y hy ↦ by
    rw [hGΩ y hy.1]
    exact Measure.eqOn_open_of_ae_eq (f := g y hy.1) (g := g x hx)
      ((EventuallyEq.symm <| ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (hug y hy.1)).trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug x hx)))
      ((hUo y hy.1).inter (hUo x hx)) ((hP_cont (hg y hy.1)).mono inter_subset_left)
      ((hP_cont (hg x hx)).mono inter_subset_right) ⟨hxU y hy.1, hy.2⟩
  refine ⟨G, fun x hx ↦ ⟨U x, hUo x hx, hxU x hx, g x hx, hg x hx, hG x hx⟩, ?_⟩
  -- A countable subcover of `Ω` turns the local almost everywhere equalities into a global one.
  have hmem : ∀ y, u y ≠ G y → y ∈ Ω := fun y hy ↦ by_contra fun hyΩ ↦ hy (hGu y hyΩ).symm
  obtain ⟨t, htc, htΩ, hΩt⟩ := hΩ.elim_nhds_subcover U fun x hx ↦ (hUo x hx).mem_nhds (hxU x hx)
  have hnull : μ (⋃ x ∈ t, {y | y ∈ U x ∧ u y ≠ G y}) = 0 := by
    refine (measure_biUnion_null_iff htc).2 fun x hx ↦ ?_
    refine measure_mono_null ?_ (ae_iff.1 (ae_imp_of_ae_restrict (hug x (htΩ x hx))))
    intro y hy
    exact not_imp.2 ⟨hy.1, by rw [← hG x (htΩ x hx) ⟨hmem y hy.2, hy.1⟩]; exact hy.2⟩
  refine ae_restrict_of_ae <| ae_iff.2 <| measure_mono_null (fun y hy ↦ ?_) hnull
  obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.1 (hΩt (hmem y hy))
  exact mem_iUnion₂.2 ⟨x, hxt, hyU, hy⟩

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
  obtain ⟨G, hG, huG⟩ := exists_eqOn_ae_eq_of_locally (HereditarilyLindelofSpace.isLindelof Ω)
    (P := fun s g ↦ ContDiffOn 𝕜 n g s)
    (fun hst hg ↦ hg.mono hst) (fun hg ↦ hg.continuousOn) h
  refine ⟨G, contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_, huG⟩
  obtain ⟨U, hUo, hxU, g, hg, hGg⟩ := hG x hx
  exact ⟨U, hUo, hxU, (hg.mono inter_subset_right).congr hGg⟩

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
