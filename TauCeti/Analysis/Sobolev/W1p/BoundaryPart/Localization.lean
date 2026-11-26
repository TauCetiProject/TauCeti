/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Membership in `W^{1,p}_Γ(Ω)` is a local property

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space, `Γ` a set and
`1 ≤ p ≤ ∞`. This file proves that membership in the space `W^{1,p}_Γ(Ω)` of Sobolev functions
vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`) can be checked near each point of
`closure Ω`: if every such point has a neighbourhood `U` with `ψ u ∈ W^{1,p}_Γ(Ω)` for every
smooth `ψ`, bounded together with its gradient on `Ω`, whose support lies in `U`, then
`u ∈ W^{1,p}_Γ(Ω)` (`TauCeti.mem_w1pVanishingOnSubmodule_of_forall_mem_closure`).

This is how boundary conditions are verified chart by chart. For instance, the trace
characterization of `W^{1,p}_Γ(Ω)` on a Lipschitz domain is local in this sense: it reduces to
showing `ψ u ∈ W^{1,p}_Γ(Ω)` for cutoffs `ψ` supported in single boundary charts, where `Ω` and `Γ`
can be flattened.

## The argument

The closure of `Ω` is compact, so finitely many of the interiors of the neighbourhoods cover it,
and a smooth partition of unity `∑ᵢ χᵢ = 1` on `closure Ω` subordinate to them exists
(`IsCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one`). Each `χᵢ` has compact support, so
it is bounded together with its gradient, and `u = ∑ᵢ χᵢ u` is a finite sum of elements of the
subspace `W^{1,p}_Γ(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5 (localization of boundary
  conditions by a partition of unity subordinate to boundary charts).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology Gradient ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Γ : Set E}

/-- **Membership in `W^{1,p}_Γ(Ω)` is local.** Let `Ω` be bounded. If every point of `closure Ω`
has a neighbourhood `U` such that `ψ u ∈ W^{1,p}_Γ(Ω)` for every smooth `ψ` bounded together with
its gradient on `Ω` and supported in `U`, then `u ∈ W^{1,p}_Γ(Ω)`. -/
theorem mem_w1pVanishingOnSubmodule_of_forall_mem_closure
    (hb : Bornology.IsBounded (Omega : Set E)) {u : W1p mu Omega p}
    (h : ∀ x ∈ closure (Omega : Set E), ∃ U ∈ 𝓝 x, ∀ (psi : E → ℝ) (hpsi : ContDiff ℝ ∞ psi)
      {M : ℝ} (hM : 0 ≤ M) (hpsiM : ∀ y ∈ Omega, |psi y| ≤ M)
      (hgradM : ∀ y ∈ Omega, ‖∇ psi y‖ ≤ M), tsupport psi ⊆ U →
        W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1pVanishingOnSubmodule mu Omega p Γ) :
    u ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  choose! U hU hUu using h
  -- A smooth partition of unity on the compact set `closure Ω`, subordinate to the interiors of
  -- the neighbourhoods.
  obtain ⟨s, χ, hχ, -, -, hsum⟩ :=
    hb.isCompact_closure.exists_contDiff_tsupport_subset_finset_sum_eq_one
      (U := fun x : closure (Omega : Set E) => interior (U x)) (fun _ => isOpen_interior)
      fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x hx)⟩
  choose M hM hχM hgradM using fun i =>
    ((hχ i).1.of_le (by simp)).exists_abs_le_and_norm_gradient_le (hχ i).2.1
  -- Split `u` along the partition of unity; every piece lies in `W^{1,p}_Γ(Ω)`.
  have hsplit : u = ∑ i ∈ s,
      W1p.contDiffSMul (χ i) (hχ i).1 (hM i) (fun y _ => hχM i y) (fun y _ => hgradM i y) u := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_finsetSum_ae s fun i =>
        W1p.contDiffSMul (χ i) (hχ i).1 (hM i) (fun y _ => hχM i y) (fun y _ => hgradM i y) u,
      (eventually_all_finset s).2 fun i _ => W1p.value_contDiffSMul_ae (hχ i).1 (hM i)
        (fun y _ => hχM i y) (fun y _ => hgradM i y) u,
      ae_restrict_mem Omega.isOpen.measurableSet] with x hsumx hi hxΩ
    rw [hsumx, Finset.sum_congr rfl hi]
    simp only [smul_eq_mul, ← Finset.sum_mul, hsum x (subset_closure hxΩ), one_mul]
  rw [hsplit]
  exact sum_mem fun i _ => hUu i i.property (χ i) (hχ i).1 (hM i) _ _
    ((hχ i).2.2.trans interior_subset)

end TauCeti
