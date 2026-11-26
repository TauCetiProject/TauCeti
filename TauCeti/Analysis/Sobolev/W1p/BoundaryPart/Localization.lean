/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
public import TauCeti.Analysis.Sobolev.W1p.Localization
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

Moving such a cutoff product between two open sets that agree on its support also preserves
vanishing on a boundary part: localizing `u ∈ W^{1,p}_Γ(Ω)` to an open set `V` by a cutoff `ψ`,
where `V ∩ tsupport ψ ⊆ Ω`, gives an element of `W^{1,p}_{Γ'}(V)` as soon as `closure Γ'` meets the
support of `ψ` only inside `closure Γ`
(`TauCeti.W1p.localizeL_restrictL_mem_w1pVanishingOnSubmodule`). This carries a function vanishing
on a boundary part of a chart model back to the original domain.

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
open scoped ENNReal Topology Gradient ContDiff Distributions

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

/-- **Localizing to another open set preserves vanishing on a boundary part.** Let `ψ` be smooth
and bounded together with its gradient on `Ω`, and let `V` be an open set with
`V ∩ tsupport ψ ⊆ Ω`. If `u ∈ W^{1,p}_Γ(Ω)` and every point of `closure Γ'` in the support of `ψ`
lies in `closure Γ`, then the localization of `u` to `V` by `ψ`, equal to `ψ u` on `Ω ∩ V` and to
zero on the rest of `V`, lies in `W^{1,p}_{Γ'}(V)`. This is the analogue of
`TauCeti.W1p.localizeL_restrictL_mem_w1p0Submodule`. -/
theorem W1p.localizeL_restrictL_mem_w1pVanishingOnSubmodule {V : Opens E} {Γ' : Set E}
    {psi : E → ℝ} {M : ℝ} (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (hV : (V : Set E) ∩ tsupport psi ⊆ Omega) (hΓ : closure Γ' ∩ tsupport psi ⊆ closure Γ)
    {u : W1p mu Omega p} (hu : u ∈ w1pVanishingOnSubmodule mu Omega p Γ) :
    W1p.localizeL (inf_le_right : Omega ⊓ V ≤ V) psi hpsi hM
      (fun x hx => hpsiM x hx.1) (fun x hx => hgradM x hx.1)
      (fun _ hx => ⟨hV hx, hx.1⟩) (W1p.restrictL inf_le_left u) ∈
        w1pVanishingOnSubmodule mu V p Γ' := by
  let T := (W1p.localizeL (μ := mu) (p := p) (inf_le_right : Omega ⊓ V ≤ V) psi hpsi hM
    (fun x hx => hpsiM x hx.1) (fun x hx => hgradM x hx.1)
    (fun _ hx => ⟨hV hx, hx.1⟩)).comp (W1p.restrictL inf_le_left)
  refine w1pVanishingOnSubmodule_subset_of_isClosed
    ((w1pVanishingOnSubmodule mu V p Γ').isClosed.preimage T.continuous) (fun φ hφ => ?_) hu
  -- The product `ψ φ` is a test function on the whole space, and `T φ` is its restriction to `V`.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : 𝓓((⊤ : Opens E), ℝ), ⇑Φ = fun x => psi x * φ x :=
    ⟨⟨fun x => psi x * φ x, hpsi.mul φ.contDiff, φ.hasCompactSupport.mul_left, subset_univ _⟩,
      rfl⟩
  have hTφ : T (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)) =
      W1p.restrictL (le_top : V ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p Φ) := by
    refine W1p.ext_value (Lp.ext ?_)
    have hres := (ae_restrict_iff' (Omega ⊓ V).isOpen.measurableSet).1
      (W1p.value_restrictL_ae (p := p) (inf_le_left : Omega ⊓ V ≤ Omega)
        (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)))
    have hφΩ := (ae_restrict_iff' Omega.isOpen.measurableSet).1
      (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : Omega ≤ ⊤) φ)
    filter_upwards [W1p.value_localizeL_ae (μ := mu) (p := p) inf_le_right hpsi hM
        (fun x hx => hpsiM x hx.1) (fun x hx => hgradM x hx.1) (fun _ hx => ⟨hV hx, hx.1⟩)
        (W1p.restrictL inf_le_left
          (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ))),
      ae_restrict_of_ae hres, ae_restrict_of_ae hφΩ,
      W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : V ≤ ⊤) Φ,
      ae_restrict_mem V.isOpen.measurableSet] with x hx hr hf hΦx hxV
    rw [ContinuousLinearMap.comp_apply, hx, hΦx, hΦ]
    by_cases hxΩ : x ∈ Omega
    · have hxU : x ∈ ((Omega ⊓ V : Opens E) : Set E) := ⟨hxΩ, hxV⟩
      rw [indicator_of_mem hxU, hr hxU, hf hxΩ, smul_eq_mul]
    · have hxψ : x ∉ tsupport psi := fun h => hxΩ (hV ⟨hxV, h⟩)
      simp [hxΩ, image_eq_zero_of_notMem_tsupport hxψ]
  rw [mem_preimage, hTφ]
  refine W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule (disjoint_left.2 fun x hx hxΓ =>
    disjoint_left.1 hφ ?_ (hΓ ⟨hxΓ, ?_⟩))
  · rw [hΦ] at hx
    exact tsupport_mul_subset_right (f := psi) (g := φ) hx
  · rw [hΦ] at hx
    exact tsupport_mul_subset_left (f := psi) (g := φ) hx

end TauCeti
