/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.Restriction
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Local Rellich compactness for first-order Sobolev functions

Restriction of the values of arbitrary `W^{1,p}(Ω)` functions to an open `V` with compact
closure inside `Ω` is compact into `Lᵖ(V)`, for `1 ≤ p < ∞`.
No boundary regularity or vanishing trace is required: a smooth cutoff equal to one near
`closure V` turns each Sobolev function into a zero-boundary Sobolev function on `Ω`, to which
Rellich--Kondrachov applies on a bounded subdomain containing `closure V`. This local compactness
is used when passing to limits in interior elliptic estimates and weak-solution arguments.

The global compactness theorem for zero-boundary functions is
`TauCeti.W1p0.isCompactOperator_valueL`.

## Reference

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Theorem 9.16 (Rellich--Kondrachov compact embedding on bounded C¹ domains).
The local statement here follows by cutoff localization and the zero-boundary theorem above.
-/

public section

noncomputable section

namespace TauCeti

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega V : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Compactness of the value restriction on a bounded ambient domain, by a smooth cutoff. -/
private theorem W1p.isCompactOperator_valueL_restrictL_of_isBounded (hp : p ≠ ∞)
    (hOmega : IsBounded (Omega : Set E))
    (hVc : IsCompact (closure (V : Set E)))
    (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    IsCompactOperator
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL (SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)))) := by
  have hV : V ≤ Omega :=
    SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)
  obtain ⟨psi, M, hpsi, _, hpsiOne, hcpt, hts, hM, hpsiM, hgradM⟩ :=
    hVc.exists_contDiff_cutoff_with_bounds Omega.isOpen hVO
  obtain ⟨cutoff, cutoff_apply⟩ := W1p.exists_clm_w1p0_apply_eq_contDiffSMul (mu := mu)
    (Omega := Omega) (p := p) hp hpsi hM (fun x _ => hpsiM x) (fun x _ => hgradM x) hcpt hts
  have hmeasure : mu.restrict (V : Set E) ≤ (1 : ENNReal) • mu.restrict (Omega : Set E) := by
    simpa only [one_smul] using Measure.restrict_mono_set mu
      (SetLike.coe_subset_coe.mpr hV)
  let res : Lp ℝ p (mu.restrict (Omega : Set E)) →L[ℝ] Lp ℝ p (mu.restrict (V : Set E)) :=
    Lp.LpToLpOfMeasureLeSMul (by simp) hmeasure
  have hcompact : IsCompactOperator
      ((res.comp (W1p0.valueL (mu := mu) (Omega := Omega) (p := p))).comp cutoff) :=
    ((W1p0.isCompactOperator_valueL hp hOmega).clm_comp res).comp_clm cutoff
  have hOne : ∀ x ∈ (V : Set E), psi x = 1 := fun x hx =>
    interior_subset (s := psi ⁻¹' {1}) (hpsiOne (subset_closure hx))
  rw [W1p.valueL_comp_restrictL_eq_comp_cutoff hV hpsi hM (fun x _ => hpsiM x)
    (fun x _ => hgradM x) hOne cutoff cutoff_apply res
    (fun f => Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hmeasure f)]
  exact hcompact

/-- **Local Rellich--Kondrachov compactness.** If `V` has compact closure contained in `Ω` and
`1 ≤ p < ∞`, restriction of values from `W^{1,p}(Ω)` to `Lᵖ(V)` is compact. Neither the
boundedness nor the boundary regularity of `Ω` is required. -/
theorem W1p.isCompactOperator_valueL_restrictL (hp : p ≠ ∞)
    (hVc : IsCompact (closure (V : Set E)))
    (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    IsCompactOperator
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL (SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)))) := by
  have hV : V ≤ Omega :=
    SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)
  obtain ⟨R, hR⟩ := hVc.isBounded.subset_ball (0 : E)
  let U : Opens E := Omega ⊓ ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := inf_le_left
  have hUc : closure (V : Set E) ⊆ (U : Set E) := by
    intro x hx
    exact ⟨hVO hx, hR hx⟩
  have hVU : V ≤ U := SetLike.coe_subset_coe.mp (Subset.trans subset_closure hUc)
  have hUbdd : IsBounded (U : Set E) :=
    (Metric.isBounded_ball (x := (0 : E)) (r := R)).subset (fun x hx => hx.2)
  have hcompact := W1p.isCompactOperator_valueL_restrictL_of_isBounded
    (mu := mu) (Omega := U) (V := V) hp hUbdd hVc hUc
  have heq : (W1p.valueL (mu := mu) (Omega := V) (p := p)).comp (W1p.restrictL hV) =
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL hVU)).comp (W1p.restrictL hU) := by
    ext u
    have hr : W1p.restrictL hV u =
        W1p.restrictL hVU (W1p.restrictL hU u) := by
      exact (W1p.restrictL_restrictL hU hVU u).symm
    simp only [ContinuousLinearMap.comp_apply, hr, Filter.EventuallyEq.rfl]
  rw [heq]
  exact hcompact.comp_clm (W1p.restrictL hU)

end TauCeti

end

end
