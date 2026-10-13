/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
public import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Integration by parts in `W^{1,p}` against Lipschitz functions

The weak gradient of `u ∈ W^{1,p}(Ω)` is defined by testing against smooth functions with compact
support in `Ω`. For `1 ≤ p < ∞` the same identity holds against every Lipschitz function `g` with
compact support in `Ω`:

`∫_Ω (∂_v g) u = -∫_Ω g ⟪∇u, v⟫`,

where `∂_v g = lineDeriv ℝ g · v` is the directional derivative of `g`, which exists almost
everywhere by Rademacher's theorem and satisfies `|∂_v g| ≤ L ‖v‖`, where `L` is the
Lipschitz constant of `g`.

Test functions built from a Lipschitz coefficient field, such as `φ ⟪a ∇ψ, e⟫` for a smooth `φ`
and a smooth cutoff `ψ`, are only Lipschitz. This identity is what lets such test functions be
used in a weak formulation, for instance when a weak solution of an equation with Lipschitz
principal coefficients is multiplied by a cutoff.

## The argument

Both sides are continuous linear functionals of `u ∈ W^{1,p}(Ω)`: `g` and `∂_v g` are bounded with
compact support, so they lie in the dual exponent space and the two sides are Hölder pairings
(`ContinuousLinearMap.lpPairing`). By the Meyers–Serrin theorem
(`TauCeti.Wkp.dense_contDiffOn_representatives`) it therefore suffices to treat `u` smooth on `Ω`.
For such `u` the identity is integration by parts against a Lipschitz function with compact
support in `Ω`, `TauCeti.integral_lineDeriv_mul_eq_neg_of_contDiffOn`: a smooth cutoff equal to one
near the support of `g` turns `u` into a smooth function with compact support on the whole space,
which is Lipschitz, and the identity becomes Mathlib's integration by parts for Lipschitz
functions, `LipschitzWith.integral_lineDeriv_mul_eq`.

## Main declarations

* `TauCeti.W1p.setIntegral_lineDeriv_mul_value_eq_neg`: integration by parts against a Lipschitz
  function with compact support in `Ω`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §4.2.3 and
  §6.2 (Lipschitz functions are weakly differentiable, with their almost everywhere gradient).
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff InnerProductSpace Topology NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {g : E → ℝ} {L : ℝ≥0}

/-- **Integration by parts against Lipschitz functions.** For `1 ≤ p < ∞`, `u ∈ W^{1,p}(Ω)`, a
Lipschitz function `g` with compact support in `Ω`, and a direction `v`,

`∫_Ω (∂_v g) u = -∫_Ω g ⟪∇u, v⟫`.

For a smooth `g` this is the definition of the weak gradient; here `g` need only be Lipschitz, and
`∂_v g` is its directional derivative, which exists almost everywhere. -/
theorem W1p.setIntegral_lineDeriv_mul_value_eq_neg (hp : p ≠ ⊤) (u : W1p mu Omega p)
    (hg : LipschitzWith L g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Omega) (v : E) :
    ∫ x in Omega, lineDeriv ℝ g x v * W1p.value u x ∂mu =
      -∫ x in Omega, g x * ⟪W1p.gradient u x, v⟫_ℝ ∂mu := by
  let q := ENNReal.conjExponent p
  let _ : q.HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  -- `∂_v g` and `g` are bounded with compact support, so they lie in the dual exponent space.
  have hdgc : HasCompactSupport fun x => lineDeriv ℝ g x v :=
    hgc.mono' fun x hx => by_contra fun h => hx (lineDeriv_of_notMem_tsupport h v)
  have hdg : MemLp (fun x => lineDeriv ℝ g x v) q (mu.restrict Omega) :=
    (hdgc.memLp_of_bound (aestronglyMeasurable_lineDeriv hg.continuous mu) (L * ‖v‖)
      (.of_forall fun _ => norm_lineDeriv_le_of_lipschitz ℝ hg)).restrict _
  have hg' : MemLp g q (mu.restrict Omega) :=
    (hg.continuous.memLp_of_hasCompactSupport hgc).restrict _
  -- The two sides, as a continuous linear functional on `W^{1,p}(Ω)`.
  let B : ℝ →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight (innerSL ℝ v)
  let Φ : W1p mu Omega p →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (mu.restrict Omega) q p (hdg.toLp _)).comp
        W1p.valueL +
      (B.lpPairing (mu.restrict Omega) q p (hg'.toLp _)).comp W1p.gradientL
  have hΦ : ∀ w : W1p mu Omega p, Φ w = (∫ x in Omega, lineDeriv ℝ g x v * W1p.value w x ∂mu) +
      ∫ x in Omega, g x * ⟪W1p.gradient w x, v⟫_ℝ ∂mu := fun w => by
    simp only [Φ, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.lpPairing_eq_integral, W1p.valueL_apply, W1p.gradientL_apply]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [hdg.coeFn_toLp] with x hx
      rw [ContinuousLinearMap.mul_apply', hx]
    · refine integral_congr_ae ?_
      filter_upwards [hg'.coeFn_toLp] with x hx
      simp [B, hx, real_inner_comm]
  -- The functional vanishes on the elements represented by functions smooth on `Ω`.
  have hsmooth : ∀ w : W1p mu Omega p, (∃ f : E → ℝ, ContDiffOn ℝ ∞ f Omega ∧
      (W1p.value w : E → ℝ) =ᵐ[mu.restrict Omega] f) → Φ w = 0 := by
    rintro w ⟨f, hf, hw⟩
    have hf1 : ContDiffOn ℝ 1 f Omega := hf.of_le (by simp)
    have hfy : ∀ y ∈ (Omega : Set E), DifferentiableAt ℝ f y := fun y hy =>
      (hf1.differentiableOn one_ne_zero y hy).differentiableAt (Omega.isOpen.mem_nhds hy)
    have hgrad : ∀ᵐ y ∂mu.restrict Omega, innerSL ℝ (W1p.gradient w y) = fderiv ℝ f y :=
      ((W1p.hasWeakFDerivOn w).congr_ae hw).ae_eq_fderiv
        ((hf1.continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl).locallyIntegrableOn
          Omega.isOpen.measurableSet) hfy
    -- Both integrands vanish off `tsupport g ⊆ Ω`, so the set integrals are whole-space ones.
    have hout : ∀ (G : E → ℝ), (∀ x ∉ tsupport g, G x = 0) →
        ∫ x in Omega, G x ∂mu = ∫ x, G x ∂mu := fun G hG =>
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        hG x fun h => hx (hgs h)
    have e1 : ∫ x in Omega, lineDeriv ℝ g x v * W1p.value w x ∂mu =
        ∫ x, lineDeriv ℝ g x v * f x ∂mu := by
      rw [← hout _ fun x hx => by simp [lineDeriv_of_notMem_tsupport hx]]
      exact integral_congr_ae (hw.mono fun x hx => by simp only [hx])
    have e2 : ∫ x in Omega, g x * ⟪W1p.gradient w x, v⟫_ℝ ∂mu =
        ∫ x, g x * fderiv ℝ f x v ∂mu := by
      rw [← hout _ fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]]
      refine integral_congr_ae (hgrad.mono fun x hx => ?_)
      simp only [← innerSL_apply_apply, hx]
    rw [hΦ, e1, e2, integral_lineDeriv_mul_eq_neg_of_contDiffOn Omega.isOpen hf1 hg hgc hgs v,
      neg_add_cancel]
  -- By Meyers–Serrin these elements are dense, and the kernel of `Φ` is closed.
  have hker :=
    closure_minimal (fun (w : Wkp mu Omega p 1) hw => by
      obtain ⟨f, hf, hwf⟩ := hw
      rw [Wkp.value_one] at hwf
      exact hsmooth w ⟨f, hf, hwf⟩)
      (ContinuousLinearMap.isClosed_ker Φ) (Wkp.dense_contDiffOn_representatives hp 1 u)
  have h := hΦ u
  have h0 : Φ u = 0 := hker
  linarith

end TauCeti
