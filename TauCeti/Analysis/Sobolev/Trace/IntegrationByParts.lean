/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Extension
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Holder

/-!
# Integration by parts on a half-space, and functions of zero trace

Let `H = TauCeti.normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, with
boundary hyperplane `{a} × E` and outward unit normal `-e₁`. This file proves the Gauss–Green
formula on `H` for Sobolev functions, with the trace `TauCeti.W1p.halfSpaceTrace` as the boundary
term: for `u ∈ W^{1,p}(H)` with `1 ≤ p < ∞`, a compactly supported `C¹` function `χ` on `ℝ × E`,
and a direction `v`,

`∫_H (∂_v χ · u + χ · ⟪v, ∇u⟫) = -v.fst ∫_E (Tr u)(y) χ(a, y) dy`.

For `u` the restriction of a test function this is the classical divergence theorem on `H`, and
the trace is the boundary value that makes the formula persist on all of `W^{1,p}(H)`. Both sides
are continuous in `u`: the fixed factors built from `χ` lie in `Lᵠ` for the conjugate exponent
`q = ENNReal.conjExponent p`, so the integrals are `Lᵖ`–`Lᵠ` pairings. No finite-volume
assumption is needed, and at `p = 1` the conjugate exponent is `∞`.

The boundary term is exactly what obstructs extending `u` by zero. Extending `u` and `∇u` by zero
to `ℝ × E`, the left-hand side is the pairing that tests whether the extended gradient is the weak
gradient of the extended function; the right-hand side is the defect, a distribution supported on
the boundary `{a} × E`. So the extension by zero of `u` lies in `W^{1,p}(ℝ × E)` if and only if
`Tr u = 0`. This is the analytic half of the identification of the kernel of the trace with
`W^{1,p}_0(H)`: membership of the zero extension in `W^{1,p}(ℝ × E)` is the characterisation of
`W^{1,p}_0` used for domains with regular boundary.

## Main declarations

* `TauCeti.setIntegral_normalHalfSpace_fderiv_apply`: the divergence theorem on `H` for
  compactly supported `C¹` functions.
* `TauCeti.W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient`: the Gauss–Green formula on
  `H` for `u ∈ W^{1,p}(H)`, with the trace as boundary term.
* `TauCeti.W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero`: the extension by zero
  of `u ∈ W^{1,p}(H)` is a Sobolev function on `ℝ × E` if and only if the trace of `u` vanishes.

## References

* L. C. Evans, *Partial Differential Equations*, §5.5 (traces) and Appendix C.2 (the
  Gauss–Green theorem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.18.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ContDiff Distributions Gradient ENNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The smooth divergence theorem on a half-space -/

/-- **The divergence theorem on a half-space.** For a compactly supported `C¹` function `g` on
`ℝ × E` and a direction `v`, the integral of the directional derivative `∂_v g` over the half-space
`{x | a < x.fst}` is the boundary integral of `g` over `{a} × E`, weighted by `⟪v, -e₁⟫ = -v.fst`,
the normal component of `v` along the outward unit normal. -/
theorem setIntegral_normalHalfSpace_fderiv_apply {g : WithLp 2 (ℝ × E) → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (a : ℝ) (v : WithLp 2 (ℝ × E)) :
    ∫ x in normalHalfSpace (E := E) a, fderiv ℝ g x v =
      -(v.fst * ∫ y : E, g (WithLp.toLp 2 (a, y))) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hdc (d : WithLp 2 (ℝ × E)) : Continuous fun x ↦ fderiv ℝ g x d :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint (d : WithLp 2 (ℝ × E)) :
      Integrable (fun z : ℝ × E ↦ fderiv ℝ g (WithLp.toLp 2 z) d)
        ((volume.restrict (Ioi a)).prod volume) := by
    have h : Integrable (fun x ↦ fderiv ℝ g x d) volume :=
      (hdc d).integrable_of_hasCompactSupport (hgc.fderiv_apply (𝕜 := ℝ) d)
    have hprod :=
      (WithLp.volume_preserving_toLp ℝ E).integrable_comp h.aestronglyMeasurable |>.mpr h
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hprod.integrableOn
  -- Pass to product coordinates.
  have hcoord : ∫ x in normalHalfSpace (E := E) a, fderiv ℝ g x v =
      ∫ z, fderiv ℝ g (WithLp.toLp 2 z) v ∂((volume.restrict (Ioi a)).prod volume) := by
    have hH : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
        {x | a < (WithLp.ofLp x).1} := Set.ext fun x ↦ by simp
    rw [Measure.restrict_prod_eq_prod_univ, Set.prod_univ, hH]
    simpa only [Measure.volume_eq_prod, Set.preimage_ofPred_eq, WithLp.ofLp_toLp, Set.Ioi] using
      ((WithLp.volume_preserving_toLp ℝ E).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding
        (fun x ↦ fderiv ℝ g x v) {x | a < (WithLp.ofLp x).1}).symm
  -- Split the direction into its normal and tangential parts.
  have hsplit (z : ℝ × E) : fderiv ℝ g (WithLp.toLp 2 z) v =
      v.fst * fderiv ℝ g (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E))) +
        fderiv ℝ g (WithLp.toLp 2 z) (WithLp.toLp 2 (0, v.snd)) := by
    have hv : v = v.fst • WithLp.toLp 2 (1, (0 : E)) + WithLp.toLp 2 (0, v.snd) := by
      cases v; simp [← WithLp.toLp_smul, ← WithLp.toLp_add]
    conv_lhs => rw [hv]
    rw [map_add, map_smul, smul_eq_mul]
  -- The normal part: the fundamental theorem of calculus on each normal line.
  have hnormal : ∫ z, fderiv ℝ g (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E)))
      ∂((volume.restrict (Ioi a)).prod volume) = -∫ y : E, g (WithLp.toLp 2 (a, y)) := by
    rw [integral_prod_symm _ (hint _), ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    have he : IsClosedEmbedding (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
      (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
        (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft y)
          (isClosedMap_prodMk_right y))
    have hline : ContDiff ℝ 1 (fun t : ℝ ↦ g (WithLp.toLp 2 (t, y))) :=
      hg.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
        (contDiff_id.prodMk contDiff_const))
    rw [← (hgc.comp_isClosedEmbedding he).integral_Ioi_deriv_eq hline a]
    exact integral_congr_ae (Eventually.of_forall fun t ↦
      ((hasDerivAt_comp_toLp_fst (hgd _)).deriv).symm)
  -- The tangential part: on each slice `{t} × E` it integrates to zero.
  have htangent : ∫ z, fderiv ℝ g (WithLp.toLp 2 z) (WithLp.toLp 2 (0, v.snd))
      ∂((volume.restrict (Ioi a)).prod volume) = 0 := by
    rw [integral_prod _ (hint _)]
    refine (integral_congr_ae (Eventually.of_forall fun t ↦ ?_)).trans (integral_zero _ _)
    have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (t, y)) :=
      (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
        (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight t)
          (isClosedMap_prodMk_left t))
    have hslice : ContDiff ℝ 1 (fun y : E ↦ g (WithLp.toLp 2 (t, y))) :=
      hg.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
        (contDiff_const.prodMk contDiff_id))
    have hsc := hgc.comp_isClosedEmbedding he
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ : E ↦ (1 : ℝ)) (g := fun y : E ↦ g (WithLp.toLp 2 (t, y))) (v := v.snd)
      (by simp) (by simpa using ((hslice.continuous_fderiv one_ne_zero).clm_apply
        continuous_const).integrable_of_hasCompactSupport (hsc.fderiv_apply (𝕜 := ℝ) v.snd))
      (by simpa using hslice.continuous.integrable_of_hasCompactSupport hsc)
      (fun _ _ ↦ differentiableAt_const _)
      (fun y _ ↦ hslice.differentiable one_ne_zero y)
    simp only [one_mul] at hibp
    simp only [← fderiv_comp_toLp_snd (hgd _)]
    simpa using hibp
  rw [hcoord, integral_congr_ae (Eventually.of_forall hsplit),
    integral_add ((hint _).const_mul _) (hint _), integral_const_mul, hnormal, htangent]
  ring

/-! ### Integration by parts against the trace -/

section GaussGreen

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bulk side of the Gauss–Green formula is a continuous function of `w ∈ W^{1,p}(H)`: it pairs
the value and gradient of `w` with fixed `Lᵠ` factors built from `χ`, for the conjugate
exponent `q`. -/
private theorem continuous_halfSpaceBulkPairing (a : ℝ)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p ↦
      ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value w x + χ x * ⟪v, W1p.gradient w x⟫_ℝ) := by
  let _ : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  have hdc : Continuous fun x ↦ fderiv ℝ χ x v :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hD : MemLp (fun x ↦ fderiv ℝ χ x v) p.conjExponent
      (volume.restrict (normalHalfSpace (E := E) a)) :=
    (hdc.memLp_of_hasCompactSupport (hχc.fderiv_apply (𝕜 := ℝ) v)).restrict _
  have hG : MemLp (fun x ↦ χ x • v) p.conjExponent
      (volume.restrict (normalHalfSpace (E := E) a)) :=
    ((hχ.continuous.smul continuous_const).memLp_of_hasCompactSupport hχc.smul_right).restrict _
  let D := (ContinuousLinearMap.mul ℝ ℝ).lpPairing _ p.conjExponent p (hD.toLp _)
  let G := (innerSL ℝ).lpPairing _ p.conjExponent p (hG.toLp _)
  have hL (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p) :
      ∫ x in normalHalfSpace (E := E) a,
          (fderiv ℝ χ x v * W1p.value w x + χ x * ⟪v, W1p.gradient w x⟫_ℝ) =
        D (W1p.value w) + G (W1p.gradient w) := by
    simp only [D, G, ContinuousLinearMap.lpPairing_eq_integral]
    rw [← integral_add
      (memLp_one_iff_integrable.mp <| (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
        (Lp.memLp (hD.toLp _)) (Lp.memLp (W1p.value w)))
      (memLp_one_iff_integrable.mp <| (innerSL ℝ).memLp_of_bilin 1
        (Lp.memLp (hG.toLp _)) (Lp.memLp (W1p.gradient w)))]
    apply integral_congr_ae
    filter_upwards [hD.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
    simp only [ContinuousLinearMap.mul_apply', h1, h2]
    rw [innerSL_apply_apply]
    exact congrArg ((fderiv ℝ χ x v * W1p.value w x) + ·)
      (real_inner_smul_left v (W1p.gradient w x) (χ x)).symm
  simp_rw [hL]
  exact ((D.comp (W1p.valueL (p := p))) +
    (G.comp (W1p.gradientL (p := p)))).continuous.congr fun w ↦ by
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        W1p.valueL_apply, W1p.gradientL_apply]

/-- The boundary side of the Gauss–Green formula is a continuous function of `w ∈ W^{1,p}(ℝ × E)`:
it pairs the hyperplane trace of `w` with the restriction of `χ` to `{a} × E`, a fixed `Lᵠ`
function. -/
private theorem continuous_hyperplaneBoundaryPairing (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p ↦
      ∫ y : E, W1p.hyperplaneTrace hp a w y * χ (WithLp.toLp 2 (a, y)) := by
  let _ : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (a, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))
  have hT : MemLp (fun y : E ↦ χ (WithLp.toLp 2 (a, y))) p.conjExponent volume :=
    (hχ.comp he.continuous).memLp_of_hasCompactSupport
      (hχc.comp_isClosedEmbedding he)
  let T := (ContinuousLinearMap.mul ℝ ℝ).lpPairing volume p.conjExponent p (hT.toLp _)
  have hR (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
      ∫ y : E, W1p.hyperplaneTrace hp a w y * χ (WithLp.toLp 2 (a, y)) =
        T (W1p.hyperplaneTrace hp a w) := by
    simp only [T, ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with y hy
    simp [hy, mul_comm]
  simp_rw [hR]
  exact T.continuous.comp (W1p.hyperplaneTrace hp a).continuous

/-- The Gauss–Green formula for the restriction to `H` of a whole-space Sobolev function, with the
hyperplane trace as boundary term. Both sides are continuous in `u`, and on test functions it is
the smooth divergence theorem. -/
private theorem setIntegral_restrictL_fderiv_mul_value_add_mul_inner_gradient
    (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ) (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top u) x +
          χ x * ⟪v, W1p.gradient (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top u) x⟫_ℝ) =
      -(v.fst * ∫ y : E, W1p.hyperplaneTrace hp a u y * χ (WithLp.toLp 2 (a, y))) := by
  -- Whole-space test functions are dense; both sides are continuous `Lᵖ`–`Lᵠ` pairings.
  have hcL : Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p ↦
      ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top w) x +
          χ x * ⟪v, W1p.gradient (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top w) x⟫_ℝ) :=
    (continuous_halfSpaceBulkPairing a hχ hχc v).comp
      (W1p.restrictL (U := normalHalfSpace (E := E) a) (Omega := ⊤)
        (p := p) (mu := volume) le_top).continuous
  have hcR : Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p ↦
      -(v.fst * ∫ y : E, W1p.hyperplaneTrace hp a w y * χ (WithLp.toLp 2 (a, y))) :=
    (continuous_const.mul (continuous_hyperplaneBoundaryPairing hp a hχ.continuous hχc)).neg
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := p) hp).induction_on u
    (isClosed_eq hcL hcR) fun ψ ↦ ?_
  have hψ : ContDiff ℝ 1 (ψ : WithLp 2 (ℝ × E) → ℝ) := ψ.contDiff.of_le (by simp)
  have hval := W1p.value_ofTestFunctionₗ (mu := volume) (Omega := ⊤) (p := p) ψ
  have hgrad := W1p.gradient_ofTestFunctionₗ (mu := volume) (Omega := ⊤) (p := p) ψ
  calc
    _ = ∫ x in normalHalfSpace (E := E) a, fderiv ℝ (fun x ↦ χ x * ψ x) x v := by
      apply integral_congr_ae
      have hv := testFunctionLp_apply_ae (mu := volume) p ψ
      have hg := gradientTestFunctionLp_apply_ae (mu := volume) p ψ
      simp only [Opens.coe_top, Measure.restrict_univ] at hv hg
      filter_upwards [W1p.value_restrictL_ae le_top (W1p.ofTestFunctionₗ volume ⊤ p ψ),
        W1p.gradient_restrictL_ae le_top (W1p.ofTestFunctionₗ volume ⊤ p ψ),
        ae_restrict_of_ae hv, ae_restrict_of_ae hg] with x hx hy hx' hy'
      rw [hx, hy, hval, hgrad, hx', hy',
        fderiv_fun_mul (hχ.differentiable one_ne_zero x) (hψ.differentiable one_ne_zero x),
        real_inner_comm, inner_gradient_left]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    _ = -(v.fst * ∫ y : E, χ (WithLp.toLp 2 (a, y)) * ψ (WithLp.toLp 2 (a, y))) :=
      setIntegral_normalHalfSpace_fderiv_apply (hχ.mul hψ) hχc.mul_right a v
    _ = _ := by
      congr 2
      apply integral_congr_ae
      filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a ψ] with y hy
      rw [hy, mul_comm]

/-- **Integration by parts on a half-space, with the trace as boundary term.** Let
`H = {x | a < x.fst}`, let `1 ≤ p < ∞` and let `u ∈ W^{1,p}(H)`. For every compactly supported
`C¹` function `χ` on the whole space `ℝ × E` and every direction `v`,

`∫_H (∂_v χ · u + χ · ⟪v, ∇u⟫) = -v₁ ∫_E (Tr u)(y) χ(a, y) dy`,

where `Tr u = TauCeti.W1p.halfSpaceTrace hp a u` and `v₁ = v.fst` is the normal component of `v`.
The outward unit normal of `H` is `-e₁`, so this is the Gauss–Green formula `∫_H ∂_v(χ u) =
∫_{∂H} χ u ⟪v, ν⟫` for Sobolev functions. Tangential directions produce no boundary term. -/
theorem W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value u x + χ x * ⟪v, W1p.gradient u x⟫_ℝ) =
      -(v.fst * ∫ y : E, W1p.halfSpaceTrace hp a u y * χ (WithLp.toLp 2 (a, y))) := by
  simpa only [W1p.restrictL_extendByReflectionL, ← W1p.halfSpaceTrace_apply] using
    setIntegral_restrictL_fderiv_mul_value_add_mul_inner_gradient hp a
      (W1p.extendByReflectionL a u) hχ hχc v

end GaussGreen

/-! ### Functions of zero trace -/

/-- Extending the value and gradient by zero restricts the weak-derivative pairing to
the half-space, independently of the exponent or trace operator. -/
private theorem setIntegral_extendByZeroₗᵢ_eq {p : ENNReal} [Fact (1 ≤ p)] (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) (v : WithLp 2 (ℝ × E)) :
    ∫ x in (⊤ : Opens (WithLp 2 (ℝ × E))),
        (lineDeriv ℝ (φ : WithLp 2 (ℝ × E) → ℝ) x v *
            Sobolev1JetLp.value (Sobolev1JetLp.extendByZeroₗᵢ le_top
              (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E)))
                (normalHalfSpace (E := E) a) p)) x +
          φ x * Sobolev1JetLp.candidateWeakFDeriv (Sobolev1JetLp.extendByZeroₗᵢ le_top
              (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E)))
                (normalHalfSpace (E := E) a) p))
            x v) =
      ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ (φ : WithLp 2 (ℝ × E) → ℝ) x v * W1p.value u x +
          φ x * ⟪v, W1p.gradient u x⟫_ℝ) := by
  have hH := (normalHalfSpace (E := E) a).isOpen.measurableSet
  have hφ : ContDiff ℝ 1 (φ : WithLp 2 (ℝ × E) → ℝ) := φ.contDiff.of_le (by simp)
  have htop := (⊤ : Opens (WithLp 2 (ℝ × E))).isOpen.measurableSet
  have hsub : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ⊆
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) := subset_univ _
  have hval := (ae_restrict_iff' htop).1 (coeFn_extendByZeroLpₗᵢ ℝ hH hsub (W1p.value u))
  have hgrad := (ae_restrict_iff' htop).1 (coeFn_extendByZeroLpₗᵢ ℝ hH hsub (W1p.gradient u))
  rw [← integral_indicator hH, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      (hx (by simp)).elim]
  apply integral_congr_ae
  filter_upwards [hval, hgrad] with x h1 h2
  rw [Sobolev1JetLp.candidateWeakFDeriv_apply, Sobolev1JetLp.value_extendByZeroₗᵢ,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.value_coe, ← W1p.gradient_coe]
  rw [h1 (by simp), h2 (by simp), (hφ.differentiable one_ne_zero x).lineDeriv_eq_fderiv]
  by_cases hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, mul_zero, inner_zero_right, add_zero]

/-- Given a Gauss–Green identity with an `Lᵖ` boundary value, zero extension is Sobolev
exactly when that boundary value vanishes. Product test functions detect its normal pairing. -/
private theorem extendByZeroₗᵢ_mem_w1pSubmodule_iff_boundary_eq_zero
    {p : ENNReal} [Fact (1 ≤ p)] (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p)
    (T : Lp ℝ p (volume : Measure E))
    (hGG : ∀ (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) (v : WithLp 2 (ℝ × E)),
      ∫ x in normalHalfSpace (E := E) a,
          (fderiv ℝ (φ : WithLp 2 (ℝ × E) → ℝ) x v * W1p.value u x +
            φ x * ⟪v, W1p.gradient u x⟫_ℝ) =
        -(v.fst * ∫ y : E, T y * φ (WithLp.toLp 2 (a, y)))) :
    Sobolev1JetLp.extendByZeroₗᵢ le_top
        (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p) ∈
          w1pSubmodule volume ⊤ p ↔ T = 0 := by
  rw [mem_w1pSubmodule_iff]
  simp only [setIntegral_extendByZeroₗᵢ_eq, hGG]
  constructor
  · intro h
    -- Testing in the normal direction against `η(x.fst) ζ(x.snd)` with `η(a) = 1`, the trace
    -- integrates to zero against every test function `ζ` on `E`.
    have hζ (ζ : E → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) :
        ∫ y, ζ y • T y = 0 := by
      let η : ContDiffBump a := ⟨1, 2, one_pos, one_lt_two⟩
      have hfst : ContDiff ℝ ∞ fun x : WithLp 2 (ℝ × E) ↦ x.fst :=
        contDiff_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff
      have hsnd : ContDiff ℝ ∞ fun x : WithLp 2 (ℝ × E) ↦ x.snd :=
        contDiff_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff
      have hc : HasCompactSupport fun x : WithLp 2 (ℝ × E) ↦ η x.fst * ζ x.snd := by
        refine HasCompactSupport.intro ((WithLp.homeomorphProd 2 ℝ E).isCompact_preimage.2
          (η.hasCompactSupport.isCompact.prod hζc.isCompact)) fun x hx ↦ ?_
        simp only [mem_preimage, mem_prod, not_and_or] at hx
        rcases hx with hx | hx
        · exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hx) _
        · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hx)
      let φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) :=
        ⟨fun x ↦ η x.fst * ζ x.snd, (η.contDiff.comp hfst).mul (hζ.comp hsnd), hc,
          fun _ _ ↦ trivial⟩
      have h1 := h φ (WithLp.toLp 2 (1, 0))
      have hη : η a = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
      simp only [WithLp.toLp_fst, one_mul, neg_eq_zero] at h1
      have hφa (y : E) : φ (WithLp.toLp 2 (a, y)) = ζ y := by
        have hcoe : (φ : WithLp 2 (ℝ × E) → ℝ) = fun x ↦ η x.fst * ζ x.snd := TestFunction.coe_mk
        simp only [hcoe, WithLp.toLp_fst, WithLp.toLp_snd, hη, one_mul]
      rw [← h1]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      dsimp only
      rw [hφa, smul_eq_mul, mul_comm]
    have hloc : LocallyIntegrable T volume :=
      (Lp.memLp _).locallyIntegrable Fact.out
    apply Lp.ext
    filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hζ, Lp.coeFn_zero ℝ p
      (volume : Measure E)] with y hy h0
    rw [hy, h0, Pi.zero_apply]
  · intro h φ v
    rw [h, neg_eq_zero, mul_eq_zero]
    right
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [Lp.coeFn_zero ℝ p (volume : Measure E)] with y hy
    rw [hy, Pi.zero_apply, zero_mul]

/-- **The functions of zero trace on a half-space are those that extend by zero.** Let
`1 ≤ p < ∞` and `u ∈ W^{1,p}(H)` on the half-space `H = {x | a < x.fst}`. Its extension by zero is
weakly differentiable on the whole space, that is, lies in `W^{1,p}(ℝ × E)` with weak gradient the
extension by zero of `∇u`, if and only if the trace of `u` on `{a} × E` vanishes. -/
theorem W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p) :
    Sobolev1JetLp.extendByZeroₗᵢ le_top
        (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) p) ∈
          w1pSubmodule volume ⊤ p ↔ W1p.halfSpaceTrace hp a u = 0 :=
  extendByZeroₗᵢ_mem_w1pSubmodule_iff_boundary_eq_zero a u (W1p.halfSpaceTrace hp a u)
    fun φ v ↦ W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient hp a u
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport v

end TauCeti
