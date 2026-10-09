/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Extension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts on a half-space, and functions of zero trace

Let `H = TauCeti.normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, with
boundary hyperplane `{a} × E` and outward unit normal `-e₁`. This file proves the Gauss–Green
formula on `H` for Sobolev functions, with the trace `TauCeti.W1p.halfSpaceTrace` as the boundary
term: for `u ∈ H¹(H)`, a compactly supported `C¹` function `χ` on `ℝ × E`, and a direction `v`,

`∫_H (∂_v χ · u + χ · ⟪v, ∇u⟫) = -v.fst ∫_E (Tr u)(y) χ(a, y) dy`.

For `u` the restriction of a test function this is the classical divergence theorem on `H`,
proved by Fubini's theorem: the fundamental theorem of calculus on each normal line produces the
boundary term, and the tangential derivatives integrate to zero on each slice `{t} × E`. Both
sides are continuous in `u ∈ H¹(H)`, because the trace is, and restrictions of test functions are
dense in `H¹(H)` by the reflection extension, so the formula holds on all of `H¹(H)`.

As a consequence, the boundary term is exactly what obstructs extending `u` by zero: the extension
by zero of `u` lies in `H¹(ℝ × E)` if and only if `Tr u = 0`. This is the analytic half of the
identification of the kernel of the trace with `H¹₀(H)`: membership of the zero extension in
`H¹(ℝ × E)` is the characterisation of `H¹₀` used for domains with regular boundary.

## Main declarations

* `TauCeti.setIntegral_normalHalfSpace_fderiv_apply`: the divergence theorem on `H` for
  compactly supported `C¹` functions.
* `TauCeti.W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient`: the Gauss–Green formula on
  `H` for `u ∈ H¹(H)`, with the trace as boundary term.
* `TauCeti.W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero`: the extension by zero
  of `u ∈ H¹(H)` is a Sobolev function on `ℝ × E` if and only if the trace of `u` vanishes.

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Along the normal line through `(t, y)`, the derivative of a differentiable function is its
derivative in the normal direction `e₁`. -/
private theorem hasDerivAt_comp_toLp_fst {g : WithLp 2 (ℝ × E) → ℝ} (hg : Differentiable ℝ g)
    (t : ℝ) (y : E) :
    HasDerivAt (fun s : ℝ ↦ g (WithLp.toLp 2 (s, y)))
      (fderiv ℝ g (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (1, (0 : E)))) t := by
  have hp : HasDerivAt (fun s : ℝ ↦ WithLp.toLp 2 (s, y)) (WithLp.toLp 2 (1, (0 : E))) t :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact (hg _).hasFDerivAt.comp_hasDerivAt t hp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- On the slice `{t} × E`, the derivative of a differentiable function in a direction `w` of `E`
is its derivative in the tangential direction `(0, w)`. -/
private theorem fderiv_comp_toLp_snd {g : WithLp 2 (ℝ × E) → ℝ} (hg : Differentiable ℝ g)
    (t : ℝ) (y w : E) :
    fderiv ℝ (fun z : E ↦ g (WithLp.toLp 2 (t, z))) y w =
      fderiv ℝ g (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (0, w)) := by
  have hp : HasFDerivAt (fun z : E ↦ WithLp.toLp 2 (t, z))
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))) y :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt).comp y
      ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have h : HasFDerivAt (fun z : E ↦ g (WithLp.toLp 2 (t, z))) _ y := (hg _).hasFDerivAt.comp y hp
  rw [h.fderiv]
  simp

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
      ((hasDerivAt_comp_toLp_fst hgd t y).deriv).symm)
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
    simp only [← fderiv_comp_toLp_snd hgd]
    simpa using hibp
  rw [hcoord, integral_congr_ae (Eventually.of_forall hsplit),
    integral_add ((hint _).const_mul _) (hint _), integral_const_mul, hnormal, htangent]
  ring

/-! ### Integration by parts against the trace -/

/-- The restriction of a whole-space test function to the half-space has the test function as
its value and its gradient as weak gradient, and its trace is its restriction to the boundary. -/
private theorem restrictL_ofTestFunctionₗ_ae (a : ℝ)
    (ψ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    (W1p.value (W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (W1p.ofTestFunctionₗ volume ⊤ 2 ψ)) =ᵐ[volume.restrict (normalHalfSpace (E := E) a)]
        (ψ : WithLp 2 (ℝ × E) → ℝ)) ∧
      (W1p.gradient (W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (W1p.ofTestFunctionₗ volume ⊤ 2 ψ)) =ᵐ[volume.restrict (normalHalfSpace (E := E) a)]
        ∇ (ψ : WithLp 2 (ℝ × E) → ℝ)) ∧
      (W1p.halfSpaceTrace a (W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (W1p.ofTestFunctionₗ volume ⊤ 2 ψ)) =ᵐ[volume] fun y ↦ ψ (WithLp.toLp 2 (a, y))) := by
  refine ⟨(W1p.value_restrictL_ae le_top _).trans ?_, (W1p.gradient_restrictL_ae le_top _).trans ?_,
    ?_⟩
  · rw [W1p.value_ofTestFunctionₗ]
    have hψ := testFunctionLp_apply_ae (mu := volume) 2 ψ
    simp only [Opens.coe_top, Measure.restrict_univ] at hψ
    exact hψ.filter_mono (ae_mono Measure.restrict_le_self)
  · rw [W1p.gradient_ofTestFunctionₗ]
    have hψ := gradientTestFunctionLp_apply_ae (mu := volume) 2 ψ
    simp only [Opens.coe_top, Measure.restrict_univ] at hψ
    exact hψ.filter_mono (ae_mono Measure.restrict_le_self)
  · rw [W1p.halfSpaceTrace_restrictL]
    exact W1p.hyperplaneTrace_ofTestFunction_apply_ae a ψ

/-- **Integration by parts on a half-space, with the trace as boundary term.** Let
`H = {x | a < x.fst}` and let `u ∈ H¹(H)`. For every compactly supported `C¹` function `χ` on the
whole space `ℝ × E` and every direction `v`,

`∫_H (∂_v χ · u + χ · ⟪v, ∇u⟫) = -v₁ ∫_E (Tr u)(y) χ(a, y) dy`,

where `Tr u = TauCeti.W1p.halfSpaceTrace a u` and `v₁ = v.fst` is the normal component of `v`.
The outward unit normal of `H` is `-e₁`, so this is the Gauss–Green formula `∫_H ∂_v(χ u) =
∫_{∂H} χ u ⟪v, ν⟫` for Sobolev functions. Tangential directions produce no boundary term. -/
theorem W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value u x + χ x * ⟪v, W1p.gradient u x⟫_ℝ) =
      -(v.fst * ∫ y : E, W1p.halfSpaceTrace a u y * χ (WithLp.toLp 2 (a, y))) := by
  have hle : normalHalfSpace (E := E) a ≤ ⊤ := le_top
  have hdc : Continuous fun x ↦ fderiv ℝ χ x v :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (a, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))
  -- The three pairings, as `L²` inner products with fixed functions built from `χ`.
  have hD : MemLp (fun x ↦ fderiv ℝ χ x v) 2 (volume.restrict (normalHalfSpace (E := E) a)) :=
    (hdc.memLp_of_hasCompactSupport (hχc.fderiv_apply (𝕜 := ℝ) v)).restrict _
  have hG : MemLp (fun x ↦ χ x • v) 2 (volume.restrict (normalHalfSpace (E := E) a)) :=
    ((hχ.continuous.smul continuous_const).memLp_of_hasCompactSupport hχc.smul_right).restrict _
  have hT : MemLp (fun y : E ↦ χ (WithLp.toLp 2 (a, y))) 2 volume :=
    (hχ.continuous.comp he.continuous).memLp_of_hasCompactSupport
      (hχc.comp_isClosedEmbedding he)
  have hL (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
      ∫ x in normalHalfSpace (E := E) a,
          (fderiv ℝ χ x v * W1p.value w x + χ x * ⟪v, W1p.gradient w x⟫_ℝ) =
        ⟪hD.toLp _, W1p.value w⟫_ℝ + ⟪hG.toLp _, W1p.gradient w⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def,
      ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [hD.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
    rw [h1, h2, real_inner_smul_left, real_inner_comm, RCLike.inner_apply, conj_trivial]
    ring
  have hR (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
      ∫ y : E, W1p.halfSpaceTrace a w y * χ (WithLp.toLp 2 (a, y)) =
        ⟪hT.toLp _, W1p.halfSpaceTrace a w⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT.coeFn_toLp] with y hy
    simp [hy, RCLike.inner_apply]
  rw [hL, hR]
  -- Restrictions of whole-space test functions are dense in `H¹(H)`.
  have hsurj : Function.Surjective (W1p.restrictL hle (mu := volume) (p := 2)) := fun w ↦
    ⟨W1p.extendByReflectionL a w, W1p.restrictL_extendByReflectionL a w⟩
  have hdense := hsurj.denseRange.comp
    (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num))
    (W1p.restrictL hle).continuous
  have hcL : Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2 ↦
      ⟪hD.toLp _, W1p.value w⟫_ℝ + ⟪hG.toLp _, W1p.gradient w⟫_ℝ := by
    simpa only [W1p.valueL_apply, W1p.gradientL_apply] using
      (continuous_const.inner (W1p.valueL (mu := volume) (Omega := normalHalfSpace (E := E) a)
        (p := 2)).continuous).fun_add
        (continuous_const.inner (W1p.gradientL (mu := volume)
          (Omega := normalHalfSpace (E := E) a) (p := 2)).continuous)
  have hcR : Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2 ↦
      -(v.fst * ⟪hT.toLp _, W1p.halfSpaceTrace a w⟫_ℝ) :=
    (continuous_const.mul (continuous_const.inner (W1p.halfSpaceTrace a).continuous)).neg
  refine hdense.induction_on u (isClosed_eq hcL hcR) fun ψ ↦ ?_
  rw [Function.comp_apply]
  refine (hL _).symm.trans (Eq.trans ?_ (congrArg (fun r ↦ -(v.fst * r)) (hR _)))
  have hψ : ContDiff ℝ 1 (ψ : WithLp 2 (ℝ × E) → ℝ) := ψ.contDiff.of_le (by simp)
  have hq := restrictL_ofTestFunctionₗ_ae (E := E) a ψ
  -- On test functions both sides are classical, and agree by the smooth divergence theorem.
  calc
    _ = ∫ x in normalHalfSpace (E := E) a, fderiv ℝ (fun x ↦ χ x * ψ x) x v := by
      refine integral_congr_ae ?_
      filter_upwards [hq.1, hq.2.1] with x h1 h2
      rw [h1, h2, fderiv_fun_mul (hχ.differentiable one_ne_zero x)
        (hψ.differentiable one_ne_zero x), real_inner_comm, inner_gradient_left]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    _ = -(v.fst * ∫ y : E, χ (WithLp.toLp 2 (a, y)) * ψ (WithLp.toLp 2 (a, y))) :=
      setIntegral_normalHalfSpace_fderiv_apply (hχ.mul hψ) hχc.mul_right a v
    _ = _ := by
      congr 2
      refine integral_congr_ae ?_
      filter_upwards [hq.2.2] with y hy
      rw [hy, mul_comm]

/-! ### Functions of zero trace -/

/-- The weak-derivative pairing of the extension by zero of `u` against a whole-space test
function is the boundary term of the integration-by-parts formula. -/
private theorem setIntegral_extendByZeroₗᵢ_eq (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) (v : WithLp 2 (ℝ × E)) :
    ∫ x in (⊤ : Opens (WithLp 2 (ℝ × E))),
        (lineDeriv ℝ (φ : WithLp 2 (ℝ × E) → ℝ) x v *
            Sobolev1JetLp.value (Sobolev1JetLp.extendByZeroₗᵢ
              (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
              (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2)) x +
          φ x * Sobolev1JetLp.candidateWeakFDeriv (Sobolev1JetLp.extendByZeroₗᵢ
              (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
              (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2))
            x v) =
      -(v.fst * ∫ y : E, W1p.halfSpaceTrace a u y * φ (WithLp.toLp 2 (a, y))) := by
  have hH : MeasurableSet (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    (normalHalfSpace (E := E) a).isOpen.measurableSet
  have hφ : ContDiff ℝ 1 (φ : WithLp 2 (ℝ × E) → ℝ) := φ.contDiff.of_le (by simp)
  have htop : MeasurableSet ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) :=
    (⊤ : Opens (WithLp 2 (ℝ × E))).isOpen.measurableSet
  have hsub : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ⊆
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) :=
    SetLike.coe_subset_coe.mpr le_top
  have hval := (ae_restrict_iff' htop).1 (coeFn_extendByZeroLpₗᵢ ℝ hH hsub (W1p.value u))
  have hgrad := (ae_restrict_iff' htop).1 (coeFn_extendByZeroLpₗᵢ ℝ hH hsub (W1p.gradient u))
  rw [← W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient a u hφ φ.hasCompactSupport v,
    ← integral_indicator hH, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      (hx (by simp)).elim]
  refine integral_congr_ae ?_
  filter_upwards [hval, hgrad] with x h1 h2
  rw [Sobolev1JetLp.candidateWeakFDeriv_apply, Sobolev1JetLp.value_extendByZeroₗᵢ,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.value_coe, ← W1p.gradient_coe]
  rw [h1 (by simp), h2 (by simp), (hφ.differentiable one_ne_zero x).lineDeriv_eq_fderiv]
  by_cases hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, mul_zero, inner_zero_right, add_zero]

/-- **The functions of zero trace on a half-space are those that extend by zero.** Let
`u ∈ H¹(H)` on the half-space `H = {x | a < x.fst}`. Its extension by zero is weakly
differentiable on the whole space, that is, lies in `H¹(ℝ × E)` with weak gradient the extension
by zero of `∇u`, if and only if the trace of `u` on `{a} × E` vanishes. -/
theorem W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    Sobolev1JetLp.extendByZeroₗᵢ (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) ∈
          w1pSubmodule volume ⊤ 2 ↔
      W1p.halfSpaceTrace a u = 0 := by
  -- The weak-derivative identities for the extension are the integration-by-parts formula, whose
  -- boundary term is the trace.
  rw [mem_w1pSubmodule_iff]
  simp only [setIntegral_extendByZeroₗᵢ_eq]
  constructor
  · intro h
    -- Testing in the normal direction against `η(x.fst) ζ(x.snd)` with `η(a) = 1`, the trace
    -- integrates to zero against every test function `ζ` on `E`.
    have hζ (ζ : E → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) :
        ∫ y, ζ y • W1p.halfSpaceTrace a u y = 0 := by
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
    have hloc : LocallyIntegrable (W1p.halfSpaceTrace a u) volume :=
      (Lp.memLp _).locallyIntegrable (by norm_num)
    apply Lp.ext
    filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hζ, Lp.coeFn_zero ℝ 2
      (volume : Measure E)] with y hy h0
    rw [hy, h0, Pi.zero_apply]
  · intro h φ v
    rw [h, neg_eq_zero, mul_eq_zero]
    right
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure E)] with y hy
    rw [hy, Pi.zero_apply, zero_mul]

end TauCeti
