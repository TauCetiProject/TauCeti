/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter

/-!
# Variational formula, noninterval excess, and equality rigidity for Steiner perimeter

Let `E` be a finite-dimensional real inner product space, `e` a unit vector, and `s` a
null-measurable set of finite volume with Steiner symmetral `S_e s = steinerSymmetrization e he s`.
Write `L(y) = |{t | y + t • e ∈ s}|` for the section lengths on the orthogonal hyperplane
`(ℝ ∙ e)ᗮ` and `D = {y | 0 < |{t | y + t • e ∈ s}|}` for the positive-section set.

1. **Exact transverse variational formula for Steiner perimeter.** The perimeter `P(S_e s)` equals
   the supremum of `2 ∫_D √(1 - ‖φ‖²) + ∫ div φ (y) L(y) dy` over transverse test vector fields
   `φ ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)` satisfying `‖φ‖ ≤ 1` (`TauCeti.perimeter_steinerSymmetrization_eq_iSup`),
   with no finiteness assumption on `P(s)` or `P(S_e s)`.

2. **Scaled perimeter bound and Pythagorean noninterval excess.** Combining the variational formula
   with the localized noninterval-excess slicing inequality of
   `TauCeti.Analysis.BoundedVariation.Slicing.Excess` at rescaled test fields `(1 - δ) • φ` for
   `δ ∈ [0, 1]` shows that every null-measurable family `A ⊆ (ℝ ∙ e)ᗮ` of noninterval sections
   satisfies `(1 - δ) P(S_e s) + 2 √(2 δ - δ²) |A| ≤ P(s)`
   (`TauCeti.ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter`). Optimizing in `δ` gives
   the parameter-free Pythagorean excess inequality
   `P(S_e s)² + 4 |A|² ≤ P(s)²`
   (`TauCeti.perimeter_steinerSymmetrization_sq_add_four_mul_volume_sq_le`), which holds for the
   entire family of noninterval sections
   (`TauCeti.perimeter_steinerSymmetrization_sq_add_four_mul_volume_noninterval_sq_le`).

3. **Steiner equality forces interval sections.** When `P(s) < ∞` and `P(S_e s) = P(s)`, the excess
   term `4 |A|²` vanishes, so for almost every `y ∈ (ℝ ∙ e)ᗮ` the line section
   `{t | y + t • e ∈ s}` agrees almost everywhere with an order-connected set (an interval, possibly
   empty; `TauCeti.ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq`).
   Finiteness of `P(s)` is essential: both `P(s)` and `P(S_e s)` can be `∞` even when noninterval
   sections have positive transverse measure.

## Proof strategy

The lower bound `≥` in `TauCeti.perimeter_steinerSymmetrization_eq_iSup` is immediate from joint
slicing applied to `S_e s`. For the upper bound `≤`, if `|D| = ∞` then `φ = 0` already makes the
supremum `∞`. When `|D| < ∞`, we test `S_e s` against an arbitrary `ψ₀ ∈ 𝓓(⊤, E)` with
`‖ψ₀‖ ≤ 1` and regularize `L` by shrinking normalized bumps `L_k = ρ_k ⋆ L`. On the smooth
symmetric slab `{|t| < L_k(y) / 2}`, decomposing `div ψ₀` into horizontal divergence and vertical
derivative and integrating `(L_k / 2) A(y, L_k u / 2)` over `u ∈ (-1, 1)` rewrites
`∫_{|t| < L_k/2} div ψ₀` as `2 ∫ d_k - ∫ DL_k (b_k)`, where the boundary horizontal average `b_k`
and vertical half-difference `d_k` satisfy `‖b_k‖² + d_k² ≤ 1` everywhere. Moving `ρ_k` onto `b_k`
produces `φ_k = ρ_k ⋆ b_k ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)` with `‖φ_k‖² + (ρ_k ⋆ d_k)² ≤ 1`, while the off-`D`
contribution of `ρ_k ⋆ d_k` and the slab-replacement error vanish in `L¹` as `k → ∞`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593, §1.2 and Theorem 1.1.
* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
-/

public noncomputable section

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace TestFunction
open scoped Convolution ContDiff Distributions ENNReal RealInnerProductSpace Topology

namespace TauCeti

/-! ### Smooth symmetric slabs and mollified transverse test fields -/

section SmoothSymmetricSlab

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Decompose `divergenceCLM ψ₀` in orthogonal line coordinates into the hyperplane divergence of
its transverse projection plus the longitudinal derivative along `e`. -/
private theorem divergenceCLM_orthogonalLine_eq (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    divergenceCLM ψ₀ ((y : E) + t • e) =
      traceCLM ℝ (ℝ ∙ e)ᗮ
        (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => ((orthogonalLineEquiv e he).symm (ψ₀ ((z : E) + t • e))).1)
          y) +
        deriv (fun s : ℝ => ⟪e, ψ₀ ((y : E) + s • e)⟫) t := by
  set L := orthogonalLineEquiv e he
  let π : E →L[ℝ] (ℝ ∙ e)ᗮ :=
    (ContinuousLinearMap.fst ℝ (ℝ ∙ e)ᗮ ℝ).comp L.symm.toContinuousLinearMap
  set g : E → (ℝ ∙ e)ᗮ := fun x => π (ψ₀ x)
  have hdecomp : (ψ₀ : E → E) = fun x => (ℝ ∙ e)ᗮ.subtypeL (g x) + ⟪e, ψ₀ x⟫ • e := by
    ext x
    have hx := L.apply_symm_apply (ψ₀ x)
    rw [← Prod.eta (p := L.symm (ψ₀ x)), orthogonalLineEquiv_apply,
      orthogonalLineEquiv_symm_snd] at hx
    exact hx.symm
  set x₀ : E := (y : E) + t • e
  have hψd : DifferentiableAt ℝ (ψ₀ : E → E) x₀ := ψ₀.contDiff.differentiable (by simp) x₀
  have hgd : DifferentiableAt ℝ g x₀ := π.differentiableAt.comp x₀ hψd
  have h1d : DifferentiableAt ℝ (fun x => (ℝ ∙ e)ᗮ.subtypeL (g x)) x₀ :=
    (ℝ ∙ e)ᗮ.subtypeL.differentiableAt.comp x₀ hgd
  have hinner : DifferentiableAt ℝ (fun x => ⟪e, ψ₀ x⟫) x₀ :=
    (innerSL ℝ e).differentiableAt.comp x₀ hψd
  conv_lhs =>
    rw [divergenceCLM_apply, hdecomp, fderiv_fun_add h1d (hinner.smul_const e),
      ContinuousLinearMap.toLinearMap_add, map_add, trace_fderiv_smul_const hinner e]
  congr 1
  · have hf1 : fderiv ℝ (fun x => (ℝ ∙ e)ᗮ.subtypeL (g x)) x₀ =
        (ℝ ∙ e)ᗮ.subtypeL.comp (fderiv ℝ g x₀) :=
      ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt.comp x₀ hgd.hasFDerivAt).fderiv
    have haff : HasFDerivAt (fun z : (ℝ ∙ e)ᗮ => (z : E) + t • e) (ℝ ∙ e)ᗮ.subtypeL y :=
      ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt (x := y)).add_const (t • e)
    have hf2 : fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => g ((z : E) + t • e)) y =
        (fderiv ℝ g x₀).comp (ℝ ∙ e)ᗮ.subtypeL :=
      (HasFDerivAt.comp (f := fun z : (ℝ ∙ e)ᗮ => (z : E) + t • e) y
        hgd.hasFDerivAt haff).fderiv
    change LinearMap.trace ℝ E _ = traceCLM ℝ (ℝ ∙ e)ᗮ (fderiv ℝ (fun z => g ((z : E) + t • e)) y)
    rw [hf1, traceCLM_apply, hf2, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.trace_comp_comm' _ _
  · have hl : HasDerivAt (fun s : ℝ => (y : E) + s • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add (y : E)
    exact (hinner.hasFDerivAt.comp_hasDerivAt t hl).deriv.symm

/-- Pointwise Leibniz-and-chain-rule identity for the rescaled horizontal field
`z ↦ (ℓ z / 2) • A z ((ℓ z / 2) * u)`. -/
private theorem trace_fderiv_slabRescaledField_eq {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] {A : H → ℝ → H}
    (hA : ContDiff ℝ ∞ (Function.uncurry A)) {ℓ : H → ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    (u : ℝ) (y : H) :
    traceCLM ℝ H (fderiv ℝ (fun z : H => (ℓ z / 2) • A z ((ℓ z / 2) * u)) y) =
      (ℓ y / 2) * traceCLM ℝ H (fderiv ℝ (fun z : H => A z ((ℓ y / 2) * u)) y) +
        deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) u := by
  have hℓd : DifferentiableAt ℝ ℓ y := hℓ.differentiable (by simp) y
  have hhalf : HasFDerivAt (fun z : H => ℓ z / 2) ((2 : ℝ)⁻¹ • fderiv ℝ ℓ y) y :=
    (hℓd.hasFDerivAt.const_mul (2 : ℝ)⁻¹).congr_of_eventuallyEq
      (.of_forall fun z => div_eq_inv_mul (ℓ z) 2)
  have hmul : HasFDerivAt (fun z : H => (ℓ z / 2) * u) ((u * (2 : ℝ)⁻¹) • fderiv ℝ ℓ y) y :=
    ((hhalf.const_mul u).congr_of_eventuallyEq
      (.of_forall fun z => mul_comm (ℓ z / 2) u)).congr_fderiv
      (smul_smul u (2 : ℝ)⁻¹ (fderiv ℝ ℓ y))
  have hFA : DifferentiableAt ℝ (Function.uncurry A) (y, (ℓ y / 2) * u) :=
    hA.differentiable (by simp) (y, (ℓ y / 2) * u)
  have hAd : DifferentiableAt ℝ (A y) ((ℓ y / 2) * u) :=
    (hA.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _
  have hcomp_diff : DifferentiableAt ℝ (fun z : H => A z ((ℓ z / 2) * u)) y :=
    show DifferentiableAt ℝ ((Function.uncurry A) ∘ fun z : H => (z, (ℓ z / 2) * u)) y from
      hFA.comp y (differentiableAt_id.prodMk hmul.differentiableAt)
  have hcomp_eq : fderiv ℝ (fun z : H => A z ((ℓ z / 2) * u)) y =
      fderiv ℝ (fun z : H => A z ((ℓ y / 2) * u)) y +
        ((u * (2 : ℝ)⁻¹) • fderiv ℝ ℓ y).smulRight (deriv (A y) ((ℓ y / 2) * u)) := by
    ext v
    have hg := fderiv_comp_graph_apply (f := Function.uncurry A) hmul.differentiableAt hFA v
    have hleft := congrArg (fun L => L v) (fderiv_slice_left hFA)
    simp only [Function.uncurry, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      at hg hleft
    rw [hg, ← hleft, hmul.fderiv, hAd.hasDerivAt.hasFDerivAt.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  have hlin : HasDerivAt (fun s : ℝ => (ℓ y / 2) * s) (ℓ y / 2) u := by
    simpa using (hasDerivAt_id u).const_mul (ℓ y / 2)
  have hsm := (hasDerivAt_id u).smul (hAd.hasDerivAt.scomp u hlin)
  have hΦd : HasDerivAt (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s)))
      ((2 : ℝ)⁻¹ * fderiv ℝ ℓ y
        (u • (ℓ y / 2) • deriv (A y) ((ℓ y / 2) * u) + (1 : ℝ) • A y ((ℓ y / 2) * u))) u :=
    ((fderiv ℝ ℓ y).hasFDerivAt.comp_hasDerivAt u hsm).const_mul (2 : ℝ)⁻¹
  rw [traceCLM_apply, trace_fderiv_smul hhalf.differentiableAt hcomp_diff, hhalf.fderiv,
    hcomp_eq, ContinuousLinearMap.toLinearMap_add, map_add,
    ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight, hΦd.deriv]
  simp [traceCLM_apply, smul_eq_mul]
  ring

/-- A continuous function on `ℝ × H` vanishing outside `ℝ × K` for compact `K` is integrable on
`Ioc (-1) 1 ×ˢ univ`, and its iterated integrals swap. -/
private theorem integrable_and_integral_swap_Ioc {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {K : Set H} (hK : IsCompact K) {P : ℝ × H → ℝ} (hP : Continuous P)
    (hvan : ∀ u, ∀ y ∉ K, P (u, y) = 0) :
    Integrable (fun y : H => ∫ u in (-1 : ℝ)..1, P (u, y)) volume ∧
      (∫ u in Ioc (-1 : ℝ) 1, ∫ y : H, P (u, y)) =
        ∫ y : H, ∫ u in (-1 : ℝ)..1, P (u, y) := by
  let g : ℝ × H → ℝ := fun q => (Ioc (-1 : ℝ) 1).indicator (fun u => P (u, q.2)) q.1
  have hg_eq : g = (Ioc (-1 : ℝ) 1 ×ˢ K).indicator P := by
    ext ⟨u, y⟩
    by_cases hu : u ∈ Ioc (-1 : ℝ) 1 <;> by_cases hy : y ∈ K <;> simp [g, hu, hy, hvan]
  have hgi : Integrable g (volume.prod volume) := by
    rw [hg_eq]
    exact ((hP.continuousOn.integrableOn_compact (isCompact_Icc.prod hK)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)).integrable_indicator
      (measurableSet_Ioc.prod hK.isClosed.measurableSet)
  have hsec (y : H) : ∫ u : ℝ, g (u, y) = ∫ u in (-1 : ℝ)..1, P (u, y) := by
    rw [show (fun u : ℝ => g (u, y)) = (Ioc (-1 : ℝ) 1).indicator (fun u => P (u, y)) from rfl,
      integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le (by norm_num)]
  have hlhs : ∫ u : ℝ, ∫ y : H, g (u, y) = ∫ u in Ioc (-1 : ℝ) 1, ∫ y : H, P (u, y) := by
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (.of_forall fun u => ?_)
    by_cases hu : u ∈ Ioc (-1 : ℝ) 1 <;> simp [g, hu]
  refine ⟨by simpa only [hsec] using hgi.integral_prod_right, ?_⟩
  rw [← hlhs, ← integral_prod g hgi, integral_prod_symm g hgi]
  exact integral_congr_ae (.of_forall hsec)

/-- Continuity of the two slab-rescaled integrands `P1` and `P2` on `ℝ × H`. -/
private theorem continuous_slabRescaledPieces {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] {A : H → ℝ → H}
    (hA : ContDiff ℝ ∞ (Function.uncurry A)) {ℓ : H → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Continuous (fun q : ℝ × H =>
        (ℓ q.2 / 2) * traceCLM ℝ H (fderiv ℝ (fun z : H => A z ((ℓ q.2 / 2) * q.1)) q.2)) ∧
      Continuous (fun q : ℝ × H =>
        deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ q.2 (s • A q.2 ((ℓ q.2 / 2) * s))) q.1) := by
  have hFA : (fun p : H × ℝ => fderiv ℝ (fun z : H => A z p.2) p.1) =
      fun p => (fderiv ℝ (Function.uncurry A) p).comp (.inl ℝ H ℝ) :=
    funext fun p => fderiv_slice_left (hA.differentiable (by simp) (p.1, p.2))
  have hFA_cont : Continuous (fun p : H × ℝ => fderiv ℝ (fun z : H => A z p.2) p.1) := by
    rw [hFA]
    exact (((ContinuousLinearMap.compL ℝ H (H × ℝ) H).flip (.inl ℝ H ℝ)).continuous.comp
      (hA.continuous_fderiv (by simp)))
  have hP1 : Continuous (fun q : ℝ × H =>
      (ℓ q.2 / 2) * traceCLM ℝ H (fderiv ℝ (fun z : H => A z ((ℓ q.2 / 2) * q.1)) q.2)) :=
    ((hℓ.continuous.comp continuous_snd).div_const 2).mul <|
      (traceCLM ℝ H).continuous.comp <| hFA_cont.comp
        (continuous_snd.prodMk (((hℓ.continuous.comp continuous_snd).div_const 2).mul
          continuous_fst))
  have hWu : ContDiff ℝ ∞ (fun q : ℝ × H => (ℓ q.2 / 2) • A q.2 ((ℓ q.2 / 2) * q.1)) :=
    ((hℓ.comp contDiff_snd).div_const 2).smul (hA.comp (contDiff_snd.prodMk
      (((hℓ.comp contDiff_snd).div_const 2).mul contDiff_fst)))
  have hdiv_eq : (fun q : ℝ × H => traceCLM ℝ H
        (fderiv ℝ (fun z : H => (ℓ z / 2) • A z ((ℓ z / 2) * q.1)) q.2)) =
      fun q => traceCLM ℝ H
        ((fderiv ℝ (fun p : ℝ × H => (ℓ p.2 / 2) • A p.2 ((ℓ p.2 / 2) * p.1)) q).comp
          (.inr ℝ ℝ H)) :=
    funext fun q => congrArg (traceCLM ℝ H)
      (fderiv_slice_right (f := fun p : ℝ × H => (ℓ p.2 / 2) • A p.2 ((ℓ p.2 / 2) * p.1))
        (hWu.differentiable (by simp) (q.1, q.2)))
  have hdiv : Continuous (fun q : ℝ × H => traceCLM ℝ H
      (fderiv ℝ (fun z : H => (ℓ z / 2) • A z ((ℓ z / 2) * q.1)) q.2)) := by
    rw [hdiv_eq]
    exact (traceCLM ℝ H).continuous.comp
      (((ContinuousLinearMap.compL ℝ H (ℝ × H) H).flip (.inr ℝ ℝ H)).continuous.comp
        (hWu.continuous_fderiv (by simp)))
  refine ⟨hP1, ?_⟩
  convert hdiv.sub hP1 using 1
  ext ⟨u, y⟩
  simp only [Pi.sub_apply]
  linarith [trace_fderiv_slabRescaledField_eq hA hℓ u y]

/-- For each fixed rescaled height `u : ℝ`, the hyperplane integral of the rescaled horizontal
divergence equals minus the integral of the `u`-derivative term, since their sum is the divergence
of a compactly supported test field. -/
private theorem integral_slabRescaledPiece_eq_neg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {K : Set H} (hK : IsCompact K) {A : H → ℝ → H} (hA : ContDiff ℝ ∞ (Function.uncurry A))
    (hA0 : ∀ {y : H}, y ∉ K → ∀ t, A y t = 0) {ℓ : H → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (u : ℝ) :
    (∫ y : H, (ℓ y / 2) * traceCLM ℝ H (fderiv ℝ (fun z : H => A z ((ℓ y / 2) * u)) y)) =
      -∫ y : H, deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) u := by
  let W : 𝓓(⊤, H) :=
    ⟨fun y => (ℓ y / 2) • A y ((ℓ y / 2) * u),
      (hℓ.div_const 2).smul (hA.comp (contDiff_id.prodMk ((hℓ.div_const 2).mul contDiff_const))),
      .of_support_subset_isCompact hK fun y hy => by by_contra hyK; exact hy (by simp [hA0 hyK]),
      subset_univ _⟩
  obtain ⟨hP1c, hP2c⟩ := continuous_slabRescaledPieces hA hℓ
  have hvan1 {y : H} (hy : y ∉ K) :
      (ℓ y / 2) * traceCLM ℝ H (fderiv ℝ (fun z : H => A z ((ℓ y / 2) * u)) y) = 0 := by
    have hloc : (fun z : H => A z ((ℓ y / 2) * u)) =ᶠ[𝓝 y] 0 :=
      Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hy) fun z hz => hA0 hz _
    simp [hloc.fderiv_eq]
  have hvan2 {y : H} (hy : y ∉ K) :
      deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) u = 0 := by
    have hloc : (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) = 0 :=
      funext fun s => by simp [hA0 hy]
    rw [hloc]
    simp
  have hi1 : Integrable (fun y : H => (ℓ y / 2) * traceCLM ℝ H
      (fderiv ℝ (fun z : H => A z ((ℓ y / 2) * u)) y)) volume :=
    (hP1c.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (.of_support_subset_isCompact hK fun y hy => by by_contra hyK; exact hy (hvan1 hyK))
  have hi2 : Integrable (fun y : H =>
      deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) u) volume :=
    (hP2c.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (.of_support_subset_isCompact hK fun y hy => by by_contra hyK; exact hy (hvan2 hyK))
  have hsum : (∫ y : H, (ℓ y / 2) * traceCLM ℝ H
        (fderiv ℝ (fun z : H => A z ((ℓ y / 2) * u)) y)) +
      (∫ y : H, deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) u) =
      ∫ y : H, divergenceCLM W y := by
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (.of_forall fun y =>
      (trace_fderiv_slabRescaledField_eq hA hℓ u y).symm.trans
        (by rw [divergenceCLM_apply, ← traceCLM_apply]; rfl))
  linarith [hsum, TestFunction.integral_divergenceCLM_eq_zero (μ := volume) W]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isCompact_fst_image_tsupport (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E)) :
    IsCompact (Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀)) ∧
      ∀ {y : (ℝ ∙ e)ᗮ}, y ∉ Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀) →
        ∀ t : ℝ, ψ₀ ((y : E) + t • e) = 0 :=
  ⟨(ψ₀.hasCompactSupport.isCompact.image (orthogonalLineEquiv e he).symm.continuous).image
      continuous_fst,
    fun hy t => image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, ⟨_, h, rfl⟩, by
      rw [← orthogonalLineEquiv_apply e he _ t, ContinuousLinearEquiv.symm_apply_apply]⟩⟩

/-- Integrating the horizontal divergence of `ψ₀` over the smooth symmetric slab `{|t| < ℓ y / 2}`
gives `-∫ y, Dℓ(y) ((A(y, ℓ y / 2) + A(y, -ℓ y / 2)) / 2)` and proves `y`-integrability. -/
private theorem integrable_and_integral_horizontal_divergence_symmSlab_eq (e : E) (he : ‖e‖ = 1)
    (ψ₀ : 𝓓(⊤, E)) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ => ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
        traceCLM ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => ((orthogonalLineEquiv e he).symm (ψ₀ ((z : E) + t • e))).1)
            y)) volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
          traceCLM ℝ (ℝ ∙ e)ᗮ
            (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
              ((orthogonalLineEquiv e he).symm (ψ₀ ((z : E) + t • e))).1) y)) =
        -∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ ℓ y
          ((2 : ℝ)⁻¹ • (((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (ℓ y / 2) • e))).1 +
            ((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))).1)) := by
  let π : E →L[ℝ] (ℝ ∙ e)ᗮ :=
    (ContinuousLinearMap.fst ℝ (ℝ ∙ e)ᗮ ℝ).comp
      (orthogonalLineEquiv e he).symm.toContinuousLinearMap
  set A : (ℝ ∙ e)ᗮ → ℝ → (ℝ ∙ e)ᗮ := fun y t => π (ψ₀ ((y : E) + t • e))
  have hA : ContDiff ℝ ∞ (Function.uncurry A) :=
    π.contDiff.comp (ψ₀.contDiff.comp (((ℝ ∙ e)ᗮ.subtypeL.contDiff.comp contDiff_fst).add
      (contDiff_snd.smul contDiff_const)))
  obtain ⟨hK, hψ0⟩ := isCompact_fst_image_tsupport e he ψ₀
  have hA0 {y : (ℝ ∙ e)ᗮ} (hy : y ∉ Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀))
      (t : ℝ) : A y t = 0 := by simp [A, hψ0 hy t]
  obtain ⟨hP1c, hP2c⟩ := continuous_slabRescaledPieces hA hℓ
  have h1 := integrable_and_integral_swap_Ioc hK hP1c fun u y hy => by
    have hloc : (fun z : (ℝ ∙ e)ᗮ => A z ((ℓ y / 2) * u)) =ᶠ[𝓝 y] 0 :=
      Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hy) fun z hz => hA0 hz _
    simp [hloc.fderiv_eq]
  have h2 := integrable_and_integral_swap_Ioc hK hP2c fun u y hy => by
    rw [show (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) = 0 from
      funext fun s => by simp [hA0 hy]]; simp
  have hp1_eq (y : (ℝ ∙ e)ᗮ) : (∫ u in (-1 : ℝ)..1,
      (ℓ y / 2) * traceCLM ℝ (ℝ ∙ e)ᗮ (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z ((ℓ y / 2) * u)) y)) =
      ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
        traceCLM ℝ (ℝ ∙ e)ᗮ (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z t) y) := by
    rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
      intervalIntegral.smul_integral_comp_mul_left
        (f := fun t => traceCLM ℝ (ℝ ∙ e)ᗮ (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z t) y)),
      mul_neg_one, mul_one]
  have hp2_eq (y : (ℝ ∙ e)ᗮ) : (∫ u in (-1 : ℝ)..1,
      deriv (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) u) =
      fderiv ℝ ℓ y ((2 : ℝ)⁻¹ • (A y (ℓ y / 2) + A y (-(ℓ y / 2)))) := by
    have hΦ : ContDiff ℝ ∞ (fun s : ℝ => (2 : ℝ)⁻¹ * fderiv ℝ ℓ y (s • A y ((ℓ y / 2) * s))) :=
      contDiff_const.mul ((fderiv ℝ ℓ y).contDiff.comp
        (contDiff_id.smul (hA.comp (contDiff_const.prodMk (contDiff_const.mul contDiff_id)))))
    rw [intervalIntegral.integral_deriv_eq_sub (fun s _ => hΦ.differentiable (by simp) s)
      ((hΦ.continuous_deriv (by simp)).intervalIntegrable _ _)]
    simp only [one_smul, mul_one, mul_neg_one, neg_one_smul, map_neg, map_add, map_smul,
      smul_eq_mul]; ring
  refine ⟨h1.1.congr (.of_forall hp1_eq), ?_⟩
  change (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
      traceCLM ℝ (ℝ ∙ e)ᗮ (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z t) y)) =
    -∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ ℓ y ((2 : ℝ)⁻¹ • (A y (ℓ y / 2) + A y (-(ℓ y / 2))))
  simp_rw [← hp1_eq, ← hp2_eq, ← h1.2, ← h2.2,
    integral_slabRescaledPiece_eq_neg hK hA hA0 hℓ, integral_neg]

/-- Continuity and integrability of the longitudinal boundary half-difference `d` on a smooth
symmetric slab. -/
private theorem continuous_and_integrable_slabVerticalDiff (e : E) (he : ‖e‖ = 1)
    (ψ₀ : 𝓓(⊤, E)) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Continuous (fun y : (ℝ ∙ e)ᗮ => (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) ∧
      Integrable (fun y : (ℝ ∙ e)ᗮ => (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) volume := by
  have hpos : Continuous fun y : (ℝ ∙ e)ᗮ => ⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ :=
    (innerSL ℝ e).continuous.comp (ψ₀.continuous.comp
      ((ℝ ∙ e)ᗮ.subtypeL.continuous.add ((hℓ.continuous.div_const 2).smul continuous_const)))
  have hneg : Continuous fun y : (ℝ ∙ e)ᗮ => ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫ :=
    (innerSL ℝ e).continuous.comp (ψ₀.continuous.comp
      ((ℝ ∙ e)ᗮ.subtypeL.continuous.add
        ((hℓ.continuous.div_const 2).neg.smul continuous_const)))
  have hdc : Continuous fun y : (ℝ ∙ e)ᗮ => (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
      ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫) :=
    continuous_const.mul (hpos.sub hneg)
  set K : Set (ℝ ∙ e)ᗮ := Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀)
  have hK : IsCompact K :=
    (ψ₀.hasCompactSupport.isCompact.image (orthogonalLineEquiv e he).symm.continuous).image
      continuous_fst
  refine ⟨hdc, hdc.integrable_of_hasCompactSupport (.of_support_subset_isCompact hK fun y hy => ?_)⟩
  by_contra hyK
  have h0 (t : ℝ) : ψ₀ ((y : E) + t • e) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hyK ⟨_, ⟨_, h, rfl⟩, by
      rw [← orthogonalLineEquiv_apply e he y t, ContinuousLinearEquiv.symm_apply_apply]⟩
  exact hy (by simp only [h0 (ℓ y / 2), h0 (-(ℓ y / 2)), inner_zero_right, sub_self, mul_zero])

/-- Integrating `divergenceCLM ψ₀` over the smooth symmetric slab `{|t| < ℓ y / 2}` splits into
twice the integral of the longitudinal boundary half-difference minus the pairing of `Dℓ` with the
transverse boundary average. -/
private theorem integrable_and_integral_divergenceCLM_symmSlab_eq (e : E) (he : ‖e‖ = 1)
    (ψ₀ : 𝓓(⊤, E)) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
        ∫ t in (-(ℓ y / 2))..(ℓ y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(ℓ y / 2))..(ℓ y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) =
        2 * (∫ y : (ℝ ∙ e)ᗮ, (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
          ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) -
        ∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ ℓ y
          ((2 : ℝ)⁻¹ • (((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (ℓ y / 2) • e))).1 +
            ((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))).1)) := by
  obtain ⟨hi1, heq1⟩ := integrable_and_integral_horizontal_divergence_symmSlab_eq e he ψ₀ hℓ
  obtain ⟨-, hdi⟩ := continuous_and_integrable_slabVerticalDiff e he ψ₀ hℓ
  let d : (ℝ ∙ e)ᗮ → ℝ := fun y =>
    (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ - ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)
  have hline (y : (ℝ ∙ e)ᗮ) :
      (∫ t in (-(ℓ y / 2))..(ℓ y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) =
        (∫ t in (-(ℓ y / 2))..(ℓ y / 2), traceCLM ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
            ((orthogonalLineEquiv e he).symm (ψ₀ ((z : E) + t • e))).1) y)) +
        2 * d y := by
    have hg : ContDiff ℝ ∞ (fun s : ℝ => ⟪e, ψ₀ ((y : E) + s • e)⟫) :=
      (innerSL ℝ e).contDiff.comp (ψ₀.contDiff.comp
        (contDiff_const.add (contDiff_id.smul contDiff_const)))
    have hi_div : IntervalIntegrable (fun t => divergenceCLM ψ₀ ((y : E) + t • e)) volume
        (-(ℓ y / 2)) (ℓ y / 2) :=
      ((divergenceCLM ψ₀).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
    have hi_v : IntervalIntegrable (deriv fun s : ℝ => ⟪e, ψ₀ ((y : E) + s • e)⟫) volume
        (-(ℓ y / 2)) (ℓ y / 2) :=
      (hg.continuous_deriv (by simp)).intervalIntegrable _ _
    have hi_h : IntervalIntegrable (fun t => traceCLM ℝ (ℝ ∙ e)ᗮ
        (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
          ((orthogonalLineEquiv e he).symm (ψ₀ ((z : E) + t • e))).1) y))
        volume (-(ℓ y / 2)) (ℓ y / 2) := by
      convert hi_div.sub hi_v using 1
      ext t; linarith [divergenceCLM_orthogonalLine_eq e he ψ₀ y t]
    simp_rw [divergenceCLM_orthogonalLine_eq e he ψ₀ y]
    rw [intervalIntegral.integral_add hi_h hi_v,
      intervalIntegral.integral_deriv_eq_sub (fun s _ => hg.differentiable (by simp) s) hi_v]
    simp only [d]; ring
  refine ⟨(hi1.add (hdi.const_mul 2)).congr (.of_forall fun y => (hline y).symm), ?_⟩
  simp_rw [hline]
  rw [integral_add hi1 (hdi.const_mul 2), heq1, integral_const_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise Pythagorean bound for the horizontal average and vertical half-difference of `ψ₀` on
the boundary of the symmetric slab. -/
private theorem norm_sq_slabBoundaryAvg_le_one (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
    (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) (ℓ : (ℝ ∙ e)ᗮ → ℝ) (y : (ℝ ∙ e)ᗮ) :
    ‖(2 : ℝ)⁻¹ • (((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (ℓ y / 2) • e))).1 +
        ((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))).1)‖ ^ 2 +
      ((2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) ^ 2 ≤ 1 := by
  set x1 := (y : E) + (ℓ y / 2) • e
  set x2 := (y : E) + (-(ℓ y / 2)) • e
  set u1 := ((orthogonalLineEquiv e he).symm (ψ₀ x1)).1
  set u2 := ((orthogonalLineEquiv e he).symm (ψ₀ x2)).1
  set v1 := ⟪e, ψ₀ x1⟫
  set v2 := ⟪e, ψ₀ x2⟫
  have hdecomp (x : E) :
      (((orthogonalLineEquiv e he).symm (ψ₀ x)).1 : E) + ⟪e, ψ₀ x⟫ • e = ψ₀ x := by
    have hx := (orthogonalLineEquiv e he).apply_symm_apply (ψ₀ x)
    rwa [← Prod.eta (p := (orthogonalLineEquiv e he).symm (ψ₀ x)), orthogonalLineEquiv_apply,
      orthogonalLineEquiv_symm_snd] at hx
  have hn1 : ‖(u1 : E) + v1 • e‖ ≤ 1 := by rw [hdecomp]; exact hψ1 x1
  have hn2 : ‖(u2 : E) + (-v2) • e‖ ≤ 1 := by
    have hsq : ‖(u2 : E) + (-v2) • e‖ ^ 2 ≤ 1 := by
      rw [norm_add_smul_sq e he, neg_sq, ← norm_add_smul_sq e he, hdecomp x2]
      exact pow_le_one₀ (norm_nonneg _) (hψ1 x2)
    nlinarith [norm_nonneg ((u2 : E) + (-v2) • e)]
  set z : E := (((2 : ℝ)⁻¹ • (u1 + u2) : (ℝ ∙ e)ᗮ) : E) + ((2 : ℝ)⁻¹ * (v1 - v2)) • e
  have hz_eq : z = (2 : ℝ)⁻¹ • (((u1 : E) + v1 • e) + ((u2 : E) + (-v2) • e)) := by
    simp only [z, Submodule.coe_smul_of_tower, Submodule.coe_add]; module
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hz_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith [norm_add_le ((u1 : E) + v1 • e) ((u2 : E) + (-v2) • e)]
  rw [← norm_add_smul_sq e he]
  exact pow_le_one₀ (norm_nonneg z) hz1

/-- Jensen inequality in `WithLp 2 (H × ℝ)` for normalized-bump convolutions of a vector field and
a scalar function satisfying `‖b y‖² + d y² ≤ 1`. -/
private theorem norm_sq_add_sq_normed_convolution_le_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (ρ : ContDiffBump (0 : H)) {b : H → H} {d : H → ℝ}
    (hb : Continuous b) (hd : Continuous d) (hbd : ∀ y, ‖b y‖ ^ 2 + d y ^ 2 ≤ 1) (z : H) :
    ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] b) z‖ ^ 2 +
        ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z) ^ 2 ≤ 1 := by
  let g : H → WithLp 2 (H × ℝ) :=
    fun y => (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm (b y, d y)
  have hg : Continuous g :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm.continuous.comp (hb.prodMk hd)
  have hgn (y : H) : ‖g y‖ ≤ 1 := by
    have hsq : ‖g y‖ ^ 2 ≤ 1 := by simpa [g, WithLp.prod_norm_sq_eq_of_L2] using hbd y
    nlinarith [norm_nonneg (g y)]
  have hex_g :=
    (ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (ρ.integrable_normed (μ := volume)).locallyIntegrable hg z
  have hle : ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z‖ ≤ 1 := by
    rw [convolution_def]
    refine (norm_integral_le_of_norm_le (ρ.integrable_normed (μ := volume))
      (.of_forall fun t => ?_)).trans_eq ρ.integral_normed
    simp only [lsmul_apply, norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed t)]
    exact mul_le_of_le_one_right (ρ.nonneg_normed t) (hgn (z - t))
  have hfst : ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z).fst =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] b) z :=
    ((WithLp.fstL 2 ℝ H ℝ).convolution_lsmul_comp_comm hex_g).symm
  have hsnd : ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z).snd =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z :=
    ((WithLp.sndL 2 ℝ H ℝ).convolution_lsmul_comp_comm hex_g).symm
  have hsq := pow_le_one₀ (norm_nonneg _) hle (n := 2)
  rwa [WithLp.prod_norm_sq_eq_of_L2, hfst, hsnd, Real.norm_eq_abs, sq_abs] at hsq

/-- Divergence commutes with normalized-bump mollification of a test vector field. -/
private theorem divergenceCLM_mollify_eq_normed_convolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (ρ : ContDiffBump (0 : H)) (B : 𝓓(⊤, H)) (z : H) :
    divergenceCLM (B.mollify volume ρ (subset_univ _)) z =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] (divergenceCLM B : H → ℝ)) z := by
  have hpre : (lsmul ℝ ℝ : ℝ →L[ℝ] H →L[ℝ] H).precompR H = lsmul ℝ ℝ := by ext; rfl
  have hB1 : ContDiff ℝ 1 (B : H → H) := B.contDiff.of_le (by simp)
  have hfd : fderiv ℝ (B.mollify volume ρ (subset_univ _) : H → H) z =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fderiv ℝ (B : H → H)) z := by
    rw [coe_mollify, (B.hasCompactSupport.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      (ρ.continuous_normed (μ := volume)).locallyIntegrable hB1 z).fderiv, hpre]
  have hex := (ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) (ρ.integrable_normed (μ := volume)).locallyIntegrable
    (hB1.continuous_fderiv one_ne_zero) z
  have hdiv_eq : (divergenceCLM B : H → ℝ) = fun y => traceCLM ℝ H (fderiv ℝ (B : H → H) y) := by
    ext y; rw [divergenceCLM_apply, ← traceCLM_apply]
  rw [divergenceCLM_apply, ← traceCLM_apply, hfd, hdiv_eq]
  exact ((traceCLM ℝ H).convolution_lsmul_comp_comm hex).symm

/-- Moving a normalized-bump mollifier from an integrable function `L` onto a test vector field
`B ∈ 𝓓(⊤, H)` turns `-∫ DL_ρ (B)` into `∫ div (mollify B) * L`. -/
private theorem neg_integral_fderiv_normed_convolution_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (ρ : ContDiffBump (0 : H)) {L : H → ℝ} (hL : Integrable L volume) (B : 𝓓(⊤, H)) :
    -∫ y : H, fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y (B y) =
      ∫ z : H, divergenceCLM (B.mollify volume ρ (subset_univ _)) z * L z := by
  set Lρ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L
  have hLρ : ContDiff ℝ 1 Lρ :=
    ((ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _
      (ρ.contDiff_normed (n := ⊤)) hL.locallyIntegrable).of_le (by simp)
  have hweak : HasWeakFDerivOn volume ⊤ Lρ (fderiv ℝ Lρ) :=
    hLρ.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn
      (.of_forall fun y _ => (hLρ.differentiable one_ne_zero y).hasFDerivAt)
  have hibp : -∫ y : H, fderiv ℝ Lρ y (B y) = ∫ y : H, divergenceCLM B y * Lρ y := by
    simpa [smul_eq_mul] using (hweak.integral_divergenceCLM_smul_eq_neg_integral B).symm
  obtain ⟨C, hC⟩ := (divergenceCLM B).continuous.bounded_above_of_compact_support
    (divergenceCLM B).hasCompactSupport
  have hFub1 := integral_mul_convolution_eq_integral_mul_integral_comp_sub
    (divergenceCLM B).continuous (divergenceCLM B).hasCompactSupport
    (ρ.integrable_normed (μ := volume)) (ρ.hasCompactSupport_normed (μ := volume))
    (hL.locallyIntegrable.locallyIntegrableOn univ) fun _ _ _ _ => mem_univ _
  have hshift (t : H) :
      ∫ y : H, divergenceCLM B y * L (y - t) = ∫ z : H, divergenceCLM B (z + t) * L z := by
    simpa only [sub_add_cancel] using
      integral_sub_right_eq_self (fun z => divergenceCLM B (z + t) * L z) t
  have hprod : Integrable
      (fun p : H × H => ρ.normed volume p.1 * (divergenceCLM B (p.2 - p.1) * L p.2))
      (volume.prod volume) := by
    refine Integrable.mono' (((ρ.integrable_normed (μ := volume)).mul_prod hL.norm).const_mul C)
      (((ρ.continuous_normed (μ := volume)).comp continuous_fst).aestronglyMeasurable.mul
        (((divergenceCLM B).continuous.comp
          (continuous_snd.sub continuous_fst)).aestronglyMeasurable.mul
          (hL.aestronglyMeasurable.comp_snd))) (.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ρ.nonneg_normed p.1)]
    calc ρ.normed volume p.1 * (|divergenceCLM B (p.2 - p.1)| * |L p.2|)
        ≤ ρ.normed volume p.1 * (C * |L p.2|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _))
            (ρ.nonneg_normed _)
      _ = C * (ρ.normed volume p.1 * ‖L p.2‖) := by rw [Real.norm_eq_abs]; ring
  rw [hibp, hFub1]
  simp_rw [hshift]
  rw [← integral_neg_eq_self]
  simp_rw [ρ.normed_neg, ← sub_eq_add_neg, ← integral_const_mul]
  rw [integral_integral_swap hprod]
  refine integral_congr_ae (.of_forall fun z => ?_)
  simp_rw [← mul_assoc, integral_mul_const]
  rw [divergenceCLM_mollify_eq_normed_convolution ρ B z]; rfl

/-- The real-valued section lengths of a finite-volume null-measurable set form an integrable
function on the orthogonal hyperplane. -/
private theorem integrable_measureReal_lineSection {s : Set E} (hs : NullMeasurableSet s volume)
    (hfin : volume s ≠ ⊤) (e : E) (he : ‖e‖ = 1) :
    Integrable (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  refine ⟨(ENNReal.measurable_toReal.comp_aemeasurable
    (aemeasurable_volume_lineSection e he hs)).aestronglyMeasurable, ?_⟩
  have hae : (fun y : (ℝ ∙ e)ᗮ => ‖volume.real {t : ℝ | (y : E) + t • e ∈ s}‖ₑ) =ᵐ[volume]
      fun y => volume {t : ℝ | (y : E) + t • e ∈ s} := by
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hy
    rw [Real.eNorm_of_nonneg measureReal_nonneg, ofReal_measureReal hy.ne]
  rw [HasFiniteIntegral, lintegral_congr_ae hae, ← volume_eq_lintegral_volume_lineSection e he hs]
  exact hfin.lt_top

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Symmetric interval integrals of a function bounded by `C` are `C`-Lipschitz in the length. -/
private theorem abs_intervalIntegral_symm_sub_le {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ t, ‖h t‖ ≤ C) (a b : ℝ) :
    |(∫ t in (-(a / 2))..(a / 2), h t) - ∫ t in (-(b / 2))..(b / 2), h t| ≤ C * |a - b| := by
  have hi (p q : ℝ) : IntervalIntegrable h volume p q := hh.intervalIntegrable p q
  have hdiff : (∫ t in (-(a / 2))..(a / 2), h t) - ∫ t in (-(b / 2))..(b / 2), h t =
      (∫ t in (-(a / 2))..(-(b / 2)), h t) + ∫ t in (b / 2)..(a / 2), h t := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hi (-(a / 2)) (-(b / 2))) (hi (-(b / 2)) (b / 2))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hi (-(a / 2)) (b / 2)) (hi (b / 2) (a / 2))
    linarith
  have hb1 : ‖∫ t in (-(a / 2))..(-(b / 2)), h t‖ ≤ C * |-(b / 2) - -(a / 2)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hC t
  have hb2 : ‖∫ t in (b / 2)..(a / 2), h t‖ ≤ C * |a / 2 - b / 2| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hC t
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖(∫ t in (-(a / 2))..(-(b / 2)), h t) + ∫ t in (b / 2)..(a / 2), h t‖
      ≤ C * |-(b / 2) - -(a / 2)| + C * |a / 2 - b / 2| :=
        (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = C * |a - b| := by
        have h1 : |-(b / 2) - -(a / 2)| = |a - b| / 2 := by
          rw [show -(b / 2) - -(a / 2) = (a - b) / 2 by ring, abs_div, abs_two]
        have h2 : |a / 2 - b / 2| = |a - b| / 2 := by
          rw [show a / 2 - b / 2 = (a - b) / 2 by ring, abs_div, abs_two]
        rw [h1, h2]
        ring

/-- Express the integral of `divergenceCLM ψ₀` over a finite-volume Steiner symmetral as an
iterated symmetric interval integral, and establish `y`-integrability. -/
private theorem integrable_and_setIntegral_steinerSymmetrization_eq_integral_intervalIntegral
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E)) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
        ∫ t in (-(volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2))..
          (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2),
          divergenceCLM ψ₀ ((y : E) + t • e)) volume ∧
      ∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x =
        ∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2))..
          (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2),
          divergenceCLM ψ₀ ((y : E) + t • e) := by
  have hS := nullMeasurableSet_steinerSymmetrization e he hs
  have hL := measurePreserving_orthogonalLineEquiv e he
  have hLe := (orthogonalLineEquiv e he).toHomeomorph.measurableEmbedding
  set G : E → ℝ := (steinerSymmetrization e he s).indicator (divergenceCLM ψ₀)
  have hi : Integrable G volume :=
    ((divergenceCLM ψ₀).continuous.integrable_of_hasCompactSupport
      (divergenceCLM ψ₀).hasCompactSupport).indicator₀ hS
  have hae : (fun y : (ℝ ∙ e)ᗮ => ∫ t : ℝ, (G ∘ orthogonalLineEquiv e he) (y, t)) =ᵐ[volume]
      fun y : (ℝ ∙ e)ᗮ => ∫ t in (-(volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2))..
        (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2),
        divergenceCLM ψ₀ ((y : E) + t • e) := by
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hy
    set L_y := volume.real {t : ℝ | (y : E) + t • e ∈ s}
    have hsec : {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
        Ioo (-(L_y / 2)) (L_y / 2) := by
      ext t
      rw [Set.mem_ofPred, mem_steinerSymmetrization, mem_eball, edist_zero_right,
        Real.eNorm_eq_ofReal_abs, ← ofReal_measureReal hy.ne, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg t), abs_lt]
      rfl
    have hind : (fun t : ℝ => (G ∘ orthogonalLineEquiv e he) (y, t)) =
        (Ioo (-(L_y / 2)) (L_y / 2)).indicator fun t => divergenceCLM ψ₀ ((y : E) + t • e) := by
      ext t
      simp only [G, Function.comp_apply, orthogonalLineEquiv_apply, ← hsec]
      exact (indicator_comp_right (fun t : ℝ => (y : E) + t • e)
        (s := steinerSymmetrization e he s) (g := divergenceCLM ψ₀)).symm
    have hL0 : 0 ≤ L_y := measureReal_nonneg
    rw [hind, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by linarith)]
  refine ⟨((hL.integrable_comp_of_integrable hi).integral_prod_left).congr hae, ?_⟩
  rw [← integral_indicator₀ hS, show ∫ x, (steinerSymmetrization e he s).indicator
      (divergenceCLM ψ₀) x = ∫ x, G x from rfl, ← hL.integral_comp hLe]
  exact (integral_prod (G ∘ orthogonalLineEquiv e he)
    (hL.integrable_comp_of_integrable hi)).trans (integral_congr_ae hae)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise bound `|d_k y| ≤ min 1 (Mψ * L y) + Mψ * |ℓ y - L y|` for the vertical boundary
half-difference of `ψ₀`, killing the contribution off `{0 < L}` in `L¹`. -/
private theorem abs_slabVerticalDiff_le (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
    (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) {Mψ : ℝ} (hM0 : 0 ≤ Mψ)
    (hMψ : ∀ x, ‖fderiv ℝ (fun z : E => ⟪e, ψ₀ z⟫) x‖ ≤ Mψ)
    {ℓ L : (ℝ ∙ e)ᗮ → ℝ} (hℓ0 : ∀ y, 0 ≤ ℓ y) (y : (ℝ ∙ e)ᗮ) :
    |(2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)| ≤
      min 1 (Mψ * L y) + Mψ * |ℓ y - L y| := by
  set f : E → ℝ := fun z => ⟪e, ψ₀ z⟫
  have hf : Differentiable ℝ f := ((innerSL ℝ e).contDiff.comp ψ₀.contDiff).differentiable (by simp)
  have hlip := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf x)
    (fun x _ => hMψ x) convex_univ (mem_univ ((y : E) + (-(ℓ y / 2)) • e))
    (mem_univ ((y : E) + (ℓ y / 2) • e))
  have hdiff : ((y : E) + (ℓ y / 2) • e) - ((y : E) + (-(ℓ y / 2)) • e) = ℓ y • e := by
    simp only [neg_smul]; module
  rw [hdiff, norm_smul, Real.norm_of_nonneg (hℓ0 y), he, mul_one, Real.norm_eq_abs] at hlip
  have h1 : |(2 : ℝ)⁻¹ * (f ((y : E) + (ℓ y / 2) • e) - f ((y : E) + (-(ℓ y / 2)) • e))| ≤ 1 := by
    have ha (x : E) : |f x| ≤ 1 :=
      (abs_real_inner_le_norm e (ψ₀ x)).trans (by rw [he, one_mul]; exact hψ1 x)
    rw [abs_mul, abs_of_pos (by positivity)]
    linarith [abs_sub (f ((y : E) + (ℓ y / 2) • e)) (f ((y : E) + (-(ℓ y / 2)) • e)),
      ha ((y : E) + (ℓ y / 2) • e), ha ((y : E) + (-(ℓ y / 2)) • e)]
  have h2 : |(2 : ℝ)⁻¹ * (f ((y : E) + (ℓ y / 2) • e) - f ((y : E) + (-(ℓ y / 2)) • e))| ≤
      Mψ * ℓ y := by
    rw [abs_mul, abs_of_pos (by positivity)]
    linarith [mul_nonneg hM0 (hℓ0 y)]
  refine (le_min h1 h2).trans ?_
  rcases le_total 1 (Mψ * L y) with hb | hb
  · rw [min_eq_left hb]
    exact (min_le_left 1 _).trans (le_add_of_nonneg_right (mul_nonneg hM0 (abs_nonneg _)))
  · rw [min_eq_right hb]
    calc min 1 (Mψ * ℓ y) ≤ Mψ * ℓ y := min_le_right _ _
      _ = Mψ * L y + Mψ * (ℓ y - L y) := by ring
      _ ≤ Mψ * L y + Mψ * |ℓ y - L y| :=
          add_le_add_right (mul_le_mul_of_nonneg_left (le_abs_self _) hM0) _

/-- Pointwise dominance of a normalized-bump convolution when `|d| ≤ g + Mψ * |e_L|`. -/
private theorem abs_normed_convolution_le_of_abs_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (ρ : ContDiffBump (0 : H)) {d g e_L : H → ℝ}
    (hg : Integrable g volume) (heL : Integrable e_L volume) {Mψ : ℝ}
    (hd_le : ∀ y, |d y| ≤ g y + Mψ * |e_L y|) (z : H) :
    |(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z| ≤
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z +
        Mψ * (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => ‖e_L y‖) z := by
  have hex_g := ((ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
    (ρ.continuous_normed (μ := volume)) hg.locallyIntegrable z).integrable
  have hex_L := ((ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
    (ρ.continuous_normed (μ := volume)) heL.norm.locallyIntegrable z).integrable
  rw [← Real.norm_eq_abs, convolution_def]
  refine (norm_integral_le_of_norm_le (hex_g.add (hex_L.const_mul Mψ))
    (.of_forall fun t => ?_)).trans_eq ?_
  · simp only [lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (ρ.nonneg_normed t)]
    calc ρ.normed volume t * |d (z - t)|
        ≤ ρ.normed volume t * (g (z - t) + Mψ * |e_L (z - t)|) :=
          mul_le_mul_of_nonneg_left (hd_le _) (ρ.nonneg_normed t)
      _ = ρ.normed volume t * g (z - t) + Mψ * (ρ.normed volume t * |e_L (z - t)|) := by ring
  · simp only [Pi.add_apply]
    rw [integral_add hex_g (hex_L.const_mul Mψ), integral_const_mul]
    rfl

/-- `L¹` bound for `∫ d`: splitting `∫ (ρ ⋆ d)` over `D` and `Dᶜ`, where `g = 0` on `Dᶜ`, leaves at
most `∫_D w + ‖ρ ⋆ g - g‖₁ + Mψ ‖L_k - L‖₁`. -/
private theorem integral_normed_convolution_le_setIntegral_add_errors {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H]
    [BorelSpace H] (ρ : ContDiffBump (0 : H)) {d g L L_k w : H → ℝ}
    (hd : Integrable d volume) (hg : Integrable g volume) (hL_err : Integrable (L_k - L) volume)
    {D : Set H} (hD : NullMeasurableSet D volume) (hg0 : ∀ z ∈ Dᶜ, g z = 0)
    {Mψ : ℝ} (hM0 : 0 ≤ Mψ) (hd_le : ∀ y, |d y| ≤ g y + Mψ * |L_k y - L y|)
    (hw : IntegrableOn w D volume)
    (hγw : ∀ z ∈ D, |(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z| ≤ w z) :
    ∫ y : H, d y ≤ (∫ z in D, w z) +
      (∫ z : H, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z‖) +
      Mψ * ∫ y : H, ‖L_k y - L y‖ := by
  set γ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d
  have hρi : Integrable (ρ.normed volume) volume := ρ.integrable_normed (μ := volume)
  have hγi : Integrable γ volume := hρi.integrable_convolution (lsmul ℝ ℝ) hd
  have hgi' : Integrable (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) volume :=
    hρi.integrable_convolution (lsmul ℝ ℝ) hg
  have hLi' : Integrable (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => ‖L_k y - L y‖) volume :=
    hρi.integrable_convolution (lsmul ℝ ℝ) hL_err.norm
  have htot : ∫ y : H, d y = (∫ z in D, γ z) + ∫ z in Dᶜ, γ z := by
    have hconv := MeasureTheory.integral_convolution (lsmul ℝ ℝ) hρi hd
    rw [ρ.integral_normed, lsmul_apply, one_smul] at hconv
    rw [← hconv, ← integral_add_compl₀ hD hγi]
  have hD_le : ∫ z in D, γ z ≤ ∫ z in D, w z :=
    setIntegral_mono_on₀ hγi.integrableOn hw hD fun z hz => (le_abs_self _).trans (hγw z hz)
  have h1 : ∫ z in Dᶜ, γ z ≤ ∫ z in Dᶜ, (‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z‖ +
      Mψ * (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => ‖L_k y - L y‖) z) := by
    refine setIntegral_mono_on₀ hγi.integrableOn
      (((hgi'.sub hg).norm.add (hLi'.const_mul Mψ)).integrableOn) hD.compl fun z hz => ?_
    refine (le_abs_self _).trans ((abs_normed_convolution_le_of_abs_le ρ hg hL_err hd_le z).trans
      (add_le_add ?_ le_rfl))
    rw [hg0 z hz, sub_zero, Real.norm_eq_abs]; exact le_abs_self _
  have h2 : ∫ z in Dᶜ, (‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z‖ +
      Mψ * (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => ‖L_k y - L y‖) z) ≤
      (∫ z : H, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z‖) +
        Mψ * ∫ z : H, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => ‖L_k y - L y‖) z := by
    have hgi_sub : Integrable (fun z => ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z‖)
        volume := (hgi'.sub hg).norm
    rw [integral_add hgi_sub.integrableOn (hLi'.const_mul Mψ).integrableOn, integral_const_mul]
    exact add_le_add (setIntegral_le_integral hgi_sub (.of_forall fun _ => norm_nonneg _))
      (mul_le_mul_of_nonneg_left (setIntegral_le_integral hLi' (.of_forall fun _ =>
        integral_nonneg fun t => mul_nonneg (ρ.nonneg_normed t) (norm_nonneg _))) hM0)
  have hconvL := MeasureTheory.integral_convolution (lsmul ℝ ℝ) hρi hL_err.norm
  rw [ρ.integral_normed, lsmul_apply, one_smul] at hconvL
  simp only [Pi.sub_apply] at hconvL
  have hDc : ∫ z in Dᶜ, γ z ≤ (∫ z : H, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z‖) +
      Mψ * ∫ y : H, ‖L_k y - L y‖ := h1.trans (h2.trans_eq (by rw [hconvL]))
  linarith

/-- Real-valued `L¹` convergence of normalized-bump mollifications. -/
private theorem tendsto_integral_norm_normed_convolution_sub {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {ρ : ℕ → ContDiffBump (0 : H)} (hρ : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0))
    {f : H → ℝ} (hf : Integrable f volume) :
    Tendsto (fun k => ∫ y : H, ‖((ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] f) y - f y‖)
      atTop (𝓝 0) := by
  have hto := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_lintegral_enorm_normed_convolution_sub hρ hf)
  rw [ENNReal.toReal_zero] at hto
  refine hto.congr fun k => ?_
  have hik : Integrable (((ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] f) - f) volume :=
    (((ρ k).integrable_normed (μ := volume)).integrable_convolution (lsmul ℝ ℝ) hf).sub hf
  exact (integral_norm_eq_lintegral_eNorm hik.aestronglyMeasurable).symm

/-- The horizontal boundary-average test vector field in `𝓓(⊤, (ℝ ∙ e)ᗮ)` associated to `ψ₀` and a
smooth slab thickness `ℓ`. -/
private def slabHorizAvg (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓((⊤ : Opens E), E))
    {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ) where
  toFun y := (2 : ℝ)⁻¹ •
    (((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (ℓ y / 2) • e))).1 +
      ((orthogonalLineEquiv e he).symm (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))).1)
  contDiff' :=
    let π : E →L[ℝ] (ℝ ∙ e)ᗮ :=
      (ContinuousLinearMap.fst ℝ (ℝ ∙ e)ᗮ ℝ).comp
        (orthogonalLineEquiv e he).symm.toContinuousLinearMap
    have h1 : ContDiff ℝ ∞ (fun y : (ℝ ∙ e)ᗮ => π (ψ₀ ((y : E) + (ℓ y / 2) • e))) :=
      π.contDiff.comp (ψ₀.contDiff.comp ((ℝ ∙ e)ᗮ.subtypeL.contDiff.add
        ((hℓ.div_const 2).smul (contDiff_const (c := e)))))
    have h2 : ContDiff ℝ ∞ (fun y : (ℝ ∙ e)ᗮ => π (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))) :=
      π.contDiff.comp (ψ₀.contDiff.comp ((ℝ ∙ e)ᗮ.subtypeL.contDiff.add
        ((hℓ.div_const 2).neg.smul (contDiff_const (c := e)))))
    (h1.add h2).const_smul (2 : ℝ)⁻¹
  hasCompactSupport' := .of_support_subset_isCompact
    ((ψ₀.hasCompactSupport.isCompact.image (orthogonalLineEquiv e he).symm.continuous).image
      continuous_fst) fun y hy => by
      by_contra hyK
      have h0 (t : ℝ) : ψ₀ ((y : E) + t • e) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hyK ⟨_, ⟨_, h, rfl⟩, by
          rw [← orthogonalLineEquiv_apply e he y t, ContinuousLinearEquiv.symm_apply_apply]⟩
      exact hy (by simp only [h0 (ℓ y / 2), h0 (-(ℓ y / 2)), map_zero, Prod.fst_zero, add_zero,
        smul_zero])
  tsupport_subset' := subset_univ _

private theorem integrable_min_one_mul {H : Type*} [MeasurableSpace H] {μ : Measure H}
    {L : H → ℝ} (hLi : Integrable L μ) (hL0 : ∀ y, 0 ≤ L y) {M : ℝ} (hM0 : 0 ≤ M) :
    Integrable (fun y => min 1 (M * L y)) μ :=
  (hLi.const_mul M).mono'
    (aestronglyMeasurable_const.aemeasurable.inf
      (hLi.aestronglyMeasurable.const_mul M).aemeasurable).aestronglyMeasurable
    (.of_forall fun y => by
      rw [Real.norm_of_nonneg (le_min zero_le_one (mul_nonneg hM0 (hL0 y)))]
      exact min_le_right _ _)

/-- Single-bump slab bound when `volume D ≠ ⊤`: integrating `div ψ₀` over `{|t| < L_ρ / 2}` is
bounded by the variational functional at `φ = mollify B` plus `L¹` mollification errors. -/
private theorem symmSlab_integral_le_variational_add_err (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ⊤)
    (ψ₀ : 𝓓(⊤, E)) (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1)
    {Mψ : ℝ} (hM0 : 0 ≤ Mψ) (hMψ : ∀ x, ‖fderiv ℝ (fun z : E => ⟪e, ψ₀ z⟫) x‖ ≤ Mψ)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    let L : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
    ∃ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)), (∀ y, ‖φ y‖ ≤ 1) ∧
      IntegrableOn (fun z : (ℝ ∙ e)ᗮ => √(1 - ‖φ z‖ ^ 2))
        {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(
          (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y / 2))..(
          (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y / 2),
          divergenceCLM ψ₀ ((y : E) + t • e)) ≤
        2 * (∫ z in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
            √(1 - ‖φ z‖ ^ 2)) +
          (∫ z : (ℝ ∙ e)ᗮ, divergenceCLM φ z * L z) +
          2 * ((∫ z, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => min 1 (Mψ * L y)) z -
              min 1 (Mψ * L z)‖) +
            Mψ * ∫ y, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y - L y‖) := by
  intro L
  set D : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  have hDm : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hLi : Integrable L volume := integrable_measureReal_lineSection hs hfin e he
  set L_ρ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L
  have hLρ_s : ContDiff ℝ ∞ L_ρ :=
    (ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _ ρ.contDiff_normed
      hLi.locallyIntegrable
  have hLρ0 (y : (ℝ ∙ e)ᗮ) : 0 ≤ L_ρ y :=
    le_convolution_lsmul_of_forall_le ρ.support_normed_eq.subset ρ.nonneg_normed ρ.integral_normed
      ((ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left _
        (ρ.continuous_normed (μ := volume)) hLi.locallyIntegrable y) fun _ _ => measureReal_nonneg
  let B := slabHorizAvg e he ψ₀ hLρ_s; let φ := B.mollify volume ρ (subset_univ _)
  set d : (ℝ ∙ e)ᗮ → ℝ := fun y =>
    (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (L_ρ y / 2) • e)⟫ - ⟪e, ψ₀ ((y : E) + (-(L_ρ y / 2)) • e)⟫)
  obtain ⟨hdc, hdi⟩ : Continuous d ∧ Integrable d volume :=
    continuous_and_integrable_slabVerticalDiff e he ψ₀ hLρ_s
  have hφ_sq (z : (ℝ ∙ e)ᗮ) : ‖φ z‖ ^ 2 + (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z ^ 2 ≤ 1 := by
    rw [mollify_apply]; exact norm_sq_add_sq_normed_convolution_le_one ρ B.continuous hdc
      (norm_sq_slabBoundaryAvg_le_one e he ψ₀ hψ1 L_ρ) z
  have hφ1 (z : (ℝ ∙ e)ᗮ) : ‖φ z‖ ≤ 1 := by
    nlinarith [norm_nonneg (φ z), hφ_sq z, sq_nonneg ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z)]
  have hwi : IntegrableOn (fun z : (ℝ ∙ e)ᗮ => √(1 - ‖φ z‖ ^ 2)) D volume :=
    (integrableOn_const (C := (1 : ℝ)) hDfin).mono'
      (Real.continuous_sqrt.comp (continuous_const.sub
        (φ.continuous.norm.pow 2))).aestronglyMeasurable.restrict
      (.of_forall fun z => (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le
        (Real.sqrt_le_one.2 (sub_le_self _ (sq_nonneg _))))
  refine ⟨φ, hφ1, hwi, ?_⟩
  have hgi := integrable_min_one_mul hLi (fun _ => measureReal_nonneg) hM0
  have hL_err : Integrable (L_ρ - L) volume :=
    ((ρ.integrable_normed (μ := volume)).integrable_convolution (lsmul ℝ ℝ) hLi).sub hLi
  have hd_le (y : (ℝ ∙ e)ᗮ) : |d y| ≤ min 1 (Mψ * L y) + Mψ * |L_ρ y - L y| :=
    abs_slabVerticalDiff_le e he ψ₀ hψ1 hM0 hMψ (L := L) hLρ0 y
  have hg0 (z : (ℝ ∙ e)ᗮ) (hz : z ∈ Dᶜ) : min 1 (Mψ * L z) = 0 := by
    have hz0 : volume {t : ℝ | (z : E) + t • e ∈ s} = 0 := by simpa [D] using hz
    simp [L, measureReal_def, hz0]
  have hd_int := integral_normed_convolution_le_setIntegral_add_errors ρ hdi hgi hL_err hDm hg0
    hM0 hd_le hwi fun z _ => Real.le_sqrt_of_sq_le (by rw [sq_abs]; linarith [hφ_sq z])
  have hslab := (integrable_and_integral_divergenceCLM_symmSlab_eq e he ψ₀ hLρ_s).2
  have hibp := neg_integral_fderiv_normed_convolution_eq ρ hLi B
  change (∫ y : (ℝ ∙ e)ᗮ, _) = 2 * (∫ y : (ℝ ∙ e)ᗮ, d y) - ∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ L_ρ y (B y)
    at hslab
  change -∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ L_ρ y (B y) = ∫ z : (ℝ ∙ e)ᗮ, divergenceCLM φ z * L z at hibp
  linarith

private theorem symmSlab_approx_sub_le (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (ψ₀ : 𝓓(⊤, E)) {C₀ : ℝ} (hC₀ : ∀ x, ‖divergenceCLM ψ₀ x‖ ≤ C₀)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    let L : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
    (∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x) -
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y / 2))..
          ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y / 2),
        divergenceCLM ψ₀ ((y : E) + t • e)) ≤
      C₀ * ∫ y : (ℝ ∙ e)ᗮ, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L) y - L y‖ := by
  intro L
  have hLi : Integrable L volume := integrable_measureReal_lineSection hs hfin e he
  set L_ρ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L
  have hLρ_s : ContDiff ℝ ∞ L_ρ :=
    (ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _
      ρ.contDiff_normed hLi.locallyIntegrable
  obtain ⟨hi_L, hI_eq⟩ :=
    integrable_and_setIntegral_steinerSymmetrization_eq_integral_intervalIntegral hs hfin e he ψ₀
  have herr_i : Integrable (fun y : (ℝ ∙ e)ᗮ => C₀ * ‖L_ρ y - L y‖) volume :=
    (((ρ.integrable_normed (μ := volume)).integrable_convolution
      (lsmul ℝ ℝ) hLi).sub hLi).norm.const_mul C₀
  have hfc (y : (ℝ ∙ e)ᗮ) : Continuous (fun t : ℝ => divergenceCLM ψ₀ ((y : E) + t • e)) :=
    (divergenceCLM ψ₀).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hpt (y : (ℝ ∙ e)ᗮ) :
      ‖(∫ t in (-(L y / 2))..(L y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) -
        (∫ t in (-(L_ρ y / 2))..(L_ρ y / 2), divergenceCLM ψ₀ ((y : E) + t • e))‖ ≤
        C₀ * ‖L_ρ y - L y‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (L_ρ y) (L y)]
    exact abs_intervalIntegral_symm_sub_le (hfc y) (fun t => hC₀ ((y : E) + t • e)) (L y) (L_ρ y)
  rw [hI_eq, ← integral_sub hi_L
    (integrable_and_integral_divergenceCLM_symmSlab_eq e he ψ₀ hLρ_s).1, ← integral_const_mul]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
    (norm_integral_le_of_norm_le herr_i (.of_forall hpt)))

/-- When `volume D ≠ ⊤`, testing `S_e s` against any `ψ₀ ∈ 𝓓(⊤, E)` with `‖ψ₀‖ ≤ 1` is bounded by
the transverse variational supremum. -/
private theorem ofReal_setIntegral_steinerSymmetrization_le_iSup
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ⊤)
    (ψ₀ : 𝓓(⊤, E)) (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) :
    ENNReal.ofReal (∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x) ≤
      ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
        2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
  let ρ : ℕ → ContDiffBump (0 : (ℝ ∙ e)ᗮ) := ContDiffBump.shrinking one_pos
  have hρ_lim : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  have hg_cd : ContDiff ℝ ∞ (fun z : E => ⟪e, ψ₀ z⟫) := (innerSL ℝ e).contDiff.comp ψ₀.contDiff
  have hg_cs : HasCompactSupport (fun z : E => ⟪e, ψ₀ z⟫) :=
    ψ₀.hasCompactSupport.comp_left (inner_zero_right e)
  obtain ⟨M₀, hM₀⟩ := (hg_cd.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hg_cs.fderiv ℝ)
  obtain ⟨Cψ, hCψ⟩ := (divergenceCLM ψ₀).continuous.bounded_above_of_compact_support
    (divergenceCLM ψ₀).hasCompactSupport
  set Mψ := max M₀ 0; set C₀ := max Cψ 0
  have hLi := integrable_measureReal_lineSection hs hfin e he
  have hgi := integrable_min_one_mul hLi (fun _ => measureReal_nonneg) (le_max_right M₀ 0 : 0 ≤ Mψ)
  have hL_lim := tendsto_integral_norm_normed_convolution_sub hρ_lim hLi
  have hg_lim := tendsto_integral_norm_normed_convolution_sub hρ_lim hgi
  set I₀ : ℝ := ∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x
  have hlim := (tendsto_const_nhds (x := I₀)).sub ((hL_lim.const_mul C₀).add
    ((hg_lim.add (hL_lim.const_mul Mψ)).const_mul 2))
  simp only [mul_zero, add_zero, sub_zero] at hlim
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) (.of_forall fun k => ?_)
  obtain ⟨φ, hφ1, hwi, hslab⟩ := symmSlab_integral_le_variational_add_err e he hs hfin hDfin ψ₀
    hψ1 (Mψ := Mψ) (le_max_right M₀ 0) (fun x => (hM₀ x).trans (le_max_left M₀ 0)) (ρ k)
  have herr₀ : I₀ - _ ≤ _ := symmSlab_approx_sub_le e he hs hfin ψ₀
    (C₀ := C₀) (fun x => (hCψ x).trans (le_max_left Cψ 0)) (ρ k)
  have hD_eq : ENNReal.ofReal (2 * ∫ z in
        {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}, √(1 - ‖φ z‖ ^ 2)) =
      2 * ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal hwi (.of_forall fun _ => Real.sqrt_nonneg _)]
  refine le_trans ?_ (le_iSup₂_of_le φ hφ1 le_rfl)
  rw [← hD_eq]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  dsimp only at hslab herr₀
  linarith

/-- **Variational formula for the perimeter of a Steiner symmetral.** For any null-measurable set
`s` of finite volume and any unit vector `e`, `P(S_e s)` equals the supremum of
`2 ∫_D √(1 - ‖φ‖²) + ∫ div φ · L` over `φ ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)` satisfying `‖φ‖ ≤ 1`. -/
theorem perimeter_steinerSymmetrization_eq_iSup (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤) :
    perimeter volume ⊤ (steinerSymmetrization e he s) =
      ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
        2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
  refine le_antisymm ?_ (iSup₂_le fun φ hφ => ?_)
  · set D : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
    rcases eq_or_ne (volume D) ⊤ with hDtop | hDfin
    · refine le_top.trans
        (le_iSup₂_of_le (0 : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ)) (by simp) ?_)
      have h0 : 2 * (∫⁻ y in D,
          ENNReal.ofReal √(1 - ‖(0 : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ)) y‖ ^ 2)) = ⊤ := by
        have h1 : (fun y : (ℝ ∙ e)ᗮ =>
            ENNReal.ofReal √(1 - ‖(0 : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ)) y‖ ^ 2)) =
            fun _ => 1 := by
          ext y; simp only [FunLike.coe_zero, Pi.zero_apply, norm_zero]; norm_num
        rw [h1, setLIntegral_one, hDtop, ENNReal.mul_top (by norm_num)]
      rw [h0, top_add]
    · rw [perimeter_eq_iSup (nullMeasurableSet_steinerSymmetrization e he hs)]
      exact iSup₂_le fun ψ₀ hψ1 =>
        ofReal_setIntegral_steinerSymmetrization_le_iSup e he hs hfin hDfin ψ₀ hψ1
  · have hfinS : volume (steinerSymmetrization e he s) ≠ ⊤ := by
      rwa [volume_steinerSymmetrization e he hs]
    have hle := two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
      (nullMeasurableSet_steinerSymmetrization e he hs) hfinS e he .empty
      (.of_forall fun _ h => False.elim h) φ hφ
    simp only [measureReal_def, volume_lineSection_steinerSymmetrization] at hle ⊢
    exact (add_le_add le_self_add le_rfl).trans hle

end SmoothSymmetricSlab

/-! ### Quantitative noninterval excess and Steiner perimeter equality rigidity -/

section SteinerEqualityRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Rescaling any `φ` (`‖φ‖ ≤ 1`) to `(1 - δ) • φ` (`0 ≤ δ ≤ 1`) scales the main variational
functional by at least `1 - δ` while gaining `2 √(2 δ - δ²) |A|` on any null-measurable family `A`
of noninterval sections. -/
private theorem mul_variational_add_excess_le_perimeter (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ENNReal.ofReal (1 - δ) *
        (2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s})) +
      2 * ENNReal.ofReal √(2 * δ - δ ^ 2) * volume A ≤
      perimeter volume ⊤ s := by
  have h1δ : 0 ≤ 1 - δ := sub_nonneg.2 hδ1
  have hφ' (y : (ℝ ∙ e)ᗮ) : ‖((1 - δ) • φ) y‖ ≤ 1 := by
    rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1δ]
    exact (mul_le_of_le_one_right h1δ (hφ y)).trans (by linarith)
  have hex := two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
    hs hfin e he hA hbad ((1 - δ) • φ) hφ'
  have hD_le : ENNReal.ofReal (1 - δ) *
      (2 * ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) ≤
      2 * ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖((1 - δ) • φ) y‖ ^ 2) := by
    rw [mul_left_comm (ENNReal.ofReal (1 - δ)) 2,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr 2 * ?_
    refine lintegral_mono fun y => ?_
    have hrhs : ENNReal.ofReal √((1 - δ) ^ 2 * (1 - ‖φ y‖ ^ 2)) =
        ENNReal.ofReal (1 - δ) * ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1δ, ENNReal.ofReal_mul h1δ]
    rw [← hrhs, FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1δ]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    have hsq1 : (1 - δ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖φ y‖]
  have hB_eq : ENNReal.ofReal (1 - δ) * ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) =
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM ((1 - δ) • φ) y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
    rw [← ENNReal.ofReal_mul h1δ, ← integral_const_mul]
    congr 1; refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hA_le : 2 * ENNReal.ofReal √(2 * δ - δ ^ 2) * volume A ≤
      2 * ∫⁻ y in A, ENNReal.ofReal √(1 - ‖((1 - δ) • φ) y‖ ^ 2) := by
    rw [mul_assoc, ← setLIntegral_const A (ENNReal.ofReal √(2 * δ - δ ^ 2))]
    gcongr 2 * ?_
    refine lintegral_mono fun y => ?_
    rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1δ, mul_pow]
    have hsq : ‖φ y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hφ y)
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - δ)]))
  rw [mul_add, hB_eq, add_right_comm]
  exact (add_le_add (add_le_add hD_le hA_le) le_rfl).trans hex

/-- **Scaled Steiner perimeter and noninterval excess bound.** For any null-measurable set `s` of
finite volume, a unit vector `e`, a null-measurable family `A` of noninterval line sections, and
`δ ∈ [0, 1]`,
`(1 - δ) P(S_e s) + 2 √(2 δ - δ²) |A| ≤ P(s)`. -/
theorem ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ) * perimeter volume ⊤ (steinerSymmetrization e he s) +
        2 * ENNReal.ofReal √(2 * δ - δ ^ 2) * volume A ≤
      perimeter volume ⊤ s := by
  let Φ := {φ : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ) // ∀ y, ‖φ y‖ ≤ 1}
  have : Nonempty Φ := ⟨⟨0, by simp⟩⟩
  let V : Φ → ℝ≥0∞ := fun p =>
    2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
      ENNReal.ofReal √(1 - ‖p.1 y‖ ^ 2)) +
    ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM p.1 y *
      volume.real {t : ℝ | (y : E) + t • e ∈ s})
  have hsup : perimeter volume ⊤ (steinerSymmetrization e he s) = ⨆ p : Φ, V p := by
    rw [perimeter_steinerSymmetrization_eq_iSup e he hs hfin, iSup_subtype]
  rw [hsup, ENNReal.mul_iSup, ENNReal.iSup_add]
  exact iSup_le fun p =>
    mul_variational_add_excess_le_perimeter e he hs hfin hA hbad hδ0 hδ1 p.1 p.2

private theorem eq_zero_of_forall_delta_le {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (hdelta : ∀ {δ : ℝ}, 0 < δ → δ < 1 → (1 - δ) * p + 2 * √(2 * δ - δ ^ 2) * a ≤ p) :
    a = 0 := by
  by_contra ha_ne
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_ne)
  set δ := 4 * a ^ 2 / (p ^ 2 + 4 * a ^ 2)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := (div_lt_one (by positivity)).2 (by linarith [mul_pos hp hp])
  have hb := hdelta hδ0 hδ1
  have hsq : 4 * (2 * δ - δ ^ 2) * a ^ 2 ≤ (δ * p) ^ 2 := by
    have hsub : 2 * √(2 * δ - δ ^ 2) * a ≤ δ * p := by linarith
    calc 4 * (2 * δ - δ ^ 2) * a ^ 2
        = (2 * √(2 * δ - δ ^ 2) * a) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]; ring
      _ ≤ (δ * p) ^ 2 := pow_le_pow_left₀ (by positivity) hsub 2
  have hid : δ * (p ^ 2 + 4 * a ^ 2) = 4 * a ^ 2 := div_mul_cancel₀ _ (by positivity)
  have hmul_id : δ ^ 2 * (p ^ 2 + 4 * a ^ 2) = 4 * δ * a ^ 2 := by
    calc δ ^ 2 * (p ^ 2 + 4 * a ^ 2) = δ * (δ * (p ^ 2 + 4 * a ^ 2)) := by ring
      _ = 4 * δ * a ^ 2 := by rw [hid]; ring
  linarith [mul_pos hδ0 (sq_pos_of_pos ha_pos)]

private theorem sq_add_four_mul_sq_le_of_forall_delta {p p₀ a : ℝ}
    (hp₀ : 0 ≤ p₀) (ha : 0 ≤ a) (hp₀_le : p₀ ≤ p) (h2a : 2 * a ≤ p)
    (hdelta : ∀ {δ : ℝ}, 0 < δ → δ < 1 → (1 - δ) * p₀ + 2 * √(2 * δ - δ ^ 2) * a ≤ p) :
    p₀ ^ 2 + 4 * a ^ 2 ≤ p ^ 2 := by
  rcases eq_or_lt_of_le hp₀ with hp₀_eq | hp₀_pos
  · rw [← hp₀_eq]; nlinarith
  rcases eq_or_lt_of_le hp₀_le with hp_eq | hp₀_lt
  · subst hp_eq
    have ha_zero : a = 0 := eq_zero_of_forall_delta_le hp₀_pos ha hdelta
    rw [ha_zero]; ring_nf; exact le_rfl
  · have hp_pos : 0 < p := hp₀_pos.trans hp₀_lt
    set δ := 1 - p₀ / p
    have hδ0 : 0 < δ := sub_pos.2 ((div_lt_one hp_pos).2 hp₀_lt)
    have hδ1 : δ < 1 := sub_lt_self 1 (div_pos hp₀_pos hp_pos)
    have hb := hdelta hδ0 hδ1
    have h1δ : 1 - δ = p₀ / p := by ring
    have h2δ : 2 * δ - δ ^ 2 = (p ^ 2 - p₀ ^ 2) / p ^ 2 := by
      calc 2 * δ - δ ^ 2 = 1 - (1 - δ) ^ 2 := by ring
        _ = 1 - (p₀ / p) ^ 2 := by rw [h1δ]
        _ = (p ^ 2 - p₀ ^ 2) / p ^ 2 := by rw [div_pow, one_sub_div (by positivity)]
    rw [h1δ, h2δ, Real.sqrt_div (by nlinarith), Real.sqrt_sq hp_pos.le] at hb
    have hmul : p₀ ^ 2 + 2 * √(p ^ 2 - p₀ ^ 2) * a ≤ p ^ 2 := by
      have hbp := mul_le_mul_of_nonneg_right hb hp_pos.le
      calc p₀ ^ 2 + 2 * √(p ^ 2 - p₀ ^ 2) * a
          = (p₀ / p * p₀ + 2 * (√(p ^ 2 - p₀ ^ 2) / p) * a) * p := by field_simp
        _ ≤ p * p := hbp
        _ = p ^ 2 := (sq p).symm
    have hdiff_pos : 0 ≤ p ^ 2 - p₀ ^ 2 := by nlinarith
    have h2a_sqrt : 2 * a ≤ √(p ^ 2 - p₀ ^ 2) := by
      have hle_sqrt : 2 * √(p ^ 2 - p₀ ^ 2) * a ≤ √(p ^ 2 - p₀ ^ 2) ^ 2 := by
        rw [Real.sq_sqrt hdiff_pos]; linarith
      have hrt_pos : 0 < √(p ^ 2 - p₀ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      nlinarith
    have hsq : (2 * a) ^ 2 ≤ √(p ^ 2 - p₀ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2a_sqrt 2
    rw [Real.sq_sqrt hdiff_pos] at hsq
    linarith

/-- **Pythagorean noninterval excess in Steiner's perimeter inequality.** For any null-measurable
set `s` of finite volume, a unit vector `e`, and any null-measurable family `A` of noninterval line
sections of `s` in direction `e`,
`P(S_e s)² + 4 |A|² ≤ P(s)²`. -/
theorem perimeter_steinerSymmetrization_sq_add_four_mul_volume_sq_le
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ^ 2 + 4 * volume A ^ 2 ≤
      perimeter volume ⊤ s ^ 2 := by
  set P := perimeter volume ⊤ s
  set P₀ := perimeter volume ⊤ (steinerSymmetrization e he s)
  rcases eq_or_ne P ⊤ with hPtop | hPfin
  · simp [hPtop]
  have hP₀_le : P₀ ≤ P := perimeter_steinerSymmetrization_le e he hs hfin
  have hP₀_fin : P₀ ≠ ⊤ := ne_top_of_le_ne_top hPfin hP₀_le
  have h2A : 2 * volume A ≤ P := le_add_self.trans
    (two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection hs hfin e he hA hbad)
  have hA_fin : volume A ≠ ⊤ := fun htop => hPfin (top_unique (by simpa [htop] using h2A))
  set p := P.toReal; set p₀ := P₀.toReal; set a := (volume A).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp₀0 : 0 ≤ p₀ := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have h2a_le : 2 * a ≤ p := by
    simpa [p, a, ENNReal.toReal_mul] using ENNReal.toReal_mono hPfin h2A
  have hdelta {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
      (1 - δ) * p₀ + 2 * √(2 * δ - δ ^ 2) * a ≤ p := by
    have h := ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter e he hs hfin hA hbad
      hδ0.le hδ1.le
    have hlt := ENNReal.toReal_mono hPfin h
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP₀_fin)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hA_fin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hδ1.le), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hlt
  have hreal : p₀ ^ 2 + 4 * a ^ 2 ≤ p ^ 2 :=
    sq_add_four_mul_sq_le_of_forall_delta hp₀0 ha0 (ENNReal.toReal_mono hPfin hP₀_le) h2a_le hdelta
  have hof := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (sq_nonneg p₀) (mul_nonneg (by norm_num) (sq_nonneg a)),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hp₀0,
    ENNReal.ofReal_pow ha0, ENNReal.ofReal_pow hp0, ENNReal.ofReal_toReal hP₀_fin,
    ENNReal.ofReal_toReal hA_fin, ENNReal.ofReal_toReal hPfin] at hof
  exact hof

/-- **Pythagorean noninterval excess for the full family of noninterval sections.** For any
null-measurable set `s` of finite volume and any unit vector `e`,
`P(S_e s)² + 4 |{y | s_y is not a.e. an interval}|² ≤ P(s)²`. -/
theorem perimeter_steinerSymmetrization_sq_add_four_mul_volume_noninterval_sq_le
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ^ 2 +
        4 * volume {y : (ℝ ∙ e)ᗮ |
          ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} ^ 2 ≤
      perimeter volume ⊤ s ^ 2 :=
  perimeter_steinerSymmetrization_sq_add_four_mul_volume_sq_le e he hs hfin
    (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ => id)

/-- **Steiner perimeter equality forces interval sections.** If a null-measurable set `s` of finite
volume and finite perimeter satisfies `P(S_e s) = P(s)`, then for almost every `y ∈ (ℝ ∙ e)ᗮ` the
line section `{t | y + t • e ∈ s}` agrees almost everywhere with an order-connected set (an
interval, possibly empty). -/
theorem ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (hPfin : perimeter volume ⊤ s ≠ ⊤)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, I.OrdConnected ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  set A : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ |
    ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  have hpyth :=
    perimeter_steinerSymmetrization_sq_add_four_mul_volume_noninterval_sq_le e he hs hfin
  rw [heq] at hpyth
  have hP2_fin : perimeter volume ⊤ s ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hPfin
  have h0 : 4 * volume A ^ 2 = 0 := by
    have hadd : perimeter volume ⊤ s ^ 2 + 4 * volume A ^ 2 = perimeter volume ⊤ s ^ 2 + 0 :=
      le_antisymm (hpyth.trans_eq (add_zero _).symm) (by simp)
    exact (ENNReal.add_right_inj hP2_fin).1 hadd
  have hA0 : volume A = 0 := by
    rcases mul_eq_zero.1 h0 with h4 | hsq
    · norm_num at h4
    · exact sq_eq_zero_iff.1 hsq
  filter_upwards [compl_mem_ae_iff.2 hA0] with y hy
  by_contra! hbad
  exact hy hbad

end SteinerEqualityRigidity

end TauCeti
