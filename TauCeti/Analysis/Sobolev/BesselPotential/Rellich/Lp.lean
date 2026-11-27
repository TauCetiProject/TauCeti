/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.ImaginaryOrder
import TauCeti.Analysis.Sobolev.BesselPotential.Kernel
import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Sobolev.BesselPotential.OrderInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.SobolevEmbedding
import TauCeti.MeasureTheory.Function.Lp.Operator.Convolution

/-!
# The Rellich theorem for Bessel-potential spaces `H^{s,p}`

Let `E` be a finite-dimensional real inner product space, `F` a finite-dimensional complex inner
product space and `1 < p < ∞`. For a Schwartz function `φ` and real orders
`r < s`, multiplication by `φ` followed by the inclusion `H^{s,p} ⊆ H^{r,p}` is a **compact
operator** `H^{s,p}(E, F) → H^{r,p}(E, F)` between Mathlib's Bessel-potential spaces
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt`). So a bounded subset
of `H^{s,p}` whose elements satisfy `φ u = u`, for instance because they are supported in a fixed
compact set on a neighbourhood of which `φ = 1`, has compact closure in `H^{r,p}`
(`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLMOfOneLt_eq`). This is the
Rellich theorem for a common compact support on the `Lᵖ` Sobolev scale; for `p = 2` it is
`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`, proved there on the Fourier
side, which is not available for `p ≠ 2`. Multiplication by `φ` is the bounded operator
`BesselPotentialSpace.smulLeftCLMOfOneLt` on `H^{s,p}`, for every real `s`.

## The argument

* **Order `0`.** For `r < 0`, the Bessel potential `J^r` is convolution with the integrable Bessel
  kernel `G_{-r}` (`TemperedDistribution.besselPotential_neg_toTemperedDistribution_apply`), so in
  the `Lᵖ` coordinates `u ↦ J^s u` of the two spaces the operator `u ↦ φ u` from `H^{0,p}` to
  `H^{r,p}` is the integral operator `w ↦ G_{-r} ⋆ (φ w)` with kernel `G_{-r} (x - y) φ y`. If
  `gₙ` are continuous compactly supported functions tending to `G_{-r}` in `L¹` and `χₙ` are
  continuous compactly supported cutoffs with `χₙ φ → φ` uniformly, the kernels
  `gₙ (x - y) χₙ(y) φ y` are continuous and compactly supported, so they give compact operators
  (`TauCeti.isCompactOperator_integralOperatorLp_of_continuousOn`), and by Schur's test they
  converge to the given one in operator norm
  (`TauCeti.isCompactOperator_integralOperatorLp_convMulKernel_of_tendsto`).
* **Orders `2k`.** The Bessel potential `J² = 1 - (2π)⁻² Δ` commutes with `φ` up to lower order
  terms whose coefficients are again Schwartz functions:
  `J² (φ u) = φ J² u - (2π)⁻² ∑ᵢ (∂ᵢ² φ u + 2 ∂ᵢ φ ∂ᵢ u)` and
  `φ J² w = J² (φ w) + (2π)⁻² ∑ᵢ (2 ∂ᵢ (∂ᵢ φ w) - ∂ᵢ² φ w)`, for an orthonormal basis of `E`
  (`TemperedDistribution.besselPotential_two_smulLeftCLM`,
  `TemperedDistribution.smulLeftCLM_besselPotential_two`).
  The first identity moves compactness from the order `t` to `t + 2`, the second to `t - 2`, for
  all multipliers at once, since `J²` is an isomorphism `H^{t + 2,p} ≃ H^{t,p}`.
* **All real orders.** If `2k ≤ s`, the operator into `H^{r,p}` factors through the even order
  `2k` when `r < 2k`. For `2k ≤ r < s` it is compact into `H^{2k - 1,p}`, and the complex
  interpolation `[H^{2k - 1,p}, H^{s,p}]_θ = H^{r,p}` gives the bound
  `‖v‖_{H^{r,p}} ≤ C ‖v‖_{H^{2k - 1,p}} ^ (1 - θ) ‖v‖_{H^{s,p}} ^ θ` with `θ < 1`
  (`BesselPotentialSpace.exists_norm_inclusion_le_mul_norm_inclusion_rpow_mul_norm_rpow`), which
  turns compactness into `H^{2k - 1,p}` into compactness into `H^{r,p}`
  (`IsCompactOperator.of_norm_le_mul_rpow_mul_rpow`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 6.4.5 (7) (complex interpolation of the spaces `H^{s,p}`).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  University Press, 1970, Chapter V, §3 (the Bessel kernel and the potential spaces).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution Filter Set Function
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace Topology

namespace BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The case of order `0` -/

section OrderZero

variable [CompleteSpace F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- For `u ∈ H^{0,p}` and `r < 0`, the `Lᵖ` function of `φ u ∈ H^{r,p}` is `G_{-r} ⋆ (φ u)`, the
integral operator with kernel `G_{-r} (x - y) φ y` applied to the `Lᵖ` function of `u`. -/
private theorem toLp_inclusion_smulLeftCLMOfOneLt_eq (hp : 1 < p)
    (hp_top : p ≠ ∞) {φ : 𝓢(E, ℂ)} {C : ℝ≥0} (hC : ∀ y, ‖φ y‖ ≤ C) {r : ℝ} (hr : r < 0)
    {hK : AEStronglyMeasurable
      (uncurry (TauCeti.convMulKernel F (fun z ↦ (TauCeti.besselKernel (-r) z : ℂ)) φ))
      (volume.prod volume)}
    {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂(volume : Measure E),
      ∫⁻ y, ‖TauCeti.convMulKernel F (fun z ↦ (TauCeti.besselKernel (-r) z : ℂ)) φ x y‖ₑ ≤ A}
    {hB : ∀ᵐ y ∂(volume : Measure E),
      ∫⁻ x, ‖TauCeti.convMulKernel F (fun z ↦ (TauCeti.besselKernel (-r) z : ℂ)) φ x y‖ₑ ≤ B}
    (u : H^{0, p}(E, F)) :
    (inclusion hr.le (smulLeftCLMOfOneLt hp hp_top φ u)).toLp =
      TauCeti.integralOperatorLp
        (TauCeti.convMulKernel F (fun z ↦ (TauCeti.besselKernel (-r) z : ℂ)) φ) p hK hA hB
        u.toLp := by
  have hu : u.toDistr = (u.toLp : 𝓢'(E, F)) := by
    rw [← u.bessel_toDistr_eq_toLp, besselPotential_zero, ContinuousLinearMap.id_apply]
  obtain ⟨v, hv, -⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le
    (g := (φ : E → ℂ)) (Eventually.of_forall hC) u.toLp
  have hvφ := (Lp.toTemperedDistribution_eq_smulLeftCLM_iff φ.hasTemperateGrowth v u.toLp).1
    hv.symm
  refine Lp.toTemperedDistribution_injective ?_
  dsimp only
  rw [← BesselPotentialSpace.bessel_toDistr_eq_toLp, toDistr_inclusion,
    toDistr_smulLeftCLMOfOneLt, hu, hv]
  ext χ
  have hJ := besselPotential_neg_toTemperedDistribution_apply (neg_pos.2 hr) v χ
  rw [neg_neg] at hJ
  rw [hJ, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.coeFn_integralOperatorLp (hK := hK) (hA := hA) (hB := hB) u.toLp]
    with x hx
  rw [hx, convolution_eq_swap]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hvφ] with y hy
  simp [hy, mul_smul, smul_comm (φ y)]

/-- **The Rellich theorem at order `0`.** For a Schwartz function `φ` and `r < 0`, `u ↦ φ u` is
compact from `H^{0,p} = Lᵖ` to `H^{r,p}`: in the `Lᵖ` coordinates of the two spaces it is
`w ↦ G_{-r} ⋆ (φ w)`. -/
private theorem isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt_zero (hp : 1 < p)
    (hp_top : p ≠ ∞) (φ : 𝓢(E, ℂ)) {r : ℝ} (hr : r < 0) :
    IsCompactOperator (inclusion hr.le ∘L smulLeftCLMOfOneLt hp hp_top φ :
      H^{0, p}(E, F) →L[ℂ] H^{r, p}(E, F)) := by
  have hC (y : E) : ‖φ y‖ ≤ ‖φ.toBoundedContinuousFunction‖₊ := by
    simpa using φ.toBoundedContinuousFunction.norm_coe_le_norm y
  set g : E → ℂ := fun z ↦ (TauCeti.besselKernel (-r) z : ℂ)
  have hg : Integrable g := (TauCeti.integrable_besselKernel (neg_pos.2 hr)).ofReal
  have hfin : ∫⁻ z, ‖g z‖ₑ ≤ (∫⁻ z, ‖g z‖ₑ).toNNReal :=
    (ENNReal.coe_toNNReal hg.hasFiniteIntegral.ne).ge
  have hAB := TauCeti.ae_lintegral_enorm_convMulKernel_le (F := F) hC hfin
  set T := TauCeti.integralOperatorLp (TauCeti.convMulKernel F g φ) p
    (TauCeti.aestronglyMeasurable_convMulKernel hg.aestronglyMeasurable φ.continuous) hAB.1 hAB.2
  have hT : IsCompactOperator T :=
    TauCeti.isCompactOperator_integralOperatorLp_convMulKernel_of_tendsto hg φ.continuous
      φ.tendsto_cocompact
  have heq : (inclusion hr.le ∘L smulLeftCLMOfOneLt hp hp_top φ :
      H^{0, p}(E, F) →L[ℂ] H^{r, p}(E, F)) =
      ((toLpₗᵢ E F r p).symm.toContinuousLinearEquiv :
        Lp F p (volume : Measure E) →L[ℂ] H^{r, p}(E, F)) ∘L T ∘L
        ((toLpₗᵢ E F 0 p).toContinuousLinearEquiv :
          H^{0, p}(E, F) →L[ℂ] Lp F p (volume : Measure E)) := by
    ext1 u
    apply (toLpₗᵢ E F r p).injective
    simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply,
      toLpₗᵢ_apply]
    exact toLp_inclusion_smulLeftCLMOfOneLt_eq hp hp_top hC hr u
  rw [heq, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (hT.comp_clm _).clm_comp _

end OrderZero

/-! ### Raising and lowering the order by two -/

section Steps

open scoped LineDeriv Real

variable [CompleteSpace F] (hp : 1 < p) (hp_top : p ≠ ∞)

variable (E F) in
/-- The Rellich property at order `t`: for every Schwartz function `φ` and every `r < t`,
`u ↦ φ u` is compact from `H^{t,p}` to `H^{r,p}`. -/
private def RellichAt (t : ℝ) : Prop :=
  ∀ φ : 𝓢(E, ℂ), ∀ r (hr : r < t),
    IsCompactOperator (inclusion hr.le ∘L smulLeftCLMOfOneLt (s := t) hp hp_top φ :
      H^{t, p}(E, F) →L[ℂ] H^{r, p}(E, F))

/-- **Raising the order.** If `φ u ∈ H^{r,p}` depends compactly on `u ∈ H^{t,p}` for all `φ` and
`r < t`, the same holds at order `t + 2`, because
`J² (φ u) = φ J² u - (2π)⁻² ∑ᵢ (∂ᵢ² φ u + 2 ∂ᵢ φ ∂ᵢ u)` only multiplies elements of `H^{t,p}`. -/
private theorem rellichAt_add_two {t : ℝ} (h : RellichAt E F hp hp_top t) :
    RellichAt E F hp hp_top (t + 2) := by
  intro φ r hr
  set b := stdOrthonormalBasis ℝ E
  have hrt : r - 2 < t := by linarith
  have hd (ψ : 𝓢(E, ℂ)) := h ψ (r - 2) hrt
  set D : Fin (Module.finrank ℝ E) → H^{t + 2, p}(E, F) →L[ℂ] H^{t, p}(E, F) := fun i ↦
    lineDerivCLM hp hp_top (b i) ∘L inclusion (by linarith : t + 1 ≤ t + 2)
  set S : H^{t + 2, p}(E, F) →L[ℂ] H^{r - 2, p}(E, F) :=
    (inclusion hrt.le ∘L smulLeftCLMOfOneLt hp hp_top φ) ∘L
      (inclusion (by simp only [Complex.ofReal_re]; linarith) ∘L
        besselPotentialCLM hp hp_top ((2 : ℝ) : ℂ)) -
      ((((2 * π) ^ 2)⁻¹ : ℝ) : ℂ) • ∑ i, ((inclusion hrt.le ∘L
        smulLeftCLMOfOneLt hp hp_top (∂_{b i} (∂_{b i} φ))) ∘L inclusion (by linarith) +
        ((inclusion hrt.le ∘L smulLeftCLMOfOneLt hp hp_top (∂_{b i} φ)) ∘L D i +
          (inclusion hrt.le ∘L smulLeftCLMOfOneLt hp hp_top (∂_{b i} φ)) ∘L D i))
  have hS : IsCompactOperator S := by
    let 𝒦 := compactOperator (RingHom.id ℂ) H^{t + 2, p}(E, F) H^{r - 2, p}(E, F)
    refine 𝒦.sub_mem ((hd φ).comp_clm _) (𝒦.smul_mem _ (𝒦.sum_mem fun _ _ ↦ ?_))
    exact 𝒦.add_mem ((hd _).comp_clm _) (𝒦.add_mem ((hd _).comp_clm _) ((hd _).comp_clm _))
  have heq : (inclusion hr.le ∘L smulLeftCLMOfOneLt hp hp_top φ :
      H^{t + 2, p}(E, F) →L[ℂ] H^{r, p}(E, F)) =
      (inclusion (by simp only [Complex.ofReal_re]; linarith) ∘L
        besselPotentialCLM hp hp_top ((-2 : ℝ) : ℂ)) ∘L S := by
    ext1 u
    refine ext ?_
    simp only [S, D, ContinuousLinearMap.comp_apply, sub_apply,
      smul_apply, FunLike.coe_sum, Finset.sum_apply,
      add_apply, toDistr_besselPotentialCLM_ofReal, toDistr_sub, toDistr_smul, toDistr_sum,
      toDistr_add, toDistr_inclusion, toDistr_smulLeftCLMOfOneLt, toDistr_lineDerivCLM]
    rw [← besselPotential_two_smulLeftCLM b, besselPotential_besselPotential_apply]
    norm_num
  rw [heq]
  exact hS.clm_comp (inclusion _ ∘L besselPotentialCLM hp hp_top ((-2 : ℝ) : ℂ))

/-- **Lowering the order.** If `φ w ∈ H^{r,p}` depends compactly on `w ∈ H^{t,p}` for all `φ` and
`r < t`, the same holds at order `t - 2`, because
`φ J² w = J² (φ w) + (2π)⁻² ∑ᵢ (2 ∂ᵢ (∂ᵢ φ w) - ∂ᵢ² φ w)` and `J²` maps `H^{t,p}` onto
`H^{t - 2,p}`. -/
private theorem rellichAt_sub_two {t : ℝ} (h : RellichAt E F hp hp_top t) :
    RellichAt E F hp hp_top (t - 2) := by
  intro φ r hr
  set b := stdOrthonormalBasis ℝ E
  have hd (ψ : 𝓢(E, ℂ)) {r' : ℝ} (hr' : r' < t) := h ψ r' hr'
  have h₂ : r + 2 < t := by linarith
  have h₁ : r + 1 < t := by linarith
  set D : Fin (Module.finrank ℝ E) → H^{t, p}(E, F) →L[ℂ] H^{r, p}(E, F) := fun i ↦
    lineDerivCLM hp hp_top (b i) ∘L
      (inclusion h₁.le ∘L smulLeftCLMOfOneLt hp hp_top (∂_{b i} φ))
  set S : H^{t, p}(E, F) →L[ℂ] H^{r, p}(E, F) :=
    (inclusion (by simp only [Complex.ofReal_re]; linarith) ∘L
        besselPotentialCLM hp hp_top ((2 : ℝ) : ℂ)) ∘L
        (inclusion h₂.le ∘L smulLeftCLMOfOneLt hp hp_top φ) +
      ((((2 * π) ^ 2)⁻¹ : ℝ) : ℂ) • ∑ i, ((D i + D i) -
        inclusion (by linarith : r ≤ r + 2) ∘L
          (inclusion h₂.le ∘L smulLeftCLMOfOneLt hp hp_top (∂_{b i} (∂_{b i} φ))))
  have hS : IsCompactOperator S := by
    let 𝒦 := compactOperator (RingHom.id ℂ) H^{t, p}(E, F) H^{r, p}(E, F)
    have hD : ∀ i, D i ∈ 𝒦 := fun i ↦ (hd _ h₁).clm_comp _
    refine 𝒦.add_mem
      ((hd φ h₂).clm_comp (inclusion _ ∘L besselPotentialCLM hp hp_top ((2 : ℝ) : ℂ)))
      (𝒦.smul_mem _ (𝒦.sum_mem fun i _ ↦ ?_))
    exact 𝒦.sub_mem (𝒦.add_mem (hD i) (hD i))
      ((hd _ h₂).clm_comp _)
  have heq : (inclusion hr.le ∘L smulLeftCLMOfOneLt hp hp_top φ :
      H^{t - 2, p}(E, F) →L[ℂ] H^{r, p}(E, F)) =
      S ∘L (inclusion (by simp only [Complex.ofReal_re]; linarith) ∘L
        besselPotentialCLM hp hp_top ((-2 : ℝ) : ℂ)) := by
    ext1 u
    refine ext ?_
    simp only [S, D, ContinuousLinearMap.comp_apply, sub_apply, smul_apply, FunLike.coe_sum,
      Finset.sum_apply, add_apply, toDistr_besselPotentialCLM_ofReal, toDistr_sub, toDistr_smul,
      toDistr_sum,
      toDistr_add, toDistr_inclusion, toDistr_smulLeftCLMOfOneLt, toDistr_lineDerivCLM]
    rw [← smulLeftCLM_besselPotential_two b, besselPotential_besselPotential_apply]
    norm_num
  rw [heq]
  exact hS.comp_clm _

end Steps

/-! ### The Rellich theorem -/

/-- For `p = 2`, `BesselPotentialSpace.smulLeftCLMOfOneLt` is `BesselPotentialSpace.smulLeftCLM`:
both multiply the underlying tempered distribution by `φ`. So the Rellich theorems below
specialise at `p = 2` to `BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM` and
`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`. -/
theorem smulLeftCLMOfOneLt_two_eq_smulLeftCLM [CompleteSpace F] {s : ℝ} (φ : 𝓢(E, ℂ)) :
    (smulLeftCLMOfOneLt ENNReal.one_lt_two ENNReal.ofNat_ne_top φ :
      H^{s, 2}(E, F) →L[ℂ] H^{s, 2}(E, F)) = smulLeftCLM s φ :=
  ContinuousLinearMap.ext fun _ ↦ ext (by simp)

section Rellich

variable [CompleteSpace F] [FiniteDimensional ℂ F]

private theorem rellichAt_two_mul (hp : 1 < p) (hp_top : p ≠ ∞) (k : ℤ) :
    RellichAt E F hp hp_top (2 * k) := by
  induction k using Int.induction_on with
  | zero =>
    have h : RellichAt E F hp hp_top 0 := fun φ r hr ↦
      isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt_zero hp hp_top φ hr
    simpa using h
  | succ n ih =>
    convert rellichAt_add_two hp hp_top ih using 1
    push_cast
    ring
  | pred n ih =>
    convert rellichAt_sub_two hp hp_top ih using 1
    push_cast
    ring

/-- **The Rellich theorem for `H^{s,p}`.** Let `F` be a finite-dimensional complex inner product
space, `1 < p < ∞` and `φ` a Schwartz function. For real orders `r < s`,
multiplication by `φ` followed by the inclusion `H^{s,p} ⊆ H^{r,p}` is a compact operator
`H^{s,p}(E, F) → H^{r,p}(E, F)`. For `p = 2`, where `smulLeftCLMOfOneLt` is
`BesselPotentialSpace.smulLeftCLM` (`BesselPotentialSpace.smulLeftCLMOfOneLt_two_eq_smulLeftCLM`),
this is `BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`. -/
theorem isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt (hp : 1 < p) (hp_top : p ≠ ∞)
    (φ : 𝓢(E, ℂ)) {r s : ℝ} (h : r < s) :
    IsCompactOperator (inclusion h.le ∘L smulLeftCLMOfOneLt hp hp_top φ :
      H^{s, p}(E, F) →L[ℂ] H^{r, p}(E, F)) := by
  -- An even order `N = 2 ⌊s / 2⌋ ≤ s`.
  set N : ℝ := 2 * (⌊s / 2⌋ : ℤ)
  have hN : N ≤ s := by have := Int.floor_le (s / 2); simp only [N]; linarith
  -- Below `N` the operator factors through the Rellich property at order `N`.
  have hbelow (r' : ℝ) (hr' : r' < N) :
      IsCompactOperator (inclusion (hr'.trans_le hN).le ∘L smulLeftCLMOfOneLt hp hp_top φ :
        H^{s, p}(E, F) →L[ℂ] H^{r', p}(E, F)) := by
    have heq : (inclusion (hr'.trans_le hN).le ∘L smulLeftCLMOfOneLt hp hp_top φ :
        H^{s, p}(E, F) →L[ℂ] H^{r', p}(E, F)) =
        (inclusion hr'.le ∘L smulLeftCLMOfOneLt (s := N) hp hp_top φ) ∘L inclusion hN := by
      ext1 u
      exact ext (by simp)
    rw [heq]
    exact (rellichAt_two_mul hp hp_top _ φ r' hr').comp_clm _
  rcases lt_or_ge r N with hr | hr
  · exact hbelow r hr
  -- Above, interpolate between the orders `N - 1` and `s`.
  have ha : N - 1 < r := by linarith
  have hsa : 0 < s - (N - 1) := by linarith
  set θ := (r - (N - 1)) / (s - (N - 1))
  have hθ : θ ∈ Ioo (0 : ℝ) 1 := ⟨div_pos (by linarith) hsa, (div_lt_one hsa).2 (by linarith)⟩
  have hrθ : r = (1 - θ) * (N - 1) + θ * s := by
    simp only [θ]
    field_simp
    ring
  obtain ⟨C, hle⟩ := exists_norm_inclusion_le_mul_norm_inclusion_rpow_mul_norm_rpow (E := E)
    (F := F) hp hp_top ha.le h.le hθ hrθ
  refine IsCompactOperator.of_norm_le_mul_rpow_mul_rpow (hbelow (N - 1) (sub_one_lt N))
    (smulLeftCLMOfOneLt hp hp_top φ)
    (T := (inclusion h.le ∘L smulLeftCLMOfOneLt hp hp_top φ :
      H^{s, p}(E, F) →L[ℂ] H^{r, p}(E, F)).toLinearMap) (C := C) hθ.1.le hθ.2 fun w ↦ ?_
  simpa [inclusion_inclusion] using hle (smulLeftCLMOfOneLt hp hp_top φ w)

/-- **The Rellich theorem for a common compact support.** Let `F` be finite-dimensional,
`1 < p < ∞`, `φ` a Schwartz function and `r < s`. A bounded subset of
`H^{s,p}(E, F)` on which multiplication by `φ` is the identity, for instance a bounded set of
elements supported in a compact set on a neighbourhood of which `φ = 1`, has compact closure in
`H^{r,p}(E, F)`. For `p = 2` this is
`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`, through
`BesselPotentialSpace.smulLeftCLMOfOneLt_two_eq_smulLeftCLM`. -/
theorem isCompact_closure_image_inclusion_of_smulLeftCLMOfOneLt_eq (hp : 1 < p)
    (hp_top : p ≠ ∞) {φ : 𝓢(E, ℂ)} {r s : ℝ} (h : r < s)
    {S : Set H^{s, p}(E, F)} (hS : Bornology.IsBounded S)
    (hφS : ∀ u ∈ S, smulLeftCLMOfOneLt hp hp_top φ u = u) :
    IsCompact (closure (inclusion h.le '' S : Set H^{r, p}(E, F))) := by
  have himage : inclusion h.le '' S =
      (inclusion h.le ∘L smulLeftCLMOfOneLt hp hp_top φ : H^{s, p}(E, F) →L[ℂ] H^{r, p}(E, F)) ''
        S :=
    image_congr fun u hu ↦ by rw [ContinuousLinearMap.comp_apply, hφS u hu]
  rw [himage]
  exact (isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt hp hp_top φ h)
    |>.isCompact_closure_image_of_bounded hS

end Rellich

end BesselPotentialSpace
