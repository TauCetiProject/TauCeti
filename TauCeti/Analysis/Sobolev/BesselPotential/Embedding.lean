/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# The Sobolev embeddings `H^k(ℝⁿ) ⊆ C₀(ℝⁿ)` for `k > n / 2` and `H^s(ℝⁿ) ⊆ C^k(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space of dimension `n`. A function in the
`L²` Sobolev space of order `s > n / 2` on `E` agrees almost everywhere with a continuous function
vanishing at infinity. For the weak-derivative space `W^{k,2}(ℝⁿ)` with `2k > n` this
representative depends linearly and boundedly on the function, so that

`sup_x |u(x)| ≤ C ‖u‖_{W^{k,2}}`.

## The Fourier argument

For a tempered distribution `u` in the Bessel-potential space `H^s`, `2s > n`, Mathlib's
`TemperedDistribution.MemSobolev.fourier_memL1` shows that its Fourier transform is an `L¹`
function `v`: Cauchy–Schwarz pairs `(1 + |ξ|²)^{s/2} 𝓕u ∈ L²` with `(1 + |ξ|²)^{-s/2} ∈ L²`. Fourier
inversion on `𝓢'` gives `u = 𝓕⁻ v`, and for `v ∈ L¹` the distribution `𝓕⁻ v` is the function
`x ↦ ∫ e^{2πi⟪ξ, x⟫} v(ξ) dξ` (`MeasureTheory.Lp.fourierInv_toTemperedDistribution_apply`). This
function is continuous by dominated convergence and vanishes at infinity by the Riemann–Lebesgue
lemma, and it represents `u` almost everywhere because both have the same pairings with Schwartz
functions (`MeasureTheory.Lp.ae_eq_of_toTemperedDistribution_apply_eq`).

If moreover `2s > n + 2k`, Cauchy–Schwarz pairs `(1 + |ξ|²)^{s/2} 𝓕u ∈ L²` with
`(1 + |ξ|²)^{-(s-k)/2} ∈ L²`, so `|ξ|^j v ∈ L¹` for every `j ≤ k`. Differentiation under the
integral sign (`Real.contDiff_fourier`) then makes `𝓕⁻ v` a `C^k` function, giving the embedding
`H^s(ℝⁿ) ⊆ C^k(ℝⁿ)` for `s > n / 2 + k`.

On the whole space the weak-derivative space `W^{k,2}` is the Bessel-potential space `H^{k,2}`
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), so every `u ∈ W^{k,2}(ℝⁿ)` has a
representative in `C₀(ℝⁿ)`. Two continuous functions that agree almost everywhere are equal, so
the representative is unique and depends linearly on `u`. Its graph is closed, since convergence
in `W^{k,2}` gives almost-everywhere convergence along a subsequence and convergence in `C₀` is
uniform, so the closed graph theorem makes the map `u ↦ u` bounded from `W^{k,2}(ℝⁿ)` to `C₀(ℝⁿ)`.

The statements are for Lebesgue measure `volume`, the measure of Mathlib's Bessel-potential
spaces.

## Main declarations

* `TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`: an `L²` function in
  `H^s`, `2s > n`, agrees almost everywhere with a continuous function vanishing at infinity.
* `TemperedDistribution.tendsto_cocompact_of_mem_realSobolevFunctions`: a continuous real
  function in `H^s`, `2s > n`, tends to zero at infinity.
* `TemperedDistribution.MemSobolev.exists_contDiff_ae_eq`: an `L²` function in `H^s`,
  `2s > n + 2k`, agrees almost everywhere with a `C^k` function.
* `TemperedDistribution.contDiff_of_mem_realSobolevFunctions`: a continuous real function in
  `H^s`, `2s > n + 2k`, is `C^k`.
* `TauCeti.Wkp.toZeroAtInfty`: the Sobolev embedding `W^{k,2}(ℝⁿ) →L[ℝ] C₀(ℝⁿ)` for `2k > n`.
* `TauCeti.Wkp.value_ae_eq_toZeroAtInfty`, `TauCeti.Wkp.toZeroAtInfty_eq_iff`: the embedding sends
  a Sobolev function to its unique continuous representative.
* `TauCeti.Wkp.toZeroAtInfty_injective`: the continuous representative determines the Sobolev
  function.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., §9.3 (the Sobolev embeddings `H_s ⊆ C₀` for
  `s > n / 2` and `H_s ⊆ C^k` for `s > k + n / 2`, proved by showing that the Fourier transform,
  weighted by `|ξ|^j` for `j ≤ k`, is integrable).
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology TopologicalSpace
open scoped FourierTransform SchwartzMap ZeroAtInfty

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TemperedDistribution

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Sobolev embedding into `C₀`.** An `L²` function on `E` lying in the Bessel-potential space
`H^s` with `s > dim E / 2` agrees almost everywhere with a continuous function vanishing at
infinity. -/
theorem MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F))) :
    ∃ g : C₀(E, F), u =ᵐ[volume] g := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 hs
  have hint : Integrable (fun x => (v : E → F) (-x)) :=
    (L1.integrable_coeFn v).comp_neg
  -- The inverse Fourier transform of `v` is the Fourier transform of `x ↦ v (-x)`.
  have hneg : 𝓕⁻ (v : E → F) = 𝓕 (fun x => (v : E → F) (-x)) :=
    Real.fourierInv_eq_fourier_comp_neg _
  let g : C₀(E, F) :=
    { toFun := 𝓕⁻ (v : E → F)
      continuous_toFun := hneg ▸ VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar
        (by simpa only [innerₗ_apply_apply] using continuous_inner) hint
      zero_at_infty' := hneg ▸ tendsto_integral_exp_inner_smul_cocompact _ }
  -- Fourier inversion on `𝓢'` identifies `u` with `𝓕⁻ v`.
  refine ⟨g, ?_⟩
  rw [ZeroAtInftyContinuousMap.coe_mk]
  exact Lp.ae_eq_fourierInv_of_fourier_eq hv

/-- **Continuous Sobolev functions vanish at infinity.** A continuous real function in `H^s`,
`s > dim E / 2`, tends to zero at infinity: it agrees almost everywhere, hence everywhere, with
the continuous representative given by `MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`. -/
theorem tendsto_cocompact_of_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) (hcont : Continuous f) :
    Tendsto f (cocompact E) (𝓝 0) := by
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨g, hg⟩ := hS.exists_zeroAtInftyContinuousMap_ae_eq hs
  have hae : (fun x ↦ (f x : ℂ)) =ᵐ[volume] g := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu, hg] with x h₁ h₂ h₃
    rw [← h₃, h₁, h₂, Complex.ofRealCLM_apply]
  have hc : Continuous fun x ↦ (f x : ℂ) := Complex.continuous_ofReal.comp hcont
  have heq := (hc.ae_eq_iff_eq volume g.continuous).1 hae
  have hg0 : Tendsto (fun x ↦ (f x : ℂ)) (cocompact E) (𝓝 0) := heq ▸ g.zero_at_infty'
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp hg0

/-- **Sobolev embedding into `C^k`.** An `L²` function on `E` lying in the Bessel-potential space
`H^s` with `s > dim E / 2 + k` agrees almost everywhere with a `C^k` function. -/
theorem MemSobolev.exists_contDiff_ae_eq {s : ℝ} {k : ℕ} (hs : finrank ℝ E + 2 * k < 2 * s)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) :
    ∃ g : E → ℂ, ContDiff ℝ k g ∧ u =ᵐ[volume] g := by
  obtain ⟨v, hv, hL2⟩ := hu.fourier_memL1_and_memLp (by linarith [k.cast_nonneg (α := ℝ)])
  -- The weight `(1 + ‖ξ‖ ^ 2) ^ (-(s - k) / 2)` is square integrable since `2 (s - k) > dim E`.
  have hw : MemLp (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (-(s - k) / 2) : ℝ) : ℂ)) 2 := by
    refine MemLp.ofReal (K := ℂ) (f := fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-(s - k) / 2))
      ((memLp_two_iff_integrable_sq (Measurable.aestronglyMeasurable (by fun_prop))).2 ?_)
    refine (integrable_rpow_neg_one_add_norm_sq (r := 2 * (s - k)) (by linarith)).congr
      (Eventually.of_forall fun ξ ↦ ?_)
    dsimp only
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    push_cast
    ring
  have hprod := hw.integrable_mul hL2
  -- Cauchy–Schwarz: `‖ξ‖ ^ n |v ξ| ≤ (1 + ‖ξ‖ ^ 2) ^ (-(s - k) / 2) (1 + ‖ξ‖ ^ 2) ^ (s / 2) |v ξ|`.
  have hmom (n : ℕ) (hn : n ≤ k) : Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖(v : E → ℂ) ξ‖) := by
    refine hprod.norm.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul
      (L1.integrable_coeFn v).1.norm) (Eventually.of_forall fun ξ ↦ ?_)
    have h1 : 1 ≤ √(1 + ‖ξ‖ ^ 2) := Real.one_le_sqrt.2 (by nlinarith [norm_nonneg ξ])
    have hξ : ‖ξ‖ ≤ √(1 + ‖ξ‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
    have hpow : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖ ^ 2) ^ (-(s - k) / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
      rw [← Real.rpow_add (by positivity), show -(s - k) / 2 + s / 2 = 1 / 2 * (k : ℝ) by ring,
        Real.rpow_mul (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
      exact (pow_le_pow_left₀ (norm_nonneg ξ) hξ n).trans (pow_le_pow_right₀ h1 hn)
    simp only [Pi.mul_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ (-(s - k) / 2)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2)), ← mul_assoc]
    gcongr
  refine ⟨𝓕⁻ (v : E → ℂ), ?_, Lp.ae_eq_fourierInv_of_fourier_eq hv⟩
  rw [Real.fourierInv_eq_fourier_comp_neg]
  refine Real.contDiff_fourier (N := k) fun n hn ↦ ?_
  simpa only [norm_neg] using (hmom n (by exact_mod_cast hn)).comp_neg

/-- **Continuous Sobolev functions are `C^k`.** A continuous real function in `H^s`,
`s > dim E / 2 + k`, is of class `C^k`: it agrees almost everywhere, hence everywhere, with the
`C^k` representative given by `MemSobolev.exists_contDiff_ae_eq`. -/
theorem contDiff_of_mem_realSobolevFunctions {s : ℝ} {k : ℕ} (hs : finrank ℝ E + 2 * k < 2 * s)
    {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) (hcont : Continuous f) :
    ContDiff ℝ k f := by
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨g, hg, hug⟩ := hS.exists_contDiff_ae_eq hs
  have hae : (fun x ↦ (f x : ℂ)) =ᵐ[volume] g := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu, hug] with x h₁ h₂ h₃
    rw [← h₃, h₁, h₂, Complex.ofRealCLM_apply]
  have heq := ((Complex.continuous_ofReal.comp hcont).ae_eq_iff_eq volume hg.continuous).1 hae
  have hf : f = fun x ↦ (g x).re := funext fun x ↦ by simp [← congrFun heq x]
  exact hf ▸ Complex.reCLM.contDiff.comp hg

end TemperedDistribution

namespace TauCeti

/-- For `s > 1`, the order `s` is above half the real dimension of the plane, so `H^s(ℂ)` embeds
into the continuous functions vanishing at infinity and is an algebra. -/
theorem finrank_real_complex_lt_two_mul {s : ℝ} (hs : 1 < s) : (finrank ℝ ℂ : ℝ) < 2 * s := by
  rw [Complex.finrank_real_complex]
  push_cast
  linarith

namespace Wkp

variable {k : ℕ}

/-- If `2k > dim E`, every function in the weak-derivative Sobolev space `W^{k,2}` on the whole
space agrees almost everywhere with a continuous function vanishing at infinity. The bundled form
is `TauCeti.Wkp.toZeroAtInfty`. -/
private theorem exists_zeroAtInftyContinuousMap_ae_eq (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) ⊤ 2 k) : ∃ g : C₀(E, ℝ), value k u =ᵐ[volume] g := by
  have hvolume : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume := by simp
  set w : Lp ℝ 2 (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume (value k u)
  have hw : ∀ x, w x = value k u x := coeFn_castLpₗᵢ hvolume _
  have hS := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k w).mpr
    ⟨u, .of_forall fun x => (hw x).symm⟩
  obtain ⟨g, hg⟩ := hS.exists_zeroAtInftyContinuousMap_ae_eq (by exact_mod_cast hk)
  -- The complex representative is real almost everywhere, so its real part represents `u`.
  refine ⟨⟨⟨fun x => (g x).re, Complex.continuous_re.comp g.continuous⟩, by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp g.zero_at_infty'⟩, ?_⟩
  filter_upwards [hg, Complex.ofRealCLM.coeFn_compLp w] with x hgx hx
  rw [← hw]
  simp [← hgx, hx]

/-- Two continuous representatives of the same Sobolev function coincide. -/
private theorem eq_of_value_ae_eq {u : Wkp (volume : Measure E) ⊤ 2 k} {g g' : C₀(E, ℝ)}
    (hg : value k u =ᵐ[volume] g) (hg' : value k u =ᵐ[volume] g') : g = g' :=
  ZeroAtInftyContinuousMap.ext <| congrFun <|
    (Continuous.ae_eq_iff_eq (volume : Measure E) g.continuous g'.continuous).mp
      (hg.symm.trans hg')

/-- The continuous representative of a Sobolev function, as a linear map. -/
private def toZeroAtInftyₗ (hk : finrank ℝ E < 2 * k) :
    Wkp (volume : Measure E) ⊤ 2 k →ₗ[ℝ] C₀(E, ℝ) where
  toFun u := (exists_zeroAtInftyContinuousMap_ae_eq hk u).choose
  map_add' u v := by
    refine eq_of_value_ae_eq (u := u + v)
      (exists_zeroAtInftyContinuousMap_ae_eq hk (u + v)).choose_spec ?_
    have hadd : ⇑(value k u + value k v) =ᵐ[volume] ⇑(value k u) + ⇑(value k v) := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_add (value k u) (value k v)
    filter_upwards [(exists_zeroAtInftyContinuousMap_ae_eq hk u).choose_spec,
      (exists_zeroAtInftyContinuousMap_ae_eq hk v).choose_spec, hadd] with x hu hv hadd
    rw [value_add, hadd, Pi.add_apply, hu, hv, _root_.add_apply]
  map_smul' c u := by
    refine eq_of_value_ae_eq (u := c • u)
      (exists_zeroAtInftyContinuousMap_ae_eq hk (c • u)).choose_spec ?_
    have hsmul : ⇑(c • value k u) =ᵐ[volume] c • ⇑(value k u) := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_smul c (value k u)
    filter_upwards [(exists_zeroAtInftyContinuousMap_ae_eq hk u).choose_spec, hsmul]
      with x hu hsmul
    rw [value_smul, hsmul, Pi.smul_apply, hu, RingHom.id_apply,
      _root_.smul_apply]

private theorem value_ae_eq_toZeroAtInftyₗ (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) ⊤ 2 k) : value k u =ᵐ[volume] toZeroAtInftyₗ hk u :=
  (exists_zeroAtInftyContinuousMap_ae_eq hk u).choose_spec

/-- The graph of the continuous representative is sequentially closed: along a sequence
converging in `W^{k,2}`, the values converge almost everywhere along a subsequence, while the
representatives converge uniformly. -/
private theorem toZeroAtInftyₗ_closedGraph (hk : finrank ℝ E < 2 * k)
    (u : ℕ → Wkp (volume : Measure E) ⊤ 2 k) (w : Wkp (volume : Measure E) ⊤ 2 k)
    (g : C₀(E, ℝ))
    (hu : Tendsto u atTop (𝓝 w)) (hg : Tendsto (toZeroAtInftyₗ hk ∘ u) atTop (𝓝 g)) :
    g = toZeroAtInftyₗ hk w := by
  refine eq_of_value_ae_eq (u := w) ?_ (value_ae_eq_toZeroAtInftyₗ hk w)
  have hval : Tendsto (fun n => value k (u n)) atTop (𝓝 (value k w)) := by
    simpa only [Function.comp_def, valueL_apply] using ((valueL k).continuous.tendsto w).comp hu
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      value k (u (ns i)) x = toZeroAtInftyₗ hk (u (ns i)) x :=
    ae_all_iff.mpr fun i => value_ae_eq_toZeroAtInftyₗ hk (u (ns i))
  replace hns : ∀ᵐ x ∂(volume : Measure E),
      Tendsto (fun i => value k (u (ns i)) x) atTop (𝓝 (value k w x)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hns
  filter_upwards [hns, hrep] with x hx hxrep
  -- Convergence in `C₀` is uniform, so it implies convergence at `x`.
  have heval : Tendsto (fun i => toZeroAtInftyₗ hk (u (ns i)) x) atTop (𝓝 (g x)) :=
    (((continuous_apply x).comp (BoundedContinuousFunction.continuous_coe.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous)).tendsto g).comp
        (hg.comp hmono.tendsto_atTop)
  exact tendsto_nhds_unique (hx.congr hxrep) heval

/-- **The Sobolev embedding `W^{k,2}(ℝⁿ) →L[ℝ] C₀(ℝⁿ)`** for `2k > dim E`: the bounded linear map
sending a function in the whole-space weak-derivative Sobolev space `W^{k,2}` to its unique
representative that is continuous and vanishes at infinity. Its boundedness is the estimate
`sup_x |u(x)| ≤ C ‖u‖_{W^{k,2}}`. -/
def toZeroAtInfty (hk : finrank ℝ E < 2 * k) : Wkp (volume : Measure E) ⊤ 2 k →L[ℝ] C₀(E, ℝ) :=
  .ofSeqClosedGraph (g := toZeroAtInftyₗ hk) (toZeroAtInftyₗ_closedGraph hk)

/-- The Sobolev embedding sends a Sobolev function to a representative of its value. -/
theorem value_ae_eq_toZeroAtInfty (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) ⊤ 2 k) :
    value k u =ᵐ[volume] toZeroAtInfty hk u :=
  value_ae_eq_toZeroAtInftyₗ hk u

/-- The Sobolev embedding of `u` is the only function in `C₀` representing the value of `u`. -/
theorem toZeroAtInfty_eq_iff (hk : finrank ℝ E < 2 * k) (u : Wkp (volume : Measure E) ⊤ 2 k)
    (g : C₀(E, ℝ)) :
    toZeroAtInfty hk u = g ↔ value k u =ᵐ[volume] g :=
  ⟨fun h => h ▸ value_ae_eq_toZeroAtInfty hk u,
    fun h => eq_of_value_ae_eq (value_ae_eq_toZeroAtInfty hk u) h⟩

/-- The Sobolev embedding is injective: the continuous representative determines the Sobolev
function. -/
theorem toZeroAtInfty_injective (hk : finrank ℝ E < 2 * k) :
    Function.Injective (toZeroAtInfty (E := E) hk) := by
  intro u v huv
  apply ext k
  apply Lp.ext
  have hae : value k u =ᵐ[volume] value k v := by
    filter_upwards [value_ae_eq_toZeroAtInfty hk u, value_ae_eq_toZeroAtInfty hk v]
      with x hu hv
    rw [hu, hv, huv]
  simpa only [Opens.coe_top, Measure.restrict_univ] using hae

end Wkp

end TauCeti
