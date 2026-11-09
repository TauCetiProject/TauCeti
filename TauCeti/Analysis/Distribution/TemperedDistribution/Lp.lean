/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Fourier.Continuous

/-!
# `Lᵖ` functions as tempered distributions

An `Lᵖ` function `u` defines the tempered distribution `φ ↦ ∫ φ • u`
(`MeasureTheory.Lp.toTemperedDistribution`). This file records facts about that embedding which
are needed to read off a pointwise representative from an identity of tempered distributions,
and a criterion for an operator into tempered distributions to take values in `Lᵖ`.

* An `Lᵖ` function is determined almost everywhere by its pairings with Schwartz functions,
  even when it is compared with a locally integrable function that need not lie in the same
  `Lᵖ` space. Mathlib's `MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot` is the case of
  two functions in one `Lᵖ` space.
* The distributional Fourier transform and inverse Fourier transform of an integrable function
  `v` are the bounded continuous functions `𝓕 v` and `𝓕⁻ v`, given by the absolutely convergent
  Fourier integrals. This is the multiplication formula `∫ (𝓕⁻ φ) • v = ∫ φ • 𝓕⁻ v`, and its
  analogue for `𝓕`, of `VectorFourier.integral_bilin_fourierIntegral_eq_flip`, read through the
  definition `𝓕⁻ T (φ) = T (𝓕⁻ φ)` of the inverse Fourier transform on `𝓢'`.

Together they turn the statement "the Fourier transform of `u ∈ Lᵖ` is an `L¹` function `v`" into
the continuous representative `𝓕⁻ v` of `u` (`MeasureTheory.Lp.ae_eq_fourierInv_of_fourier_eq`);
this is how the Sobolev embedding `H^s(ℝⁿ) ⊆ C₀(ℝⁿ)`, `s > n / 2`, is derived from
`TemperedDistribution.MemSobolev.fourier_memL1`. Multiplying the tempered distribution of an `Lᵖ`
function by a function of temperate growth multiplies the function pointwise
(`MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_apply`).

* A continuous linear map `T : Lᵖ → 𝓢'`, `p < ∞`, that is given on Schwartz functions by an
  operator bounded in the `Lᵖ` norm takes values in `Lᵖ`, with the same bound. Schwartz functions
  are dense in `Lᵖ`, so the bounded operator extends, and the extension agrees with `T` because
  `𝓢'` is Hausdorff. This is how `Lᵖ` bounds for Fourier multipliers and multiplication operators,
  proved on Schwartz functions, pass to all of `Lᵖ` or of a Sobolev space.
* The extended `Lᵖ` norm `TemperedDistribution.lpENorm p u` of a tempered distribution is `‖g‖_p`
  when `u` is the distribution of `g ∈ Lᵖ`, which is unique by the first point, and `∞`
  otherwise. It measures distributions not known in advance to be `Lᵖ` functions, such as the
  Littlewood–Paley blocks in a Besov norm.

## Main declarations

* `MeasureTheory.Lp.ae_eq_of_toTemperedDistribution_apply_eq`: an `Lᵖ` function whose pairings
  with Schwartz functions agree with those of a locally integrable `g` is almost everywhere
  equal to `g`.
* `MeasureTheory.Lp.toTemperedDistribution_compLp_apply`: applying a continuous linear map to the
  values of an `Lᵖ` function applies it to its tempered distribution.
* `SchwartzMap.toTemperedDistributionCLM_postcompCLM_apply`: the same for the values of a
  Schwartz function.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_apply`: the Fourier transform of the tempered
  distribution of an `Lᵖ` function `v` with an integrable representative `f` pairs with `φ` as
  `∫ φ • 𝓕 f`.
* `MeasureTheory.Lp.fourierInv_toTemperedDistribution_apply`: the inverse Fourier transform of
  the tempered distribution of an `L¹` function `v` pairs with `φ` as `∫ φ • 𝓕⁻ v`.
* `MeasureTheory.Lp.ae_eq_fourierInv_of_fourier_eq`: an `Lᵖ` function whose Fourier transform is
  an `L¹` function `v` agrees almost everywhere with `𝓕⁻ v`.
* `MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_apply`: the product of the tempered
  distribution of an `Lᵖ` function `u` with a function `g` of temperate growth pairs with `φ` as
  `∫ φ • (g • u)`.
* `ContinuousLinearMap.exists_apply_eq_toTemperedDistribution_and_norm_le`: an operator
  `Lᵖ → 𝓢'` bounded on Schwartz functions takes values in `Lᵖ`.
* `MeasureTheory.Lp.toTemperedDistribution_injective`: an `Lᵖ` function is determined by its
  tempered distribution.
* `MeasureTheory.Lp.toTemperedDistribution_add`, `MeasureTheory.Lp.toTemperedDistribution_smul`,
  `MeasureTheory.Lp.toTemperedDistribution_sum`: the coercion `Lᵖ → 𝓢'` is linear.
* `TemperedDistribution.lpENorm`: the extended `Lᵖ` norm of a tempered distribution, `‖g‖_p` on
  the distribution of `g ∈ Lᵖ` and `∞` off `Lᵖ`; it is subadditive and absolutely homogeneous.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., §2.3 (functions as tempered distributions
  and the Fourier transform on `𝓢'`).
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open SchwartzMap
open scoped ContDiff FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section NormedSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An `Lᵖ` function is almost everywhere equal to any locally integrable function with the same
pairings against Schwartz functions. The two functions need not lie in the same `Lᵖ` space. -/
theorem ae_eq_of_toTemperedDistribution_apply_eq {μ : Measure E} [μ.HasTemperateGrowth]
    [IsLocallyFiniteMeasure μ] {p : ENNReal} [hp : Fact (1 ≤ p)] (u : Lp F p μ) {g : E → F}
    (hg : LocallyIntegrable g μ)
    (h : ∀ φ : 𝓢(E, ℂ), (u : 𝓢'(E, F)) φ = ∫ x, φ x • g x ∂μ) :
    u =ᵐ[μ] g := by
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp u).locallyIntegrable hp.out) hg
    fun ψ hψ hψc => ?_
  -- A smooth compactly supported real function is a complex Schwartz function.
  have hψ₁ : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hψc.comp_left rfl
  have hψ₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have := h (hψ₁.toSchwartzMap hψ₂)
  simpa [Lp.toTemperedDistribution_apply] using this

/-- An `Lᵖ` function is determined by its tempered distribution. -/
theorem toTemperedDistribution_injective {μ : Measure E} [μ.HasTemperateGrowth]
    [IsLocallyFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)] :
    Function.Injective (toTemperedDistribution : Lp F p μ → 𝓢'(E, F)) :=
  LinearMap.ker_eq_bot.mp ker_toTemperedDistributionCLM_eq_bot

section Linear

variable {μ : Measure E} [μ.HasTemperateGrowth] {p : ENNReal} [Fact (1 ≤ p)]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toTemperedDistribution_zero : ((0 : Lp F p μ) : 𝓢'(E, F)) = 0 :=
  map_zero (toTemperedDistributionCLM F μ p)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toTemperedDistribution_add (f g : Lp F p μ) :
    ((f + g : Lp F p μ) : 𝓢'(E, F)) = (f : 𝓢'(E, F)) + g :=
  map_add (toTemperedDistributionCLM F μ p) f g

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toTemperedDistribution_smul (c : ℂ) (f : Lp F p μ) :
    ((c • f : Lp F p μ) : 𝓢'(E, F)) = c • (f : 𝓢'(E, F)) :=
  map_smul (toTemperedDistributionCLM F μ p) c f

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toTemperedDistribution_neg (f : Lp F p μ) :
    ((-f : Lp F p μ) : 𝓢'(E, F)) = -(f : 𝓢'(E, F)) :=
  map_neg (toTemperedDistributionCLM F μ p) f

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toTemperedDistribution_sub (f g : Lp F p μ) :
    ((f - g : Lp F p μ) : 𝓢'(E, F)) = (f : 𝓢'(E, F)) - g :=
  map_sub (toTemperedDistributionCLM F μ p) f g

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toTemperedDistribution_sum {ι : Type*} (s : Finset ι) (f : ι → Lp F p μ) :
    ((∑ i ∈ s, f i : Lp F p μ) : 𝓢'(E, F)) = ∑ i ∈ s, (f i : 𝓢'(E, F)) :=
  map_sum (toTemperedDistributionCLM F μ p) f s

end Linear

omit [FiniteDimensional ℝ E] in
/-- Multiplying the tempered distribution of an `Lᵖ` function `u` by a function `g` of temperate
growth gives the distribution `φ ↦ ∫ φ • (g • u)`. -/
theorem smulLeftCLM_toTemperedDistribution_apply {μ : Measure E} [μ.HasTemperateGrowth]
    {p : ENNReal} [Fact (1 ≤ p)] {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : Lp F p μ)
    (φ : 𝓢(E, ℂ)) :
    TemperedDistribution.smulLeftCLM F g (u : 𝓢'(E, F)) φ = ∫ x, φ x • g x • u x ∂μ := by
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm (g _), mul_smul]

omit [FiniteDimensional ℝ E] in
/-- Applying a continuous linear map `L` to the values of an `Lᵖ` function `u` applies `L` to the
pairings of its tempered distribution. -/
theorem toTemperedDistribution_compLp_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {μ : Measure E} [μ.HasTemperateGrowth] {p : ENNReal} [hp : Fact (1 ≤ p)]
    (L : F →L[ℂ] G) (u : Lp F p μ) (φ : 𝓢(E, ℂ)) :
    ((L.compLp u : Lp G p μ) : 𝓢'(E, G)) φ = L ((u : 𝓢'(E, F)) φ) := by
  have : (1 - p⁻¹)⁻¹.HolderConjugate p :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  have hφu : Integrable (fun x ↦ φ x • u x) μ :=
    memLp_one_iff_integrable.1 ((φ.memLp (1 - p⁻¹)⁻¹ (μ := μ)).smul (Lp.memLp u))
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply, ← L.integral_comp_comm hφu]
  refine integral_congr_ae ((L.coeFn_compLp u).mono fun x hx ↦ ?_)
  simp only [hx, map_smul]

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Fourier transform of an integrable function as a tempered distribution.** If the
`Lᵖ` function `v` agrees almost everywhere with an integrable function `f`, the distributional
Fourier transform of `v` is the function `𝓕 f` given by the absolutely convergent Fourier
integral: it pairs with a Schwartz function `φ` as `∫ φ • 𝓕 f`. -/
theorem fourier_toTemperedDistribution_apply {p : ENNReal} [Fact (1 ≤ p)]
    (v : Lp F p (volume : Measure E)) {f : E → F} (hf : Integrable f) (hvf : v =ᵐ[volume] f)
    (φ : 𝓢(E, ℂ)) :
    𝓕 (v : 𝓢'(E, F)) φ = ∫ x, φ x • 𝓕 f x := by
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    integral_congr_ae (hvf.mono fun x hx => by rw [hx]), SchwartzMap.fourier_coe]
  -- On functions, `𝓕` is the Fourier integral for the pairing `⟪·, ·⟫`, which is its own flip,
  -- so this is the multiplication formula for that pairing.
  have hL : Continuous fun p : E × E => (innerₗ E) p.1 p.2 := by
    simp only [innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    (φ.integrable (μ := volume)) hf
  rwa [flip_innerₗ] at h

/-- **The inverse Fourier transform of an `L¹` function as a tempered distribution.** For
`v ∈ L¹`, the distributional inverse Fourier transform of `v` is the function `𝓕⁻ v` given by the
absolutely convergent Fourier integral: it pairs with a Schwartz function `φ` as `∫ φ • 𝓕⁻ v`. -/
theorem fourierInv_toTemperedDistribution_apply (v : Lp F 1 (volume : Measure E))
    (φ : 𝓢(E, ℂ)) :
    𝓕⁻ (v : 𝓢'(E, F)) φ = ∫ x, φ x • 𝓕⁻ (v : E → F) x := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.fourierInv_coe]
  -- On functions, `𝓕⁻` is defined (`Real.instFourierTransformInv`) as the Fourier integral for
  -- the pairing `-⟪·, ·⟫`, which is its own flip, so this is the multiplication formula for that
  -- pairing.
  have hflip : (-innerₗ E).flip = -innerₗ E :=
    LinearMap.ext₂ fun x y => by simp [real_inner_comm]
  have hL : Continuous fun p : E × E => (-innerₗ E) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    (φ.integrable (μ := volume)) (L1.integrable_coeFn v)
  rw [hflip] at h
  exact h

/-- **The representative of an `Lᵖ` function with integrable Fourier transform.** If the
distributional Fourier transform of `u ∈ Lᵖ` is an `L¹` function `v`, then `u` agrees almost
everywhere with the continuous function `𝓕⁻ v`. -/
theorem ae_eq_fourierInv_of_fourier_eq {p : ENNReal} [Fact (1 ≤ p)]
    {u : Lp F p (volume : Measure E)} {v : Lp F 1 (volume : Measure E)}
    (h : 𝓕 (u : 𝓢'(E, F)) = v) :
    u =ᵐ[volume] 𝓕⁻ (v : E → F) := by
  have hcont : Continuous (𝓕⁻ (v : E → F)) := (L1.integrable_coeFn v).continuous_fourierInv
  have hu : (u : 𝓢'(E, F)) = 𝓕⁻ (v : 𝓢'(E, F)) := by
    rw [← h]
    exact (FourierTransform.fourierInv_fourier_eq _).symm
  refine ae_eq_of_toTemperedDistribution_apply_eq u hcont.locallyIntegrable fun φ => ?_
  rw [hu, fourierInv_toTemperedDistribution_apply]

end InnerProductSpace

end MeasureTheory.Lp

namespace SchwartzMap

open MeasureTheory

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Applying a continuous linear map `L` to the values of a Schwartz function `u` applies `L` to
the pairings of its tempered distribution. -/
theorem toTemperedDistributionCLM_postcompCLM_apply (L : F →L[ℂ] G) (u : 𝓢(E, F))
    (φ : 𝓢(E, ℂ)) :
    ((u.postcompCLM L : 𝓢(E, G)) : 𝓢'(E, G)) φ = L ((u : 𝓢'(E, F)) φ) := by
  have hφu : Integrable (fun x ↦ φ x • u x) := φ.integrable.smul_of_top_left u.memLp_top
  rw [SchwartzMap.coe_apply, SchwartzMap.coe_apply, ← L.integral_comp_comm hφu]
  simp only [postcompCLM_apply, map_smul]

end SchwartzMap

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-- **Extension from Schwartz functions.** Let `T` be a continuous linear map from `Lᵖ`,
`p < ∞`, to tempered distributions, which on Schwartz functions `φ` is given by an operator
`M` on Schwartz functions with `‖M φ‖_p ≤ C ‖φ‖_p`. Then `T` takes values in `Lᵖ`: every `T f`
is the tempered distribution of some `g ∈ Lᵖ` with `‖g‖_p ≤ C ‖f‖_p`.

The function `g` is the value at `f` of the bounded extension of `φ ↦ M φ` from the dense
Schwartz functions to `Lᵖ`; it agrees with `T f` because both sides are continuous in `f` with
values in the Hausdorff space of tempered distributions. -/
theorem exists_apply_eq_toTemperedDistribution_and_norm_le {μ : Measure E}
    [μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (T : Lp F p μ →L[ℂ] 𝓢'(E, F)) (M : 𝓢(E, F) →L[ℂ] 𝓢(E, F)) {C : ℝ}
    (hT : ∀ φ : 𝓢(E, F), T (φ.toLp p μ) = ((M φ).toLp p μ : 𝓢'(E, F)))
    (hM : ∀ φ : 𝓢(E, F), ‖(M φ).toLp p μ‖ ≤ C * ‖φ.toLp p μ‖) (f : Lp F p μ) :
    ∃ g : Lp F p μ, T f = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  set e : 𝓢(E, F) →ₗ[ℂ] Lp F p μ := (SchwartzMap.toLpCLM ℂ F p μ).toLinearMap
  have he : DenseRange e := SchwartzMap.denseRange_toLpCLM (F := F) (μ := μ) hp
  set S : 𝓢(E, F) →ₗ[ℂ] Lp F p μ := e ∘ₗ M.toLinearMap
  have hSe : ∀ φ, ‖S φ‖ ≤ C * ‖e φ‖ := fun φ ↦ by
    simpa only [S, e, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      SchwartzMap.toLpCLM_apply] using hM φ
  refine ⟨S.extendOfNorm e f, ?_, LinearMap.norm_extendOfNorm_apply_le he _ hSe f⟩
  refine congrFun (he.equalizer (g := T) (h := fun f ↦ (S.extendOfNorm e f : 𝓢'(E, F)))
    T.continuous ((Lp.toTemperedDistributionCLM F μ p).continuous.comp
      (S.extendOfNorm e).continuous) (funext fun φ ↦ ?_)) f
  simp only [Function.comp_apply, LinearMap.extendOfNorm_eq he ⟨_, hSe⟩]
  simpa only [S, e, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    SchwartzMap.toLpCLM_apply] using hT φ

end ContinuousLinearMap

namespace TemperedDistribution

open MeasureTheory
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-! ### The extended `Lᵖ` norm of a tempered distribution -/

section LpENorm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The **extended `Lᵖ` norm** of a tempered distribution: `‖g‖_p` if `u` is the tempered
distribution of `g ∈ Lᵖ(E, F)`, and `∞` if `u` is not given by an `Lᵖ` function. -/
noncomputable def lpENorm (u : 𝓢'(E, F)) : ℝ≥0∞ :=
  ⨅ (g : Lp F p (volume : Measure E)) (_ : u = g), ‖g‖ₑ

/-- On the tempered distribution of an `Lᵖ` function, the extended `Lᵖ` norm is its norm. -/
@[simp]
theorem lpENorm_toTemperedDistribution (g : Lp F p (volume : Measure E)) :
    lpENorm p (g : 𝓢'(E, F)) = ‖g‖ₑ := by
  refine le_antisymm ?_ (le_iInf₂ fun _ h ↦ (Lp.toTemperedDistribution_injective h ▸ le_rfl))
  exact iInf₂_le (f := fun (g' : Lp F p (volume : Measure E)) (_ : (g : 𝓢'(E, F)) = g') ↦ ‖g'‖ₑ)
    g rfl

/-- A tempered distribution that is not given by an `Lᵖ` function has infinite extended `Lᵖ`
norm. -/
theorem lpENorm_eq_top {u : 𝓢'(E, F)} (hu : ∀ g : Lp F p (volume : Measure E), u ≠ g) :
    lpENorm p u = ∞ := by
  simp [lpENorm, hu]

/-- The extended `Lᵖ` norm of a tempered distribution is finite exactly when the distribution is
given by an `Lᵖ` function. -/
theorem lpENorm_lt_top_iff {u : 𝓢'(E, F)} :
    lpENorm p u < ∞ ↔ ∃ g : Lp F p (volume : Measure E), u = g := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ hg ▸ (lpENorm_toTemperedDistribution g).symm ▸ enorm_lt_top⟩
  by_contra! hu
  exact h.ne (lpENorm_eq_top hu)

@[simp]
theorem lpENorm_zero : lpENorm p (0 : 𝓢'(E, F)) = 0 := by
  rw [← Lp.toTemperedDistribution_zero (F := F) (μ := volume) (p := p),
    lpENorm_toTemperedDistribution, enorm_zero]

theorem lpENorm_add_le (u v : 𝓢'(E, F)) : lpENorm p (u + v) ≤ lpENorm p u + lpENorm p v := by
  rcases eq_top_or_lt_top (lpENorm p u) with hu | hu
  · simp [hu]
  rcases eq_top_or_lt_top (lpENorm p v) with hv | hv
  · simp [hv]
  obtain ⟨g, rfl⟩ := lpENorm_lt_top_iff.1 hu
  obtain ⟨h, rfl⟩ := lpENorm_lt_top_iff.1 hv
  simp only [← Lp.toTemperedDistribution_add, lpENorm_toTemperedDistribution]
  exact enorm_add_le g h

/-- The extended `Lᵖ` norm is absolutely homogeneous. -/
theorem lpENorm_smul (c : ℂ) (u : 𝓢'(E, F)) : lpENorm p (c • u) = ‖c‖ₑ * lpENorm p u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_top_or_lt_top (lpENorm p u) with hu | hu
  · -- If `c • u` were an `Lᵖ` function, so would be `u = c⁻¹ • (c • u)`.
    rw [hu, ENNReal.mul_top (enorm_ne_zero.2 hc)]
    by_contra! h
    obtain ⟨g, hg⟩ := lpENorm_lt_top_iff.1 (lt_top_iff_ne_top.2 h)
    refine (lt_top_iff_ne_top.1 (lpENorm_lt_top_iff.2 ⟨c⁻¹ • g, ?_⟩)) hu
    rw [Lp.toTemperedDistribution_smul, ← hg, inv_smul_smul₀ hc]
  · obtain ⟨g, rfl⟩ := lpENorm_lt_top_iff.1 hu
    rw [← Lp.toTemperedDistribution_smul, lpENorm_toTemperedDistribution, enorm_smul,
      lpENorm_toTemperedDistribution]

@[simp]
theorem lpENorm_neg (u : 𝓢'(E, F)) : lpENorm p (-u) = lpENorm p u := by
  simpa using lpENorm_smul (-1) u

end LpENorm

end TemperedDistribution
