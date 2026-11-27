/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Eigenfunction
public import TauCeti.Dynamics.Ergodic.Action.WeakMixing.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Correlation
import TauCeti.Analysis.SpecificLimits.Cesaro.Integral
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weak mixing in `L²` and eigenfunctions

Let `ℝ` act jointly measurably on `X`, preserving a finite measure `μ`, and let `U_t` be the
Koopman group on complex `L²(μ)`, `U_t f = f ∘ (t +ᵥ ·)` (`TauCeti.koopmanGroup`).

The action is weakly mixing exactly when, for all `f g ∈ L²(μ)`, the centered correlations
`⟪g, U_t f⟫ - (∫ f) conj (∫ g)` tend to `0` in Cesàro mean in absolute value:
`T⁻¹ ∫₀ᵀ |⟪g, U_t f⟫ - (∫ f) conj (∫ g)| dt → 0`
(`MeasureTheory.Measure.isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup`). For
indicator functions `f = 1_A`, `g = 1_B` the centered correlation is
`μ((t +ᵥ ·)⁻¹' A ∩ B) - μ(A) μ(B)`, which gives one direction. For the other, the set of pairs
`(f, g)` with vanishing Cesàro mean is closed under addition in each variable, since the centered
correlation is additive in each, and closed, since it is Lipschitz in each variable uniformly in
`t`; simple functions are dense in `L²(μ)`.

As a consequence, a measurable eigenfunction of a weakly mixing action is almost everywhere
constant (`MeasureTheory.Measure.IsWeaklyMixing.exists_ae_eq_const_of_eigenfunction`): the action
is ergodic, so for frequency `0` the eigenfunction is almost invariant, hence constant; for a
frequency `a ≠ 0` it is in `L²(μ)`, has integral `0` because `∫ f = exp(2πiat) ∫ f`, and its
centered correlation `⟪f, U_t f⟫ = exp(2πiat) ‖f‖²` has constant absolute value `‖f‖²`, which
must therefore vanish. This is the easy half of the eigenfunction criterion for weak mixing.

Conversely, for a probability measure, if every measurable eigenfunction is almost everywhere
constant then the action is weakly mixing
(`MeasureTheory.Measure.isWeaklyMixing_of_forall_eigenfunction`), so weak mixing is equivalent to
the triviality of eigenfunctions (`MeasureTheory.Measure.isWeaklyMixing_iff_forall_eigenfunction`).
Every Koopman eigenvector is then a multiple of `1`, so the centered parts `f - (∫ f) 1` and
`g - (∫ g) 1` are orthogonal to every eigenspace of the Koopman group, and their correlation is
the centered correlation of `f` and `g`. Its Cesàro averages vanish by the spectral theory of
unitary groups: Bochner's theorem, Wiener's lemma and the atomic-mass identity, then
polarization (`IsUnitary.tendsto_average_norm_inner_sub_of_forall_mem_eigenspace` in the namespace
`TauCeti.Semigroups.StronglyContinuousGroup`).

## Main results

* `MeasureTheory.Measure.IsWeaklyMixing.tendsto_average_norm_inner_koopmanGroup`: the `L²` form
  of weak mixing;
* `MeasureTheory.Measure.isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup`: weak mixing
  is equivalent to its `L²` form;
* `MeasureTheory.Measure.IsWeaklyMixing.exists_ae_eq_const_of_eigenfunction`: every measurable
  eigenfunction of a weakly mixing action is almost everywhere constant;
* `MeasureTheory.Measure.isWeaklyMixing_iff_forall_eigenfunction`: the eigenfunction criterion,
  for a probability measure.

## References

* M. Hochman, *Notes on ergodic theory*, 2012, Section 6.1 (for actions of `ℤ`).
-/

public section

noncomputable section

open Filter MeasureTheory Set TauCeti TauCeti.Semigroups
open scoped Topology ENNReal ComplexConjugate InnerProductSpace

namespace MeasureTheory.Measure

/-! ### Centered correlations of a unitary group -/

section Correlation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : StronglyContinuousGroup H) (e : H)

/-- The centered correlation `⟪g, U_t f⟫ - ⟪e, f⟫ ⟪g, e⟫` of a group `U` relative to a vector
`e`. For the Koopman group and `e = 1`, it is `⟪g, U_t f⟫ - (∫ f) conj (∫ g)`. -/
private def corr (f g : H) (t : ℝ) : ℂ :=
  ⟪g, U t f⟫_ℂ - ⟪e, f⟫_ℂ * ⟪g, e⟫_ℂ

private theorem corr_apply (f g : H) (t : ℝ) :
    corr U e f g t = ⟪g, U t f⟫_ℂ - ⟪e, f⟫_ℂ * ⟪g, e⟫_ℂ :=
  rfl

private theorem continuous_corr (f g : H) : Continuous (corr U e f g) :=
  (continuous_const.inner (U.continuous_orbit f)).sub continuous_const

private theorem corr_add_left (f₁ f₂ g : H) (t : ℝ) :
    corr U e (f₁ + f₂) g t = corr U e f₁ g t + corr U e f₂ g t := by
  simp only [corr, map_add, inner_add_right]
  ring

private theorem corr_add_right (f g₁ g₂ : H) (t : ℝ) :
    corr U e f (g₁ + g₂) t = corr U e f g₁ t + corr U e f g₂ t := by
  simp only [corr, inner_add_left]
  ring

variable {U}

private theorem norm_corr_le (hU : U.IsUnitary) (f g : H) (t : ℝ) :
    ‖corr U e f g t‖ ≤ (1 + ‖e‖ ^ 2) * (‖f‖ * ‖g‖) := by
  calc ‖corr U e f g t‖ ≤ ‖⟪g, U t f⟫_ℂ‖ + ‖⟪e, f⟫_ℂ‖ * ‖⟪g, e⟫_ℂ‖ := by
        rw [corr, ← norm_mul]
        exact norm_sub_le _ _
    _ ≤ ‖g‖ * ‖U t f‖ + (‖e‖ * ‖f‖) * (‖g‖ * ‖e‖) := by
        gcongr
        · exact norm_inner_le_norm _ _
        · exact norm_inner_le_norm _ _
        · exact norm_inner_le_norm _ _
    _ = (1 + ‖e‖ ^ 2) * (‖f‖ * ‖g‖) := by
        rw [hU.norm_map]
        ring

end Correlation

/-! ### The `L²` form of weak mixing -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The constant function `1` in complex `L²(μ)`. -/
private def one : Lp ℂ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1

private theorem inner_one_left (f : Lp ℂ 2 μ) : ⟪(one : Lp ℂ 2 μ), f⟫_ℂ = ∫ x, f x ∂μ := by
  rw [one, L2.inner_indicatorConstLp_one, Measure.restrict_univ]

private theorem inner_one_right (g : Lp ℂ 2 μ) :
    ⟪g, (one : Lp ℂ 2 μ)⟫_ℂ = conj (∫ x, g x ∂μ) := by
  rw [← inner_conj_symm, inner_one_left]

private theorem coeFn_one : (one : Lp ℂ 2 μ) =ᵐ[μ] fun _ => (1 : ℂ) := by
  rw [one, indicatorConstLp_univ]
  exact Lp.coeFn_const 2 μ 1

private theorem inner_one_one [IsProbabilityMeasure μ] : ⟪(one : Lp ℂ 2 μ), one⟫_ℂ = 1 := by
  rw [inner_one_left, integral_congr_ae coeFn_one]
  simp

variable [AddAction ℝ X] [MeasurableVAdd₂ ℝ X] [VAddInvariantMeasure ℝ X μ]

private theorem corr_koopmanGroup (f g : Lp ℂ 2 μ) (t : ℝ) :
    corr (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one f g t =
      ⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ -
        (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ) := by
  unfold corr
  rw [inner_one_left, inner_one_right]
  -- `corr` reaches `Lp ℂ 2 μ` through its `InnerProductSpace ℂ` structure, so the inner product
  -- is `InnerProductSpace.toInner` of `L2.innerProductSpace` and the real scalars of the group
  -- come from `InnerProductSpace.toNormedSpace`; the right side uses the `L2` inner product and
  -- `Lp.instNormedSpace` directly. These agree definitionally but not reducibly.
  rfl

private theorem koopmanGroup_one (t : ℝ) :
    koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t one = one := by
  rw [one, koopmanGroup_indicatorConstLp μ ℂ 2]
  simp only [preimage_univ]

/-- The centered correlation of two indicator functions. -/
private theorem corr_indicatorConstLp {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (c d : ℂ) (t : ℝ) :
    corr (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one
        (indicatorConstLp 2 hA (measure_ne_top μ A) c)
        (indicatorConstLp 2 hB (measure_ne_top μ B) d) t =
      (conj d * c) * ((μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B : ℝ) : ℂ) := by
  rw [corr_koopmanGroup, koopmanGroup_indicatorConstLp μ ℂ 2, ← inner_one_left, ← inner_one_right,
    one, L2.inner_indicatorConstLp_indicatorConstLp, L2.inner_indicatorConstLp_indicatorConstLp,
    L2.inner_indicatorConstLp_indicatorConstLp, univ_inter, inter_univ, inter_comm B]
  simp only [RCLike.inner_apply, map_one, one_mul, mul_one, Complex.real_smul]
  push_cast
  ring

private theorem norm_corr_indicatorConstLp {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (c d : ℂ) (t : ℝ) :
    ‖corr (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one
        (indicatorConstLp 2 hA (measure_ne_top μ A) c)
        (indicatorConstLp 2 hB (measure_ne_top μ B) d) t‖ =
      ‖d‖ * ‖c‖ * |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B| := by
  rw [corr_indicatorConstLp, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs]

/-- **The `L²` form of weak mixing.** For a weakly mixing jointly measurable action of `ℝ`
preserving a finite measure `μ`, and all `f g` in complex `L²(μ)`, the centered correlations
`⟪g, U_t f⟫ - (∫ f) conj (∫ g)` of the Koopman group tend to `0` in Cesàro mean in absolute
value. -/
theorem IsWeaklyMixing.tendsto_average_norm_inner_koopmanGroup (h : IsWeaklyMixing μ)
    (f g : Lp ℂ 2 μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ -
          (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ)‖) atTop (𝓝 0) := by
  set U := koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top
  have hU : U.IsUnitary := koopmanGroup_isUnitary μ ℂ
  suffices hfg : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖corr U one f g t‖) atTop (𝓝 0) by
    simpa only [U, corr_koopmanGroup] using hfg
  -- Indicator functions.
  have hind : ∀ {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (c d : ℂ),
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖corr U one (indicatorConstLp 2 hA (measure_ne_top μ A) c)
          (indicatorConstLp 2 hB (measure_ne_top μ B) d) t‖) atTop (𝓝 0) := by
    intro A B hA hB c d
    simp only [U, norm_corr_indicatorConstLp, intervalIntegral.integral_const_mul]
    simpa [mul_left_comm _ (‖d‖ * ‖c‖)] using
      (isWeaklyMixing_def.1 h A B hA hB).const_mul (‖d‖ * ‖c‖)
  -- The first variable.
  have hleft : ∀ {B : Set X} (hB : MeasurableSet B) (d : ℂ) (f : Lp ℂ 2 μ),
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖corr U one f (indicatorConstLp 2 hB (measure_ne_top μ B) d) t‖) atTop (𝓝 0) := by
    intro B hB d f
    induction f using Lp.induction (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞) with
    | indicatorConst c hA _ => exact hind hA hB c d
    | add _ _ _ h₁ h₂ =>
      exact tendsto_average_norm_apply_add (continuous_corr U one · _)
        (corr_add_left U one · · _) h₁ h₂
    | isClosed =>
      exact isClosed_setOf_tendsto_average_norm (continuous_corr U one · _)
        (corr_add_left U one · · _)
        (C := (1 + ‖one‖ ^ 2) * ‖indicatorConstLp 2 hB (measure_ne_top μ B) d‖)
        fun f t => (norm_corr_le one hU f _ t).trans_eq (by ring)
  -- The second variable.
  induction g using Lp.induction (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞) with
  | indicatorConst d hB _ => exact hleft hB d f
  | add _ _ _ h₁ h₂ =>
    exact tendsto_average_norm_apply_add (continuous_corr U one f) (corr_add_right U one f) h₁ h₂
  | isClosed =>
    exact isClosed_setOf_tendsto_average_norm (continuous_corr U one f) (corr_add_right U one f)
      (C := (1 + ‖one‖ ^ 2) * ‖f‖) fun g t => (norm_corr_le one hU f g t).trans_eq (by ring)

/-- **Weak mixing is equivalent to its `L²` form.** A jointly measurable action of `ℝ` preserving
a finite measure `μ` is weakly mixing exactly when, for all `f g` in complex `L²(μ)`, the
centered correlations `⟪g, U_t f⟫ - (∫ f) conj (∫ g)` of the Koopman group tend to `0` in Cesàro
mean in absolute value. -/
theorem isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup :
    IsWeaklyMixing μ ↔ ∀ f g : Lp ℂ 2 μ,
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ -
          (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ)‖) atTop (𝓝 0) := by
  refine ⟨fun h => h.tendsto_average_norm_inner_koopmanGroup,
    fun h => isWeaklyMixing_def.2 fun A B hA hB => ?_⟩
  have := h (indicatorConstLp 2 hA (measure_ne_top μ A) 1)
    (indicatorConstLp 2 hB (measure_ne_top μ B) 1)
  simp_rw [← corr_koopmanGroup, norm_corr_indicatorConstLp, norm_one, one_mul] at this
  exact this

/-! ### Eigenfunctions of a weakly mixing action -/

/-- **Eigenfunctions of a weakly mixing action are constant.** For a weakly mixing jointly
measurable action of `ℝ` preserving a finite measure `μ`, every a.e. strongly measurable
`f : X → ℂ` with, for some `a` and every `t`, `f(t +ᵥ x) = exp(2πiat) f(x)` for almost every `x`,
is almost everywhere constant. This is one half of the eigenfunction criterion for weak mixing. -/
theorem IsWeaklyMixing.exists_ae_eq_const_of_eigenfunction (h : IsWeaklyMixing μ) {f : X → ℂ}
    (hf : AEStronglyMeasurable f μ) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    ∃ c : ℂ, f =ᵐ[μ] Function.const X c := by
  have := h.ergodicVAdd
  rcases eq_or_ne a 0 with rfl | ha
  · refine ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀ ℝ hf.aemeasurable.nullMeasurable
      fun t => ?_
    filter_upwards [heig t] with x hx
    simpa using hx
  refine ⟨0, ?_⟩
  have hF := memLp_of_eigenfunction 2 hf heig
  set F := hF.toLp f
  -- The integral of `f` vanishes: it is multiplied by `exp(2πia t) = -1` at `t = 1/(2a)`.
  have hint : ∫ x, f x ∂μ = 0 := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hcomp := (measurePreserving_vadd (1 / (2 * a)) μ).integral_comp
      (MeasurableEquiv.vadd (1 / (2 * a)) : X ≃ᵐ X).measurableEmbedding f
    rw [integral_congr_ae (heig _), integral_const_mul,
      show 2 * (Real.pi : ℂ) * a * ((1 / (2 * a) : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by
        push_cast; field_simp] at hcomp
    simp only [Complex.exp_pi_mul_I] at hcomp
    linear_combination -hcomp / 2
  have hFint : ∫ x, F x ∂μ = 0 := by
    rw [integral_congr_ae hF.coeFn_toLp, hint]
  -- The centered correlation of `F` with itself has constant absolute value `‖F‖²`.
  have heigF : ∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t F =
      Complex.exp ((2 * Real.pi * a : ℝ) * t * Complex.I) • F :=
    (Semigroups.StronglyContinuousGroup.mem_eigenspace_iff _ _ _ _).1
      (toLp_mem_eigenspace_koopmanGroup hf heig)
  have hcorr : ∀ t : ℝ, ‖⟪F, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t F⟫_ℂ -
      (∫ x, F x ∂μ) * conj (∫ x, F x ∂μ)‖ = ‖F‖ ^ 2 := by
    intro t
    rw [hFint, zero_mul, sub_zero, heigF t, inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_mul]
    simp only [show ((2 * Real.pi * a : ℝ) : ℂ) * t * Complex.I = ((2 * Real.pi * a * t : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
    norm_cast
    exact abs_of_nonneg (by positivity)
  have hlim := h.tendsto_average_norm_inner_koopmanGroup F F
  simp_rw [hcorr] at hlim
  have hF0 : F = 0 := by simpa using TauCeti.intervalIntegral.eq_zero_of_tendsto_average_const hlim
  filter_upwards [hF.coeFn_toLp, (Lp.ext_iff.1 hF0).trans (Lp.coeFn_zero ℂ 2 μ)] with x h₁ h₂
  rw [← h₁, h₂, Pi.zero_apply, Function.const_apply]

/-! ### The eigenfunction criterion -/

/-- **Trivial eigenfunctions imply weak mixing.** For a jointly measurable action of `ℝ`
preserving a probability measure `μ`, if every a.e. strongly measurable `f : X → ℂ` with, for some
`a` and every `t`, `f(t +ᵥ x) = exp(2πiat) f(x)` for almost every `x`, is almost everywhere
constant, then the action is weakly mixing. -/
theorem isWeaklyMixing_of_forall_eigenfunction [IsProbabilityMeasure μ]
    (h : ∀ f : X → ℂ, AEStronglyMeasurable f μ → ∀ a : ℝ,
      (∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
        fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) →
      ∃ c : ℂ, f =ᵐ[μ] Function.const X c) :
    IsWeaklyMixing μ := by
  set U := koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top
  have hU : U.IsUnitary := koopmanGroup_isUnitary μ ℂ
  refine isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup.2 fun f g => ?_
  have hfg := hU.tendsto_average_norm_inner_sub_of_forall_mem_eigenspace inner_one_one
    koopmanGroup_one ?_ f g
  · simp only [← corr_apply U one] at hfg
    simpa only [U, corr_koopmanGroup] using hfg
  -- every Koopman eigenvector is a multiple of `1`
  · intro ω u hu
    obtain ⟨c, hc⟩ := h u (Lp.aestronglyMeasurable u) (ω / (2 * Real.pi)) fun t => by
      filter_upwards [(mem_eigenspace_koopmanGroup_iff ω u).1 hu t] with x hx
      rw [hx]
      congr 2
      push_cast
      field_simp
    refine ⟨c, Lp.ext ?_⟩
    filter_upwards [hc, Lp.coeFn_smul c (one : Lp ℂ 2 μ), coeFn_one] with x h₁ h₂ h₃
    rw [h₁, h₂, Pi.smul_apply, h₃, smul_eq_mul, mul_one, Function.const_apply]

/-- **The eigenfunction criterion for weak mixing.** A jointly measurable action of `ℝ` preserving
a probability measure `μ` is weakly mixing exactly when every a.e. strongly measurable
`f : X → ℂ` with, for some `a` and every `t`, `f(t +ᵥ x) = exp(2πiat) f(x)` for almost every
`x`, is almost everywhere constant. -/
theorem isWeaklyMixing_iff_forall_eigenfunction [IsProbabilityMeasure μ] :
    IsWeaklyMixing μ ↔ ∀ f : X → ℂ, AEStronglyMeasurable f μ → ∀ a : ℝ,
      (∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
        fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) →
      ∃ c : ℂ, f =ᵐ[μ] Function.const X c :=
  ⟨fun h _ hf _ heig => h.exists_ae_eq_const_of_eigenfunction hf heig,
    isWeaklyMixing_of_forall_eigenfunction⟩

end MeasureTheory.Measure
