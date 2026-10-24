/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace

/-!
# The Mihlin–Hörmander multiplier theorem

Let `V` be a real inner product space of finite dimension `n ≥ 1` and `F` a complex Hilbert space.
A symbol `m : V → ℂ`, smooth away from the origin, satisfies **Mihlin's condition** of order `N`
with constant `A` if

`‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`.

The **Mihlin–Hörmander multiplier theorem**
(`TauCeti.exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le`) says that if
`2N > n`, then for every `1 < p < ∞` the `L²` Fourier multiplier `T_m`
(`MeasureTheory.Lp.fourierMultiplierCLM`) is bounded in the `Lᵖ` norm, `‖T_m f‖_p ≤ C A ‖f‖_p`,
with `C` independent of `m` and `A`. For a symbol of temperate growth, the multiplier on
tempered distributions therefore maps every `f ∈ Lᵖ` to an `Lᵖ` function with the same bound
(`TauCeti.exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le`), by density of
the Schwartz functions in `Lᵖ`. The symbols of the Riesz transforms and of
`∂_v ∂_w Δ⁻¹`, and more generally every symbol that is smooth away from the origin and
homogeneous of degree `0`, satisfy Mihlin's condition of every order.

## The argument

Cut `m` into the Littlewood–Paley pieces `ψⱼ • m` of a bump function supported in the unit ball
(`ContDiffBump.littlewoodPaleyPiece`), and let `σₙ = ∑_{-n < j ≤ n} ψⱼ • m` be the truncations.
These are Schwartz functions, bounded by `‖m‖_∞`, and they converge to `m` away from the origin.

* The pieces are band-limited at the scales `2 ^ j` and satisfy the derivative bounds
  `‖D^k (ψⱼ • m) ξ‖ ≤ C A / (2 ^ j) ^ k` with `C` independent of `j`
  (`ContDiffBump.exists_norm_iteratedFDeriv_littlewoodPaleyPiece_le`), so the kernels `𝓕⁻ σₙ`
  satisfy Hörmander's condition `∫_{‖x‖ > 2 ‖h‖} ‖𝓕⁻ σₙ (x - h) - 𝓕⁻ σₙ x‖ dx ≤ B A`
  uniformly in `n` (`SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le`).
* `T_{σₙ}` is convolution with `𝓕⁻ σₙ` (`SchwartzMap.coeFn_fourierMultiplierCLM_toLp`), and its
  adjoint is the multiplier with the truncations of the conjugate symbol, which satisfies the
  same condition. The Calderón–Zygmund theorem under Hörmander's condition
  (`TauCeti.exists_eLpNorm_le_of_hormander`) then bounds `T_{σₙ}` in the `Lᵖ` norm uniformly
  in `n`.
* `T_{σₙ} f → T_m f` in `L²` (`MeasureTheory.Lp.tendsto_fourierMultiplierCLM_apply`), so almost
  everywhere along a subsequence, and Fatou's lemma passes the bound to `T_m`.

The proof first treats symbols with Mihlin constant `1` and then rescales.

The symbol is assumed smooth away from the origin, rather than only `N` times differentiable, so
that its Littlewood–Paley pieces are Schwartz functions.

## References

* S. G. Mihlin, *On the multipliers of Fourier integrals*, Dokl. Akad. Nauk SSSR **109** (1956),
  701–703.
* L. Hörmander, *Estimates for translation invariant operators in Lᵖ spaces*, Acta Math. **104**
  (1960), 93–140.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Theorem 6.2.7.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap ContDiff LineDeriv Topology
open FourierTransform MeasureTheory Metric Filter ContinuousLinearMap Module

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

variable [FiniteDimensional ℝ V]

/-- The bump function equal to `1` on the ball of radius `1/2` and supported in the unit ball,
whose Littlewood–Paley pieces at scale `2 ^ j` are supported in `closedBall 0 (2 ^ j)`. -/
private def mihlinBump : ContDiffBump (0 : V) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The truncation `∑_{-n < j ≤ n} ψⱼ • m` of a symbol `m` smooth away from the origin. -/
private def mihlinTrunc {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (n : ℕ) : 𝓢(V, ℂ) :=
  ∑ j ∈ Finset.Ioc (-(n : ℤ)) n, mihlinBump.littlewoodPaleyPiece hm j

/-- The truncations are `(φ (2⁻ⁿ ξ) - φ (2ⁿ ξ)) • m ξ`, where `φ` is the bump function. -/
private theorem mihlinTrunc_apply {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (n : ℕ) (ξ : V) :
    mihlinTrunc hm n ξ = (mihlinBump (V := V) (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ) -
      mihlinBump (V := V) (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ)) • m ξ := by
  rw [mihlinTrunc, sum_apply,
    ContDiffBump.sum_littlewoodPaleyPiece_Ioc _ hm (by omega)]

/-- The truncations of a symbol bounded by `A` away from the origin are bounded by `A`. -/
private theorem norm_mihlinTrunc_le {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {A : ℝ}
    (hmA : ∀ ξ ≠ 0, ‖m ξ‖ ≤ A) (hA : 0 ≤ A) (n : ℕ) (ξ : V) : ‖mihlinTrunc hm n ξ‖ ≤ A := by
  rw [mihlinTrunc_apply]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hA]
  rw [norm_smul, Real.norm_eq_abs]
  refine (mul_le_mul ?_ (hmA ξ hξ) (norm_nonneg _) zero_le_one).trans (one_mul A).le
  have h₁ := (mihlinBump (V := V)).nonneg (x := ((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ)
  have h₂ := (mihlinBump (V := V)).le_one (x := ((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ)
  have h₃ := (mihlinBump (V := V)).nonneg (x := ((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ)
  have h₄ := (mihlinBump (V := V)).le_one (x := ((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ)
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- Away from the origin the truncations converge to the symbol. -/
private theorem tendsto_mihlinTrunc {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {ξ : V}
    (hξ : ξ ≠ 0) : Tendsto (fun n ↦ mihlinTrunc hm n ξ) atTop (𝓝 (m ξ)) := by
  have := (mihlinBump.hasSum_littlewoodPaleyPiece hm hξ).comp (Finset.tendsto_Ioc_neg (R := ℤ))
  simpa [mihlinTrunc, sum_apply, Function.comp_def] using this

variable [MeasurableSpace V] [BorelSpace V]

/-- **Hörmander's condition for the truncations**, uniformly in the truncation and in the symbol:
the kernels `𝓕⁻ σₙ` of the truncations `σₙ` of a symbol satisfying Mihlin's condition of order
`N > n / 2` with constant `1` satisfy `∫_{‖x‖ > 2 ‖h‖} ‖𝓕⁻ σₙ (x - h) - 𝓕⁻ σₙ x‖ dx ≤ B`. -/
private theorem exists_setIntegral_norm_fourierInv_mihlinTrunc_sub_sub_le {N : ℕ}
    (hN : finrank ℝ V < 2 * N) :
    ∃ B, 0 ≤ B ∧ ∀ {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ),
      (∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ 1 / ‖ξ‖ ^ k) → ∀ (n : ℕ) (h : V),
        ∫ x in {x | 2 * ‖h‖ < ‖x‖},
          ‖𝓕⁻ (mihlinTrunc hm n) (x - h) - 𝓕⁻ (mihlinTrunc hm n) x‖ ≤ B := by
  obtain ⟨C₀, hC₀, hpiece⟩ :=
    (mihlinBump (V := V)).exists_norm_iteratedFDeriv_littlewoodPaleyPiece_le N
  obtain ⟨C, hC, hK⟩ :=
    SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le (H := ℂ)
      (stdOrthonormalBasis ℝ V) hN
  refine ⟨C * C₀, mul_nonneg hC hC₀, fun hm hmA n h ↦ ?_⟩
  refine hK (fun j ↦ mihlinBump.littlewoodPaleyPiece hm j) _ hC₀ (fun j _ ↦ ?_)
    (fun j _ k hk i ξ ↦ ?_) h
  · refine (subset_tsupport _).trans ((mihlinBump.tsupport_littlewoodPaleyPiece_subset hm j).trans
      ?_)
    exact fun ξ hξ ↦ mem_closedBall_zero_iff.2 (by simpa [mihlinBump] using hξ.2)
  · rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ k (mihlinBump.littlewoodPaleyPiece hm j : V → ℂ) ξ).le_opNorm
      _).trans ?_
    simpa using hpiece hm zero_le_one hmA j k hk ξ

/-- The real-linear kernel `k x y = 𝓕⁻ σ (x - y) • id` of the multiplier with symbol `σ`. -/
private def mihlinKernel (σ : 𝓢(V, ℂ)) (x y : V) : F →L[ℝ] F :=
  lsmul ℝ ℂ (𝓕⁻ σ (x - y))

/-- The kernel `mihlinKernel σ` is continuous, hence strongly measurable. -/
private theorem stronglyMeasurable_mihlinKernel (σ : 𝓢(V, ℂ)) :
    StronglyMeasurable (Function.uncurry (mihlinKernel (F := F) σ)) :=
  ((lsmul ℝ ℂ).continuous.comp ((𝓕⁻ σ).continuous.comp continuous_sub)).stronglyMeasurable

/-- Hörmander's condition for `𝓕⁻ σ` in the translation-invariant form gives it for the kernel
`mihlinKernel σ` in the two-variable form of the Calderón–Zygmund theorems. -/
private theorem setLIntegral_enorm_mihlinKernel_sub_le (σ : 𝓢(V, ℂ)) {B : ℝ}
    (hB : ∀ h, ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖𝓕⁻ σ (x - h) - 𝓕⁻ σ x‖ ≤ B) (y y' : V) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'},
      ‖mihlinKernel (F := F) σ x y - mihlinKernel σ x y'‖ₑ ≤ ENNReal.ofReal B := by
  set h := y - y'
  have hS : MeasurableSet {z : V | 2 * ‖h‖ < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hS' : MeasurableSet {x : V | 2 * dist y y' < dist x y'} :=
    measurableSet_lt measurable_const (measurable_id.dist measurable_const)
  have hint : Integrable (fun z ↦ 𝓕⁻ σ (z - h) - 𝓕⁻ σ z) :=
    ((𝓕⁻ σ).integrable.comp_sub_right h).sub (𝓕⁻ σ).integrable
  calc ∫⁻ x in {x | 2 * dist y y' < dist x y'},
        ‖mihlinKernel (F := F) σ x y - mihlinKernel σ x y'‖ₑ
      ≤ ∫⁻ x, {z : V | 2 * ‖h‖ < ‖z‖}.indicator
          (fun z ↦ ‖𝓕⁻ σ (z - h) - 𝓕⁻ σ z‖ₑ) (x - y') := by
        rw [← lintegral_indicator hS']
        refine lintegral_mono fun x ↦ ?_
        simp only [Set.indicator, Set.mem_ofPred_eq, dist_eq_norm, h]
        split_ifs
        · rw [mihlinKernel, mihlinKernel, ← map_sub, sub_sub_sub_cancel_right]
          exact enorm_le_iff_norm_le.2 ((opNorm_lsmul_apply_le _).trans_eq (by abel_nf))
        · exact le_rfl
    _ = ∫⁻ z in {z | 2 * ‖h‖ < ‖z‖}, ‖𝓕⁻ σ (z - h) - 𝓕⁻ σ z‖ₑ := by
        rw [lintegral_sub_right_eq_self, lintegral_indicator hS]
    _ = ENNReal.ofReal (∫ z in {z | 2 * ‖h‖ < ‖z‖}, ‖𝓕⁻ σ (z - h) - 𝓕⁻ σ z‖) :=
        (ofReal_integral_norm_eq_lintegral_enorm hint.integrableOn).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB h)

variable [CompleteSpace F]

/-- The `L²` multiplier with a Schwartz symbol `σ`, viewed as a real-linear operator, is given by
the kernel `mihlinKernel σ`. -/
private theorem ae_fourierMultiplierCLM_eq_integral_mihlinKernel (σ : 𝓢(V, ℂ))
    (f : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, (Lp.fourierMultiplierCLM F (σ.toLp ∞)).restrictScalars ℝ f x =
      ∫ z, mihlinKernel σ x z (f z) := by
  filter_upwards [σ.coeFn_fourierMultiplierCLM_toLp f] with x hx
  simp [hx, mihlinKernel]

/-- The truncations of a symbol bounded by `1` give multipliers of norm at most `1`. -/
private theorem norm_toLp_mihlinTrunc_le {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ)
    (hmA : ∀ ξ ≠ 0, ‖m ξ‖ ≤ 1) (n : ℕ) : ‖(mihlinTrunc hm n).toLp ∞ (volume : Measure V)‖ ≤ 1 :=
  SchwartzMap.norm_toLp_top_le.trans (SchwartzMap.seminorm_le_bound ℝ 0 0 _ zero_le_one fun ξ ↦ by
    simpa using norm_mihlinTrunc_le hm hmA zero_le_one n ξ)

/-- Complex conjugation of the truncated symbol truncates the conjugate symbol. -/
private theorem star_toLp_mihlinTrunc {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ)
    (hm' : ContDiffOn ℝ ∞ (fun ξ ↦ (starRingEnd ℂ) (m ξ)) {0}ᶜ) (n : ℕ) :
    star ((mihlinTrunc hm n).toLp ∞ (volume : Measure V)) =
      (mihlinTrunc hm' n).toLp ∞ (volume : Measure V) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star ((mihlinTrunc hm n).toLp ∞ (volume : Measure V)),
    (mihlinTrunc hm n).coeFn_toLp ∞ (volume : Measure V),
    (mihlinTrunc hm' n).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂ h₃
  rw [h₁, Pi.star_apply, h₂, h₃, mihlinTrunc_apply, mihlinTrunc_apply]
  simp [Complex.real_smul]

/-- **The Calderón–Zygmund bound for the truncations**, uniformly in the truncation and in the
symbol, for symbols satisfying Mihlin's condition of order `N > n / 2` with constant `1`. -/
private theorem exists_eLpNorm_fourierMultiplierCLM_mihlinTrunc_le [Nontrivial V] {N : ℕ}
    (hN : finrank ℝ V < 2 * N) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ {m : V → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ),
      (∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ 1 / ‖ξ‖ ^ k) →
      ∀ (n : ℕ) (f : Lp F 2 (volume : Measure V)),
        eLpNorm (Lp.fourierMultiplierCLM F ((mihlinTrunc hm n).toLp ∞ volume) f) p volume ≤
          C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, -, hB⟩ := exists_setIntegral_norm_fourierInv_mihlinTrunc_sub_sub_le (V := V) hN
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_hormander (V := V) (H := F) (K := F) (M := 1)
    (B := ENNReal.ofReal B) (B' := ENNReal.ofReal B) ENNReal.one_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hp hp_top
  refine ⟨C, fun {m} hm hmA n f ↦ ?_⟩
  have hm0 : ∀ ξ ≠ 0, ‖m ξ‖ ≤ 1 := fun ξ hξ ↦ by simpa using hmA 0 (Nat.zero_le _) ξ hξ
  set σ := mihlinTrunc hm n
  -- The conjugate symbol is smooth away from the origin and satisfies the same Mihlin bounds.
  have hm' : ContDiffOn ℝ ∞ (fun ξ ↦ (starRingEnd ℂ) (m ξ)) {0}ᶜ :=
    Complex.conjCLE.contDiff.comp_contDiffOn hm
  have hmA' : ∀ k ≤ N, ∀ ξ ≠ 0,
      ‖iteratedFDeriv ℝ k (fun ξ ↦ (starRingEnd ℂ) (m ξ)) ξ‖ ≤ 1 / ‖ξ‖ ^ k := fun k hk ξ hξ ↦ by
    simpa [Function.comp_def, Complex.conjLIE_apply] using
      (Complex.conjLIE.norm_iteratedFDeriv_comp_left m ξ k).trans_le (hmA k hk ξ hξ)
  set σ' := mihlinTrunc hm' n
  set T := (Lp.fourierMultiplierCLM F (σ.toLp ∞ (volume : Measure V))).restrictScalars ℝ
  have hT : adjoint T =
      (Lp.fourierMultiplierCLM F (σ'.toLp ∞ (volume : Measure V))).restrictScalars ℝ := by
    -- The real inner product of `L²` is the real part of the complex one.
    have hre : ∀ f g : Lp F 2 (volume : Measure V), inner ℝ f g = Complex.re (inner ℂ f g) :=
      fun f g ↦ by
        rw [L2.inner_def, L2.inner_def]
        exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
    refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
    rw [hre, hre, coe_restrictScalars', coe_restrictScalars', ← star_toLp_mihlinTrunc hm hm',
      ← Lp.adjoint_fourierMultiplierCLM, adjoint_inner_left]
  have hTn : ‖T‖ₑ ≤ 1 := by
    rw [← ofReal_norm, norm_restrictScalars, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      ((Lp.norm_fourierMultiplierCLM_le _).trans (norm_toLp_mihlinTrunc_le hm hm0 n))
  refine hC T (mihlinKernel σ) (mihlinKernel σ') hTn (stronglyMeasurable_mihlinKernel σ)
    (stronglyMeasurable_mihlinKernel σ') (setLIntegral_enorm_mihlinKernel_sub_le σ (hB hm hmA n))
    (setLIntegral_enorm_mihlinKernel_sub_le σ' (hB hm' hmA' n))
    (fun g _ _ _ ↦ (ae_fourierMultiplierCLM_eq_integral_mihlinKernel σ g).mono fun _ hx _ ↦ hx)
    (fun g _ _ _ ↦ hT ▸ (ae_fourierMultiplierCLM_eq_integral_mihlinKernel σ' g).mono
      fun _ hx _ ↦ hx) f

/-- The Mihlin–Hörmander bound for symbols with Mihlin constant `1`: the truncated bounds pass to
the limit, since the truncated multipliers converge strongly on `L²`. -/
private theorem exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le_one
    [Nontrivial V] {N : ℕ} (hN : finrank ℝ V < 2 * N) {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ {m : V → ℂ}, ContDiffOn ℝ ∞ m {0}ᶜ →
      (∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ 1 / ‖ξ‖ ^ k) →
      ∀ m' : Lp ℂ ∞ (volume : Measure V), m' =ᵐ[volume] m →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (Lp.fourierMultiplierCLM F m' f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_mihlinTrunc_le (F := F) hN hp hp_top
  refine ⟨C, fun {m} hm hmA m' hm' f ↦ ?_⟩
  have hm0 : ∀ ξ ≠ 0, ‖m ξ‖ ≤ 1 := fun ξ hξ ↦ by simpa using hmA 0 (Nat.zero_le _) ξ hξ
  have hlim : Tendsto (fun n ↦ Lp.fourierMultiplierCLM F ((mihlinTrunc hm n).toLp ∞ volume) f)
      atTop (𝓝 (Lp.fourierMultiplierCLM F m' f)) := by
    refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1)
      (.of_forall (norm_toLp_mihlinTrunc_le hm hm0)) ?_ f
    filter_upwards [ae_all_iff.2 fun n ↦ (mihlinTrunc hm n).coeFn_toLp ∞ (volume : Measure V),
      hm', Measure.ae_ne volume 0] with ξ h₁ h₂ h₃
    simp only [h₁, h₂]
    exact tendsto_mihlinTrunc hm h₃
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun _ ↦ Lp.aestronglyMeasurable _) _
    (Lp.aestronglyMeasurable _) hae).trans ?_
  exact liminf_le_of_frequently_le' (.of_forall fun n ↦ hC hm hmA (ns n) f)

/-- **The Mihlin–Hörmander multiplier theorem.** Let `V` be a real inner product space of finite
dimension `n ≥ 1`, let `N` be an integer with `2N > n`, and let `1 < p < ∞`. There is a constant
`C` with the following property. Let `m : V → ℂ` be smooth away from the origin and satisfy
**Mihlin's condition** of order `N` with constant `A`:

`‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`.

Then the `L²` Fourier multiplier `T_m` with symbol `m` is bounded in the `Lᵖ` norm:
`‖T_m f‖_p ≤ C A ‖f‖_p` for every `f ∈ L²(V, F)`, with values in any complex Hilbert space `F`.
The symbol enters as any element of `L^∞` almost everywhere equal to `m`, and the constant `C`
does not depend on `m` or `A`. -/
theorem exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le [Nontrivial V] {N : ℕ}
    (hN : finrank ℝ V < 2 * N) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ {m : V → ℂ}, ContDiffOn ℝ ∞ m {0}ᶜ → ∀ {A : ℝ≥0},
      (∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k) →
      ∀ m' : Lp ℂ ∞ (volume : Measure V), m' =ᵐ[volume] m →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (Lp.fourierMultiplierCLM F m' f) p volume ≤ C * A * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le_one (F := F) hN hp hp_top
  refine ⟨C, fun {m} hm {A} hmA m' hm' f ↦ ?_⟩
  rcases eq_or_ne A 0 with rfl | hA
  · -- With `A = 0` the symbol vanishes away from the origin, hence almost everywhere.
    have hzero : m' = 0 := by
      refine Lp.ext ?_
      filter_upwards [hm', Lp.coeFn_zero ℂ ∞ (volume : Measure V), Measure.ae_ne volume 0]
        with ξ h₁ h₂ h₃
      rw [h₁, h₂, Pi.zero_apply, ← norm_le_zero_iff]
      simpa using hmA 0 (Nat.zero_le _) ξ h₃
    simp only [hzero, Lp.fourierMultiplierCLM_zero, zero_apply]
    rw [eLpNorm_congr_ae (Lp.coeFn_zero _ _ _)]
    simp
  -- Otherwise rescale the symbol to Mihlin constant `1`: `T_{m'} = A • T_{A⁻¹ m'}`.
  set c : ℂ := (((A : ℝ)⁻¹ : ℝ) : ℂ)
  have hA' : (A : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hA
  have hc : (A : ℂ) * c = 1 := by
    simp only [c, Complex.ofReal_inv]
    exact mul_inv_cancel₀ (by exact_mod_cast hA)
  have hmc : ContDiffOn ℝ ∞ (fun ξ ↦ c • m ξ) {0}ᶜ := hm.const_smul c
  have hmcA : ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k (fun ξ ↦ c • m ξ) ξ‖ ≤ 1 / ‖ξ‖ ^ k :=
    fun k hk ξ hξ ↦ by
      rw [iteratedFDeriv_const_smul_apply'
        ((hm.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)).of_le (mod_cast le_top)),
        norm_smul]
      calc ‖c‖ * ‖iteratedFDeriv ℝ k m ξ‖ ≤ (A : ℝ)⁻¹ * (A / ‖ξ‖ ^ k) := by
            rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 A.coe_nonneg)]
            gcongr
            exact hmA k hk ξ hξ
        _ = 1 / ‖ξ‖ ^ k := by field_simp
  have hcm' : c • m' =ᵐ[volume] fun ξ ↦ c • m ξ := by
    filter_upwards [Lp.coeFn_smul c m', hm'] with ξ h₁ h₂
    rw [h₁, Pi.smul_apply, h₂]
  have hT : Lp.fourierMultiplierCLM F m' f =
      (A : ℂ) • Lp.fourierMultiplierCLM F (c • m') f := by
    rw [← smul_apply, ← Lp.fourierMultiplierCLM_smul, smul_smul, hc, one_smul]
  rw [hT, eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, mul_comm (C : ℝ≥0∞),
    mul_assoc]
  gcongr
  · simp [← ofReal_norm]
  · exact hC hmc hmcA (c • m') hcm' f

/-- **The Mihlin–Hörmander multiplier theorem on `Lᵖ`.** Let `V` be a real inner product space of
finite dimension `n ≥ 1`, let `2N > n` and `1 < p < ∞`. There is a constant `C` such that for
every symbol `m` of temperate growth satisfying Mihlin's condition of order `N` with constant `A`,

`‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`,

the Fourier multiplier `𝓕⁻ (m • 𝓕 f)` of the tempered distribution of any `f ∈ Lᵖ(V, F)` is an
`Lᵖ` function `g` with `‖g‖_p ≤ C A ‖f‖_p`. -/
theorem exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le [Nontrivial V]
    {N : ℕ} (hN : finrank ℝ V < 2 * N) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ {m : V → ℂ}, m.HasTemperateGrowth → ∀ {A : ℝ≥0},
      (∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k) →
      ∀ f : Lp F p (volume : Measure V), ∃ g : Lp F p (volume : Measure V),
        TemperedDistribution.fourierMultiplierCLM F m (f : 𝓢'(V, F)) = g ∧
          ‖g‖ ≤ C * A * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le (F := F) hN hp hp_top
  refine ⟨C, fun {m} hm {A} hmA f ↦ ?_⟩
  -- The symbol is bounded, by Mihlin's condition of order zero away from the origin.
  have hm_bdd : MemLp m (∞ : ℝ≥0∞) volume := by
    refine memLp_top_of_bound hm.1.continuous.aestronglyMeasurable A ?_
    filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    simpa using hmA 0 (Nat.zero_le _) ξ hξ
  -- On Schwartz functions the multiplier agrees with the `L²` multiplier, so it satisfies the
  -- `Lᵖ` bound of `exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le`.
  set T : 𝓢(V, F) →L[ℂ] 𝓢(V, F) := SchwartzMap.fourierMultiplierCLM F m
  have hS : ∀ φ : 𝓢(V, F), ‖(T φ).toLp p‖ ≤ C * A * ‖φ.toLp p‖ := by
    intro φ
    have h := hC hm.1.contDiffOn hmA (hm_bdd.toLp m) hm_bdd.coeFn_toLp (φ.toLp 2)
    rw [SchwartzMap.toLp_fourierMultiplierCLM_eq hm hm_bdd,
      eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 _),
      eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 _)] at h
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ p _),
      eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ p _)]
    have hfin : eLpNorm (φ : V → F) p volume ≠ (∞ : ℝ≥0∞) := (φ.memLp p).eLpNorm_ne_top
    calc _ ≤ ((C : ℝ≥0∞) * A * eLpNorm (φ : V → F) p volume).toReal :=
          ENNReal.toReal_mono (by finiteness) h
      _ = _ := by simp [ENNReal.toReal_mul]
  -- Extend `φ ↦ (T φ).toLp p` from the dense Schwartz functions to all of `Lᵖ`, by the bound.
  set e : 𝓢(V, F) →ₗ[ℂ] Lp F p (volume : Measure V) :=
    (SchwartzMap.toLpCLM ℂ F p (volume : Measure V)).toLinearMap
  have he : DenseRange e := SchwartzMap.denseRange_toLpCLM (F := F) (μ := volume) hp_top
  set S : 𝓢(V, F) →ₗ[ℂ] Lp F p (volume : Measure V) := e ∘ₗ T.toLinearMap
  have hSe : ∀ φ, ‖S φ‖ ≤ C * A * ‖e φ‖ := hS
  refine ⟨S.extendOfNorm e f, ?_, LinearMap.norm_extendOfNorm_apply_le he _ hSe f⟩
  -- Both sides are continuous in `f` and agree on the dense Schwartz functions.
  refine congrFun (he.equalizer (g := fun f ↦ TemperedDistribution.fourierMultiplierCLM F m
    (f : 𝓢'(V, F))) (h := fun f ↦ ((S.extendOfNorm e f : Lp F p volume) : 𝓢'(V, F)))
    (TemperedDistribution.fourierMultiplierCLM F m ∘L
      Lp.toTemperedDistributionCLM F volume p).continuous
    ((Lp.toTemperedDistributionCLM F volume p).continuous.comp (S.extendOfNorm e).continuous)
    (funext fun φ ↦ ?_)) f
  simp only [Function.comp_apply, LinearMap.extendOfNorm_eq he ⟨_, hSe⟩]
  simp only [S, e, T, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, SchwartzMap.toLpCLM_apply,
    Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hm]

end TauCeti
