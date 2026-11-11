/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Dilation
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# The reverse Bernstein inequality

Let `E` be a finite-dimensional real inner product space, and let `f` be a Schwartz function on
`E` whose Fourier transform vanishes outside the annulus `R ≤ ‖ξ‖ ≤ θ R`, for some `R > 0`. The
**reverse Bernstein inequality** says that the derivatives of `f` control `f` itself: for
`1 ≤ p ≤ ∞` and every order `k` there is `C`, depending on `θ` but not on `R` or `f`, with

`‖f‖_p ≤ C R ^ (-k) ‖Dᵏ f‖_p`

(`SchwartzMap.exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset`). It complements
Bernstein's inequality for frequencies in a ball,
`TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`, which bounds the
derivatives by the function.

These are the basic estimates of Littlewood–Paley theory: a dyadic block whose frequencies have
size `2 ^ j` behaves like a function at the single scale `2 ^ (-j)`, so that each derivative costs
exactly a factor `2 ^ j`. The reverse inequality identifies Besov norms of positive regularity
through derivatives.

## Implementation notes

The inequality is proved at frequency scale `R = 1` and transported to every `R` by the dilation
`f ↦ f (R⁻¹ • ·)`, which rescales frequencies by `R⁻¹` and `Lᵖ` norms by `R ^ (d/p)`, where `d`
is the dimension of `E`. At scale `1`, the symbols `⟪bᵢ, ξ⟫ / (2πi ‖ξ‖²)`, cut off by a
Littlewood–Paley partition, invert the partial derivatives: `f = ∑ᵢ T_{σᵢ} (∂_{bᵢ} f)`. The full
derivative `Dᵏ f` is then compared with its entries on an orthonormal basis.

## Main declarations

* `SchwartzMap.exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset`: the reverse
  Bernstein inequality for frequencies in an annulus.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.1.
-/

public section

namespace SchwartzMap

open MeasureTheory Module LineDeriv
open scoped ENNReal NNReal FourierTransform Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A Schwartz function with frequencies in the annulus `1 ≤ ‖ξ‖ ≤ θ` is a sum of Fourier
multipliers with Schwartz symbols applied to its partial derivatives: on the annulus, the
symbols agree with `⟪bᵢ, ξ⟫ / (2πi ‖ξ‖²)`, and `∑ᵢ ⟪bᵢ, ξ⟫ ⟪ξ, bᵢ⟫ / ‖ξ‖² = 1`. -/
private theorem exists_eq_sum_fourierMultiplierCLM_lineDerivOp (θ : ℝ) :
    ∃ σ : Fin (finrank ℝ E) → 𝓢(E, ℂ), ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        f = ∑ i, fourierMultiplierCLM F (σ i) (∂_{stdOrthonormalBasis ℝ E i} f) := by
  let b := stdOrthonormalBasis ℝ E
  let m (i : Fin (finrank ℝ E)) (ξ : E) : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * ((inner ℝ (b i) ξ / ‖ξ‖ ^ 2 : ℝ) : ℂ)
  have hm (i : Fin (finrank ℝ E)) : ContDiffOn ℝ (⊤ : ℕ∞) (m i) {0}ᶜ := by
    refine contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn ?_)
    exact (innerSL ℝ (b i)).contDiff.contDiffOn.div (contDiff_norm_sq ℝ).contDiffOn
      fun ξ hξ => pow_ne_zero 2 (norm_ne_zero_iff.2 hξ)
  choose σ hσ using fun i => exists_eqOn_annulus_of_contDiffOn (hm i) θ
  refine ⟨σ, fun f hf => ?_⟩
  have hv (v : E) : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  have key : 𝓕 f = 𝓕 (∑ i, fourierMultiplierCLM F (σ i) (∂_{b i} f)) := by
    rw [FourierTransform.fourier_sum]
    ext ξ
    simp only [sum_apply, fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
      smulLeftCLM_apply_apply (σ _).hasTemperateGrowth, fourier_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply (hv _)]
    by_cases h0 : (𝓕 f : 𝓢(E, F)) ξ = 0
    · simp [h0]
    · have hξ := hf h0
      have hξ0 : ‖ξ‖ ≠ 0 := by linarith [hξ.1]
      simp_rw [hσ _ hξ]
      have hterm (i : Fin (finrank ℝ E)) :
          m i ξ • (2 * (Real.pi : ℂ) * Complex.I) • inner ℝ ξ (b i) • (𝓕 f : 𝓢(E, F)) ξ =
            ((inner ℝ (b i) ξ ^ 2 / ‖ξ‖ ^ 2 : ℝ) : ℂ) • (𝓕 f : 𝓢(E, F)) ξ := by
        rw [← Complex.coe_smul, smul_smul, smul_smul]
        congr 1
        simp only [m, real_inner_comm ξ (b i)]
        push_cast
        field_simp
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul, ← Complex.ofReal_sum,
        ← Finset.sum_div, b.sum_sq_inner_right, div_self (pow_ne_zero 2 hξ0), Complex.ofReal_one,
        one_smul]
  simpa using congrArg 𝓕⁻ key

/-- The reverse Bernstein inequality for the first partial derivatives, at frequency scale `1`. -/
private theorem exists_eLpNorm_le_sum_eLpNorm_lineDerivOp (θ : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        eLpNorm f p ≤ C * ∑ i, eLpNorm ⇑(∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E, F)) p := by
  obtain ⟨σ, hσ⟩ := exists_eq_sum_fourierMultiplierCLM_lineDerivOp (E := E) (F := F) θ
  -- Each multiplier is bounded on `Lᵖ` by the `L¹` norm of its Schwartz kernel `𝓕⁻ σᵢ`.
  have hfin (i : Fin (finrank ℝ E)) : eLpNorm (𝓕⁻ (σ i : E → ℂ)) 1 ≠ ∞ := by
    rw [← fourierInv_coe]
    exact ((𝓕⁻ (σ i) : 𝓢(E, ℂ)).memLp 1).eLpNorm_ne_top
  let C (i : Fin (finrank ℝ E)) : ℝ≥0 := (eLpNorm (𝓕⁻ (σ i : E → ℂ)) 1).toNNReal
  refine ⟨∑ i, C i, fun f hf => ?_⟩
  set b := stdOrthonormalBasis ℝ E
  have h (i : Fin (finrank ℝ E)) :
      eLpNorm ⇑(fourierMultiplierCLM F (σ i) (∂_{b i} f)) p ≤
        C i * eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p := by
    rw [ENNReal.coe_toNNReal (hfin i)]
    exact eLpNorm_fourierMultiplierCLM_le _ _ hp
  let g (i : Fin (finrank ℝ E)) : E → F := ⇑(fourierMultiplierCLM F (σ i) (∂_{b i} f))
  have h1 : eLpNorm f p = eLpNorm (∑ i, g i) p := by
    conv_lhs => rw [hσ f hf]
    congr 1
    ext x
    simp [g, sum_apply]
  have h2 : eLpNorm (∑ i, g i) p ≤ ∑ i, eLpNorm (g i) p := eLpNorm_sum_le hp
  have h3 (i : Fin (finrank ℝ E)) : eLpNorm (g i) p ≤
      (∑ j, (C j : ℝ≥0∞)) * eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p := by
    refine (h i).trans ?_
    gcongr
    exact Finset.single_le_sum (f := fun j => (C j : ℝ≥0∞)) (fun _ _ => zero_le)
      (Finset.mem_univ i)
  calc eLpNorm f p ≤ ∑ i, (∑ j, (C j : ℝ≥0∞)) * eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p :=
        h1.trans_le (h2.trans (Finset.sum_le_sum fun i _ => h3 i))
    _ = ((∑ i, C i : ℝ≥0) : ℝ≥0∞) * ∑ i, eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p := by
        push_cast
        rw [Finset.mul_sum]

/-- The reverse Bernstein inequality for the iterated partial derivatives of order `k`, at
frequency scale `1`. -/
private theorem exists_eLpNorm_le_sum_eLpNorm_iteratedLineDerivOp (θ : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        eLpNorm f p ≤ C * ∑ r : Fin k → Fin (finrank ℝ E),
          eLpNorm ⇑(∂^{fun j => stdOrthonormalBasis ℝ E (r j)} f : 𝓢(E, F)) p := by
  set b := stdOrthonormalBasis ℝ E
  induction k with
  | zero =>
    refine ⟨1, fun f _ => ?_⟩
    simp [iteratedLineDerivOp_fin_zero]
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_le_sum_eLpNorm_lineDerivOp (E := E) (F := F) θ hp
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * C₁, fun f hf => ?_⟩
    -- Reindex the pairs `(i, r)` as the tuples `Fin.cons i r`.
    have hre : ∑ r : Fin k → Fin (finrank ℝ E), ∑ i,
          eLpNorm ⇑(∂_{b i} (∂^{fun j => b (r j)} f) : 𝓢(E, F)) p =
        ∑ r : Fin (k + 1) → Fin (finrank ℝ E), eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p := by
      rw [← (Fin.consEquiv fun _ => Fin (finrank ℝ E)).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
      -- The tuple `Fin.cons i r` has head `i` and tail `r`.
      rw [iteratedLineDerivOp_succ_left]
      rfl
    calc eLpNorm f p
        ≤ C * ∑ r : Fin k → Fin (finrank ℝ E), eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p :=
          hC f hf
      _ ≤ C * ∑ r : Fin k → Fin (finrank ℝ E),
            C₁ * ∑ i, eLpNorm ⇑(∂_{b i} (∂^{fun j => b (r j)} f) : 𝓢(E, F)) p := by
          gcongr with r
          exact hC₁ _ ((support_fourier_iteratedLineDerivOp_subset f _).trans hf)
      _ = ((C * C₁ : ℝ≥0) : ℝ≥0∞) * ∑ r : Fin (k + 1) → Fin (finrank ℝ E),
            eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p := by
          rw [← hre, ← Finset.mul_sum, ENNReal.coe_mul, mul_assoc]

/-- The reverse Bernstein inequality for the iterated derivative, at frequency scale `1`. -/
private theorem exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_one_le_norm (θ : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        eLpNorm f p ≤ C * eLpNorm (iteratedFDeriv ℝ k f) p := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_sum_eLpNorm_iteratedLineDerivOp (E := E) (F := F) θ hp k
  refine ⟨C * Fintype.card (Fin k → Fin (finrank ℝ E)), fun f hf => ?_⟩
  set b := stdOrthonormalBasis ℝ E
  -- Each partial derivative along basis vectors is bounded by the full derivative.
  have h (r : Fin k → Fin (finrank ℝ E)) :
      eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p ≤ eLpNorm (iteratedFDeriv ℝ k f) p := by
    refine eLpNorm_mono (∂^{fun j => b (r j)} f).continuous.aestronglyMeasurable fun x => ?_
    rw [iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ k f x).le_opNorm _).trans_eq ?_
    simp [b.orthonormal.1]
  calc eLpNorm f p ≤ C * ∑ r : Fin k → Fin (finrank ℝ E),
        eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p := hC f hf
    _ ≤ C * ∑ _r : Fin k → Fin (finrank ℝ E), eLpNorm (iteratedFDeriv ℝ k f) p := by
        gcongr with r
        exact h r
    _ = ((C * Fintype.card (Fin k → Fin (finrank ℝ E)) : ℝ≥0) : ℝ≥0∞) *
          eLpNorm (iteratedFDeriv ℝ k f) p := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-- **The reverse Bernstein inequality.** For `1 ≤ p ≤ ∞`, `k : ℕ` and `θ : ℝ` there is `C` such
that every Schwartz function `f` whose Fourier transform vanishes outside the annulus
`R ≤ ‖ξ‖ ≤ θ R`, for some `R > 0`, satisfies `‖f‖_p ≤ C R ^ (-k) ‖Dᵏ f‖_p`. -/
theorem exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset (k : ℕ) (θ : ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ {R : ℝ}, 0 < R → ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ * R} →
        eLpNorm f p ≤ C * ENNReal.ofReal (R⁻¹ ^ k) * eLpNorm (iteratedFDeriv ℝ k f) p := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_one_le_norm (E := E) (F := F) θ hp k
  refine ⟨C, fun {R} hR f hf => ?_⟩
  -- The dilation `g = f (R⁻¹ • ·)` has its frequencies in the annulus `1 ≤ ‖ξ‖ ≤ θ`.
  let g : 𝓢(E, F) := compCLMOfContinuousLinearEquiv ℝ
    (LinearEquiv.smulOfNeZero ℝ E R⁻¹ (inv_ne_zero hR.ne')).toContinuousLinearEquiv f
  have hg : ⇑g = fun x => f (R⁻¹ • x) := rfl
  have hgsupp : Function.support ⇑(𝓕 g : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} := by
    rw [fourier_coe, hg, TauCeti.support_fourier_comp_smul _ (inv_ne_zero hR.ne'), ← fourier_coe]
    rintro _ ⟨ξ, hξ, rfl⟩
    obtain ⟨h1, h2⟩ := hf hξ
    refine ⟨?_, ?_⟩ <;> rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
    exacts [(le_inv_mul_iff₀ hR).2 (by linarith), (inv_mul_le_iff₀ hR).2 (by linarith)]
  have hmain := hC g hgsupp
  rw [hg, Measure.eLpNorm_iteratedFDeriv_comp_inv_smul volume (f.smooth k) hR.ne' p,
    Measure.eLpNorm_comp_inv_smul volume _ hR.ne' p, abs_of_pos hR, Real.rpow_sub hR,
    Real.rpow_natCast, div_eq_mul_inv _ (R ^ k), ← inv_pow,
    ENNReal.ofReal_mul (by positivity)] at hmain
  have h0 : ENNReal.ofReal (R ^ (finrank ℝ E / p.toReal)) ≠ 0 := by
    simpa using Real.rpow_pos_of_pos hR _
  refine (ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top).1 ?_
  exact hmain.trans_eq (by ring)

end SchwartzMap
