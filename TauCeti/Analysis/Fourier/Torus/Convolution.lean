/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Convolution.Young

/-!
# Convolution on the torus

On the torus `𝕋ᵈ = UnitAddTorus d` with an invariant measure `μ`, such as its Haar probability
measure, convolving a function `f` with the Fourier monomial `e_n = mFourier n` keeps only the
`n`-th Fourier mode of `f`:

`(e_n ⋆ f)(x) = ∫ e_n(t) f(x - t) dμ(t) = e_n(x) ∫ e_{-n}(t) f(t) dμ(t)`

(`UnitAddTorus.mFourier_convolution`). For the Haar probability measure the last integral is the
Fourier coefficient `f̂(n)`. The proof substitutes `t ↦ x - t` and splits
`e_n(x - t) = e_n(x) e_{-n}(t)` (`UnitAddTorus.mFourier_apply_sub`). No integrability of `f` is
needed: where the integral defining `f̂(n)` diverges, both sides vanish.

By linearity, convolution of an integrable `f` with a trigonometric polynomial `∑ c_n e_n` is the
Fourier multiplier `f ↦ ∑ c_n f̂(n) e_n` (`UnitAddTorus.sum_mul_mFourier_convolution`). This is
how convolution operators on `Lᵖ(𝕋ᵈ)` with trigonometric polynomial kernels, such as the periodic
Littlewood–Paley blocks, are identified with Fourier multipliers.

For a finite invariant measure `μ` and `1 ≤ p ≤ ∞`, convolution with a continuous kernel `k` is a
bounded operator on `Lᵖ(𝕋ᵈ, μ)` of norm at most `‖k‖₁`, by Young's inequality
`‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` (`MeasureTheory.eLpNorm_convolution_le`). This is
`UnitAddTorus.convolutionLp`, with operator norm bound `UnitAddTorus.norm_convolutionLp_le`.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution

namespace UnitAddTorus

variable {d : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure (UnitAddTorus d)}

section Fourier

variable [Fintype d]

/-- **Convolution with a Fourier monomial.** For an invariant measure `μ` on the torus, convolving
a function `f` with the monomial `mFourier n` keeps only its `n`-th Fourier mode:
`(mFourier n ⋆ f) x = mFourier n x • ∫ t, mFourier (-n) t • f t ∂μ`. For the Haar probability
measure the integral is the Fourier coefficient `mFourierCoeff f n`. -/
theorem mFourier_convolution [μ.IsAddLeftInvariant] [μ.IsNegInvariant] (n : d → ℤ)
    (f : UnitAddTorus d → E) :
    (mFourier n : UnitAddTorus d → ℂ) ⋆[lsmul ℂ ℂ, μ] f =
      fun x ↦ mFourier n x • ∫ t, mFourier (-n) t • f t ∂μ := by
  ext x
  rw [convolution_def, ← integral_smul, ← integral_sub_left_eq_self _ μ x]
  congr 1 with t
  rw [lsmul_apply, sub_sub_cancel, mFourier_apply_sub, smul_smul]

/-- **Convolution with a trigonometric polynomial.** For an invariant measure `μ` on the torus and
an integrable `f`, convolving `f` with the trigonometric polynomial `∑ n ∈ s, c n e_n` multiplies
its Fourier modes by `c n`:
`(∑ n ∈ s, c n e_n) ⋆ f = ∑ n ∈ s, c n e_n • ∫ t, mFourier (-n) t • f t ∂μ`. -/
theorem sum_mul_mFourier_convolution [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) {f : UnitAddTorus d → E} (hf : Integrable f μ) :
    (fun t ↦ ∑ n ∈ s, c n * mFourier n t) ⋆[lsmul ℂ ℂ, μ] f =
      fun x ↦ ∑ n ∈ s, (c n * mFourier n x) • ∫ t, mFourier (-n) t • f t ∂μ := by
  ext x
  rw [convolution_def]
  simp_rw [lsmul_apply, Finset.sum_smul]
  rw [integral_finsetSum _ fun n _ ↦ ?_]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    have h := congr_fun (mFourier_convolution (μ := μ) n f) x
    simp only [convolution_def, lsmul_apply] at h
    simp_rw [mul_smul, integral_smul, h]
  · exact (hf.comp_sub_left x).bdd_smul ‖c n‖
      (by fun_prop : Continuous fun t ↦ c n * mFourier n t).aestronglyMeasurable
      (.of_forall fun t ↦ by simp)

end Fourier

/-! ### Convolution operators on `Lᵖ` -/

variable [Finite d] (μ) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

omit [μ.IsNegInvariant] in
/-- **Young's inequality on the torus.** Convolution with a continuous kernel `k` maps
`Lᵖ(𝕋ᵈ, μ)` to itself, with `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`. -/
theorem memLp_convolution (k : C(UnitAddTorus d, ℂ)) (f : Lp ℂ p μ) :
    MemLp (⇑k ⋆[lsmul ℂ ℂ, μ] (f : UnitAddTorus d → ℂ)) p μ ∧
      eLpNorm (⇑k ⋆[lsmul ℂ ℂ, μ] (f : UnitAddTorus d → ℂ)) p μ ≤
        ENNReal.ofReal (∫ z, ‖k z‖ ∂μ) * eLpNorm f p μ := by
  have hL : ‖lsmul ℂ ℂ (E := ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
  have hk : eLpNorm k 1 μ = ENNReal.ofReal (∫ z, ‖k z‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_eNorm k.continuous.aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_eNorm
      (k.continuous.integrable_of_hasCompactSupport (.of_compactSpace _))]
  have hbound : eLpNorm (⇑k ⋆[lsmul ℂ ℂ, μ] (f : UnitAddTorus d → ℂ)) p μ ≤
      ENNReal.ofReal (∫ z, ‖k z‖ ∂μ) * eLpNorm f p μ :=
    calc _ ≤ ‖lsmul ℂ ℂ (E := ℂ)‖ₑ * eLpNorm k 1 μ * eLpNorm f p μ :=
          eLpNorm_convolution_le _ k.continuous.aestronglyMeasurable
            (Lp.aestronglyMeasurable f) Fact.out
      _ ≤ _ := by
          rw [hk, mul_assoc]
          exact mul_le_of_le_one_left zero_le hL
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)), hbound⟩

/-- **Convolution with a continuous kernel on `Lᵖ(𝕋ᵈ, μ)`**, `1 ≤ p ≤ ∞`, as a bounded operator
of norm at most `‖k‖₁` (`UnitAddTorus.norm_convolutionLp_le`). -/
def convolutionLp (k : C(UnitAddTorus d, ℂ)) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun f := (memLp_convolution μ p k f).1.toLp _
      map_add' f g := by
        have hex (h : Lp ℂ p μ) :=
          (HasCompactSupport.of_compactSpace _).convolutionExists_left (lsmul ℂ ℂ) k.continuous
            ((Lp.memLp h).integrable Fact.out).locallyIntegrable
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (.of_eq ?_)
        rw [convolution_congr _ (.rfl) (Lp.coeFn_add f g)]
        exact (hex f).distrib_add (hex g)
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (.of_eq ?_)
        rw [convolution_congr _ (.rfl) (Lp.coeFn_smul c f)]
        exact convolution_smul }
    (∫ z, ‖k z‖ ∂μ) fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      rw [Lp.norm_def, ← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (by finiteness) (memLp_convolution μ p k f).2

/-- The operator `UnitAddTorus.convolutionLp μ p k` is convolution with `k`. -/
theorem coeFn_convolutionLp (k : C(UnitAddTorus d, ℂ)) (f : Lp ℂ p μ) :
    convolutionLp μ p k f =ᵐ[μ] ⇑k ⋆[lsmul ℂ ℂ, μ] (f : UnitAddTorus d → ℂ) :=
  (memLp_convolution μ p k f).1.coeFn_toLp

/-- Convolution with `k` on `Lᵖ(𝕋ᵈ, μ)` has operator norm at most `‖k‖₁`. -/
theorem norm_convolutionLp_le (k : C(UnitAddTorus d, ℂ)) :
    ‖convolutionLp μ p k‖ ≤ ∫ z, ‖k z‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

end UnitAddTorus
