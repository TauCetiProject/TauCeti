/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.Decay
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# Smooth functions on the torus and the convergence of their Fourier series

A function `f` on the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` is smooth when its lift
`x ↦ f (fun i ↦ (x i : UnitAddCircle))` to `d → ℝ` is `C^∞`. These functions form the complex
subspace `TauCeti.UnitAddTorus.smoothFunctions d`, whose topology is given by the `C^N` norms: the
suprema of the derivatives of order at most `N` of the lift. Instead of these suprema, this file
uses the predicate `TauCeti.UnitAddTorus.DerivBound N M f`, which says that `M` bounds those
derivatives. Continuity of a linear map `T` from smooth functions to a normed space is expressed
by a bound: there are `C` and `N` with `‖T f‖ ≤ C * M` whenever `DerivBound N M f`.

The Fourier coefficients of a smooth function decay faster than every power of `‖n‖`, while the
derivatives of order `j` of the Fourier monomial `mFourier n` are bounded by
`(2π (card d) ‖n‖) ^ j`. Hence the Fourier series of a smooth function converges to it in every
`C^N` norm. Applying a continuous linear map `T` termwise, `T f` is the sum of the values of `T`
on the monomials, weighted by the Fourier coefficients of `f`; in particular `T` is determined by
these values. These expansions are the input to the Fourier-series proof of the Schwartz kernel
theorem.

Conversely, a trigonometric series `∑ n, c n • mFourier n` whose coefficients decrease rapidly
converges in every `C^N` norm, so it is a smooth function, with Fourier coefficients `c`.

## Main definitions

* `TauCeti.UnitAddTorus.smoothFunctions d`: the smooth functions on `UnitAddTorus d`.
* `TauCeti.UnitAddTorus.DerivBound N M f`: `M` bounds the derivatives of order at most `N` of the
  lift of `f`.
* `TauCeti.UnitAddTorus.mFourierSmooth n`: the Fourier monomial `mFourier n` as a smooth function.
* `TauCeti.UnitAddTorus.mFourierCoeffₗ n`: the `n`-th Fourier coefficient as a linear form on
  smooth functions.
* `UnitAddTorus.lineDeriv f w`: the derivative of a function `f` on `UnitAddTorus d` in the
  direction `w : d → ℝ`.

## Main results

* `TauCeti.UnitAddTorus.exists_derivBound`: a smooth function satisfies a `C^N` bound for every
  `N`.
* `TauCeti.UnitAddTorus.DerivBound.add`, `TauCeti.UnitAddTorus.DerivBound.sub` and
  `TauCeti.UnitAddTorus.DerivBound.const_smul`: the `C^N` bounds of sums and scalar multiples.
* `TauCeti.UnitAddTorus.norm_iteratedFDeriv_mFourier_le` and
  `TauCeti.UnitAddTorus.derivBound_mFourier`: the derivative bounds for the Fourier monomials.
* `TauCeti.UnitAddTorus.one_add_norm_pow_mul_norm_mFourierCoeff_le`: the decay estimate
  `(1 + ‖n‖) ^ k * ‖mFourierCoeff f n‖ ≤ 2 ^ (k + 1) * M` under the bound `DerivBound k M f`.
* `TauCeti.UnitAddTorus.summable_norm_mFourierCoeff_mul_pow`: the coefficients of a smooth
  function remain summable after multiplication by any polynomial weight `(1 + R ‖n‖) ^ N`.
* `TauCeti.UnitAddTorus.eventually_derivBound_sub_sum`: the Fourier series of a smooth function
  converges to it in every `C^N` norm.
* `TauCeti.UnitAddTorus.eq_of_mFourierCoeff_eq`: a smooth function is determined by its Fourier
  coefficients.
* `TauCeti.UnitAddTorus.tsum_smul_mFourier_mem_smoothFunctions` and
  `TauCeti.UnitAddTorus.tsum_smul_mFourier_mem_smoothFunctions_of_bounded`: a trigonometric series
  with rapidly decreasing coefficients is a smooth function.
* `LinearMap.hasSum_mFourierCoeff_smul_apply`: a continuous linear map applied to a
  smooth function `f` is the sum of its values on the Fourier monomials, weighted by the Fourier
  coefficients of `f`.
* `TauCeti.UnitAddTorus.linearMap_eq_of_apply_mFourierSmooth_eq`: two continuous linear maps that
  agree on the Fourier monomials are equal.
* `UnitAddTorus.lineDeriv_mem_smoothFunctions` and `UnitAddTorus.mFourierCoeff_lineDeriv`: the
  directional derivatives of a smooth function are smooth, with Fourier coefficients multiplied by
  `2πi ∑ i, n i * w i`.

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 3.2 (Fourier series of smooth functions on the torus).
-/

public section

noncomputable section

open Complex Filter Topology
open scoped Real ContDiff

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

/-! ### Smooth functions and bounds for their derivatives -/

/-- The smooth functions on the torus `UnitAddTorus d`: those whose lift to `d → ℝ` is `C^∞`. -/
def smoothFunctions (d : Type*) [Fintype d] : Submodule ℂ (UnitAddTorus d → ℂ) where
  carrier := {f | ContDiff ℝ ∞ fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)}
  add_mem' {_ _} hf hg := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    exact hf.add hg
  zero_mem' := by
    simpa only [Set.mem_ofPred_eq, Pi.zero_apply] using
      (contDiff_const : ContDiff ℝ ∞ fun _ : d → ℝ ↦ (0 : ℂ))
  smul_mem' c _ hf := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *
    exact hf.const_smul c

theorem mem_smoothFunctions {f : UnitAddTorus d → ℂ} :
    f ∈ smoothFunctions d ↔ ContDiff ℝ ∞ fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle) := by
  simp [smoothFunctions]

/-- A smooth function on the torus is continuous. -/
theorem continuous_of_mem_smoothFunctions {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d) :
    Continuous f :=
  isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2 (mem_smoothFunctions.1 hf).continuous

/-- A smooth function on the torus is integrable. -/
theorem integrable_of_mem_smoothFunctions {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d) :
    MeasureTheory.Integrable f :=
  (continuous_of_mem_smoothFunctions hf).integrable_of_hasCompactSupport (.of_compactSpace _)

/-- `DerivBound N M f` states that `M` bounds the derivatives of order at most `N` of the lift
`x ↦ f (fun i ↦ (x i : UnitAddCircle))` of `f` to `d → ℝ`. For a smooth function `f`, the least
such `M` is the `C^N` norm of `f`. -/
def DerivBound (N : ℕ) (M : ℝ) (f : UnitAddTorus d → ℂ) : Prop :=
  ∀ j ≤ N, ∀ x : d → ℝ,
    ‖iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M

theorem derivBound_iff {N : ℕ} {M : ℝ} {f : UnitAddTorus d → ℂ} :
    DerivBound N M f ↔ ∀ j ≤ N, ∀ x : d → ℝ,
      ‖iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M :=
  Iff.rfl

theorem DerivBound.norm_iteratedFDeriv_le {N : ℕ} {M : ℝ} {f : UnitAddTorus d → ℂ}
    (h : DerivBound N M f) {j : ℕ} (hj : j ≤ N) (x : d → ℝ) :
    ‖iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M :=
  h j hj x

theorem DerivBound.mono {N : ℕ} {M M' : ℝ} {f : UnitAddTorus d → ℂ} (h : DerivBound N M f)
    (hM : M ≤ M') : DerivBound N M' f :=
  fun j hj x ↦ (h j hj x).trans hM

/-- A bound for the derivatives of order at most `N` bounds those of smaller order. -/
theorem DerivBound.of_le {N N' : ℕ} {M : ℝ} {f : UnitAddTorus d → ℂ} (h : DerivBound N M f)
    (hN : N' ≤ N) : DerivBound N' M f :=
  fun j hj x ↦ h j (hj.trans hN) x

theorem DerivBound.neg {N : ℕ} {M : ℝ} {f : UnitAddTorus d → ℂ} (h : DerivBound N M f) :
    DerivBound N M (-f) := fun j hj x ↦ by
  have : (fun x : d → ℝ ↦ (-f) fun i ↦ (x i : UnitAddCircle)) =
      -fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle) := rfl
  rw [this, iteratedFDeriv_neg_apply, norm_neg]
  exact h j hj x

theorem DerivBound.add {N : ℕ} {M₁ M₂ : ℝ} {f g : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ N fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    (hg : ContDiff ℝ N fun x : d → ℝ ↦ g fun i ↦ (x i : UnitAddCircle))
    (h₁ : DerivBound N M₁ f) (h₂ : DerivBound N M₂ g) : DerivBound N (M₁ + M₂) (f + g) :=
  fun j hj x ↦ by
    have : (fun x : d → ℝ ↦ (f + g) fun i ↦ (x i : UnitAddCircle)) =
        (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) +
          fun x : d → ℝ ↦ g fun i ↦ (x i : UnitAddCircle) := rfl
    rw [this, iteratedFDeriv_add_apply ((hf.of_le (mod_cast hj)).contDiffAt)
      ((hg.of_le (mod_cast hj)).contDiffAt)]
    exact (norm_add_le _ _).trans (add_le_add (h₁ j hj x) (h₂ j hj x))

theorem DerivBound.sub {N : ℕ} {M₁ M₂ : ℝ} {f g : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ N fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    (hg : ContDiff ℝ N fun x : d → ℝ ↦ g fun i ↦ (x i : UnitAddCircle))
    (h₁ : DerivBound N M₁ f) (h₂ : DerivBound N M₂ g) : DerivBound N (M₁ + M₂) (f - g) := by
  rw [sub_eq_add_neg]
  exact h₁.add hf (by simpa using hg.neg) h₂.neg

theorem DerivBound.const_smul {N : ℕ} {M : ℝ} {f : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ N fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) (h : DerivBound N M f)
    (c : ℂ) : DerivBound N (‖c‖ * M) (c • f) := fun j hj x ↦ by
  have : (fun x : d → ℝ ↦ (c • f) fun i ↦ (x i : UnitAddCircle)) =
      c • fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle) := rfl
  rw [this, iteratedFDeriv_const_smul_apply ((hf.of_le (mod_cast hj)).contDiffAt), norm_smul]
  exact mul_le_mul_of_nonneg_left (h j hj x) (norm_nonneg c)

theorem DerivBound.nonneg {N : ℕ} {M : ℝ} {f : UnitAddTorus d → ℂ} (h : DerivBound N M f) :
    0 ≤ M :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le _) 0)

theorem derivBound_zero (N : ℕ) : DerivBound N 0 (0 : UnitAddTorus d → ℂ) := fun j _ x ↦ by
  simp

/-- A smooth function on the torus satisfies a `C^N` bound for every `N`. -/
theorem exists_derivBound {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d) (N : ℕ) :
    ∃ M, DerivBound N M f := by
  choose M hM using fun j : ℕ ↦ exists_forall_norm_iteratedFDeriv_le f
    ((mem_smoothFunctions.1 hf).continuous_iteratedFDeriv (mod_cast le_top))
  refine ⟨∑ j ∈ Finset.range (N + 1), |M j|, fun j hj x ↦ (hM j x).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (fun i _ ↦ abs_nonneg (M i))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))

/-! ### The Fourier monomials -/

/-- The linear form `x ↦ 2πi ∑ i, n i * x i`, whose exponential is the lift of `mFourier n`. -/
private def phase (n : d → ℤ) : (d → ℝ) →L[ℝ] ℂ :=
  ∑ i, (2 * π * I * n i) • (ofRealCLM ∘L ContinuousLinearMap.proj i)

private theorem phase_apply (n : d → ℤ) (x : d → ℝ) :
    phase n x = 2 * π * I * ∑ i, (n i : ℂ) * x i := by
  simp only [phase, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply, ofRealCLM_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem lift_mFourier (n : d → ℤ) :
    (fun x : d → ℝ ↦ mFourier n fun i ↦ (x i : UnitAddCircle)) = cexp ∘ phase n :=
  funext fun x ↦ by rw [mFourier_coe_apply, Function.comp_apply, phase_apply]

private theorem norm_phase_le (n : d → ℤ) : ‖phase n‖ ≤ 2 * π * Fintype.card d * ‖n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  rw [phase_apply, norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  calc 2 * π * ‖∑ i, (n i : ℂ) * x i‖ ≤ 2 * π * ∑ _i : d, ‖n‖ * ‖x‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        rw [norm_mul, Complex.norm_intCast, Complex.norm_real, ← Int.norm_eq_abs]
        exact mul_le_mul (norm_le_pi_norm n i) (norm_le_pi_norm x i) (norm_nonneg _)
          (norm_nonneg _)
    _ = 2 * π * Fintype.card d * ‖n‖ * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem mFourier_mem_smoothFunctions (n : d → ℤ) : ⇑(mFourier n) ∈ smoothFunctions d := by
  rw [mem_smoothFunctions, lift_mFourier]
  exact Complex.contDiff_exp.comp (phase n).contDiff

/-- The Fourier monomial `mFourier n` as a smooth function on the torus. -/
def mFourierSmooth (n : d → ℤ) : smoothFunctions d :=
  ⟨mFourier n, mFourier_mem_smoothFunctions n⟩

@[simp]
theorem coe_mFourierSmooth (n : d → ℤ) :
    ((mFourierSmooth n : smoothFunctions d) : UnitAddTorus d → ℂ) = mFourier n :=
  (rfl)

/-- The derivatives of order `j` of the lift of the Fourier monomial `mFourier n` are bounded by
`(2π (card d) ‖n‖) ^ j`, where `‖n‖` is the sup norm of `n : d → ℤ`. -/
theorem norm_iteratedFDeriv_mFourier_le (n : d → ℤ) (j : ℕ) (x : d → ℝ) :
    ‖iteratedFDeriv ℝ j (fun x : d → ℝ ↦ mFourier n fun i ↦ (x i : UnitAddCircle)) x‖ ≤
      (2 * π * Fintype.card d * ‖n‖) ^ j := by
  have h1 : ‖cexp (phase n x)‖ = 1 := by
    rw [← Function.comp_apply (f := cexp), ← lift_mFourier]
    exact norm_mFourier_apply n _
  rw [lift_mFourier, (phase n).iteratedFDeriv_comp_right (Complex.contDiff_exp (n := j)) x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_real_cexp, h1, one_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_phase_le n) j

/-- The Fourier monomial `mFourier n` satisfies the `C^N` bound `(1 + 2π (card d) ‖n‖) ^ N`. -/
theorem derivBound_mFourier (n : d → ℤ) (N : ℕ) :
    DerivBound N ((1 + 2 * π * Fintype.card d * ‖n‖) ^ N) (mFourier n) := fun j hj x ↦
  (norm_iteratedFDeriv_mFourier_le n j x).trans <|
    (pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_left zero_le_one) j).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hj)

/-! ### Rapid decay of the Fourier coefficients -/

/-- **Rapid decay of the Fourier coefficients.** If the lift of `f` is `C^k` and
`DerivBound k M f`, then `(1 + ‖n‖) ^ k * ‖mFourierCoeff f n‖ ≤ 2 ^ (k + 1) * M`. -/
theorem one_add_norm_pow_mul_norm_mFourierCoeff_le {f : UnitAddTorus d → ℂ} {k : ℕ}
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) {M : ℝ}
    (hM : DerivBound k M f) (n : d → ℤ) :
    (1 + ‖n‖) ^ k * ‖mFourierCoeff f n‖ ≤ 2 ^ (k + 1) * M := by
  have h0 : ‖mFourierCoeff f n‖ ≤ M := norm_mFourierCoeff_le (fun z ↦ by
    obtain ⟨x, rfl⟩ := surjective_coe z
    simpa [norm_iteratedFDeriv_zero] using hM 0 (Nat.zero_le _) x) n
  have hk : ‖n‖ ^ k * ‖mFourierCoeff f n‖ ≤ M := by
    refine le_trans ?_ (pow_mul_norm_mFourierCoeff_le hf (hM k le_rfl) n)
    gcongr
    nlinarith [mul_nonneg (by linarith [Real.two_le_pi] : (0 : ℝ) ≤ 2 * π - 1) (norm_nonneg n)]
  have hpow : (1 + ‖n‖) ^ k ≤ 2 ^ k * (1 + ‖n‖ ^ k) := by
    calc (1 + ‖n‖) ^ k ≤ 2 ^ (k - 1) * (1 ^ k + ‖n‖ ^ k) := add_pow_le zero_le_one (norm_nonneg n) k
      _ ≤ 2 ^ k * (1 + ‖n‖ ^ k) := by
          rw [one_pow]
          gcongr
          exacts [one_le_two, Nat.sub_le k 1]
  calc (1 + ‖n‖) ^ k * ‖mFourierCoeff f n‖
      ≤ 2 ^ k * (1 + ‖n‖ ^ k) * ‖mFourierCoeff f n‖ := by gcongr
    _ = 2 ^ k * (‖mFourierCoeff f n‖ + ‖n‖ ^ k * ‖mFourierCoeff f n‖) := by ring
    _ ≤ 2 ^ k * (M + M) := by gcongr
    _ = 2 ^ (k + 1) * M := by ring

/-- A summable form of the decay estimate: if the lift of `f` is `C^(N + card d + 1)` and
`DerivBound (N + card d + 1) M f`, then `(1 + ‖n‖) ^ N * ‖mFourierCoeff f n‖` is bounded by
`2 ^ (N + card d + 2) * M` times the summable weight `(1 + ‖n‖) ^ (-(card d + 1))`. -/
theorem one_add_norm_pow_mul_norm_mFourierCoeff_le_mul_inv {f : UnitAddTorus d → ℂ} {N : ℕ}
    (hf : ContDiff ℝ (N + Fintype.card d + 1) fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    {M : ℝ} (hM : DerivBound (N + Fintype.card d + 1) M f) (n : d → ℤ) :
    (1 + ‖n‖) ^ N * ‖mFourierCoeff f n‖ ≤
      2 ^ (N + Fintype.card d + 2) * M * ((1 + ‖n‖) ^ (Fintype.card d + 1))⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h := one_add_norm_pow_mul_norm_mFourierCoeff_le (mod_cast hf) hM n
  calc (1 + ‖n‖) ^ N * ‖mFourierCoeff f n‖ * (1 + ‖n‖) ^ (Fintype.card d + 1)
      = (1 + ‖n‖) ^ (N + Fintype.card d + 1) * ‖mFourierCoeff f n‖ := by ring
    _ ≤ 2 ^ (N + Fintype.card d + 1 + 1) * M := h
    _ = 2 ^ (N + Fintype.card d + 2) * M := by ring

/-- The Fourier coefficients of a smooth function remain absolutely summable after
multiplication by the polynomial weight `(1 + R ‖n‖) ^ N`, for every `R ≥ 0` and `N`. -/
theorem summable_norm_mFourierCoeff_mul_pow {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d)
    {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    Summable fun n ↦ ‖mFourierCoeff f n‖ * (1 + R * ‖n‖) ^ N := by
  obtain ⟨M, hM⟩ := exists_derivBound hf (N + Fintype.card d + 1)
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (summable_pi_int_inv_one_add_norm_pow.mul_left
      ((1 + R) ^ N * (2 ^ (N + Fintype.card d + 2) * M)))
  have h1 : (1 + R * ‖n‖) ^ N ≤ (1 + R) ^ N * (1 + ‖n‖) ^ N := by
    rw [← mul_pow]
    gcongr
    nlinarith [norm_nonneg n]
  have h2 := one_add_norm_pow_mul_norm_mFourierCoeff_le_mul_inv
    ((mem_smoothFunctions.1 hf).of_le (mod_cast le_top)) hM n
  calc ‖mFourierCoeff f n‖ * (1 + R * ‖n‖) ^ N
      ≤ ‖mFourierCoeff f n‖ * ((1 + R) ^ N * (1 + ‖n‖) ^ N) := by gcongr
    _ = (1 + R) ^ N * ((1 + ‖n‖) ^ N * ‖mFourierCoeff f n‖) := by ring
    _ ≤ (1 + R) ^ N * (2 ^ (N + Fintype.card d + 2) * M *
          ((1 + ‖n‖) ^ (Fintype.card d + 1))⁻¹) := by gcongr
    _ = _ := by ring

/-! ### Convergence of Fourier series in the `C^N` norms -/

/-- **Convergence of Fourier series in the `C^N` norms.** For a smooth function `f` on the torus,
every `N` and every `ε > 0`, the remainders `f - ∑ n ∈ s, mFourierCoeff f n • mFourier n` of the
Fourier series of `f` eventually satisfy the `C^N` bound `ε` as the finite set `s` grows. -/
theorem eventually_derivBound_sub_sum {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : Finset (d → ℤ) in atTop,
      DerivBound N ε (f - ∑ n ∈ s, mFourierCoeff f n • ⇑(mFourier n)) := by
  set A : ℝ := 2 * π * Fintype.card d with hAdef
  have hA : 0 ≤ A := by positivity
  set w : (d → ℤ) → ℝ := fun n ↦ ‖mFourierCoeff f n‖ * (1 + A * ‖n‖) ^ N with hwdef
  have hw : Summable w := summable_norm_mFourierCoeff_mul_pow hf hA N
  -- The weight `w n` dominates the bounds for the derivatives of the `n`-th term.
  have hvw (k : ℕ) (hk : k ≤ N) (n : d → ℤ) : ‖mFourierCoeff f n‖ * (A * ‖n‖) ^ k ≤ w n := by
    have h1 : 1 ≤ 1 + A * ‖n‖ := le_add_of_nonneg_right (by positivity)
    rw [hwdef]
    exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity)
      (le_add_of_nonneg_left zero_le_one) k).trans (pow_le_pow_right₀ h1 hk)) (norm_nonneg _)
  have hsum : Summable fun n ↦ mFourierCoeff f n :=
    Summable.of_norm_bounded hw fun n ↦ by simpa using hvw 0 (Nat.zero_le _) n
  -- The Fourier series converges pointwise.
  have hpt (z : UnitAddTorus d) : HasSum (fun n ↦ mFourierCoeff f n • mFourier n z) (f z) :=
    hasSum_mFourier_series_apply_of_summable
      (f := ⟨f, continuous_of_mem_smoothFunctions hf⟩) hsum z
  -- The derivatives of the `n`-th term of the lifted series.
  have hterm (k : ℕ) (n : d → ℤ) (y : d → ℝ) : ‖iteratedFDeriv ℝ k (fun y : d → ℝ ↦
      mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle)) y‖ ≤
        ‖mFourierCoeff f n‖ * (A * ‖n‖) ^ k := by
    rw [iteratedFDeriv_const_smul_apply' (((mem_smoothFunctions.1
      (mFourier_mem_smoothFunctions n)).of_le (mod_cast le_top)).contDiffAt), norm_smul, hAdef]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mFourier_le n k y) (norm_nonneg _)
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero w)).2 ε hε] with s hs j hj x
  -- The lift of the remainder is the tail of the Fourier series.
  have hlift : (fun y : d → ℝ ↦ (f - ∑ n ∈ s, mFourierCoeff f n • ⇑(mFourier n))
      fun i ↦ (y i : UnitAddCircle)) =
      fun y ↦ ∑' n : {n // n ∉ s},
        mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle) := by
    funext y
    rw [Pi.sub_apply, Finset.sum_apply, ← (hpt (fun i ↦ (y i : UnitAddCircle))).tsum_eq,
      ← (hpt (fun i ↦ (y i : UnitAddCircle))).summable.sum_add_tsum_subtype_compl s]
    simp only [Pi.smul_apply, add_sub_cancel_left]
  have hcd (n : {n // n ∉ s}) : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) fun y : d → ℝ ↦
      mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle) :=
    ((mem_smoothFunctions.1 (mFourier_mem_smoothFunctions (n : d → ℤ))).const_smul
      (mFourierCoeff f n)).of_le (WithTop.coe_le_coe.2 le_top)
  have hv (k : ℕ) (hk : (k : ℕ∞) ≤ N) :
      Summable fun n : {n // n ∉ s} ↦ ‖mFourierCoeff f n‖ * (A * ‖(n : d → ℤ)‖) ^ k :=
    (hw.subtype _).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ hvw k (by exact_mod_cast hk) n
  have hD := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := N)
    (f := fun (n : {n // n ∉ s}) (y : d → ℝ) ↦
      mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle))
    (v := fun k (n : {n // n ∉ s}) ↦ ‖mFourierCoeff f n‖ * (A * ‖(n : d → ℤ)‖) ^ k)
    hcd hv (fun k n y _ ↦ hterm k n y) (k := j) (by exact_mod_cast hj) x
  rw [hlift, hD]
  have hws : HasSum (fun n : {n // n ∉ s} ↦ w n) (∑' n : {n // n ∉ s}, w n) :=
    (hw.subtype (· ∉ s)).hasSum
  refine (tsum_of_norm_bounded hws fun n ↦ ?_).trans hs.le
  exact (hterm j n x).trans (hvw j hj n)

/-- **Expansion of a continuous linear map in Fourier modes.** Let `T` be a linear map on the
smooth functions on the torus which is continuous for the `C^N` norm: `‖T u‖ ≤ C * M` whenever
`DerivBound N M u`. Then for every smooth `f`, `T f` is the sum of the values `T (mFourier n)`,
weighted by the Fourier coefficients of `f`. -/
theorem _root_.LinearMap.hasSum_mFourierCoeff_smul_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (T : smoothFunctions d →ₗ[ℂ] F) {C : ℝ} {N : ℕ}
    (hT : ∀ (u : smoothFunctions d) M, DerivBound N M (u : UnitAddTorus d → ℂ) → ‖T u‖ ≤ C * M)
    (f : smoothFunctions d) :
    HasSum (fun n ↦ mFourierCoeff (f : UnitAddTorus d → ℂ) n • T (mFourierSmooth n)) (T f) := by
  unfold HasSum
  rw [SummationFilter.unconditional_filter, Metric.tendsto_nhds]
  intro δ hδ
  have hε : 0 < δ / (|C| + 1) := by positivity
  filter_upwards [eventually_derivBound_sub_sum f.2 N hε] with s hs
  have hT' := hT (f - ∑ n ∈ s, mFourierCoeff (f : UnitAddTorus d → ℂ) n • mFourierSmooth n) _
    (by simpa using hs)
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  simp only [map_sub, map_sum, map_smul] at hT'
  calc _ ≤ C * (δ / (|C| + 1)) := hT'
    _ ≤ |C| * (δ / (|C| + 1)) := by gcongr; exact le_abs_self C
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]

/-- **Uniqueness of continuous linear maps.** Two linear maps on the smooth functions on the torus,
each continuous for some `C^N` norm, are equal as soon as they agree on the Fourier monomials. -/
theorem linearMap_eq_of_apply_mFourierSmooth_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {T T' : smoothFunctions d →ₗ[ℂ] F}
    (hT : ∃ (C : ℝ) (N : ℕ), ∀ (u : smoothFunctions d) M,
      DerivBound N M (u : UnitAddTorus d → ℂ) → ‖T u‖ ≤ C * M)
    (hT' : ∃ (C : ℝ) (N : ℕ), ∀ (u : smoothFunctions d) M,
      DerivBound N M (u : UnitAddTorus d → ℂ) → ‖T' u‖ ≤ C * M)
    (h : ∀ n, T (mFourierSmooth n) = T' (mFourierSmooth n)) : T = T' := by
  obtain ⟨C, N, hT⟩ := hT
  obtain ⟨C', N', hT'⟩ := hT'
  ext f
  refine (T.hasSum_mFourierCoeff_smul_apply hT f).unique ?_
  simpa only [h] using T'.hasSum_mFourierCoeff_smul_apply hT' f

/-! ### Fourier coefficients determine smooth functions -/

/-- The Fourier series of a smooth function on the torus converges to it pointwise. -/
theorem hasSum_mFourierCoeff_smul_mFourier {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) :
    HasSum (fun n ↦ mFourierCoeff f n • ⇑(mFourier n)) f := by
  have hsum : Summable fun n ↦ mFourierCoeff f n :=
    Summable.of_norm <| by simpa using summable_norm_mFourierCoeff_mul_pow hf le_rfl 0
  exact Pi.hasSum.2 (hasSum_mFourier_series_apply_of_summable
    (f := ⟨f, continuous_of_mem_smoothFunctions hf⟩) hsum)

/-- Two smooth functions on the torus with the same Fourier coefficients are equal. -/
theorem eq_of_mFourierCoeff_eq {f g : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d)
    (hg : g ∈ smoothFunctions d) (h : ∀ n, mFourierCoeff f n = mFourierCoeff g n) : f = g :=
  (hasSum_mFourierCoeff_smul_mFourier hf).unique <| by
    simpa only [h] using hasSum_mFourierCoeff_smul_mFourier hg

/-! ### Smooth functions from rapidly decreasing coefficients -/

/-- **Rapidly decreasing coefficients give a smooth function.** If `‖c n‖ * ‖n‖ ^ k` is summable
for every `k`, then the trigonometric series `∑ n, c n • mFourier n` is a smooth function on the
torus. -/
theorem tsum_smul_mFourier_mem_smoothFunctions {c : (d → ℤ) → ℂ}
    (hc : ∀ k : ℕ, Summable fun n ↦ ‖c n‖ * ‖n‖ ^ k) :
    (fun z ↦ ∑' n, c n • mFourier n z) ∈ smoothFunctions d := by
  rw [mem_smoothFunctions]
  refine contDiff_tsum (fun n ↦ (contDiff_mFourier_coe n).const_smul (c n))
    (v := fun k n ↦ ‖c n‖ * (2 * π * Fintype.card d * ‖n‖) ^ k) (fun k _ ↦ ?_)
    fun k n x _ ↦ ?_
  · exact ((hc k).mul_left ((2 * π * Fintype.card d) ^ k)).congr fun n ↦ by ring
  · rw [iteratedFDeriv_const_smul_apply' ((contDiff_mFourier_coe n).contDiffAt.of_le
      (mod_cast le_top)), norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mFourier_le n k x) (norm_nonneg _)

/-- **Rapidly decreasing coefficients give a smooth function**, under the classical hypothesis
that `‖n‖ ^ k * ‖c n‖` is bounded for every `k`. -/
theorem tsum_smul_mFourier_mem_smoothFunctions_of_bounded {c : (d → ℤ) → ℂ}
    (hc : ∀ k : ℕ, ∃ C, ∀ n, ‖n‖ ^ k * ‖c n‖ ≤ C) :
    (fun z ↦ ∑' n, c n • mFourier n z) ∈ smoothFunctions d := by
  refine tsum_smul_mFourier_mem_smoothFunctions fun k ↦ ?_
  set K := k + Fintype.card d + 1
  obtain ⟨C₀, hC₀⟩ := hc 0
  obtain ⟨C, hC⟩ := hc K
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (summable_pi_int_inv_one_add_norm_pow.mul_left (2 ^ K * (C₀ + C)))
  have hpow : (1 + ‖n‖) ^ K ≤ 2 ^ K * (1 + ‖n‖ ^ K) := by
    calc (1 + ‖n‖) ^ K ≤ 2 ^ (K - 1) * (1 ^ K + ‖n‖ ^ K) := add_pow_le zero_le_one (norm_nonneg n) K
      _ ≤ 2 ^ K * (1 + ‖n‖ ^ K) := by
          rw [one_pow]
          gcongr
          exacts [one_le_two, Nat.sub_le K 1]
  have h0 := hC₀ n
  rw [pow_zero, one_mul] at h0
  have hK : (1 + ‖n‖) ^ K * ‖c n‖ ≤ 2 ^ K * (C₀ + C) :=
    calc (1 + ‖n‖) ^ K * ‖c n‖ ≤ 2 ^ K * (1 + ‖n‖ ^ K) * ‖c n‖ := by gcongr
      _ = 2 ^ K * (‖c n‖ + ‖n‖ ^ K * ‖c n‖) := by ring
      _ ≤ 2 ^ K * (C₀ + C) := by gcongr; exact hC n
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖c n‖ * ‖n‖ ^ k * (1 + ‖n‖) ^ (Fintype.card d + 1)
      ≤ ‖c n‖ * (1 + ‖n‖) ^ k * (1 + ‖n‖) ^ (Fintype.card d + 1) := by
        gcongr; linarith [norm_nonneg n]
    _ = (1 + ‖n‖) ^ K * ‖c n‖ := by ring
    _ ≤ 2 ^ K * (C₀ + C) := hK

/-! ### Fourier coefficients as linear forms -/

/-- The `n`-th Fourier coefficient as a complex-linear form on the smooth functions. -/
def mFourierCoeffₗ (n : d → ℤ) : smoothFunctions d →ₗ[ℂ] ℂ where
  toFun f := mFourierCoeff (f : UnitAddTorus d → ℂ) n
  map_add' f g := mFourierCoeff_add (integrable_of_mem_smoothFunctions f.2)
    (integrable_of_mem_smoothFunctions g.2) n
  map_smul' c _ := mFourierCoeff_smul c _ n

@[simp]
theorem mFourierCoeffₗ_apply (n : d → ℤ) (f : smoothFunctions d) :
    mFourierCoeffₗ n f = mFourierCoeff (f : UnitAddTorus d → ℂ) n :=
  (rfl)

/-- The constant function `1 = mFourier 0` has mean `1`. -/
theorem mFourierCoeffₗ_zero_mFourierSmooth_zero :
    mFourierCoeffₗ (0 : d → ℤ) (mFourierSmooth 0) = 1 := by
  classical
  simp [mFourierCoeff_mFourier]

/-- The constant function `1 = mFourier 0` is a nonzero smooth function. -/
theorem mFourierSmooth_zero_ne_zero : mFourierSmooth (0 : d → ℤ) ≠ 0 := fun h ↦ by
  have := congrArg (fun f : smoothFunctions d ↦ (f : UnitAddTorus d → ℂ) 0) h
  simp [mFourier_zero] at this

end TauCeti.UnitAddTorus

namespace UnitAddTorus

open TauCeti.UnitAddTorus

variable {d : Type*} [Fintype d]

/-! ### Directional derivatives on the torus -/

/-- The derivative of a function `f` on the torus `UnitAddTorus d` in the direction `w : d → ℝ`:
its value at `z` is the derivative at `0` of `t ↦ f (z + t w)`. -/
def lineDeriv (f : UnitAddTorus d → ℂ) (w : d → ℝ) : UnitAddTorus d → ℂ :=
  fun z ↦ deriv (fun t : ℝ ↦ f (z + fun i ↦ ((t * w i : ℝ) : UnitAddCircle))) 0

omit [Fintype d] in
/-- Along the line through the image of `x`, a function on the torus is its lift along the line
through `x`. -/
private theorem comp_line_eq (f : UnitAddTorus d → ℂ) (x w : d → ℝ) :
    (fun t : ℝ ↦ f ((fun i ↦ (x i : UnitAddCircle)) + fun i ↦ ((t * w i : ℝ) : UnitAddCircle))) =
      fun t ↦ (fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle)) (x + t • w) := by
  funext t
  congr 1

omit [Fintype d] in
/-- At the image of `x`, the directional derivative of `f` is the derivative of its lift. -/
theorem lineDeriv_coe [Finite d] {f : UnitAddTorus d → ℂ} (x w : d → ℝ)
    (hf : DifferentiableAt ℝ (fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle)) x) :
    lineDeriv f w (fun i ↦ (x i : UnitAddCircle)) =
      fderiv ℝ (fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle)) x w := by
  have := Fintype.ofFinite d
  rw [lineDeriv, comp_line_eq]
  exact hf.lineDeriv_eq_fderiv (v := w)

omit [Fintype d] in
/-- The directional derivatives of a constant function vanish. -/
@[simp]
theorem lineDeriv_const (c : ℂ) (w : d → ℝ) : lineDeriv (fun _ : UnitAddTorus d ↦ c) w = 0 := by
  funext z
  simp [lineDeriv]

/-- For a smooth function, `t ↦ f (z + t w)` has derivative `lineDeriv f w z` at `0`. -/
theorem hasDerivAt_lineDeriv {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d)
    (w : d → ℝ) {z : UnitAddTorus d} :
    HasDerivAt (fun t : ℝ ↦ f (z + fun i ↦ ((t * w i : ℝ) : UnitAddCircle))) (lineDeriv f w z)
      0 := by
  obtain ⟨x, rfl⟩ := surjective_coe z
  refine DifferentiableAt.hasDerivAt ?_
  rw [comp_line_eq]
  exact DifferentiableAt.comp (g := fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle))
    (f := fun t : ℝ ↦ x + t • w) (0 : ℝ)
    ((mem_smoothFunctions.1 hf).differentiable (by simp) _) (by fun_prop)

/-- The directional derivatives of a smooth function are smooth. -/
theorem lineDeriv_mem_smoothFunctions {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d)
    (w : d → ℝ) : lineDeriv f w ∈ smoothFunctions d := by
  have hF := mem_smoothFunctions.1 hf
  rw [mem_smoothFunctions]
  have h : (fun x : d → ℝ ↦ lineDeriv f w (fun i ↦ (x i : UnitAddCircle))) =
      fun x ↦ fderiv ℝ (fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle)) x w :=
    funext fun x ↦ lineDeriv_coe x w (hF.differentiable (by simp) x)
  rw [h]
  exact (contDiff_infty_iff_fderiv.1 hF).2.clm_apply contDiff_const

/-- **Fourier coefficients of a directional derivative.** The derivative of a smooth function in
the direction `w` multiplies its `n`-th Fourier coefficient by `2πi ∑ i, n i * w i`. -/
theorem mFourierCoeff_lineDeriv {f : UnitAddTorus d → ℂ} (hf : f ∈ smoothFunctions d)
    (w : d → ℝ) (n : d → ℤ) :
    mFourierCoeff (lineDeriv f w) n =
      (2 * π * I * ∑ i, (n i : ℂ) * w i) * mFourierCoeff f n :=
  mFourierCoeff_eq_smul_of_hasDerivAt (continuous_of_mem_smoothFunctions hf)
    (continuous_of_mem_smoothFunctions (lineDeriv_mem_smoothFunctions hf w))
    (fun _ ↦ hasDerivAt_lineDeriv hf w) n

end UnitAddTorus
