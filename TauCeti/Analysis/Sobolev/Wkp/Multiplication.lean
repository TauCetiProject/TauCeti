/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Analysis.Sobolev.W1p.Multiplication
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Bounded smooth multiplication in zero-boundary Sobolev spaces

Multiplication by a smooth scalar function whose derivatives through order `k` are bounded
by `M` preserves `W^{k,p}_0(Ω)`, with operator norm at most `2^(k+1) M`. This holds for
`1 ≤ p ≤ ∞` on any open domain, without boundary regularity. The estimate includes every
recorded weak derivative in the iterated graph norm.

The underlying estimate, `TauCeti.Wkp.norm_ofTestFunctionₗ_le_of_eqOn_mul`, needs only that the
multiplied function be a `Cᵏ` representative `f` of some `u ∈ W^{k,p}(Ω)`: a test function equal
to `ψ f` on `Ω` has norm at most `2^(k+1) M ‖u‖`. It controls the error when a smooth
approximation is multiplied by a fixed cutoff. Extending the resulting map on test functions to
their closure gives the zero-boundary operator. This file does not assert multiplication on all
of `W^{k,p}(Ω)`.

## References

L. C. Evans, *Partial Differential Equations*, §5.2.3 and §5.3.2.

Adapted from Tau Ceti contribution
[#12418](https://github.com/TauCetiProject/TauCeti/pull/12418),
*Bound smooth multiplication in higher-order zero-boundary Sobolev spaces*.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem derivative_mul_le (k i : ℕ) (hi : i ≤ k)
    {psi : E → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ j ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ j psi x‖ ≤ M)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f Omega)
    (hu : (Wkp.value k u : E → ℝ) =ᵐ[mu.restrict Omega] f)
    (Phi : 𝓓(Omega, ℝ)) (hPhi : EqOn Phi (fun x => psi x * f x) Omega) :
    lpNorm (iteratedFDeriv ℝ i Phi) p (mu.restrict Omega) ≤ 2 ^ i * M * ‖u‖ := by
  have hmem := Wkp.memLp_iteratedFDeriv_of_contDiffOn k u hf hu
  let a (j : ℕ) : ℝ := (i.choose j : ℝ) * M
  let b (j : ℕ) : E → ℝ := fun x => a j * ‖iteratedFDeriv ℝ (i - j) f x‖
  have hbmem (j : ℕ) : MemLp (b j) p (mu.restrict Omega) :=
    (hmem (i - j) ((Nat.sub_le _ _).trans hi)).norm.const_mul (a j)
  -- Integrate Mathlib's pointwise binomial estimate using the finite-sum triangle inequality.
  -- On the open set `Ω`, the derivatives of `Phi` are those of `psi * f`.
  have hprod : eLpNorm (iteratedFDeriv ℝ i Phi) p (mu.restrict Omega) ≤
      eLpNorm (∑ j ∈ Finset.range (i + 1), b j) p (mu.restrict Omega) := by
    apply eLpNorm_mono_ae
      ((Phi.contDiff.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    have hU : (Omega : Set E) ∈ nhds x := Omega.isOpen.mem_nhds hx
    rw [((hPhi.eventuallyEq_of_mem hU).iteratedFDeriv ℝ i).eq_of_nhds,
      ← iteratedFDerivWithin_of_isOpen i Omega.isOpen hx]
    refine (norm_iteratedFDerivWithin_mul_le ((hpsi.of_le (by simp)).contDiffOn) hf
      Omega.isOpen.uniqueDiffOn hx (n := i) (by exact_mod_cast hi)).trans ?_
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    refine (Finset.sum_le_sum fun j hj => ?_).trans (le_abs_self _)
    rw [iteratedFDerivWithin_of_isOpen j Omega.isOpen hx,
      iteratedFDerivWithin_of_isOpen (i - j) Omega.isOpen hx]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (hbound j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hi) x hx)
        (Nat.cast_nonneg _)) (norm_nonneg _)
  have hsum := memLp_finsetSum' (Finset.range (i + 1)) (fun j _ => hbmem j)
  have hreal := ENNReal.toReal_mono hsum.eLpNorm_ne_top hprod
  calc
    lpNorm (iteratedFDeriv ℝ i Phi) p (mu.restrict Omega)
        ≤ lpNorm (∑ j ∈ Finset.range (i + 1), b j) p (mu.restrict Omega) := by
      simpa only [toReal_eLpNorm] using hreal
    _ ≤ ∑ j ∈ Finset.range (i + 1), lpNorm (b j) p (mu.restrict Omega) :=
      lpNorm_sum_le (fun j _ => hbmem j) Fact.out
    _ = ∑ j ∈ Finset.range (i + 1),
        a j * lpNorm (iteratedFDeriv ℝ (i - j) f) p (mu.restrict Omega) := by
      apply Finset.sum_congr rfl
      intro j _
      have hbj : b j = a j • (fun x => ‖iteratedFDeriv ℝ (i - j) f x‖) := by
        funext x
        simp [b, smul_eq_mul]
      rw [hbj, lpNorm_const_smul,
        lpNorm_norm (hmem (i - j) ((Nat.sub_le _ _).trans hi)).aestronglyMeasurable,
        Real.nnnorm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hM)]
      rfl
    _ ≤ ∑ j ∈ Finset.range (i + 1), a j * ‖u‖ := by
      gcongr with j hj
      exact Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k u hf hu (i - j)
        ((Nat.sub_le _ _).trans hi)
    _ = 2 ^ i * M * ‖u‖ := by
      simp only [a, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

private theorem norm_ofTestFunction_one_le_of_eqOn_mul {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ 1, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (u : Wkp mu Omega p 1) {f : E → ℝ}
    (hu : (Wkp.value 1 u : E → ℝ) =ᵐ[mu.restrict Omega] f)
    (Phi : 𝓓(Omega, ℝ)) (hPhi : EqOn Phi (fun x => psi x * f x) Omega) :
    ‖Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1 Phi‖ ≤ 2 ^ (1 + 1) * M * ‖u‖ := by
  have hval : ∀ x ∈ Omega, |psi x| ≤ M := fun x hx => by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hbound 0 (by omega) x hx
  have hgrad : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M := fun x hx => by
    simpa only [norm_gradient_eq_norm_fderiv, norm_iteratedFDeriv_one] using
      hbound 1 le_rfl x hx
  -- The recursively indexed order-one space and its norm are those of `W1p`.
  let v : W1p mu Omega p := u
  have hv : (W1p.value v : E → ℝ) =ᵐ[mu.restrict Omega] f := by
    simpa only [Wkp.value_one] using hu
  -- At order one the test function `Phi` is the Leibniz product `psi u` of `W1p`.
  have he : W1p.ofTestFunctionₗ mu Omega p Phi = W1p.contDiffSMul psi hpsi hM hval hgrad v := by
    refine W1p.ext_value (Lp.ext ?_)
    rw [W1p.value_ofTestFunctionₗ]
    filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hval hgrad v,
      testFunctionLp_apply_ae (mu := mu) p Phi, hv,
      ae_restrict_mem Omega.isOpen.measurableSet] with x hx hPx hvx hxO
    rw [hPx, hx, hvx, hPhi hxO, smul_eq_mul]
  have h := W1p.norm_contDiffSMul_le hpsi hM hval hgrad v
  rw [← he] at h
  have h' : ‖W1p.ofTestFunctionₗ mu Omega p Phi‖ ≤ 2 ^ (1 + 1) * M * ‖v‖ :=
    h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 2 ^ (1 + 1)) hM)
      (norm_nonneg _))
  simp only [Wkp.ofTestFunctionₗ_one]
  convert h' using 1 <;> rfl

/-- Let `u ∈ W^{k,p}(Ω)` have a representative `f` which is `Cᵏ` on `Ω`. If a test function
`Phi` agrees on `Ω` with the product of `f` and a smooth scalar function whose derivatives through
order `k` are bounded by `M`, then the full `W^{k,p}` norm of `Phi` is at most `2^(k+1) M ‖u‖`. -/
theorem Wkp.norm_ofTestFunctionₗ_le_of_eqOn_mul (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f)
    (Phi : 𝓓(Omega, ℝ)) (hPhi : EqOn Phi (fun x => psi x * f x) Omega) :
    ‖ofTestFunctionₗ (mu := mu) (p := p) k Phi‖ ≤ 2 ^ (k + 1) * M * ‖u‖ := by
  have hPhi_ae (j : ℕ) : (value j (ofTestFunctionₗ (mu := mu) (p := p) j Phi) : E → ℝ)
      =ᵐ[mu.restrict Omega] Phi := by
    rw [value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae p Phi
  -- Orders zero and one use their existing norms; later orders split into the preceding
  -- graph stage and the highest derivative, each controlled by the norm of `u`.
  induction k using Nat.twoStepInduction with
  | zero =>
      have h := derivative_mul_le (mu := mu) (p := p) 0 0 le_rfl hpsi hM hbound u hf hu Phi hPhi
      have he : ‖ofTestFunctionₗ (mu := mu) (p := p) 0 Phi‖ =
          lpNorm (iteratedFDeriv ℝ 0 (Phi : E → ℝ)) p (mu.restrict Omega) := by
        rw [← value_zero (ofTestFunctionₗ (mu := mu) (p := p) 0 Phi), Lp.norm_def, lpNorm]
        congr 1
        refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
          ((Phi.contDiff.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable) ?_
        filter_upwards [hPhi_ae 0] with x hx
        rw [hx, norm_iteratedFDeriv_zero]
      rw [he]
      simp only [pow_zero, one_mul] at h
      simp only [zero_add, pow_one]
      nlinarith [norm_nonneg u]
  | one => exact norm_ofTestFunction_one_le_of_eqOn_mul hpsi hM hbound u hu Phi hPhi
  | more k _ ih =>
      have hlow := ih (fun i hi => hbound i (by omega)) (lowerOrder (k + 1) u)
        (hf.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2)))
        (by simpa only [value_succ] using hu)
      have hhigh : ‖iteratedGradient (k + 1)
          (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi)‖ ≤ 2 ^ (k + 2) * M * ‖u‖ := by
        rw [norm_iteratedGradient_eq_lpNorm_of_contDiffOn (k + 1) _
          (Phi.contDiff.of_le (by simp)).contDiffOn (hPhi_ae (k + 2))]
        exact derivative_mul_le (k + 2) (k + 2) le_rfl hpsi hM hbound u hf hu Phi hPhi
      have hnorm := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k
        (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi)
      rw [lowerOrder_ofTestFunctionₗ] at hnorm
      have hlow' := hlow.trans (mul_le_mul_of_nonneg_left (norm_lowerOrder_le (k + 1) u)
        (by positivity))
      rw [pow_succ (2 : ℝ) (k + 2)]
      nlinarith [norm_nonneg (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi),
        norm_nonneg (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) Phi),
        norm_nonneg (iteratedGradient (k + 1)
          (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi)),
        mul_nonneg (by positivity : 0 ≤ 2 ^ (k + 2) * M) (norm_nonneg u)]

/-- Multiplying a test function by a smooth scalar function with derivatives through order
`k` bounded by `M` increases its full `W^{k,p}` norm by at most `2^(k+1) M`. -/
theorem Wkp.norm_ofTestFunctionₗ_bilinLeftCLM_le (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (phi : 𝓓(Omega, ℝ)) :
    ‖ofTestFunctionₗ (mu := mu) (p := p) k
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi)‖ ≤
      2 ^ (k + 1) * M * ‖ofTestFunctionₗ (mu := mu) (p := p) k phi‖ :=
  norm_ofTestFunctionₗ_le_of_eqOn_mul k hpsi hM hbound _
    (phi.contDiff.of_le (by simp)).contDiffOn
    (by rw [value_ofTestFunctionₗ]; exact testFunctionLp_apply_ae p phi) _
    (fun x _ => by simp [smul_eq_mul, mul_comm])

namespace Wkp0

/-- A continuous linear endomorphism associated to a smooth scalar function on
`W^{k,p}_0(Ω)`. When the derivatives through order `k` are bounded on `Ω`, its action
on test functions is characterized by `contDiffSMulL_apply_ofTestFunction`. -/
def contDiffSMulL (k : ℕ) {psi : E → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) :
    Wkp0 mu Omega p k →L[ℝ] Wkp0 mu Omega p k :=
  ((Wkp0.ofTestFunctionₗ (mu := mu) (p := p) k).comp
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi).toLinearMap).extendOfNorm
      (Wkp0.ofTestFunctionₗ k)

/-- On a test function, zero-boundary smooth multiplication is ordinary pointwise
multiplication. The product remains a test function in the same domain. -/
theorem contDiffSMulL_apply_ofTestFunction (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (phi : 𝓓(Omega, ℝ)) :
    contDiffSMulL (mu := mu) (p := p) k hpsi
      (Wkp0.ofTestFunctionₗ k phi) =
      Wkp0.ofTestFunctionₗ k
        (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi) := by
  exact LinearMap.extendOfNorm_eq (Wkp0.denseRange_ofTestFunctionₗ k)
    ⟨2 ^ (k + 1) * M, fun phi => by
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← Submodule.norm_coe,
        Wkp0.coe_ofTestFunctionₗ] using
          Wkp.norm_ofTestFunctionₗ_bilinLeftCLM_le (mu := mu) (p := p)
            k hpsi hM hbound phi⟩ phi

/-- Smooth multiplication commutes with forgetting the highest weak derivative when the
derivatives through order `k + 1` are bounded on `Ω`. -/
theorem lowerOrderL_contDiffSMulL (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k + 1, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (u : Wkp0 mu Omega p (k + 1)) :
    lowerOrderL k (contDiffSMulL (k + 1) hpsi u) =
      contDiffSMulL k hpsi (lowerOrderL k u) := by
  let T := (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k).comp
    (contDiffSMulL (k + 1) hpsi)
  let S := (contDiffSMulL (mu := mu) (Omega := Omega) (p := p) k hpsi).comp (lowerOrderL k)
  have heq : (T : Wkp0 mu Omega p (k + 1) → Wkp0 mu Omega p k) = S := by
    apply (Wkp0.denseRange_ofTestFunctionₗ (k + 1)).equalizer T.continuous S.continuous
    funext phi
    simp only [T, S, Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [contDiffSMulL_apply_ofTestFunction (k + 1) hpsi hM hbound,
      lowerOrderL_ofTestFunctionₗ, lowerOrderL_ofTestFunctionₗ,
      contDiffSMulL_apply_ofTestFunction k hpsi hM
        (fun i hi x hx => hbound i (hi.trans (Nat.le_succ k)) x hx)]
  exact congrFun heq u

/-- The norm of smooth multiplication on `W^{k,p}_0(Ω)` is bounded explicitly in terms
of the Sobolev order and a common bound on the multiplier's derivatives. -/
theorem norm_contDiffSMulL_le (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M) :
    ‖contDiffSMulL (mu := mu) (Omega := Omega) (p := p) k hpsi‖ ≤ 2 ^ (k + 1) * M :=
  LinearMap.opNorm_extendOfNorm_le (Wkp0.denseRange_ofTestFunctionₗ k) (by positivity)
    (fun phi => by
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← Submodule.norm_coe,
        Wkp0.coe_ofTestFunctionₗ] using
          Wkp.norm_ofTestFunctionₗ_bilinLeftCLM_le (mu := mu) (p := p)
            k hpsi hM hbound phi)

/-- Smooth multiplication is the unique continuous linear endomorphism of `W^{k,p}_0(Ω)`
with its stated action on test functions. -/
theorem contDiffSMulL_unique (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (T : Wkp0 mu Omega p k →L[ℝ] Wkp0 mu Omega p k)
    (hT : ∀ phi : 𝓓(Omega, ℝ),
      T (Wkp0.ofTestFunctionₗ k phi) =
        Wkp0.ofTestFunctionₗ k
          (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi)) :
    contDiffSMulL k hpsi = T := by
  apply DFunLike.coe_injective
  apply (Wkp0.denseRange_ofTestFunctionₗ k).equalizer (contDiffSMulL k hpsi).continuous
    T.continuous
  funext phi
  exact (contDiffSMulL_apply_ofTestFunction k hpsi hM hbound phi).trans (hT phi).symm

/-- The value of zero-boundary smooth multiplication is represented almost everywhere by
the pointwise product, at every order and including the infinite exponent. -/
theorem value_contDiffSMulL_ae (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (u : Wkp0 mu Omega p k) :
    ∀ᵐ x ∂mu.restrict Omega,
      Wkp.value k (contDiffSMulL k hpsi u : Wkp mu Omega p k) x =
        psi x * Wkp.value k (u : Wkp mu Omega p k) x := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (Wkp0.denseRange_ofTestFunctionₗ k u)
  choose phi hphi using hv
  let T := contDiffSMulL (mu := mu) (Omega := Omega) (p := p) k hpsi
  let V := (Wkp.valueL (mu := mu) (p := p) k).comp
    (wkp0Submodule mu Omega p k).toSubmodule.subtypeL
  have hinput := V.continuous.tendsto u |>.comp hlim
  have houtput := (V.comp T).continuous.tendsto u |>.comp hlim
  -- Two subsequence extractions give simultaneous a.e. limits for inputs and outputs.
  obtain ⟨ns, hns, hin⟩ := (tendstoInMeasure_of_tendsto_Lp hinput).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hout⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (houtput.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hterm : ∀ᵐ x ∂mu.restrict Omega, ∀ j, V (T (v j)) x = psi x * V (v j) x := by
    rw [ae_all_iff]
    intro j
    rw [← hphi j]
    have he := contDiffSMulL_apply_ofTestFunction (mu := mu) (p := p) k hpsi hM hbound (phi j)
    have he' : T (Wkp0.ofTestFunctionₗ k (phi j)) = Wkp0.ofTestFunctionₗ k
        (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi (phi j)) := he
    rw [he']
    filter_upwards [testFunctionLp_apply_ae (mu := mu) p (phi j),
      testFunctionLp_apply_ae (mu := mu) p
        (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi (phi j))]
      with x hx hy
    simp only [V, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Wkp0.coe_ofTestFunctionₗ, Wkp.valueL_apply,
      Wkp.value_ofTestFunctionₗ, hx, hy, TestFunction.bilinLeftCLM_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  filter_upwards [hin, hout, hterm] with x hx hy ht
  have hproduct := (tendsto_const_nhds (x := psi x)).mul (hx.comp hms.tendsto_atTop)
  have houtput' : Tendsto (fun j => V (T (v (ns (ms j)))) x) atTop
      (nhds (psi x * V u x)) := by
    simpa only [Function.comp_def, ht] using hproduct
  have heq := tendsto_nhds_unique hy houtput'
  simpa only [V, T, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Wkp.valueL_apply] using heq

end Wkp0

end TauCeti
