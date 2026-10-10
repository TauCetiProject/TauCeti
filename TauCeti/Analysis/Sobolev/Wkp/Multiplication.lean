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

The test-function estimate controls the error when a smooth approximation is multiplied by a
fixed cutoff. Extending that map to the closure of test functions gives the zero-boundary
operator. This file does not assert multiplication on all of `W^{k,p}(Ω)`.

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
    (phi : 𝓓(Omega, ℝ)) :
    lpNorm (iteratedFDeriv ℝ i (fun x => phi x * psi x)) p (mu.restrict Omega) ≤
      2 ^ i * M * ‖Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi‖ := by
  let u := Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi
  have hu : (Wkp.value k u : E → ℝ) =ᵐ[mu.restrict Omega] (phi : E → ℝ) := by
    rw [Wkp.value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae p phi
  have hmem := Wkp.memLp_iteratedFDeriv_of_contDiffOn k u
    (phi.contDiff.of_le (by simp)).contDiffOn hu
  let a (j : ℕ) : ℝ := (i.choose j : ℝ) * M
  let b (j : ℕ) : E → ℝ := fun x => a j * ‖iteratedFDeriv ℝ (i - j) (phi : E → ℝ) x‖
  have hbmem (j : ℕ) : MemLp (b j) p (mu.restrict Omega) :=
    (hmem (i - j) ((Nat.sub_le _ _).trans hi)).norm.const_mul (a j)
  -- Integrate Mathlib's pointwise binomial estimate using the finite-sum triangle inequality.
  have hprod : eLpNorm (iteratedFDeriv ℝ i (fun x => phi x * psi x)) p
      (mu.restrict Omega) ≤ eLpNorm (∑ j ∈ Finset.range (i + 1), b j) p
        (mu.restrict Omega) := by
    apply eLpNorm_mono_ae
      (((phi.contDiff.mul hpsi).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    have heq : (fun y => phi y * psi y) = (fun y => psi y * phi y) := by
      funext y
      exact mul_comm _ _
    rw [heq]
    refine (norm_iteratedFDeriv_mul_le hpsi phi.contDiff x (by simp)).trans ?_
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    refine (Finset.sum_le_sum fun j hj => ?_).trans (le_abs_self _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (hbound j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hi) x hx)
        (Nat.cast_nonneg _)) (norm_nonneg _)
  have hsum := memLp_finsetSum' (Finset.range (i + 1)) (fun j _ => hbmem j)
  have hreal := ENNReal.toReal_mono hsum.eLpNorm_ne_top hprod
  calc
    lpNorm (iteratedFDeriv ℝ i (fun x => phi x * psi x)) p (mu.restrict Omega)
        ≤ lpNorm (∑ j ∈ Finset.range (i + 1), b j) p (mu.restrict Omega) := by
      simpa only [toReal_eLpNorm] using hreal
    _ ≤ ∑ j ∈ Finset.range (i + 1), lpNorm (b j) p (mu.restrict Omega) :=
      lpNorm_sum_le (fun j _ => hbmem j) Fact.out
    _ = ∑ j ∈ Finset.range (i + 1),
        a j * lpNorm (iteratedFDeriv ℝ (i - j) (phi : E → ℝ)) p (mu.restrict Omega) := by
      apply Finset.sum_congr rfl
      intro j _
      have hbj : b j = a j • (fun x => ‖iteratedFDeriv ℝ (i - j) (phi : E → ℝ) x‖) := by
        funext x
        simp [b, smul_eq_mul]
      rw [hbj, lpNorm_const_smul,
        lpNorm_norm (hmem (i - j) ((Nat.sub_le _ _).trans hi)).aestronglyMeasurable,
        Real.nnnorm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hM)]
      rfl
    _ ≤ ∑ j ∈ Finset.range (i + 1), a j * ‖u‖ := by
      gcongr with j hj
      exact Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k u
        (phi.contDiff.of_le (by simp)).contDiffOn hu (i - j) ((Nat.sub_le _ _).trans hi)
    _ = 2 ^ i * M * ‖u‖ := by
      simp only [a, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

private theorem norm_ofTestFunction_one_mul_le {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ 1, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (phi : 𝓓(Omega, ℝ)) :
    ‖Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi)‖ ≤
      2 ^ (1 + 1) * M * ‖Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1 phi‖ := by
  let Phi := TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi
  have hPhi : (Phi : E → ℝ) = fun x => phi x * psi x := by
    simp [Phi, smul_eq_mul]
  have hval : ∀ x ∈ Omega, |psi x| ≤ M := fun x hx => by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hbound 0 (by omega) x hx
  have hgrad : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M := fun x hx => by
    simpa only [norm_gradient_eq_norm_fderiv, norm_iteratedFDeriv_one] using
      hbound 1 le_rfl x hx
  have he := W1p.contDiffSMul_ofTestFunctionₗ (mu := mu) (p := p) hpsi hM hval hgrad phi Phi (by
    funext x
    simp [hPhi, mul_comm])
  have h := W1p.norm_contDiffSMul_le hpsi hM hval hgrad
    (W1p.ofTestFunctionₗ mu Omega p phi)
  rw [he] at h
  have h' : ‖W1p.ofTestFunctionₗ mu Omega p Phi‖ ≤
      2 ^ (1 + 1) * M * ‖W1p.ofTestFunctionₗ mu Omega p phi‖ :=
    h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 2 ^ (1 + 1)) hM)
      (norm_nonneg _))
  -- The recursively indexed order-one norm is the existing `W1p` norm.
  simp only [Wkp.ofTestFunctionₗ_one]
  convert h' using 1 <;> rfl

/-- Multiplying a test function by a smooth scalar function with derivatives through order
`k` bounded by `M` increases its full `W^{k,p}` norm by at most `2^(k+1) M`. -/
theorem Wkp.norm_ofTestFunctionₗ_bilinLeftCLM_le (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (phi : 𝓓(Omega, ℝ)) :
    ‖ofTestFunctionₗ (mu := mu) (p := p) k
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi)‖ ≤
      2 ^ (k + 1) * M * ‖ofTestFunctionₗ (mu := mu) (p := p) k phi‖ := by
  let Phi := TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi
  have hPhi : (Phi : E → ℝ) = fun x => phi x * psi x := by
    simp [Phi, smul_eq_mul]
  -- Orders zero and one use their existing norms; later orders split into the preceding
  -- graph stage and the highest derivative, each controlled by the input graph norm.
  induction k using Nat.twoStepInduction with
  | zero =>
      have h := derivative_mul_le (mu := mu) (p := p) 0 0 le_rfl hpsi hM hbound phi
      have he : ‖ofTestFunctionₗ (mu := mu) (p := p) 0 Phi‖ =
          lpNorm (iteratedFDeriv ℝ 0 (Phi : E → ℝ)) p (mu.restrict Omega) := by
        rw [← value_zero (ofTestFunctionₗ (mu := mu) (p := p) 0 Phi),
          value_ofTestFunctionₗ, Lp.norm_def, lpNorm]
        congr 1
        refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
          ((Phi.contDiff.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable) ?_
        filter_upwards [testFunctionLp_apply_ae (mu := mu) p Phi] with x hx
        rw [hx, norm_iteratedFDeriv_zero]
      rw [he, hPhi]
      simp only [pow_zero, one_mul] at h
      simp only [zero_add, pow_one]
      nlinarith [norm_nonneg (ofTestFunctionₗ (mu := mu) (p := p) 0 phi)]
  | one => exact norm_ofTestFunction_one_mul_le hpsi hM hbound phi
  | more k _ ih =>
      have hlow := ih (fun i hi => hbound i (by omega))
      have hhigh : ‖iteratedGradient (k + 1)
          (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi)‖ ≤
          2 ^ (k + 2) * M * ‖ofTestFunctionₗ (mu := mu) (p := p) (k + 2) phi‖ := by
        rw [norm_iteratedGradient_eq_lpNorm_of_contDiffOn (k + 1) _
          (Phi.contDiff.of_le (by simp)).contDiffOn (by
            rw [value_ofTestFunctionₗ]
            exact testFunctionLp_apply_ae p Phi), hPhi]
        exact derivative_mul_le (k + 2) (k + 2) le_rfl hpsi hM hbound phi
      have hnorm := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k
        (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi)
      rw [lowerOrder_ofTestFunctionₗ] at hnorm
      have hcontrol := norm_lowerOrder_le (k + 1)
        (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) phi)
      rw [lowerOrder_ofTestFunctionₗ] at hcontrol
      have hlow' := hlow.trans (mul_le_mul_of_nonneg_left hcontrol (by positivity))
      rw [pow_succ (2 : ℝ) (k + 2)]
      nlinarith [norm_nonneg (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi),
        norm_nonneg (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) Phi),
        norm_nonneg (iteratedGradient (k + 1)
          (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) Phi)),
        mul_nonneg (by positivity : 0 ≤ 2 ^ (k + 2) * M)
          (norm_nonneg (ofTestFunctionₗ (mu := mu) (p := p) (k + 2) phi))]

namespace Wkp0

/-- Multiplication by a smooth scalar function with derivatives through order `k` bounded
by `M`, as a continuous linear endomorphism of `W^{k,p}_0(Ω)`. -/
def contDiffSMulL (k : ℕ) {psi : E → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    {M : ℝ} (_hM : 0 ≤ M)
    (_hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M) :
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
    contDiffSMulL (mu := mu) (p := p) k hpsi hM hbound
      (Wkp0.ofTestFunctionₗ k phi) =
      Wkp0.ofTestFunctionₗ k
        (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hpsi phi) := by
  exact LinearMap.extendOfNorm_eq (Wkp0.denseRange_ofTestFunctionₗ k)
    ⟨2 ^ (k + 1) * M, fun phi => by
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← Submodule.norm_coe,
        Wkp0.coe_ofTestFunctionₗ] using
          Wkp.norm_ofTestFunctionₗ_bilinLeftCLM_le (mu := mu) (p := p)
            k hpsi hM hbound phi⟩ phi

/-- Smooth multiplication commutes with forgetting the highest weak derivative. The
lower-order multiplier uses the same smooth function and the restricted derivative bound. -/
theorem lowerOrderL_contDiffSMulL (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k + 1, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M)
    (u : Wkp0 mu Omega p (k + 1)) :
    lowerOrderL k (contDiffSMulL (k + 1) hpsi hM hbound u) =
      contDiffSMulL k hpsi hM
        (fun i hi x hx => hbound i (hi.trans (Nat.le_succ k)) x hx) (lowerOrderL k u) := by
  let T := (lowerOrderL (mu := mu) (p := p) k).comp
    (contDiffSMulL (k + 1) hpsi hM hbound)
  let S := (contDiffSMulL (mu := mu) (p := p) k hpsi hM
    (fun i hi x hx => hbound i (hi.trans (Nat.le_succ k)) x hx)).comp (lowerOrderL k)
  have heq : (T : Wkp0 mu Omega p (k + 1) → Wkp0 mu Omega p k) = S := by
    apply (Wkp0.denseRange_ofTestFunctionₗ (k + 1)).equalizer T.continuous S.continuous
    funext phi
    simp only [T, S, Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [contDiffSMulL_apply_ofTestFunction, lowerOrderL_ofTestFunctionₗ,
      lowerOrderL_ofTestFunctionₗ, contDiffSMulL_apply_ofTestFunction]
  exact congrFun heq u

/-- The norm of smooth multiplication on `W^{k,p}_0(Ω)` is bounded explicitly in terms
of the Sobolev order and a common bound on the multiplier's derivatives. -/
theorem norm_contDiffSMulL_le (k : ℕ) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ k, ∀ x ∈ Omega, ‖iteratedFDeriv ℝ i psi x‖ ≤ M) :
    ‖contDiffSMulL (mu := mu) (p := p) k hpsi hM hbound‖ ≤ 2 ^ (k + 1) * M :=
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
    contDiffSMulL k hpsi hM hbound = T := by
  apply DFunLike.coe_injective
  apply (Wkp0.denseRange_ofTestFunctionₗ k).equalizer (contDiffSMulL k hpsi hM hbound).continuous
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
      Wkp.value k (contDiffSMulL k hpsi hM hbound u : Wkp mu Omega p k) x =
        psi x * Wkp.value k (u : Wkp mu Omega p k) x := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (Wkp0.denseRange_ofTestFunctionₗ k u)
  choose phi hphi using hv
  let T := contDiffSMulL (mu := mu) (p := p) k hpsi hM hbound
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
