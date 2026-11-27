/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.VanishingMeanOscillation
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.SeparatedVariables
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Matrix.Contraction.LpNorm
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Interpolation
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.BumpFunction.LpNorm
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp

/-!
# The whole-space `W^{2,p}` estimate with a zero-order shift, for VMO coefficients

Let `a` be a coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants `0 < λ ≤ Λ`,
neither symmetric nor continuous in general, whose operators `a(x)` have vanishing mean
oscillation, and let `2 < p < ∞`. This file proves the whole-space estimate with a zero-order
shift: there is `λ₀ > 0` such that for every `μ ≥ λ₀` every `u ∈ W^{2,p}(ℝ^{n+1})` satisfies

`μ ‖u‖_{Lᵖ} + √μ ‖∇u‖_{Lᵖ} + ‖D²u‖_{Lᵖ} ≤ C ‖∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u‖_{Lᵖ}`,

with `C` depending only on `n`, `p`, `λ` and `Λ`, and `λ₀` depending on `a` through the radius
below which its mean oscillation is small
(`TauCeti.PDE.exists_mul_norm_add_sqrt_mul_norm_add_norm_le_of_sum_mul_inner_sub_mul_eq_of_memVMO`).
The estimate without the shift,
`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO`, keeps `‖u‖` on the
right side; here it is absorbed, so the shifted operator is injective on `W^{2,p}(ℝ^{n+1})` for
`μ ≥ λ₀` (`TauCeti.PDE.exists_forall_eq_zero_of_sum_mul_inner_sub_mul_eq_zero_of_memVMO`). This is
the a priori estimate of Krylov's whole-space theorem for `p > 2`. Solvability of the shifted
equation and the range `1 < p ≤ 2` are not treated here.

## The argument

The estimate for the zero-order term is Agmon's device of an extra variable.

* **The extra variable.** On `ℝ^{n+2} = ℝ × ℝ^{n+1}`, `y = (t, x)`, the coefficient
  `ã(y) = diag(1, a(x))` is uniformly elliptic with constants `min λ 1` and `max Λ 1`, and has
  vanishing mean oscillation (`TauCeti.MemVMO.comp_snd_consEquivL_symm`), so the estimate without
  shift holds for it with some radius `r₀`.
* **Agmon's inequality.** Let `μ = k²`, let `φ` be `C²` with compact support on `ℝ^{n+1}`, let
  `g = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼφ - μ φ`, and let `η(t) = ζ(t) cos(k t + θ)` for a fixed bump function `ζ`.
  Then `v(t, x) = φ(x) η(t)` solves `∑ᵢⱼ ãᵢⱼ ∂ᵢ∂ⱼv = g(x) η(t) + φ(x) (η'' + k² η)(t)`, and
  `η'' + k² η = ζ'' cos - 2 k ζ' sin` involves no factor `k²`. The estimate for `v`, whose
  `Lᵖ` norms factor (`EuclideanSpace.lpNorm_smul_comp_consEquivL_symm`), and the lower bound
  `‖D²v‖ ≥ ‖∂ₜ²v‖ = ‖φ‖ ‖η''‖` give `k² ‖η‖ ‖φ‖ ≤ C (‖ζ‖ ‖g‖ + (1 + k + r₀⁻²) ‖φ‖)` up to
  constants depending on `ζ`.
* **Two phases.** Since `|cos| + |sin| ≥ 1`, the phases `θ = 0` and `θ = -π/2` together carry the
  norm of `ζ`; summing the two inequalities, the terms with `‖φ‖` on the right are absorbed for
  `μ ≥ λ₀`, and `μ ‖φ‖ ≤ 4 C ‖g‖`.
* **Density.** Both sides are continuous on `W^{2,p}(ℝ^{n+1})`, in which the test functions are
  dense, so the bound holds for every `u`.
* **Higher derivatives.** The estimate without shift for `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f + μ u` bounds `‖D²u‖`
  once `μ ≥ r₀⁻²`, and the interpolation inequality with step `1 / √μ` bounds `√μ ‖∇u‖`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.6 and its use of Agmon's idea.
* S. Agmon, *On the eigenfunctions and on the eigenvalues of general elliptic boundary value
  problems*, Comm. Pure Appl. Math. **15** (1962), 119–147 (the extra variable).
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

open EuclideanSpace Matrix

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The coefficient `diag(1, a)` on `ℝ × ℝ^m` -/

section Coefficient

variable {m : ℕ}

/-- The block matrix `diag(1, A)`, with the new coordinate first. -/
private def consOneMatrix (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons 1 0) fun i => Fin.cons 0 (A i))

@[simp] private theorem consOneMatrix_zero_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    consOneMatrix A 0 0 = 1 := by simp [consOneMatrix]

@[simp] private theorem consOneMatrix_zero_succ (A : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    consOneMatrix A 0 j.succ = 0 := by simp [consOneMatrix]

@[simp] private theorem consOneMatrix_succ_zero (A : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    consOneMatrix A i.succ 0 = 0 := by simp [consOneMatrix]

@[simp] private theorem consOneMatrix_succ_succ (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    consOneMatrix A i.succ j.succ = A i j := by simp [consOneMatrix]

/-- The operator `(t, x) ↦ (t, M x)` on `ℝ^{m+1} = ℝ × ℝ^m`. -/
private def consOneCLM (M : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (consEquivL ℝ m : ℝ × EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) ∘L
    ((ContinuousLinearMap.id ℝ ℝ).prodMap M) ∘L
      ((consEquivL ℝ m).symm : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin m))

private theorem consOneCLM_consEquivL (M : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    consOneCLM M (consEquivL ℝ m (t, x)) = consEquivL ℝ m (t, M x) := by
  simp [consOneCLM]

private theorem toEuclideanCLM_consOneMatrix (A : Matrix (Fin m) (Fin m) ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (consOneMatrix A) = consOneCLM (toEuclideanCLM (𝕜 := ℝ) A) := by
  ext y : 1
  obtain ⟨⟨t, x⟩, rfl⟩ := (consEquivL ℝ m).surjective y
  rw [consOneCLM_consEquivL]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ]

private theorem lipschitzWith_consOneCLM :
    LipschitzWith 1 (consOneCLM (m := m)) := by
  refine LipschitzWith.of_dist_le_mul fun M N => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  obtain ⟨⟨t, x⟩, rfl⟩ := (consEquivL ℝ m).surjective y
  rw [sub_apply, consOneCLM_consEquivL, consOneCLM_consEquivL, ← dist_eq_norm]
  have h1 := dist_consEquivL_sq (t, M x) (t, N x)
  have h2 := norm_consEquivL_sq (t, x)
  rw [dist_self, zero_pow two_ne_zero, zero_add] at h1
  have h3 : ‖M x - N x‖ ≤ ‖M - N‖ * ‖x‖ := by
    rw [← sub_apply]; exact ContinuousLinearMap.le_opNorm _ _
  have h4 : ‖x‖ ≤ ‖consEquivL ℝ m (t, x)‖ :=
    le_of_sq_le_sq (by nlinarith [sq_nonneg ‖t‖]) (norm_nonneg _)
  calc dist (consEquivL ℝ m (t, M x)) (consEquivL ℝ m (t, N x)) = ‖M x - N x‖ := by
        rw [← dist_eq_norm, ← sq_eq_sq₀ dist_nonneg dist_nonneg, h1]
    _ ≤ ‖M - N‖ * ‖consEquivL ℝ m (t, x)‖ := h3.trans (by gcongr)

private theorem consOneCLM_mem_ellipticCLMSet {lam Lam : ℝ}
    {M : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hM : M ∈ ellipticCLMSet lam Lam) :
    consOneCLM M ∈ ellipticCLMSet (min lam 1) (max Lam 1) := by
  obtain ⟨hlow, hup⟩ := mem_ellipticCLMSet_iff.1 hM
  refine mem_ellipticCLMSet_iff.2 ⟨fun ξ => ?_, fun η ξ => ?_⟩
  · obtain ⟨⟨t, x⟩, rfl⟩ := (consEquivL ℝ m).surjective ξ
    rw [consOneCLM_consEquivL, inner_consEquivL, norm_consEquivL_sq, real_inner_self_eq_norm_sq]
    have h := hlow x
    have h1 : min lam 1 ≤ lam := min_le_left _ _
    have h2 : min lam 1 ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg ‖t‖, sq_nonneg ‖x‖]
  · obtain ⟨⟨t, x⟩, rfl⟩ := (consEquivL ℝ m).surjective ξ
    obtain ⟨⟨s, z⟩, rfl⟩ := (consEquivL ℝ m).surjective η
    rw [consOneCLM_consEquivL, inner_consEquivL]
    have hzx := hup z x
    -- Cauchy–Schwarz in `ℝ²` for the vectors `(‖s‖, ‖z‖)` and `(‖t‖, ‖x‖)`.
    have hcs : ‖s‖ * ‖t‖ + ‖z‖ * ‖x‖ ≤ ‖consEquivL ℝ m (s, z)‖ * ‖consEquivL ℝ m (t, x)‖ := by
      have h1 := norm_consEquivL_sq (s, z)
      have h2 := norm_consEquivL_sq (t, x)
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      rw [mul_pow, h1, h2]
      nlinarith [sq_nonneg (‖s‖ * ‖x‖ - ‖z‖ * ‖t‖)]
    calc |⟪s, t⟫_ℝ + ⟪z, M x⟫_ℝ| ≤ ‖s‖ * ‖t‖ + Lam * ‖z‖ * ‖x‖ :=
          (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm s t) hzx)
      _ ≤ max Lam 1 * (‖s‖ * ‖t‖ + ‖z‖ * ‖x‖) := by
          have h1 : Lam ≤ max Lam 1 := le_max_left _ _
          have h2 : 1 ≤ max Lam 1 := le_max_right _ _
          nlinarith [mul_nonneg (norm_nonneg s) (norm_nonneg t),
            mul_nonneg (norm_nonneg z) (norm_nonneg x)]
      _ ≤ max Lam 1 * ‖consEquivL ℝ m (s, z)‖ * ‖consEquivL ℝ m (t, x)‖ := by
          rw [mul_assoc]; gcongr

/-- The coefficient field `diag(1, a(x))` on `ℝ^{m+1} = ℝ × ℝ^m`, constant in the new variable. -/
private def extCoeff (a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (y : EuclideanSpace ℝ (Fin (m + 1))) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  consOneMatrix (a ((consEquivL ℝ m).symm y).2)

private theorem uniformlyEllipticOn_extCoeff
    {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn univ a lam Lam) :
    UniformlyEllipticOn univ (extCoeff a) (min lam 1) (max Lam 1) := by
  refine uniformlyEllipticOn_of_forall_toEuclideanCLM_mem (lt_min hell.pos one_pos)
    ((min_le_left _ _).trans (hell.le.trans (le_max_left _ _))) fun y _ => ?_
  rw [extCoeff, toEuclideanCLM_consOneMatrix]
  exact consOneCLM_mem_ellipticCLMSet ((toEuclideanCLM_mem_ellipticCLMSet_iff _).2
    ((uniformlyEllipticOn_iff.1 hell).2.2 (mem_univ _)))

private theorem memVMO_extCoeff {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hvmo : MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume) :
    MemVMO (fun y => toEuclideanCLM (𝕜 := ℝ) (extCoeff a y)) volume := by
  have h := (MemVMO.comp_snd_consEquivL_symm hvmo).comp_lipschitz lipschitzWith_consOneCLM
  refine h.congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, extCoeff, toEuclideanCLM_consOneMatrix]

end Coefficient

/-! ### The extra variable -/

section Tensor

variable {m : ℕ}

/-- The projection `(t, x) ↦ x` of `ℝ^{m+1} = ℝ × ℝ^m` onto the old variables. -/
private abbrev consSndCLM (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ContinuousLinearMap.snd ℝ ℝ _ ∘L (consEquivL ℝ m).symm.toContinuousLinearMap

/-- The projection `(t, x) ↦ t` of `ℝ^{m+1} = ℝ × ℝ^m` onto the new variable. -/
private abbrev consFstCLM (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ _ ∘L (consEquivL ℝ m).symm.toContinuousLinearMap

/-- The second derivative of `y ↦ φ(x) η(t)`, `y = (t, x)`, in the new direction is
`φ(x) η''(t)`. -/
private theorem fderiv_fderiv_tensor_single_zero {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    {η : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hη : ContDiff ℝ 2 η) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    fderiv ℝ (fderiv ℝ fun y => φ ((consEquivL ℝ m).symm y).2 * η ((consEquivL ℝ m).symm y).1) y
        (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) =
      φ ((consEquivL ℝ m).symm y).2 * iteratedDeriv 2 η ((consEquivL ℝ m).symm y).1 := by
  have h := fderiv_fderiv_mul_comp_apply (φ := φ) (η := η) (consSndCLM m) (consFstCLM m) (y := y)
    hφ.contDiffAt hη.contDiffAt (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  simpa using h

/-- The second derivatives of `y ↦ φ(x) η(t)`, `y = (t, x)`, in the old directions are
`η(t) ∂ᵢ∂ⱼφ(x)`. -/
private theorem fderiv_fderiv_tensor_single_succ {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    {η : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hη : ContDiff ℝ 2 η) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (i j : Fin m) :
    fderiv ℝ (fderiv ℝ fun y => φ ((consEquivL ℝ m).symm y).2 * η ((consEquivL ℝ m).symm y).1) y
        (EuclideanSpace.single i.succ 1) (EuclideanSpace.single j.succ 1) =
      η ((consEquivL ℝ m).symm y).1 * fderiv ℝ (fderiv ℝ φ) ((consEquivL ℝ m).symm y).2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have h := fderiv_fderiv_mul_comp_apply (φ := φ) (η := η) (consSndCLM m) (consFstCLM m) (y := y)
    hφ.contDiffAt hη.contDiffAt (EuclideanSpace.single i.succ 1) (EuclideanSpace.single j.succ 1)
  simpa using h

/-- The principal part of `diag(1, a)` applied to `y ↦ φ(x) η(t)` is `(aⁱʲ ∂ᵢ∂ⱼφ)(x) η(t) +
φ(x) η''(t)`. -/
private theorem sum_extCoeff_mul_fderiv_fderiv_tensor
    (a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    {η : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hη : ContDiff ℝ 2 η) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    ∑ i, ∑ j, extCoeff a y i j *
        fderiv ℝ (fderiv ℝ fun y => φ ((consEquivL ℝ m).symm y).2 * η ((consEquivL ℝ m).symm y).1)
          y (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) =
      (∑ i, ∑ j, a ((consEquivL ℝ m).symm y).2 i j *
          fderiv ℝ (fderiv ℝ φ) ((consEquivL ℝ m).symm y).2 (EuclideanSpace.single j 1)
            (EuclideanSpace.single i 1)) * η ((consEquivL ℝ m).symm y).1 +
        φ ((consEquivL ℝ m).symm y).2 * iteratedDeriv 2 η ((consEquivL ℝ m).symm y).1 := by
  simp only [Fin.sum_univ_succ, extCoeff, consOneMatrix_zero_zero, consOneMatrix_zero_succ,
    consOneMatrix_succ_zero, consOneMatrix_succ_succ, zero_mul, Finset.sum_const_zero, add_zero,
    zero_add, one_mul, fderiv_fderiv_tensor_single_zero hφ hη,
    fderiv_fderiv_tensor_single_succ hφ hη, Finset.sum_mul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The tensor product `y ↦ φ(x) η(t)`, `y = (t, x)`, of two `C²` functions with compact support
is a `W^{2,p}` function on `ℝ^{m+1}` whose weak Hessian is its classical one. -/
private theorem exists_wkp_tensor {φ : EuclideanSpace ℝ (Fin m) → ℝ} {η : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    ∃ V : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))) ⊤ p 2,
      (Wkp.value 2 V : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) =ᵐ[volume]
        (fun y => φ ((consEquivL ℝ m).symm y).2 * η ((consEquivL ℝ m).symm y).1) ∧
      ∀ᵐ y, ∀ i j : Fin (m + 1),
        Wkp.iteratedGradient 1 V y (EuclideanSpace.single j 1) i =
          fderiv ℝ (fderiv ℝ fun y => φ ((consEquivL ℝ m).symm y).2 *
            η ((consEquivL ℝ m).symm y).1) y (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) := by
  set v := fun y => φ ((consEquivL ℝ m).symm y).2 * η ((consEquivL ℝ m).symm y).1
  have hv : ContDiff ℝ 2 v :=
    (hφ.comp (consSndCLM m).contDiff).mul (hη.comp (consFstCLM m).contDiff)
  have hvc : HasCompactSupport v := hφc.smul_comp_consEquivL_symm hηc
  obtain ⟨V, hV, -⟩ := Wkp.exists_value_ae_eq_and_norm_le (p := p) (k := 2)
    (mu := (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))) hv fun i hi =>
      (hv.continuous_iteratedFDeriv (by exact_mod_cast hi)).memLp_of_hasCompactSupport
        (hvc.iteratedFDeriv i)
  have hV' : (Wkp.value 2 V : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) =ᵐ[volume.restrict
      ((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) :
        Set (EuclideanSpace ℝ (Fin (m + 1))))] v :=
    hV.filter_mono (Measure.ae_restrict_coe_opens_top _).le
  exact ⟨V, hV, (Wkp.iteratedGradient_one_single_apply_ae_eq_of_contDiffOn V hv.contDiffOn
    hV').filter_mono Measure.ae_le_ae_restrict_coe_opens_top⟩

/-! ### Agmon's inequality -/

/-- The Calderón–Zygmund estimate `‖D²V‖ ≤ C (‖∑ᵢⱼ ãᵢⱼ ∂ᵢ∂ⱼV‖ + r₀⁻² ‖V‖)` on
`W^{2,p}(ℝ^{m+1})` for the coefficient `ã = diag(1, a)`, the hypothesis of Agmon's argument. -/
private def ExtCoeffEstimate (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) (C r₀ : ℝ) : Prop :=
  ∀ (V : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))) ⊤ p 2)
    (F : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).restrict
      (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))))),
    (∀ᵐ y, ∑ i, ∑ j, extCoeff a y i j * ⟪Wkp.iteratedGradient 1 V y
      (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = F y) →
    ‖Wkp.iteratedGradient 1 V‖ ≤ C * (‖F‖ + (r₀ ^ 2)⁻¹ * ‖Wkp.value 2 V‖)

omit [Fact (1 ≤ p)] in
/-- The second derivative of a `C²` function with compact support on `ℝ` is in every `Lᵖ`. -/
private theorem memLp_iteratedDeriv_two {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) : MemLp (iteratedDeriv 2 η) p volume :=
  hη.memLp_iteratedFDeriv_apply_of_hasCompactSupport le_rfl hηc fun _ => 1

omit [Fact (1 ≤ p)] in
/-- Multiplying by `cos (k t + θ)` keeps a function in `Lᵖ` and does not increase its `Lᵖ`
norm. -/
private theorem memLp_mul_cos_and_lpNorm_le {f : ℝ → ℝ} (hf : MemLp f p volume) (k θ : ℝ) :
    MemLp (fun t => f t * Real.cos (k * t + θ)) p volume ∧
      lpNorm (fun t => f t * Real.cos (k * t + θ)) p volume ≤ lpNorm f p volume := by
  simpa only [smul_eq_mul, mul_comm (Real.cos _), one_mul] using
    memLp_smul_and_lpNorm_smul_le_of_ae_le (c := 1) hf
      ((by fun_prop : Continuous fun t => Real.cos (k * t + θ)).aestronglyMeasurable)
      (.of_forall fun t => (Real.norm_eq_abs _).trans_le (Real.abs_cos_le_one _))

/-- **Agmon's inequality for a tensor product.** Suppose the Calderón–Zygmund estimate
`‖D²V‖ ≤ C (‖∑ᵢⱼ ãᵢⱼ ∂ᵢ∂ⱼV‖ + r₀⁻² ‖V‖)` holds on `W^{2,p}(ℝ^{m+1})` for the coefficient
`ã = diag(1, a)`. Let `φ` and `η` be `C²` with compact support and
`g = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼφ - μ φ`. Applied to `y ↦ φ(x) η(t)`, the estimate gives
`‖η''‖ ‖φ‖ ≤ C (‖η‖ ‖g‖ + ‖η'' + μ η‖ ‖φ‖ + r₀⁻² ‖η‖ ‖φ‖)`. -/
private theorem lpNorm_iteratedDeriv_two_mul_lpNorm_le {C r₀ μ : ℝ} (hC : 0 ≤ C)
    {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hest : ExtCoeffEstimate p a C r₀)
    {φ : EuclideanSpace ℝ (Fin m) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : MemLp g p volume)
    (hgeq : ∀ x, g x = ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ φ) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) - μ * φ x) :
    lpNorm (iteratedDeriv 2 η) p volume * lpNorm φ p volume ≤
      C * (lpNorm η p volume * lpNorm g p volume +
        lpNorm (fun t => iteratedDeriv 2 η t + μ * η t) p volume * lpNorm φ p volume +
          (r₀ ^ 2)⁻¹ * (lpNorm η p volume * lpNorm φ p volume)) := by
  obtain ⟨V, hV, hH⟩ := exists_wkp_tensor (p := p) hφ hφc hη hηc
  set ρ := fun t => iteratedDeriv 2 η t + μ * η t
  have hφp : MemLp φ p volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hηp : MemLp η p volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hη2p : MemLp (iteratedDeriv 2 η) p volume := memLp_iteratedDeriv_two hη hηc
  have h1 : MemLp (fun y => g ((consEquivL ℝ m).symm y).2 * η ((consEquivL ℝ m).symm y).1) p
      volume :=
    hg.smul_comp_consEquivL_symm hηp
  have hρp : MemLp ρ p volume := hη2p.add (hηp.const_mul μ)
  have h2 : MemLp (fun y => φ ((consEquivL ℝ m).symm y).2 * ρ ((consEquivL ℝ m).symm y).1) p
      volume :=
    hφp.smul_comp_consEquivL_symm hρp
  have hF := h1.add h2
  rw [← Measure.restrict_coe_opens_top volume] at hF
  have heq : ∀ᵐ y, ∑ i, ∑ j, extCoeff a y i j * ⟪Wkp.iteratedGradient 1 V y
      (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = hF.toLp _ y := by
    filter_upwards [hF.coeFn_toLp.filter_mono Measure.ae_le_ae_restrict_coe_opens_top, hH]
      with y hy hHy
    simp only [hy, EuclideanSpace.inner_single_right, one_mul, conj_trivial, hHy]
    rw [sum_extCoeff_mul_fderiv_fderiv_tensor a hφ hη y]
    simp only [Pi.add_apply, hgeq]
    ring
  have key := hest V _ heq
  have hFn : ‖hF.toLp _‖ ≤ lpNorm η p volume * lpNorm g p volume +
      lpNorm ρ p volume * lpNorm φ p volume := by
    rw [Lp.norm_toLp, ← lpNorm, Measure.restrict_coe_opens_top,
      ← lpNorm_smul_comp_consEquivL_symm hg.aestronglyMeasurable hηp.aestronglyMeasurable,
      ← lpNorm_smul_comp_consEquivL_symm hφp.aestronglyMeasurable hρp.aestronglyMeasurable]
    exact lpNorm_add_le h1 Fact.out
  have hVn : ‖Wkp.value 2 V‖ = lpNorm η p volume * lpNorm φ p volume := by
    rw [Lp.norm_eq_lpNorm_of_ae_eq (hV.filter_mono (Measure.ae_restrict_coe_opens_top _).le),
      Measure.restrict_coe_opens_top]
    exact lpNorm_smul_comp_consEquivL_symm hφp.aestronglyMeasurable hηp.aestronglyMeasurable
  have hDn : lpNorm (iteratedDeriv 2 η) p volume * lpNorm φ p volume ≤
      ‖Wkp.iteratedGradient 1 V‖ := by
    have hae : ∀ᵐ y, ‖φ ((consEquivL ℝ m).symm y).2 * iteratedDeriv 2 η ((consEquivL ℝ m).symm y).1‖
        ≤ 1 * ‖Wkp.iteratedGradient 1 V y‖ := by
      filter_upwards [hH] with y hHy
      rw [← fderiv_fderiv_tensor_single_zero hφ hη, ← hHy, one_mul]
      refine (PiLp.norm_apply_le _ _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
      simp
    have h := lpNorm_le_mul_lpNorm_of_ae_le_mul
      (hφp.smul_comp_consEquivL_symm hη2p).aestronglyMeasurable
      (Lp.memLp_of_restrict_coe_opens_top (Wkp.iteratedGradient 1 V)) hae
    rwa [one_mul, lpNorm_smul_comp_consEquivL_symm hφp.aestronglyMeasurable
      hη2p.aestronglyMeasurable, ← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top] at h
  calc _ ≤ ‖Wkp.iteratedGradient 1 V‖ := hDn
    _ ≤ _ := key
    _ ≤ _ := by rw [hVn]; gcongr

/-! ### The oscillating cutoffs -/

/-- `t ↦ ζ(t) cos(k t + θ)` is `C²` when `ζ` is. -/
private theorem contDiff_mul_cos {ζ : ℝ → ℝ} (hζ : ContDiff ℝ 2 ζ) (k θ : ℝ) :
    ContDiff ℝ 2 fun t => ζ t * Real.cos (k * t + θ) :=
  hζ.mul (Real.contDiff_cos.comp ((contDiff_const.mul contDiff_id).add contDiff_const))

/-- The remainder `η'' + k² η = ζ'' cos(k t + θ) - 2 k ζ' sin(k t + θ)` of
`η(t) = ζ(t) cos(k t + θ)` has `Lᵖ` norm at most `‖ζ''‖ + 2 |k| ‖ζ'‖`. -/
private theorem lpNorm_iteratedDeriv_two_mul_cos_add_le {ζ : ℝ → ℝ} (hζ : ContDiff ℝ 2 ζ)
    (hζc : HasCompactSupport ζ) (k θ : ℝ) :
    lpNorm (fun t => iteratedDeriv 2 (fun t => ζ t * Real.cos (k * t + θ)) t +
        k ^ 2 * (ζ t * Real.cos (k * t + θ))) p volume ≤
      lpNorm (iteratedDeriv 2 ζ) p volume + 2 * |k| * lpNorm (deriv ζ) p volume := by
  have h1 : MemLp (deriv ζ) p volume :=
    (hζ.continuous_deriv one_le_two).memLp_of_hasCompactSupport hζc.deriv
  obtain ⟨hc, hcn⟩ := memLp_mul_cos_and_lpNorm_le (memLp_iteratedDeriv_two (p := p) hζ hζc) k θ
  have hsin : lpNorm (fun t => deriv ζ t * Real.sin (k * t + θ)) p volume ≤
      lpNorm (deriv ζ) p volume := by
    simpa only [smul_eq_mul, mul_comm (Real.sin _), one_mul] using
      (memLp_smul_and_lpNorm_smul_le_of_ae_le (c := 1) h1
        ((by fun_prop : Continuous fun t => Real.sin (k * t + θ)).aestronglyMeasurable)
        (.of_forall fun t => (Real.norm_eq_abs _).trans_le (Real.abs_sin_le_one _))).2
  simp_rw [iteratedDeriv_two_mul_cos hζ, sub_add_cancel]
  calc _ ≤ lpNorm (fun t => iteratedDeriv 2 ζ t * Real.cos (k * t + θ)) p volume +
        lpNorm (fun t => 2 * k * (deriv ζ t * Real.sin (k * t + θ))) p volume :=
        lpNorm_sub_le hc Fact.out
    _ ≤ _ := by
        gcongr
        · rw [show (fun t => 2 * k * (deriv ζ t * Real.sin (k * t + θ))) =
            (2 * k) • fun t => deriv ζ t * Real.sin (k * t + θ) by
              ext t; simp only [Pi.smul_apply, smul_eq_mul], lpNorm_const_smul]
          simp only [nnNorm_mul, Real.nnNorm_ofNat, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnNorm,
            Real.norm_eq_abs]
          gcongr

/-- Since `|cos x| + |sin x| ≥ 1`, the two phases `θ = 0` and `θ = -π/2` of `ζ(t) cos(k t + θ)`
together carry the full `Lᵖ` norm of `ζ`. -/
private theorem lpNorm_le_lpNorm_mul_cos_add_lpNorm_mul_cos {ζ : ℝ → ℝ} (hζ : MemLp ζ p volume)
    (k : ℝ) :
    lpNorm ζ p volume ≤ lpNorm (fun t => ζ t * Real.cos (k * t + 0)) p volume +
      lpNorm (fun t => ζ t * Real.cos (k * t + -(Real.pi / 2))) p volume := by
  have hm (θ : ℝ) := (memLp_mul_cos_and_lpNorm_le hζ k θ).1
  have hsum := (hm 0).norm.add (hm (-(Real.pi / 2))).norm
  have h := lpNorm_le_mul_lpNorm_of_ae_le_mul (c := 1) hζ.aestronglyMeasurable hsum
    (.of_forall fun t => ?_)
  · rw [one_mul] at h
    refine h.trans ((lpNorm_add_le (hm 0).norm Fact.out).trans_eq ?_)
    rw [lpNorm_norm (hm 0).aestronglyMeasurable, lpNorm_norm (hm _).aestronglyMeasurable]
  · rw [one_mul, Pi.add_apply]
    refine le_trans ?_ (Real.le_norm_self _)
    rw [norm_mul, norm_mul, add_zero, ← sub_eq_add_neg, Real.cos_sub_pi_div_two, ← mul_add]
    refine le_mul_of_one_le_right (norm_nonneg _) ?_
    have hc := Real.abs_cos_le_one (k * t)
    have hs := Real.abs_sin_le_one (k * t)
    simp only [Real.norm_eq_abs]
    nlinarith [Real.cos_sq_add_sin_sq (k * t), sq_abs (Real.cos (k * t)),
      sq_abs (Real.sin (k * t)), abs_nonneg (Real.cos (k * t)), abs_nonneg (Real.sin (k * t))]

/-- Agmon's inequality for `η(t) = ζ(t) cos(k t + θ)` and the shift `μ = k²`: with
`R = ‖ζ''‖ + 2 |k| ‖ζ'‖`, `k² ‖η‖ ‖φ‖ ≤ C (‖ζ‖ ‖g‖ + R ‖φ‖ + r₀⁻² ‖ζ‖ ‖φ‖) + R ‖φ‖`. -/
private theorem sq_mul_lpNorm_mul_cos_mul_lpNorm_le {C r₀ k : ℝ} (hC : 0 ≤ C)
    {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hest : ExtCoeffEstimate p a C r₀)
    {ζ : ℝ → ℝ} (hζ : ContDiff ℝ 2 ζ) (hζc : HasCompactSupport ζ)
    {φ : EuclideanSpace ℝ (Fin m) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : MemLp g p volume)
    (hgeq : ∀ x, g x = ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ φ) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) - k ^ 2 * φ x) (θ : ℝ) :
    k ^ 2 * lpNorm (fun t => ζ t * Real.cos (k * t + θ)) p volume * lpNorm φ p volume ≤
      C * (lpNorm ζ p volume * lpNorm g p volume +
        (lpNorm (iteratedDeriv 2 ζ) p volume + 2 * |k| * lpNorm (deriv ζ) p volume) *
          lpNorm φ p volume + (r₀ ^ 2)⁻¹ * (lpNorm ζ p volume * lpNorm φ p volume)) +
        (lpNorm (iteratedDeriv 2 ζ) p volume + 2 * |k| * lpNorm (deriv ζ) p volume) *
          lpNorm φ p volume := by
  have hη := contDiff_mul_cos hζ k θ
  have hηc : HasCompactSupport fun t => ζ t * Real.cos (k * t + θ) := hζc.mul_right
  have hag := lpNorm_iteratedDeriv_two_mul_lpNorm_le hC hest hφ hφc hη hηc hg hgeq
  have hρ := lpNorm_iteratedDeriv_two_mul_cos_add_le (p := p) hζ hζc k θ
  have hζp : MemLp ζ p volume := hζ.continuous.memLp_of_hasCompactSupport hζc
  have hN := (memLp_mul_cos_and_lpNorm_le hζp k θ).2
  have hη2 : MemLp (iteratedDeriv 2 fun t => ζ t * Real.cos (k * t + θ)) p volume :=
    memLp_iteratedDeriv_two hη hηc
  have hlow : k ^ 2 * lpNorm (fun t => ζ t * Real.cos (k * t + θ)) p volume ≤
      lpNorm (iteratedDeriv 2 fun t => ζ t * Real.cos (k * t + θ)) p volume +
        lpNorm (fun t => iteratedDeriv 2 (fun t => ζ t * Real.cos (k * t + θ)) t +
          k ^ 2 * (ζ t * Real.cos (k * t + θ))) p volume := by
    rw [← lpNorm_const_smul_of_nonneg (sq_nonneg k)]
    refine le_of_eq_of_le ?_ ((lpNorm_sub_le (g := iteratedDeriv 2
      fun t => ζ t * Real.cos (k * t + θ)) ?_ Fact.out).trans_eq (add_comm _ _))
    · congr 1
      ext t
      simp
    · exact hη2.add ((hη.continuous.memLp_of_hasCompactSupport hηc).const_mul _)
  have hA := lpNorm_nonneg (f := φ) (p := p) (μ := volume)
  calc _ ≤ (lpNorm (iteratedDeriv 2 fun t => ζ t * Real.cos (k * t + θ)) p volume +
        lpNorm (fun t => iteratedDeriv 2 (fun t => ζ t * Real.cos (k * t + θ)) t +
          k ^ 2 * (ζ t * Real.cos (k * t + θ))) p volume) * lpNorm φ p volume := by gcongr
    _ ≤ _ := by
      rw [add_mul]
      refine add_le_add (hag.trans ?_) (by gcongr)
      have hG := lpNorm_nonneg (f := g) (p := p) (μ := volume)
      gcongr

/-- **The zero-order shift for smooth functions.** If the Calderón–Zygmund estimate holds for
`diag(1, a)` on `W^{2,p}(ℝ^{m+1})` with constants `C` and `r₀`, then there is `λ₀ > 0` such that
every `C²` function `φ` with compact support on `ℝ^m` satisfies `μ ‖φ‖ ≤ 4 C ‖g‖` for
`g = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼφ - μ φ` and every `μ ≥ λ₀`. -/
private theorem exists_mul_lpNorm_le_of_contDiff {C r₀ : ℝ} (hC : 0 ≤ C)
    {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hest : ExtCoeffEstimate p a C r₀) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ μ, lam₀ ≤ μ →
      ∀ {φ : EuclideanSpace ℝ (Fin m) → ℝ}, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {g : EuclideanSpace ℝ (Fin m) → ℝ}, MemLp g p volume →
      (∀ x, g x = ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ φ) x
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) - μ * φ x) →
      μ * lpNorm φ p volume ≤ 4 * C * lpNorm g p volume := by
  set ζ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hζ : ContDiff ℝ 2 ζ := ζ.contDiff
  have hζc : HasCompactSupport ζ := ζ.hasCompactSupport
  set Z := lpNorm ζ p volume
  set Z₁ := lpNorm (deriv ζ) p volume
  set Z₂ := lpNorm (iteratedDeriv 2 ζ) p volume
  have hZ : 0 < Z := ζ.lpNorm_pos (zero_lt_one.trans_le Fact.out).ne' volume
  set K₁ := (2 * (C + 1) * Z₂ + 2 * C * (r₀ ^ 2)⁻¹ * Z) / Z
  set K₂ := 4 * (C + 1) * Z₁ / Z
  refine ⟨max (4 * K₁) ((4 * K₂) ^ 2) + 1, by positivity, fun μ hμ φ hφ hφc g hg hgeq => ?_⟩
  have hμ0 : 0 ≤ μ := le_trans (by positivity) hμ
  set k := Real.sqrt μ
  have hk : k ^ 2 = μ := Real.sq_sqrt hμ0
  have hk0 : 0 ≤ k := Real.sqrt_nonneg μ
  have hgeq' : ∀ x, g x = ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ φ) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) - k ^ 2 * φ x := by
    simpa only [hk] using hgeq
  have h₀ := sq_mul_lpNorm_mul_cos_mul_lpNorm_le hC hest hζ hζc hφ hφc hg hgeq' 0
  have h₁ := sq_mul_lpNorm_mul_cos_mul_lpNorm_le hC hest hζ hζc hφ hφc hg hgeq' (-(Real.pi / 2))
  have hsum := lpNorm_le_lpNorm_mul_cos_add_lpNorm_mul_cos (p := p)
    (ζ.continuous.memLp_of_hasCompactSupport hζc) k
  rw [abs_of_nonneg hk0, hk] at h₀ h₁
  have hA := lpNorm_nonneg (f := φ) (p := p) (μ := volume)
  -- Summing the two phases: `μ ‖ζ‖ ‖φ‖ ≤ 2 C ‖ζ‖ ‖g‖ + ‖ζ‖ (K₁ + K₂ √μ) ‖φ‖`.
  have hmain : μ * Z * lpNorm φ p volume ≤
      2 * C * Z * lpNorm g p volume + Z * (K₁ + K₂ * k) * lpNorm φ p volume := by
    have hK₁ : Z * K₁ = 2 * (C + 1) * Z₂ + 2 * C * (r₀ ^ 2)⁻¹ * Z := mul_div_cancel₀ _ hZ.ne'
    have hK₂ : Z * K₂ = 4 * (C + 1) * Z₁ := mul_div_cancel₀ _ hZ.ne'
    have hsumA := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hA) hμ0
    have e1 : Z * K₁ * lpNorm φ p volume =
        (2 * (C + 1) * Z₂ + 2 * C * (r₀ ^ 2)⁻¹ * Z) * lpNorm φ p volume := by rw [hK₁]
    have e2 : Z * K₂ * k * lpNorm φ p volume = 4 * (C + 1) * Z₁ * k * lpNorm φ p volume := by
      rw [hK₂]
    linarith
  -- The threshold makes `K₁ + K₂ √μ ≤ μ / 2`.
  have hK₁μ : K₁ ≤ μ / 4 := by
    have := (le_max_left _ _).trans (le_of_add_le_of_nonneg_left hμ zero_le_one)
    linarith
  have hK₂μ : K₂ * k ≤ μ / 4 := by
    have h4 : 4 * K₂ ≤ k := (le_abs_self _).trans (Real.abs_le_sqrt
      ((le_max_right _ _).trans (le_of_add_le_of_nonneg_left hμ zero_le_one)))
    nlinarith
  have hfin : μ * Z * lpNorm φ p volume ≤ 4 * C * Z * lpNorm g p volume := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hK₁μ hK₂μ) (mul_nonneg hZ.le hA)]
  have := (mul_le_mul_iff_left₀ hZ).1 (by linarith : μ * lpNorm φ p volume * Z ≤
    4 * C * lpNorm g p volume * Z)
  exact this

/-! ### Density -/

/-- The shifted operator `w ↦ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼw - μ w` with bounded measurable coefficients maps
`W^{2,p}(ℝ^m)` into `Lᵖ`, with norm at most `m² Λ + |μ|`. -/
private theorem memLp_contraction_sub_mul_and_lpNorm_le
    {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ} (ha : AEStronglyMeasurable a volume)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x i j, |a x i j| ≤ Λ) (μ : ℝ)
    (w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin m))) ⊤ p 2) :
    MemLp (fun x => Matrix.contraction (a x) (Wkp.iteratedGradient 1 w x) -
        μ * Wkp.value 2 w x) p volume ∧
      lpNorm (fun x => Matrix.contraction (a x) (Wkp.iteratedGradient 1 w x) -
        μ * Wkp.value 2 w x) p volume ≤ (m ^ 2 * Λ + |μ|) * ‖w‖ := by
  obtain ⟨hc, hcn⟩ := Matrix.memLp_contraction_and_lpNorm_le ha (.of_forall fun x => hΛ x)
    (Lp.memLp_of_restrict_coe_opens_top (Wkp.iteratedGradient 1 w))
  have hv := (Lp.memLp_of_restrict_coe_opens_top (Wkp.value 2 w)).const_mul μ
  refine ⟨hc.sub hv, (lpNorm_sub_le hc Fact.out).trans ?_⟩
  have h1 : lpNorm (Wkp.iteratedGradient 1 w) p volume ≤ ‖w‖ := by
    rw [← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top]; exact Wkp.norm_iteratedGradient_le 1 w
  have h2 : lpNorm (fun x => μ * Wkp.value 2 w x) p volume ≤ |μ| * ‖w‖ := by
    rw [show (fun x => μ * Wkp.value 2 w x) = μ • ⇑(Wkp.value 2 w) by
        ext x; simp only [Pi.smul_apply, smul_eq_mul], lpNorm_const_smul,
      ← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top]
    simpa using mul_le_mul_of_nonneg_left (Wkp.norm_value_le 2 w) (abs_nonneg μ)
  calc _ ≤ m ^ 2 * Λ * ‖w‖ + |μ| * ‖w‖ :=
        add_le_add (hcn.trans (mul_le_mul_of_nonneg_left h1 (by positivity))) h2
    _ = _ := by ring

/-- **Density.** A bound `μ ‖φ‖ ≤ K ‖∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼφ - μ φ‖` for `C²` functions with compact
support extends to all of `W^{2,p}(ℝ^m)`, `p < ∞`, since both sides are continuous there. -/
private theorem mul_norm_value_le_of_forall_contDiff (hp_top : p ≠ ⊤)
    {a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ} (ha : AEStronglyMeasurable a volume)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x i j, |a x i j| ≤ Λ) {μ K : ℝ}
    (hsmooth : ∀ {φ : EuclideanSpace ℝ (Fin m) → ℝ}, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {g : EuclideanSpace ℝ (Fin m) → ℝ}, MemLp g p volume →
      (∀ x, g x = ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ φ) x
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) - μ * φ x) →
      μ * lpNorm φ p volume ≤ K * lpNorm g p volume)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin m))) ⊤ p 2) :
    μ * ‖Wkp.value 2 u‖ ≤ K * lpNorm (fun x => Matrix.contraction (a x)
      (Wkp.iteratedGradient 1 u x) - μ * Wkp.value 2 u x) p volume := by
  set F := fun (w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin m))) ⊤ p 2) x =>
    Matrix.contraction (a x) (Wkp.iteratedGradient 1 w x) - μ * Wkp.value 2 w x
  have hF := memLp_contraction_sub_mul_and_lpNorm_le (p := p) ha hΛ0 hΛ μ
  -- The right side is Lipschitz on `W^{2,p}`, since `F` is linear up to null sets.
  have hlip : ∀ w w', lpNorm (F w) p volume ≤
      lpNorm (F w') p volume + (m ^ 2 * Λ + |μ|) * dist w w' := by
    intro w w'
    have hsub : F w - F w' =ᵐ[volume] F (w - w') := by
      have hD := (Lp.coeFn_sub (Wkp.iteratedGradient 1 w) (Wkp.iteratedGradient 1 w')).filter_mono
        Measure.ae_le_ae_restrict_coe_opens_top
      have hv := (Lp.coeFn_sub (Wkp.value 2 w) (Wkp.value 2 w')).filter_mono
        Measure.ae_le_ae_restrict_coe_opens_top
      filter_upwards [hD, hv] with x hDx hvx
      simp only [F, Pi.sub_apply]
      rw [Wkp.iteratedGradient_sub, Wkp.value_sub, hDx, hvx, Pi.sub_apply, Pi.sub_apply, map_sub]
      ring
    rw [dist_eq_norm]
    exact (lpNorm_le_lpNorm_add_lpNorm_sub' (hF w').1 Fact.out).trans
      (add_le_add_right ((lpNorm_congr_ae hsub).trans_le (hF (w - w')).2) _)
  have hcont : Continuous fun w => lpNorm (F w) p volume :=
    (LipschitzWith.of_le_add_mul' _ hlip).continuous
  refine (Wkp.denseRange_ofTestFunctionₗ_top hp_top 2).induction_on u (isClosed_le ?_
    (continuous_const.mul hcont)) fun ψ => ?_
  · simp only [← Wkp.valueL_apply]
    exact continuous_const.mul (Wkp.valueL 2).continuous.norm
  have hψ : ContDiff ℝ 2 (ψ : EuclideanSpace ℝ (Fin m) → ℝ) := ψ.contDiff.of_le (by simp)
  have hval := Wkp.value_ofTestFunctionₗ_top_ae (mu := volume) (p := p) 2 ψ
  have hH := (Wkp.iteratedGradient_one_single_apply_ae_eq_of_contDiffOn _ hψ.contDiffOn
    (hval.filter_mono (Measure.ae_restrict_coe_opens_top _).le)).filter_mono
      Measure.ae_le_ae_restrict_coe_opens_top
  have hFg : F (Wkp.ofTestFunctionₗ 2 ψ) =ᵐ[volume] fun x => ∑ i, ∑ j, a x i j *
      fderiv ℝ (fderiv ℝ (ψ : EuclideanSpace ℝ (Fin m) → ℝ)) x (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1) - μ * ψ x := by
    filter_upwards [hH, hval] with x hx hv
    simp only [F, Matrix.contraction_apply, EuclideanSpace.inner_single_right, one_mul,
      conj_trivial, hx, hv]
  have hnorm : ‖Wkp.value 2 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 ψ)‖ =
      lpNorm ψ p volume := by
    rw [Lp.norm_eq_lpNorm_of_restrict_coe_opens_top]
    exact lpNorm_congr_ae hval
  rw [hnorm, lpNorm_congr_ae hFg]
  exact hsmooth hψ ψ.hasCompactSupport ((hF _).1.ae_eq hFg) fun x => rfl

end Tensor

/-! ### The estimate on the whole space -/

variable {n : ℕ}

/-- **The zero-order term of the shifted estimate.** For `2 < p < ∞` there is `C`, depending on
`n`, `p`, `λ`, `Λ`, such that for every uniformly elliptic coefficient field `a` of vanishing mean
oscillation there is `λ₀ > 0` with `μ ‖u‖ ≤ C ‖∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u‖` on `W^{2,p}(ℝ^{n+1})` for
every `μ ≥ λ₀`. -/
private theorem exists_mul_norm_value_le_of_memVMO (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))))),
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x = f x) →
        μ * ‖Wkp.value 2 u‖ ≤ 4 * C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO (n := n + 1) hp
    hp_top (min lam 1) (max Lam 1)
  refine ⟨C, fun {a} hvmo hell => ?_⟩
  obtain ⟨r₀, -, hest⟩ := hC (memVMO_extCoeff hvmo) (uniformlyEllipticOn_extCoeff hell)
  obtain ⟨lam₀, hlam₀, hsmooth⟩ := exists_mul_lpNorm_le_of_contDiff C.coe_nonneg hest
  refine ⟨lam₀, hlam₀, fun μ hμ u f heq => ?_⟩
  have ha : AEStronglyMeasurable a volume := Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1
    hvmo.memBMO.locallyIntegrable.aestronglyMeasurable
  have h := mul_norm_value_le_of_forall_contDiff hp_top ha hell.upper_nonneg
    (fun x i j => hell.abs_apply_le (mem_univ x) i j) (hsmooth μ hμ) u
  have hf : (fun x => Matrix.contraction (a x) (Wkp.iteratedGradient 1 u x) -
      μ * Wkp.value 2 u x) =ᵐ[volume] f := by
    filter_upwards [heq] with x hx
    rw [Matrix.contraction_apply, hx]
  rwa [lpNorm_congr_ae hf, ← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top] at h

/-- **Krylov's whole-space `W^{2,p}` estimate with a zero-order shift, for coefficients of
vanishing mean oscillation.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There is a constant `C`, depending
only on `n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a coefficient matrix on
`ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, whose operators `a(x)` have vanishing mean
oscillation. Then there is `λ₀ > 0` such that for every `μ ≥ λ₀`, every `u ∈ W^{2,p}(ℝ^{n+1})`
with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u = f ∈ Lᵖ` almost everywhere satisfies

`μ ‖u‖_{Lᵖ} + √μ ‖∇u‖_{Lᵖ} + ‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`.

The threshold `λ₀` depends on `a` through the radius below which its mean oscillation is small.
Unlike `TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO`, the right side
does not contain `‖u‖`; in particular `u ↦ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u` is injective on `W^{2,p}` for
`μ ≥ λ₀`. -/
theorem exists_mul_norm_add_sqrt_mul_norm_add_norm_le_of_sum_mul_inner_sub_mul_eq_of_memVMO
    (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))))),
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x = f x) →
        μ * ‖Wkp.value 2 u‖ + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C₁, hC₁⟩ := exists_mul_norm_value_le_of_memVMO (n := n) hp hp_top lam Lam
  obtain ⟨C₂, hC₂⟩ := exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO (n := n) hp
    hp_top lam Lam
  refine ⟨4 * C₁ + 2 * C₂ * (1 + 8 * C₁) + 4 * ((n + 1 : ℕ) : ℝ≥0) ^ 2 * C₁,
    fun {a} hvmo hell => ?_⟩
  obtain ⟨lam₁, hlam₁, hval⟩ := hC₁ hvmo hell
  obtain ⟨r₁, -, hest⟩ := hC₂ hvmo hell
  refine ⟨max lam₁ ((r₁ ^ 2)⁻¹), lt_max_of_lt_left hlam₁, fun μ hμ u f heq => ?_⟩
  have hμ0 : 0 < μ := hlam₁.trans_le ((le_max_left _ _).trans hμ)
  have hU := hval μ ((le_max_left _ _).trans hμ) u f heq
  set U := ‖Wkp.value 2 u‖
  set D := ‖Wkp.iteratedGradient 1 u‖
  -- The Hessian: the equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f + μ u` and the estimate without shift.
  have hD : D ≤ C₂ * (1 + 8 * C₁) * ‖f‖ := by
    have heq' : ∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x
        (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = (f + μ • Wkp.value 2 u) x := by
      filter_upwards [heq, (Lp.coeFn_add f (μ • Wkp.value 2 u)).filter_mono
        Measure.ae_le_ae_restrict_coe_opens_top, (Lp.coeFn_smul μ (Wkp.value 2 u)).filter_mono
        Measure.ae_le_ae_restrict_coe_opens_top] with x hx h1 h2
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, ← hx]
      ring
    have hr : (r₁ ^ 2)⁻¹ * U ≤ μ * U :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hμ) (norm_nonneg _)
    have hfU : ‖f + μ • Wkp.value 2 u‖ ≤ ‖f‖ + μ * U := by
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_smul, Real.norm_of_nonneg hμ0.le]
    calc D ≤ C₂ * (‖f + μ • Wkp.value 2 u‖ + (r₁ ^ 2)⁻¹ * U) := hest u _ heq'
      _ ≤ C₂ * (‖f‖ + μ * U + μ * U) := by gcongr
      _ ≤ C₂ * (‖f‖ + 4 * C₁ * ‖f‖ + 4 * C₁ * ‖f‖) := by gcongr
      _ = C₂ * (1 + 8 * C₁) * ‖f‖ := by ring
  -- The gradient, by the interpolation inequality with the step `1 / √μ`.
  have hG : √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ ≤
      D + ((n + 1 : ℕ) : ℝ) ^ 2 * (μ * U) := by
    have hsq : 0 < √μ := Real.sqrt_pos.2 hμ0
    have h := Wkp.norm_iteratedGradient_lowerOrder_le hp_top u (inv_pos.2 hsq)
    rw [finrank_euclideanSpace_fin] at h
    calc √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖
        ≤ √μ * ((√μ)⁻¹ * D + ((n + 1 : ℕ) : ℝ) ^ 2 / (√μ)⁻¹ * U) := by gcongr
      _ = D + ((n + 1 : ℕ) : ℝ) ^ 2 * (√μ * √μ * U) := by field_simp
      _ = _ := by rw [Real.mul_self_sqrt hμ0.le]
  have hU' := mul_le_mul_of_nonneg_left hU (sq_nonneg ((n + 1 : ℕ) : ℝ))
  calc μ * U + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + D
      ≤ μ * U + (D + ((n + 1 : ℕ) : ℝ) ^ 2 * (μ * U)) + D := by gcongr
    _ ≤ 4 * C₁ * ‖f‖ + (C₂ * (1 + 8 * C₁) * ‖f‖ + ((n + 1 : ℕ) : ℝ) ^ 2 * (4 * C₁ * ‖f‖)) +
        C₂ * (1 + 8 * C₁) * ‖f‖ := by gcongr
    _ = _ := by push_cast; ring

/-- **Uniqueness for the shifted equation.** For `2 < p < ∞` and a uniformly elliptic coefficient
field `a` of vanishing mean oscillation on `ℝ^{n+1}`, there is `λ₀ > 0` such that for `μ ≥ λ₀` the
only `u ∈ W^{2,p}(ℝ^{n+1})` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u = 0` almost everywhere is `u = 0`. -/
theorem exists_forall_eq_zero_of_sum_mul_inner_sub_mul_eq_zero_of_memVMO (hp : 2 < p)
    (hp_top : p ≠ ⊤) {lam Lam : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hvmo : MemVMO (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume)
    (hell : UniformlyEllipticOn univ a lam Lam) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x = 0) → u = 0 := by
  obtain ⟨C, hC⟩ :=
    exists_mul_norm_add_sqrt_mul_norm_add_norm_le_of_sum_mul_inner_sub_mul_eq_of_memVMO (n := n)
      hp hp_top lam Lam
  obtain ⟨lam₀, hlam₀, hest⟩ := hC hvmo hell
  refine ⟨lam₀, hlam₀, fun μ hμ u hu => ?_⟩
  have h := hest μ hμ u 0 (by
    filter_upwards [hu, (Lp.coeFn_zero ℝ p _).filter_mono Measure.ae_le_ae_restrict_coe_opens_top]
      with x hx h0
    rw [hx, h0, Pi.zero_apply])
  rw [norm_zero, mul_zero] at h
  have hv : ‖Wkp.value 2 u‖ = 0 := by
    have := mul_nonneg (Real.sqrt_nonneg μ) (norm_nonneg (Wkp.iteratedGradient 0
      (Wkp.lowerOrder 1 u)))
    nlinarith [norm_nonneg (Wkp.value 2 u), norm_nonneg (Wkp.iteratedGradient 1 u),
      hlam₀.trans_le hμ]
  exact Wkp.ext 2 (by rw [norm_eq_zero.1 hv, ← Wkp.valueL_apply, map_zero])

end PDE

end TauCeti
