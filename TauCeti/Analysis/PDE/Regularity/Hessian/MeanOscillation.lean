/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average

/-!
# Mean oscillation of the Hessian for constant-coefficient equations

Let `A` be a constant coefficient matrix, uniformly elliptic with constants `0 < λ ≤ Λ`, and let
`u ∈ W^{2,2}(Ω)` be a strong solution of

`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on a ball `B_r = ball x₀ r ⊆ Ω ⊆ ℝ^{n+1}`.

Then `f ∈ L²(B_r)`, and this file proves that the square mean oscillation
`ψ(t) = ∫_{B_t} ‖D²u - (D²u)_{B_t}‖²` of the weak Hessian decays from `B_r` to `B_ρ` like that of a
solution of the homogeneous equation, up to the `L²` norm of `f`:

`ψ(ρ) ≤ (n + 1)² (4 D (ρ / r)^(n + 3) ψ(r) + ((4 D + 2) / λ²) ∫_{B_r} f²)`

for `0 < ρ ≤ r`, with `D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`
(`TauCeti.PDE.setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq`).
Here `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm.
Dividing by `|B_ρ|` and writing `κ = r / ρ`, it gives the estimate

`⨍_{B_ρ} ‖D²u - (D²u)_{B_ρ}‖² ≤ C κ⁻² ⨍_{B_r} ‖D²u‖² + C κ^(n + 1) ⨍_{B_r} f²`

for the mean oscillation of the Hessian in Krylov's proof of the `W^{2,p}` estimates for
coefficients of vanishing mean oscillation, where it is combined with the Fefferman–Stein
inequality for the sharp maximal function.

## The argument

Each first derivative `∂ₖu` lies in `H¹(Ω)`, and differentiating the equation shows that it
solves the divergence-form equation `-div(A ∇(∂ₖu)) = -div(f eₖ)` weakly: for every test function
`φ`, moving `∂ₖ` and then the remaining derivative onto `φ` gives
`∫ ⟨A ∇(∂ₖu), ∇φ⟩ = ∫ f ∂ₖφ`
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn` and
`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_of_hasWeakLineDerivOn`). The
comparison with the frozen problem for divergence-form equations with `L²` data
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq`)
then bounds the square mean oscillation of `∇(∂ₖu)`, which is the column `D²u eₖ` of the Hessian
by the symmetry of weak second derivatives. Summing over `k`, the operator norm is controlled by
the columns: `‖T‖² ≤ (n + 1) ∑ₖ ‖T eₖ‖²` and `‖T eₖ‖ ≤ ‖T‖`.

## References

* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, AMS, 2008,
  Chapter 3 (mean oscillation estimates for the second derivatives).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.3 (comparison with the frozen problem).
-/

public section

open InnerProductSpace MeasureTheory Metric TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ}

/-- A strong solution `u ∈ W^{2,2}(Ω)` of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` with constant `A` has first
derivatives `∂ₖu ∈ H¹(Ω)` solving `-div(A ∇(∂ₖu)) = -div(f eₖ)` weakly. -/
private theorem energyFormH1_eq_setIntegral_inner_smul_single
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (heq : ∀ᵐ x ∂(volume.restrict Omega), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    {D : Fin (n + 1) → W1p volume Omega 2}
    (hD : ∀ j, HasWeakLineDerivOn volume Omega (W1p.value (Wkp.lowerOrder 1 u))
      (W1p.value (D j)) (EuclideanSpace.single j 1))
    (hDg : ∀ i j, (fun x => ⟪W1p.gradient (D j) x, EuclideanSpace.single i 1⟫_ℝ)
      =ᵐ[volume.restrict Omega]
        fun x => ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ)
    (k : Fin (n + 1)) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => A) 0 0 (D k) (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪f x • EuclideanSpace.single k 1,
        ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  have hA : ∀ i j, ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin (n + 1)) => A i j) Omega :=
    fun _ _ => contDiffOn_const
  have hD' : ∀ j, HasWeakLineDerivOn volume Omega (W1p.value (Wkp.lowerOrder 1 u))
      (W1p.value (D j)) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) := by
    simpa only [EuclideanSpace.basisFun_apply] using hD
  -- Move `∂ₖ` from `∂ₖu` onto the test function; the coefficients are constant.
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn hA (hD k) φ,
    energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_of_hasWeakLineDerivOn hA hD']
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul, zero_add,
    EuclideanSpace.basisFun_apply]
  -- The energy form with zero coefficients vanishes.
  have h0 : energyFormH1 (fun _ => Matrix.of fun _ _ => (0 : ℝ)) 0 0 (Wkp.lowerOrder 1 u)
      (W1p.ofTestFunctionₗ volume Omega 2 φ) = 0 := by
    rw [energyFormH1_zero_zero_eq_setIntegral _ (Wkp.lowerOrder 1 u)]
    simp [Matrix.mulVec, dotProduct]
  rw [h0, sub_zero, neg_neg]
  refine integral_congr_ae ?_
  filter_upwards [heq, ae_all_iff.2 fun i => ae_all_iff.2 fun j => hDg i j] with x hx hxD
  simp only [hxD, hx, real_inner_smul_left, TestFunction.lineDerivOp_apply]
  rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv, real_inner_comm,
    inner_gradient_left, mul_comm]

/-- The weak Hessian of `u` is square integrable on `Ω`. -/
private theorem memLp_iteratedGradient_one
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2) :
    MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict Omega) :=
  Lp.memLp _

/-- Each column of the weak Hessian of `u` is square integrable on `Ω`. -/
private theorem memLp_iteratedGradient_one_apply
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    MemLp (fun x => Wkp.iteratedGradient 1 u x v : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict Omega) :=
  (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) v).comp_memLp'
    (memLp_iteratedGradient_one u)

/-- The set average of the weak Hessian over a ball in `Ω`, applied to a vector, is the set
average of the corresponding column. -/
private theorem setAverage_ball_iteratedGradient_apply
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {t : ℝ} (ht : ball x₀ t ⊆ Omega) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y) v =
      ⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y v :=
  ContinuousLinearMap.average_apply
    ((memLp_iteratedGradient_one u).integrableOn_of_subset one_le_two ht
      measure_ball_lt_top.ne) v

/-- The gradient of `∂ⱼu`, with `∂ⱼu` the weak line derivative of `u`, is the corresponding
column of the Hessian, almost everywhere. -/
private theorem ae_gradient_eq_iteratedGradient_apply
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {D : Fin (n + 1) → W1p volume Omega 2}
    (hDg : ∀ i j, (fun x => ⟪W1p.gradient (D j) x, EuclideanSpace.single i 1⟫_ℝ)
      =ᵐ[volume.restrict Omega]
        fun x => ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ) (k : Fin (n + 1)) :
    (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1) := by
  filter_upwards [ae_all_iff.2 fun i => hDg i k,
    ae_all_iff.2 fun i => Wkp.inner_iteratedGradient_one_apply_ae_eq u
      (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)] with x h1 h2
  refine ext_inner_right_basis (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rw [h1 i, h2 i]

/-- The square mean oscillation of the gradient of `∂ₖu` over a ball in `Ω` is that of the
`k`-th column of the Hessian. -/
private theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_eq
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {D : Fin (n + 1) → W1p volume Omega 2} (k : Fin (n + 1))
    (hcol : (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (ht : ball x₀ t ⊆ Omega) :
    ∫ x in ball x₀ t, ‖W1p.gradient (D k) x - ⨍ y in ball x₀ t, W1p.gradient (D k) y‖ ^ 2 =
      ∫ x in ball x₀ t, ‖(Wkp.iteratedGradient 1 u x -
        ⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y) (EuclideanSpace.single k 1)‖ ^ 2 := by
  have hct := ae_restrict_of_ae_restrict_of_subset ht hcol
  rw [average_congr hct, integral_congr_ae (hct.mono fun x hx => by rw [hx])]
  simp only [sub_apply, setAverage_ball_iteratedGradient_apply u ht]

/-- The square mean oscillation of the Hessian over a ball in `Ω` is controlled by the sum of
those of its columns, with the factor `n + 1`. -/
private theorem setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_sum
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {t : ℝ} (ht : ball x₀ t ⊆ Omega) :
    ∫ x in ball x₀ t,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      (n + 1) * ∑ k, ∫ x in ball x₀ t, ‖(Wkp.iteratedGradient 1 u x -
        ⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y) (EuclideanSpace.single k 1)‖ ^ 2 := by
  have hH := memLp_iteratedGradient_one u
  have hint : ∀ k : Fin (n + 1), Integrable (fun x => ‖(Wkp.iteratedGradient 1 u x -
      ⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y) (EuclideanSpace.single k 1)‖ ^ 2)
        (volume.restrict (ball x₀ t)) := fun k =>
    (memLp_iteratedGradient_one_apply u (EuclideanSpace.single k 1)
      ).integrableOn_norm_sub_sq_of_subset ht measure_ball_lt_top.ne
      ((⨍ y in ball x₀ t, Wkp.iteratedGradient 1 u y) (EuclideanSpace.single k 1))
  rw [← integral_finsetSum _ fun k _ => hint k, ← integral_const_mul]
  refine setIntegral_mono_on ?_ ((integrable_finsetSum _ fun k _ => hint k).const_mul _)
    measurableSet_ball fun x _ => ?_
  · exact hH.integrableOn_norm_sub_sq_of_subset ht measure_ball_lt_top.ne _
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, EuclideanSpace.basisFun_apply] using
      ContinuousLinearMap.opNorm_sq_le_card_mul_sum_norm_apply_sq_orthonormalBasis _
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)

/-- The comparison estimate for one column of the Hessian of a strong solution on all of `Ω`. -/
private theorem setIntegral_ball_norm_column_sub_setAverage_sq_le_aux
    {lam Lam : ℝ} (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hball : ball x₀ r ⊆ Omega)
    (heq : ∀ᵐ x ∂(volume.restrict Omega), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (k : Fin (n + 1)) :
    ∫ x in ball x₀ ρ, ‖(Wkp.iteratedGradient 1 u x -
        ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y) (EuclideanSpace.single k 1)‖ ^ 2 ≤
      4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) *
          (∫ x in ball x₀ r,
            ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ r, Wkp.iteratedGradient 1 u y‖ ^ 2) +
        (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
          ∫ x in ball x₀ r, f x ^ 2 := by
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) *
      (ρ / r) ^ (n + 3) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ,
      K₂ = (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 :=
    ⟨_, rfl⟩
  rw [← hK₁, ← hK₂]
  have hr : 0 < r := hρ.trans_le hρr
  have hK₁0 : 0 ≤ K₁ := hK₁ ▸ by positivity
  have hρΩ : ball x₀ ρ ⊆ Omega := (ball_subset_ball hρr).trans hball
  set e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun k => EuclideanSpace.single k 1
    with he
  have hH := memLp_iteratedGradient_one u
  -- `f` agrees with a contraction of the Hessian, so it is square integrable.
  have hf : MemLp f 2 (volume.restrict (ball x₀ r)) := by
    refine (((Matrix.contraction A).comp_memLp' hH).ae_eq ?_).mono_measure
      (Measure.restrict_mono hball le_rfl)
    filter_upwards [heq] with x hx
    rw [Function.comp_apply, Matrix.contraction_apply, hx]
  -- The first derivatives `∂ₖu ∈ H¹(Ω)` solve `-div(A ∇(∂ₖu)) = -div(f eₖ)`, and their
  -- gradients are the columns of the Hessian.
  choose D hD₀ hDg using fun j =>
    Wkp.exists_hasWeakLineDerivOn_value_and_inner_gradient_ae_eq u (e j)
  have hD : ∀ j, HasWeakLineDerivOn volume Omega (W1p.value (Wkp.lowerOrder 1 u))
      (W1p.value (D j)) (e j) := fun j => by
    simpa only [Wkp.value_succ 1 u, Wkp.value_one] using hD₀ j
  have hcol := ae_gradient_eq_iteratedGradient_apply u (fun i j => hDg j (e i))
  have hGc : MemLp (fun x => f x • e k - 0) 2 (volume.restrict (ball x₀ r)) := by
    simpa only [sub_zero, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using
      (ContinuousLinearMap.toSpanSingleton ℝ (e k)).comp_memLp' hf
  have h := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq
    hA (energyFormH1_eq_setIntegral_inner_smul_single u heq hD (fun i j => hDg j (e i)) k) hball
    hGc hρ hρr
  rw [setIntegral_ball_norm_gradient_sub_setAverage_sq_eq u k (hcol k) hρΩ,
    setIntegral_ball_norm_gradient_sub_setAverage_sq_eq u k (hcol k) hball, ← hK₁, ← hK₂] at h
  have hfe : ∫ x in ball x₀ r, ‖f x • e k - 0‖ ^ 2 = ∫ x in ball x₀ r, f x ^ 2 := by
    simp [he, norm_smul]
  rw [hfe] at h
  refine h.trans (add_le_add_left (mul_le_mul_of_nonneg_left ?_ hK₁0) _)
  have hHk := memLp_iteratedGradient_one_apply u (e k)
  refine setIntegral_mono_on ?_ ?_ measurableSet_ball fun x _ => ?_
  · simpa only [sub_apply, setAverage_ball_iteratedGradient_apply u hball] using
      hHk.integrableOn_norm_sub_sq_of_subset hball measure_ball_lt_top.ne _
  · exact hH.integrableOn_norm_sub_sq_of_subset hball measure_ball_lt_top.ne _
  · refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by simp)

/-- The core estimate, for a strong solution on all of `Ω`. -/
private theorem setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_aux
    {lam Lam : ℝ} (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hball : ball x₀ r ⊆ Omega)
    (heq : ∀ᵐ x ∂(volume.restrict Omega), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      (n + 1) ^ 2 *
        (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) *
            (∫ x in ball x₀ r,
              ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ r, Wkp.iteratedGradient 1 u y‖ ^ 2) +
          (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
            ∫ x in ball x₀ r, f x ^ 2) := by
  have hρΩ : ball x₀ ρ ⊆ Omega := (ball_subset_ball hρr).trans hball
  refine (setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_sum u hρΩ).trans ?_
  calc (n + 1) * ∑ k, ∫ x in ball x₀ ρ, ‖(Wkp.iteratedGradient 1 u x -
          ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y) (EuclideanSpace.single k 1)‖ ^ 2
      ≤ (n + 1) * ∑ _k : Fin (n + 1), (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 *
          √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) * (∫ x in ball x₀ r,
          ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ r, Wkp.iteratedGradient 1 u y‖ ^ 2) +
          (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
            ∫ x in ball x₀ r, f x ^ 2) := by
        gcongr with k
        exact setIntegral_ball_norm_column_sub_setAverage_sq_le_aux hA u hball heq hρ hρr k
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Mean oscillation of the Hessian for constant coefficients.** Let `A` be a constant
coefficient matrix, uniformly elliptic with constants `0 < λ ≤ Λ`, and let `u ∈ W^{2,2}(Ω)`,
`Ω ⊆ ℝ^{n+1}` open, solve `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on a ball `B_r = ball x₀ r ⊆ Ω`.
Then for `0 < ρ ≤ r` the square mean oscillation
`ψ(t) = ∫_{B_t} ‖D²u - (D²u)_{B_t}‖²` of the weak Hessian satisfies

`ψ(ρ) ≤ (n + 1)² (4 D (ρ / r)^(n + 3) ψ(r) + ((4 D + 2) / λ²) ∫_{B_r} f²)`,

with `D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`. Here `D²u` is the weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm, and `∂ᵢ∂ⱼu = ⟪D²u eᵢ, eⱼ⟫`. -/
theorem setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq
    {lam Lam : ℝ} (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hball : ball x₀ r ⊆ Omega)
    (heq : ∀ᵐ x ∂(volume.restrict (ball x₀ r)), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      (n + 1) ^ 2 *
        (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) *
            (∫ x in ball x₀ r,
              ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ r, Wkp.iteratedGradient 1 u y‖ ^ 2) +
          (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
            ∫ x in ball x₀ r, f x ^ 2) := by
  -- Restrict `u` to `B_r`, where the equation holds almost everywhere.
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ r, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hHB : Wkp.iteratedGradient 1 (Wkp.restrictL hB 2 u)
      =ᵐ[volume.restrict (ball x₀ r)] Wkp.iteratedGradient 1 u :=
    Wkp.iteratedGradient_restrictL_ae hB 1 u
  have heqB : ∀ᵐ x ∂(volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      ∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 (Wkp.restrictL hB 2 u) x
        (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = f x := by
    filter_upwards [heq, hHB] with x hx h
    rw [h]
    exact hx
  have key := setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_aux hA
    (Wkp.restrictL hB 2 u) (Omega := B) subset_rfl heqB hρ hρr
  have hHρ := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρr) hHB
  rwa [average_congr hHρ, integral_congr_ae (hHρ.mono fun x hx => by rw [hx]),
    average_congr hHB, integral_congr_ae (hHB.mono fun x hx => by rw [hx])] at key

end PDE

end TauCeti
