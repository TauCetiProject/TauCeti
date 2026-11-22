/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Pi.Parseval
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Pi.Oscillator

/-!
# The spectral gap of the harmonic oscillator on `ℝ^ι`

For frequencies `ωᵢ > 0`, the harmonic oscillator `H = ∑ᵢ (-∂ᵢ² + ωᵢ² xᵢ²)` on `ℝ^ι` has the
dilated multi-index Hermite functions `Ψ_a(x) = ∏ᵢ ψ_{aᵢ}(√ωᵢ xᵢ)` as eigenfunctions, with
eigenvalues `∑ᵢ ωᵢ (2aᵢ + 1)`. Its lowest eigenvalue `∑ᵢ ωᵢ` belongs to the Gaussian ground state
`Ψ_0`, and every other eigenvalue exceeds it by at least `2 minᵢ ωᵢ`. This file proves the
corresponding inequality for the quadratic form of `H` on compactly supported `C²` functions,
which is what the spectral decomposition gives without a self-adjoint realization of `H`: if `u`
is orthogonal to `Ψ_0` and `κ ≤ ωᵢ` for every `i`, then

`(∑ᵢ ωᵢ + 2κ) ∫ u² ≤ ∑ᵢ (∫ -∂ᵢ²u · u + ωᵢ² ∫ xᵢ² u²)`

(`TauCeti.add_two_mul_mul_integral_sq_le_sum_integral_neg_fderiv_fderiv_mul_add_mul_integral`).
Without the orthogonality the bound is only `∑ᵢ ωᵢ ∫ u²`, the uncertainty inequality
`TauCeti.abs_mul_integral_sq_le_integral_neg_fderiv_fderiv_apply_mul_add`, whose constant is the
ground state energy. The gap inequality says that the ground state is the only obstruction to
the larger constant.

The proof expands `u` in the dilated Hermite functions. Parseval's identity for the Hermite basis
`TauCeti.hermiteFunctionPiBasis` of `L²(ℝ^ι)` holds for the dilated family after the change of
variables `xᵢ ↦ cᵢ xᵢ`, which scales integrals by `|∏ᵢ cᵢ|⁻¹`
(`TauCeti.integral_comp_mul_pi`); this is
`TauCeti.hasSum_integral_prod_hermiteFunction_comp_mul_mul_mul_integral`. Integrating by parts
twice moves each `-∂ᵢ² + cᵢ⁴ xᵢ²` onto the Hermite function, whose eigenvalue `cᵢ² (2aᵢ + 1)`
it produces (`TauCeti.integral_prod_hermiteFunction_comp_mul_mul_neg_fderiv_fderiv_add`). So
the quadratic form of each oscillator is the sum of the squared Hermite coefficients of `u`
weighted by these eigenvalues
(`TauCeti.hasSum_mul_sq_integral_prod_hermiteFunction_comp_mul_mul`), and the gap is a termwise
comparison of two convergent series in which the coefficient of the ground state vanishes.

## Main results

* `TauCeti.integral_prod_hermiteFunction_comp_mul_mul_neg_fderiv_fderiv_add`: the oscillator
  acts on the Hermite coefficients by its eigenvalues.
* `TauCeti.hasSum_mul_sq_integral_prod_hermiteFunction_comp_mul_mul`: the quadratic form of one
  oscillator in the Hermite coefficients.
* `TauCeti.add_two_mul_mul_integral_sq_le_sum_integral_neg_fderiv_fderiv_mul_add_mul_integral`: the
  spectral gap of the harmonic oscillator above its ground state.

## References

* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Springer (1987),
  Chapter 11 (the harmonic-oscillator model of the Witten Laplacian).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- Away from the ground state, the oscillator eigenvalue `∑ᵢ ωᵢ (2aᵢ + 1)` is at least
`∑ᵢ ωᵢ + 2κ` when `0 ≤ κ ≤ ωᵢ` for every `i`. -/
private theorem sum_add_two_mul_le_sum_mul_two_mul_add_one {ω : ι → ℝ} {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i, κ ≤ ω i) {a : ι → ℕ} (ha : a ≠ 0) :
    ∑ i, ω i + 2 * κ ≤ ∑ i, ω i * (2 * a i + 1) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have hj1 : (1 : ℝ) ≤ a j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  have hle : ∀ i ∈ Finset.univ.erase j, ω i ≤ ω i * (2 * a i + 1) := fun i _ ↦
    le_mul_of_one_le_right (hκ0.trans (hκ i)) (by linarith [(a i).cast_nonneg (α := ℝ)])
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  nlinarith [Finset.sum_le_sum hle, hκ j]

variable [DecidableEq ι]

/-- **The oscillator acts on Hermite coefficients by its eigenvalues.** For a compactly supported
`C²` function `u`, integrating by parts twice moves the oscillator `-∂ᵢ² + cᵢ⁴ xᵢ²` onto the
dilated Hermite function `∏ⱼ ψ_{aⱼ}(cⱼ xⱼ)`, of which it is the eigenvalue `cᵢ² (2aᵢ + 1)`. -/
theorem integral_prod_hermiteFunction_comp_mul_mul_neg_fderiv_fderiv_add (c : ι → ℝ)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (a : ι → ℕ) (i : ι) :
    ∫ x, (∏ j, hermiteFunction (a j) (c j * x j)) *
        (-fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) + c i ^ 4 * x i ^ 2 * u x) =
      c i ^ 2 * (2 * a i + 1) * ∫ x, (∏ j, hermiteFunction (a j) (c j * x j)) * u x := by
  set P : (ι → ℝ) → ℝ := fun x ↦ ∏ j, hermiteFunction (a j) (c j * x j)
  set v : ι → ℝ := Pi.single i 1
  have hP : ContDiff ℝ 2 P := contDiff_prod_hermiteFunction_comp_mul c a
  -- every integrand below has a factor vanishing off the support of `u`
  have hxPu : Integrable fun x ↦ P x * (c i ^ 4 * x i ^ 2 * u x) :=
    integrable_bilinear_of_forall_notMem_tsupport_eq_zero (ContinuousLinearMap.mul ℝ ℝ) huc
      hP.continuous (continuous_const.mul ((continuous_apply i).pow 2) |>.mul hu.continuous)
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have hPu2 : Integrable fun x ↦ P x * fderiv ℝ (fderiv ℝ u) x v v :=
    integrable_bilinear_of_forall_notMem_tsupport_eq_zero (ContinuousLinearMap.mul ℝ ℝ) huc
      hP.continuous (hu.continuous_fderiv_fderiv_apply le_rfl v v)
      fun x hx ↦ by simp [fderiv_fderiv_of_notMem_tsupport hx]
  have hP2u : Integrable fun x ↦ fderiv ℝ (fderiv ℝ P) x v v * u x :=
    integrable_bilinear_of_forall_notMem_tsupport_eq_zero (ContinuousLinearMap.mul ℝ ℝ) huc
      (hP.continuous_fderiv_fderiv_apply le_rfl v v) hu.continuous
      fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have heig : ∀ x, fderiv ℝ (fderiv ℝ P) x v v =
      c i ^ 2 * ((c i * x i) ^ 2 - (2 * a i + 1)) * P x :=
    fun x ↦ fderiv_fderiv_prod_hermiteFunction_comp_mul_apply_single_single c a x i
  calc ∫ x, P x * (-fderiv ℝ (fderiv ℝ u) x v v + c i ^ 4 * x i ^ 2 * u x)
      = ∫ x, (P x * (c i ^ 4 * x i ^ 2 * u x) - P x * fderiv ℝ (fderiv ℝ u) x v v) :=
        integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ by ring
    _ = (∫ x, P x * (c i ^ 4 * x i ^ 2 * u x)) - ∫ x, fderiv ℝ (fderiv ℝ P) x v v * u x := by
        have h := integral_bilinear_fderiv_fderiv_apply_eq_integral_fderiv_fderiv_apply
          (μ := volume) (ContinuousLinearMap.mul ℝ ℝ) (fun x _ ↦ hP.contDiffAt) hu huc v v
        simp only [ContinuousLinearMap.mul_apply'] at h
        rw [integral_sub hxPu hPu2, h]
    _ = ∫ x, (P x * (c i ^ 4 * x i ^ 2 * u x) - fderiv ℝ (fderiv ℝ P) x v v * u x) :=
        (integral_sub hxPu hP2u).symm
    _ = c i ^ 2 * (2 * a i + 1) * ∫ x, P x * u x := by
        rw [← integral_const_mul]
        exact integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ by
          dsimp only
          rw [heig]
          ring

/-- **The quadratic form of one oscillator in Hermite coefficients.** For nonzero dilation factors
`cⱼ` and a compactly supported `C²` function `u`, the squared coefficients
`(∫ ∏ⱼ ψ_{aⱼ}(cⱼ xⱼ) u(x) dx)²`, weighted by the eigenvalues `cᵢ² (2aᵢ + 1)` of the oscillator
`-∂ᵢ² + cᵢ⁴ xᵢ²`, sum to `|∏ⱼ cⱼ|⁻¹` times its quadratic form on `u`. -/
theorem hasSum_mul_sq_integral_prod_hermiteFunction_comp_mul_mul {c : ι → ℝ} (hc : ∀ i, c i ≠ 0)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (i : ι) :
    HasSum (fun a : ι → ℕ ↦ c i ^ 2 * (2 * a i + 1) *
        (∫ x, (∏ j, hermiteFunction (a j) (c j * x j)) * u x) ^ 2)
      (|∏ j, c j|⁻¹ *
        ∫ x, (-fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) + c i ^ 4 * x i ^ 2 * u x) *
          u x) := by
  have hcont : Continuous fun x ↦
      -fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) + c i ^ 4 * x i ^ 2 * u x :=
    (hu.continuous_fderiv_fderiv_apply le_rfl _ _).neg.add
      ((continuous_const.mul ((continuous_apply i).pow 2)).mul hu.continuous)
  have hsupp : HasCompactSupport fun x ↦
      -fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) + c i ^ 4 * x i ^ 2 * u x := by
    refine huc.mono' <| Function.support_subset_iff'.2 fun x hx ↦ ?_
    simp [fderiv_fderiv_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx]
  convert hasSum_integral_prod_hermiteFunction_comp_mul_mul_mul_integral hc
    (hcont.memLp_of_hasCompactSupport hsupp) (hu.continuous.memLp_of_hasCompactSupport huc)
    using 1
  · funext a
    rw [integral_prod_hermiteFunction_comp_mul_mul_neg_fderiv_fderiv_add c hu huc]
    ring

/-- The spectral gap for Lebesgue measure and positive frequencies, through the Hermite expansion
in the dilation `cᵢ = √ωᵢ`. -/
private theorem add_two_mul_mul_integral_sq_le_sum_integral_of_pos {ω : ι → ℝ}
    (hω : ∀ i, 0 < ω i) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : ∀ i, κ ≤ ω i) {u : (ι → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (horth : ∫ x, (∏ i, hermiteFunction 0 (√(ω i) * x i)) * u x = 0) :
    (∑ i, ω i + 2 * κ) * ∫ x, u x ^ 2 ≤
      ∑ i, ∫ x, (-fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) +
        ω i ^ 2 * x i ^ 2 * u x) * u x := by
  set c : ι → ℝ := fun i ↦ √(ω i)
  have hc : ∀ i, c i ≠ 0 := fun i ↦ (Real.sqrt_pos.2 (hω i)).ne'
  have hc2 : ∀ i, c i ^ 2 = ω i := fun i ↦ Real.sq_sqrt (hω i).le
  have hc4 : ∀ i, c i ^ 4 = ω i ^ 2 := fun i ↦ by rw [← hc2]; ring
  set d : (ι → ℕ) → ℝ := fun a ↦ ∫ x, (∏ j, hermiteFunction (a j) (c j * x j)) * u x
  have hd0 : d 0 = 0 := by simpa [d, c] using horth
  have hJ : 0 < |∏ j, c j|⁻¹ := inv_pos.2 (abs_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ ↦ hc i))
  -- the quadratic form is the sum of the eigenvalues times the squared Hermite coefficients
  have hosc : HasSum (fun a ↦ ∑ i, ω i * (2 * a i + 1) * d a ^ 2) (|∏ j, c j|⁻¹ *
      ∑ i, ∫ x, (-fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) +
        ω i ^ 2 * x i ^ 2 * u x) * u x) := by
    rw [Finset.mul_sum]
    refine hasSum_sum fun i _ ↦ ?_
    simpa only [hc2, hc4] using hasSum_mul_sq_integral_prod_hermiteFunction_comp_mul_mul hc hu huc i
  have hnorm : HasSum (fun a ↦ (∑ i, ω i + 2 * κ) * d a ^ 2)
      ((∑ i, ω i + 2 * κ) * (|∏ j, c j|⁻¹ * ∫ x, u x ^ 2)) := by
    refine HasSum.mul_left _ ?_
    have hu2 : MemLp u 2 (Measure.pi fun _ : ι ↦ volume) :=
      hu.continuous.memLp_of_hasCompactSupport huc
    simpa only [sq] using hasSum_integral_prod_hermiteFunction_comp_mul_mul_mul_integral hc hu2 hu2
  -- the ground state coefficient vanishes, and every other eigenvalue lies above the gap
  have hterm : ∀ a : ι → ℕ, (∑ i, ω i + 2 * κ) * d a ^ 2 ≤ ∑ i, ω i * (2 * a i + 1) * d a ^ 2 := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp [hd0]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_add_two_mul_le_sum_mul_two_mul_add_one hκ0 hκ ha)
      (sq_nonneg _)
  have := hasSum_le hterm hnorm hosc
  rw [← mul_assoc, mul_comm _ (|∏ j, c j|⁻¹), mul_assoc] at this
  exact le_of_mul_le_mul_left this hJ

/-- **The spectral gap of the harmonic oscillator.** Let `u` be a compactly supported `C²`
function on `ℝ^ι`, orthogonal to the Gaussian ground state `∏ᵢ ψ₀(√ωᵢ xᵢ)` of the oscillator
`∑ᵢ (-∂ᵢ² + ωᵢ² xᵢ²)`. If `κ ≤ ωᵢ` for every `i`, the quadratic form
`∑ᵢ (∫ -∂ᵢ²u · u + ωᵢ² ∫ xᵢ² u²)` of the oscillator on `u` is at least `∑ᵢ ωᵢ + 2κ` times
`∫ u²`: the excited states lie at least `2 minᵢ ωᵢ` above the ground state energy `∑ᵢ ωᵢ`. For
`κ ≤ 0` this is the uncertainty inequality and needs no orthogonality. The integrals are against
an arbitrary additive Haar measure. -/
theorem add_two_mul_mul_integral_sq_le_sum_integral_neg_fderiv_fderiv_mul_add_mul_integral
    {μ : Measure (ι → ℝ)} [μ.IsAddHaarMeasure] {ω : ι → ℝ} {κ : ℝ} (hκ : ∀ i, κ ≤ ω i)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (horth : ∫ x, (∏ i, hermiteFunction 0 (√(ω i) * x i)) * u x ∂μ = 0) :
    (∑ i, ω i + 2 * κ) * ∫ x, u x ^ 2 ∂μ ≤
      ∑ i, (∫ x, -fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) * u x ∂μ +
        ω i ^ 2 * ∫ x, x i ^ 2 * u x ^ 2 ∂μ) := by
  rcases le_or_gt κ 0 with hκ0 | hκ0
  · -- for `κ ≤ 0` each oscillator is at least `|ωᵢ| ≥ ωᵢ` by the uncertainty inequality
    have hN : 0 ≤ ∫ x, u x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
    calc (∑ i, ω i + 2 * κ) * ∫ x, u x ^ 2 ∂μ ≤ ∑ i, |ω i| * ∫ x, u x ^ 2 ∂μ := by
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ hN
          linarith [Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ le_abs_self (ω i)]
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
          simpa using abs_mul_integral_sq_le_integral_neg_fderiv_fderiv_apply_mul_add (μ := μ)
            (ContinuousLinearMap.id ℝ ℝ) (ℓ := ContinuousLinearMap.proj i) (v := Pi.single i 1)
            (by simp) hu huc (ω i)
  -- for `κ > 0` every frequency is positive; reduce to Lebesgue measure
  have hω : ∀ i, 0 < ω i := fun i ↦ hκ0.trans_le (hκ i)
  have hA : ∀ i, Integrable
      (fun x ↦ -fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) * u x) := fun i ↦ by
    simpa using integrable_neg_fderiv_fderiv_apply_mul_of_hasCompactSupport
      (ContinuousLinearMap.id ℝ ℝ) hu huc (Pi.single i 1) (Pi.single i 1)
  have hX : ∀ i, Integrable (fun x : ι → ℝ ↦ x i ^ 2 * u x ^ 2) := fun i ↦ by
    simpa using integrable_mul_sq_of_hasCompactSupport (ContinuousLinearMap.id ℝ ℝ)
      ((continuous_apply i).pow 2) hu.continuous huc
  have hsplit : ∀ i, ∫ x, (-fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) +
      ω i ^ 2 * x i ^ 2 * u x) * u x =
        (∫ x, -fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) * u x) +
          ω i ^ 2 * ∫ x, x i ^ 2 * u x ^ 2 := fun i ↦ by
    rw [← integral_const_mul, ← integral_add (hA i) ((hX i).const_mul _)]
    exact integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ by ring
  obtain ⟨k, hk, rfl⟩ : ∃ k : NNReal, 0 < k ∧ μ = k • volume :=
    ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume,
      Measure.isAddLeftInvariant_eq_smul μ volume⟩
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at horth ⊢
  have h := add_two_mul_mul_integral_sq_le_sum_integral_of_pos hω hκ0.le hκ hu huc
    ((mul_eq_zero.1 horth).resolve_left (by exact_mod_cast hk.ne'))
  simp only [hsplit] at h
  calc (∑ i, ω i + 2 * κ) * (k * ∫ x, u x ^ 2) = k * ((∑ i, ω i + 2 * κ) * ∫ x, u x ^ 2) := by
        ring
    _ ≤ k * ∑ i, ((∫ x, -fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) * u x) +
          ω i ^ 2 * ∫ x, x i ^ 2 * u x ^ 2) := mul_le_mul_of_nonneg_left h k.coe_nonneg
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

end TauCeti
