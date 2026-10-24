/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.SchwartzSpace.LaplacianResolvent
public import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier

/-!
# The resolvent of the Laplacian on tempered distributions

For `c > 0` the shifted Laplacian `-Δ + c` is the Fourier multiplier with symbol
`(2π)² ‖ξ‖² + c`, the factor `(2π)²` coming from Mathlib's normalization of the Fourier transform.
This symbol is bounded below by `c`, so the Fourier multiplier with the reciprocal symbol is a
two-sided inverse `TemperedDistribution.laplacianResolvent c` of `-Δ + c` on all tempered
distributions. It extends the resolvent `SchwartzMap.laplacianResolvent` on Schwartz space.

On the `L²` Sobolev scale the resolvent gains two derivatives: it maps `H^s` to `H^{s+2}`. With
Mathlib's mapping property of the Laplacian, this gives elliptic regularity for `-Δ + c`: a
tempered distribution `f` lies in `H^{s+2}` exactly when `-Δ f + c f` lies in `H^s`. Inverting a
constant-coefficient first-order operator `L` satisfying a Weitzenböck identity `L* L = L L* =
-Δ + c` on the Sobolev scale reduces to this statement, through `L⁻¹ = L* (-Δ + c)⁻¹`.

## Main declarations

* `TemperedDistribution.neg_laplacian_add_smul_eq_fourierMultiplierCLM`: `-Δ + c` is the Fourier
  multiplier with symbol `(2π)² ‖ξ‖² + c`.
* `TemperedDistribution.laplacianResolvent c`: the Fourier multiplier with symbol
  `((2π)² ‖ξ‖² + c)⁻¹` (`TemperedDistribution.laplacianResolvent_eq_fourierMultiplierCLM`),
  characterized for `c > 0` as the two-sided inverse of `-Δ + c` by
  `TemperedDistribution.laplacianResolvent_neg_laplacian_add_smul` and
  `TemperedDistribution.neg_laplacian_laplacianResolvent_add_smul`.
* `TemperedDistribution.eq_zero_of_neg_laplacian_add_smul_eq_zero`: for `c > 0`, `-Δ + c` has
  trivial kernel on tempered distributions.
* `TemperedDistribution.laplacianResolvent_toTemperedDistributionCLM_eq`: on Schwartz functions it
  is `SchwartzMap.laplacianResolvent`.
* `TemperedDistribution.MemSobolev.laplacianResolvent`: the resolvent maps `H^s` to `H^{s+2}`.
* `TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`: `f ∈ H^{s+2}` if and only
  if `-Δ f + c f ∈ H^s`.

## References

* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (the Sobolev spaces `H^s` and
  the mapping properties of elliptic operators with constant coefficients).
-/

public section

noncomputable section

namespace TemperedDistribution

open scoped SchwartzMap Laplacian Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hasTemperateGrowth_resolventSymbol {c : ℝ} (hc : 0 < c) :
    (fun ξ : E ↦ ((((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth := by
  have h := TauCeti.hasTemperateGrowth_inv_mul_norm_sq_add (E := E) (a := (2 * π) ^ 2)
    (by positivity) hc
  fun_prop

omit [InnerProductSpace ℝ E] in
private theorem resolventSymbol_mul {c : ℝ} (hc : 0 < c) :
    (fun ξ : E ↦ (((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c : ℝ) : ℂ)) *
      (fun ξ : E ↦ ((((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹ : ℝ) : ℂ)) = fun _ ↦ 1 := by
  ext ξ
  have : ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c : ℝ) ≠ 0 := by positivity
  simp only [Pi.mul_apply, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section normed

variable [NormedSpace ℂ F]

/-- The shifted Laplacian `-Δ + c` is the Fourier multiplier with symbol `(2π)² ‖ξ‖² + c`. -/
theorem neg_laplacian_add_smul_eq_fourierMultiplierCLM (c : ℝ) (f : 𝓢'(E, F)) :
    -Δ f + c • f = fourierMultiplierCLM F (fun ξ ↦ (((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c : ℝ) : ℂ)) f := by
  have hsymb : (fun ξ : E ↦ (((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c : ℝ) : ℂ)) =
      ((2 * π) ^ 2 : ℂ) • (fun ξ : E ↦ ((‖ξ‖ ^ 2 : ℝ) : ℂ)) + fun _ ↦ (c : ℂ) := by
    ext ξ
    simp
  rw [hsymb, fourierMultiplierCLM_add (by fun_prop) (by fun_prop),
    fourierMultiplierCLM_smul (by fun_prop), fourierMultiplierCLM_const,
    laplacian_eq_fourierMultiplierCLM]
  simp [← Complex.coe_smul]

variable (F) in
/-- The **resolvent of the Laplacian** `(c - Δ)⁻¹` on tempered distributions: the Fourier
multiplier with symbol `((2π)² ‖ξ‖² + c)⁻¹`. For `c > 0` it is the two-sided inverse of `-Δ + c`
(`laplacianResolvent_neg_laplacian_add_smul` and `neg_laplacian_laplacianResolvent_add_smul`);
for `c ≤ 0` the value is not meaningful. -/
def laplacianResolvent (c : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun ξ : E ↦ ((((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹ : ℝ) : ℂ))

variable (F) in
/-- The resolvent of the Laplacian is the Fourier multiplier with symbol `((2π)² ‖ξ‖² + c)⁻¹`. -/
theorem laplacianResolvent_eq_fourierMultiplierCLM (c : ℝ) :
    laplacianResolvent F c =
      fourierMultiplierCLM F (fun ξ : E ↦ ((((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹ : ℝ) : ℂ)) :=
  (rfl)

/-- The resolvent of the Laplacian is a left inverse of `-Δ + c`, for `c > 0`. -/
@[simp]
theorem laplacianResolvent_neg_laplacian_add_smul {c : ℝ} (hc : 0 < c) (f : 𝓢'(E, F)) :
    laplacianResolvent F c (-Δ f + c • f) = f := by
  rw [neg_laplacian_add_smul_eq_fourierMultiplierCLM, laplacianResolvent_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
      (hasTemperateGrowth_resolventSymbol hc), resolventSymbol_mul hc]
  simp

/-- The resolvent of the Laplacian is a right inverse of `-Δ + c`, for `c > 0`. -/
@[simp]
theorem neg_laplacian_laplacianResolvent_add_smul {c : ℝ} (hc : 0 < c) (f : 𝓢'(E, F)) :
    -Δ (laplacianResolvent F c f) + c • laplacianResolvent F c f = f := by
  rw [neg_laplacian_add_smul_eq_fourierMultiplierCLM, laplacianResolvent_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (hasTemperateGrowth_resolventSymbol hc)
      (by fun_prop), mul_comm, resolventSymbol_mul hc]
  simp

/-- For `c > 0`, the shifted Laplacian `-Δ + c` has trivial kernel on tempered distributions. -/
theorem eq_zero_of_neg_laplacian_add_smul_eq_zero {c : ℝ} (hc : 0 < c) {f : 𝓢'(E, F)}
    (hf : -Δ f + c • f = 0) : f = 0 := by
  rw [← laplacianResolvent_neg_laplacian_add_smul hc f, hf, map_zero]

/-- The resolvent of the Laplacian on tempered distributions extends the resolvent
`SchwartzMap.laplacianResolvent` on Schwartz space, for `c > 0`. -/
theorem laplacianResolvent_toTemperedDistributionCLM_eq [CompleteSpace F] {c : ℝ} (hc : 0 < c)
    (f : 𝓢(E, F)) :
    laplacianResolvent F c (f : 𝓢'(E, F)) = SchwartzMap.laplacianResolvent c f := by
  conv_lhs => rw [← SchwartzMap.neg_laplacian_laplacianResolvent_add_smul hc f]
  rw [map_add, map_neg, ContinuousLinearMap.map_smul_of_tower,
    ← laplacian_toTemperedDistributionCLM_eq, laplacianResolvent_neg_laplacian_add_smul hc]

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The resolvent of the Laplacian gains two derivatives**: it maps the Sobolev space `H^s` to
`H^{s+2}`, for `c > 0`. -/
theorem MemSobolev.laplacianResolvent {c s : ℝ} (hc : 0 < c) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    MemSobolev (s + 2) 2 (TemperedDistribution.laplacianResolvent F c f) := by
  -- Factor the resolvent as the Bessel potential of order `-2` after the bounded multiplier
  -- `(1 + ‖ξ‖²) / ((2π)² ‖ξ‖² + c)`.
  set m : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹ : ℝ) : ℂ)
  have hr := TauCeti.hasTemperateGrowth_inv_mul_norm_sq_add (E := E) (a := (2 * π) ^ 2)
    (by positivity) hc
  have hm : m.HasTemperateGrowth := by fun_prop
  have hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C := by
    refine ⟨c⁻¹ + ((2 * π) ^ 2)⁻¹, fun ξ ↦ ?_⟩
    have ha : 0 < (2 * π) ^ 2 := by positivity
    have hd : 0 < (2 * π) ^ 2 * ‖ξ‖ ^ 2 + c := by positivity
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv,
      div_le_iff₀ hd]
    have hexp : (c⁻¹ + ((2 * π) ^ 2)⁻¹) * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c) =
        (2 * π) ^ 2 * ‖ξ‖ ^ 2 / c + 1 + ‖ξ‖ ^ 2 + c / (2 * π) ^ 2 := by
      field_simp
      ring
    have h₁ : 0 ≤ (2 * π) ^ 2 * ‖ξ‖ ^ 2 / c := by positivity
    have h₂ : 0 ≤ c / (2 * π) ^ 2 := by positivity
    linarith
  have heq : TemperedDistribution.laplacianResolvent F c f =
      besselPotential E F (-2) (fourierMultiplierCLM F m f) := by
    rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hm (by fun_prop),
      laplacianResolvent_eq_fourierMultiplierCLM]
    congr 2
    ext ξ
    have h₁ : (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [Pi.mul_apply, ← Complex.ofReal_mul, show (-2 : ℝ) / 2 = -1 by norm_num,
      Real.rpow_neg_one, mul_comm (1 + ‖ξ‖ ^ 2), mul_assoc, mul_inv_cancel₀ h₁, mul_one]
  rw [heq, memSobolev_besselPotential_iff, show -2 + (s + 2) = s by ring]
  exact hf.fourierMultiplierCLM_of_bounded hm hmb

/-- **Elliptic regularity for the shifted Laplacian**: for `c > 0`, a tempered distribution `f`
lies in the Sobolev space `H^{s+2}` if and only if `-Δ f + c f` lies in `H^s`. -/
theorem memSobolev_add_two_iff_neg_laplacian_add_smul {c s : ℝ} (hc : 0 < c) {f : 𝓢'(E, F)} :
    MemSobolev (s + 2) 2 f ↔ MemSobolev s 2 (-Δ f + c • f) := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hΔ := hf.laplacian
    rw [add_sub_cancel_right] at hΔ
    rw [← Complex.coe_smul]
    exact hΔ.neg.add ((hf.mono (by linarith)).smul _)
  · have h := hf.laplacianResolvent (F := F) hc
    rwa [laplacianResolvent_neg_laplacian_add_smul hc] at h

end inner

end TemperedDistribution
