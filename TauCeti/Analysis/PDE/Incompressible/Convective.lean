/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.IntegrationByParts
public import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Antisymmetry of the convective form

Let `u : E → E` be a velocity field on a finite-dimensional real inner product space `E`, and let
`v, w : E → F` have weak derivatives `V, W`. The convective term `(u · ∇) v` is `V x (u x)`, and
the convective trilinear form of the Navier–Stokes equations is

`b(u, v, w) = ∫ ⟪(u · ∇) v, w⟫ = ∫ ⟪V x (u x), w x⟫`.

Integrating `div (⟪v, w⟫ u) = ⟪(u · ∇) v, w⟫ + ⟪v, (u · ∇) w⟫ + ⟪v, w⟫ div u` over the whole
space gives

`b(u, v, w) + b(u, w, v) = -∫ (div u) ⟪v, w⟫`

(`TauCeti.HasWeakDivergenceOn.integral_inner_apply_add_integral_inner_apply`). The hypotheses are
those of the energy class in dimensions two and three, where `H¹ ⊆ L⁴`: `u, v, w ∈ L⁴`,
`v ∈ L²`, and `V, W` and `div u` in `L²`. For a divergence-free field `u` the form is
antisymmetric in its last two arguments
(`TauCeti.IsSolenoidalOn.integral_inner_apply_eq_neg_integral_inner_apply`), so
`b(u, v, v) = 0` (`TauCeti.IsSolenoidalOn.integral_inner_apply_self_eq_zero`); this cancellation
is what makes the nonlinear term disappear from the energy identity. For a general `u`,
`b(u, v, v) = -½ ∫ (div u) ‖v‖²` (`TauCeti.HasWeakDivergenceOn.integral_inner_apply_self`).
Tested against a test field `φ`, antisymmetry is the divergence form `(u · ∇) v = div (v ⊗ u)`
of the convective term in the sense of distributions
(`TauCeti.IsSolenoidalOn.integral_inner_apply_eq_neg_integral_inner_fderiv_apply`).

The identity is `TauCeti.HasWeakDivergenceOn.integral_apply_eq_neg_integral_mul` applied to the
scalar function `⟪v, w⟫`, whose weak derivative is given by the bilinear Leibniz rule
`TauCeti.HasWeakFDerivOn.bilin_of_memLp`; every pairing is controlled by Hölder's inequality with
the exponents `1/2 + 1/4 + 1/4 = 1`.

## References

R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, Chapter II, §1, where the
trilinear form `b` and its antisymmetry are introduced on bounded domains.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {u : E → E} {g : E → ℝ} {v w : E → F} {V W : E → E →L[ℝ] F}

private theorem inv_four_add_inv_four : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
  norm_num

/-- **The convective form against a divergence.** Let `u` have weak divergence `g` on the whole
space, and let `v, w` have weak derivatives `V, W`. If `u, v, w ∈ L⁴`, `v ∈ L²` and
`V, W, g ∈ L²`, then

`∫ ⟪(u · ∇) v, w⟫ + ∫ ⟪v, (u · ∇) w⟫ = -∫ g ⟪v, w⟫`. -/
theorem HasWeakDivergenceOn.integral_inner_apply_add_integral_inner_apply
    (hu : HasWeakDivergenceOn μ ⊤ u g) (hv : HasWeakFDerivOn μ ⊤ v V)
    (hw : HasWeakFDerivOn μ ⊤ w W) (hu4 : MemLp u 4 μ) (hv2 : MemLp v 2 μ) (hv4 : MemLp v 4 μ)
    (hw4 : MemLp w 4 μ) (hV : MemLp V 2 μ) (hW : MemLp W 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ⟪V x (u x), w x⟫_ℝ ∂μ + ∫ x, ⟪v x, W x (u x)⟫_ℝ ∂μ =
      -∫ x, g x * ⟪v x, w x⟫_ℝ ∂μ := by
  -- Hölder exponents: `1/2 + 1/4 = 1/r`, so that `r = 4/3` is conjugate to `4`.
  let r : ℝ≥0∞ := (2⁻¹ + 4⁻¹)⁻¹
  have : ENNReal.HolderTriple 2 4 r := ENNReal.HolderTriple.of 2 4
  have : ENNReal.HolderTriple 4 4 2 := ⟨by rw [inv_four_add_inv_four]⟩
  have : r.HolderConjugate 4 := ⟨by
    rw [inv_inv, inv_one, add_assoc, inv_four_add_inv_four, ENNReal.inv_two_add_inv_two]⟩
  have h24 : (2 : ℝ≥0∞)⁻¹ + 4⁻¹ ≤ 1 := by
    rw [← ENNReal.inv_two_add_inv_two]
    gcongr
    norm_num
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  let B : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  have hB (a b : F) : B a b = ⟪a, b⟫_ℝ := rfl
  -- The weak derivative of `⟪v, w⟫`.
  have hψ := hv.bilin_of_memLp B (p := 4) (p' := 2) (q := 4) (q' := 2) (by simp) (by simp)
    (by simp) (by simp) (by rw [inv_four_add_inv_four]; norm_num) h24 (by rwa [add_comm])
    hw (fun K _ _ ↦ hv4.restrict K) (fun K _ _ ↦ hV.restrict K) (fun K _ _ ↦ hw4.restrict K)
    (fun K _ _ ↦ hW.restrict K)
  -- The Hölder bounds on the pairings.
  have hψ2 : MemLp (fun x ↦ B (v x) (w x)) 2 μ := B.memLp_of_bilin 2 hv4 hw4
  have hDψ : MemLp (fun x ↦ B.precompL E (V x) (w x) + B.precompR E (v x) (W x)) r μ :=
    ((B.precompL E).memLp_of_bilin r hV hw4).add ((B.precompR E).memLp_of_bilin r hv4 hW)
  let A : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.id ℝ (E →L[ℝ] F)
  have hVu : MemLp (fun x ↦ V x (u x)) r μ := A.memLp_of_bilin r hV hu4
  have hWu : MemLp (fun x ↦ W x (u x)) r μ := A.memLp_of_bilin r hW hu4
  have h₁ : Integrable (fun x ↦ ⟪V x (u x), w x⟫_ℝ) μ :=
    memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hVu hw4)
  have h₂ : Integrable (fun x ↦ ⟪v x, W x (u x)⟫_ℝ) μ :=
    memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hv4 hWu)
  have h₁₂ : Integrable (fun x ↦ ⟪V x (u x), w x⟫_ℝ + ⟪v x, W x (u x)⟫_ℝ) μ := h₁.add h₂
  have key := hu.integral_apply_eq_neg_integral_mul (s := r) (s' := 4) (t := 2) (t' := 2) hψ
    (ENNReal.HolderTriple.le 2 4 r) (fun K _ ↦ hψ2.restrict K) (fun K _ ↦ hDψ.restrict K)
    (fun K _ ↦ hu4.restrict K) (fun K _ ↦ hg.restrict K)
    (by simpa [hB] using h₁₂) (hψ2.integrable_mul hg)
    (memLp_one_iff_integrable.1 ((ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin 1
      (B.memLp_of_bilin r hv2 hw4) hu4))
  simp only [add_apply, ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hB] at key
  rw [integral_add h₁ h₂] at key
  simpa only [mul_comm (g _)] using key

/-- **The convective form on a diagonal.** Let `u` have weak divergence `g` on the whole space and
let `v` have a weak derivative `V`. If `u ∈ L⁴`, `v ∈ L² ∩ L⁴` and `V, g ∈ L²`, then
`∫ ⟪(u · ∇) v, v⟫ = -½ ∫ g ‖v‖²`. -/
theorem HasWeakDivergenceOn.integral_inner_apply_self (hu : HasWeakDivergenceOn μ ⊤ u g)
    (hv : HasWeakFDerivOn μ ⊤ v V) (hu4 : MemLp u 4 μ) (hv2 : MemLp v 2 μ) (hv4 : MemLp v 4 μ)
    (hV : MemLp V 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ⟪V x (u x), v x⟫_ℝ ∂μ = -(∫ x, g x * ‖v x‖ ^ 2 ∂μ) / 2 := by
  have h := hu.integral_inner_apply_add_integral_inner_apply hv hv hu4 hv2 hv4 hv4 hV hV hg
  simp only [real_inner_comm (v _) (V _ _), real_inner_self_eq_norm_sq] at h ⊢
  linarith

/-- **Antisymmetry of the convective form.** For a divergence-free field `u ∈ L⁴` on the whole
space and fields `v, w` with weak derivatives `V, W`, where `v ∈ L² ∩ L⁴`, `w ∈ L⁴` and
`V, W ∈ L²`, `∫ ⟪(u · ∇) v, w⟫ = -∫ ⟪v, (u · ∇) w⟫`. -/
theorem IsSolenoidalOn.integral_inner_apply_eq_neg_integral_inner_apply
    (hu : IsSolenoidalOn μ ⊤ u) (hv : HasWeakFDerivOn μ ⊤ v V) (hw : HasWeakFDerivOn μ ⊤ w W)
    (hu4 : MemLp u 4 μ) (hv2 : MemLp v 2 μ) (hv4 : MemLp v 4 μ) (hw4 : MemLp w 4 μ)
    (hV : MemLp V 2 μ) (hW : MemLp W 2 μ) :
    ∫ x, ⟪V x (u x), w x⟫_ℝ ∂μ = -∫ x, ⟪v x, W x (u x)⟫_ℝ ∂μ := by
  have h := (isSolenoidalOn_iff_hasWeakDivergenceOn.1 hu)
    |>.integral_inner_apply_add_integral_inner_apply hv hw hu4 hv2 hv4 hw4 hV hW
      (MemLp.zero' (ε := ℝ))
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero] at h
  linarith

/-- **The convective form vanishes on a diagonal.** For a divergence-free field `u ∈ L⁴` on the
whole space and a field `v ∈ L² ∩ L⁴` with weak derivative `V ∈ L²`,
`∫ ⟪(u · ∇) v, v⟫ = 0`. -/
theorem IsSolenoidalOn.integral_inner_apply_self_eq_zero (hu : IsSolenoidalOn μ ⊤ u)
    (hv : HasWeakFDerivOn μ ⊤ v V) (hu4 : MemLp u 4 μ) (hv2 : MemLp v 2 μ) (hv4 : MemLp v 4 μ)
    (hV : MemLp V 2 μ) :
    ∫ x, ⟪V x (u x), v x⟫_ℝ ∂μ = 0 := by
  simpa using (isSolenoidalOn_iff_hasWeakDivergenceOn.1 hu).integral_inner_apply_self hv hu4 hv2
    hv4 hV (MemLp.zero' (ε := ℝ))

/-- **The divergence form of the convective term.** For a divergence-free field `u ∈ L⁴` on the
whole space and a field `v ∈ L⁴` with weak derivative `V ∈ L²`, the convective term
`(u · ∇) v` is the divergence of `v ⊗ u` in the sense of distributions: for every test field `φ`,
`∫ ⟪(u · ∇) v, φ⟫ = -∫ ⟪v, Dφ (u)⟫`. -/
theorem IsSolenoidalOn.integral_inner_apply_eq_neg_integral_inner_fderiv_apply
    (hu : IsSolenoidalOn μ ⊤ u) (hv : HasWeakFDerivOn μ ⊤ v V) (hu4 : MemLp u 4 μ)
    (hv4 : MemLp v 4 μ) (hV : MemLp V 2 μ) (φ : 𝓓((⊤ : Opens E), F)) :
    ∫ x, ⟪V x (u x), φ x⟫_ℝ ∂μ = -∫ x, ⟪v x, fderiv ℝ φ x (u x)⟫_ℝ ∂μ := by
  have := hv.completeSpace
  have h := hu.integral_inner_apply_eq_neg_integral_inner_apply
    ((φ.contDiff.of_le (by simp)).contDiffOn.hasWeakFDerivOn_fderiv) hv hu4
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport) hv4
    ((φ.contDiff.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv (𝕜 := ℝ))) hV
  simp only [real_inner_comm] at h ⊢
  linarith

end TauCeti
