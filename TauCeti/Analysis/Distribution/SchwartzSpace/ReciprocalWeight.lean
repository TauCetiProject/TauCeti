/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Duality of Fourier-weighted `L²` norms with reciprocal weights

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. A real
weight `w` on the frequency side defines the norm

`N_w(u) = ‖w 𝓕 u‖_{L²}`

on Schwartz functions `u : E → F`. The Sobolev norms are the case `w(ζ) = (1 + ‖ζ‖²) ^ (s / 2)`, and
other conventions for the frequency variable, such as the angular frequency `ξ = 2π ζ`, only change
the weight. This file proves that for **reciprocal weights**, `w'(ζ) w(ζ) = 1`, the norms `N_w` and
`N_{w'}` are dual to each other for the `L²` pairing `∫ ⟪u, v⟫` of Schwartz functions, with constant
one, and deduces that a formal adjoint satisfies the dual estimate with the same constant.

* **Pairing normalization.** By Plancherel's theorem with Mathlib's normalization of the Fourier
  transform, `∫ ⟪u x, v x⟫ dx = ∫ ⟪w 𝓕 u, w' 𝓕 v⟫ dζ`
  (`SchwartzMap.integral_inner_eq_integral_inner_smul_fourier`).
* **Duality.** `‖∫ ⟪u, v⟫‖ ≤ N_w(u) N_{w'}(v)`
  (`SchwartzMap.norm_integral_inner_le_of_mul_eq_one`), and the bound is attained: the Schwartz
  function `u` with `𝓕 u = w'² 𝓕 v` has `∫ ⟪u, v⟫ = N_{w'}(v)²` and `N_w(u) = N_{w'}(v)`
  (`SchwartzMap.exists_integral_inner_eq_and_eLpNorm_eq`). Hence `N_{w'}(v) ≤ M` exactly when
  `‖∫ ⟪u, v⟫‖ ≤ M N_w(u)` for every Schwartz `u`
  (`SchwartzMap.eLpNorm_smul_fourier_le_iff_forall_norm_integral_inner_le`).
* **Transpose bound.** If `A'` is a formal adjoint of `A`, `∫ ⟪A u, v⟫ = ∫ ⟪u, A' v⟫`, and
  `N_{w₂}(A u) ≤ C N_{w₁}(u)` for every `u`, then `N_{w₁'}(A' v) ≤ C N_{w₂'}(v)` for every `v`, for
  the reciprocal weights `w₁'` and `w₂'` and with the same constant `C`
  (`SchwartzMap.eLpNorm_smul_fourier_le_of_integral_inner_eq`). No linearity or continuity of `A`
  and `A'` is used.

The constant is preserved because the dual norms are computed exactly, not up to equivalence.
Passing to another norm equivalent to `N_w` changes the constant by the equivalence constants.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the dual of `H_s` is `H_{-s}`).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap InnerProductSpace

namespace SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Pairing normalization.** For real Fourier weights with `w' ζ * w ζ = 1`, the `L²` pairing of
two Schwartz functions is the `L²` pairing of their weighted Fourier transforms `w 𝓕 u` and
`w' 𝓕 v`. -/
theorem integral_inner_eq_integral_inner_smul_fourier {w w' : E → ℝ}
    (hww' : ∀ ζ, w' ζ * w ζ = 1) (u v : 𝓢(E, F)) :
    ∫ x, ⟪u x, v x⟫_ℂ = ∫ ζ, ⟪(w ζ : ℂ) • 𝓕 u ζ, (w' ζ : ℂ) • 𝓕 v ζ⟫_ℂ := by
  rw [← integral_inner_fourier_fourier]
  congr 1
  funext ζ
  simp [inner_smul_left, inner_smul_right, ← mul_assoc, ← Complex.ofReal_mul, hww',
    -Complex.coe_smul]

omit [CompleteSpace F] in
/-- For a weight of temperate growth, the weighted `L²` norm `‖w 𝓕 u‖_{L²}` of a Schwartz function
is the `L²` norm of the Schwartz function `w 𝓕 u`. -/
private theorem eLpNorm_smul_fourier_toReal_eq {w : E → ℝ}
    (hw : (fun ζ ↦ (w ζ : ℂ)).HasTemperateGrowth) (u : 𝓢(E, F)) :
    (eLpNorm (fun ζ ↦ (w ζ : ℂ) • 𝓕 u ζ) 2 volume).toReal =
      ‖(smulLeftCLM F (fun ζ ↦ (w ζ : ℂ)) (𝓕 u)).toLp 2‖ := by
  rw [norm_toLp, smulLeftCLM_apply hw]

/-- **Duality of reciprocal weights.** For real Fourier weights of temperate growth with
`w' ζ * w ζ = 1`, `‖∫ ⟪u, v⟫‖ ≤ ‖w 𝓕 u‖_{L²} ‖w' 𝓕 v‖_{L²}` for Schwartz functions `u` and `v`. -/
theorem norm_integral_inner_le_of_mul_eq_one {w w' : E → ℝ}
    (hw : (fun ζ ↦ (w ζ : ℂ)).HasTemperateGrowth) (hw' : (fun ζ ↦ (w' ζ : ℂ)).HasTemperateGrowth)
    (hww' : ∀ ζ, w' ζ * w ζ = 1) (u v : 𝓢(E, F)) :
    ‖∫ x, ⟪u x, v x⟫_ℂ‖ ≤
      (eLpNorm (fun ζ ↦ (w ζ : ℂ) • 𝓕 u ζ) 2 volume).toReal *
        (eLpNorm (fun ζ ↦ (w' ζ : ℂ) • 𝓕 v ζ) 2 volume).toReal := by
  rw [eLpNorm_smul_fourier_toReal_eq hw, eLpNorm_smul_fourier_toReal_eq hw',
    integral_inner_eq_integral_inner_smul_fourier hww']
  refine le_of_eq_of_le ?_ (norm_inner_le_norm (𝕜 := ℂ) _ _)
  simp only [inner_toL2_toL2_eq _ _ volume, smulLeftCLM_apply_apply hw,
    smulLeftCLM_apply_apply hw']

/-- **The duality bound is attained.** For real Fourier weights with `w' ζ * w ζ = 1` and `w'` of
temperate growth, every Schwartz function `v` has a partner `u`, the Schwartz function with
`𝓕 u = w'² 𝓕 v`, such that `∫ ⟪u, v⟫ = ‖w' 𝓕 v‖²_{L²}` and `‖w 𝓕 u‖_{L²} = ‖w' 𝓕 v‖_{L²}`. -/
theorem exists_integral_inner_eq_and_eLpNorm_eq {w w' : E → ℝ}
    (hw' : (fun ζ ↦ (w' ζ : ℂ)).HasTemperateGrowth) (hww' : ∀ ζ, w' ζ * w ζ = 1)
    (v : 𝓢(E, F)) :
    ∃ u : 𝓢(E, F),
      ∫ x, ⟪u x, v x⟫_ℂ = (((eLpNorm (fun ζ ↦ (w' ζ : ℂ) • 𝓕 v ζ) 2 volume).toReal ^ 2 : ℝ) : ℂ) ∧
        (eLpNorm (fun ζ ↦ (w ζ : ℂ) • 𝓕 u ζ) 2 volume).toReal =
          (eLpNorm (fun ζ ↦ (w' ζ : ℂ) • 𝓕 v ζ) 2 volume).toReal := by
  set b := smulLeftCLM F (fun ζ ↦ (w' ζ : ℂ)) (𝓕 v)
  refine ⟨𝓕⁻ (smulLeftCLM F (fun ζ ↦ (w' ζ : ℂ)) b), ?_⟩
  -- The weighted Fourier transform of the partner is `w' 𝓕 v`, since `w' w = 1`.
  have hu (ζ : E) : (w ζ : ℂ) • 𝓕 (𝓕⁻ (smulLeftCLM F (fun ζ ↦ (w' ζ : ℂ)) b)) ζ = b ζ := by
    rw [fourier_fourierInv_eq, smulLeftCLM_apply_apply hw']
    simp [smul_smul, mul_comm (w ζ), hww']
  have hb (ζ : E) : (w' ζ : ℂ) • 𝓕 v ζ = b ζ := (smulLeftCLM_apply_apply hw' _ ζ).symm
  refine ⟨?_, by simp only [hu, hb]⟩
  simp_rw [integral_inner_eq_integral_inner_smul_fourier hww', hu, hb]
  rw [← inner_toL2_toL2_eq b b volume, inner_self_eq_norm_sq_to_K, norm_toLp, Complex.ofReal_pow]
  -- The two sides differ only by the eta-expansion `fun ζ ↦ b ζ` of `b`.
  rfl

/-- **A bound on the dual norm.** For real Fourier weights with `w' ζ * w ζ = 1`, `w'` of temperate
growth and `M ≥ 0`, if `‖∫ ⟪u, v⟫‖ ≤ M ‖w 𝓕 u‖_{L²}` for every Schwartz function `u`, then
`‖w' 𝓕 v‖_{L²} ≤ M`. -/
theorem eLpNorm_smul_fourier_le_of_forall_norm_integral_inner_le {w w' : E → ℝ}
    (hw' : (fun ζ ↦ (w' ζ : ℂ)).HasTemperateGrowth) (hww' : ∀ ζ, w' ζ * w ζ = 1) {M : ℝ}
    (hM : 0 ≤ M) {v : 𝓢(E, F)}
    (h : ∀ u : 𝓢(E, F),
      ‖∫ x, ⟪u x, v x⟫_ℂ‖ ≤ M * (eLpNorm (fun ζ ↦ (w ζ : ℂ) • 𝓕 u ζ) 2 volume).toReal) :
    (eLpNorm (fun ζ ↦ (w' ζ : ℂ) • 𝓕 v ζ) 2 volume).toReal ≤ M := by
  obtain ⟨u, hu, hnorm⟩ := exists_integral_inner_eq_and_eLpNorm_eq hw' hww' v
  have huv := h u
  rw [hu, hnorm, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at huv
  -- `N ^ 2 ≤ M N` with `N, M ≥ 0` forces `N ≤ M`.
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (fun ζ ↦ (w' ζ : ℂ) • 𝓕 v ζ) 2 volume)]

/-- **The dual norm of a weighted `L²` norm.** For real Fourier weights of temperate growth with
`w' ζ * w ζ = 1` and `M ≥ 0`, a Schwartz function `v` satisfies `‖w' 𝓕 v‖_{L²} ≤ M` exactly when
`‖∫ ⟪u, v⟫‖ ≤ M ‖w 𝓕 u‖_{L²}` for every Schwartz function `u`. -/
theorem eLpNorm_smul_fourier_le_iff_forall_norm_integral_inner_le {w w' : E → ℝ}
    (hw : (fun ζ ↦ (w ζ : ℂ)).HasTemperateGrowth) (hw' : (fun ζ ↦ (w' ζ : ℂ)).HasTemperateGrowth)
    (hww' : ∀ ζ, w' ζ * w ζ = 1) {M : ℝ} (hM : 0 ≤ M) (v : 𝓢(E, F)) :
    (eLpNorm (fun ζ ↦ (w' ζ : ℂ) • 𝓕 v ζ) 2 volume).toReal ≤ M ↔
      ∀ u : 𝓢(E, F),
        ‖∫ x, ⟪u x, v x⟫_ℂ‖ ≤ M * (eLpNorm (fun ζ ↦ (w ζ : ℂ) • 𝓕 u ζ) 2 volume).toReal := by
  refine ⟨fun h u ↦ (norm_integral_inner_le_of_mul_eq_one hw hw' hww' u v).trans ?_,
    eLpNorm_smul_fourier_le_of_forall_norm_integral_inner_le hw' hww' hM⟩
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg

/-- **Transpose bound with the same constant.** Let `(w₁, w₁')` and `(w₂, w₂')` be pairs of real
Fourier weights with `w₁' ζ * w₁ ζ = 1` and `w₂' ζ * w₂ ζ = 1`, and let `A'` be a formal adjoint of
`A` for the `L²` pairing of Schwartz functions. If `‖w₂ 𝓕 (A u)‖_{L²} ≤ C ‖w₁ 𝓕 u‖_{L²}` for every
`u`, then `‖w₁' 𝓕 (A' v)‖_{L²} ≤ C ‖w₂' 𝓕 v‖_{L²}` for every `v`. -/
theorem eLpNorm_smul_fourier_le_of_integral_inner_eq {w₁ w₁' w₂ w₂' : E → ℝ}
    (hw₁' : (fun ζ ↦ (w₁' ζ : ℂ)).HasTemperateGrowth) (hww₁ : ∀ ζ, w₁' ζ * w₁ ζ = 1)
    (hw₂ : (fun ζ ↦ (w₂ ζ : ℂ)).HasTemperateGrowth)
    (hw₂' : (fun ζ ↦ (w₂' ζ : ℂ)).HasTemperateGrowth) (hww₂ : ∀ ζ, w₂' ζ * w₂ ζ = 1)
    {A : 𝓢(E, F) → 𝓢(E, G)} {A' : 𝓢(E, G) → 𝓢(E, F)}
    (hA : ∀ u v, ∫ x, ⟪A u x, v x⟫_ℂ = ∫ x, ⟪u x, A' v x⟫_ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hAC : ∀ u, (eLpNorm (fun ζ ↦ (w₂ ζ : ℂ) • 𝓕 (A u) ζ) 2 volume).toReal ≤
      C * (eLpNorm (fun ζ ↦ (w₁ ζ : ℂ) • 𝓕 u ζ) 2 volume).toReal) (v : 𝓢(E, G)) :
    (eLpNorm (fun ζ ↦ (w₁' ζ : ℂ) • 𝓕 (A' v) ζ) 2 volume).toReal ≤
      C * (eLpNorm (fun ζ ↦ (w₂' ζ : ℂ) • 𝓕 v ζ) 2 volume).toReal := by
  -- By duality it suffices to bound `‖∫ ⟪u, A' v⟫‖ = ‖∫ ⟪A u, v⟫‖`.
  refine eLpNorm_smul_fourier_le_of_forall_norm_integral_inner_le hw₁' hww₁
    (mul_nonneg hC ENNReal.toReal_nonneg) fun u ↦ ?_
  rw [← hA, mul_right_comm]
  exact (norm_integral_inner_le_of_mul_eq_one hw₂ hw₂' hww₂ (A u) v).trans
    (mul_le_mul_of_nonneg_right (hAC u) ENNReal.toReal_nonneg)

end SchwartzMap
