/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Scattering
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.ODE.Gronwall.CoshSinh
import TauCeti.Analysis.ODE.Propagator.Backward

/-!
# The Dyson bounds for the scattering functions

Let `q` be integrable on `[0, t]` with `t ≥ 0`, let `L = ∫₀ᵗ |q|`, and let `z` be in the closed
upper half-plane. The scattering functions `a = (G_q)₂₂` and `b = (G_q)₂₁`
(`TauCeti.diracScatteringA`, `TauCeti.diracScatteringB`) satisfy

* `|a(t, z)| ≤ cosh L` and `|a(t, z) - 1| ≤ cosh L - 1`
  (`TauCeti.norm_diracScatteringA_le`, `TauCeti.norm_diracScatteringA_sub_one_le`);
* `|b(t, z)| ≤ sinh L` and `|b(t, z) - ∫₀ᵗ q(s) e^{2isz} ds| ≤ sinh L - L`
  (`TauCeti.norm_diracScatteringB_le`, `TauCeti.norm_diracScatteringB_sub_integral_le`).

## Implementation notes

The bottom row of `N(t, s)`, the propagator of the scattering coefficient from `s` to `t`, solves
the backward integral equation (`TauCeti.propagator_eq_one_add_integral_right`). With
`m(s) = N(t, s)₂₂` and `n(s) = e^{-2isz} N(t, s)₂₁` it reads
`n(s) = ∫ₛᵗ e^{2i(r - s)z} q(r) m(r) dr` and `m(s) = 1 + ∫ₛᵗ conj q(r) n(r) dr`. For `Im z ≥ 0` the
factor `e^{2i(r - s)z}` has modulus at most `1`, so `|n| ≤ ∫ₛᵗ |q| |m|` and
`|m| ≤ 1 + ∫ₛᵗ |q| |n|`, and the comparison with `cosh` and `sinh`
(`TauCeti.le_cosh_and_le_sinh_of_le_integral`) bounds them. At `s = 0`, `m(0) = a(t, z)` and
`n(0) = b(t, z)`. The roadmap routes the same bounds through the Dyson terms.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §5.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate intervalIntegral
open scoped Interval

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ} {z : ℂ}

/-- The `(i, j)` entry `(X e_j)_i` of an operator `X` on `ℂ²`. -/
private noncomputable def entryL (i j : Fin 2) :
    (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) →L[ℂ] ℂ :=
  (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace.single j 1))

private theorem entryL_apply (i j : Fin 2)
    (X : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    entryL i j X = X (EuclideanSpace.single j 1) i :=
  rfl

private theorem entryL_toEuclideanCLM (i j : Fin 2) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    entryL i j (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A) = A i j := by
  simp [entryL]

private theorem entryL_comp_toEuclideanCLM (i j : Fin 2)
    (X : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    entryL i j (X ∘L toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A) = ∑ k, entryL i k X * A k j := by
  have h : toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A (EuclideanSpace.single j 1) =
      ∑ k, A k j • EuclideanSpace.single k 1 := by
    ext l
    fin_cases l <;> simp [Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  simp only [entryL_apply, ContinuousLinearMap.comp_apply, h, map_sum, map_smul]
  simp [Fin.sum_univ_two, mul_comm]

/-- `|e^{2i u z}| ≤ 1` for `u ≥ 0` and `Im z ≥ 0`. -/
private theorem norm_exp_two_I_mul_le_one (hz : 0 ≤ z.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖exp (2 * I * (u * z))‖ ≤ 1 := by
  rw [norm_exp, Real.exp_le_one_iff]
  simp only [mul_re, re_ofNat, I_re, im_ofNat, I_im, ofReal_re, ofReal_im, mul_im]
  nlinarith

/-- The bottom-right entry `m(s) = N(t, s)₂₂` of the propagator from `s` to `t`. -/
private noncomputable def bm (q : ℝ → ℂ) (z : ℂ) (t s : ℝ) : ℂ :=
  entryL 1 1 (propagator (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (diracScatteringCoeff q z r)) t s)

/-- The rescaled bottom-left entry `n(s) = e^{-2isz} N(t, s)₂₁`. -/
private noncomputable def bn (q : ℝ → ℂ) (z : ℂ) (t s : ℝ) : ℂ :=
  exp (-2 * I * (s * z)) * entryL 1 0 (propagator (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (diracScatteringCoeff q z r)) t s)

/-- `m` and `n` are continuous on `[0, t]`. -/
private theorem continuousOn_bm_bn (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) :
    ContinuousOn (bm q z t) (Icc 0 t) ∧ ContinuousOn (bn q z t) (Icc 0 t) := by
  have hNc := continuousOn_propagator_right
    (integrableOn_toEuclideanCLM_diracScatteringCoeff hq z) (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  exact ⟨(entryL 1 1).continuous.comp_continuousOn hNc,
    (by fun_prop : Continuous fun s : ℝ ↦ exp (-2 * I * (s * z))).continuousOn.mul
      ((entryL 1 0).continuous.comp_continuousOn hNc)⟩

/-- **The backward equations of the bottom row.** For `s ∈ [0, t]`,
`m(s) = 1 + ∫ₛᵗ conj q(r) n(r) dr` and `n(s) = ∫ₛᵗ e^{2i(r - s)z} q(r) m(r) dr`. -/
private theorem bm_bn_eq (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) {s : ℝ}
    (hs : s ∈ Icc 0 t) :
    bm q z t s = 1 + ∫ r in s..t, conj (q r) * bn q z t r ∧
      bn q z t s = ∫ r in s..t, exp (2 * I * ((r - s) * z)) * q r * bm q z t r := by
  set P := fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z r)
  have hP : IntegrableOn P (Icc 0 t) := integrableOn_toEuclideanCLM_diracScatteringCoeff hq z
  have htt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  have hNP : IntervalIntegrable (fun r ↦ propagator P t r ∘L P r) volume s t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).2
      ((IntegrableOn.continuousOn_mul (continuousOn_propagator_right hP htt) hP
        isCompact_Icc).mono_set (Icc_subset_Icc_left hs.1))
  -- The entries of the backward integral equation.
  have hback (i j : Fin 2) : entryL i j (propagator P t s) = entryL i j 1 +
      ∫ r in s..t, ∑ k, entryL i k (propagator P t r) * diracScatteringCoeff q z r k j := by
    rw [propagator_eq_one_add_integral_right hP hs htt, map_add,
      ← (entryL i j).intervalIntegral_comp_comm hNP]
    simp only [P, entryL_comp_toEuclideanCLM]
  have hentry (r : ℝ) := (diracScatteringCoeff_def q z r ▸ (by simp :
    (!![(0 : ℂ), exp (-2 * I * (r * z)) * conj (q r); exp (2 * I * (r * z)) * q r, 0] 0 0 = 0 ∧
      !![(0 : ℂ), exp (-2 * I * (r * z)) * conj (q r); exp (2 * I * (r * z)) * q r, 0] 0 1 =
        exp (-2 * I * (r * z)) * conj (q r) ∧
      !![(0 : ℂ), exp (-2 * I * (r * z)) * conj (q r); exp (2 * I * (r * z)) * q r, 0] 1 0 =
        exp (2 * I * (r * z)) * q r ∧
      !![(0 : ℂ), exp (-2 * I * (r * z)) * conj (q r); exp (2 * I * (r * z)) * q r, 0] 1 1 = 0)))
  constructor
  · rw [bm, show entryL 1 1 _ = _ from hback 1 1, (show entryL 1 1 1 = 1 by simp [entryL_apply])]
    congr 1
    refine integral_congr fun r _ ↦ ?_
    simp only [Fin.sum_univ_two, (hentry r).2.1, (hentry r).2.2.2, mul_zero, add_zero, bn, P]
    ring
  · rw [bn, show entryL 1 0 _ = _ from hback 1 0, (show entryL 1 0 1 = 0 by simp [entryL_apply]),
      zero_add, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun r _ ↦ ?_
    have he : exp (2 * I * ((r - s) * z)) = exp (-2 * I * (s * z)) * exp (2 * I * (r * z)) := by
      rw [← exp_add]; ring_nf
    simp only [Fin.sum_univ_two, (hentry r).1, (hentry r).2.2.1, mul_zero, zero_add, bm, he, P]
    ring

/-- The core estimate: for every `s ∈ [0, t]`, `|m(s)| ≤ cosh Lₛ`, `|n(s)| ≤ sinh Lₛ` and
`|m(s) - 1| ≤ cosh Lₛ - 1`, where `Lₛ = ∫ₛᵗ |q|`. -/
private theorem bounds_aux (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (hz : 0 ≤ z.im) {s : ℝ}
    (hs : s ∈ Icc 0 t) :
    ‖bm q z t s‖ ≤ Real.cosh (∫ r in s..t, ‖q r‖) ∧ ‖bn q z t s‖ ≤ Real.sinh (∫ r in s..t, ‖q r‖) ∧
      ‖bm q z t s - 1‖ ≤ Real.cosh (∫ r in s..t, ‖q r‖) - 1 := by
  obtain ⟨hmc, hnc⟩ := continuousOn_bm_bn (z := z) hq ht
  have hqn : IntegrableOn (fun r ↦ ‖q r‖) (Icc 0 t) := hq.norm
  have hii {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 t)) {s : ℝ} (hs : s ∈ Icc 0 t) :
      IntervalIntegrable f volume s t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).2 (hf.mono_set (Icc_subset_Icc_left hs.1))
  have hmint := hqn.mul_continuousOn hmc.norm isCompact_Icc
  have hnint := hqn.mul_continuousOn hnc.norm isCompact_Icc
  have hnle (s : ℝ) (hs : s ∈ Icc 0 t) : ‖bn q z t s‖ ≤ ∫ r in s..t, ‖q r‖ * ‖bm q z t r‖ := by
    rw [(bm_bn_eq hq ht hs).2]
    refine norm_integral_le_of_norm_le hs.2 (ae_of_all _ fun r hr ↦ ?_) (hii hmint hs)
    rw [norm_mul, norm_mul]
    calc ‖exp (2 * I * ((r - s) * z))‖ * ‖q r‖ * ‖bm q z t r‖ ≤ 1 * ‖q r‖ * ‖bm q z t r‖ := by
          gcongr
          simpa using norm_exp_two_I_mul_le_one hz (sub_nonneg.2 hr.1.le)
      _ = ‖q r‖ * ‖bm q z t r‖ := by rw [one_mul]
  have hm1le (s : ℝ) (hs : s ∈ Icc 0 t) :
      ‖bm q z t s - 1‖ ≤ ∫ r in s..t, ‖q r‖ * ‖bn q z t r‖ := by
    rw [(bm_bn_eq hq ht hs).1, add_sub_cancel_left]
    refine norm_integral_le_of_norm_le hs.2 (ae_of_all _ fun r _ ↦ ?_) (hii hnint hs)
    rw [norm_mul, RCLike.norm_conj]
  have hmle (s : ℝ) (hs : s ∈ Icc 0 t) : ‖bm q z t s‖ ≤ 1 + ∫ r in s..t, ‖q r‖ * ‖bn q z t r‖ := by
    calc ‖bm q z t s‖ = ‖1 + (bm q z t s - 1)‖ := by rw [add_sub_cancel]
      _ ≤ 1 + ‖bm q z t s - 1‖ := (norm_add_le _ _).trans_eq (by rw [norm_one])
      _ ≤ _ := add_le_add le_rfl (hm1le s hs)
  have hcmp (s : ℝ) (hs : s ∈ Icc 0 t) := le_cosh_and_le_sinh_of_le_integral hqn
    (fun r ↦ norm_nonneg _) hmc.norm hnc.norm hmle hnle hs
  refine ⟨(hcmp s hs).1, (hcmp s hs).2, (hm1le s hs).trans ?_⟩
  -- `∫ₛᵗ |q| |n| ≤ ∫ₛᵗ |q| sinh L = cosh Lₛ - 1`.
  rw [cosh_integral_eq_one_add_integral hqn hs, add_sub_cancel_left]
  have hLc : ContinuousOn (fun r ↦ ∫ u in r..t, ‖q u‖) (Icc 0 t) := by
    simpa [uIcc_of_le ht] using
      continuousOn_primitive_interval_left (μ := volume) (a := 0) (b := t)
        (by rwa [uIcc_of_le ht])
  refine integral_mono_on hs.2 (hii hnint hs)
    (hii (hqn.mul_continuousOn (Real.continuous_sinh.comp_continuousOn hLc) isCompact_Icc) hs)
    fun r hr ↦ mul_le_mul_of_nonneg_left (hcmp r ⟨hs.1.trans hr.1, hr.2⟩).2 (norm_nonneg _)

/-- At `s = 0` the bottom row of `N(t, s)` is `(b(t, z), a(t, z))`. -/
private theorem entryL_propagator_zero (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    bm q z t 0 = diracScatteringA q t z ∧ bn q z t 0 = diracScatteringB q t z := by
  rw [bm, bn, ← toEuclideanCLM_diracScatteringMatrix, entryL_toEuclideanCLM,
    entryL_toEuclideanCLM]
  simp [diracScatteringA_def, diracScatteringB_def]

/-- **The Dyson bound for `a`.** For `q` integrable on `[0, t]` with `t ≥ 0` and `Im z ≥ 0`,
`|a(t, z)| ≤ cosh ∫₀ᵗ |q|`. -/
theorem norm_diracScatteringA_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (hz : 0 ≤ z.im) :
    ‖diracScatteringA q t z‖ ≤ Real.cosh (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [← (entryL_propagator_zero q t z).1]
  exact (bounds_aux hq ht hz ⟨le_rfl, ht⟩).1

/-- **The Dyson bound for `a - 1`.** For `q` integrable on `[0, t]` with `t ≥ 0` and `Im z ≥ 0`,
`|a(t, z) - 1| ≤ cosh (∫₀ᵗ |q|) - 1`. -/
theorem norm_diracScatteringA_sub_one_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (hz : 0 ≤ z.im) :
    ‖diracScatteringA q t z - 1‖ ≤ Real.cosh (∫ s in (0 : ℝ)..t, ‖q s‖) - 1 := by
  rw [← (entryL_propagator_zero q t z).1]
  exact (bounds_aux hq ht hz ⟨le_rfl, ht⟩).2.2

/-- **The Dyson bound for `b`.** For `q` integrable on `[0, t]` with `t ≥ 0` and `Im z ≥ 0`,
`|b(t, z)| ≤ sinh ∫₀ᵗ |q|`. -/
theorem norm_diracScatteringB_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (hz : 0 ≤ z.im) :
    ‖diracScatteringB q t z‖ ≤ Real.sinh (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [← (entryL_propagator_zero q t z).2]
  exact (bounds_aux hq ht hz ⟨le_rfl, ht⟩).2.1

/-- **The first-order Dyson bound for `b`.** For `q` integrable on `[0, t]` with `t ≥ 0` and
`Im z ≥ 0`, `|b(t, z) - ∫₀ᵗ q(s) e^{2isz} ds| ≤ sinh L - L` with `L = ∫₀ᵗ |q|`. -/
theorem norm_diracScatteringB_sub_integral_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (hz : 0 ≤ z.im) :
    ‖diracScatteringB q t z - ∫ s in (0 : ℝ)..t, q s * exp (2 * I * (s * z))‖ ≤
      Real.sinh (∫ s in (0 : ℝ)..t, ‖q s‖) - ∫ s in (0 : ℝ)..t, ‖q s‖ := by
  set m := bm q z t
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  have hmc : ContinuousOn m (Icc 0 t) := (continuousOn_bm_bn hq ht).1
  have hqn : IntegrableOn (fun r ↦ ‖q r‖) (Icc 0 t) := hq.norm
  have hLc : ContinuousOn (fun r ↦ ∫ u in r..t, ‖q u‖) (Icc 0 t) := by
    simpa [uIcc_of_le ht] using
      continuousOn_primitive_interval_left (μ := volume) (a := 0) (b := t)
        (by rwa [uIcc_of_le ht])
  have hii {f : ℝ → ℂ} (hf : IntegrableOn f (Icc 0 t)) : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hf
  have hiiR {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 t)) : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hf
  have he : ContinuousOn (fun r : ℝ ↦ exp (2 * I * (r * z))) (Icc 0 t) := by fun_prop
  -- `b - ∫ q e^{2isz} = ∫ e^{2isz} q (m - 1)`.
  have hb : diracScatteringB q t z - ∫ s in (0 : ℝ)..t, q s * exp (2 * I * (s * z)) =
      ∫ r in (0 : ℝ)..t, exp (2 * I * (r * z)) * q r * (m r - 1) := by
    rw [← (entryL_propagator_zero q t z).2, (bm_bn_eq hq ht h0).2]
    simp only [ofReal_zero, sub_zero]
    rw [← intervalIntegral.integral_sub]
    · refine integral_congr fun r _ ↦ ?_
      simp only [m]
      ring
    · exact hii ((IntegrableOn.continuousOn_mul he hq isCompact_Icc).mul_continuousOn hmc
        isCompact_Icc)
    · exact hii (hq.mul_continuousOn he isCompact_Icc)
  rw [hb, sinh_integral_eq_integral hqn h0]
  calc ‖∫ r in (0 : ℝ)..t, exp (2 * I * (r * z)) * q r * (m r - 1)‖
      ≤ ∫ r in (0 : ℝ)..t, ‖q r‖ * (Real.cosh (∫ u in r..t, ‖q u‖) - 1) := by
        refine norm_integral_le_of_norm_le ht (ae_of_all _ fun r hr ↦ ?_)
          (hiiR (hqn.mul_continuousOn
            ((Real.continuous_cosh.comp_continuousOn hLc).sub continuousOn_const) isCompact_Icc))
        have hr' : r ∈ Icc 0 t := Ioc_subset_Icc_self hr
        rw [norm_mul, norm_mul]
        calc ‖exp (2 * I * (r * z))‖ * ‖q r‖ * ‖m r - 1‖ ≤ 1 * ‖q r‖ * ‖m r - 1‖ := by
              gcongr; exact norm_exp_two_I_mul_le_one hz hr'.1
          _ ≤ ‖q r‖ * (Real.cosh (∫ u in r..t, ‖q u‖) - 1) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left (bounds_aux hq ht hz hr').2.2 (norm_nonneg _)
    _ = (∫ r in (0 : ℝ)..t, ‖q r‖ * Real.cosh (∫ u in r..t, ‖q u‖)) - ∫ r in (0 : ℝ)..t, ‖q r‖ := by
        simp_rw [mul_sub, mul_one]
        exact intervalIntegral.integral_sub
          (hiiR (hqn.mul_continuousOn (Real.continuous_cosh.comp_continuousOn hLc) isCompact_Icc))
          (hiiR hqn)

end TauCeti
