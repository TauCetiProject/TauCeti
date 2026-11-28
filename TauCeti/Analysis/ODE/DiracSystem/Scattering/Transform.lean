/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Scattering
import TauCeti.Analysis.ODE.Propagator.Translate
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Concatenation, translation, modulation and dilation of the scattering matrix

For a potential `q : ℝ → ℂ`, the scattering matrix `G_q(t, z)` (`TauCeti.diracScatteringMatrix`)
and the scattering functions `a = (G_q)₂₂`, `b = (G_q)₂₁` transform as follows, with the gauge
`D(s) = diag(e^{-isz}, e^{isz})`.

## Main results

* `TauCeti.diracScatteringMatrix_eq_mul`: **concatenation**, for `0, s, t` in an interval on
  which `q` is integrable,
  `G_q(t, z) = D(s) G_{q(s + ·)}(t - s, z) D(s)⁻¹ G_q(s, z)`; in terms of the scattering functions
  `(a₁, b₁)` of `q` at time `s` and `(a₂, b₂)` of `q(s + ·)` at time `t - s`,
  `b_q(t) = e^{2isz} b₂ a₁# + a₂ b₁` and `a_q(t) = e^{2isz} b₂ b₁# + a₂ a₁`
  (`TauCeti.diracScatteringB_eq_add`, `TauCeti.diracScatteringA_eq_add`);
* `TauCeti.diracScatteringMatrix_indicator_comp_sub`: **translation**, for `t₀ ≥ 0` and
  `q^{t₀}(u) = q(u - t₀) 1_{u ≥ t₀}`, `G_{q^{t₀}}(t + t₀, z) = D(t₀) G_q(t, z) D(t₀)⁻¹`, so
  `a_{q^{t₀}}(t + t₀, z) = a_q(t, z)` and `b_{q^{t₀}}(t + t₀, z) = e^{2it₀z} b_q(t, z)`;
* `TauCeti.diracScatteringMatrix_mul_exp`: **modulation**, `G_{q e^{2iξ·}}(t, z) = G_q(t, z + ξ)`
  for `ξ ∈ ℝ`;
* `TauCeti.diracScatteringMatrix_mul_comp_mul`: **dilation**, `G_{c q(c ·)}(t, z) = G_q(c t, z / c)`
  for every real `c`.

## Implementation notes

Modulation is an identity of coefficients. Concatenation is the cocycle identity of the
propagator together with `P(u + s) = D(s) P_{q(s + ·)}(u) D(s)⁻¹` for the scattering coefficient
`P`, translation of time (`TauCeti.propagator_comp_add_right`) and conjugation of the coefficient
(`TauCeti.propagator_mul_mul`). Dilation is `TauCeti.propagator_smul_comp_mul_left`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §5.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate
open scoped Matrix Interval

namespace TauCeti

variable {q : ℝ → ℂ} {a b c s t : ℝ}

/-- `e^{w s z} e^{w s z'} = e^{w s (z + z')}`, in the form used for the coefficients. -/
private theorem exp_mul_exp_mul (w z z' : ℂ) (s : ℝ) :
    exp (w * (s * z)) * exp (w * (s * z')) = exp (w * (s * (z + z'))) := by
  rw [← exp_add]; ring_nf

/-- `e^{2isz} = e^{isz} e^{isz}`. -/
private theorem exp_two_mul_I_mul (z : ℂ) (s : ℝ) :
    exp (2 * I * (s * z)) = exp (I * (s * z)) * exp (I * (s * z)) := by
  rw [exp_mul_exp_mul]; ring_nf

/-- The gauge `diag(e^{-isz}, e^{isz})` and `diag(e^{isz}, e^{-isz})` are mutually inverse. -/
private theorem gauge_mul_gauge (z : ℂ) (s : ℝ) :
    !![exp (-I * (s * z)), 0; 0, exp (I * (s * z))] *
      !![exp (I * (s * z)), 0; 0, exp (-I * (s * z))] = 1 ∧
    !![exp (I * (s * z)), 0; 0, exp (-I * (s * z))] *
      !![exp (-I * (s * z)), 0; 0, exp (I * (s * z))] = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [← exp_add]

/-- Conjugating by the gauge multiplies the lower left entry by `e^{2isz}`. -/
private theorem gauge_mul_mul_gauge_apply_one_zero (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (s : ℝ) :
    (!![exp (-I * (s * z)), 0; 0, exp (I * (s * z))] * M *
      !![exp (I * (s * z)), 0; 0, exp (-I * (s * z))]) 1 0 = exp (2 * I * (s * z)) * M 1 0 := by
  rw [exp_two_mul_I_mul, eta_fin_two M, mul_fin_two, mul_fin_two]
  simp only [of_apply, cons_val_one, cons_val_zero, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- Conjugating by the gauge leaves the lower right entry unchanged. -/
private theorem gauge_mul_mul_gauge_apply_one_one (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (s : ℝ) :
    (!![exp (-I * (s * z)), 0; 0, exp (I * (s * z))] * M *
      !![exp (I * (s * z)), 0; 0, exp (-I * (s * z))]) 1 1 = M 1 1 := by
  rw [eta_fin_two M, mul_fin_two, mul_fin_two]
  simp only [neg_mul, exp_neg, of_apply, cons_val_one, cons_val_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  field_simp

/-- **Modulation.** For `ξ ∈ ℝ`, `G_{q e^{2iξ·}}(t, z) = G_q(t, z + ξ)`. -/
theorem diracScatteringMatrix_mul_exp (q : ℝ → ℂ) (ξ t : ℝ) (z : ℂ) :
    diracScatteringMatrix (fun u ↦ q u * exp (2 * I * (u * ξ))) t z =
      diracScatteringMatrix q t (z + ξ) := by
  have h (u : ℝ) : diracScatteringCoeff (fun u ↦ q u * exp (2 * I * (u * ξ))) z u =
      diracScatteringCoeff q (z + ξ) u := by
    have hc : conj (exp (2 * I * (u * ξ))) = exp (-2 * I * (u * ξ)) := by
      rw [← exp_conj]; congr 1; simp [map_ofNat]
    have h1 : exp (-2 * I * (u * z)) * conj (q u * exp (2 * I * (u * ξ))) =
        exp (-2 * I * (u * (z + ξ))) * conj (q u) := by
      rw [map_mul, hc, ← exp_mul_exp_mul]; ring
    have h2 : exp (2 * I * (u * z)) * (q u * exp (2 * I * (u * ξ))) =
        exp (2 * I * (u * (z + ξ))) * q u := by
      rw [← exp_mul_exp_mul]; ring
    simp only [diracScatteringCoeff_def, h1, h2]
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  simp only [toEuclideanCLM_diracScatteringMatrix, h]

/-- **Modulation of `a`.** For `ξ ∈ ℝ`, `a_{q e^{2iξ·}}(t, z) = a_q(t, z + ξ)`. -/
theorem diracScatteringA_mul_exp (q : ℝ → ℂ) (ξ t : ℝ) (z : ℂ) :
    diracScatteringA (fun u ↦ q u * exp (2 * I * (u * ξ))) t z = diracScatteringA q t (z + ξ) := by
  rw [diracScatteringA_def, diracScatteringMatrix_mul_exp, diracScatteringA_def]

/-- **Modulation of `b`.** For `ξ ∈ ℝ`, `b_{q e^{2iξ·}}(t, z) = b_q(t, z + ξ)`. -/
theorem diracScatteringB_mul_exp (q : ℝ → ℂ) (ξ t : ℝ) (z : ℂ) :
    diracScatteringB (fun u ↦ q u * exp (2 * I * (u * ξ))) t z = diracScatteringB q t (z + ξ) := by
  rw [diracScatteringB_def, diracScatteringMatrix_mul_exp, diracScatteringB_def]

/-- **Concatenation.** If `q` is integrable on `[a, b]` and `0, s, t ∈ [a, b]`, then
`G_q(t, z) = D(s) G_{q(s + ·)}(t - s, z) D(s)⁻¹ G_q(s, z)` with `D(s) = diag(e^{-isz}, e^{isz})`. -/
theorem diracScatteringMatrix_eq_mul (hq : IntegrableOn q (Icc a b)) (h0 : 0 ∈ Icc a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (z : ℂ) :
    diracScatteringMatrix q t z =
      !![exp (-I * (s * z)), 0; 0, exp (I * (s * z))] *
        diracScatteringMatrix (fun u ↦ q (s + u)) (t - s) z *
          !![exp (I * (s * z)), 0; 0, exp (-I * (s * z))] * diracScatteringMatrix q s z := by
  set T := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  set D : Matrix (Fin 2) (Fin 2) ℂ := !![exp (-I * (s * z)), 0; 0, exp (I * (s * z))]
  set D' : Matrix (Fin 2) (Fin 2) ℂ := !![exp (I * (s * z)), 0; 0, exp (-I * (s * z))]
  set P : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun u ↦ T (diracScatteringCoeff q z u)
  set Ps : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun u ↦ T (diracScatteringCoeff (fun u ↦ q (s + u)) z u)
  have hP : IntegrableOn P (Icc a b) := integrableOn_toEuclideanCLM_diracScatteringCoeff hq z
  have hPs : IntegrableOn Ps (Icc (a - s) (b - s)) := by
    refine integrableOn_toEuclideanCLM_diracScatteringCoeff ?_ z
    simpa only [add_comm s] using hq.comp_add_right_Icc s
  have hDD' : T D * T D' = 1 := by rw [← map_mul, (gauge_mul_gauge z s).1, map_one]
  have hD'D : T D' * T D = 1 := by rw [← map_mul, (gauge_mul_gauge z s).2, map_one]
  -- The translated coefficient is the gauge conjugate of the coefficient of `q(s + ·)`.
  have hshift : (fun u ↦ P (u + s)) = fun u ↦ T D * Ps u * T D' := by
    ext1 u
    simp only [P, Ps, ← map_mul]
    congr 1
    have he (w : ℂ) : exp (2 * w * (↑(u + s) * z)) =
        exp (w * (s * z)) * exp (2 * w * (u * z)) * exp (w * (s * z)) := by
      rw [mul_right_comm, ← exp_add, ← exp_add]; push_cast; ring_nf
    have he' := he (-I)
    simp only [show 2 * -I = -2 * I by ring] at he'
    simp only [D, D', diracScatteringCoeff_def, mul_fin_two, he I, he', add_comm s u, mul_zero,
      zero_mul, add_zero, zero_add]
    ring_nf
  have h0' : (0 : ℝ) ∈ Icc (a - s) (b - s) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : t - s ∈ Icc (a - s) (b - s) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  apply EquivLike.injective T
  rw [map_mul, map_mul, map_mul, toEuclideanCLM_diracScatteringMatrix,
    toEuclideanCLM_diracScatteringMatrix, toEuclideanCLM_diracScatteringMatrix,
    ← propagator_mul_mul hPs h0' ht' hDD' hD'D, ← hshift, propagator_comp_add_right hP h0' ht',
    sub_add_cancel, zero_add, ContinuousLinearMap.mul_def,
    propagator_comp_propagator hP hs h0 ht]

/-- **Concatenation of `b`.** If `q` is integrable on `[0, t]` and `s ∈ [0, t]`, then
`b_q(t, z) = e^{2isz} b₂(t - s, z) a₁#(s, z) + a₂(t - s, z) b₁(s, z)`, where `(a₁, b₁)` are the
scattering functions of `q`, `(a₂, b₂)` those of `q(s + ·)`, and
`a₁#(s, z) = conj a₁(s, conj z)`. -/
theorem diracScatteringB_eq_add (hq : IntegrableOn q (Icc 0 t)) (hs : s ∈ Icc 0 t) (z : ℂ) :
    diracScatteringB q t z =
      exp (2 * I * (s * z)) * diracScatteringB (fun u ↦ q (s + u)) (t - s) z *
          conj (diracScatteringA q s (conj z)) +
        diracScatteringA (fun u ↦ q (s + u)) (t - s) z * diracScatteringB q s z := by
  have hqs : IntegrableOn q (Icc 0 s) := hq.mono_set (Icc_subset_Icc_right hs.2)
  rw [diracScatteringB_def, diracScatteringMatrix_eq_mul hq ⟨le_rfl, hs.1.trans hs.2⟩ hs
    ⟨hs.1.trans hs.2, le_rfl⟩, Matrix.mul_apply, Fin.sum_univ_two,
    gauge_mul_mul_gauge_apply_one_zero, gauge_mul_mul_gauge_apply_one_one,
    diracScatteringMatrix_apply_zero_zero hqs hs.1]
  simp only [diracScatteringA_def, diracScatteringB_def]

/-- **Concatenation of `a`.** If `q` is integrable on `[0, t]` and `s ∈ [0, t]`, then
`a_q(t, z) = e^{2isz} b₂(t - s, z) b₁#(s, z) + a₂(t - s, z) a₁(s, z)`, where `(a₁, b₁)` are the
scattering functions of `q`, `(a₂, b₂)` those of `q(s + ·)`, and
`b₁#(s, z) = conj b₁(s, conj z)`. -/
theorem diracScatteringA_eq_add (hq : IntegrableOn q (Icc 0 t)) (hs : s ∈ Icc 0 t) (z : ℂ) :
    diracScatteringA q t z =
      exp (2 * I * (s * z)) * diracScatteringB (fun u ↦ q (s + u)) (t - s) z *
          conj (diracScatteringB q s (conj z)) +
        diracScatteringA (fun u ↦ q (s + u)) (t - s) z * diracScatteringA q s z := by
  have hqs : IntegrableOn q (Icc 0 s) := hq.mono_set (Icc_subset_Icc_right hs.2)
  rw [diracScatteringA_def, diracScatteringMatrix_eq_mul hq ⟨le_rfl, hs.1.trans hs.2⟩ hs
    ⟨hs.1.trans hs.2, le_rfl⟩, Matrix.mul_apply, Fin.sum_univ_two,
    gauge_mul_mul_gauge_apply_one_zero, gauge_mul_mul_gauge_apply_one_one,
    diracScatteringMatrix_apply_zero_one hqs hs.1]
  simp only [diracScatteringA_def, diracScatteringB_def]

/-- **Translation of the potential.** If `q` is integrable on `[0, t]`, `t ≥ 0` and `t₀ ≥ 0`, then
the potential `q^{t₀}(u) = q(u - t₀) 1_{u ≥ t₀}` has
`G_{q^{t₀}}(t + t₀, z) = D(t₀) G_q(t, z) D(t₀)⁻¹` with `D(t₀) = diag(e^{-it₀z}, e^{it₀z})`. -/
theorem diracScatteringMatrix_indicator_comp_sub (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (z : ℂ) :
    diracScatteringMatrix ((Ici t₀).indicator fun u ↦ q (u - t₀)) (t + t₀) z =
      !![exp (-I * (t₀ * z)), 0; 0, exp (I * (t₀ * z))] * diracScatteringMatrix q t z *
        !![exp (I * (t₀ * z)), 0; 0, exp (-I * (t₀ * z))] := by
  set q' := (Ici t₀).indicator fun u ↦ q (u - t₀)
  have hq' : IntegrableOn q' (Icc 0 (t + t₀)) := by
    have h := hq.comp_add_right_Icc (-t₀)
    simp only [sub_neg_eq_add, zero_add, ← sub_eq_add_neg] at h
    have hset : Ici t₀ ∩ Icc 0 (t + t₀) = Icc t₀ (t + t₀) := by
      ext u
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ht₀.trans h.1, h.2⟩⟩
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ici, hset]
    exact h
  have hs : t₀ ∈ Icc 0 (t + t₀) := ⟨ht₀, by linarith⟩
  -- Up to time `t₀` the potential vanishes almost everywhere.
  have hone : diracScatteringMatrix q' t₀ z = 1 := by
    rw [diracScatteringMatrix_eq_of_ae_eq_zero (hq'.mono_set (Icc_subset_Icc_right hs.2))
      (T := 0) ⟨le_rfl, ht₀⟩ ?_ z, diracScatteringMatrix_zero]
    filter_upwards [Measure.ae_ne volume t₀] with u hu hmem
    exact indicator_of_notMem (fun h ↦ hu (le_antisymm hmem.2 h)) _
  -- After time `t₀` it is the translate of `q`.
  have hshift : diracScatteringMatrix (fun u ↦ q' (t₀ + u)) (t + t₀ - t₀) z =
      diracScatteringMatrix q t z := by
    rw [add_sub_cancel_right]
    refine diracScatteringMatrix_congr_ae (ae_of_all _ fun u hu ↦ ?_) z
    rw [uIoc_of_le ht] at hu
    simp only [q', indicator_of_mem (show t₀ + u ∈ Ici t₀ by simp [hu.1.le]),
      add_sub_cancel_left]
  rw [diracScatteringMatrix_eq_mul hq' ⟨le_rfl, hs.1.trans hs.2⟩ hs ⟨hs.1.trans hs.2, le_rfl⟩,
    hshift, hone, mul_one]

/-- **Translation of `a`.** If `q` is integrable on `[0, t]`, `t ≥ 0` and `t₀ ≥ 0`, then
`a_{q^{t₀}}(t + t₀, z) = a_q(t, z)` for `q^{t₀}(u) = q(u - t₀) 1_{u ≥ t₀}`. -/
theorem diracScatteringA_indicator_comp_sub (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (z : ℂ) :
    diracScatteringA ((Ici t₀).indicator fun u ↦ q (u - t₀)) (t + t₀) z =
      diracScatteringA q t z := by
  rw [diracScatteringA_def, diracScatteringMatrix_indicator_comp_sub hq ht ht₀,
    gauge_mul_mul_gauge_apply_one_one, diracScatteringA_def]

/-- **Translation of `b`.** If `q` is integrable on `[0, t]`, `t ≥ 0` and `t₀ ≥ 0`, then
`b_{q^{t₀}}(t + t₀, z) = e^{2it₀z} b_q(t, z)` for `q^{t₀}(u) = q(u - t₀) 1_{u ≥ t₀}`. -/
theorem diracScatteringB_indicator_comp_sub (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (z : ℂ) :
    diracScatteringB ((Ici t₀).indicator fun u ↦ q (u - t₀)) (t + t₀) z =
      exp (2 * I * (t₀ * z)) * diracScatteringB q t z := by
  rw [diracScatteringB_def, diracScatteringMatrix_indicator_comp_sub hq ht ht₀,
    gauge_mul_mul_gauge_apply_one_zero, diracScatteringB_def]

/-- **Dilation.** If `q` is integrable between `0` and `c t` for a real `c`, then
`G_{c q(c ·)}(t, z) = G_q(c t, z / c)`. -/
theorem diracScatteringMatrix_mul_comp_mul (hq : IntegrableOn q (uIcc 0 (c * t))) (z : ℂ) :
    diracScatteringMatrix (fun u ↦ (c : ℂ) * q (c * u)) t z =
      diracScatteringMatrix q (c * t) (z / c) := by
  set T := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  have hcoeff : (fun u ↦ T (diracScatteringCoeff (fun u ↦ (c : ℂ) * q (c * u)) z u)) =
      fun u ↦ (c : ℂ) • T (diracScatteringCoeff q (z / c) (c * u)) := by
    ext1 u
    rw [← map_smul]
    congr 1
    rcases eq_or_ne c 0 with rfl | hc
    · simp [diracScatteringCoeff_def, ← Matrix.ext_iff, Fin.forall_fin_two]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hz : ((c * u : ℝ) : ℂ) * (z / c) = u * z := by
      push_cast
      field_simp
    have hcc : conj (c : ℂ) = c := conj_ofReal c
    simp only [diracScatteringCoeff_def, hz, map_mul, hcc, smul_of, smul_cons, Matrix.smul_empty,
      smul_eq_mul]
    congr 1
    ring_nf
  apply EquivLike.injective T
  simp only [T, toEuclideanCLM_diracScatteringMatrix]
  rw [hcoeff]
  exact (propagator_smul_comp_mul_left
    (integrableOn_toEuclideanCLM_diracScatteringCoeff hq (z / c)) c (by simp) right_mem_uIcc).trans
      (by rw [mul_zero])

/-- **Dilation of `a`.** If `q` is integrable between `0` and `c t` for a real `c`, then
`a_{c q(c ·)}(t, z) = a_q(c t, z / c)`. -/
theorem diracScatteringA_mul_comp_mul (hq : IntegrableOn q (uIcc 0 (c * t))) (z : ℂ) :
    diracScatteringA (fun u ↦ (c : ℂ) * q (c * u)) t z = diracScatteringA q (c * t) (z / c) := by
  rw [diracScatteringA_def, diracScatteringMatrix_mul_comp_mul hq, diracScatteringA_def]

/-- **Dilation of `b`.** If `q` is integrable between `0` and `c t` for a real `c`, then
`b_{c q(c ·)}(t, z) = b_q(c t, z / c)`. -/
theorem diracScatteringB_mul_comp_mul (hq : IntegrableOn q (uIcc 0 (c * t))) (z : ℂ) :
    diracScatteringB (fun u ↦ (c : ℂ) * q (c * u)) t z = diracScatteringB q (c * t) (z / c) := by
  rw [diracScatteringB_def, diracScatteringMatrix_mul_comp_mul hq, diracScatteringB_def]

end TauCeti
