/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Function.Lp.Integral.L2NormSq

/-!
# Rellich compactness on `(0, π)`: `sin (j x) / j` against `sin (j x)`

Rellich's theorem says that a sequence bounded in `H¹(0, π)` has a subsequence converging in
`L²(0, π)`. The two sequences of this file show what the hypothesis and the conclusion say.

* **A sequence bounded in `H¹`.** For `j ≥ 1`, `u_j(x) = sin (j x) / j` lies in `H¹(0, π)` with
  `‖u_j‖² = π / (2 j²)` and `‖u_j'‖² = ‖cos (j x)‖² = π / 2`
  (`TauCeti.Examples.SineRellich.norm_value_sq_eq_and_norm_gradient_sq_eq`). So the sequence is
  bounded in `H¹(0, π)`, and it converges to `0` in `L²(0, π)`
  (`TauCeti.Examples.SineRellich.exists_tendsto_value_nhds_zero`), as Rellich predicts.
* **A sequence bounded only in `L²`.** The sine modes `v_j(x) = sin (j x)` are orthogonal in
  `L²(0, π)`, each of squared norm `π / 2`, so any two distinct modes with `j, k ≥ 1` are at
  distance `‖v_j - v_k‖ = √π` (`TauCeti.Examples.SineRellich.norm_sub_sq_eq`). Hence no
  subsequence is Cauchy, let alone convergent
  (`TauCeti.Examples.SineRellich.not_cauchySeq_comp`). The `v_j = j u_j` are themselves values of
  classes of `H¹(0, π)`, but their gradients `j cos (j x)` have squared norms `j² π / 2`, unbounded
  in `j` (`TauCeti.Examples.SineRellich.exists_value_ae_eq_sin_and_not_cauchySeq`): the compactness
  in Rellich's theorem genuinely uses the bound on the gradient.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.8 (Rellich–Kondrachov on an interval).
-/

public section

open Filter MeasureTheory Real Set Topology

namespace TauCeti.Examples.SineRellich

open W1p

/-! ### Trigonometric integrals over `[0, π]` -/

/-- `∫_0^π sin (j x)² = π / 2` for every positive integer `j`. -/
private theorem integral_sin_nat_mul_sq {j : ℕ} (hj : j ≠ 0) :
    ∫ x in (0 : ℝ)..π, sin (j * x) ^ 2 = π / 2 := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  rw [intervalIntegral.integral_comp_mul_left (fun x => sin x ^ 2) hj', integral_sin_sq]
  simp [Real.sin_nat_mul_pi]
  field_simp

/-- `∫_0^π cos (j x)² = π / 2` for every positive integer `j`. -/
private theorem integral_cos_nat_mul_sq {j : ℕ} (hj : j ≠ 0) :
    ∫ x in (0 : ℝ)..π, cos (j * x) ^ 2 = π / 2 := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x ^ 2) hj', integral_cos_sq]
  simp [Real.sin_nat_mul_pi]
  field_simp

/-- `∫_0^π cos (m x) = 0` for every nonzero integer `m`. -/
private theorem integral_cos_int_mul {m : ℤ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..π, cos (m * x) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hm', integral_cos]
  simp [Real.sin_int_mul_pi]

/-- **Orthogonality of the sine modes.** `∫_0^π sin (j x) sin (k x) = 0` for distinct natural
numbers `j` and `k`. -/
private theorem integral_sin_nat_mul_mul_sin_nat_mul {j k : ℕ} (hjk : j ≠ k) :
    ∫ x in (0 : ℝ)..π, sin (j * x) * sin (k * x) = 0 := by
  -- `sin a sin b = (cos (a - b) - cos (a + b)) / 2`, and both frequencies are nonzero integers.
  have h : ∀ x : ℝ, sin (j * x) * sin (k * x) =
      (cos (((j - k : ℤ) : ℝ) * x) - cos (((j + k : ℤ) : ℝ) * x)) / 2 := fun x => by
    push_cast
    rw [sub_mul, add_mul, cos_sub, cos_add]
    ring
  have h₁ : (j - k : ℤ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hjk)
  have h₂ : (j + k : ℤ) ≠ 0 := by omega
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_int_mul h₁,
    integral_cos_int_mul h₂]
  simp

/-! ### The sequence `sin (j x) / j` -/

/-- For `j ≥ 1`, `sin (j x) / j` is the value of a class of `H¹(0, π)` whose weak gradient is
`cos (j x)`. -/
theorem exists_value_ae_eq_sin_div {j : ℕ} (hj : j ≠ 0) :
    ∃ u : W1p volume ⟨Ioo (0 : ℝ) π, isOpen_Ioo⟩ 2,
      value u =ᵐ[volume.restrict (Ioo 0 π)] (fun x => sin (j * x) / j) ∧
      gradient u =ᵐ[volume.restrict (Ioo 0 π)] fun x => cos (j * x) := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  obtain ⟨u, -, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff (p := 2) pi_pos
    (f := fun x : ℝ => sin (j * x) / j) (by fun_prop)
  refine ⟨u, hv, hg.trans (Filter.Eventually.of_forall fun x => ?_)⟩
  exact (((hasDerivAt_id' x).const_mul (j : ℝ)).sin.div_const (j : ℝ)).deriv.trans
    (by field_simp)

/-- For `j ≥ 1`, a class of `H¹(0, π)` with value `sin (j x) / j` has weak gradient `cos (j x)`. -/
private theorem gradient_ae_eq_cos {j : ℕ} (hj : j ≠ 0)
    {u : W1p volume ⟨Ioo (0 : ℝ) π, isOpen_Ioo⟩ 2}
    (hv : value u =ᵐ[volume.restrict (Ioo 0 π)] (fun x => sin (j * x) / j)) :
    gradient u =ᵐ[volume.restrict (Ioo 0 π)] fun x => cos (j * x) := by
  obtain ⟨w, hw, hg⟩ := exists_value_ae_eq_sin_div hj
  rwa [W1p.ext_value (Lp.ext (hv.trans hw.symm))]

/-- For `j ≥ 1`, a class of `H¹(0, π)` with value `sin (j x) / j`, hence with weak gradient
`cos (j x)`, has `‖u‖² = π / (2 j²)` and `‖u'‖² = π / 2`. -/
theorem norm_value_sq_eq_and_norm_gradient_sq_eq {j : ℕ} (hj : j ≠ 0)
    {u : W1p volume ⟨Ioo (0 : ℝ) π, isOpen_Ioo⟩ 2}
    (hv : value u =ᵐ[volume.restrict (Ioo 0 π)] (fun x => sin (j * x) / j)) :
    ‖value u‖ ^ 2 = π / (2 * j ^ 2) ∧ ‖gradient u‖ ^ 2 = π / 2 := by
  refine ⟨?_,
    (norm_gradient_sq_eq_intervalIntegral_of_ae_eq pi_pos (gradient_ae_eq_cos hj hv)).trans
    (integral_cos_nat_mul_sq hj)⟩
  rw [norm_value_sq_eq_intervalIntegral_of_ae_eq pi_pos hv]
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, integral_sin_nat_mul_sq hj]
  field_simp

/-- **The sequence `sin (j x) / j` converges in `L²`.** There are classes `u_j` of `H¹(0, π)`,
`j ≥ 1`, with values `sin (j x) / j` and weak gradients `cos (j x)`, bounded in `H¹(0, π)` since
`‖u_j'‖² = π / 2`, whose values converge to `0` in `L²(0, π)`. -/
theorem exists_tendsto_value_nhds_zero :
    ∃ u : ℕ → W1p volume ⟨Ioo (0 : ℝ) π, isOpen_Ioo⟩ 2,
      (∀ j ≠ 0, value (u j) =ᵐ[volume.restrict (Ioo 0 π)] (fun x => sin (j * x) / j) ∧
        gradient (u j) =ᵐ[volume.restrict (Ioo 0 π)] fun x => cos (j * x)) ∧
      (∀ j ≠ 0, ‖gradient (u j)‖ ^ 2 = π / 2) ∧
      Tendsto (fun j => value (u j)) atTop (𝓝 0) := by
  choose! u hu using fun (j : ℕ) (hj : j ≠ 0) => exists_value_ae_eq_sin_div hj
  have hnorm (j : ℕ) (hj : j ≠ 0) : ‖value (u j)‖ = √(π / 2) / j := by
    rw [← Real.sqrt_sq (norm_nonneg _),
      (norm_value_sq_eq_and_norm_gradient_sq_eq hj (hu j hj).1).1,
      show π / (2 * (j : ℝ) ^ 2) = (π / 2) / (j : ℝ) ^ 2 by ring,
      Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg j)]
  refine ⟨u, hu, fun j hj => (norm_value_sq_eq_and_norm_gradient_sq_eq hj (hu j hj).1).2,
    tendsto_zero_iff_norm_tendsto_zero.2 ?_⟩
  refine (tendsto_const_div_atTop_nhds_zero_nat (√(π / 2))).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with j hj
  exact (hnorm j hj).symm

/-! ### The sine modes -/

/-- **The sine modes are at distance `√π`.** In `L²(0, π)`, classes with values `sin (j x)` and
`sin (k x)`, for distinct positive integers `j` and `k`, satisfy `‖v_j - v_k‖² = π`, while
`‖v_j‖² = π / 2`. -/
theorem norm_sub_sq_eq {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) (hjk : j ≠ k)
    {f g : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) π))}
    (hf : f =ᵐ[volume.restrict (Ioo 0 π)] fun x => sin (j * x))
    (hg : g =ᵐ[volume.restrict (Ioo 0 π)] fun x => sin (k * x)) :
    ‖f - g‖ ^ 2 = π := by
  rw [L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq pi_pos.le ((Lp.coeFn_sub f g).trans (hf.sub hg))]
  have h : ∀ x : ℝ, ((fun x => sin (j * x)) - fun x => sin (k * x)) x ^ 2 =
      sin (j * x) ^ 2 + sin (k * x) ^ 2 - 2 * (sin (j * x) * sin (k * x)) := fun x => by
    simp only [Pi.sub_apply]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, integral_sin_nat_mul_sq hj, integral_sin_nat_mul_sq hk,
    integral_sin_nat_mul_mul_sin_nat_mul hjk]
  ring

/-- **No subsequence of the sine modes is Cauchy in `L²`.** If `v_j` has value `sin (j x)` in
`L²(0, π)` for every `j`, then `j ↦ v_{φ j}` is not a Cauchy sequence for any strictly increasing
`φ`, although `‖v_j‖² = π / 2` for `j ≥ 1`. -/
theorem not_cauchySeq_comp {v : ℕ → Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) π))}
    (hv : ∀ j, v j =ᵐ[volume.restrict (Ioo 0 π)] fun x => sin (j * x)) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : ¬ CauchySeq (v ∘ φ) := by
  intro h
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 h (√π) (Real.sqrt_pos.2 pi_pos)
  -- The modes `φ (N + 1)` and `φ (N + 2)` are distinct and positive.
  have h₁ : φ (N + 1) ≠ 0 := (Nat.zero_le _).trans_lt (hφ (Nat.lt_succ_self N)) |>.ne'
  have h₂ : φ (N + 2) ≠ 0 := (Nat.zero_le _).trans_lt (hφ (by omega : N < N + 2)) |>.ne'
  have h₁₂ : φ (N + 1) ≠ φ (N + 2) := hφ.injective.ne (by omega)
  have hd := hN (N + 1) (by omega) (N + 2) (by omega)
  rw [Function.comp_apply, Function.comp_apply, dist_eq_norm,
    ← Real.sqrt_sq (norm_nonneg _), norm_sub_sq_eq h₁ h₂ h₁₂ (hv _) (hv _)] at hd
  exact lt_irrefl _ hd

/-- **The sine modes are values of classes with unbounded gradients.** There are classes `w_j` of
`H¹(0, π)` with values `sin (j x)` whose gradients have squared norms `j² π / 2`, and no
subsequence of their values is Cauchy in `L²(0, π)`. -/
theorem exists_value_ae_eq_sin_and_not_cauchySeq :
    ∃ w : ℕ → W1p volume ⟨Ioo (0 : ℝ) π, isOpen_Ioo⟩ 2,
      (∀ j, value (w j) =ᵐ[volume.restrict (Ioo 0 π)] fun x => sin (j * x)) ∧
      (∀ j ≠ 0, ‖gradient (w j)‖ ^ 2 = j ^ 2 * π / 2) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ¬ CauchySeq fun j => value (w (φ j)) := by
  have h (j : ℕ) : ∃ w : W1p volume ⟨Ioo (0 : ℝ) π, isOpen_Ioo⟩ 2,
      value w =ᵐ[volume.restrict (Ioo 0 π)] (fun x => sin (j * x)) ∧
      gradient w =ᵐ[volume.restrict (Ioo 0 π)] fun x => j * cos (j * x) := by
    obtain ⟨w, -, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff (p := 2) pi_pos
      (f := fun x : ℝ => sin (j * x)) (by fun_prop)
    refine ⟨w, hv, hg.trans (Filter.Eventually.of_forall fun x => ?_)⟩
    exact (((hasDerivAt_id' x).const_mul (j : ℝ)).sin).deriv.trans (by ring)
  choose w hw using h
  refine ⟨w, fun j => (hw j).1, fun j hj => ?_, fun φ hφ =>
    not_cauchySeq_comp (v := fun j => value (w j)) (fun j => (hw j).1) hφ⟩
  rw [norm_gradient_sq_eq_intervalIntegral_of_ae_eq pi_pos (hw j).2]
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_cos_nat_mul_sq hj]
  ring

end TauCeti.Examples.SineRellich
