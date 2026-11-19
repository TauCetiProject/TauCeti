/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.AmplitudeForm
public import TauCeti.Analysis.PDE.Vortex.Decay
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Algebra.Order.BigOperators.GroupWithZero.Multiset
import TauCeti.Algebra.Order.BigOperators.Ring.Multiset
import TauCeti.Analysis.Complex.LogOneAddNormSq
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# A lower bound for the modulus of a plane vortex in terms of its zeros

Let `x` be a smooth plane vortex with the degree-`m` end framing and zero divisor `D`, a multiset
of `m` points of `ℂ`, and write `α` for its section. This file proves the explicit lower bound

`|α(z)|² ≥ ∏_{a ∈ D} ‖z - a‖² / (‖z - a‖² + C)`  for every `C > 16 m`

(`TauCeti.Vortex.prod_div_le_normSq`). It depends on the vortex only through its zeros, so it is
uniform over all vortices whose zeros lie in a prescribed compact set: the modulus is close to one
at a definite distance from the divisor, with constants depending only on `m`. Three consequences
are drawn.

* **Polynomial decay.** `1 - |α(z)|² ≤ ∑_{a ∈ D} C / (‖z - a‖² + C)`
  (`TauCeti.Vortex.one_sub_normSq_le_sum`), by `1 - ∏ (1 - tₐ) ≤ ∑ tₐ`.
* **Zero localization.** A point where `|α|² ≤ θ < 1` lies near the divisor:
  `(1 - θ) ‖z - a‖² < m C` for some `a ∈ D`
  (`TauCeti.Vortex.exists_mem_mul_norm_sub_sq_lt`).
* **Uniform exponential decay.** For every rate `c < 1 / 2` and radius `R₀` there is one
  constant `K`, depending only on `m`, `R₀` and `c`, with `1 - |α(z)|² ≤ K exp (-c |z|)` for every
  such vortex whose zeros lie in the closed disc of radius `R₀`
  (`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp_of_forall_mem_norm_le`). For a single vortex
  this is `TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`; the point here is that the constant is
  uniform over a compact window of divisors. The lower bound gives `|α|² ≥ (1 + 4 c²) / 2`
  outside an explicit radius depending only on `m`, `R₀` and `c`, which is the input of the
  exterior comparison `TauCeti.Vortex.one_sub_normSq_le_neg_log_mul_exp`.

## The comparison argument

By `TauCeti.Vortex.exists_framedGaugeGroup_smul_amplitudeField_eq` the vortex is gauge equivalent
to an amplitude field with section `exp(u) f`, `f(z) = ∏_{a ∈ D} (z - a)`, where `u` solves the
regularized scalar equation `Δu = (exp(2u) |f|² - 1) / 8` and `u + m log |z| → 0`. The lower bound
says `u ≥ v` for the comparison function

`v(z) = -(1 / 2) ∑_{a ∈ D} log (‖z - a‖² + C)`,

since `exp(2v) |f|² = ∏ ‖z - a‖² / (‖z - a‖² + C)`
(`TauCeti.Vortex.prod_div_le_exp_two_mul_mul_norm_prod_sq`). Both `v + m log |z|` and
`u + m log |z|` tend to zero, so `v - u` tends to zero at infinity, and by the whole-plane maximum
principle `TauCeti.nonpos_of_tendsto_cocompact_of_laplacian_nonneg` it suffices that `Δu < Δv`
wherever `u < v`. With `tₐ = C / (‖z - a‖² + C) ∈ (0, 1]`,

`Δv = -(2 / C) ∑ tₐ²`,    `Δu ≤ (∏ (1 - tₐ) - 1) / 8`

at such a point. Each `tₐ` is at most `1 - ∏ (1 - t_b)`, so `∑ tₐ² ≤ m (1 - ∏ (1 - tₐ))`, and
`C > 16 m` turns these into `Δu < Δv`. (Where `f` vanishes `Δu = -1 / 8`, while
`Δv ≥ -2 m / C > -1 / 8`.)

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology InnerProductSpace Laplacian
open scoped ContDiff

/-! ### The comparison function -/

/-- The function `z ↦ ∑_{a ∈ D} log (‖z - a‖² + C)` is `C²`, with Laplacian
`∑_{a ∈ D} 4 C / (‖z - a‖² + C)²`. -/
private theorem contDiff_sum_log_and_laplacian {C : ℝ} (hC : 0 < C) (D : Multiset ℂ) :
    ContDiff ℝ 2 (fun w : ℂ ↦ (D.map fun a ↦ Real.log (‖w - a‖ ^ 2 + C)).sum) ∧
      ∀ z, Δ (fun w : ℂ ↦ (D.map fun a ↦ Real.log (‖w - a‖ ^ 2 + C)).sum) z =
        (D.map fun a ↦ 4 * C / (‖z - a‖ ^ 2 + C) ^ 2).sum := by
  induction D using Multiset.induction_on with
  | empty => simp [contDiff_const]
  | cons b D ih =>
    have hb : ContDiff ℝ 2 (fun w : ℂ ↦ Real.log (‖w - b‖ ^ 2 + C)) :=
      (((contDiff_id.sub contDiff_const).norm_sq ℝ).add contDiff_const).log fun w ↦ by positivity
    have heq : (fun w : ℂ ↦ ((b ::ₘ D).map fun a ↦ Real.log (‖w - a‖ ^ 2 + C)).sum) =
        (fun w : ℂ ↦ Real.log (‖w - b‖ ^ 2 + C)) +
          fun w : ℂ ↦ (D.map fun a ↦ Real.log (‖w - a‖ ^ 2 + C)).sum := by
      funext w
      simp
    refine ⟨heq ▸ hb.add ih.1, fun z ↦ ?_⟩
    rw [heq, hb.contDiffAt.laplacian_add ih.1.contDiffAt, laplacian_log_norm_sub_sq_add hC,
      ih.2, Multiset.map_cons, Multiset.sum_cons]

/-- The comparison function: `exp (-∑ log (‖z - a‖² + C)) |∏ (z - a)|² =
∏ ‖z - a‖² / (‖z - a‖² + C)`. -/
private theorem exp_neg_sum_log_mul_norm_prod_sq {C : ℝ} (hC : 0 < C) (D : Multiset ℂ) (z : ℂ) :
    Real.exp (-(D.map fun a ↦ Real.log (‖z - a‖ ^ 2 + C)).sum) *
        ‖(D.map fun a ↦ z - a).prod‖ ^ 2 =
      (D.map fun a ↦ ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + C)).prod := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons b D ih =>
    have hb : 0 < ‖z - b‖ ^ 2 + C := by positivity
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons, ← ih, neg_add,
      Real.exp_add, Real.exp_neg, Real.exp_log hb, norm_mul, mul_pow]
    field_simp

/-- The comparison function has the same growth as the amplitude:
`-(1 / 2) ∑_{a ∈ D} log (‖z - a‖² + C) + m log ‖z‖ → 0`, where `m` is the cardinality of `D`. -/
private theorem tendsto_neg_half_mul_sum_log_add_card_mul_log {C : ℝ} (hC : 0 < C)
    (D : Multiset ℂ) :
    Tendsto (fun z : ℂ ↦ -(1 / 2 : ℝ) * (D.map fun a ↦ Real.log (‖z - a‖ ^ 2 + C)).sum +
      Multiset.card D * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
  have hsum : Tendsto (fun z : ℂ ↦
      (D.map fun a ↦ Real.log (‖z - a‖ ^ 2 + C) - 2 * Real.log ‖z‖).sum) (cocompact ℂ) (𝓝 0) := by
    induction D using Multiset.induction_on with
    | empty => simp
    | cons b D ih =>
      simpa using (tendsto_log_norm_sub_sq_add_sub hC b).add ih
  have h := hsum.const_mul (-(1 / 2 : ℝ))
  rw [mul_zero] at h
  refine h.congr fun z ↦ ?_
  rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate,
    nsmul_eq_mul]
  ring

/-! ### The weights `C / (‖z - a‖² + C)` -/

/-- The weights `C / (‖z - a‖² + C)` lie in `[0, 1]`. -/
private theorem mem_Icc_of_mem_map_div_norm_sub_sq_add {C : ℝ} (hC : 0 < C) (D : Multiset ℂ)
    (z : ℂ) : ∀ s ∈ D.map fun a ↦ C / (‖z - a‖ ^ 2 + C), s ∈ Set.Icc 0 1 := by
  intro s hs
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hs
  exact ⟨by positivity, div_le_one_of_le₀ (by nlinarith [sq_nonneg ‖z - a‖]) (by positivity)⟩

/-- `∏ (1 - C / (‖z - a‖² + C)) = ∏ ‖z - a‖² / (‖z - a‖² + C)`. -/
private theorem prod_map_one_sub_div_norm_sub_sq_add {C : ℝ} (hC : 0 < C) (D : Multiset ℂ)
    (z : ℂ) :
    ((D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).map fun t ↦ 1 - t).prod =
      (D.map fun a ↦ ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + C)).prod := by
  rw [Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ ↦ ?_
  have : 0 < ‖z - a‖ ^ 2 + C := by positivity
  simp only [Function.comp_apply]
  field_simp
  ring

/-! ### The comparison theorem for the scalar equation -/

/-- **The comparison step at one point.** Let `C > 16 m`, where `m` is the cardinality of `D`. If
`U` lies below the comparison value `-(1 / 2) ∑_{a ∈ D} log (‖z - a‖² + C)`, then the right-hand
side of the scalar equation at `U` is smaller than the Laplacian
`-(1 / 2) ∑_{a ∈ D} 4 C / (‖z - a‖² + C)²` of the comparison function. -/
private theorem rhs_lt_neg_half_mul_sum {D : Multiset ℂ} {C : ℝ}
    (hC : 16 * (Multiset.card D : ℝ) < C) {z : ℂ} {U : ℝ}
    (hU : U < -(1 / 2) * (D.map fun a ↦ Real.log (‖z - a‖ ^ 2 + C)).sum) :
    (Real.exp (2 * U) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 - 1) / 8 <
      -(1 / 2) * (D.map fun a ↦ 4 * C / (‖z - a‖ ^ 2 + C) ^ 2).sum := by
  have hC₀ : 0 < C := lt_of_le_of_lt (by positivity) hC
  -- The weights `tₐ = C / (‖z - a‖² + C) ∈ [0, 1]`.
  have h01 := mem_Icc_of_mem_map_div_norm_sub_sq_add hC₀ D z
  have hP₀ := Multiset.prod_map_nonneg (f := fun t : ℝ ↦ 1 - t) fun t ht ↦
    sub_nonneg.2 (h01 t ht).2
  have hP₁ : ((D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).map fun t ↦ 1 - t).prod ≤ 1 :=
    Multiset.prod_map_le_one₀ (fun t ht ↦ sub_nonneg.2 (h01 t ht).2)
      fun t ht ↦ sub_le_self _ (h01 t ht).1
  have hS := Multiset.sum_map_sq_le_card_mul_one_sub_prod_map_one_sub (fun t ht ↦ (h01 t ht).1)
    fun t ht ↦ (h01 t ht).2
  rw [Multiset.card_map] at hS
  -- In these weights the Laplacian is `-(2 / C) ∑ tₐ²` and `exp (2 v) |f|² = ∏ (1 - tₐ)`.
  have hsum : (D.map fun a ↦ 4 * C / (‖z - a‖ ^ 2 + C) ^ 2).sum =
      4 / C * ((D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).map fun t ↦ t ^ 2).sum := by
    rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun a _ ↦ ?_
    simp only [Function.comp_apply]
    field_simp
  have hprod : Real.exp (2 * (-(1 / 2) * (D.map fun a ↦ Real.log (‖z - a‖ ^ 2 + C)).sum)) *
      ‖(D.map fun a ↦ z - a).prod‖ ^ 2 =
        ((D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).map fun t ↦ 1 - t).prod := by
    rw [show ∀ y : ℝ, 2 * (-(1 / 2) * y) = -y from fun y ↦ by ring,
      exp_neg_sum_log_mul_norm_prod_sq hC₀ D z, prod_map_one_sub_div_norm_sub_sq_add hC₀ D z]
  rw [hsum]
  set P := ((D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).map fun t ↦ 1 - t).prod
  set S := ((D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).map fun t ↦ t ^ 2).sum
  rcases eq_or_ne ‖(D.map fun a ↦ z - a).prod‖ 0 with h0 | h0
  · -- Where `f` vanishes the left side is `-1 / 8`, while `-(2 / C) ∑ tₐ² ≥ -2 m / C > -1 / 8`.
    rw [h0]
    have : 4 / C * S ≤ 4 / C * Multiset.card D := by gcongr; nlinarith
    have h16 : 4 / C * Multiset.card D < 1 / 4 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hC₀]; linarith
    norm_num
    linarith
  · -- Elsewhere the left side is below `(∏ (1 - tₐ) - 1) / 8 ≤ -(2 / C) ∑ tₐ²`.
    have hexp : Real.exp (2 * U) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 < P := by
      rw [← hprod]
      exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.2 (by linarith))
        (pow_pos (lt_of_le_of_ne (norm_nonneg _) h0.symm) 2)
    have : 4 / C * S ≤ (1 - P) / 4 := by rw [div_mul_eq_mul_div, div_le_iff₀ hC₀]; nlinarith
    linarith

/-- **Lower bound for solutions of the regularized scalar equation.** Let `D` be a multiset of
`m` points, `f(z) = ∏_{a ∈ D} (z - a)`, and let `u` be a `C²` solution of
`Δu = (exp(2u) |f|² - 1) / 8` with `u + m log |z| → 0` at infinity. Then for every `C > 16 m`,

`∏_{a ∈ D} ‖z - a‖² / (‖z - a‖² + C) ≤ exp(2u(z)) |f(z)|²`. -/
theorem prod_div_le_exp_two_mul_mul_norm_prod_sq {D : Multiset ℂ} {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ z, Δ u z = (Real.exp (2 * u z) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 - 1) / 8)
    (hbc : Tendsto (fun z ↦ u z + Multiset.card D * Real.log ‖z‖) (cocompact ℂ) (𝓝 0))
    {C : ℝ} (hC : 16 * (Multiset.card D : ℝ) < C) (z : ℂ) :
    (D.map fun a ↦ ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + C)).prod ≤
      Real.exp (2 * u z) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 := by
  have hC₀ : 0 < C := lt_of_le_of_lt (by positivity) hC
  set F : ℂ → ℝ := fun w ↦ (D.map fun a ↦ Real.log (‖w - a‖ ^ 2 + C)).sum with hF
  obtain ⟨hFd, hFΔ⟩ := contDiff_sum_log_and_laplacian hC₀ D
  set v : ℂ → ℝ := (-(1 / 2) : ℝ) • F with hv
  have hvz (w : ℂ) : v w = -(1 / 2) * F w := by simp only [hv, Pi.smul_apply, smul_eq_mul]
  -- It suffices to show that the comparison function `v` lies below `u`.
  suffices hle : ∀ w, v w ≤ u w by
    calc _ = Real.exp (2 * v z) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 := by
          rw [hvz, show 2 * (-(1 / 2) * F z) = -F z by ring]
          exact (exp_neg_sum_log_mul_norm_prod_sq hC₀ D z).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hle z])) (sq_nonneg _)
  have hvd : ContDiff ℝ 2 v := hFd.const_smul (-(1 / 2) : ℝ)
  -- `v - u` tends to zero at infinity and is subharmonic where positive, so it is nonpositive.
  have hglim : Tendsto (v - u) (cocompact ℂ) (𝓝 0) := by
    have h := (tendsto_neg_half_mul_sum_log_add_card_mul_log hC₀ D).sub hbc
    rw [sub_zero] at h
    refine h.congr fun w ↦ ?_
    simp only [Pi.sub_apply, hvz, hF]
    ring
  refine fun w ↦ sub_nonpos.1 <| nonpos_of_tendsto_cocompact_of_laplacian_nonneg (f := v - u)
    (hvd.sub hu) (fun y hy ↦ ?_) hglim w
  -- Where `u < v`, the comparison step gives `Δu < Δv`.
  rw [hvd.contDiffAt.laplacian_sub hu.contDiffAt, hv, laplacian_smul _ hFd.contDiffAt,
    smul_eq_mul, hFΔ, hΔ]
  have := rhs_lt_neg_half_mul_sum hC (z := y) ((sub_pos.1 hy).trans_eq (hvz y))
  linarith

/-! ### Plane vortices -/

/-- **Lower bound for the modulus of a plane vortex.** Let `x` be a smooth plane vortex with the
degree-`m` end framing and zero divisor `D`. Then for every `C > 16 m` and every `z`,

`∏_{a ∈ D} ‖z - a‖² / (‖z - a‖² + C) ≤ |α(z)|²`. -/
theorem prod_div_le_normSq {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    {C : ℝ} (hC : 16 * (m : ℝ) < C) (z : ℂ) :
    (D.map fun a ↦ ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + C)).prod ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
  obtain ⟨u, hu, hΔ, hbc, g, hg⟩ := exists_framedGaugeGroup_smul_amplitudeField_eq hx hsol hframe hD
  have hm : Multiset.card D = m := hD.card_eq_of_tendsto_mul_inv_pow hframe
  subst hm
  rw [← sq_norm_sectionValue, ← exp_mul_norm_eq_norm_sectionValue hg z, mul_pow, sq (Real.exp _),
    ← Real.exp_add, ← two_mul]
  exact prod_div_le_exp_two_mul_mul_norm_prod_sq (hu.of_le (by simp)) hΔ hbc hC z

/-- **Polynomial decay of the modulus defect.** For a smooth plane vortex with the degree-`m` end
framing and zero divisor `D`, and every `C > 16 m`,

`1 - |α(z)|² ≤ ∑_{a ∈ D} C / (‖z - a‖² + C)`. -/
theorem one_sub_normSq_le_sum {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    {C : ℝ} (hC : 16 * (m : ℝ) < C) (z : ℂ) :
    1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ (D.map fun a ↦ C / (‖z - a‖ ^ 2 + C)).sum := by
  have hC₀ : 0 < C := lt_of_le_of_lt (by positivity) hC
  have hlow := prod_div_le_normSq hx hsol hframe hD hC z
  have h01 := mem_Icc_of_mem_map_div_norm_sub_sq_add hC₀ D z
  have h := Multiset.one_sub_prod_map_one_sub_le_sum (fun t ht ↦ (h01 t ht).1)
    fun t ht ↦ (h01 t ht).2
  rw [prod_map_one_sub_div_norm_sub_sq_add hC₀ D z] at h
  linarith

/-- **Localization of small moduli near the zeros.** For a smooth plane vortex with the degree-`m`
end framing and zero divisor `D`, every `C > 16 m` and every `θ < 1`, a point where
`|α(z)|² ≤ θ` lies near a zero: `(1 - θ) ‖z - a‖² < m C` for some `a ∈ D`. -/
theorem exists_mem_mul_norm_sub_sq_lt {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    {C : ℝ} (hC : 16 * (m : ℝ) < C) {θ : ℝ} (hθ : θ < 1) {z : ℂ}
    (hz : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ θ) :
    ∃ a ∈ D, (1 - θ) * ‖z - a‖ ^ 2 < m * C := by
  have hC₀ : 0 < C := lt_of_le_of_lt (by positivity) hC
  have hm : Multiset.card D = m := hD.card_eq_of_tendsto_mul_inv_pow hframe
  have h := one_sub_normSq_le_sum hx hsol hframe hD hC z
  by_contra! hfar
  -- Every term of the sum is at most `(1 - θ) C / (m C + (1 - θ) C)`.
  have hterm : ∀ a ∈ D, C / (‖z - a‖ ^ 2 + C) ≤ (1 - θ) * C / (m * C + (1 - θ) * C) := by
    intro a ha
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hfar a ha]
  have hsum := Multiset.sum_map_le_sum_map _ _ hterm
  rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hm] at hsum
  have : (m : ℝ) * ((1 - θ) * C / (m * C + (1 - θ) * C)) < 1 - θ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.2 hθ) hC₀]
  linarith

/-! ### Uniform exponential decay -/

/-- **The modulus near one outside an explicit radius.** Let `0 < δ`, `C > 16 m` and
`R ≥ R₀ + √(m C / δ)`. For a smooth plane vortex with the degree-`m` end framing whose zeros lie in
the closed disc of radius `R₀`, `|α(z)|² ≥ 1 - δ` whenever `‖z‖ ≥ R`. -/
private theorem one_sub_le_normSq_of_le_norm {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {R₀ : ℝ}
    (hD₀ : ∀ a ∈ D, ‖a‖ ≤ R₀) {C δ R : ℝ} (hC : 16 * (m : ℝ) < C) (hδ : 0 < δ)
    (hR : R₀ + Real.sqrt (m * C / δ) ≤ R) {z : ℂ} (hz : R ≤ ‖z‖) :
    1 - δ ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
  have hC₀ : 0 < C := lt_of_le_of_lt (by positivity) hC
  set L : ℝ := Real.sqrt (m * C / δ)
  have hL : L ^ 2 = m * C / δ := Real.sq_sqrt (by positivity)
  -- Otherwise the localization lemma puts a zero within distance `L` of `z`, which is impossible.
  by_contra! h
  obtain ⟨a, ha, hlt⟩ := exists_mem_mul_norm_sub_sq_lt hx hsol hframe hD hC
    (θ := 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (by linarith) le_rfl
  have hLa : L ≤ ‖z - a‖ := by linarith [norm_sub_norm_le z a, hD₀ a ha]
  have hsq : m * C / δ ≤ ‖z - a‖ ^ 2 := hL ▸ pow_le_pow_left₀ (Real.sqrt_nonneg _) hLa 2
  have hcancel : δ * (m * C / δ) = m * C := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hsq hδ.le, sq_nonneg ‖z - a‖]

/-- The case `0 ≤ c` of `exists_one_sub_normSq_le_mul_exp_of_forall_mem_norm_le`, with a
nonnegative constant. -/
private theorem exists_one_sub_normSq_le_mul_exp_of_forall_mem_norm_le_of_nonneg (m : ℕ) (R₀ : ℝ)
    {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ R₀) →
      ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- Outside the radius `R`, `|α|² ≥ σ = (1 + 4 c²) / 2`, which exceeds `4 c²`.
  set σ : ℝ := (1 + 4 * c ^ 2) / 2
  have hσ1 : σ < 1 := by simp only [σ]; nlinarith
  set C : ℝ := 16 * m + 1
  set R : ℝ := max R₀ 0 + Real.sqrt (m * C / (1 - σ)) + 1
  have hR : 0 < R := by positivity
  set M : ℝ := -Real.log σ
  refine ⟨max 1 M * Real.exp (c * R), by positivity, fun x D hx hsol hframe hD hD₀ z ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hp : ContDiff ℝ 2 fun w ↦ x w 2 := (hxi 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ x w 3 := (hxi 3).of_le (by simp)
  have hfar : ∀ w, R ≤ ‖w‖ → σ ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2) := fun w hw ↦ by
    have := one_sub_le_normSq_of_le_norm hx hsol hframe hD (fun a ha ↦ (hD₀ a ha).trans
      (le_max_left R₀ 0)) (lt_add_one _) (sub_pos.2 hσ1) (by simp only [R]; linarith) hw
    linarith
  by_cases hz : R ≤ ‖z‖
  · have hdecay := one_sub_normSq_le_neg_log_mul_exp hp hq hsol
      (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hR hc₀ (by positivity)
      (by simp only [σ]; nlinarith) hfar hz
    rw [exp_neg_mul_sub, ← mul_assoc] at hdecay
    exact hdecay.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le) (Real.exp_pos _).le)
  · -- Inside the radius, `1 - |α|² ≤ 1 ≤ exp (c R) exp (-c |z|)`.
    rw [not_le] at hz
    have hexp : 1 ≤ Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1 := by nlinarith
      _ ≤ max 1 M * (Real.exp (c * R) * Real.exp (-(c * ‖z‖))) :=
        one_le_mul_of_one_le_of_one_le (le_max_left _ _) hexp
      _ = _ := by rw [mul_assoc]

/-- **Uniform exponential decay of plane vortices over a compact window of divisors.** For every
degree `m`, radius `R₀` and rate `c < 1 / 2` there is a constant `K` such that every smooth plane
vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius `R₀` satisfies
`1 - |α(z)|² ≤ K exp (-c |z|)` for every `z`. -/
theorem exists_one_sub_normSq_le_mul_exp_of_forall_mem_norm_le (m : ℕ) (R₀ : ℝ) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ R₀) →
      ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_mem_norm_le_of_nonneg m R₀
    (le_max_right c 0) (max_lt hc (by norm_num))
  refine ⟨K, fun x D hx hsol hframe hD hD₀ z ↦ (hK x D hx hsol hframe hD hD₀ z).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))) hK₀

end TauCeti.Vortex
