/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogConvex
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.FiniteProduct

/-!
# Gauss's multiplication formula for the Gamma function

Mathlib has Legendre's duplication formula `Complex.Gamma_mul_Gamma_add_half` (the case
`m = 2`). This file proves Gauss's multiplication formula (DLMF 5.5.6) for every `m ≥ 1`,

$$
\prod_{k=0}^{m-1}\Gamma\bigl(z+k/m\bigr)=(2\pi)^{(m-1)/2}\, m^{1/2-mz}\,\Gamma(mz),
$$

together with the product of `Γ` at the rational points `k/m` (DLMF 5.5.7) and Gauss's
triplication formula, the case `m = 3`.

## Main results

* `Real.prod_Gamma_div`, `Complex.prod_Gamma_div`: `∏_{k=1}^{m-1} Γ(k/m) = (2π)^{(m-1)/2} / √m`
  (DLMF 5.5.7).
* `Complex.prod_Gamma_add_div`, `Complex.Gamma_natCast_mul`: DLMF 5.5.6 for every `s : ℂ`.
* `Real.prod_Gamma_add_div`, `Real.Gamma_natCast_mul`: DLMF 5.5.6 for every `s : ℝ`.
* `Complex.Gamma_mul_Gamma_add_third`: Gauss's triplication formula
  `Γ(z) Γ(z + ⅓) Γ(z + ⅔) = 2π 3^{½ − 3z} Γ(3z)`.

## Implementation notes

For `s > 0` the formula follows from the Bohr–Mollerup theorem `Real.eq_Gamma_of_log_convex`.
The constant is evaluated with Euler's reflection formula and the sine product
`Real.prod_sin_pi_mul_div`. The identity theorem then extends the formula for `1/Γ` to all complex
arguments, and the real formula for every `s` is read off from the complex one. Both sides vanish
at the poles of `Γ`, under Mathlib's convention `Γ(−n) = 0`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, Theorem 1.5.2.
* [DLMF, §5.5(iii)](https://dlmf.nist.gov/5.5.iii)

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Gamma/Multiplication.lean`.
-/

@[expose] public section

open Filter Finset

open scoped Topology Real

noncomputable section

namespace Real

/-- `∏_{k=1}^{m-1} Γ(k/m) = (2π)^{(m-1)/2} / √m` (DLMF 5.5.7). -/
theorem prod_Gamma_div {m : ℕ} (hm : 0 < m) :
    ∏ k ∈ Ico 1 m, Gamma (k / m : ℝ) =
      (2 * π) ^ ((m - 1 : ℝ) / 2) / √(m : ℝ) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hPpos : 0 < ∏ k ∈ Ico 1 m, Gamma (k / m : ℝ) :=
    prod_pos fun k hk =>
      Gamma_pos_of_pos <|
        div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one (Finset.mem_Ico.mp hk).1)) hm0
  have hpair :
      (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) *
          ∏ k ∈ Ico 1 m, Gamma (((m - k : ℕ) : ℝ) / m) =
        ∏ k ∈ Ico 1 m, π / sin (π * k / m) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun k hk => ?_
    have hle : k ≤ m := Nat.le_of_lt (Finset.mem_Ico.mp hk).2
    have hcast : ((m - k : ℕ) : ℝ) / m = 1 - (k : ℝ) / m := by
      rw [Nat.cast_sub hle]
      field
    have hsin : π / sin (π * ((k : ℝ) / m)) = π / sin (π * k / m) := by
      congr 2
      ring
    rw [hcast, Gamma_mul_Gamma_one_sub, hsin]
  have hrev :
      ∏ k ∈ Ico 1 m, Gamma (((m - k : ℕ) : ℝ) / m) =
        ∏ k ∈ Ico 1 m, Gamma (k / m : ℝ) := by
    simpa using (prod_Ico_reflect (fun j : ℕ => Gamma ((j : ℝ) / m)) 1 (Nat.le_succ m))
  have hsq :
      (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) ^ 2 =
        π ^ (m - 1) * (2 : ℝ) ^ (m - 1) / m := by
    have hcard : #(Ico 1 m) = m - 1 := Nat.card_Ico 1 m
    calc
      (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) ^ 2
        = (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) *
            ∏ k ∈ Ico 1 m, Gamma (k / m : ℝ) := by ring
      _ = (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) *
            ∏ k ∈ Ico 1 m, Gamma (((m - k : ℕ) : ℝ) / m) := by rw [hrev]
      _ = ∏ k ∈ Ico 1 m, π / sin (π * k / m) := hpair
      _ = (∏ _k ∈ Ico 1 m, (π : ℝ)) / ∏ k ∈ Ico 1 m, sin (π * k / m) :=
          prod_div_distrib _ _
      _ = π ^ (m - 1) / (m / (2 : ℝ) ^ (m - 1)) := by
          simp [prod_const, hcard, prod_sin_pi_mul_div hm]
      _ = π ^ (m - 1) * (2 : ℝ) ^ (m - 1) / m := by field
  have hsqrt :
      √(π ^ (m - 1) * (2 : ℝ) ^ (m - 1) / m) =
        (2 * π) ^ ((m - 1 : ℝ) / 2) / √(m : ℝ) := by
    have hnum : 0 ≤ π ^ (m - 1) * (2 : ℝ) ^ (m - 1) :=
      mul_nonneg (pow_nonneg pi_pos.le _) (pow_nonneg zero_le_two _)
    have h2π : 0 ≤ 2 * π := mul_nonneg zero_le_two pi_pos.le
    have hpow : (2 * π) ^ (m - 1) = π ^ (m - 1) * (2 : ℝ) ^ (m - 1) := by
      rw [mul_pow, mul_comm]
    rw [sqrt_div hnum]
    have : √(π ^ (m - 1) * (2 : ℝ) ^ (m - 1)) = √((2 * π) ^ (m - 1)) := by
      congr 1
      exact hpow.symm
    rw [this, sqrt_eq_rpow, ← rpow_natCast (2 * π), ← rpow_mul h2π]
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one]
    simp [hcast]
    ring_nf
  have hnn : 0 ≤ ∏ k ∈ Ico 1 m, Gamma (k / m : ℝ) := hPpos.le
  have hnn' : 0 ≤ √(π ^ (m - 1) * (2 : ℝ) ^ (m - 1) / m) := sqrt_nonneg _
  have hsq' :
      (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) ^ 2 =
        (√(π ^ (m - 1) * (2 : ℝ) ^ (m - 1) / m)) ^ 2 := by
    rw [sq_sqrt (div_nonneg (mul_nonneg (pow_nonneg pi_pos.le _) (pow_nonneg zero_le_two _))
      hm0.le)]
    exact hsq
  rw [(sq_eq_sq₀ hnn hnn').mp hsq', hsqrt]

/-- Auxiliary function for the Bohr–Mollerup argument: this will equal `Gamma s`. -/
private def multiplicationGamma (m : ℕ) (s : ℝ) : ℝ :=
  (∏ k ∈ range m, Gamma ((s + k) / m)) * (m : ℝ) ^ (s - 1 / 2) /
    (2 * π) ^ ((m - 1 : ℝ) / 2)

/-- The normalized Gauss product `multiplicationGamma m` satisfies the Gamma recurrence `G(s + 1) =
s G(s)` for `s ≠ 0`. -/
private theorem multiplicationGamma_add_one {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : s ≠ 0) :
    multiplicationGamma m (s + 1) = s * multiplicationGamma m s := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  have hg :
      ∏ k ∈ range m, Gamma ((s + 1 + k) / m) =
        ∏ k ∈ Ico 1 (m + 1), Gamma ((s + k) / m) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      (prod_Ico_eq_prod_range (fun k : ℕ => Gamma ((s + k) / m)) 1 (m + 1)).symm
  have hsucc :
      ∏ k ∈ Ico 1 (m + 1), Gamma ((s + k) / m) =
        (∏ k ∈ Ico 1 m, Gamma ((s + k) / m)) * Gamma ((s + m) / m) := by
    simpa using prod_Ico_succ_top (Nat.one_le_of_lt hm) (fun k : ℕ => Gamma ((s + k) / m))
  have h0 :
      ∏ k ∈ range m, Gamma ((s + k) / m) =
        Gamma (s / m) * ∏ k ∈ Ico 1 m, Gamma ((s + k) / m) := by
    simpa using prod_eq_prod_Ico_succ_bot hm (fun k : ℕ => Gamma ((s + k) / m))
  have hadd : Gamma ((s + m) / m) = Gamma (s / m + 1) := by
    congr 1
    field
  have hG : Gamma (s / m + 1) = (s / m) * Gamma (s / m) :=
    Gamma_add_one (div_ne_zero hs hmne)
  have hshift :
      ∏ k ∈ range m, Gamma ((s + 1 + k) / m) =
        (s / m) * ∏ k ∈ range m, Gamma ((s + k) / m) := by
    calc
      ∏ k ∈ range m, Gamma ((s + 1 + k) / m)
        = (∏ k ∈ Ico 1 m, Gamma ((s + k) / m)) * Gamma ((s + m) / m) := by
            rw [hg, hsucc]
      _ = (∏ k ∈ Ico 1 m, Gamma ((s + k) / m)) * ((s / m) * Gamma (s / m)) := by
            rw [hadd, hG]
      _ = (s / m) * (Gamma (s / m) * ∏ k ∈ Ico 1 m, Gamma ((s + k) / m)) := by ring
      _ = (s / m) * ∏ k ∈ range m, Gamma ((s + k) / m) := by rw [h0]
  have hrpow : (m : ℝ) ^ (s + 1 - 1 / 2) = (m : ℝ) ^ (s - 1 / 2) * m := by
    have : s + 1 - 1 / 2 = (s - 1 / 2) + 1 := by ring
    rw [this, rpow_add hm0, rpow_one]
  simp_rw [multiplicationGamma, hshift, hrpow]
  field

/-- `multiplicationGamma m 1 = 1`. -/
private theorem multiplicationGamma_one {m : ℕ} (hm : 0 < m) : multiplicationGamma m 1 = 1 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hIco :
      ∏ k ∈ range m, Gamma ((1 + k : ℝ) / m) =
        ∏ k ∈ Ico 1 (m + 1), Gamma (k / m : ℝ) := by
    simpa [add_comm] using
      (prod_Ico_eq_prod_range (fun k : ℕ => Gamma (k / m : ℝ)) 1 (m + 1)).symm
  have hsucc :
      ∏ k ∈ Ico 1 (m + 1), Gamma (k / m : ℝ) =
        (∏ k ∈ Ico 1 m, Gamma (k / m : ℝ)) * Gamma ((m : ℝ) / m) := by
    simpa using prod_Ico_succ_top (Nat.one_le_of_lt hm) (fun k : ℕ => Gamma (k / m : ℝ))
  have hG : Gamma ((m : ℝ) / m) = 1 := by
    have : (m : ℝ) / m = 1 := div_self hm0.ne'
    simp [this, Gamma_one]
  have hprod :
      ∏ k ∈ range m, Gamma ((1 + k : ℝ) / m) =
        ∏ k ∈ Ico 1 m, Gamma (k / m : ℝ) := by
    rw [hIco, hsucc, hG, mul_one]
  have hrpow : (m : ℝ) ^ ((1 : ℝ) - 1 / 2) = √(m : ℝ) := by
    have : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
    rw [this, sqrt_eq_rpow]
  simp_rw [multiplicationGamma, hprod, hrpow, prod_Gamma_div hm]
  field

/-- On `(0, ∞)`, `log` of `multiplicationGamma m s` is `∑_{k<m} log Γ((s + k)/m) + (s - 1/2) log m -
log((2π)^((m-1)/2))`. -/
private theorem log_multiplicationGamma_eq {m : ℕ} (hm : 0 < m) :
    Set.EqOn (log ∘ multiplicationGamma m)
      (fun s => ∑ k ∈ range m, log (Gamma ((s + k) / m)) +
        (s - 1 / 2) * log m - log ((2 * π) ^ ((m - 1 : ℝ) / 2)))
      (Set.Ioi 0) := by
  intro s hs
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hGpos : ∀ k ∈ range m, 0 < Gamma ((s + k) / m) := fun k _ =>
    Gamma_pos_of_pos <| div_pos (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)) hm0
  have hprod : 0 < ∏ k ∈ range m, Gamma ((s + k) / m) := prod_pos hGpos
  have hrpow : 0 < (m : ℝ) ^ (s - 1 / 2) := rpow_pos_of_pos hm0 _
  have hC : 0 < (2 * π) ^ ((m - 1 : ℝ) / 2) :=
    rpow_pos_of_pos (mul_pos two_pos pi_pos) _
  have hnum : (∏ k ∈ range m, Gamma ((s + k) / m)) * (m : ℝ) ^ (s - 1 / 2) ≠ 0 :=
    (mul_pos hprod hrpow).ne'
  rw [Function.comp_apply, multiplicationGamma,
    log_div hnum hC.ne', log_mul hprod.ne' hrpow.ne',
    log_prod (fun k hk => (hGpos k hk).ne'), log_rpow hm0]

/-- `multiplicationGamma m` is log-convex on `(0, ∞)`. -/
private theorem multiplicationGamma_log_convex_Ioi {m : ℕ} (hm : 0 < m) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (log ∘ multiplicationGamma m) := by
  have hsum := convexOn_sum_log_Gamma_add_div (range m) (fun k _ => Nat.cast_nonneg (α := ℝ) k)
    (Nat.cast_pos.mpr hm)
  have hlin : ConvexOn ℝ (Set.Ioi 0) (fun s : ℝ => s * log m) := by
    simpa [mul_comm] using (convexOn_id (convex_Ioi (0 : ℝ))).smul (log_natCast_nonneg m)
  have hconst : ConvexOn ℝ (Set.Ioi 0)
      (fun _ : ℝ => -(1 / 2) * log m - log ((2 * π) ^ ((m - 1 : ℝ) / 2))) :=
    convexOn_const _ (convex_Ioi 0)
  refine (((hsum.add hlin).add hconst).congr fun s hs => ?_)
  have heq := log_multiplicationGamma_eq hm hs
  simp only [Pi.add_apply, Function.comp_apply] at heq ⊢
  rw [heq]
  ring

/-- `multiplicationGamma m s > 0` for `s > 0`. -/
private theorem multiplicationGamma_pos {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    0 < multiplicationGamma m s := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine div_pos (mul_pos ?_ (rpow_pos_of_pos hm0 _))
      (rpow_pos_of_pos (mul_pos two_pos pi_pos) _)
  exact prod_pos fun k _ =>
    Gamma_pos_of_pos <| div_pos (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)) hm0

/-- Gauss's multiplication formula in Bohr–Mollerup form: `multiplicationGamma m s = Γ(s)` for
`s > 0`. -/
private theorem multiplicationGamma_eq_Gamma {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    multiplicationGamma m s = Gamma s :=
  eq_Gamma_of_log_convex (multiplicationGamma_log_convex_Ioi hm)
    (fun {_y} hy => multiplicationGamma_add_one hm hy.ne')
    (fun {_y} hy => multiplicationGamma_pos hm hy) (multiplicationGamma_one hm) hs

/-- Gauss's multiplication formula (DLMF 5.5.6) for `s > 0`:
`∏_{k<m} Γ(s + k/m) = (2π)^{(m-1)/2} m^{1/2 - ms} Γ(ms)`. -/
private theorem prod_Gamma_add_div_of_pos {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    ∏ k ∈ range m, Gamma (s + k / m) =
      (2 * π) ^ ((m - 1 : ℝ) / 2) * (m : ℝ) ^ (1 / 2 - m * s) * Gamma (m * s) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hs' : 0 < m * s := mul_pos hm0 hs
  have harg : ∀ k : ℕ, (m * s + k) / m = s + k / m := fun k => by field
  have hC : (2 * π : ℝ) ^ ((m - 1 : ℝ) / 2) ≠ 0 :=
    (rpow_pos_of_pos (mul_pos two_pos pi_pos) _).ne'
  have hmne : (m : ℝ) ^ (m * s - 1 / 2) ≠ 0 := (rpow_pos_of_pos hm0 _).ne'
  have hrpow : ((m : ℝ) ^ (m * s - 1 / 2))⁻¹ = (m : ℝ) ^ (1 / 2 - m * s) := by
    rw [← rpow_neg hm0.le]
    congr 1
    ring
  have hrearr :
      ∏ k ∈ range m, Gamma (s + k / m) =
        ((∏ k ∈ range m, Gamma (s + k / m)) * (m : ℝ) ^ (m * s - 1 / 2) /
            (2 * π) ^ ((m - 1 : ℝ) / 2)) *
          (2 * π) ^ ((m - 1 : ℝ) / 2) * ((m : ℝ) ^ (m * s - 1 / 2))⁻¹ := by
    field
  have hF : (∏ k ∈ range m, Gamma (s + k / m)) *
        (m : ℝ) ^ (m * s - 1 / 2) / (2 * π) ^ ((m - 1 : ℝ) / 2) =
      Gamma (m * s) := by
    simpa [multiplicationGamma, harg] using multiplicationGamma_eq_Gamma hm hs'
  rw [hrearr, hF, hrpow]
  ring

end Real

namespace Complex

/-- `(2π)^w ≠ 0`. -/
private theorem two_pi_cpow_ne_zero (w : ℂ) : (2 * π : ℂ) ^ w ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))

/-- `z ↦ ∏_{k<m} 1/Γ(z + k/m)` is entire. -/
private theorem differentiable_prod_one_div_Gamma_add_div (m : ℕ) :
    Differentiable ℂ fun z : ℂ => ∏ k ∈ range m, (Gamma (z + k / m))⁻¹ :=
  Differentiable.fun_finsetProd fun _ _ =>
    differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))

/-- `z ↦ m^(mz - 1/2) / (Γ(mz) (2π)^((m-1)/2))` is entire. -/
private theorem differentiable_mul_cpow_one_div_Gamma (m : ℕ) (hm : 0 < m) :
    Differentiable ℂ fun z : ℂ =>
      (Gamma (m * z))⁻¹ * (m : ℂ) ^ (m * z - 1 / 2) / (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine (Differentiable.mul ?_ ?_).div (differentiable_const _)
    (fun _ => two_pi_cpow_ne_zero _)
  · exact differentiable_one_div_Gamma.comp (differentiable_id.const_mul _)
  · exact ((differentiable_id.const_mul (m : ℂ)).sub_const (1 / 2)).const_cpow (Or.inl hm0)

/-- At a real point `s`, Gauss's multiplication formula for the real `Γ` is the coercion of the
formula for the complex `Γ`. -/
private theorem prod_Gamma_add_div_ofReal_iff (m : ℕ) (s : ℝ) :
    (∏ k ∈ range m, Real.Gamma (s + k / m) =
        (2 * π) ^ ((m - 1 : ℝ) / 2) * (m : ℝ) ^ (1 / 2 - m * s) * Real.Gamma (m * s)) ↔
      ∏ k ∈ range m, Gamma ((s : ℂ) + k / m) =
        (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2) * (m : ℂ) ^ (1 / 2 - m * (s : ℂ)) *
          Gamma (m * (s : ℂ)) := by
  have hprod : ((∏ k ∈ range m, Real.Gamma (s + k / m) : ℝ) : ℂ) =
      ∏ k ∈ range m, Gamma ((s : ℂ) + k / m) := by
    rw [ofReal_prod]
    refine prod_congr rfl fun k _ => ?_
    have : ((s + k / m : ℝ) : ℂ) = (s : ℂ) + k / m := by push_cast; ring
    rw [← this, Gamma_ofReal]
  have hG : (Real.Gamma (m * s) : ℂ) = Gamma (m * (s : ℂ)) := by
    have : ((m * s : ℝ) : ℂ) = m * (s : ℂ) := by push_cast; ring
    rw [← this, Gamma_ofReal]
  have hM : (((m : ℝ) ^ (1 / 2 - m * s) : ℝ) : ℂ) = (m : ℂ) ^ (1 / 2 - m * (s : ℂ)) := by
    rw [ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    ring
  have hC : (((2 * π) ^ ((m - 1 : ℝ) / 2) : ℝ) : ℂ) = (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2) := by
    rw [ofReal_cpow (mul_nonneg zero_le_two Real.pi_pos.le)]
    push_cast
    ring
  rw [← ofReal_inj, ofReal_mul, ofReal_mul, hprod, hG, hM, hC]

/-- **Gauss's multiplication formula** (DLMF 5.5.6) for every `s : ℂ`:
`∏_{k<m} Γ(s + k/m) = (2π)^{(m-1)/2} m^{1/2 - ms} Γ(ms)`. -/
theorem prod_Gamma_add_div {m : ℕ} (hm : 0 < m) (s : ℂ) :
    ∏ k ∈ range m, Gamma (s + k / m) =
      (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2) * (m : ℂ) ^ (1 / 2 - m * s) * Gamma (m * s) := by
  suffices (fun z : ℂ => ∏ k ∈ range m, (Gamma (z + k / m))⁻¹) =
      fun z => (Gamma (m * z))⁻¹ * (m : ℂ) ^ (m * z - 1 / 2) /
        (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2) by
    have h := congr_arg Inv.inv (congr_fun this s)
    simp only [prod_inv_distrib, inv_inv] at h
    rw [h]
    simp [div_eq_mul_inv, ← cpow_neg]
    ring
  have h1 : AnalyticOnNhd ℂ
      (fun z : ℂ => ∏ k ∈ range m, (Gamma (z + k / m))⁻¹) Set.univ :=
    (differentiable_prod_one_div_Gamma_add_div m).differentiableOn.analyticOnNhd isOpen_univ
  have h2 : AnalyticOnNhd ℂ
      (fun z => (Gamma (m * z))⁻¹ * (m : ℂ) ^ (m * z - 1 / 2) /
        (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2)) Set.univ :=
    (differentiable_mul_cpow_one_div_Gamma m hm).differentiableOn.analyticOnNhd isOpen_univ
  have h3 : Tendsto ((↑) : ℝ → ℂ) (nhdsWithin 1 {1}ᶜ) (nhdsWithin 1 {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ofReal_ne_one.mpr ht)
  refine AnalyticOnNhd.eq_of_frequently_eq h1 h2 (h3.frequently ?_)
  refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
  refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht => ?_)
  have h := (prod_Gamma_add_div_ofReal_iff m t).mp (Real.prod_Gamma_add_div_of_pos hm ht)
  rw [prod_inv_distrib, h, mul_inv, mul_inv, ← cpow_neg (m : ℂ), neg_sub]
  ring

/-- `∏_{k=1}^{m-1} Γ(k/m) = (2π)^{(m-1)/2} m^{-1/2}` (DLMF 5.5.7), for complex `Γ`. -/
theorem prod_Gamma_div {m : ℕ} (hm : 0 < m) :
    ∏ k ∈ Ico 1 m, Gamma ((k : ℂ) / m) =
      (2 * π : ℂ) ^ (((m : ℂ) - 1) / 2) * (m : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h := prod_Gamma_add_div hm (1 / m)
  have hL : ∏ k ∈ range m, Gamma (1 / m + k / m) =
      ∏ k ∈ Ico 1 (m + 1), Gamma ((k : ℂ) / m) := by
    rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine prod_congr rfl fun k _ => ?_
    push_cast
    congr 1
    ring
  rw [hL, prod_Ico_succ_top (Nat.one_le_of_lt hm), div_self hm0, Gamma_one, mul_one,
    mul_one_div_cancel hm0, Gamma_one, mul_one] at h
  rw [h]
  congr 2
  ring

/-- Gauss's multiplication formula (DLMF 5.5.6, AAR Theorem 1.5.2) for every `s : ℂ`, solved
for `Γ(ms)`: `Γ(ms) = (2π)^{(1-m)/2} m^{ms - 1/2} ∏_{k<m} Γ(s + k/m)`. -/
theorem Gamma_natCast_mul {m : ℕ} (hm : 0 < m) (s : ℂ) :
    Gamma (m * s) =
      (2 * π : ℂ) ^ ((1 - m : ℂ) / 2) * (m : ℂ) ^ (m * s - 1 / 2) *
        ∏ k ∈ range m, Gamma (s + k / m) := by
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hC : (2 * π : ℂ) ^ ((1 - m : ℂ) / 2) * (2 * π : ℂ) ^ ((m - 1 : ℂ) / 2) = 1 := by
    rw [← cpow_add _ _ h2π, show (1 - m : ℂ) / 2 + (m - 1) / 2 = 0 by ring, cpow_zero]
  have hM : (m : ℂ) ^ (m * s - 1 / 2) * (m : ℂ) ^ (1 / 2 - m * s) = 1 := by
    rw [← cpow_add _ _ hm0, show (m * s - 1 / 2 : ℂ) + (1 / 2 - m * s) = 0 by ring, cpow_zero]
  rw [prod_Gamma_add_div hm s]
  linear_combination
    (-Gamma (m * s) * (m : ℂ) ^ (m * s - 1 / 2) * (m : ℂ) ^ (1 / 2 - m * s)) * hC -
      Gamma (m * s) * hM

/-- **Gauss's triplication formula** (DLMF 5.5.6 with `n = 3`): for every `z : ℂ`,
`Γ(z) Γ(z + ⅓) Γ(z + ⅔) = 2π 3^{½ − 3z} Γ(3z)`. Both sides vanish at the poles of `Γ`, under
Mathlib's convention `Γ(−n) = 0`. -/
theorem Gamma_mul_Gamma_add_third (z : ℂ) :
    Gamma z * Gamma (z + 1 / 3) * Gamma (z + 2 / 3) =
      2 * π * (3 : ℂ) ^ (1 / 2 - 3 * z) * Gamma (3 * z) := by
  have h := prod_Gamma_add_div (m := 3) (by norm_num) z
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, zero_div, add_zero] at h
  have h2 : ((3 : ℂ) - 1) / 2 = 1 := by norm_num
  rw [h2, cpow_one] at h
  rw [h]

end Complex

namespace Real

/-- Gauss's multiplication formula (DLMF 5.5.6) for every `s : ℝ`:
`∏_{k<m} Γ(s + k/m) = (2π)^{(m-1)/2} m^{1/2 - ms} Γ(ms)`. -/
theorem prod_Gamma_add_div {m : ℕ} (hm : 0 < m) (s : ℝ) :
    ∏ k ∈ range m, Gamma (s + k / m) =
      (2 * π) ^ ((m - 1 : ℝ) / 2) * (m : ℝ) ^ (1 / 2 - m * s) * Gamma (m * s) :=
  (Complex.prod_Gamma_add_div_ofReal_iff m s).mpr (Complex.prod_Gamma_add_div hm s)

/-- Gauss's multiplication formula (DLMF 5.5.6, AAR Theorem 1.5.2) for every `s : ℝ`, solved
for `Γ(ms)`: `Γ(ms) = (2π)^{(1-m)/2} m^{ms - 1/2} ∏_{k<m} Γ(s + k/m)`. -/
theorem Gamma_natCast_mul {m : ℕ} (hm : 0 < m) (s : ℝ) :
    Gamma (m * s) =
      (2 * π) ^ ((1 - m : ℝ) / 2) * (m : ℝ) ^ (m * s - 1 / 2) *
        ∏ k ∈ range m, Gamma (s + k / m) := by
  have h2π : 0 < 2 * π := mul_pos two_pos pi_pos
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hC : (2 * π) ^ ((1 - m : ℝ) / 2) * (2 * π) ^ ((m - 1 : ℝ) / 2) = 1 := by
    rw [← rpow_add h2π, show (1 - m : ℝ) / 2 + (m - 1) / 2 = 0 by ring, rpow_zero]
  have hM : (m : ℝ) ^ (m * s - 1 / 2) * (m : ℝ) ^ (1 / 2 - m * s) = 1 := by
    rw [← rpow_add hm0, show (m * s - 1 / 2 : ℝ) + (1 / 2 - m * s) = 0 by ring, rpow_zero]
  rw [prod_Gamma_add_div hm s]
  linear_combination
    (-Gamma (m * s) * (m : ℝ) ^ (m * s - 1 / 2) * (m : ℝ) ^ (1 / 2 - m * s)) * hC -
      Gamma (m * s) * hM

end Real
