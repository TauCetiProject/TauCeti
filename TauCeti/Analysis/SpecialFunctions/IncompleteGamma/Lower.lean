/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The complex lower incomplete Gamma function

The regularized lower incomplete Gamma function `P(a, z) = z^a γ*(a, z)` (DLMF 8.2.6), with the
principal power, and the lower incomplete Gamma function `γ(a, z) = Γ(a) P(a, z)` (DLMF 8.2.4),
both defined through Tricomi's entire function `γ*` of
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi`.

## Main results

* `Complex.lowerIncompleteGamma_eq_integral`: DLMF 8.2.1, `γ(a, z) = z^a ∫₀¹ s^{a−1} e^{−zs} ds`
  for `0 < Re a`;
* `Complex.tendsto_add_natCast_mul_Gamma`: the residue `(−1)ⁿ/n!` of `Γ` at `−n`;
* `Complex.tendsto_mul_lowerIncompleteGamma`: for `z ≠ 0`, `γ(·, z)` has simple poles at
  `a = −n` with residue `(−1)ⁿ/n!`;
* `Complex.differentiable_regularizedGamma_left`: for `z ≠ 0`, `P(·, z)` is entire;
* `Complex.differentiableAt_lowerIncompleteGamma_left`: for `z ≠ 0`, `γ(·, z)` is holomorphic
  off `−ℕ`;
* `Complex.regularizedGamma_one_left`, `Complex.regularizedGamma_neg_natCast`,
  `Complex.regularizedGammaQ_neg_natCast`: `P(1, z) = 1 − e^{−z}`, and `P(−n, z) = 1`,
  `Q(−n, z) = 0` for `z ≠ 0` (DLMF 8.2.5, 8.4.12).

## Implementation notes

The functions live in the root `Complex` namespace, beside `Complex.tricomiIncompleteGamma`.
At the poles `a ∈ −ℕ`, `γ(a, z)` takes the value given by Mathlib's junk value `Γ(−n) = 0`.

## References

* NIST Digital Library of Mathematical Functions, §§8.2, 8.4, <https://dlmf.nist.gov/8.2>.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology

namespace Complex

/-- The regularized lower incomplete Gamma function `P(a, z) = z^a γ*(a, z)` (DLMF 8.2.6), with
the principal power. For fixed `z ≠ 0` it is entire in `a`. -/
def regularizedGamma (a z : ℂ) : ℂ :=
  z ^ a * tricomiIncompleteGamma a z

/-- The lower incomplete Gamma function `γ(a, z) = Γ(a) P(a, z)` (DLMF 8.2.4). At the poles
`a ∈ −ℕ` it takes Mathlib's junk value `Γ(−n) = 0`. -/
def lowerIncompleteGamma (a z : ℂ) : ℂ :=
  Gamma a * regularizedGamma a z

/-- The regularized upper incomplete Gamma function `Q(a, z) = 1 − P(a, z)` (DLMF 8.2.5). -/
def regularizedGammaQ (a z : ℂ) : ℂ :=
  1 - regularizedGamma a z

/-- DLMF 8.2.6: `P(a, z) = z^a γ*(a, z)`. -/
theorem regularizedGamma_def (a z : ℂ) :
    regularizedGamma a z = z ^ a * tricomiIncompleteGamma a z := (rfl)

/-- DLMF 8.2.4: `γ(a, z) = Γ(a) P(a, z)`. -/
theorem lowerIncompleteGamma_def (a z : ℂ) :
    lowerIncompleteGamma a z = Gamma a * regularizedGamma a z := (rfl)

/-- DLMF 8.2.5: `P(a, z) + Q(a, z) = 1`. -/
theorem regularizedGamma_add_regularizedGammaQ (a z : ℂ) :
    regularizedGamma a z + regularizedGammaQ a z = 1 := by
  rw [regularizedGammaQ]
  ring

/-- **DLMF 8.2.1**: `γ(a, z) = z^a ∫₀¹ s^{a−1} e^{−zs} ds` for `0 < Re a` and every `z`. -/
theorem lowerIncompleteGamma_eq_integral {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    lowerIncompleteGamma a z =
      z ^ a * ∫ s in (0 : ℝ)..1, (s : ℂ) ^ (a - 1) * cexp (-(z * s)) := by
  rw [lowerIncompleteGamma_def, regularizedGamma_def, tricomiIncompleteGamma_eq_integral ha]
  have hG := Gamma_ne_zero_of_re_pos ha
  field_simp

/-- **The residue of `Γ` at `−n`**: `(a + n) Γ(a) → (−1)ⁿ/n!` as `a → −n`. -/
theorem tendsto_add_natCast_mul_Gamma (n : ℕ) :
    Tendsto (fun a : ℂ => (a + n) * Gamma a) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1) ^ n / (n ! : ℂ))) := by
  induction n with
  | zero => simpa using tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
    have hn : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast n.succ_ne_zero)
    have hshift : Tendsto (fun a : ℂ => a + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
        (𝓝[≠] (-(n : ℂ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Tendsto (fun a : ℂ => a + 1) (𝓝 (-((n + 1 : ℕ) : ℂ)))
            (𝓝 (-((n + 1 : ℕ) : ℂ) + 1)) := (continuous_id.add continuous_const).tendsto _
        convert h.mono_left nhdsWithin_le_nhds using 2
        push_cast
        ring
      · filter_upwards [self_mem_nhdsWithin] with a ha
        simp only [mem_compl_iff, mem_singleton_iff] at ha ⊢
        intro h
        apply ha
        push_cast
        linear_combination h
    have hinv : Tendsto (fun a : ℂ => a⁻¹) (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
        (𝓝 (-((n + 1 : ℕ) : ℂ))⁻¹) :=
      ((continuousAt_inv₀ hn).tendsto).mono_left nhdsWithin_le_nhds
    have hne0 : ∀ᶠ a in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), a ≠ 0 :=
      (hinv.eventually_ne (inv_ne_zero hn)).mono fun a ha h0 => ha (by rw [h0, inv_zero])
    have hlim : (-1 : ℂ) ^ n / n ! * (-((n + 1 : ℕ) : ℂ))⁻¹ = (-1) ^ (n + 1) / ((n + 1)! : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
      field_simp
      ring
    rw [← hlim]
    refine ((ih.comp hshift).mul hinv).congr' ?_
    filter_upwards [hne0] with a ha
    simp only [Function.comp_apply]
    rw [Gamma_add_one a ha]
    push_cast
    field_simp
    ring

/-- For `z ≠ 0`, `P(·, z)` is entire. -/
theorem differentiable_regularizedGamma_left {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ fun a => regularizedGamma a z := fun a =>
  (differentiableAt_id.const_cpow (Or.inl hz)).mul
    (differentiable_tricomiIncompleteGamma_left z a)

/-- For `z ≠ 0`, `γ(·, z)` is holomorphic off the nonpositive integers. -/
theorem differentiableAt_lowerIncompleteGamma_left {a z : ℂ} (ha : ∀ m : ℕ, a ≠ -m)
    (hz : z ≠ 0) : DifferentiableAt ℂ (fun a => lowerIncompleteGamma a z) a :=
  (differentiableAt_Gamma a ha).mul (differentiable_regularizedGamma_left hz a)

/-- `P(−n, z) = 1` for `z ≠ 0` (DLMF 8.4.12). -/
theorem regularizedGamma_neg_natCast (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma (-n) z = 1 := by
  rw [regularizedGamma_def, tricomiIncompleteGamma_neg_natCast, cpow_neg, cpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hz)]

/-- `Q(−n, z) = 0` for `z ≠ 0` (DLMF 8.2.5 and 8.4.12). -/
theorem regularizedGammaQ_neg_natCast (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGammaQ (-n) z = 0 := by
  rw [regularizedGammaQ, regularizedGamma_neg_natCast n hz, sub_self]

/-- `P(1, z) = 1 − e^{−z}` for every `z` (DLMF 8.4.1). -/
theorem regularizedGamma_one_left (z : ℂ) : regularizedGamma 1 z = 1 - cexp (-z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [regularizedGamma_def]
  · rw [regularizedGamma_def, tricomiIncompleteGamma_one_left hz, cpow_one]
    field_simp

/-- **The poles of `γ(·, z)`**: for `z ≠ 0`, `(a + n) γ(a, z) → (−1)ⁿ/n!` as `a → −n`. -/
theorem tendsto_mul_lowerIncompleteGamma (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun a => (a + n) * lowerIncompleteGamma a z) (𝓝[≠] (-n : ℂ))
      (𝓝 ((-1) ^ n / (n ! : ℂ))) := by
  have hP : Tendsto (fun a => regularizedGamma a z) (𝓝[≠] (-(n : ℂ))) (𝓝 1) := by
    rw [← regularizedGamma_neg_natCast n hz]
    exact ((differentiable_regularizedGamma_left hz).continuous.tendsto _).mono_left
      nhdsWithin_le_nhds
  simpa [lowerIncompleteGamma_def, mul_assoc] using (tendsto_add_natCast_mul_Gamma n).mul hP

end Complex
