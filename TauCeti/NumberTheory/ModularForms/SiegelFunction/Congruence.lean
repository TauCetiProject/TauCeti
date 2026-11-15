/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Transform
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.Data.ZMod.Two
import TauCeti.LinearAlgebra.Matrix.RationalVector
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.SiegelFunction.LevelThree

/-!
# Congruence invariance of powers and products of Siegel functions

For a row vector `r = a / N` with integral numerator, the power
`g_r ^ (12 * N / gcd(6, N))` is invariant under the principal congruence subgroup
`Γ(N)`. More generally, twelfth powers transform by the right matrix action on
`r`, and `g_r ^ (12 * k)` is unchanged by integral translations of `r` whenever
both coordinates of `6 * k * r` are integers.

The second part of the file proves the Kubert–Lang criterion for a finite product
`∏ g_{aᵢ/N}^{mᵢ}` with integral numerators `aᵢ` and integral exponents `mᵢ`. Suppose that
`gcd(2, N) N` divides `∑ mᵢ aᵢ₁²` and `∑ mᵢ aᵢ₂²`, and `N` divides `∑ mᵢ aᵢ₁ aᵢ₂` (the
quadratic relations). Then under `γ ∈ Γ(N)` the product is multiplied by exactly
`ε ^ ∑ mᵢ`, where `ε` is the multiplier with `g_r(γ τ) = ε g_{r γ}(τ)`. Indeed, writing
`γ = 1 + N B`, each factor is translated by `aᵢ B`. The resulting roots of unity cancel by
a parity computation modulo `2N` that uses `det γ = 1`. The multiplier itself has order
dividing `12 / gcd(12, N)`. This is read off from three products whose behaviour is known
independently: `g₀ g₁ g₂ = 2 ζ₈` at levels `2` and `4`, and the `SL₂(ℤ)`-invariant product of
the four level-three functions. Hence the product is `Γ(N)`-invariant as soon as `12` also
divides `gcd(12, N) ∑ mᵢ`. Unlike the power `12 N / gcd(6, N)`, this condition admits small
exponents. For example `g_{(0, 1/2)}⁴` is invariant under `Γ(6)`.

These statements remove the root-of-unity ambiguity from the transformation law.
They provide the invariance needed to regard the indicated powers and products as modular
functions; they do not assert cusp meromorphy or a Fourier coefficient field.
The parameter is allowed to be integral, in which case the Siegel function vanishes.
For modular units one additionally excludes integral parameters.

## Main results

* `TauCeti.ModularForm.siegelFunction_div_pow_smul_of_mem_Gamma`: `g_{a/N}^{12N / gcd(6, N)}`
  is invariant under `Γ(N)`.
* `TauCeti.ModularForm.prod_siegelFunction_div_zpow_smul_eq_zpow_mul`: under the quadratic
  relations, `∏ g_{aᵢ/N}^{mᵢ}` is multiplied by `ε ^ ∑ mᵢ` under `γ ∈ Γ(N)`.
* `TauCeti.ModularForm.pow_twelve_div_gcd_eq_one_of_mem_Gamma`: the multiplier of `γ ∈ Γ(N)`
  satisfies `ε ^ (12 / gcd(12, N)) = 1`.
* `TauCeti.ModularForm.prod_siegelFunction_div_zpow_smul_of_mem_Gamma`: the Kubert–Lang
  criterion for `∏ g_{aᵢ/N}^{mᵢ}` to be invariant under `Γ(N)`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1, and Chapter 3, §5 (the quadratic
  relations).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.ModularForm

/-- Twelfth multiples of the Siegel function transform without a multiplier:
`g_r(γτ)^(12k) = g_(rγ)(τ)^(12k)`, with a right action on row vectors. -/
theorem siegelFunction_pow_twelve_mul_smul (r : Fin 2 → ℝ) (k : ℕ)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    siegelFunction r ↑(γ • τ) ^ (12 * k) =
      siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ ^
        (12 * k) := by
  obtain ⟨ε, hε, hγ⟩ := exists_siegelFunction_smul_eq_mul γ
  rw [hγ, mul_pow, pow_mul ε, hε, one_pow, one_mul]

/-- Integral translation does not change `g_r^(12k)` when the coordinates of
`6kr` are integral. This includes parameters that are themselves integral. -/
theorem siegelFunction_add_intCast_pow_twelve_mul (r : Fin 2 → ℝ) (s : Fin 2 → ℤ)
    (k : ℕ) (hr : ∀ i, ∃ a : ℤ, (6 * k : ℝ) * r i = a) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (r + fun i ↦ (s i : ℝ)) τ ^ (12 * k) =
      siegelFunction r τ ^ (12 * k) := by
  obtain ⟨a, ha⟩ := hr 0
  obtain ⟨b, hb⟩ := hr 1
  have ha' : (6 * k : ℂ) * (r 0 : ℂ) = a := by exact_mod_cast ha
  have hb' : (6 * k : ℂ) * (r 1 : ℂ) = b := by exact_mod_cast hb
  have hexp : cexp (-(π * I * (s 0 * r 1 - s 1 * r 0))) ^ (12 * k) = 1 := by
    rw [← Complex.exp_nat_mul]
    have heq : ((12 * k : ℕ) : ℂ) * (-(π * I * (s 0 * r 1 - s 1 * r 0))) =
        ((s 1 * a - s 0 * b : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      linear_combination 2 * π * I * ((s 1 : ℂ) * ha' - (s 0 : ℂ) * hb')
    rw [heq, Complex.exp_int_mul, exp_two_pi_mul_I, _root_.one_zpow]
  have hsign (z : ℤ) : ((-1 : ℂ) ^ z) ^ (12 * k) = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
    exact Even.neg_one_zpow ⟨z * (6 * k), by push_cast; ring⟩
  rw [siegelFunction_add_intCast r s hτ, mul_pow, mul_pow, hsign, hexp, one_mul, one_mul]

/-- For an integral numerator `a`, the power `g_(a/N)^(12k)` is invariant under
`Γ(N)` as soon as `N` divides `6k`. -/
theorem siegelFunction_div_pow_twelve_mul_smul_of_mem_Gamma {N : ℕ}
    (a : Fin 2 → ℤ) (k : ℕ) (hk : N ∣ 6 * k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * k) =
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k) := by
  rw [siegelFunction_pow_twelve_mul_smul]
  obtain ⟨s, hs⟩ := (γ : Matrix (Fin 2) (Fin 2) ℤ).exists_vecMul_div_eq_add_intCast
    (K := ℝ) (CongruenceSubgroup.map_eq_one_of_mem_Gamma hγ) a
  rw [hs]
  refine siegelFunction_add_intCast_pow_twelve_mul _ s k ?_ τ.im_pos
  intro i
  by_cases hN : N = 0
  · exact ⟨0, by simp [hN]⟩
  obtain ⟨m, hm⟩ := hk
  refine ⟨(m : ℤ) * a i, ?_⟩
  have hm' : (6 * k : ℝ) = N * m := by exact_mod_cast hm
  rw [hm']
  push_cast
  field_simp

/-- The standard exponent `12N / gcd(6,N)` kills both multipliers for a
level-`N` Siegel function. This is invariance under `Γ(N)`, not a claim about
its Fourier coefficients or its behavior at cusps. -/
theorem siegelFunction_div_pow_smul_of_mem_Gamma {N : ℕ}
    (a : Fin 2 → ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N / Nat.gcd 6 N) =
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N) := by
  have hg : Nat.gcd 6 N ∣ N := Nat.gcd_dvd_right 6 N
  have hexponent : 12 * N / Nat.gcd 6 N = 12 * (N / Nat.gcd 6 N) :=
    Nat.mul_div_assoc 12 hg
  rw [hexponent]
  refine siegelFunction_div_pow_twelve_mul_smul_of_mem_Gamma a _ ?_ hγ τ
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left 6 N
  refine ⟨m, ?_⟩
  calc
    6 * (N / Nat.gcd 6 N) = (Nat.gcd 6 N * m) * (N / Nat.gcd 6 N) :=
      congrArg (· * (N / Nat.gcd 6 N)) hm
    _ = (Nat.gcd 6 N * (N / Nat.gcd 6 N)) * m := by ring
    _ = N * m := by rw [Nat.mul_div_cancel' hg]

/-! ### Products of Siegel functions and the quadratic relations -/

/-- `g_{(0, 1/2)}` has no zero on the upper half-plane, since `g₀ g₁ g₂ = 2 ζ₈`. -/
private theorem siegelFunction_zero_half_ne_zero (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ≠ 0 := by
  intro h
  have h' := siegelFunction_zero_half_mul_half_zero_mul_half_half τ.im_pos
  rw [h, zero_mul, zero_mul] at h'
  exact mul_ne_zero two_ne_zero (Complex.exp_ne_zero _) h'.symm

/-- A multiplier of `γ` for the Siegel functions is nonzero. -/
private theorem ne_zero_of_siegelFunction_smul_eq_mul {γ : SL(2, ℤ)} {ε : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ) :
    ε ≠ 0 := by
  rintro rfl
  have h := hε ![0, 1 / 2] (γ⁻¹ • UpperHalfPlane.I)
  rw [smul_inv_smul, zero_mul] at h
  exact siegelFunction_zero_half_ne_zero _ h

/-- The multiplier of `γ` for the Siegel functions is unique. -/
private theorem eq_of_siegelFunction_smul_eq_mul {γ : SL(2, ℤ)} {ε ε' : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ)
    (hε' : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε' * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ) :
    ε = ε' := by
  have h := (hε (![0, 1 / 2] ᵥ* (↑γ⁻¹ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))
    UpperHalfPlane.I).symm.trans
      (hε' (![0, 1 / 2] ᵥ* (↑γ⁻¹ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))
        UpperHalfPlane.I)
  rw [SpecialLinearGroup.vecMul_map_inv_vecMul_map] at h
  exact mul_right_cancel₀ (siegelFunction_zero_half_ne_zero _) h

/-- The integer `N (s₁ s₂ + s₁ + s₂) - (s₁ a₂ - s₂ a₁)` with `s = a B`: for `γ = 1 + N B`, the
translation `g_{(a/N) γ} = g_{a/N + s}` multiplies `g_{a/N}` by `exp(π i e / N)` for this `e`. -/
private def translationPhase (N : ℤ) (B : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → ℤ) : ℤ :=
  N * ((a ᵥ* B) 0 * (a ᵥ* B) 1 + (a ᵥ* B) 0 + (a ᵥ* B) 1) -
    ((a ᵥ* B) 0 * a 1 - (a ᵥ* B) 1 * a 0)

/-- The transformation of one Siegel function of level `N` under `γ = 1 + N B ∈ Γ(N)`, in terms
of a multiplier `ε` of `γ` and an explicit root of unity. -/
private theorem siegelFunction_div_smul_eq_mul_exp {N : ℕ} (hN : N ≠ 0) {γ : SL(2, ℤ)}
    {B : Matrix (Fin 2) (Fin 2) ℤ} (hB : (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • B)
    {ε : ℂ} (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ)
    (a : Fin 2 → ℤ) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) =
      ε * cexp (translationPhase N B a * (π * I / N)) *
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [hε, hB, Matrix.vecMul_div_eq_add_intCast_vecMul B (Nat.cast_ne_zero.mpr hN) a,
    siegelFunction_add_intCast _ _ τ.im_pos, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul,
    ← Complex.exp_add, mul_assoc ε]
  congr 3
  simp only [translationPhase]
  push_cast
  field_simp
  ring

/-- Parity of the phases in `ZMod 2`: the reduction of `γ = 1 + N B ∈ SL₂(ℤ)` modulo `2`,
together with the trace relation `B₁₁ + B₂₂ + N det B = 0`, forces the needed cancellation. -/
private theorem translationPhase_parity :
    ∀ n b₀₀ b₀₁ b₁₀ b₁₁ u₀ u₁ w : ZMod 2,
      b₀₀ + b₁₁ + n * (b₀₀ * b₁₁ - b₀₁ * b₁₀) = 0 →
      (1 + n * b₀₀) * (1 + n * b₁₁) - n * b₀₁ * (n * b₁₀) = 1 →
      n * (n * (b₀₀ * b₀₁ + b₀₀ + b₀₁) + b₀₁) * u₀ +
        n * (n * (b₁₀ * b₁₁ + b₁₀ + b₁₁) - b₁₀) * u₁ +
        (n * (b₀₀ * b₁₁ + b₁₀ * b₀₁) - b₀₀ + b₁₁) * w = 0 := by
  decide

/-- **The quadratic relations make the phases cancel.** If `γ = 1 + N B ∈ SL₂(ℤ)` and the
family `(a_i, m_i)` satisfies the quadratic relations of level `N`, then the weighted sum of the
phase exponents is divisible by `2N`. -/
private theorem two_mul_dvd_sum_mul_translationPhase {N : ℕ} (hN : N ≠ 0)
    {B : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : (1 + N * B 0 0) * (1 + N * B 1 1) - N * B 0 1 * (N * B 1 0) = 1)
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) :
    2 * (N : ℤ) ∣ ∑ i ∈ s, m i * translationPhase N B (a i) := by
  -- Sort the phase into the three quadratic sums and an even remainder.
  have key (i : ι) : m i * translationPhase N B (a i) =
      (N * (B 0 0 * B 0 1 + B 0 0 + B 0 1) + B 0 1) * (m i * a i 0 ^ 2) +
        (N * (B 1 0 * B 1 1 + B 1 0 + B 1 1) - B 1 0) * (m i * a i 1 ^ 2) +
        (N * (B 0 0 * B 1 1 + B 1 0 * B 0 1) - B 0 0 + B 1 1) * (m i * (a i 0 * a i 1)) -
        N * (m i * ((B 0 0 + B 0 1) * (a i 0 * (a i 0 - 1)) +
          (B 1 0 + B 1 1) * (a i 1 * (a i 1 - 1)))) := by
    simp only [translationPhase, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  obtain ⟨u₀, hu₀⟩ := h₀
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨w, hw⟩ := h₀₁
  obtain ⟨ρ, hρ⟩ : (2 : ℤ) ∣ ∑ i ∈ s, m i * ((B 0 0 + B 0 1) * (a i 0 * (a i 0 - 1)) +
      (B 1 0 + B 1 1) * (a i 1 * (a i 1 - 1))) :=
    Finset.dvd_sum fun i _ ↦ (dvd_add
      ((even_iff_two_dvd.mp (Int.even_mul_pred_self _)).mul_left _)
      ((even_iff_two_dvd.mp (Int.even_mul_pred_self _)).mul_left _)).mul_left _
  rw [hu₀, hu₁, hw, hρ]
  -- The trace relation, from `det γ = 1` after cancelling `N`.
  have htr : B 0 0 + B 1 1 + N * (B 0 0 * B 1 1 - B 0 1 * B 1 0) = 0 := by
    have h : (N : ℤ) * (B 0 0 + B 1 1 + N * (B 0 0 * B 1 1 - B 0 1 * B 1 0)) = 0 := by
      linear_combination hdet
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hN)
  obtain ⟨y, hy⟩ : (2 : ℤ) ∣ (Nat.gcd 2 N : ℤ) * (N * (B 0 0 * B 0 1 + B 0 0 + B 0 1) + B 0 1) *
      u₀ + (Nat.gcd 2 N : ℤ) * (N * (B 1 0 * B 1 1 + B 1 0 + B 1 1) - B 1 0) * u₁ +
      (N * (B 0 0 * B 1 1 + B 1 0 * B 0 1) - B 0 0 + B 1 1) * w := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp ?_
    push_cast
    rw [ZMod.natCast_gcd_two]
    exact translationPhase_parity _ _ _ _ _ _ _ _
      (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) htr)
      (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) hdet)
  exact ⟨y - ρ, by push_cast; linear_combination (N : ℤ) * hy⟩

/-- **Products of Siegel functions under `Γ(N)`.** Let `(a_i, m_i)` be a finite family of
integral numerators and integral exponents satisfying the quadratic relations of level `N`:
`gcd(2, N) N` divides `∑ mᵢ aᵢ₁²` and `∑ mᵢ aᵢ₂²`, and `N` divides `∑ mᵢ aᵢ₁ aᵢ₂`. If `ε` is a
multiplier of `γ ∈ Γ(N)` for the Siegel functions, so that `g_r(γ τ) = ε g_{r γ}(τ)` for every
`r`, then `∏ g_{aᵢ/N}^{mᵢ}` is multiplied by exactly `ε ^ ∑ mᵢ` under `γ`. -/
theorem prod_siegelFunction_div_zpow_smul_eq_zpow_mul {N : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) {ε : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ)
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) (τ : ℍ) :
    ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i =
      ε ^ (∑ i ∈ s, m i) * ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i := by
  rcases eq_or_ne N 0 with rfl | hN
  · -- `Γ(0)` is trivial, and the multiplier of the identity is `1`.
    rw [CongruenceSubgroup.Gamma_zero_bot, Subgroup.mem_bot] at hγ
    subst hγ
    have hε₁ : ε = 1 := eq_of_siegelFunction_smul_eq_mul hε fun r τ ↦ by simp
    simp [hε₁]
  obtain ⟨B, hB⟩ := Matrix.exists_eq_one_add_smul_of_map_eq_one _
    (CongruenceSubgroup.map_eq_one_of_mem_Gamma hγ)
  have hdet : (1 + N * B 0 0) * (1 + N * B 1 1) - N * B 0 1 * (N * B 1 0) = 1 := by
    have hentry (i j : Fin 2) :
        (γ : Matrix (Fin 2) (Fin 2) ℤ) i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + N * B i j := by
      rw [hB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hentry, hentry, hentry, hentry] at h
    simpa using h
  obtain ⟨j, hj⟩ := two_mul_dvd_sum_mul_translationPhase hN hdet s a m h₀ h₁ h₀₁
  -- The roots of unity from the integral translations multiply to `1`.
  have hphase : ∏ i ∈ s, cexp (translationPhase N B (a i) * (π * I / N)) ^ m i = 1 := by
    simp_rw [← Complex.exp_int_mul, ← Complex.exp_sum]
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hsum : ∑ i ∈ s, (m i : ℂ) * (translationPhase N B (a i) * (π * I / N)) =
        j * (2 * π * I) := by
      have h := congrArg (fun x : ℤ ↦ (x : ℂ) * (π * I / N)) hj
      simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul] at h
      rw [Finset.sum_congr rfl fun i _ ↦ by rw [← mul_assoc], h]
      push_cast
      field_simp
    rw [hsum, Complex.exp_int_mul_two_pi_mul_I]
  simp_rw [siegelFunction_div_smul_eq_mul_exp hN hB hε, mul_zpow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hphase, mul_one,
    Finset.prod_zpow_eq_zpow_sum_of_isUnit _ (ne_zero_of_siegelFunction_smul_eq_mul hε).isUnit]

/-! ### The multiplier on `Γ(N)` -/

/-- On `Γ(2)` the multiplier is a sixth root of unity: `(g₀ g₁ g₂)²` is the constant `(2 ζ₈)²`,
and its family `2 · {(0, 1), (1, 0), (1, 1)} / 2` satisfies the quadratic relations of level `2`. -/
private theorem pow_six_eq_one_of_mem_Gamma_two {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma 2) {ε : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ) :
    ε ^ 6 = 1 := by
  have hv (τ : ℍ) : ∏ i, siegelFunction
      (fun j ↦ ((![![0, 1], ![1, 0], ![1, 1]] i j : ℤ) : ℝ) / (2 : ℕ)) τ ^ (2 : ℤ) =
      (2 * cexp (2 * π * I / 8)) ^ 2 := by
    rw [← siegelFunction_zero_half_mul_half_zero_mul_half_half τ.im_pos]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    norm_num [mul_pow]
    congr! <;> rename_i j <;> fin_cases j <;> norm_num
  have h := prod_siegelFunction_div_zpow_smul_eq_zpow_mul hγ hε Finset.univ
    ![![0, 1], ![1, 0], ![1, 1]] (fun _ ↦ 2) (by decide) (by decide) (by decide)
    UpperHalfPlane.I
  rw [hv, hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  have h₀ : (2 * cexp (2 * π * I / 8)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (Complex.exp_ne_zero _))
  have h' : ε ^ (6 : ℤ) = 1 := by
    have := (mul_eq_right₀ h₀).mp h.symm
    simpa using this
  exact_mod_cast h'

/-- On `Γ(4)` the multiplier is a cube root of unity: `g₀ g₁ g₂` is the constant `2 ζ₈`, and its
family `{(0, 2), (2, 0), (2, 2)} / 4` satisfies the quadratic relations of level `4`. -/
private theorem pow_three_eq_one_of_mem_Gamma_four {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma 4) {ε : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ) :
    ε ^ 3 = 1 := by
  have hv (τ : ℍ) : ∏ i, siegelFunction
      (fun j ↦ ((![![0, 2], ![2, 0], ![2, 2]] i j : ℤ) : ℝ) / (4 : ℕ)) τ ^ (1 : ℤ) =
      2 * cexp (2 * π * I / 8) := by
    rw [← siegelFunction_zero_half_mul_half_zero_mul_half_half τ.im_pos]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    congr! <;> rename_i j <;> fin_cases j <;> norm_num
  have h := prod_siegelFunction_div_zpow_smul_eq_zpow_mul hγ hε Finset.univ
    ![![0, 2], ![2, 0], ![2, 2]] (fun _ ↦ 1) (by decide) (by decide) (by decide)
    UpperHalfPlane.I
  rw [hv, hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  have h₀ : 2 * cexp (2 * π * I / 8) ≠ 0 := mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)
  have h' : ε ^ (3 : ℤ) = 1 := by
    have := (mul_eq_right₀ h₀).mp h.symm
    simpa using this
  exact_mod_cast h'

/-- On `Γ(3)` the multiplier is a fourth root of unity: the product of the four level-three
Siegel functions is invariant under `SL₂(ℤ)` and nowhere zero, and its family
`{(0, 1), (1, 0), (1, 1), (1, 2)} / 3` satisfies the quadratic relations of level `3`. -/
private theorem pow_four_eq_one_of_mem_Gamma_three {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma 3) {ε : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ) :
    ε ^ 4 = 1 := by
  have hv (τ : ℍ) : ∏ i, siegelFunction
      (fun j ↦ ((![![0, 1], ![1, 0], ![1, 1], ![1, 2]] i j : ℤ) : ℝ) / (3 : ℕ)) τ ^ (1 : ℤ) =
      siegelFunction ![0, 1 / 3] τ * siegelFunction ![1 / 3, 0] τ *
        siegelFunction ![1 / 3, 1 / 3] τ * siegelFunction ![1 / 3, 2 / 3] τ := by
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    congr! <;> rename_i j <;> fin_cases j <;> norm_num
  have h := prod_siegelFunction_div_zpow_smul_eq_zpow_mul hγ hε Finset.univ
    ![![0, 1], ![1, 0], ![1, 1], ![1, 2]] (fun _ ↦ 1) (by decide) (by decide) (by decide)
    UpperHalfPlane.I
  rw [hv, hv, siegelFunction_zero_third_mul_third_zero_mul_third_third_mul_third_two_thirds_smul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  have hne (r : Fin 2 → ℝ) (hr : r 1 = 1 / 3 ∨ r 0 = 1 / 3) :
      siegelFunction r UpperHalfPlane.I ≠ 0 := by
    refine siegelFunction_ne_zero (fun s hs ↦ ?_) UpperHalfPlane.I.im_pos
    -- A coordinate equal to `1/3` is not an integer.
    have h3 (k : ℤ) (hk : (k : ℝ) = 1 / 3) : False := by
      have : (3 * k : ℝ) = 1 := by rw [hk]; norm_num
      have : 3 * k = 1 := by exact_mod_cast this
      omega
    rcases hr with hr | hr
    · exact h3 (s 1) (by rw [← hr, hs])
    · exact h3 (s 0) (by rw [← hr, hs])
  have h₀ : siegelFunction ![0, 1 / 3] UpperHalfPlane.I * siegelFunction ![1 / 3, 0]
      UpperHalfPlane.I * siegelFunction ![1 / 3, 1 / 3] UpperHalfPlane.I *
      siegelFunction ![1 / 3, 2 / 3] UpperHalfPlane.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hne _ (by simp)) (hne _ (by simp)))
      (hne _ (by simp))) (hne _ (by simp))
  have h' : ε ^ (4 : ℤ) = 1 := by
    have := (mul_eq_right₀ h₀).mp h.symm
    simpa using this
  exact_mod_cast h'

/-- **The multiplier on `Γ(N)`.** If `γ ∈ Γ(N)` and `ε` is a multiplier of `γ` for the Siegel
functions, so that `g_r(γ τ) = ε g_{r γ}(τ)` for every `r`, then `ε` is a root of unity of order
dividing `12 / gcd(12, N)`. In particular `ε = 1` when `12 ∣ N`. -/
theorem pow_twelve_div_gcd_eq_one_of_mem_Gamma {N : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) {ε : ℂ}
    (hε : ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ) :
    ε ^ (12 / Nat.gcd 12 N) = 1 := by
  have h₁ : ε ^ 12 = 1 := by
    obtain ⟨ε', hε'12, hε'⟩ := exists_siegelFunction_smul_eq_mul γ
    rwa [eq_of_siegelFunction_smul_eq_mul hε hε']
  have h₂ (h : 2 ∣ N) : ε ^ 6 = 1 :=
    pow_six_eq_one_of_mem_Gamma_two (CongruenceSubgroup.Gamma_le_Gamma_of_dvd h hγ) hε
  have h₃ (h : 3 ∣ N) : ε ^ 4 = 1 :=
    pow_four_eq_one_of_mem_Gamma_three (CongruenceSubgroup.Gamma_le_Gamma_of_dvd h hγ) hε
  have h₄ (h : 4 ∣ N) : ε ^ 3 = 1 :=
    pow_three_eq_one_of_mem_Gamma_four (CongruenceSubgroup.Gamma_le_Gamma_of_dvd h hγ) hε
  have hdN : Nat.gcd 12 N ∣ N := Nat.gcd_dvd_right 12 N
  have hd : Nat.gcd 12 N ∣ 12 := Nat.gcd_dvd_left 12 N
  have hle : Nat.gcd 12 N ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  generalize Nat.gcd 12 N = d at hdN hd hle ⊢
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 12 := by
    interval_cases d <;> omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂ hdN
  · exact h₃ hdN
  · exact h₄ hdN
  · -- `gcd(12, N) = 6`: both `ε⁶ = 1` and `ε⁴ = 1`.
    have h6 := h₂ (dvd_trans (by norm_num) hdN)
    rw [show 6 = 4 + 2 by rfl, pow_add, h₃ (dvd_trans (by norm_num) hdN), one_mul] at h6
    exact h6
  · -- `gcd(12, N) = 12`: both `ε⁴ = 1` and `ε³ = 1`.
    have h4 := h₃ (dvd_trans (by norm_num) hdN)
    rw [show 4 = 3 + 1 by rfl, pow_add, h₄ (dvd_trans (by norm_num) hdN), one_mul] at h4
    simpa using h4

/-- **The Kubert–Lang congruence criterion.** Let `(a_i, m_i)` be a finite family of integral
numerators and integral exponents such that
* `gcd(2, N) N` divides `∑ mᵢ aᵢ₁²` and `∑ mᵢ aᵢ₂²`,
* `N` divides `∑ mᵢ aᵢ₁ aᵢ₂`, and
* `12` divides `gcd(12, N) ∑ mᵢ`.

Then the product `∏ g_{aᵢ/N}^{mᵢ}` of Siegel functions is invariant under `Γ(N)`. This removes
every root of unity from the transformation law: no power of the product needs to be taken. -/
theorem prod_siegelFunction_div_zpow_smul_of_mem_Gamma {N : ℕ} {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i =
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i := by
  obtain ⟨ε, -, hε⟩ := exists_siegelFunction_smul_eq_mul γ
  rw [prod_siegelFunction_div_zpow_smul_eq_zpow_mul hγ hε s a m h₀ h₁ h₀₁]
  -- `12 / gcd(12, N)` divides `∑ mᵢ`, and kills `ε`.
  have hd : Nat.gcd 12 N * (12 / Nat.gcd 12 N) = 12 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left 12 N)
  obtain ⟨t, ht⟩ : ((12 / Nat.gcd 12 N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i := by
    refine Int.dvd_of_mul_dvd_mul_left (a := Nat.gcd 12 N)
      (by exact_mod_cast (Nat.gcd_pos_of_pos_left N (by norm_num)).ne') ?_
    rw [← Nat.cast_mul, hd, Nat.cast_ofNat]
    exact h₁₂
  rw [ht, _root_.zpow_mul, zpow_natCast, pow_twelve_div_gcd_eq_one_of_mem_Gamma hγ hε,
    _root_.one_zpow, one_mul]

end TauCeti.ModularForm
