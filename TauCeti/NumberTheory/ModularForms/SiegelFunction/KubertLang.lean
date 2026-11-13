/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.QExpansion
import TauCeti.RingTheory.PowerSeries.SubringCoeff

/-!
# Fourier expansions of Kubert–Lang Siegel products at infinity

For a finite family `(aᵢ, mᵢ)` of integral numerators `aᵢ : Fin 2 → ℤ` and integer exponents
`mᵢ : ℤ` at level `N`, the product `∏ i ∈ s, g_{aᵢ/N}(τ)^{mᵢ}` factors on the upper half-plane
whenever `12 * N` divides the weighted sum `∑ i ∈ s, mᵢ (6 rᵢ₀² - 6 N rᵢ₀ + N²)` (where
`rᵢ₀ = aᵢ₀ % N`, a condition implied by the Kubert–Lang quadratic congruence hypotheses `h₀` and
`h₁₂` via `twelve_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq`). Under that divisibility
hypothesis `hdvd`, the product is meromorphic at `i∞` in `q_N = e^{2π i τ / N}`, with Laurent
expansion equal to `kubertLangPhase N s a m * q_N ^ kubertLangCuspOrder N s a m` times the
corresponding product of integer powers of the `q_N`-expansions of `siegelThetaDisc N (a i)`.

When additionally `N ∣ ∑ i ∈ s, mᵢ aᵢ₀ aᵢ₁` (`h₀₁`), `kubertLangPhase N s a m` is a `(2N)`-th
root of unity, hence lies in `ℚ(ζ_{2N})` (and in `ℚ(ζ_N)` when `N` is odd). When `aᵢ / N ∉ ℤ²`
for all `i ∈ s` (`ha`), each `siegelThetaDisc N (a i)` has nonzero constant term, so
`kubertLangCuspOrder` is the exact `q_N`-order at infinity and all `q_N`-Laurent coefficients of
the product lie in a subfield `K ⊆ ℂ` containing `e^{2π i / N}` if and only if
`kubertLangPhase N s a m ∈ K`. Paired with `SL₂(ℤ)`-transport (`SiegelFunction.Transform`) and
`Γ(N)`-invariance (`SiegelFunction.Congruence`), these expansions place Kubert–Lang products in
the level-`N` modular function field over `ℚ(ζ_N)`.

## Main definitions and results

* `TauCeti.ModularForm.kubertLangCuspOrder` and `TauCeti.ModularForm.kubertLangPhase`: the integer
  `q_N`-exponent from the `B₂`-prefactors and the constant exponential-prefactor phase, together
  with `*_def` restatements, exponent-family lemmas, and nonvanishing.
* `TauCeti.ModularForm.twelve_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq`: divisibility by `12 * N`
  of the weighted sum of reduced `B₂`-numerators under the Kubert–Lang hypotheses `h₀` and `h₁₂`.
* `TauCeti.ModularForm.kubertLangPhase_pow_two_mul_eq_one`,
  `TauCeti.ModularForm.kubertLangPhase_mem_of_odd`, and
  `TauCeti.ModularForm.kubertLangPhase_mem_of_exp_pi_I_div_mem`: root-of-unity order and subring
  membership of `kubertLangPhase` under `h₀₁`.
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow`,
  `TauCeti.ModularForm.laurentQExpansion_prod_siegelFunction_div_zpow`, and
  `TauCeti.ModularForm.orderTop_laurentQExpansion_prod_siegelFunction_div_zpow`: cusp meromorphy,
  exact `q_N`-expansion (under `hdvd`), and exact `q_N`-order and leading coefficient (under
  `hdvd` and `ha`).
* `TauCeti.ModularForm.forall_laurentQExpansion_prod_siegelFunction_div_zpow_coeff_mem_iff`: all
  `q_N`-coefficients lie in a subfield `K ⊆ ℂ` containing `e^{2π i / N}` iff `kubertLangPhase ∈ K`
  (under `hdvd` and `ha`).

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1 and Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Filter Polynomial
open UpperHalfPlane hiding I
open scoped Real Topology

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

section KubertLang

variable {N : ℕ} [NeZero N]

/-- The integer `q_N`-exponent from the `B₂`-prefactors of `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}`. When `12 * N`
divides the numerator (for instance under the Kubert–Lang divisibility hypotheses `h₀` and `h₁₂`),
this division is exact, and when additionally `aᵢ / N ∉ ℤ²` for all `i ∈ s`, it equals the
`q_N`-order at infinity (`orderTop` and `meromorphicOrderAt`). -/
noncomputable def kubertLangCuspOrder (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) : ℤ :=
  (∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) / (12 * N)

/-- The defining formula of `kubertLangCuspOrder`. -/
theorem kubertLangCuspOrder_def (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangCuspOrder N s a m =
      (∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) /
        (12 * N) :=
  (rfl)

/-- The `B₂`-exponent of the empty product is `0`. -/
@[simp]
theorem kubertLangCuspOrder_empty (N : ℕ) {ι : Type*} (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangCuspOrder N (∅ : Finset ι) a m = 0 := by
  simp [kubertLangCuspOrder_def]

/-- The `B₂`-exponent of a singleton product. -/
theorem kubertLangCuspOrder_singleton (N : ℕ) {ι : Type*} (i : ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangCuspOrder N {i} a m =
      (m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) / (12 * N) := by
  simp [kubertLangCuspOrder_def]

omit [NeZero N] in
/-- Reducing the numerators `a i` modulo `N` leaves `kubertLangCuspOrder` unchanged. -/
@[simp]
theorem kubertLangCuspOrder_mod {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangCuspOrder N s (fun i j ↦ a i j % (N : ℤ)) m = kubertLangCuspOrder N s a m := by
  simp [kubertLangCuspOrder_def]

/-- Negating the exponents negates `kubertLangCuspOrder` when `12 * N` divides the numerator sum. -/
theorem kubertLangCuspOrder_neg {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    kubertLangCuspOrder N s a (-m) = -kubertLangCuspOrder N s a m := by
  obtain ⟨q, hq⟩ := hdvd
  have h12 : (12 * N : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (Int.natCast_ne_zero.mpr (NeZero.ne N))
  simp only [kubertLangCuspOrder_def, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hq]
  rw [show -(12 * (N : ℤ) * q) = (12 * N) * (-q) by ring, Int.mul_ediv_cancel_left _ h12,
    Int.mul_ediv_cancel_left _ h12]

/-- Adding exponent families adds `kubertLangCuspOrder` when `12 * N` divides the first numerator
sum. -/
theorem kubertLangCuspOrder_add {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ)
    (m₁ m₂ : ι → ℤ)
    (hdvd₁ : (12 * N : ℤ) ∣
      ∑ i ∈ s, m₁ i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    kubertLangCuspOrder N s a (m₁ + m₂) =
      kubertLangCuspOrder N s a m₁ + kubertLangCuspOrder N s a m₂ := by
  obtain ⟨q, hq⟩ := hdvd₁
  have h12 : (12 * N : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (Int.natCast_ne_zero.mpr (NeZero.ne N))
  simp only [kubertLangCuspOrder_def, Pi.add_apply, add_mul, Finset.sum_add_distrib, hq]
  rw [Int.mul_add_ediv_left _ _ h12, Int.mul_ediv_cancel_left _ h12]

/-- Scaling the exponents by `k : ℤ` scales `kubertLangCuspOrder` by `k` when `12 * N` divides the
numerator sum. -/
theorem kubertLangCuspOrder_zsmul {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (k : ℤ)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    kubertLangCuspOrder N s a (k • m) = k * kubertLangCuspOrder N s a m := by
  obtain ⟨q, hq⟩ := hdvd
  have h12 : (12 * N : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (Int.natCast_ne_zero.mpr (NeZero.ne N))
  have hsum : ∑ i ∈ s, (k • m) i *
      (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) =
      k * ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [mul_assoc]
  rw [kubertLangCuspOrder_def, kubertLangCuspOrder_def, hsum, hq,
    show k * (12 * (N : ℤ) * q) = (12 * N) * (k * q) by ring,
    Int.mul_ediv_cancel_left _ h12, Int.mul_ediv_cancel_left _ h12]

/-- On a disjoint union, `kubertLangCuspOrder` splits as a sum when `12 * N` divides the first
part's numerator sum. -/
theorem kubertLangCuspOrder_union {ι : Type*} [DecidableEq ι] {s₁ s₂ : Finset ι}
    (hdisj : Disjoint s₁ s₂) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hdvd₁ : (12 * N : ℤ) ∣
      ∑ i ∈ s₁, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    kubertLangCuspOrder N (s₁ ∪ s₂) a m =
      kubertLangCuspOrder N s₁ a m + kubertLangCuspOrder N s₂ a m := by
  obtain ⟨q, hq⟩ := hdvd₁
  have h12 : (12 * N : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (Int.natCast_ne_zero.mpr (NeZero.ne N))
  simp only [kubertLangCuspOrder_def, Finset.sum_union hdisj, hq]
  rw [Int.mul_add_ediv_left _ _ h12, Int.mul_ediv_cancel_left _ h12]

/-- The constant exponential-prefactor phase multiplying
`𝕢 N τ ^ kubertLangCuspOrder N s a m * ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i` in
`prod_siegelFunction_div_zpow_eq`. Under the Kubert–Lang cross-term divisibility
`N ∣ ∑ mᵢ aᵢ₀ aᵢ₁`, this is a `(2N)`-th root of unity. Note that when `N ∣ a i 0` for some
`i ∈ s`, `siegelThetaDisc N (a i) 0 = 1 - e^{2π i aᵢ₁ / N}` also contributes to the leading
Fourier coefficient of the product. -/
noncomputable def kubertLangPhase (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) : ℂ :=
  ∏ i ∈ s,
    ((-1 : ℂ) ^ ((a i 0 / (N : ℤ)) * (a i 1 / (N : ℤ)) +
        a i 0 / (N : ℤ) + a i 1 / (N : ℤ) + 1) *
      cexp (-(π * I * ((a i 0 / (N : ℤ) : ℤ) * ((a i 1 % (N : ℤ) : ℤ) : ℂ) -
        (a i 1 / (N : ℤ) : ℤ) * ((a i 0 % (N : ℤ) : ℤ) : ℂ)) / N)) *
      cexp (π * I * ((a i 1 % (N : ℤ) : ℤ) : ℂ) *
        (((a i 0 % (N : ℤ) : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) ^ m i

/-- The defining product of `kubertLangPhase`. -/
theorem kubertLangPhase_def (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangPhase N s a m =
      ∏ i ∈ s,
        ((-1 : ℂ) ^ ((a i 0 / (N : ℤ)) * (a i 1 / (N : ℤ)) +
            a i 0 / (N : ℤ) + a i 1 / (N : ℤ) + 1) *
          cexp (-(π * I * ((a i 0 / (N : ℤ) : ℤ) * ((a i 1 % (N : ℤ) : ℤ) : ℂ) -
            (a i 1 / (N : ℤ) : ℤ) * ((a i 0 % (N : ℤ) : ℤ) : ℂ)) / N)) *
          cexp (π * I * ((a i 1 % (N : ℤ) : ℤ) : ℂ) *
            (((a i 0 % (N : ℤ) : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) ^ m i :=
  (rfl)

/-- `kubertLangPhase N s a m` is always nonzero. -/
theorem kubertLangPhase_ne_zero (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) : kubertLangPhase N s a m ≠ 0 := by
  rw [kubertLangPhase_def]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
    zpow_ne_zero _ (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num))
      (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _))

/-- The constant phase of the empty product is `1`. -/
@[simp]
theorem kubertLangPhase_empty (N : ℕ) {ι : Type*} (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangPhase N (∅ : Finset ι) a m = 1 := by
  simp [kubertLangPhase_def]

/-- The constant phase of a singleton product. -/
@[simp]
theorem kubertLangPhase_singleton (N : ℕ) {ι : Type*} (i : ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangPhase N {i} a m =
      ((-1 : ℂ) ^ ((a i 0 / (N : ℤ)) * (a i 1 / (N : ℤ)) +
          a i 0 / (N : ℤ) + a i 1 / (N : ℤ) + 1) *
        cexp (-(π * I * ((a i 0 / (N : ℤ) : ℤ) * ((a i 1 % (N : ℤ) : ℤ) : ℂ) -
          (a i 1 / (N : ℤ) : ℤ) * ((a i 0 % (N : ℤ) : ℤ) : ℂ)) / N)) *
        cexp (π * I * ((a i 1 % (N : ℤ) : ℤ) : ℂ) *
          (((a i 0 % (N : ℤ) : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) ^ m i := by
  simp [kubertLangPhase_def]

/-- `kubertLangPhase` is multiplicative on disjoint unions of index sets. -/
theorem kubertLangPhase_union (N : ℕ) {ι : Type*} [DecidableEq ι] {s₁ s₂ : Finset ι}
    (hdisj : Disjoint s₁ s₂) (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangPhase N (s₁ ∪ s₂) a m =
      kubertLangPhase N s₁ a m * kubertLangPhase N s₂ a m := by
  simp [kubertLangPhase_def, Finset.prod_union hdisj]

/-- `kubertLangPhase` turns addition of exponent families into multiplication. -/
theorem kubertLangPhase_add (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m₁ m₂ : ι → ℤ) :
    kubertLangPhase N s a (m₁ + m₂) =
      kubertLangPhase N s a m₁ * kubertLangPhase N s a m₂ := by
  simp only [kubertLangPhase_def, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  exact zpow_add₀ (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num))
    (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)) (m₁ i) (m₂ i)

/-- Negating the exponent family inverts `kubertLangPhase`. -/
theorem kubertLangPhase_neg (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) :
    kubertLangPhase N s a (-m) = (kubertLangPhase N s a m)⁻¹ := by
  simp [kubertLangPhase_def, zpow_neg, Finset.prod_inv_distrib]

/-- Scaling the exponent family by `k : ℤ` raises `kubertLangPhase` to the `k`-th power. -/
theorem kubertLangPhase_zsmul (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) (k : ℤ) :
    kubertLangPhase N s a (k • m) = kubertLangPhase N s a m ^ k := by
  rw [kubertLangPhase_def, kubertLangPhase_def]
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm (n : ℤ), _root_.zpow_mul, zpow_natCast]
  · rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm (-(n : ℤ)), _root_.zpow_mul, zpow_neg, zpow_natCast]

/-- For a single index `i`, `(Nat.gcd 2 N * N : ℤ)` divides `a₀ ^ 2 - (a₀ % N) ^ 2`. -/
private theorem gcd_two_mul_dvd_sq_sub_emod_sq (N : ℕ) (a₀ : ℤ) :
    ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ a₀ ^ 2 - (a₀ % (N : ℤ)) ^ 2 := by
  set r : ℤ := a₀ % (N : ℤ)
  set q : ℤ := a₀ / (N : ℤ)
  have ha : a₀ = q * N + r := (Int.ediv_mul_add_emod a₀ N).symm
  have hsq : a₀ ^ 2 - r ^ 2 = q ^ 2 * N ^ 2 + 2 * q * N * r := by rw [ha]; ring
  rw [hsq]
  refine dvd_add ?_ ?_
  · rcases Nat.even_or_odd N with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hg : Nat.gcd 2 (k + k) = 2 := Nat.gcd_eq_left ⟨k, by ring⟩
      rw [hg]
      exact ⟨q ^ 2 * k, by push_cast; ring⟩
    · have hg : Nat.gcd 2 (2 * k + 1) = 1 :=
        Nat.coprime_two_left.mpr ⟨k, rfl⟩
      rw [hg, one_mul]
      exact ⟨q ^ 2 * (2 * k + 1), by push_cast; ring⟩
  · refine dvd_trans (Nat.cast_dvd_cast (Nat.mul_dvd_mul_right (Nat.gcd_dvd_left 2 N) N)) ?_
    exact ⟨q * r, by push_cast; ring⟩

omit [NeZero N] in
/-- `(3 * N : ℤ)` divides the weighted sum of reduced `B₂`-numerators under the Kubert–Lang
hypotheses `h₀` and `h₁₂`. -/
private theorem three_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hN_sq : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 % (N : ℤ)) ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    (3 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) := by
  set r : ι → ℤ := fun i ↦ a i 0 % (N : ℤ)
  have hS_eq : (∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2)) =
      6 * (∑ i ∈ s, m i * r i ^ 2) +
        (N : ℤ) * ((N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i) := by
    have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) =
        ∑ i ∈ s, (6 * (m i * r i ^ 2) + ((N : ℤ) ^ 2 * m i - 6 * N * (m i * r i))) :=
      Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hS_eq]
  refine dvd_add ⟨2 * ((∑ i ∈ s, m i * r i ^ 2) / N), ?_⟩ ?_
  · have := Int.mul_ediv_cancel' hN_sq
    linear_combination -6 * this
  · have h3_sum : (3 : ℤ) ∣ (N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i := by
      refine dvd_sub ?_ ⟨2 * ∑ i ∈ s, m i * r i, by ring⟩
      by_cases h3N' : (3 : ℕ) ∣ N
      · exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h3N') _
      · have hcop : IsCoprime (3 : ℤ) (Nat.gcd 12 N : ℤ) :=
          Nat.Coprime.isCoprime (Nat.prime_three.coprime_iff_not_dvd.mpr
            (fun h ↦ h3N' (dvd_trans h (Nat.gcd_dvd_right 12 N))))
        have h3_12 : (3 : ℤ) ∣ (Nat.gcd 12 N : ℤ) * ∑ i ∈ s, m i :=
          dvd_trans ⟨4, by norm_num⟩ h₁₂
        exact dvd_mul_of_dvd_right (hcop.dvd_of_dvd_mul_left h3_12) _
    obtain ⟨k, hk⟩ := h3_sum
    exact ⟨k, by rw [hk]; ring⟩

omit [NeZero N] in
/-- `(4 * N : ℤ)` divides the weighted sum of reduced `B₂`-numerators under the Kubert–Lang
hypotheses `h₀` and `h₁₂`. -/
private theorem four_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hr_sq : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 % (N : ℤ)) ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    (4 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) := by
  set r : ι → ℤ := fun i ↦ a i 0 % (N : ℤ)
  set S : ℤ := ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2)
  have hret : (4 * (N : ℤ) ∣ S) →
      (4 * (N : ℤ) ∣ ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2)) := id
  refine hret ?_
  rcases Nat.even_or_odd N with ⟨k, hN⟩ | ⟨k, hN⟩
  · -- Case `N = 2k` even: use `2N ∣ ∑ mᵢ rᵢ²` and `2 ∣ ∑ mᵢ` whenever `4 ∤ N`.
    have hg : Nat.gcd 2 N = 2 := Nat.gcd_eq_left ⟨k, by omega⟩
    have h2N_sq : (2 * (N : ℤ)) ∣ ∑ i ∈ s, m i * r i ^ 2 := by
      simpa [hg, Nat.cast_mul, mul_assoc] using hr_sq
    have h2_sq : (2 : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 := dvd_trans ⟨(N : ℤ), by ring⟩ h2N_sq
    have h2_lin : (2 : ℤ) ∣ ∑ i ∈ s, m i * r i := by
      have hdiff : (2 : ℤ) ∣ ∑ i ∈ s, m i * (r i ^ 2 - r i) :=
        Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right (by
          rcases Int.even_or_odd (r i) with ⟨u, hu⟩ | ⟨u, hu⟩
          · exact ⟨2 * u ^ 2 - u, by rw [hu]; ring⟩
          · exact ⟨2 * u ^ 2 + u, by rw [hu]; ring⟩) _
      have heq : (∑ i ∈ s, m i * r i) =
          (∑ i ∈ s, m i * r i ^ 2) - ∑ i ∈ s, m i * (r i ^ 2 - r i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [heq]
      exact dvd_sub h2_sq hdiff
    have h4_mul : (4 : ℤ) ∣ (N : ℤ) * ∑ i ∈ s, m i := by
      by_cases h4k : 4 ∣ N
      · exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h4k) _
      · have h2sum : (2 : ℤ) ∣ ∑ i ∈ s, m i := by
          have hdvd6 : Nat.gcd 12 N ∣ 6 := by
            have h12 : Nat.gcd 12 N ∣ 12 := Nat.gcd_dvd_left 12 N
            have hndvd : ¬ 4 ∣ Nat.gcd 12 N := fun h ↦
              h4k (dvd_trans h (Nat.gcd_dvd_right 12 N))
            generalize Nat.gcd 12 N = d at h12 hndvd
            have hle : d ≤ 12 := Nat.le_of_dvd (by norm_num) h12
            interval_cases d <;> omega
          obtain ⟨u, hu⟩ := hdvd6
          have hdvd12 : (2 * Nat.gcd 12 N : ℤ) ∣ (12 : ℤ) :=
            ⟨(u : ℤ), by exact_mod_cast (by linarith : 12 = 2 * Nat.gcd 12 N * u)⟩
          have h2g : (Nat.gcd 12 N : ℤ) * 2 ∣ (Nat.gcd 12 N : ℤ) * ∑ i ∈ s, m i := by
            rw [mul_comm (Nat.gcd 12 N : ℤ) 2]
            exact dvd_trans hdvd12 h₁₂
          have hgpos : (Nat.gcd 12 N : ℤ) ≠ 0 :=
            Int.natCast_ne_zero.mpr (Nat.gcd_pos_of_pos_left N (by norm_num)).ne'
          exact (Int.mul_dvd_mul_iff_left hgpos).mp h2g
        obtain ⟨u, hu⟩ := h2sum
        exact ⟨(k : ℤ) * u, by rw [hN, hu]; push_cast; ring⟩
    have hS_eq : S = 6 * (∑ i ∈ s, m i * r i ^ 2) +
        (N : ℤ) * ((N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i) := by
      have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) =
          ∑ i ∈ s, (6 * (m i * r i ^ 2) + ((N : ℤ) ^ 2 * m i - 6 * N * (m i * r i))) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      dsimp only [S]
      rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hS_eq]
    refine dvd_add (dvd_trans ⟨3, by ring⟩ (mul_dvd_mul_left 6 h2N_sq)) ?_
    rw [mul_comm 4 _]
    refine mul_dvd_mul_left _ (dvd_sub h4_mul ?_)
    obtain ⟨u, hu⟩ := h2_lin
    exact ⟨3 * u, by rw [hu]; ring⟩
  · -- Case `N = 2k + 1` odd: `4 ∣ S` and `N ∣ S` with `Coprime 4 N` give `4N ∣ S`.
    have hcop4 : Nat.Coprime 4 N := by
      rw [hN]
      simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr ⟨k, rfl⟩)
    have hN_sq : (N : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 :=
      dvd_trans ⟨(Nat.gcd 2 N : ℤ), by push_cast; ring⟩ hr_sq
    have hN_S : (N : ℤ) ∣ S := by
      have hS_eq : S = 6 * (∑ i ∈ s, m i * r i ^ 2) +
          (N : ℤ) * ((N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i) := by
        have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) =
            ∑ i ∈ s, (6 * (m i * r i ^ 2) + ((N : ℤ) ^ 2 * m i - 6 * N * (m i * r i))) :=
          Finset.sum_congr rfl fun i _ ↦ by ring
        dsimp only [S]
        rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      rw [hS_eq]
      exact dvd_add (dvd_mul_of_dvd_right hN_sq 6) (dvd_mul_right _ _)
    have h4_S : (4 : ℤ) ∣ S := by
      have hS_even : S = (∑ i ∈ s, m i * (6 * r i * (r i - N))) +
          ((N : ℤ) ^ 2) * ∑ i ∈ s, m i := by
        have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) =
            ∑ i ∈ s, (m i * (6 * r i * (r i - N)) + (N : ℤ) ^ 2 * m i) :=
          Finset.sum_congr rfl fun i _ ↦ by ring
        dsimp only [S]
        rw [hsum1, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hS_even]
      refine dvd_add ?_ ?_
      · refine Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right ?_ _
        rcases Int.even_or_odd (r i) with ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨3 * u * (u + u - N), by rw [hu]; ring⟩
        · exact ⟨3 * (2 * u + 1) * (u - k), by rw [hu, hN]; push_cast; ring⟩
      · have hcop : IsCoprime (4 : ℤ) (Nat.gcd 12 N : ℤ) :=
          Nat.Coprime.isCoprime (hcop4.coprime_dvd_right (Nat.gcd_dvd_right 12 N))
        have h4_12 : (4 : ℤ) ∣ (Nat.gcd 12 N : ℤ) * ∑ i ∈ s, m i :=
          dvd_trans ⟨3, by norm_num⟩ h₁₂
        exact dvd_mul_of_dvd_right (hcop.dvd_of_dvd_mul_left h4_12) _
    obtain ⟨T, hT⟩ := hN_S
    rw [hT, mul_comm 4 _]
    exact mul_dvd_mul_left _ ((Nat.Coprime.isCoprime hcop4).dvd_of_dvd_mul_left (hT ▸ h4_S))

/-- Under the Kubert–Lang congruence hypotheses, `12 * N` divides the sum of reduced `B₂`
numerators, so `kubertLangCuspOrder N s a m` is exact (with zero remainder). -/
theorem twelve_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) := by
  set r : ι → ℤ := fun i ↦ a i 0 % (N : ℤ)
  -- Transfer `gcd(2, N) * N` divisibility from `a i 0 ^ 2` to `(a i 0 % N) ^ 2`.
  have hr_diff : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 ^ 2 - r i ^ 2) :=
    Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right (gcd_two_mul_dvd_sq_sub_emod_sq N (a i 0)) _
  have hr_sq : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 := by
    have hsub : (∑ i ∈ s, m i * r i ^ 2) =
        (∑ i ∈ s, m i * a i 0 ^ 2) - ∑ i ∈ s, m i * (a i 0 ^ 2 - r i ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsub]
    exact dvd_sub h₀ hr_diff
  have hN_sq : (N : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 :=
    dvd_trans ⟨(Nat.gcd 2 N : ℤ), by push_cast; ring⟩ hr_sq
  -- Combine `3N ∣ S` and `4N ∣ S` to get `12N ∣ S`.
  obtain ⟨T, hT⟩ : (N : ℤ) ∣ ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) := by
    have hS_eq : (∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2)) =
        6 * (∑ i ∈ s, m i * r i ^ 2) +
          (N : ℤ) * ((N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i) := by
      have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) =
          ∑ i ∈ s, (6 * (m i * r i ^ 2) + ((N : ℤ) ^ 2 * m i - 6 * N * (m i * r i))) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hS_eq]
    exact dvd_add (dvd_mul_of_dvd_right hN_sq 6) (dvd_mul_right _ _)
  have hN_ne : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have h3T : (3 : ℤ) ∣ T := by
    obtain ⟨k, hk⟩ := three_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq s a m hN_sq h₁₂
    exact ⟨k, mul_left_cancel₀ hN_ne (by linear_combination -hT + hk)⟩
  have h4T : (4 : ℤ) ∣ T := by
    obtain ⟨k, hk⟩ := four_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq s a m hr_sq h₁₂
    exact ⟨k, mul_left_cancel₀ hN_ne (by linear_combination -hT + hk)⟩
  obtain ⟨a3, ha3⟩ := h3T
  obtain ⟨b4, hb4⟩ := h4T
  refine ⟨a3 - b4, ?_⟩
  rw [hT]
  linear_combination (N : ℤ) * (4 * ha3 - 3 * hb4)

/-- Under the Kubert–Lang cross-term divisibility `N ∣ ∑ mᵢ aᵢ₀ aᵢ₁`, `kubertLangPhase N s a m`
is a `(2N)`-th root of unity. -/
theorem kubertLangPhase_pow_two_mul_eq_one {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) :
    kubertLangPhase N s a m ^ (2 * N) = 1 := by
  set r : ι → Fin 2 → ℤ := fun i j ↦ a i j % (N : ℤ)
  set q : ι → Fin 2 → ℤ := fun i j ↦ a i j / (N : ℤ)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [kubertLangPhase_def, ← Finset.prod_pow]
  -- Reduce each vector's `(2 * N)`-th power via `neg_one_zpow_mul_exp_mul_exp_pow_two_mul`.
  have hsplit : ∏ i ∈ s, (((-1 : ℂ) ^ (q i 0 * q i 1 + q i 0 + q i 1 + 1) *
      cexp (-(π * I * ((q i 0 : ℂ) * (r i 1 : ℂ) - (q i 1 : ℂ) * (r i 0 : ℂ)) / N)) *
      cexp (π * I * (r i 1 : ℂ) * ((r i 0 : ℂ) - N) / (N : ℂ) ^ 2)) ^ m i) ^ (2 * N) =
      ∏ i ∈ s, cexp ((2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm (m i), _root_.zpow_mul, zpow_natCast,
      neg_one_zpow_mul_exp_mul_exp_pow_two_mul, ← _root_.zpow_mul, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [hsplit, ← Complex.exp_sum]
  -- Transfer `N ∣ ∑ mᵢ aᵢ₀ aᵢ₁` to `N ∣ ∑ mᵢ rᵢ₁ (rᵢ₀ - N)`.
  have hdvd : (N : ℤ) ∣ ∑ i ∈ s, m i * r i 1 * (r i 0 - N) := by
    have hdiff : (N : ℤ) ∣ ∑ i ∈ s, m i * (r i 1 * (r i 0 - N) - a i 0 * a i 1) := by
      refine Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right ?_ _
      have ha0 : a i 0 = q i 0 * N + r i 0 := (Int.ediv_mul_add_emod (a i 0) N).symm
      have ha1 : a i 1 = q i 1 * N + r i 1 := (Int.ediv_mul_add_emod (a i 1) N).symm
      rw [ha0, ha1]
      exact ⟨-(r i 1 + q i 0 * q i 1 * N + q i 0 * r i 1 + r i 0 * q i 1), by ring⟩
    have hsum : (∑ i ∈ s, m i * r i 1 * (r i 0 - N)) =
        (∑ i ∈ s, m i * (r i 1 * (r i 0 - N) - a i 0 * a i 1)) +
          ∑ i ∈ s, m i * (a i 0 * a i 1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum]
    exact dvd_add hdiff h₀₁
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (∑ i ∈ s, (2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) =
      (k : ℂ) * (2 * π * I) := by
    have hsum : (∑ i ∈ s, (2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) =
        (2 * π * I / N) * ((∑ i ∈ s, m i * r i 1 * (r i 0 - N) : ℤ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum, hk]
    push_cast
    field_simp
  rw [hk', Complex.exp_int_mul_two_pi_mul_I]

/-- If `kubertLangPhase N s a m` is an `N`-th root of unity, then it lies in every subring
containing `e^{2π i / N}`. -/
theorem kubertLangPhase_mem_of_pow_eq_one (S : Subring ℂ)
    (hζ : cexp (2 * π * I / N) ∈ S) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) (hpow : kubertLangPhase N s a m ^ N = 1) :
    kubertLangPhase N s a m ∈ S := by
  obtain ⟨k, _, hk⟩ :=
    (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).eq_pow_of_pow_eq_one hpow
  rw [← hk]
  exact pow_mem hζ k

/-- When `N` is odd and `N ∣ ∑ mᵢ aᵢ₀ aᵢ₁`, `kubertLangPhase N s a m` lies in every subring
containing `e^{2π i / N}`. -/
theorem kubertLangPhase_mem_of_odd (S : Subring ℂ)
    (hζ : cexp (2 * π * I / N) ∈ S) (hN : Odd N) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) :
    kubertLangPhase N s a m ∈ S := by
  have h2N : (kubertLangPhase N s a m ^ N) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm N 2]
    exact kubertLangPhase_pow_two_mul_eq_one s a m h₀₁
  rcases sq_eq_one_iff.mp h2N with h1 | hneg1
  · exact kubertLangPhase_mem_of_pow_eq_one S hζ s a m h1
  · have hpow : (-kubertLangPhase N s a m) ^ N = 1 := by
      rw [hN.neg_pow, hneg1, neg_neg]
    obtain ⟨k, _, hk⟩ :=
      (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).eq_pow_of_pow_eq_one hpow
    rw [show kubertLangPhase N s a m = -(cexp (2 * π * I / N) ^ k) by rw [hk, neg_neg]]
    exact S.neg_mem (pow_mem hζ k)

/-- Under `N ∣ ∑ mᵢ aᵢ₀ aᵢ₁`, `kubertLangPhase N s a m` lies in every subring containing the
`(2N)`-th root of unity `e^{π i / N}`. -/
theorem kubertLangPhase_mem_of_exp_pi_I_div_mem (S : Subring ℂ)
    (hζ : cexp (π * I / N) ∈ S) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) :
    kubertLangPhase N s a m ∈ S := by
  have hprim : IsPrimitiveRoot (cexp (π * I / N)) (2 * N) := by
    have heq : 2 * π * I / ((2 * N : ℕ) : ℂ) = π * I / N := by
      push_cast
      ring
    simpa only [heq] using Complex.isPrimitiveRoot_exp (2 * N) (Nat.mul_ne_zero two_ne_zero
      (NeZero.ne N))
  obtain ⟨k, _, hk⟩ := hprim.eq_pow_of_pow_eq_one (kubertLangPhase_pow_two_mul_eq_one s a m h₀₁)
  rw [← hk]
  exact pow_mem hζ k

/-- Exact factorization of a product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` into its constant phase,
`𝕢 N τ ^ kubertLangCuspOrder N s a m`, and the product of powers of `siegelThetaDisc`, assuming
`12 * N` divides the weighted sum of reduced `B₂`-numerators (implied by the Kubert–Lang
hypotheses via `twelve_mul_dvd_sum_mul_six_mul_emod_sq_sub_add_sq`). -/
theorem prod_siegelFunction_div_zpow_eq {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2))
    (τ : ℍ) :
    ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i =
      kubertLangPhase N s a m *
        𝕢 N τ ^ kubertLangCuspOrder N s a m *
        ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i := by
  have h12 : (12 * N : ℤ) * kubertLangCuspOrder N s a m =
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) :=
    Int.mul_ediv_cancel' hdvd
  have hprod : ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i =
      kubertLangPhase N s a m *
        (∏ i ∈ s, cexp (π * I * bernoulliFun 2 (((a i 0 % (N : ℤ) : ℤ) : ℝ) / N) * τ) ^ m i) *
        ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i := by
    simp only [siegelFunction_div_eq, mul_zpow, Finset.prod_mul_distrib, kubertLangPhase]
  rw [hprod]
  congr 2
  simp_rw [← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Function.Periodic.qParam, ← Complex.exp_int_mul]
  congr 1
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h12' : (12 * N : ℂ) * (kubertLangCuspOrder N s a m : ℂ) =
      ∑ i ∈ s, (m i : ℂ) * (6 * ((a i 0 % (N : ℤ) : ℤ) : ℂ) ^ 2 -
        6 * N * ((a i 0 % (N : ℤ) : ℤ) : ℂ) + (N : ℂ) ^ 2) := by
    exact_mod_cast h12
  have hB : ∑ i ∈ s, (m i : ℂ) * (π * I *
      (bernoulliFun 2 (((a i 0 % (N : ℤ) : ℤ) : ℝ) / N) : ℂ) * τ) =
      (∑ i ∈ s, (m i : ℂ) * (6 * ((a i 0 % (N : ℤ) : ℤ) : ℂ) ^ 2 -
        6 * N * ((a i 0 % (N : ℤ) : ℤ) : ℂ) + (N : ℂ) ^ 2)) *
        (π * I * τ / (6 * (N : ℂ) ^ 2)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [bernoulliFun_two]
    push_cast
    field_simp
  rw [hB, ← h12']
  push_cast
  field_simp
  ring

/-- The cusp function of a product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` at period `N` is meromorphic at `0`
whenever `12 * N` divides the weighted sum of reduced `B₂`-numerators. -/
theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) 0 := by
  have hfun : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) =
      (fun τ : ℍ ↦ kubertLangPhase N s a m * 𝕢 N τ ^ kubertLangCuspOrder N s a m) *
        ∏ i ∈ s, (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ^ m i := by
    funext τ
    simpa [Pi.mul_apply, Finset.prod_apply] using
      prod_siegelFunction_div_zpow_eq s a m hdvd τ
  rw [hfun]
  refine UpperHalfPlane.meromorphicAt_cuspFunction_mul ?_ ?_
  · exact UpperHalfPlane.meromorphicAt_cuspFunction_mul
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow N _)
  · exact UpperHalfPlane.meromorphicAt_cuspFunction_prod s fun i _ ↦
      UpperHalfPlane.meromorphicAt_cuspFunction_zpow
        (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i)).meromorphicAt (m i)

/-- Exact `q_N`-Laurent expansion of a product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` whenever `12 * N` divides
the weighted sum of reduced `B₂`-numerators. -/
theorem laurentQExpansion_prod_siegelFunction_div_zpow {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) =
      HahnSeries.single (kubertLangCuspOrder N s a m) (kubertLangPhase N s a m) *
        ∏ i ∈ s,
          (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i := by
  have hfun : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) =
      ((fun _ : ℍ ↦ kubertLangPhase N s a m) *
        fun τ : ℍ ↦ 𝕢 N τ ^ kubertLangCuspOrder N s a m) *
        ∏ i ∈ s, (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ^ m i := by
    funext τ
    simpa [Pi.mul_apply, Finset.prod_apply] using
      prod_siegelFunction_div_zpow_eq s a m hdvd τ
  have hm_pre : MeromorphicAt (cuspFunction N
      ((fun _ : ℍ ↦ kubertLangPhase N s a m) *
        fun τ : ℍ ↦ 𝕢 N τ ^ kubertLangCuspOrder N s a m)) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_mul
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow N _)
  have hm_i (i : ι) : MeromorphicAt (cuspFunction N
      ((fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ^ m i)) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_zpow
      (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i)).meromorphicAt (m i)
  have hm_prod : MeromorphicAt (cuspFunction N
      (∏ i ∈ s, (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ^ m i)) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_prod s fun i _ ↦ hm_i i
  rw [hfun, UpperHalfPlane.laurentQExpansion_mul hm_pre hm_prod,
    UpperHalfPlane.laurentQExpansion_mul (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow N _),
    UpperHalfPlane.laurentQExpansion_const,
    UpperHalfPlane.laurentQExpansion_qParam_zpow (Nat.cast_pos.mpr (NeZero.pos N)),
    UpperHalfPlane.laurentQExpansion_prod s fun i _ ↦ hm_i i]
  congr 1
  · rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [UpperHalfPlane.laurentQExpansion_zpow
        (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i)).meromorphicAt,
      UpperHalfPlane.laurentQExpansion_of_analyticAt
        (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i))]

/-- Helper lifting
`∏ i ∈ s, (qExpansion N (siegelThetaDisc N (a i) ∘ 𝕢 N) : LaurentSeries ℂ) ^ m i` to a unit
power series over a subfield `K` containing `e^{2π i / N}` whenever `aᵢ / N ∉ ℤ²`. -/
private theorem exists_powerSeries_unit_prod_siegelThetaDisc (K : Subfield ℂ)
    (hζ : cexp (2 * π * I / N) ∈ K) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j) :
    ∃ u : (PowerSeries K)ˣ,
      (PowerSeries.map K.subtype (u : PowerSeries K) : LaurentSeries ℂ) =
        ∏ i ∈ s,
          (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i ∧
      ((PowerSeries.constantCoeff (u : PowerSeries K) : K) : ℂ) =
        ∏ i ∈ s, siegelThetaDisc N (a i) 0 ^ m i := by
  classical
  have hθ_mem (i : ι) (hi : i ∈ s) :
      ∃ Q : PowerSeries K,
        PowerSeries.map K.subtype Q =
          qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ∧
        IsUnit Q := by
    obtain ⟨Q, hQ⟩ := (PowerSeries.mem_map_range K.subtype).mpr
      (fun k ↦ by simpa using qExpansion_siegelThetaDisc_coeff_mem (a i) K.toSubring hζ k)
    refine ⟨Q, hQ, ?_⟩
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    intro h0
    have h0' : ((PowerSeries.constantCoeff Q : K) : ℂ) = 0 := congrArg Subtype.val h0
    have hcoeff0 : (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ))).coeff 0 = 0 := by
      rw [← hQ, PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
      exact h0'
    rw [qExpansion_siegelThetaDisc_coeff_zero] at hcoeff0
    exact siegelThetaDisc_zero_ne_zero (N := N) (a i) (ha i hi) hcoeff0
  choose Q hQ_eq hQ_unit using hθ_mem
  let φ : PowerSeries K →+* LaurentSeries ℂ :=
    (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map K.subtype)
  let u : (PowerSeries K)ˣ := ∏ i ∈ s.attach, (hQ_unit i.1 i.2).unit ^ m i.1
  refine ⟨u, ?_, ?_⟩
  · have hu_eq : φ (u : PowerSeries K) =
        ((Units.map φ.toMonoidHom u : (LaurentSeries ℂ)ˣ) : LaurentSeries ℂ) :=
      (Units.coe_map φ.toMonoidHom u).symm
    rw [show (PowerSeries.map K.subtype (u : PowerSeries K) : LaurentSeries ℂ) =
        φ (u : PowerSeries K) from rfl, hu_eq]
    simp only [u, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, IsUnit.unit_spec]
    rw [← Finset.prod_attach s fun i ↦
      (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    congr 1
    exact congrArg (HahnSeries.ofPowerSeries ℤ ℂ) (hQ_eq i.1 i.2)
  · have hconst (i : s) : ((PowerSeries.constantCoeff ((hQ_unit i.1 i.2).unit : PowerSeries K) :
        K) : ℂ) = siegelThetaDisc N (a i.1) 0 := by
      rw [IsUnit.unit_spec, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (PowerSeries.coeff_map K.subtype 0 (Q i.1 i.2)).symm.trans
        (by rw [hQ_eq i.1 i.2, qExpansion_siegelThetaDisc_coeff_zero])
    let ψ : PowerSeries K →+* ℂ := K.subtype.comp PowerSeries.constantCoeff
    have hψ_u : ((PowerSeries.constantCoeff (u : PowerSeries K) : K) : ℂ) =
        ((Units.map ψ.toMonoidHom u : ℂˣ) : ℂ) :=
      (Units.coe_map ψ.toMonoidHom u).symm
    rw [hψ_u]
    simp only [u, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [← Finset.prod_attach s fun i ↦ siegelThetaDisc N (a i) 0 ^ m i]
    exact Finset.prod_congr rfl fun i _ ↦ by
      congr 1
      exact hconst i

/-- When `12 * N` divides the weighted sum of reduced `B₂`-numerators and `aᵢ / N ∉ ℤ²` for
all `i ∈ s`, the `q_N`-order of `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` equals `kubertLangCuspOrder N s a m`. -/
theorem orderTop_laurentQExpansion_prod_siegelFunction_div_zpow {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i).orderTop =
      (kubertLangCuspOrder N s a m : WithTop ℤ) := by
  obtain ⟨u, hu_eq, _⟩ :=
    exists_powerSeries_unit_prod_siegelThetaDisc (⊤ : Subfield ℂ) trivial s a m ha
  set P : PowerSeries ℂ :=
    PowerSeries.map (⊤ : Subfield ℂ).subtype (u : PowerSeries (⊤ : Subfield ℂ))
  have hP0 : PowerSeries.constantCoeff P ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff]
    exact Subtype.coe_ne_coe.mpr
      (PowerSeries.isUnit_iff_constantCoeff.mp u.isUnit).ne_zero
  have hP_ord : P.order = 0 :=
    PowerSeries.order_zero_of_isUnit
      (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hP0))
  have hP_ordTop : (P : LaurentSeries ℂ).orderTop = 0 := by
    rw [PowerSeries.orderTop_coe, hP_ord]
    rfl
  rw [laurentQExpansion_prod_siegelFunction_div_zpow s a m hdvd, ← hu_eq,
    HahnSeries.orderTop_mul, HahnSeries.orderTop_single (kubertLangPhase_ne_zero N s a m),
    hP_ordTop, add_zero]

/-- When `12 * N` divides the weighted sum of reduced `B₂`-numerators and `aᵢ / N ∉ ℤ²` for
all `i ∈ s`, the meromorphic order at `0` of the cusp function of `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}`
equals `kubertLangCuspOrder N s a m`. -/
theorem meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) 0 =
      (kubertLangCuspOrder N s a m : WithTop ℤ) := by
  rw [← UpperHalfPlane.orderTop_laurentQExpansion
    (meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow s a m hdvd)]
  exact orderTop_laurentQExpansion_prod_siegelFunction_div_zpow s a m ha hdvd

/-- Under `hdvd` and `aᵢ / N ∉ ℤ²`, the leading `q_N`-coefficient of `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}`
(at exponent `kubertLangCuspOrder N s a m`) is
`kubertLangPhase N s a m * ∏ i ∈ s, siegelThetaDisc N (a i) 0 ^ m i`. -/
theorem laurentQExpansion_prod_siegelFunction_div_zpow_coeff_kubertLangCuspOrder {ι : Type*}
    (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i).coeff
          (kubertLangCuspOrder N s a m) =
      kubertLangPhase N s a m * ∏ i ∈ s, siegelThetaDisc N (a i) 0 ^ m i := by
  obtain ⟨u, hu_eq, hu_const⟩ :=
    exists_powerSeries_unit_prod_siegelThetaDisc (⊤ : Subfield ℂ) trivial s a m ha
  rw [laurentQExpansion_prod_siegelFunction_div_zpow s a m hdvd, ← hu_eq,
    HahnSeries.coeff_single_mul, sub_self, PowerSeries.coeff_coe,
    ite_eq_right (not_lt.mpr le_rfl), Int.natAbs_zero, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff]
  exact congrArg (kubertLangPhase N s a m * ·) hu_const

/-- Let `K` be a subfield of `ℂ` containing `e^{2π i / N}`, assume `aᵢ / N ∉ ℤ²` for all `i ∈ s`,
and assume `12 * N` divides `∑ i ∈ s, mᵢ (6 (aᵢ₀ % N)² - 6 N (aᵢ₀ % N) + N²)` (for instance via
the Kubert–Lang hypotheses `h₀` and `h₁₂`). Then every `q_N`-Laurent coefficient of
`∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` lies in `K` if and only if `kubertLangPhase N s a m ∈ K`. -/
theorem forall_laurentQExpansion_prod_siegelFunction_div_zpow_coeff_mem_iff (K : Subfield ℂ)
    (hζ : cexp (2 * π * I / N) ∈ K) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j)
    (hdvd : (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) :
    (∀ n : ℤ, (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i).coeff n ∈ K) ↔
      kubertLangPhase N s a m ∈ K := by
  obtain ⟨u, hu_eq, _⟩ :=
    exists_powerSeries_unit_prod_siegelThetaDisc K hζ s a m ha
  have hu_coeff (k : ℤ) :
      ((PowerSeries.map K.subtype (u : PowerSeries K) : LaurentSeries ℂ).coeff k) ∈ K := by
    rw [PowerSeries.coeff_coe]
    split_ifs
    · exact K.zero_mem
    · rw [PowerSeries.coeff_map]
      exact ((u : PowerSeries K).coeff k.natAbs).2
  have hu0 :
      ((PowerSeries.map K.subtype (u : PowerSeries K) : LaurentSeries ℂ).coeff 0) ≠ 0 := by
    rw [PowerSeries.coeff_coe, ite_eq_right (not_lt.mpr le_rfl), Int.natAbs_zero,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
    exact Subtype.coe_ne_coe.mpr
      (PowerSeries.isUnit_iff_constantCoeff.mp u.isUnit).ne_zero
  rw [laurentQExpansion_prod_siegelFunction_div_zpow s a m hdvd, ← hu_eq]
  constructor
  · intro h
    have h0 := h (kubertLangCuspOrder N s a m)
    rw [HahnSeries.coeff_single_mul, sub_self] at h0
    have hdiv := K.div_mem h0 (hu_coeff 0)
    rwa [mul_div_cancel_right₀ _ hu0] at hdiv
  · intro hphase n
    rw [HahnSeries.coeff_single_mul]
    exact K.mul_mem hphase (hu_coeff _)

end KubertLang

end TauCeti.ModularForm
