/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.QExpansion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# Fourier expansions of Kubert–Lang Siegel products at infinity

For a finite Kubert–Lang family `(aᵢ, mᵢ)` of level `N`, the `B₂`-exponents sum to an integer
multiple of `1 / N`, so the product `∏ g_{aᵢ/N}(τ)^{mᵢ}` is meromorphic in `q_N = e^{2π i τ / N}`
at `0`, with Laurent expansion equal to an explicit `(2N)`-th root of unity times a power of `q_N`
times a product of integer powers of the theta-product expansions over `ℚ(ζ_N)`.

## Main definitions and results

* `TauCeti.ModularForm.kubertLangCuspOrder` and `TauCeti.ModularForm.kubertLangPhase`: the exact
  `q_N`-order and `(2N)`-th root-of-unity phase of a Kubert–Lang product.
* `TauCeti.ModularForm.twelve_mul_dvd_kubertLang_sum`: divisibility by `12 * N` of the weighted
  sum of reduced `B₂`-numerators under the Kubert–Lang quadratic congruence hypotheses.
* `TauCeti.ModularForm.kubertLangPhase_pow_two_mul_eq_one`: `kubertLangPhase N s a m` is a
  `(2N)`-th root of unity when `N ∣ ∑ mᵢ aᵢ₁ aᵢ₂`.
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow` and
  `TauCeti.ModularForm.laurentQExpansion_prod_siegelFunction_div_zpow`: meromorphicity and exact
  `q_N`-expansion of a Kubert–Lang product.
* `TauCeti.ModularForm.laurentQExpansion_prod_siegelFunction_div_zpow_coeff_mem_iff`: all
  `q_N`-coefficients lie in a subfield `K ⊆ ℂ` containing `e^{2π i / N}` iff `kubertLangPhase ∈ K`.

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

/-- The `q_N`-order at infinity of the Kubert–Lang product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}`. When the
Kubert–Lang divisibility hypotheses hold, the numerator below is divisible by `12 * N`. -/
noncomputable def kubertLangCuspOrder (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) : ℤ :=
  (∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2)) / (12 * N)

/-- The constant phase of the Kubert–Lang product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` at infinity. Under the
Kubert–Lang cross-term divisibility `N ∣ ∑ mᵢ aᵢ₁ aᵢ₂`, this is a `(2N)`-th root of unity. -/
noncomputable def kubertLangPhase (N : ℕ) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ) : ℂ :=
  ∏ i ∈ s,
    ((-1 : ℂ) ^ ((a i 0 / (N : ℤ)) * (a i 1 / (N : ℤ)) +
        a i 0 / (N : ℤ) + a i 1 / (N : ℤ) + 1) *
      cexp (-(π * I * ((a i 0 / (N : ℤ) : ℤ) * ((a i 1 % (N : ℤ) : ℤ) : ℂ) -
        (a i 1 / (N : ℤ) : ℤ) * ((a i 0 % (N : ℤ) : ℤ) : ℂ)) / N)) *
      cexp (π * I * ((a i 1 % (N : ℤ) : ℤ) : ℂ) *
        (((a i 0 % (N : ℤ) : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) ^ m i

/-- Under the Kubert–Lang congruence hypotheses, `12 * N` divides the sum of reduced `B₂`
numerators, so `kubertLangCuspOrder N s a m` is exact (with zero remainder). -/
theorem twelve_mul_dvd_kubertLang_sum {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    (12 * N : ℤ) ∣
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) := by
  set r : ι → ℤ := fun i ↦ a i 0 % (N : ℤ)
  set q : ι → ℤ := fun i ↦ a i 0 / (N : ℤ)
  have hr_diff : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣
      ∑ i ∈ s, m i * (a i 0 ^ 2 - r i ^ 2) := by
    refine Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right ?_ _
    have ha : a i 0 = q i * N + r i := (Int.ediv_mul_add_emod (a i 0) N).symm
    have hsq : a i 0 ^ 2 - r i ^ 2 = q i ^ 2 * N ^ 2 + 2 * q i * N * r i := by rw [ha]; ring
    rw [hsq]
    refine dvd_add ?_ ?_
    · rcases Nat.even_or_odd N with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hg : Nat.gcd 2 (k + k) = 2 := by
          refine Nat.gcd_eq_left ?_
          exact ⟨k, by ring⟩
        rw [hg]
        refine ⟨q i ^ 2 * k, ?_⟩
        push_cast
        ring
      · have hg : Nat.gcd 2 (2 * k + 1) = 1 := by
          have : Nat.Coprime 2 (2 * k + 1) := by
            rw [Nat.coprime_two_left]
            exact ⟨k, rfl⟩
          exact this
        rw [hg, one_mul]
        exact ⟨q i ^ 2 * (2 * k + 1), by push_cast; ring⟩
    · refine dvd_trans (Nat.cast_dvd_cast (Nat.gcd_dvd_left 2 N |> fun _ ↦
        Nat.mul_dvd_mul_right (Nat.gcd_dvd_left 2 N) N)) ?_
      exact ⟨q i * r i, by push_cast; ring⟩
  have hr_sq : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 := by
    have hsub : (∑ i ∈ s, m i * r i ^ 2) =
        (∑ i ∈ s, m i * a i 0 ^ 2) - ∑ i ∈ s, m i * (a i 0 ^ 2 - r i ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hsub]
    exact dvd_sub h₀ hr_diff
  have hN_sq : (N : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 :=
    dvd_trans ⟨(Nat.gcd 2 N : ℤ), by push_cast; ring⟩ hr_sq
  set S : ℤ := ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2)
  have hS_eq : S = 6 * (∑ i ∈ s, m i * r i ^ 2) +
      (N : ℤ) * ((N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i) := by
    have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) =
        ∑ i ∈ s, (6 * (m i * r i ^ 2) + ((N : ℤ) ^ 2 * m i - 6 * N * (m i * r i))) :=
      Finset.sum_congr rfl fun i _ ↦ by ring
    rw [show S = ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * N * r i + N ^ 2) from rfl, hsum1,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  have hN_S : (N : ℤ) ∣ S := by
    rw [hS_eq]
    exact dvd_add (dvd_mul_of_dvd_right hN_sq 6) (dvd_mul_right _ _)
  obtain ⟨T, hT⟩ := hN_S
  have hN_ne : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have h3N : (3 * N : ℤ) ∣ S := by
    rw [hS_eq]
    refine dvd_add ⟨2 * ((∑ i ∈ s, m i * r i ^ 2) / N), ?_⟩ ?_
    · have := Int.mul_ediv_cancel' hN_sq
      linear_combination -6 * this
    · have h3_sum : (3 : ℤ) ∣ (N : ℤ) * ∑ i ∈ s, m i - 6 * ∑ i ∈ s, m i * r i := by
        refine dvd_sub ?_ ⟨2 * ∑ i ∈ s, m i * r i, by ring⟩
        by_cases h3N' : (3 : ℕ) ∣ N
        · exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h3N') _
        · have hcop : IsCoprime (3 : ℤ) (Nat.gcd 12 N : ℤ) := by
            refine Nat.Coprime.isCoprime ?_
            exact Nat.prime_three.coprime_iff_not_dvd.mpr
              (fun h ↦ h3N' (dvd_trans h (Nat.gcd_dvd_right 12 N)))
          have h3_12 : (3 : ℤ) ∣ (Nat.gcd 12 N : ℤ) * ∑ i ∈ s, m i :=
            dvd_trans ⟨4, by norm_num⟩ h₁₂
          exact dvd_mul_of_dvd_right (hcop.dvd_of_dvd_mul_left h3_12) _
      obtain ⟨k, hk⟩ := h3_sum
      exact ⟨k, by rw [hk]; ring⟩
  have h3T : (3 : ℤ) ∣ T := by
    obtain ⟨k, hk⟩ := h3N
    refine ⟨k, ?_⟩
    exact mul_left_cancel₀ hN_ne (by linear_combination -hT + hk)
  have h4N : (4 * N : ℤ) ∣ S := by
    rcases Nat.even_or_odd N with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hg : Nat.gcd 2 (k + k) = 2 := Nat.gcd_eq_left ⟨k, by ring⟩
      have h2N_sq : (2 * ((k + k : ℕ) : ℤ)) ∣ ∑ i ∈ s, m i * r i ^ 2 := by
        simpa [hg, Nat.cast_mul, mul_assoc] using hr_sq
      have h2_sq : (2 : ℤ) ∣ ∑ i ∈ s, m i * r i ^ 2 :=
        dvd_trans ⟨((k + k : ℕ) : ℤ), by ring⟩ h2N_sq
      have h2_lin : (2 : ℤ) ∣ ∑ i ∈ s, m i * r i := by
        have hdiff : (2 : ℤ) ∣ ∑ i ∈ s, m i * (r i ^ 2 - r i) :=
          Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right (by
            rcases Int.even_or_odd (r i) with ⟨u, hu⟩ | ⟨u, hu⟩
            · exact ⟨2 * u ^ 2 - u, by rw [hu]; ring⟩
            · exact ⟨2 * u ^ 2 + u, by rw [hu]; ring⟩) _
        have heq : (∑ i ∈ s, m i * r i) =
            (∑ i ∈ s, m i * r i ^ 2) - ∑ i ∈ s, m i * (r i ^ 2 - r i) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ by ring
        rw [heq]
        exact dvd_sub h2_sq hdiff
      have h4_mul : (4 : ℤ) ∣ ((k + k : ℕ) : ℤ) * ∑ i ∈ s, m i := by
        by_cases h4k : 4 ∣ k + k
        · exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h4k) _
        · have h2sum : (2 : ℤ) ∣ ∑ i ∈ s, m i := by
            have hdvd : Nat.gcd 12 (k + k) ∣ 6 := by
              have h12 : Nat.gcd 12 (k + k) ∣ 12 := Nat.gcd_dvd_left 12 (k + k)
              have hle : Nat.gcd 12 (k + k) ≤ 12 := Nat.le_of_dvd (by norm_num) h12
              have hndvd : ¬ 4 ∣ Nat.gcd 12 (k + k) := fun h ↦
                h4k (dvd_trans h (Nat.gcd_dvd_right 12 (k + k)))
              generalize Nat.gcd 12 (k + k) = d at h12 hle hndvd
              interval_cases d <;> omega
            obtain ⟨u, hu⟩ := hdvd
            have h12' : (2 * (u : ℤ)) * (Nat.gcd 12 (k + k) : ℤ) ∣
                (Nat.gcd 12 (k + k) : ℤ) * ∑ i ∈ s, m i := by
              have hu' : (12 : ℤ) = 2 * u * (Nat.gcd 12 (k + k) : ℤ) := by
                exact_mod_cast (by linarith : 12 = 2 * u * Nat.gcd 12 (k + k))
              rw [← hu']
              exact h₁₂
            have hgpos : (Nat.gcd 12 (k + k) : ℤ) ≠ 0 := by positivity
            have h2g : (2 : ℤ) * (Nat.gcd 12 (k + k) : ℤ) ∣
                (Nat.gcd 12 (k + k) : ℤ) * ∑ i ∈ s, m i := by
              obtain ⟨v, hv⟩ := h12'
              exact ⟨u * v, by rw [hv]; ring⟩
            exact (Int.mul_dvd_mul_iff_left hgpos).mp (by simpa [mul_comm] using h2g)
          obtain ⟨u, hu⟩ := h2sum
          exact ⟨(k : ℤ) * u, by push_cast; rw [hu]; ring⟩
      rw [hS_eq]
      refine dvd_add (dvd_trans ⟨3, by ring⟩ (mul_dvd_mul_left 6 h2N_sq)) ?_
      rw [mul_comm 4 _]
      refine mul_dvd_mul_left _ (dvd_sub h4_mul ?_)
      obtain ⟨u, hu⟩ := h2_lin
      exact ⟨3 * u, by rw [hu]; ring⟩
    · have hS_even : S = (∑ i ∈ s, m i * (6 * r i * (r i - ((2 * k + 1 : ℕ) : ℤ)))) +
          (((2 * k + 1 : ℕ) : ℤ) ^ 2) * ∑ i ∈ s, m i := by
        have hsum1 : ∑ i ∈ s, m i * (6 * r i ^ 2 - 6 * ((2 * k + 1 : ℕ) : ℤ) * r i +
            ((2 * k + 1 : ℕ) : ℤ) ^ 2) =
            ∑ i ∈ s, (m i * (6 * r i * (r i - ((2 * k + 1 : ℕ) : ℤ))) +
              ((2 * k + 1 : ℕ) : ℤ) ^ 2 * m i) :=
          Finset.sum_congr rfl fun i _ ↦ by ring
        dsimp only [S]
        rw [hsum1, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h4_S : (4 : ℤ) ∣ S := by
        rw [hS_even]
        refine dvd_add ?_ ?_
        · refine Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right ?_ _
          rcases Int.even_or_odd (r i) with ⟨u, hu⟩ | ⟨u, hu⟩
          · exact ⟨3 * u * (u + u - ((2 * k + 1 : ℕ) : ℤ)), by rw [hu]; ring⟩
          · exact ⟨3 * (2 * u + 1) * (u - k), by rw [hu]; push_cast; ring⟩
        · have hcop : IsCoprime (4 : ℤ) (Nat.gcd 12 (2 * k + 1) : ℤ) := by
            refine Nat.Coprime.isCoprime ?_
            have hodd : Nat.Coprime 4 (2 * k + 1) := by
              simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr ⟨k, rfl⟩)
            exact hodd.coprime_dvd_right (Nat.gcd_dvd_right 12 (2 * k + 1))
          have h4_12 : (4 : ℤ) ∣ (Nat.gcd 12 (2 * k + 1) : ℤ) * ∑ i ∈ s, m i :=
            dvd_trans ⟨3, by norm_num⟩ h₁₂
          exact dvd_mul_of_dvd_right (hcop.dvd_of_dvd_mul_left h4_12) _
      have hcop : IsCoprime (4 : ℤ) ((2 * k + 1 : ℕ) : ℤ) := by
        refine Nat.Coprime.isCoprime ?_
        simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr ⟨k, rfl⟩)
      rw [hT] at h4_S
      rw [hT, mul_comm 4 _]
      exact mul_dvd_mul_left _ (hcop.dvd_of_dvd_mul_left h4_S)
  have h4T : (4 : ℤ) ∣ T := by
    obtain ⟨k, hk⟩ := h4N
    refine ⟨k, ?_⟩
    exact mul_left_cancel₀ hN_ne (by linear_combination -hT + hk)
  obtain ⟨a3, ha3⟩ := h3T
  obtain ⟨b4, hb4⟩ := h4T
  refine ⟨a3 - b4, ?_⟩
  rw [hT]
  linear_combination (N : ℤ) * (4 * ha3 - 3 * hb4)

/-- Under the Kubert–Lang cross-term divisibility `N ∣ ∑ mᵢ aᵢ₁ aᵢ₂`, `kubertLangPhase N s a m`
is a `(2N)`-th root of unity. -/
theorem kubertLangPhase_pow_two_mul_eq_one {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) :
    kubertLangPhase N s a m ^ (2 * N) = 1 := by
  set r : ι → Fin 2 → ℤ := fun i j ↦ a i j % (N : ℤ)
  set q : ι → Fin 2 → ℤ := fun i j ↦ a i j / (N : ℤ)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  dsimp only [kubertLangPhase]
  rw [← Finset.prod_pow]
  have hsplit : ∏ i ∈ s, (((-1 : ℂ) ^ (q i 0 * q i 1 + q i 0 + q i 1 + 1) *
      cexp (-(π * I * ((q i 0 : ℂ) * (r i 1 : ℂ) - (q i 1 : ℂ) * (r i 0 : ℂ)) / N)) *
      cexp (π * I * (r i 1 : ℂ) * ((r i 0 : ℂ) - N) / (N : ℂ) ^ 2)) ^ m i) ^ (2 * N) =
      ∏ i ∈ s, cexp ((2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_zpow, mul_zpow]
    have hs1 :
        ((-1 : ℂ) ^ (q i 0 * q i 1 + q i 0 + q i 1 + 1)) ^ (m i * ((2 * N : ℕ) : ℤ)) = 1 := by
      rw [← _root_.zpow_mul]
      refine Even.neg_one_zpow ⟨(q i 0 * q i 1 + q i 0 + q i 1 + 1) * (m i * N), ?_⟩
      push_cast
      ring
    have hs2 : cexp (-(π * I * ((q i 0 : ℂ) * (r i 1 : ℂ) -
        (q i 1 : ℂ) * (r i 0 : ℂ)) / N)) ^ (m i * ((2 * N : ℕ) : ℤ)) = 1 := by
      rw [← Complex.exp_int_mul]
      have heq : ((m i * ((2 * N : ℕ) : ℤ) : ℤ) : ℂ) *
          (-(π * I * ((q i 0 : ℂ) * (r i 1 : ℂ) - (q i 1 : ℂ) * (r i 0 : ℂ)) / N)) =
          ((m i * (q i 1 * r i 0 - q i 0 * r i 1) : ℤ) : ℂ) * (2 * π * I) := by
        push_cast
        field_simp
        ring
      rw [heq, Complex.exp_int_mul_two_pi_mul_I]
    have hs3 : cexp (π * I * (r i 1 : ℂ) * ((r i 0 : ℂ) - N) / (N : ℂ) ^ 2) ^
        (m i * ((2 * N : ℕ) : ℤ)) =
        cexp ((2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) := by
      rw [← Complex.exp_int_mul]
      congr 1
      push_cast
      field_simp
    rw [hs1, hs2, hs3, one_mul, one_mul]
  rw [hsplit, ← Complex.exp_sum]
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
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum]
    exact dvd_add hdiff h₀₁
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (∑ i ∈ s, (2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) =
      (k : ℂ) * (2 * π * I) := by
    have hsum : (∑ i ∈ s, (2 * π * I / N) * (m i : ℂ) * (r i 1 : ℂ) * ((r i 0 : ℂ) - N)) =
        (2 * π * I / N) * ((∑ i ∈ s, m i * r i 1 * (r i 0 - N) : ℤ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum, hk]
    push_cast
    field_simp
  rw [hk', Complex.exp_int_mul_two_pi_mul_I]

/-- Exact factorization of a Kubert–Lang product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` into its constant
phase, `𝕢 N τ ^ kubertLangCuspOrder N s a m`, and the product of powers of `siegelThetaDisc`. -/
theorem prod_siegelFunction_div_zpow_eq {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (τ : ℍ) :
    ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i =
      kubertLangPhase N s a m *
        𝕢 N τ ^ kubertLangCuspOrder N s a m *
        ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i := by
  have h12 : (12 * N : ℤ) * kubertLangCuspOrder N s a m =
      ∑ i ∈ s, m i * (6 * (a i 0 % (N : ℤ)) ^ 2 - 6 * N * (a i 0 % (N : ℤ)) + N ^ 2) :=
    Int.mul_ediv_cancel' (twelve_mul_dvd_kubertLang_sum s a m h₀ h₁₂)
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

/-- The cusp function of a Kubert–Lang product at period `N` is meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) 0 := by
  have hfun : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) =
      fun τ : ℍ ↦ (kubertLangPhase N s a m * 𝕢 N τ ^ kubertLangCuspOrder N s a m) *
        ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i := by
    funext τ
    exact prod_siegelFunction_div_zpow_eq s a m h₀ h₁₂ τ
  rw [hfun]
  refine UpperHalfPlane.meromorphicAt_cuspFunction_mul ?_ ?_
  · exact UpperHalfPlane.meromorphicAt_cuspFunction_mul
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (laurentQExpansion_qParam_zpow _).1
  · classical
    clear h₀ h₁₂ hfun
    induction s using Finset.induction with
    | empty =>
      simp only [Finset.prod_empty]
      exact (UpperHalfPlane.meromorphicAt_cuspFunction_const 1)
    | insert i s hi ih =>
      have hm_i : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
          siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) 0 := by
        have hm := (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i)).meromorphicAt
        rcases Int.eq_nat_or_neg (m i) with ⟨k, hk | hk⟩
        · simp_rw [hk, zpow_natCast]
          exact UpperHalfPlane.meromorphicAt_cuspFunction_pow hm k
        · simp_rw [hk, zpow_neg, zpow_natCast]
          exact UpperHalfPlane.meromorphicAt_cuspFunction_inv
            (UpperHalfPlane.meromorphicAt_cuspFunction_pow hm k)
      simp_rw [Finset.prod_insert hi]
      exact UpperHalfPlane.meromorphicAt_cuspFunction_mul hm_i ih

/-- Exact `q_N`-Laurent expansion of a Kubert–Lang product `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}`. -/
theorem laurentQExpansion_prod_siegelFunction_div_zpow {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) =
      HahnSeries.single (kubertLangCuspOrder N s a m) (kubertLangPhase N s a m) *
        ∏ i ∈ s,
          (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i := by
  classical
  have hfun : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i) =
      fun τ : ℍ ↦ (kubertLangPhase N s a m * 𝕢 N τ ^ kubertLangCuspOrder N s a m) *
        ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i := by
    funext τ
    exact prod_siegelFunction_div_zpow_eq s a m h₀ h₁₂ τ
  have hm_pre : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      kubertLangPhase N s a m * 𝕢 N τ ^ kubertLangCuspOrder N s a m) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_mul
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (laurentQExpansion_qParam_zpow _).1
  have hm_i (i : ι) : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) 0 := by
    have hm := (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i)).meromorphicAt
    rcases Int.eq_nat_or_neg (m i) with ⟨k, hk | hk⟩
    · simp_rw [hk, zpow_natCast]
      exact UpperHalfPlane.meromorphicAt_cuspFunction_pow hm k
    · simp_rw [hk, zpow_neg, zpow_natCast]
      exact UpperHalfPlane.meromorphicAt_cuspFunction_inv
        (UpperHalfPlane.meromorphicAt_cuspFunction_pow hm k)
  have hm_prod (t : Finset ι) : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ t, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) 0 := by
    induction t using Finset.induction with
    | empty =>
      simp only [Finset.prod_empty]
      exact UpperHalfPlane.meromorphicAt_cuspFunction_const 1
    | insert i t hi ih =>
      simp_rw [Finset.prod_insert hi]
      exact UpperHalfPlane.meromorphicAt_cuspFunction_mul (hm_i i) ih
  have hL_prod : UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) =
      ∏ i ∈ s,
        (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i := by
    clear h₀ h₁₂ hfun hm_pre
    induction s using Finset.induction with
    | empty => simp
    | insert i s hi ih =>
      simp_rw [Finset.prod_insert hi]
      change UpperHalfPlane.laurentQExpansion N
          ((fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) *
            fun τ : ℍ ↦ ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) = _
      rw [UpperHalfPlane.laurentQExpansion_mul (hm_i i) (hm_prod s), ih]
      congr 1
      have hm := (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i)).meromorphicAt
      rcases Int.eq_nat_or_neg (m i) with ⟨k, hk | hk⟩
      · have hfun_i : (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) =
            (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ^ k := by
          funext τ
          rw [hk, zpow_natCast]
          rfl
        rw [hfun_i, hk, zpow_natCast, UpperHalfPlane.laurentQExpansion_pow hm,
          UpperHalfPlane.laurentQExpansion_of_analyticAt
            (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i))]
      · have hfun_i : (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) =
            ((fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) ^ k)⁻¹ := by
          funext τ
          rw [hk, zpow_neg, zpow_natCast]
          rfl
        rw [hfun_i, hk, zpow_neg, zpow_natCast,
          UpperHalfPlane.laurentQExpansion_inv
            (UpperHalfPlane.meromorphicAt_cuspFunction_pow hm k),
          UpperHalfPlane.laurentQExpansion_pow hm,
          UpperHalfPlane.laurentQExpansion_of_analyticAt
            (analyticAt_cuspFunction_siegelThetaDisc (N := N) (a i))]
  rw [hfun]
  change UpperHalfPlane.laurentQExpansion N
      ((fun τ : ℍ ↦ kubertLangPhase N s a m * 𝕢 N τ ^ kubertLangCuspOrder N s a m) *
        fun τ : ℍ ↦ ∏ i ∈ s, siegelThetaDisc N (a i) (𝕢 N τ) ^ m i) = _
  rw [UpperHalfPlane.laurentQExpansion_mul hm_pre (hm_prod s)]
  change UpperHalfPlane.laurentQExpansion N
      ((fun _ : ℍ ↦ kubertLangPhase N s a m) *
        fun τ : ℍ ↦ 𝕢 N τ ^ kubertLangCuspOrder N s a m) * _ = _
  rw [UpperHalfPlane.laurentQExpansion_mul (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (laurentQExpansion_qParam_zpow _).1,
    UpperHalfPlane.laurentQExpansion_const, (laurentQExpansion_qParam_zpow _).2, hL_prod]
  congr 1
  change HahnSeries.single 0 (kubertLangPhase N s a m) *
      HahnSeries.single (kubertLangCuspOrder N s a m) 1 =
    HahnSeries.single (kubertLangCuspOrder N s a m) (kubertLangPhase N s a m)
  rw [HahnSeries.single_mul_single, zero_add, mul_one]

/-- If `K` is a subfield of `ℂ` containing `e^{2π i / N}` and `kubertLangPhase N s a m ∈ K`,
then every `q_N`-Laurent coefficient of `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` lies in `K`. Conversely, if all
`q_N`-coefficients lie in `K` (and `aᵢ / N ∉ ℤ²`), then `kubertLangPhase N s a m ∈ K`. -/
theorem laurentQExpansion_prod_siegelFunction_div_zpow_coeff_mem_iff (K : Subfield ℂ)
    (hζ : cexp (2 * π * I / N) ∈ K) {ι : Type*} (s : Finset ι)
    (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) :
    (∀ n : ℤ, (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i).coeff n ∈ K) ↔
      kubertLangPhase N s a m ∈ K := by
  have hθ_mem (i : ι) (hi : i ∈ s) :
      ∃ Q : PowerSeries K, (PowerSeries.map K.subtype Q : LaurentSeries ℂ) =
        (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ∧
        IsUnit Q := by
    let Q : PowerSeries K :=
      PowerSeries.mk fun k ↦ ⟨(qExpansion N fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)).coeff k,
        qExpansion_siegelThetaDisc_coeff_mem (a i) K.toSubring hζ k⟩
    refine ⟨Q, ?_, ?_⟩
    · congr 1
      ext k
      simp [Q]
    · rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
      intro h0
      have h0' : ((PowerSeries.constantCoeff Q : K) : ℂ) = 0 := congrArg Subtype.val h0
      simp only [Q, PowerSeries.constantCoeff_mk] at h0'
      rw [_root_.UpperHalfPlane.qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
          one_mul, iteratedDeriv_zero,
          (cuspFunction_siegelThetaDisc_eventuallyEq (N := N) (a i)).eq_of_nhds] at h0'
      exact siegelThetaDisc_zero_ne_zero (N := N) (a i) (ha i hi) h0'
  choose Q hQ_eq hQ_unit using hθ_mem
  let φ : PowerSeries K →* LaurentSeries ℂ :=
    { toFun := fun P ↦ (PowerSeries.map K.subtype P : LaurentSeries ℂ)
      map_one' := by simp
      map_mul' := fun P R ↦ by simp [map_mul] }
  let u : (PowerSeries K)ˣ := ∏ i ∈ s.attach, (hQ_unit i.1 i.2).unit ^ m i.1
  have hu_eq : φ (u : PowerSeries K) =
      ∏ i ∈ s,
        (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i := by
    change ((Units.map φ u : (LaurentSeries ℂ)ˣ) : LaurentSeries ℂ) = _
    simp only [u, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
      IsUnit.unit_spec]
    rw [← Finset.prod_attach s fun i ↦
      (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N (a i) (𝕢 N τ)) : LaurentSeries ℂ) ^ m i]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    congr 1
    exact hQ_eq i.1 i.2
  have hu_coeff (k : ℤ) : (φ (u : PowerSeries K)).coeff k ∈ K := by
    rcases lt_or_ge k 0 with hlt | hge
    · have h0 : (φ (u : PowerSeries K)).coeff k = 0 := by
        change (HahnSeries.ofPowerSeries ℤ ℂ
          (PowerSeries.map K.subtype (u : PowerSeries K))).coeff k = 0
        rw [HahnSeries.ofPowerSeries_apply]
        exact HahnSeries.embDomain_of_notMem_range fun ⟨m, hm⟩ ↦ by
          simp only [Nat.castOrderEmbedding_apply] at hm
          omega
      rw [h0]
      exact K.zero_mem
    · lift k to ℕ using hge with k
      simp [φ, HahnSeries.ofPowerSeries_apply_coeff]
  have hu0 : (φ (u : PowerSeries K)).coeff 0 ≠ 0 := by
    have hunit : IsUnit (PowerSeries.constantCoeff (u : PowerSeries K)) :=
      PowerSeries.isUnit_iff_constantCoeff.mp u.isUnit
    have h0 : ((φ (u : PowerSeries K)).coeff 0) =
        ((PowerSeries.constantCoeff (u : PowerSeries K) : K) : ℂ) := by
      change (HahnSeries.ofPowerSeries ℤ ℂ
          (PowerSeries.map K.subtype (u : PowerSeries K))).coeff ((0 : ℕ) : ℤ) = _
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff]
      rfl
    rw [h0]
    exact Subtype.coe_ne_coe.mpr hunit.ne_zero
  rw [laurentQExpansion_prod_siegelFunction_div_zpow s a m h₀ h₁₂, ← hu_eq]
  constructor
  · intro h
    have h0 := h (kubertLangCuspOrder N s a m)
    rw [HahnSeries.coeff_single_mul, sub_self] at h0
    have h0' : kubertLangPhase N s a m * (φ (u : PowerSeries K)).coeff 0 ∈ K := h0
    have hdiv : (kubertLangPhase N s a m * (φ (u : PowerSeries K)).coeff 0) /
        (φ (u : PowerSeries K)).coeff 0 ∈ K := K.div_mem h0' (hu_coeff 0)
    rwa [mul_div_cancel_right₀ _ hu0] at hdiv
  · intro hphase n
    rw [HahnSeries.coeff_single_mul]
    exact K.mul_mem hphase (hu_coeff _)

end KubertLang

end TauCeti.ModularForm
