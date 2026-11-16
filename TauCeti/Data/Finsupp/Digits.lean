/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Digits.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Base-`B` positional weights of finite exponent vectors

For `m, B : ℕ`, the positional weight `w_B(d) = ∑ i : Fin m, d i * B ^ (i : ℕ)` evaluates an
exponent vector `d : Fin m →₀ ℕ` as the `m`-digit base-`B` expansion `(d 0, …, d (m - 1))`
(`Finsupp.weight_pow_eq_ofDigits`).

Restricting `d` to the box `{d : Fin m →₀ ℕ | ∀ i, d i < B}` makes `w_B` a bijection onto
`{n : ℕ | n < B ^ m}` for every `m` and `B`, including the degenerate bases `B = 0, 1`
(`Finsupp.bijOn_weight_pow`, `Finsupp.injOn_weight_pow`, `Finsupp.weight_pow_lt_pow`). When fed
into `MvPolynomial.coeff_aeval_X_pow_weight` and `MvPolynomial.injOn_aeval_X_pow`, the injectivity
`Finsupp.injOn_weight_pow` separates all monomials in `m` variables whose individual exponents lie
below `B` under the Kronecker substitution `Xᵢ ↦ T ^ (B ^ i)`.

## Main results

* `Finsupp.weight_pow_eq_ofDigits`: `weight (fun i : Fin m ↦ B ^ (i : ℕ)) d` equals
  `Nat.ofDigits B (List.ofFn d)`.
* `Finsupp.weight_pow_lt_pow`: if `d i < B` for every `i : Fin m`, then
  `weight (fun i : Fin m ↦ B ^ (i : ℕ)) d < B ^ m`.
* `Finsupp.injOn_weight_pow`: `weight (fun i : Fin m ↦ B ^ (i : ℕ))` is injective on
  `{d : Fin m →₀ ℕ | ∀ i, d i < B}` for every `m` and `B`.
* `Finsupp.bijOn_weight_pow`: `weight (fun i : Fin m ↦ B ^ (i : ℕ))` maps
  `{d : Fin m →₀ ℕ | ∀ i, d i < B}` bijectively onto `{n : ℕ | n < B ^ m}` for every `m` and `B`.
-/

public section

namespace Finsupp

/-- The positional weight `∑ i : Fin m, d i * B ^ i` of `d : Fin m →₀ ℕ` is the base-`B` value
`Nat.ofDigits B` of its tuple of entries `(d 0, …, d (m - 1))`. -/
theorem weight_pow_eq_ofDigits (m B : ℕ) (d : Fin m →₀ ℕ) :
    weight (fun i : Fin m ↦ B ^ (i : ℕ)) d = Nat.ofDigits B (List.ofFn (d : Fin m → ℕ)) := by
  simp [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn, weight_apply,
    Finsupp.sum_fintype]

/-- On zero variables, the positional weight vanishes. -/
@[simp]
theorem weight_pow_zero_vars (B : ℕ) (d : Fin 0 →₀ ℕ) :
    weight (fun i : Fin 0 ↦ B ^ (i : ℕ)) d = 0 := by
  simp [Subsingleton.elim d 0]

/-- On one variable, the positional weight of `d` is its single entry `d 0`, for every base `B`
including `B = 0`. -/
theorem weight_pow_one_var (B : ℕ) (d : Fin 1 →₀ ℕ) :
    weight (fun i : Fin 1 ↦ B ^ (i : ℕ)) d = d 0 := by
  simp [weight_apply, Finsupp.sum_fintype]

/-- On two variables, the positional weight of `d` is `d 0 + B * d 1`. -/
theorem weight_pow_two_vars (B : ℕ) (d : Fin 2 →₀ ℕ) :
    weight (fun i : Fin 2 ↦ B ^ (i : ℕ)) d = d 0 + B * d 1 := by
  simp [weight_pow_eq_ofDigits, List.ofFn_succ, Nat.ofDigits_cons]

/-- Every exponent vector `d : Fin m →₀ ℕ` with entries below `B` has base-`B` positional weight
strictly below `B ^ m`. No positivity assumption on `B` is needed: for `B = 0` and `m > 0` the
bound `∀ i, d i < 0` is vacuous, while for `m = 0` we have `0 < B ^ 0 = 1`. -/
theorem weight_pow_lt_pow {m B : ℕ} {d : Fin m →₀ ℕ} (hd : ∀ i, d i < B) :
    weight (fun i : Fin m ↦ B ^ (i : ℕ)) d < B ^ m := by
  rcases lt_trichotomy B 1 with hB0 | rfl | hB1
  · obtain rfl : B = 0 := by omega
    rcases m with _ | m
    · simp
    · exact (Nat.not_lt_zero _ (hd 0)).elim
  · have hd0 : d = 0 := Finsupp.ext fun i ↦ Nat.lt_one_iff.mp (hd i)
    simp [hd0]
  · rw [weight_pow_eq_ofDigits]
    simpa using Nat.ofDigits_lt_base_pow_length hB1 (l := List.ofFn (d : Fin m → ℕ))
      (by simpa using hd)

/-- **Uniqueness of bounded base-`B` weights.** The positional weight
`d ↦ ∑ i : Fin m, d i * B ^ i` is injective on the box `{d : Fin m →₀ ℕ | ∀ i, d i < B}` for every
`m` and `B`: by uniqueness of fixed-length base-`B` expansions when `B ≥ 2`, and because the box
has at most one element when `B ≤ 1`. -/
theorem injOn_weight_pow (m B : ℕ) :
    Set.InjOn (weight fun i : Fin m ↦ B ^ (i : ℕ)) {d : Fin m →₀ ℕ | ∀ i, d i < B} := by
  intro d₁ hd₁ d₂ hd₂ h
  simp only [Set.mem_ofPred_eq] at hd₁ hd₂
  rcases le_or_gt B 1 with hB | hB
  · ext i
    have := hd₁ i
    have := hd₂ i
    omega
  · rw [weight_pow_eq_ofDigits, weight_pow_eq_ofDigits] at h
    have hL : List.ofFn (d₁ : Fin m → ℕ) = List.ofFn (d₂ : Fin m → ℕ) :=
      Nat.injOn_ofDigits hB m
        ⟨List.length_ofFn, by simpa using hd₁⟩
        ⟨List.length_ofFn, by simpa using hd₂⟩ h
    exact DFunLike.coe_injective (List.ofFn_injective hL)

/-- The positional weight `d ↦ ∑ i : Fin m, d i * B ^ i` maps the box
`{d : Fin m →₀ ℕ | ∀ i, d i < B}` bijectively onto `{n : ℕ | n < B ^ m}` for every `m` and `B`. -/
theorem bijOn_weight_pow (m B : ℕ) :
    Set.BijOn (weight fun i : Fin m ↦ B ^ (i : ℕ))
      {d : Fin m →₀ ℕ | ∀ i, d i < B} {n : ℕ | n < B ^ m} := by
  refine ⟨fun d hd ↦ weight_pow_lt_pow hd, injOn_weight_pow m B, fun n hn ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hn
  rcases lt_trichotomy B 1 with hB0 | rfl | hB1
  · obtain rfl : B = 0 := by omega
    rcases m with _ | m
    · obtain rfl : n = 0 := by simpa using hn
      exact ⟨0, by simp, by simp⟩
    · simp [Nat.zero_pow (Nat.succ_pos m)] at hn
  · obtain rfl : n = 0 := by simpa using hn
    exact ⟨0, by simp, by simp⟩
  · obtain ⟨hlen, hlt⟩ := Nat.mapsTo_digitsAppend hB1 m hn
    let d : Fin m →₀ ℕ :=
      equivFunOnFinite.symm fun i : Fin m ↦ (Nat.digitsAppend B m n)[i.1]'(by omega)
    have hofFn : List.ofFn (d : Fin m → ℕ) = Nat.digitsAppend B m n := by
      refine List.ext_getElem (by simp [hlen]) fun i hi₁ hi₂ ↦ ?_
      simp [d]
    refine ⟨d, fun i ↦ ?_, ?_⟩
    · exact hlt _ (List.getElem_mem _)
    · rw [weight_pow_eq_ofDigits, hofFn]
      exact (Nat.setInvOn_digitsAppend_ofDigits hB1 m).2 hn

end Finsupp
