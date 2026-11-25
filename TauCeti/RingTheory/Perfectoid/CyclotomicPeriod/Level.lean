/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.CyclotomicPeriod.Basic

import TauCeti.RingTheory.WittVector.Frobenius

/-!
# Finite Frobenius products of the cyclotomic period

Let `S` be a perfect ring of characteristic `p`, `ε ∈ S`, and let `φ` be the Witt vector
Frobenius of `W(S)`. From the cyclotomic periods `μ = [ε] - 1` and `ξ = ∑ j < p, [ε^(1/p)]^j`
we form the finite Fontaine kernel generators

* `ξ_r = ∏_{j < r} φ^(-j)(ξ)` (`TauCeti.Perfectoid.xiLevel`), and
* `ξ̃_r = ∏_{j < r} φ^(j + 1)(ξ)` (`TauCeti.Perfectoid.xiTildeLevel`).

They satisfy `ξ_(r+1) = ξ_r * φ^(-r)(ξ)`, `ξ̃_(r+1) = ξ̃_r * φ^(r+1)(ξ)` and `φ^r(ξ_r) = ξ̃_r`.
Iterating the factorization `μ = ξ * φ^(-1)(μ)` gives `μ = ξ_r * φ^(-r)(μ)` and
`φ^r(μ) = ξ̃_r * μ`, so that `μ` lies in every ideal `(ξ_r)`, and `ξ` divides `φ^j(ξ_r)` for
`j < r`. Frobenius acts on `μ` and `ξ̃` by replacing `ε` with `ε ^ p`.

## Main definitions

* `TauCeti.Perfectoid.xiLevel`: the finite Fontaine kernel generator `ξ_r`.
* `TauCeti.Perfectoid.xiTildeLevel`: its Frobenius twist `ξ̃_r = φ^r(ξ_r)`.

## Main results

* `TauCeti.Perfectoid.xiLevel_succ`, `TauCeti.Perfectoid.xiTildeLevel_succ`: the recursions.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_xiLevel`: `φ^r(ξ_r) = ξ̃_r`.
* `TauCeti.Perfectoid.mu_eq_xiLevel_mul`: `μ = ξ_r * φ^(-r)(μ)`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_mu_eq_xiTildeLevel_mul`: `φ^r(μ) = ξ̃_r * μ`.
* `TauCeti.Perfectoid.span_mu_le_span_xiLevel`: `(μ) ⊆ (ξ_r)`.
* `TauCeti.Perfectoid.xi_dvd_iterate_frobeniusEquiv_xiLevel`: `ξ ∣ φ^j(ξ_r)` for `j < r`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_mu`: `φ^j(μ(ε)) = μ(ε ^ p ^ j)`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_xiTilde`: `φ^j(ξ̃(ε)) = ξ̃(ε ^ p ^ j)`.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3,
  Lemmas 3.12, 3.13 and 3.23.
-/

public section

namespace TauCeti.Perfectoid

open _root_.WittVector

section Frobenius

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- Frobenius on `μ` replaces `ε` by `ε ^ p`. -/
theorem frobeniusEquiv_mu (ε : S) : frobeniusEquiv p S (mu p ε) = mu p (ε ^ p) := by
  rw [mu_eq, mu_eq, map_sub, map_one, WittVector.frobeniusEquiv_apply, frobenius_teichmuller,
    map_pow]

/-- Iterated Frobenius on `μ` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_mu (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (mu p ε) = mu p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, frobeniusEquiv_mu, ← pow_mul, ← pow_succ]

/-- Frobenius on `xiTilde` replaces `ε` by `ε ^ p`. -/
theorem frobeniusEquiv_xiTilde (ε : S) :
    frobeniusEquiv p S (xiTilde p ε) = xiTilde p (ε ^ p) := by
  simp only [xiTilde_eq_sum, map_sum, map_pow, WittVector.frobeniusEquiv_apply,
    frobenius_teichmuller]

/-- Iterated Frobenius on `xiTilde` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_xiTilde (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (xiTilde p ε) = xiTilde p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, frobeniusEquiv_xiTilde, ← pow_mul, ← pow_succ]

end Frobenius

section Level

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- The finite Fontaine kernel generator `ξ_r = ∏_{j < r} φ^(-j)(ξ)`. -/
noncomputable def xiLevel (ε : S) (r : ℕ) : WittVector p S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (xi p ε)

/-- The Frobenius twist `ξ̃_r = ∏_{j < r} φ^(j + 1)(ξ)` of the finite Fontaine kernel
generator. -/
noncomputable def xiTildeLevel (ε : S) (r : ℕ) : WittVector p S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j + 1]) (xi p ε)

/-- The defining product of `ξ_r`. -/
theorem xiLevel_eq (ε : S) (r : ℕ) :
    xiLevel p ε r = ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (xi p ε) := (rfl)

/-- The defining product of `ξ̃_r`. -/
theorem xiTildeLevel_eq (ε : S) (r : ℕ) :
    xiTildeLevel p ε r = ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j + 1]) (xi p ε) := (rfl)

@[simp]
theorem xiLevel_zero (ε : S) : xiLevel p ε 0 = 1 := by simp [xiLevel]

@[simp]
theorem xiTildeLevel_zero (ε : S) : xiTildeLevel p ε 0 = 1 := by simp [xiTildeLevel]

/-- The recursion `ξ_(r+1) = ξ_r * φ^(-r)(ξ)`. -/
theorem xiLevel_succ (ε : S) (r : ℕ) :
    xiLevel p ε (r + 1) = xiLevel p ε r * ((frobeniusEquiv p S).symm^[r]) (xi p ε) :=
  Finset.prod_range_succ _ r

/-- The recursion `ξ̃_(r+1) = ξ̃_r * φ^(r+1)(ξ)`. -/
theorem xiTildeLevel_succ (ε : S) (r : ℕ) :
    xiTildeLevel p ε (r + 1) = xiTildeLevel p ε r * ((frobeniusEquiv p S)^[r + 1]) (xi p ε) :=
  Finset.prod_range_succ _ r

/-- The first finite generator is `ξ`. -/
@[simp]
theorem xiLevel_one (ε : S) : xiLevel p ε 1 = xi p ε := by simp [xiLevel]

/-- The first twisted generator is `ξ̃ = φ(ξ)`. -/
@[simp]
theorem xiTildeLevel_one (ε : S) : xiTildeLevel p ε 1 = xiTilde p ε := by
  simp [xiTildeLevel, xiTilde_eq]

/-- The second finite generator is `ξ * φ^(-1)(ξ)`. -/
theorem xiLevel_two (ε : S) :
    xiLevel p ε 2 = xi p ε * (frobeniusEquiv p S).symm (xi p ε) := by
  rw [xiLevel_succ, xiLevel_one, Function.iterate_one]

/-- The second twisted generator is `ξ̃ * φ(ξ̃)`: it uses positive Frobenius powers. -/
theorem xiTildeLevel_two (ε : S) :
    xiTildeLevel p ε 2 = xiTilde p ε * frobeniusEquiv p S (xiTilde p ε) := by
  rw [xiTildeLevel_succ, xiTildeLevel_one, xiTilde_eq, Function.iterate_succ_apply',
    Function.iterate_one]

/-- `φ^(-j)(ξ)` divides `ξ_r` for every `j < r`. -/
theorem iterate_frobeniusEquiv_symm_xi_dvd_xiLevel (ε : S) {j r : ℕ} (hj : j < r) :
    ((frobeniusEquiv p S).symm^[j]) (xi p ε) ∣ xiLevel p ε r :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)

/-- `ξ` divides `φ^j(ξ_r)` for every `j < r`. -/
theorem xi_dvd_iterate_frobeniusEquiv_xiLevel (ε : S) {j r : ℕ} (hj : j < r) :
    xi p ε ∣ ((frobeniusEquiv p S)^[j]) (xiLevel p ε r) := by
  obtain ⟨c, hc⟩ := iterate_frobeniusEquiv_symm_xi_dvd_xiLevel p ε hj
  refine ⟨((frobeniusEquiv p S)^[j]) c, ?_⟩
  rw [hc, iterate_map_mul,
    Function.LeftInverse.iterate (frobeniusEquiv p S).apply_symm_apply j]

/-- The recursion `ξ̃_(r+1) = φ(ξ̃_r) * φ(ξ)`, peeling off the lowest Frobenius power. -/
theorem xiTildeLevel_succ' (ε : S) (r : ℕ) :
    xiTildeLevel p ε (r + 1) =
      frobeniusEquiv p S (xiTildeLevel p ε r) * frobeniusEquiv p S (xi p ε) := by
  rw [xiTildeLevel, Finset.prod_range_succ', xiTildeLevel, map_prod]
  simp only [Function.iterate_succ_apply', zero_add, Function.iterate_zero, id]

/-- Applying `φ^r` to `ξ_r` gives `ξ̃_r`. -/
theorem iterate_frobeniusEquiv_xiLevel (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (xiLevel p ε r) = xiTildeLevel p ε r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [xiLevel_succ, iterate_map_mul, Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih,
      Function.LeftInverse.iterate (frobeniusEquiv p S).apply_symm_apply r,
      xiTildeLevel_succ']

/-- Iterating `μ = ξ * φ^(-1)(μ)` gives `μ = ξ_r * φ^(-r)(μ)`. -/
theorem mu_eq_xiLevel_mul (ε : S) (r : ℕ) :
    mu p ε = xiLevel p ε r * ((frobeniusEquiv p S).symm^[r]) (mu p ε) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [xiLevel_succ, mul_assoc, Function.iterate_succ_apply, ← iterate_map_mul,
      ← mu_eq_xi_mul_frobeniusEquiv_symm]
    exact ih

/-- Applying `φ^r` to the factorization of `μ` gives `φ^r(μ) = ξ̃_r * μ`. -/
theorem iterate_frobeniusEquiv_mu_eq_xiTildeLevel_mul (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (mu p ε) = xiTildeLevel p ε r * mu p ε := by
  conv_lhs => rw [mu_eq_xiLevel_mul p ε r]
  rw [iterate_map_mul, iterate_frobeniusEquiv_xiLevel,
    Function.LeftInverse.iterate (frobeniusEquiv p S).apply_symm_apply r]

/-- The cyclotomic period `μ` lies in every ideal `(ξ_r)`. -/
theorem span_mu_le_span_xiLevel (ε : S) (r : ℕ) :
    Ideal.span {mu p ε} ≤ Ideal.span {xiLevel p ε r} :=
  Ideal.span_singleton_le_span_singleton.mpr ⟨_, mu_eq_xiLevel_mul p ε r⟩

end Level

end TauCeti.Perfectoid
