/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Period

import TauCeti.RingTheory.WittVector.Frobenius
import TauCeti.RingTheory.WittVector.Units

/-!
# Finite Frobenius products of the cyclotomic period

Let `S` be a perfect ring of characteristic `p`, `ε ∈ S`, and let `φ` be the Witt vector
Frobenius of `W(S)`. From the cyclotomic periods `μ = [ε] - 1` and `ξ = ∑ j < p, [ε^(1/p)]^j`
we form the finite Frobenius products

* `ξ_r = ∏_{j < r} φ^(-j)(ξ)` (`TauCeti.Perfectoid.xiLevel`), and
* `xiTilde_r = ∏_{j < r} φ^(j + 1)(ξ)` (`TauCeti.Perfectoid.xiTildeLevel`).

They satisfy `ξ_(r+1) = ξ_r * φ^(-r)(ξ)`, `xiTilde_(r+1) = xiTilde_r * φ^(r+1)(ξ)` and
`φ^r(ξ_r) = xiTilde_r`, and they are natural in ring homomorphisms between perfect rings.
Iterating the factorization `μ = ξ * φ^(-1)(μ)` gives `μ = ξ_r * φ^(-r)(μ)` and
`φ^r(μ) = xiTilde_r * μ`, so that `μ` lies in every ideal `(ξ_r)`, and `ξ` divides `φ^j(ξ_r)` for
`j < r`. Frobenius acts on `μ` and `xiTilde` by replacing `ε` with `ε ^ p`. The zeroth Witt
coordinate of `μ` is `ε - 1`, so for `ε ≠ 1` all of these elements are nonzero.

When `S = A♭` and the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, Fontaine's map
`θ` kills `φ^j(ξ_r)` for `j < r`; in the setting of Bhatt–Morrow–Scholze, `ξ_r` generates the
kernel of the finite specialization map `θ_r`.

## Main definitions

* `TauCeti.Perfectoid.xiLevel`: the finite Frobenius product `ξ_r`.
* `TauCeti.Perfectoid.xiTildeLevel`: its Frobenius twist `xiTilde_r = φ^r(ξ_r)`.

## Main results

* `TauCeti.Perfectoid.xiLevel_succ`, `TauCeti.Perfectoid.xiTildeLevel_succ`: the recursions.
* `TauCeti.Perfectoid.map_xiLevel`, `TauCeti.Perfectoid.map_xiTildeLevel`: base change.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_xiLevel`: `φ^r(ξ_r) = xiTilde_r`.
* `TauCeti.Perfectoid.mu_eq_xiLevel_mul`: `μ = ξ_r * φ^(-r)(μ)`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_mu_eq_xiTildeLevel_mul`: `φ^r(μ) = xiTilde_r * μ`.
* `TauCeti.Perfectoid.span_mu_le_span_xiLevel`: `(μ) ⊆ (ξ_r)`.
* `TauCeti.Perfectoid.xi_dvd_iterate_frobeniusEquiv_xiLevel`: `ξ ∣ φ^j(ξ_r)` for `j < r`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_mu`: `φ^j(μ(ε)) = μ(ε ^ p ^ j)`.
* `TauCeti.Perfectoid.iterate_frobeniusEquiv_xiTilde`: `φ^j(xiTilde(ε)) = xiTilde(ε ^ p ^ j)`.
* `TauCeti.Perfectoid.coeff_zero_mu`: the zeroth Witt coordinate of `μ` is `ε - 1`.
* `TauCeti.Perfectoid.mu_ne_zero`, `TauCeti.Perfectoid.xi_ne_zero`,
  `TauCeti.Perfectoid.xiLevel_ne_zero`, `TauCeti.Perfectoid.xiTilde_ne_zero`,
  `TauCeti.Perfectoid.xiTildeLevel_ne_zero`: for `ε ≠ 1` the periods are nonzero.
* `PreTilt.fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero`,
  `PreTilt.fontaineTheta_iterate_frobeniusEquiv_succ_xi`,
  `PreTilt.fontaineTheta_iterate_frobeniusEquiv_xiLevel_eq_zero`: values of `θ ∘ φ^j`.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3,
  Lemmas 3.12, 3.13 and 3.23.
-/
public section

namespace TauCeti.Perfectoid

open _root_.WittVector

section Frobenius

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- Iterated Frobenius on `μ` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_mu (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (mu p ε) = mu p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [mu_eq, map_sub, map_one, WittVector.frobeniusEquiv_apply, frobenius_teichmuller,
      ← map_pow, ← pow_mul, ← pow_succ]

/-- Iterated Frobenius on `xiTilde` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_xiTilde (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (xiTilde p ε) = xiTilde p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h (δ : S) : frobeniusEquiv p S (xiTilde p δ) = xiTilde p (δ ^ p) := by
      simp only [xiTilde_eq_sum, map_sum, map_pow, WittVector.frobeniusEquiv_apply,
        frobenius_teichmuller]
    rw [Function.iterate_succ_apply', ih, h, ← pow_mul, ← pow_succ]

end Frobenius

section Level

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- The finite Frobenius product `ξ_r = ∏_{j < r} φ^(-j)(ξ)`. -/
noncomputable def xiLevel (ε : S) (r : ℕ) : WittVector p S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (xi p ε)

/-- The Frobenius twist `xiTilde_r = ∏_{j < r} φ^(j + 1)(ξ)` of the finite Frobenius product
`ξ_r`. -/
noncomputable def xiTildeLevel (ε : S) (r : ℕ) : WittVector p S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j + 1]) (xi p ε)

/-- The defining product of `ξ_r`. -/
theorem xiLevel_eq (ε : S) (r : ℕ) :
    xiLevel p ε r = ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (xi p ε) := (rfl)

/-- The defining product of `xiTilde_r`. -/
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

/-- The recursion `xiTilde_(r+1) = xiTilde_r * φ^(r+1)(ξ)`. -/
theorem xiTildeLevel_succ (ε : S) (r : ℕ) :
    xiTildeLevel p ε (r + 1) = xiTildeLevel p ε r * ((frobeniusEquiv p S)^[r + 1]) (xi p ε) :=
  Finset.prod_range_succ _ r

/-- The first finite product is `ξ`. -/
@[simp]
theorem xiLevel_one (ε : S) : xiLevel p ε 1 = xi p ε := by simp [xiLevel]

/-- The first twisted product is `xiTilde = φ(ξ)`. -/
@[simp]
theorem xiTildeLevel_one (ε : S) : xiTildeLevel p ε 1 = xiTilde p ε := by
  simp [xiTildeLevel, xiTilde_eq]

/-- The second finite product is `ξ * φ^(-1)(ξ)`. -/
theorem xiLevel_two (ε : S) :
    xiLevel p ε 2 = xi p ε * (frobeniusEquiv p S).symm (xi p ε) := by
  rw [xiLevel_succ, xiLevel_one, Function.iterate_one]

/-- The second twisted product is `xiTilde * φ(xiTilde)`: it uses positive Frobenius powers. -/
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

/-- The recursion `xiTilde_(r+1) = φ(xiTilde_r) * φ(ξ)`, peeling off the lowest Frobenius power. -/
theorem xiTildeLevel_succ' (ε : S) (r : ℕ) :
    xiTildeLevel p ε (r + 1) =
      frobeniusEquiv p S (xiTildeLevel p ε r) * frobeniusEquiv p S (xi p ε) := by
  rw [xiTildeLevel, Finset.prod_range_succ', xiTildeLevel, map_prod]
  simp only [Function.iterate_succ_apply', zero_add, Function.iterate_zero, id]

/-- Applying `φ^r` to `ξ_r` gives `xiTilde_r`. -/
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

/-- Applying `φ^r` to the factorization of `μ` gives `φ^r(μ) = xiTilde_r * μ`. -/
theorem iterate_frobeniusEquiv_mu_eq_xiTildeLevel_mul (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (mu p ε) = xiTildeLevel p ε r * mu p ε := by
  conv_lhs => rw [mu_eq_xiLevel_mul p ε r]
  rw [iterate_map_mul, iterate_frobeniusEquiv_xiLevel,
    Function.LeftInverse.iterate (frobeniusEquiv p S).apply_symm_apply r]

/-- The cyclotomic period `μ` lies in every ideal `(ξ_r)`. -/
theorem span_mu_le_span_xiLevel (ε : S) (r : ℕ) :
    Ideal.span {mu p ε} ≤ Ideal.span {xiLevel p ε r} :=
  Ideal.span_singleton_le_span_singleton.mpr ⟨_, mu_eq_xiLevel_mul p ε r⟩

/-- `ξ` divides `ξ_r` for every `r ≥ 1`. -/
theorem xi_dvd_xiLevel (ε : S) {r : ℕ} (hr : 1 ≤ r) : xi p ε ∣ xiLevel p ε r := by
  rw [← xiLevel_one p ε]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hr)

/-- `xiTilde` divides `xiTilde_r` for every `r ≥ 1`. -/
theorem xiTilde_dvd_xiTildeLevel (ε : S) {r : ℕ} (hr : 1 ≤ r) :
    xiTilde p ε ∣ xiTildeLevel p ε r := by
  rw [← xiTildeLevel_one p ε]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hr)

end Level

section Naturality

variable (p : ℕ) [Fact p.Prime] {S T : Type*} [CommRing S] [CharP S p] [PerfectRing S p]
  [CommRing T] [CharP T p] [PerfectRing T p]

private theorem semiconj_map_frobeniusEquiv (f : S →+* T) :
    Function.Semiconj (WittVector.map f) (frobeniusEquiv p S) (frobeniusEquiv p T) := fun x ↦ by
  simp only [WittVector.frobeniusEquiv_apply, map_frobenius]

private theorem semiconj_map_frobeniusEquiv_symm (f : S →+* T) :
    Function.Semiconj (WittVector.map f) (frobeniusEquiv p S).symm (frobeniusEquiv p T).symm :=
  fun x ↦ (frobeniusEquiv p T).injective <| by
    rw [RingEquiv.apply_symm_apply, ← semiconj_map_frobeniusEquiv p f, RingEquiv.apply_symm_apply]

/-- Base change of `ξ` between perfect rings replaces `ε` by its image. -/
@[simp]
theorem map_xi (f : S →+* T) (ε : S) : WittVector.map f (xi p ε) = xi p (f ε) := by
  simp [xi_eq, map_sum, map_teichmuller, RingHom.map_frobeniusEquiv_symm]

/-- Base change of `ξ_r` between perfect rings replaces `ε` by its image. -/
@[simp]
theorem map_xiLevel (f : S →+* T) (ε : S) (r : ℕ) :
    WittVector.map f (xiLevel p ε r) = xiLevel p (f ε) r := by
  rw [xiLevel_eq, xiLevel_eq, map_prod]
  exact Finset.prod_congr rfl fun j _ ↦ by
    rw [((semiconj_map_frobeniusEquiv_symm p f).iterate_right j).eq, map_xi]

/-- Base change of `xiTilde_r` between perfect rings replaces `ε` by its image. -/
@[simp]
theorem map_xiTildeLevel (f : S →+* T) (ε : S) (r : ℕ) :
    WittVector.map f (xiTildeLevel p ε r) = xiTildeLevel p (f ε) r := by
  rw [xiTildeLevel_eq, xiTildeLevel_eq, map_prod]
  exact Finset.prod_congr rfl fun j _ ↦ by
    rw [((semiconj_map_frobeniusEquiv p f).iterate_right (j + 1)).eq, map_xi]

end Naturality

section Nonzero

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p] {ε : S}

omit [CharP S p] [PerfectRing S p] in
/-- The zeroth Witt coordinate of `μ = [ε] - 1` is `ε - 1`. -/
@[simp]
theorem coeff_zero_mu (ε : S) : (mu p ε).coeff 0 = ε - 1 := by
  simp [mu_eq, sub_coeff_zero]

omit [CharP S p] [PerfectRing S p] in
/-- For `ε ≠ 1`, the zeroth Witt coordinate of `μ` is nonzero. -/
theorem coeff_zero_mu_ne_zero (hε : ε ≠ 1) : (mu p ε).coeff 0 ≠ 0 := by
  rwa [coeff_zero_mu, sub_ne_zero]

/-- For `ε ≠ 1`, the zeroth Witt coordinate of every `ξ_r` is nonzero: it divides that of `μ`. -/
theorem coeff_zero_xiLevel_ne_zero (hε : ε ≠ 1) (r : ℕ) : (xiLevel p ε r).coeff 0 ≠ 0 :=
  fun h ↦ coeff_zero_mu_ne_zero p hε (by rw [mu_eq_xiLevel_mul p ε r, mul_coeff_zero, h, zero_mul])

/-- For `ε ≠ 1`, the zeroth Witt coordinate of `ξ` is nonzero. -/
theorem coeff_zero_xi_ne_zero (hε : ε ≠ 1) : (xi p ε).coeff 0 ≠ 0 := by
  simpa using coeff_zero_xiLevel_ne_zero p hε 1

omit [CharP S p] [PerfectRing S p] in
/-- For `ε ≠ 1`, `μ` is nonzero. -/
theorem mu_ne_zero (hε : ε ≠ 1) : mu p ε ≠ 0 :=
  fun h ↦ coeff_zero_mu_ne_zero p hε (by rw [h, zero_coeff])

/-- For `ε ≠ 1`, every finite product `ξ_r` is nonzero. -/
theorem xiLevel_ne_zero (hε : ε ≠ 1) (r : ℕ) : xiLevel p ε r ≠ 0 :=
  fun h ↦ coeff_zero_xiLevel_ne_zero p hε r (by rw [h, zero_coeff])

/-- For `ε ≠ 1`, `ξ` is nonzero. -/
theorem xi_ne_zero (hε : ε ≠ 1) : xi p ε ≠ 0 := by
  simpa using xiLevel_ne_zero p hε 1

/-- For `ε ≠ 1`, every twisted product `xiTilde_r` is nonzero: `φ^r(μ) = xiTilde_r * μ` and `φ` is
injective. -/
theorem xiTildeLevel_ne_zero (hε : ε ≠ 1) (r : ℕ) : xiTildeLevel p ε r ≠ 0 := by
  intro h
  have h0 := iterate_frobeniusEquiv_mu_eq_xiTildeLevel_mul p ε r
  rw [h, zero_mul, ← iterate_map_zero (frobeniusEquiv p S) r] at h0
  exact mu_ne_zero p hε ((frobeniusEquiv p S).injective.iterate r h0)

/-- For `ε ≠ 1`, `xiTilde` is nonzero. -/
theorem xiTilde_ne_zero (hε : ε ≠ 1) : xiTilde p ε ≠ 0 := by
  simpa using xiTildeLevel_ne_zero p hε 1

end Nonzero

end TauCeti.Perfectoid

namespace PreTilt

open TauCeti.Perfectoid _root_.WittVector

section FontaineValues

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- If `ε♯ = 1`, then Fontaine's map kills every Frobenius iterate of `μ`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero (ε : PreTilt A p) (hε : ε.untilt = 1)
    (j : ℕ) : fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) (mu p ε)) = 0 := by
  rw [iterate_frobeniusEquiv_mu]
  exact fontaineTheta_mu_eq_zero _ (by rw [map_pow, hε, one_pow])

/-- If `ε♯ = 1`, then Fontaine's map sends `φ^(j + 1)(ξ)` to `p`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_succ_xi (ε : PreTilt A p) (hε : ε.untilt = 1)
    (j : ℕ) :
    fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j + 1]) (xi p ε)) = p := by
  rw [Function.iterate_succ_apply, ← xiTilde_eq, iterate_frobeniusEquiv_xiTilde]
  exact fontaineTheta_xiTilde _ (by rw [map_pow, hε, one_pow])

/-- If Fontaine's map kills `ξ`, then it kills `φ^j(ξ_r)` for every `j < r`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_xiLevel_eq_zero (ε : PreTilt A p)
    (hξ : fontaineTheta A p (xi p ε) = 0) {j r : ℕ} (hj : j < r) :
    fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) (xiLevel p ε r)) = 0 := by
  obtain ⟨c, hc⟩ := xi_dvd_iterate_frobeniusEquiv_xiLevel p ε hj
  rw [hc, map_mul, hξ, zero_mul]

end FontaineValues

end PreTilt
