/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Cyclotomic.Level
public import TauCeti.RingTheory.WittVector.Regular.Basic

/-!
# Regularity of the cyclotomic period elements

Let `S` be a perfect ring of characteristic `p` and `ε ∈ S`. Whenever `ε - 1 ∈ S⁰`, the zeroth
Witt coordinates of `μ = [ε] - 1`, `ξ`, `ξ'`, `ξ_r`, and `ξ'_r` all lie in `S⁰`, so each of these
elements is a nonzerodivisor in `W(S)` with `p`-torsion-free quotient. When in addition `ε - 1`
is not a unit of `S`, `[p, x]` and `[x, p]` are regular sequences on `W(S)` for
`x ∈ {μ, ξ, ξ'}` and for `x ∈ {ξ_r, ξ'_r}` with `r ≥ 1`.

## Main results

* `TauCeti.WittVector.cyclotomicXi_coeff_zero_mem_nonZeroDivisors`,
  `TauCeti.WittVector.cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors`,
  `TauCeti.WittVector.cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors`: zeroth Witt
  coordinates lie in `S⁰` whenever `ε - 1 ∈ S⁰`.
* `TauCeti.WittVector.cyclotomicXi_coeff_zero_mem_jacobson`,
  `TauCeti.WittVector.cyclotomicXiLevel_coeff_zero_mem_jacobson`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_coeff_zero_mem_jacobson`: zeroth Witt coordinates
  lie in `Ring.jacobson S` when `ε - 1 ∈ Ring.jacobson S`.
* `mem_nonZeroDivisors` and `isSMulRegular_quotient_natCast` for `μ`, `ξ`, `ξ'`, `ξ_r`, `ξ'_r`.
* `isRegular_pair` (in both orders) for `μ`, `ξ`, `ξ'`, `ξ_r` (`1 ≤ r`), and `ξ'_r` (`1 ≤ r`)
  under `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Proposition 3.17 and
  Lemma 3.23.
-/

public section

open _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

namespace TauCeti.WittVector

variable (p : ℕ) [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

local notation "𝕎" => _root_.WittVector p

/-- If `ε - 1 ∈ S⁰`, then `ξ.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXi_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    (cyclotomicXi p ε).coeff 0 ∈ S⁰ :=
  (mul_mem_nonZeroDivisors.mp (by rwa [cyclotomicXi_coeff_zero_mul])).1

/-- If `ε - 1 ∈ S⁰`, then `ξ'.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    (cyclotomicXiTilde p ε).coeff 0 ∈ S⁰ := by
  rw [← frobenius_cyclotomicXi, coeff_frobenius_charP]
  exact pow_mem (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε) p

/-- If `ε - 1 ∈ S⁰`, then `ξ_r.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 ∈ S⁰ :=
  (mul_mem_nonZeroDivisors.mp (by rwa [cyclotomicXiLevel_coeff_zero_mul])).1

/-- If `ε - 1 ∈ S⁰`, then `ξ'_r.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 ∈ S⁰ := by
  rw [cyclotomicXiTildeLevel_coeff_zero]
  exact pow_mem (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r) (p ^ r)

/-- If `ε - 1 ∈ Ring.jacobson S`, then `ξ.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXi_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    (cyclotomicXi p ε).coeff 0 ∈ Ring.jacobson S := by
  let q := Ideal.Quotient.mk (Ring.jacobson S)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_coeff, map_mk_jacobson_cyclotomicXi_eq_natCast p hε,
    ← constantCoeff_apply, map_natCast, ← map_natCast q, CharP.cast_eq_zero, map_zero]

/-- If `ε - 1 ∈ Ring.jacobson S` and `1 ≤ r`, then `ξ_r.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXiLevel_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S)
    {r : ℕ} (hr : 1 ≤ r) :
    (cyclotomicXiLevel p ε r).coeff 0 ∈ Ring.jacobson S := by
  obtain ⟨c, hc⟩ := cyclotomicXi_dvd_cyclotomicXiLevel p ε hr
  rw [show (cyclotomicXiLevel p ε r).coeff 0 = (cyclotomicXi p ε).coeff 0 * c.coeff 0 by
    simpa [mul_coeff_zero] using congrArg (·.coeff 0) hc]
  exact Ideal.mul_mem_right _ _ (cyclotomicXi_coeff_zero_mem_jacobson p hε)

/-- If `ε - 1 ∈ Ring.jacobson S` and `1 ≤ r`, then `ξ'_r.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S)
    {r : ℕ} (hr : 1 ≤ r) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 ∈ Ring.jacobson S := by
  rw [cyclotomicXiTildeLevel_coeff_zero]
  exact Ideal.pow_mem_of_mem _ (cyclotomicXiLevel_coeff_zero_mem_jacobson p hε hr) _
    (pow_pos hp.out.pos r)

/-- If `ε - 1 ∈ S⁰`, then `μ = [ε] - 1` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicMu_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicMu p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (by simpa using hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXi_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicXi p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ'` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiTilde_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicXiTilde p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ_r` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiLevel_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    cyclotomicXiLevel p ε r ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `ξ'_r` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiTildeLevel_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (μ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicMu {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicMu p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero (by simpa using hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXi {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXi p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ')` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiTilde p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiLevel {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiLevel p ε r}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ'_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (r : ℕ) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiTildeLevel p ε r}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)

private theorem not_isUnit_coeff_zero_cyclotomicXi {ε : S} (hnu : ¬ IsUnit (ε - 1)) :
    ¬ IsUnit ((cyclotomicXi p ε).coeff 0) := by
  let P : Polynomial (ZMod p) := ∑ j ∈ Finset.range p, Polynomial.X ^ j
  have hP : (Polynomial.X - 1) * P = (Polynomial.X - 1) * (Polynomial.X - 1) ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.pos, sub_pow_char, one_pow, mul_geom_sum]
  have hQ : P = (Polynomial.X - 1) ^ (p - 1) :=
    mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero 1) hP
  have h0 : (cyclotomicXi p ε).coeff 0 =
      ((_root_.frobeniusEquiv S p).symm ε - 1) ^ (p - 1) := by
    have heval := congrArg (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl p) S)
      ((_root_.frobeniusEquiv S p).symm ε)) hQ
    rw [cyclotomicXi_def, ← constantCoeff_apply, map_sum]
    simp only [map_pow, constantCoeff_apply, teichmuller_coeff_zero]
    simpa [P, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_one] using heval
  rw [h0, isUnit_pow_iff (Nat.sub_ne_zero_iff_lt.mpr hp.out.one_lt),
    ← isUnit_pow_iff hp.out.ne_zero, sub_pow_char, one_pow, _root_.frobeniusEquiv_symm_pow_p]
  exact hnu

private theorem not_isUnit_coeff_zero_cyclotomicXiTilde {ε : S} (hnu : ¬ IsUnit (ε - 1)) :
    ¬ IsUnit ((cyclotomicXiTilde p ε).coeff 0) := by
  rw [← frobenius_cyclotomicXi, coeff_frobenius_charP, isUnit_pow_iff hp.out.ne_zero]
  exact not_isUnit_coeff_zero_cyclotomicXi p hnu

private theorem not_isUnit_coeff_zero_cyclotomicXiLevel {ε : S} (hnu : ¬ IsUnit (ε - 1))
    {r : ℕ} (hr : 1 ≤ r) : ¬ IsUnit ((cyclotomicXiLevel p ε r).coeff 0) := fun hu ↦ by
  obtain ⟨c, hc⟩ := cyclotomicXi_dvd_cyclotomicXiLevel p ε hr
  exact not_isUnit_coeff_zero_cyclotomicXi p hnu (isUnit_of_dvd_unit
    ⟨c.coeff 0, by simpa [mul_coeff_zero] using congrArg (·.coeff 0) hc⟩ hu)

private theorem not_isUnit_coeff_zero_cyclotomicXiTildeLevel {ε : S} (hnu : ¬ IsUnit (ε - 1))
    {r : ℕ} (hr : 1 ≤ r) : ¬ IsUnit ((cyclotomicXiTildeLevel p ε r).coeff 0) := by
  rw [cyclotomicXiTildeLevel_coeff_zero, isUnit_pow_iff (pow_ne_zero r hp.out.ne_zero)]
  exact not_isUnit_coeff_zero_cyclotomicXiLevel p hnu hr

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[p, μ]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicMu {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicMu p ε] :=
  isRegular_natCast_cons_singleton _ (by simpa using hε) (by simpa using hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[μ, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicMu_natCast {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [cyclotomicMu p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (by simpa using hε) (by simpa using hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[p, ξ]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXi {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXi p ε] :=
  isRegular_natCast_cons_singleton _ (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXi p hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[ξ, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXi_natCast {ε : S} (hε : ε - 1 ∈ S⁰) (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [cyclotomicXi p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXi p hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[p, ξ']` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiTilde p ε] :=
  isRegular_natCast_cons_singleton _ (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXiTilde p hnu)

/-- If `ε - 1 ∈ S⁰` and `¬ IsUnit (ε - 1)`, then `[ξ', p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiTilde_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) :
    IsRegular (𝕎 S) [cyclotomicXiTilde p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_coeff_zero_cyclotomicXiTilde p hnu)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[p, ξ_r]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiLevel p ε r] :=
  isRegular_natCast_cons_singleton _ (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiLevel p hnu hr)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[ξ_r, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiLevel_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [cyclotomicXiLevel p ε r, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiLevel p hnu hr)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[p, ξ'_r]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTildeLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiTildeLevel p ε r] :=
  isRegular_natCast_cons_singleton _
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiTildeLevel p hnu hr)

/-- If `ε - 1 ∈ S⁰`, `¬ IsUnit (ε - 1)`, and `1 ≤ r`, then `[ξ'_r, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiTildeLevel_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hnu : ¬ IsUnit (ε - 1)) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [cyclotomicXiTildeLevel p ε r, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_coeff_zero_cyclotomicXiTildeLevel p hnu hr)

end TauCeti.WittVector
