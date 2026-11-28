/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Cyclotomic.Basic

import TauCeti.RingTheory.Perfect.Basic

/-!
# Finite Frobenius products of the cyclotomic period

Let `S` be a commutative ring, `ε ∈ S`, and let `φ` be the Witt vector Frobenius of `W(S)`. From
the forward cyclotomic period `ξ' = ∑_{j < p} [ε] ^ j` (`TauCeti.WittVector.cyclotomicXiTilde`) we
form the forward finite Frobenius product

* `ξ'_r = ∏_{j < r} φʲ(ξ')` (`TauCeti.WittVector.cyclotomicXiTildeLevel`),

without requiring characteristic `p` or perfection. In characteristic `p`, `ξ'_r` satisfies
`φʳ(μ) = ξ'_r · μ` and `(ξ'_r).coeff 0 = (ε - 1) ^ (p ^ r - 1)`. When `S` is perfect of
characteristic `p`, we also form

* `ξ_r = ∏_{j < r} φ⁻ʲ(ξ)` (`TauCeti.WittVector.cyclotomicXiLevel`),

which satisfies `φʳ(ξ_r) = ξ'_r`, `φ⁻ʳ(ξ'_r) = ξ_r`, `μ = ξ_r · φ⁻ʳ(μ)`,
`(ξ_r).coeff 0 = (ε ^ (1 / p ^ r) - 1) ^ (p ^ r - 1)`, and for each `j < r` the Frobenius factor
`φ⁻ʲ(ξ)` divides `ξ_r` (equivalently `ξ ∣ φʲ(ξ_r)`), while `φʲ(ξ') ∣ ξ'_r` (equivalently
`ξ' ∣ φ⁻ʲ(ξ'_r)`).

## Main definitions

* `TauCeti.WittVector.cyclotomicXiTildeLevel`, `TauCeti.WittVector.cyclotomicXiLevel`: the
  finite Frobenius products `ξ'_r` and `ξ_r` in `W(S)`.

## Main results

* `TauCeti.WittVector.cyclotomicXiTildeLevel_succ`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_succ'`,
  `TauCeti.WittVector.cyclotomicXiLevel_succ`, `TauCeti.WittVector.cyclotomicXiLevel_succ'`:
  recursions for `ξ'_r` and `ξ_r`.
* `TauCeti.WittVector.iterate_frobeniusEquiv_cyclotomicXiLevel`,
  `TauCeti.WittVector.iterate_frobenius_cyclotomicXiLevel`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel`,
  `TauCeti.WittVector.iterate_map_frobeniusEquiv_symm_cyclotomicXiTildeLevel`: `φʳ(ξ_r) = ξ'_r`
  and `φ⁻ʳ(ξ'_r) = ξ_r`.
* `TauCeti.WittVector.iterate_frobenius_cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_symm_cyclotomicXi_dvd_cyclotomicXiLevel`,
  `TauCeti.WittVector.cyclotomicXi_dvd_iterate_frobeniusEquiv_cyclotomicXiLevel`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel`,
  `TauCeti.WittVector.cyclotomicXiTilde_dvd_iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel`:
  divisibility by individual Frobenius factors for `j < r`.
* `TauCeti.WittVector.iterate_frobenius_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul`,
  `TauCeti.WittVector.cyclotomicMu_eq_cyclotomicXiLevel_mul`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul`:
  `φʳ(μ) = ξ'_r · μ` and `μ = ξ_r · φ⁻ʳ(μ)`.
* `TauCeti.WittVector.cyclotomicXiTildeLevel_coeff_zero`,
  `TauCeti.WittVector.cyclotomicXiLevel_coeff_zero`,
  `TauCeti.WittVector.cyclotomicXiLevel_coeff_zero_mul`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_coeff_zero_eq_pow`: zeroth Witt coordinate formulas
  and relations.
* `TauCeti.WittVector.cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors`,
  `TauCeti.WittVector.cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_coeff_zero_mem_jacobson`,
  `TauCeti.WittVector.cyclotomicXiLevel_coeff_zero_mem_jacobson`,
  `TauCeti.WittVector.not_isUnit_coeff_zero_cyclotomicXiTildeLevel`,
  `TauCeti.WittVector.not_isUnit_coeff_zero_cyclotomicXiLevel`: nonzerodivisor, Jacobson, and
  nonunit properties of the zeroth Witt coordinates of `ξ'_r` and `ξ_r`.
* `TauCeti.WittVector.span_cyclotomicXiLevel_eq_of_span_cyclotomicXi_eq`: equality of `(ξ)`
  propagates to `(ξ_r)` for all `r`.
* `TauCeti.WittVector.map_cyclotomicXiTildeLevel`, `TauCeti.WittVector.map_cyclotomicXiLevel`,
  `TauCeti.WittVector.map_cyclotomicXiTildeLevel_eq_natCast`,
  `TauCeti.WittVector.map_cyclotomicXiLevel_eq_natCast`,
  `TauCeti.WittVector.cyclotomicXiTildeLevel_one_eq_natCast`,
  `TauCeti.WittVector.cyclotomicXiLevel_one_eq_natCast`: naturality and specialization at
  `ε = 1`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemmas 3.12, 3.13, and 3.23.
-/

public section

open _root_.WittVector
open scoped nonZeroDivisors

namespace TauCeti.WittVector

variable (p : ℕ) [hp : Fact p.Prime] {S T : Type*} [CommRing S] [CommRing T]

local notation "𝕎" => _root_.WittVector p

/-- The Frobenius-twisted finite cyclotomic product `ξ'_r = ∏_{j < r} φʲ(ξ')` in `W(S)`. -/
noncomputable def cyclotomicXiTildeLevel (ε : S) (r : ℕ) : 𝕎 S :=
  ∏ j ∈ Finset.range r, (frobenius^[j]) (cyclotomicXiTilde p ε)

/-- Unfolding lemma for `cyclotomicXiTildeLevel`. -/
theorem cyclotomicXiTildeLevel_def (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r =
      ∏ j ∈ Finset.range r, (frobenius^[j]) (cyclotomicXiTilde p ε) :=
  (rfl)

/-- At level `0`, `ξ'_0 = 1`. -/
@[simp]
theorem cyclotomicXiTildeLevel_zero (ε : S) : cyclotomicXiTildeLevel p ε 0 = 1 := by
  simp [cyclotomicXiTildeLevel_def]

/-- At level `1`, `ξ'_1 = ξ'`. -/
@[simp]
theorem cyclotomicXiTildeLevel_one (ε : S) :
    cyclotomicXiTildeLevel p ε 1 = cyclotomicXiTilde p ε := by
  simp [cyclotomicXiTildeLevel_def]

/-- Recursion for `ξ'_{r + 1}` appending `φʳ(ξ')`. -/
theorem cyclotomicXiTildeLevel_succ (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε (r + 1) =
      cyclotomicXiTildeLevel p ε r * (frobenius^[r]) (cyclotomicXiTilde p ε) :=
  Finset.prod_range_succ _ r

/-- At level `2`, `ξ'_2 = ξ' · φ(ξ')`. -/
theorem cyclotomicXiTildeLevel_two (ε : S) :
    cyclotomicXiTildeLevel p ε 2 =
      cyclotomicXiTilde p ε * frobenius (cyclotomicXiTilde p ε) := by
  rw [cyclotomicXiTildeLevel_succ, cyclotomicXiTildeLevel_one, Function.iterate_one]

/-- Recursion for `ξ'_{r + 1}` factoring out `ξ'`: `ξ'_{r + 1} = ξ' · φ(ξ'_r)`. -/
theorem cyclotomicXiTildeLevel_succ' (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε (r + 1) =
      cyclotomicXiTilde p ε * frobenius (cyclotomicXiTildeLevel p ε r) := by
  rw [cyclotomicXiTildeLevel_def, Finset.prod_range_succ', Function.iterate_zero_apply,
    mul_comm, cyclotomicXiTildeLevel_def, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun j _ ↦ Function.iterate_succ_apply' _ j _

/-- `φʲ(ξ')` divides `ξ'_r` for every `j < r`. -/
theorem iterate_frobenius_cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel (ε : S) {j r : ℕ}
    (hj : j < r) :
    (frobenius^[j]) (cyclotomicXiTilde p ε) ∣ cyclotomicXiTildeLevel p ε r :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)

/-- `ξ'_r ∣ ξ'_s` whenever `r ≤ s`. -/
theorem cyclotomicXiTildeLevel_dvd_cyclotomicXiTildeLevel_of_le (ε : S) {r s : ℕ} (hrs : r ≤ s) :
    cyclotomicXiTildeLevel p ε r ∣ cyclotomicXiTildeLevel p ε s :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hrs)

/-- `ξ'` divides `ξ'_r` for every `r ≥ 1`. -/
theorem cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel (ε : S) {r : ℕ} (hr : 1 ≤ r) :
    cyclotomicXiTilde p ε ∣ cyclotomicXiTildeLevel p ε r := by
  simpa only [cyclotomicXiTildeLevel_one] using
    cyclotomicXiTildeLevel_dvd_cyclotomicXiTildeLevel_of_le p ε hr

/-- `WittVector.map f` sends `ξ'_r(ε)` to `ξ'_r(f ε)`. -/
@[simp]
theorem map_cyclotomicXiTildeLevel (f : S →+* T) (ε : S) (r : ℕ) :
    map f (cyclotomicXiTildeLevel p ε r) = cyclotomicXiTildeLevel p (f ε) r := by
  simp only [cyclotomicXiTildeLevel_def, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [(Function.Semiconj.iterate_right (map_frobenius f) j) _, map_cyclotomicXiTilde]

/-- At `ε = 1`, `ξ'_r(1) = p ^ r`. -/
@[simp]
theorem cyclotomicXiTildeLevel_one_eq_natCast (r : ℕ) :
    cyclotomicXiTildeLevel p (1 : S) r = (p : 𝕎 S) ^ r := by
  have hprod :
      ∏ j ∈ Finset.range r, (frobenius^[j]) (cyclotomicXiTilde p (1 : S)) =
        ∏ _j ∈ Finset.range r, (p : 𝕎 S) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [cyclotomicXiTilde_one, Function.iterate_fixed (map_natCast (frobenius : 𝕎 S →+* 𝕎 S) p)]
  rw [cyclotomicXiTildeLevel_def, hprod, Finset.prod_const, Finset.card_range]

/-- If `f ε = 1`, then `W(f)` sends `ξ'_r` to `p ^ r`. -/
theorem map_cyclotomicXiTildeLevel_eq_natCast {f : S →+* T} {ε : S} (hε : f ε = 1) (r : ℕ) :
    map f (cyclotomicXiTildeLevel p ε r) = (p : 𝕎 T) ^ r := by
  rw [map_cyclotomicXiTildeLevel, hε, cyclotomicXiTildeLevel_one_eq_natCast]

section CharP

variable [CharP S p]

/-- **`φʳ(μ) = ξ'_r · μ`** in characteristic `p`. -/
theorem iterate_frobenius_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul (ε : S) (r : ℕ) :
    (frobenius^[r]) (cyclotomicMu p ε) = cyclotomicXiTildeLevel p ε r * cyclotomicMu p ε := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul,
      cyclotomicXiTildeLevel_succ', mul_assoc,
      mul_left_comm (frobenius (cyclotomicXiTildeLevel p ε r))]

/-- `ξ'_r` divides `φʳ(μ)` in `W(S)`. -/
theorem cyclotomicXiTildeLevel_dvd_iterate_frobenius_cyclotomicMu (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ∣ (frobenius^[r]) (cyclotomicMu p ε) :=
  ⟨_, iterate_frobenius_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul p ε r⟩

/-- In characteristic `p`, the zeroth Witt coordinate of `ξ'_r = ∏_{j < r} φʲ(ξ')` is
`(ε - 1) ^ (p ^ r - 1)`. -/
@[simp]
theorem cyclotomicXiTildeLevel_coeff_zero (ε : S) (r : ℕ) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 = (ε - 1) ^ (p ^ r - 1) := by
  rw [cyclotomicXiTildeLevel_def, ← constantCoeff_apply, map_prod]
  have hprod :
      ∏ j ∈ Finset.range r, constantCoeff ((frobenius^[j]) (cyclotomicXiTilde p ε)) =
        ∏ j ∈ Finset.range r, (ε - 1) ^ ((p - 1) * p ^ j) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [constantCoeff_apply, iterate_frobenius_coeff, cyclotomicXiTilde_coeff_zero, ← pow_mul]
  rw [hprod, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, mul_comm]
  congr 1
  have hgeom := geom_sum_mul_add (p - 1) r
  rw [Nat.sub_add_cancel hp.out.one_le] at hgeom
  exact Nat.eq_sub_of_add_eq hgeom

/-- If `ε - 1 ∈ S⁰`, then `ξ'_r.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 ∈ S⁰ := by
  rw [cyclotomicXiTildeLevel_coeff_zero]
  exact pow_mem hε (p ^ r - 1)

/-- If `ε - 1 ∈ Ring.jacobson S` and `1 ≤ r`, then `ξ'_r.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S)
    {r : ℕ} (hr : 1 ≤ r) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 ∈ Ring.jacobson S := by
  obtain ⟨c, hc⟩ := map_dvd (constantCoeff : 𝕎 S →+* S)
    (cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel p ε hr)
  rw [constantCoeff_apply, constantCoeff_apply] at hc
  rw [hc]
  exact Ideal.mul_mem_right _ _ (cyclotomicXiTilde_coeff_zero_mem_jacobson p hε)

/-- If `ε - 1` is not a unit of `S` and `1 ≤ r`, then `ξ'_r.coeff 0` is not a unit of `S`. -/
theorem not_isUnit_coeff_zero_cyclotomicXiTildeLevel {ε : S} (hnu : ¬ IsUnit (ε - 1))
    {r : ℕ} (hr : 1 ≤ r) : ¬ IsUnit ((cyclotomicXiTildeLevel p ε r).coeff 0) := fun hu ↦
  not_isUnit_coeff_zero_cyclotomicXiTilde p hnu <|
    isUnit_of_dvd_unit
      (by
        simpa only [constantCoeff_apply] using
          map_dvd (constantCoeff : 𝕎 S →+* S)
            (cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel p ε hr))
      hu

end CharP

section Perfect

variable [CharP S p] [PerfectRing S p]

/-- The finite cyclotomic Frobenius product `ξ_r = ∏_{j < r} φ⁻ʲ(ξ)` in `W(S)`. -/
noncomputable def cyclotomicXiLevel (ε : S) (r : ℕ) : 𝕎 S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε)

/-- Unfolding lemma for `cyclotomicXiLevel`. -/
theorem cyclotomicXiLevel_def (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε r =
      ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε) :=
  (rfl)

/-- At level `0`, `ξ_0 = 1`. -/
@[simp]
theorem cyclotomicXiLevel_zero (ε : S) : cyclotomicXiLevel p ε 0 = 1 := by
  simp [cyclotomicXiLevel_def]

/-- At level `1`, `ξ_1 = ξ`. -/
@[simp]
theorem cyclotomicXiLevel_one (ε : S) : cyclotomicXiLevel p ε 1 = cyclotomicXi p ε := by
  simp [cyclotomicXiLevel_def]

/-- Recursion for `ξ_{r + 1}` appending `φ⁻ʳ(ξ)`. -/
theorem cyclotomicXiLevel_succ (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε (r + 1) =
      cyclotomicXiLevel p ε r * ((frobeniusEquiv p S).symm^[r]) (cyclotomicXi p ε) :=
  Finset.prod_range_succ _ r

/-- At level `2`, `ξ_2 = ξ · φ⁻¹(ξ)`. -/
theorem cyclotomicXiLevel_two (ε : S) :
    cyclotomicXiLevel p ε 2 = cyclotomicXi p ε * (frobeniusEquiv p S).symm (cyclotomicXi p ε) := by
  rw [cyclotomicXiLevel_succ, cyclotomicXiLevel_one, Function.iterate_one]

/-- Recursion for `ξ_{r + 1}` factoring out `ξ`: `ξ_{r + 1} = ξ · φ⁻¹(ξ_r)`. -/
theorem cyclotomicXiLevel_succ' (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε (r + 1) =
      cyclotomicXi p ε * (frobeniusEquiv p S).symm (cyclotomicXiLevel p ε r) := by
  rw [cyclotomicXiLevel_def, Finset.prod_range_succ', Function.iterate_zero_apply, mul_comm,
    cyclotomicXiLevel_def, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun j _ ↦ Function.iterate_succ_apply' _ j _

/-- `φʳ(ξ_r) = ξ'_r`. -/
theorem iterate_frobeniusEquiv_cyclotomicXiLevel (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (cyclotomicXiLevel p ε r) = cyclotomicXiTildeLevel p ε r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [cyclotomicXiLevel_succ', cyclotomicXiTildeLevel_succ, Function.iterate_succ_apply,
      map_mul, (frobeniusEquiv p S).apply_symm_apply, iterate_map_mul (frobeniusEquiv p S), ih,
      iterate_frobeniusEquiv_apply, _root_.WittVector.frobeniusEquiv_apply, frobenius_cyclotomicXi,
      mul_comm]

/-- `φʳ(ξ_r) = ξ'_r`, in `simp`-normal form. -/
@[simp]
theorem iterate_frobenius_cyclotomicXiLevel (ε : S) (r : ℕ) :
    (frobenius^[r]) (cyclotomicXiLevel p ε r) = cyclotomicXiTildeLevel p ε r := by
  rw [← iterate_frobeniusEquiv_apply, iterate_frobeniusEquiv_cyclotomicXiLevel]

/-- `φ⁻ʳ(ξ'_r) = ξ_r`. -/
theorem iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S).symm^[r]) (cyclotomicXiTildeLevel p ε r) = cyclotomicXiLevel p ε r := by
  rw [← iterate_frobeniusEquiv_cyclotomicXiLevel]
  exact ((frobeniusEquiv p S).left_inv.iterate r) _

/-- `φ⁻ʳ(ξ'_r) = ξ_r`, in `simp`-normal form. -/
@[simp]
theorem iterate_map_frobeniusEquiv_symm_cyclotomicXiTildeLevel (ε : S) (r : ℕ) :
    ((map ((_root_.frobeniusEquiv S p).symm : S →+* S))^[r]) (cyclotomicXiTildeLevel p ε r) =
      cyclotomicXiLevel p ε r := by
  rw [← _root_.WittVector.frobeniusEquiv_symm_apply,
    iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel]

/-- `φ⁻ʲ(ξ)` divides `ξ_r` for every `j < r`. -/
theorem iterate_frobeniusEquiv_symm_cyclotomicXi_dvd_cyclotomicXiLevel (ε : S) {j r : ℕ}
    (hj : j < r) :
    ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε) ∣ cyclotomicXiLevel p ε r :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)

/-- `ξ` divides `φʲ(ξ_r)` for every `j < r`. -/
theorem cyclotomicXi_dvd_iterate_frobeniusEquiv_cyclotomicXiLevel (ε : S) {j r : ℕ}
    (hj : j < r) :
    cyclotomicXi p ε ∣ ((frobeniusEquiv p S)^[j]) (cyclotomicXiLevel p ε r) := by
  obtain ⟨c, hc⟩ := iterate_frobeniusEquiv_symm_cyclotomicXi_dvd_cyclotomicXiLevel p ε hj
  refine ⟨((frobeniusEquiv p S)^[j]) c, ?_⟩
  rw [hc, iterate_map_mul,
    Function.LeftInverse.iterate (frobeniusEquiv p S).apply_symm_apply j]

/-- `φʲ(ξ')` divides `ξ'_r` for every `j < r`. -/
theorem iterate_frobeniusEquiv_cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel (ε : S) {j r : ℕ}
    (hj : j < r) :
    ((frobeniusEquiv p S)^[j]) (cyclotomicXiTilde p ε) ∣ cyclotomicXiTildeLevel p ε r := by
  rw [iterate_frobeniusEquiv_apply]
  exact iterate_frobenius_cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel p ε hj

/-- `ξ'` divides `φ⁻ʲ(ξ'_r)` for every `j < r`. -/
theorem cyclotomicXiTilde_dvd_iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel (ε : S) {j r : ℕ}
    (hj : j < r) :
    cyclotomicXiTilde p ε ∣ ((frobeniusEquiv p S).symm^[j]) (cyclotomicXiTildeLevel p ε r) := by
  obtain ⟨c, hc⟩ := iterate_frobeniusEquiv_cyclotomicXiTilde_dvd_cyclotomicXiTildeLevel p ε hj
  refine ⟨((frobeniusEquiv p S).symm^[j]) c, ?_⟩
  rw [hc, iterate_map_mul,
    Function.LeftInverse.iterate (frobeniusEquiv p S).symm_apply_apply j]

/-- `ξ_r ∣ ξ_s` whenever `r ≤ s`. -/
theorem cyclotomicXiLevel_dvd_cyclotomicXiLevel_of_le (ε : S) {r s : ℕ} (hrs : r ≤ s) :
    cyclotomicXiLevel p ε r ∣ cyclotomicXiLevel p ε s :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hrs)

/-- `ξ` divides `ξ_r` for every `r ≥ 1`. -/
theorem cyclotomicXi_dvd_cyclotomicXiLevel (ε : S) {r : ℕ} (hr : 1 ≤ r) :
    cyclotomicXi p ε ∣ cyclotomicXiLevel p ε r := by
  simpa only [cyclotomicXiLevel_one] using
    cyclotomicXiLevel_dvd_cyclotomicXiLevel_of_le p ε hr

/-- If `cyclotomicXi p ε` and `cyclotomicXi p ε'` generate the same ideal of `W(S)`, then so do
`cyclotomicXiLevel p ε r` and `cyclotomicXiLevel p ε' r` for every `r : ℕ`. -/
theorem span_cyclotomicXiLevel_eq_of_span_cyclotomicXi_eq {ε ε' : S}
    (h : Ideal.span {cyclotomicXi p ε} = Ideal.span {cyclotomicXi p ε'}) (r : ℕ) :
    Ideal.span {cyclotomicXiLevel p ε r} = Ideal.span {cyclotomicXiLevel p ε' r} := by
  have hdvd (a b : S)
      (hab : Ideal.span {cyclotomicXi p a} ≤ Ideal.span {cyclotomicXi p b}) (j : ℕ) :
      ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p b) ∣
        ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p a) := by
    have h0 : cyclotomicXi p b ∣ cyclotomicXi p a :=
      Ideal.mem_span_singleton.mp (hab (Ideal.mem_span_singleton_self _))
    induction j with
    | zero => exact h0
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact map_dvd _ ih
  refine le_antisymm ?_ ?_ <;> rw [Ideal.span_singleton_le_span_singleton,
    cyclotomicXiLevel_def, cyclotomicXiLevel_def]
  · exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ ↦ hdvd ε ε' h.le j
  · exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ ↦ hdvd ε' ε h.ge j

/-- **`μ = ξ_r · φ⁻ʳ(μ)`**: the iterated geometric sum factorisation in `W(S)`. -/
theorem cyclotomicMu_eq_cyclotomicXiLevel_mul (ε : S) (r : ℕ) :
    cyclotomicMu p ε =
      cyclotomicXiLevel p ε r * ((frobeniusEquiv p S).symm^[r]) (cyclotomicMu p ε) := by
  induction r with
  | zero => simp
  | succ r ih =>
    conv_lhs => rw [ih]
    rw [cyclotomicXiLevel_succ, Function.iterate_succ_apply (frobeniusEquiv p S).symm r, mul_assoc,
      ← iterate_map_mul (frobeniusEquiv p S).symm, ← cyclotomicMu_eq_cyclotomicXi_mul]

/-- **`φʳ(μ) = ξ'_r · μ`**, the Frobenius twist of `cyclotomicMu_eq_cyclotomicXiLevel_mul`. -/
theorem iterate_frobeniusEquiv_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (cyclotomicMu p ε) =
      cyclotomicXiTildeLevel p ε r * cyclotomicMu p ε := by
  rw [iterate_frobeniusEquiv_apply, iterate_frobenius_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul]

/-- `ξ_r` divides `μ` in `W(S)`. -/
theorem cyclotomicXiLevel_dvd_cyclotomicMu (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε r ∣ cyclotomicMu p ε :=
  ⟨_, cyclotomicMu_eq_cyclotomicXiLevel_mul p ε r⟩

/-- The cyclotomic period `μ` lies in every ideal `(ξ_r)`. -/
theorem span_cyclotomicMu_le_span_cyclotomicXiLevel (ε : S) (r : ℕ) :
    Ideal.span {cyclotomicMu p ε} ≤ Ideal.span {cyclotomicXiLevel p ε r} :=
  Ideal.span_singleton_le_span_singleton.mpr (cyclotomicXiLevel_dvd_cyclotomicMu p ε r)

/-- `ξ'_r` divides `φʳ(μ)` in `W(S)`. -/
theorem cyclotomicXiTildeLevel_dvd_iterate_frobeniusEquiv_cyclotomicMu (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ∣ ((frobeniusEquiv p S)^[r]) (cyclotomicMu p ε) :=
  ⟨_, iterate_frobeniusEquiv_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul p ε r⟩

/-- Zeroth Witt coordinate relation for `μ = ξ_r · φ⁻ʳ(μ)`:
`ξ_r.coeff 0 · (ε ^ (1 / p ^ r) - 1) = ε - 1`. -/
theorem cyclotomicXiLevel_coeff_zero_mul (ε : S) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 * (((_root_.frobeniusEquiv S p).symm^[r]) ε - 1) =
      ε - 1 := by
  have h := congrArg (·.coeff 0) (cyclotomicMu_eq_cyclotomicXiLevel_mul p ε r).symm
  rw [mul_coeff_zero, iterate_frobeniusEquiv_symm_cyclotomicMu, cyclotomicMu_coeff_zero,
    cyclotomicMu_coeff_zero] at h
  exact h

/-- The zeroth Witt coordinate of `ξ'_r` is the `p ^ r`-th power of that of `ξ_r`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_eq_pow (ε : S) (r : ℕ) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 = (cyclotomicXiLevel p ε r).coeff 0 ^ p ^ r := by
  rw [← iterate_frobeniusEquiv_cyclotomicXiLevel, coeff_iterate_frobeniusEquiv]

/-- Over a perfect ring of characteristic `p`, the zeroth Witt coordinate of
`ξ_r = ∏_{j < r} φ⁻ʲ(ξ)` is `(φ⁻ʳ(ε) - 1) ^ (p ^ r - 1)`. -/
@[simp]
theorem cyclotomicXiLevel_coeff_zero (ε : S) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 =
      (((_root_.frobeniusEquiv S p).symm^[r]) ε - 1) ^ (p ^ r - 1) := by
  have hcoeff (x : 𝕎 S) :
      (((frobeniusEquiv p S).symm^[r]) x).coeff 0 =
        ((_root_.frobeniusEquiv S p).symm^[r]) (x.coeff 0) := by
    induction r generalizing x with
    | zero => rfl
    | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        _root_.WittVector.frobeniusEquiv_symm_apply, map_coeff]; rfl
  rw [← iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel, hcoeff,
    cyclotomicXiTildeLevel_coeff_zero, iterate_map_pow, iterate_map_sub, iterate_map_one]

/-- If `ε - 1 ∈ S⁰`, then `ξ_r.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 ∈ S⁰ :=
  (mul_mem_nonZeroDivisors.mp (by rwa [cyclotomicXiLevel_coeff_zero_mul])).1

/-- If `ε - 1 ∈ Ring.jacobson S` and `1 ≤ r`, then `ξ_r.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXiLevel_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S)
    {r : ℕ} (hr : 1 ≤ r) :
    (cyclotomicXiLevel p ε r).coeff 0 ∈ Ring.jacobson S := by
  obtain ⟨c, hc⟩ := map_dvd (constantCoeff : 𝕎 S →+* S) (cyclotomicXi_dvd_cyclotomicXiLevel p ε hr)
  rw [constantCoeff_apply, constantCoeff_apply] at hc
  rw [hc]
  exact Ideal.mul_mem_right _ _ (cyclotomicXi_coeff_zero_mem_jacobson p hε)

/-- If `ε - 1` is not a unit of `S` and `1 ≤ r`, then `ξ_r.coeff 0` is not a unit of `S`. -/
theorem not_isUnit_coeff_zero_cyclotomicXiLevel {ε : S} (hnu : ¬ IsUnit (ε - 1))
    {r : ℕ} (hr : 1 ≤ r) : ¬ IsUnit ((cyclotomicXiLevel p ε r).coeff 0) := fun hu ↦
  not_isUnit_coeff_zero_cyclotomicXi p hnu <|
    isUnit_of_dvd_unit
      (by
        simpa only [constantCoeff_apply] using
          map_dvd (constantCoeff : 𝕎 S →+* S) (cyclotomicXi_dvd_cyclotomicXiLevel p ε hr))
      hu

/-- For `ε ≠ 1`, the zeroth Witt coordinate of every `ξ_r` is nonzero: it divides `ε - 1 ≠ 0`. -/
theorem coeff_zero_cyclotomicXiLevel_ne_zero {ε : S} (hε : ε ≠ 1) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 ≠ 0 :=
  fun h ↦ coeff_zero_cyclotomicMu_ne_zero p hε <| by
    rw [cyclotomicMu_coeff_zero, ← cyclotomicXiLevel_coeff_zero_mul p ε r, h, zero_mul]

/-- For `ε ≠ 1`, every finite product `ξ_r` is nonzero. -/
theorem cyclotomicXiLevel_ne_zero {ε : S} (hε : ε ≠ 1) (r : ℕ) : cyclotomicXiLevel p ε r ≠ 0 :=
  fun h ↦ coeff_zero_cyclotomicXiLevel_ne_zero p hε r (by rw [h, zero_coeff])

/-- For `ε ≠ 1`, every twisted product `ξ'_r` is nonzero: `φʳ(ξ_r) = ξ'_r` and `φ` is injective. -/
theorem cyclotomicXiTildeLevel_ne_zero {ε : S} (hε : ε ≠ 1) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ≠ 0 := by
  intro h
  rw [← iterate_frobeniusEquiv_cyclotomicXiLevel, ← iterate_map_zero (frobeniusEquiv p S) r] at h
  exact cyclotomicXiLevel_ne_zero p hε r ((frobeniusEquiv p S).injective.iterate r h)

section LevelNatural

variable [CharP T p] [PerfectRing T p]

/-- `WittVector.map f` sends `ξ_r(ε)` to `ξ_r(f ε)`. -/
@[simp]
theorem map_cyclotomicXiLevel (f : S →+* T) (ε : S) (r : ℕ) :
    map f (cyclotomicXiLevel p ε r) = cyclotomicXiLevel p (f ε) r := by
  simp only [cyclotomicXiLevel_def, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [iterate_frobeniusEquiv_symm_cyclotomicXi, map_cyclotomicXi,
    iterate_frobeniusEquiv_symm_cyclotomicXi, RingHom.map_iterate_frobeniusEquiv_symm p f j _]

end LevelNatural

/-- If `f ε = 1` and `T` is reduced, then `W(f)` sends `ξ_r` to `p ^ r`. -/
theorem map_cyclotomicXiLevel_eq_natCast [IsReduced T] {f : S →+* T} {ε : S}
    (hε : f ε = 1) (r : ℕ) :
    map f (cyclotomicXiLevel p ε r) = (p : 𝕎 T) ^ r := by
  simp only [cyclotomicXiLevel_def, map_prod]
  have hf (j : ℕ) : f (((_root_.frobeniusEquiv S p).symm^[j]) ε) = 1 := by
    induction j with
    | zero => exact hε
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← sub_eq_zero]
      refine IsReduced.eq_zero _ ⟨p, ?_⟩
      rw [← map_one f, ← map_sub, ← map_pow, frobeniusEquiv_symm_sub_one_pow]
      simp [ih]
  have hprod :
      ∏ j ∈ Finset.range r, map f (((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε)) =
        ∏ _j ∈ Finset.range r, (p : 𝕎 T) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [iterate_frobeniusEquiv_symm_cyclotomicXi]
    exact map_cyclotomicXi_eq_natCast p (hf j)
  rw [hprod, Finset.prod_const, Finset.card_range]

/-- At `ε = 1`, `ξ_r(1) = p ^ r`. -/
@[simp]
theorem cyclotomicXiLevel_one_eq_natCast (r : ℕ) :
    cyclotomicXiLevel p (1 : S) r = (p : 𝕎 S) ^ r := by
  have : IsReduced S := TauCeti.isReduced_of_perfectRing S p
  simpa [WittVector.map_id] using
    map_cyclotomicXiLevel_eq_natCast p (f := RingHom.id S) (ε := (1 : S)) rfl r

end Perfect

end TauCeti.WittVector
