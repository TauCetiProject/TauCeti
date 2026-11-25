/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Rat.Lemmas
public import TauCeti.NumberTheory.Supernatural
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The rational subgroup of a supernatural number and the invariant of a sequence of sizes

For a supernatural number `ν`, let `Q_ν` be the set of rationals `a / b` with `a ∈ ℤ`, `b ∈ ℕ+`
and `b ∣ ν`, that is `ofNat b ≤ ν`. Equivalently, `Q_ν` consists of the rationals whose reduced
denominator divides `ν`. It is an additive subgroup of `ℚ`, since the denominator of a sum
divides the lcm of the denominators; it contains `ℤ = Q_1`, grows with `ν`, and determines `ν`:
`Q_ν ≤ Q_μ` exactly when `ν ≤ μ`.

For a UHF algebra with matrix sizes `dₙ`, the supernatural invariant is
`supernaturalOfSizes d = ⨆ₙ ofNat dₙ`, and the ordered `K₀`-group with its unit is
`(Q_ν, Q_ν ∩ ℚ≥0, 1)` (Glimm's classification). This file records the number-theoretic side.

## Main definitions

* `TauCeti.Supernatural.ratSubgroup ν`: the additive subgroup `Q_ν` of `ℚ`.
* `TauCeti.Supernatural.supernaturalOfSizes d`: the supremum `⨆ₙ ofNat (d n)`.

## Main statements

* `TauCeti.Supernatural.mem_ratSubgroup_iff_exists`: `Q_ν` consists of the `a / b` with
  `ofNat b ≤ ν`.
* `TauCeti.Supernatural.ratSubgroup_le_ratSubgroup_iff`: `Q_ν ≤ Q_μ ↔ ν ≤ μ`.
* `TauCeti.Supernatural.ratSubgroup_top`, `mem_ratSubgroup_ofNat_iff`,
  `mem_ratSubgroup_primePower_top_iff`: `Q_⊤ = ℚ`, `Q_(ofNat n) = (1/n) ℤ` and
  `Q_(p^∞) = ℤ[1/p]`.
* `TauCeti.Supernatural.supernaturalOfSizes_const`, `supernaturalOfSizes_prime_pow` and
  `supernaturalOfSizes_factorial`: constant sizes `d` give `ofNat d`, sizes `pⁿ` give `p^∞`, and
  sizes `n!` give `⊤`.

## References

* J. G. Glimm, *On a certain class of operator algebras*, Trans. Amer. Math. Soc. 95 (1960),
  318–340, Definition 1.3.
-/

public section

namespace TauCeti

namespace Supernatural

/-- The supernatural number of a prime power `p ^ k` is the supernatural prime power. -/
theorem ofNat_prime_pow (p : Nat.Primes) (k : ℕ) :
    ofNat ⟨(p : ℕ) ^ k, pow_pos p.prop.pos k⟩ = primePower p k := by
  ext q
  refine (ofNat_apply_eq_factorization _ q).trans ?_
  rw [PNat.mk_coe, p.prop.factorization_pow]
  by_cases hq : q = p
  · subst hq
    simp
  · have hpq : (p : ℕ) ≠ q := fun h ↦ hq (Subtype.ext h.symm)
    simp [primePower_apply_of_ne hq, hpq]

/-- The additive subgroup `Q_ν` of `ℚ` attached to a supernatural number `ν`: the rationals whose
reduced denominator `b` satisfies `ofNat b ≤ ν`, that is, `b ∣ ν`. -/
def ratSubgroup (ν : Supernatural) : AddSubgroup ℚ where
  carrier := {x | ofNat x.pnatDen ≤ ν}
  zero_mem' := by simp [Rat.pnatDen_zero, one_eq_bot]
  add_mem' {x y} hx hy := by
    have h : (x + y).pnatDen ∣ PNat.lcm x.pnatDen y.pnatDen := by
      rw [PNat.dvd_iff, PNat.lcm_coe, Rat.coe_pnatDen, Rat.coe_pnatDen, Rat.coe_pnatDen]
      exact Rat.add_den_dvd_lcm x y
    exact (ofNat_le_ofNat_iff.2 h).trans (by rw [ofNat_lcm]; exact sup_le hx hy)
  neg_mem' {x} hx := by
    have h : (-x).pnatDen = x.pnatDen := PNat.coe_injective (by simp [Rat.coe_pnatDen])
    simpa [h] using hx

variable {ν μ : Supernatural}

/-- A rational lies in `Q_ν` exactly when its reduced denominator divides `ν`. -/
theorem mem_ratSubgroup_iff {x : ℚ} : x ∈ ratSubgroup ν ↔ ofNat x.pnatDen ≤ ν :=
  Iff.rfl

/-- The reduced denominator of `a / b` divides `b`. -/
private theorem pnatDen_intCast_div_dvd (a : ℤ) (b : ℕ+) : ((a : ℚ) / b).pnatDen ∣ b := by
  rw [PNat.dvd_iff, Rat.coe_pnatDen, ← Int.natCast_dvd_natCast]
  have h := Rat.den_dvd a b
  rwa [Rat.divInt_eq_div, Int.cast_natCast] at h

/-- `Q_ν` consists of the rationals `a / b` with `a ∈ ℤ`, `b ∈ ℕ+` and `ofNat b ≤ ν`. -/
theorem mem_ratSubgroup_iff_exists {x : ℚ} :
    x ∈ ratSubgroup ν ↔ ∃ (a : ℤ) (b : ℕ+), ofNat b ≤ ν ∧ x = a / b := by
  refine ⟨fun hx ↦ ⟨x.num, x.pnatDen, hx, ?_⟩, ?_⟩
  · rw [Rat.coe_pnatDen, Rat.num_div_den]
  · rintro ⟨a, b, hb, rfl⟩
    exact (ofNat_le_ofNat_iff.2 (pnatDen_intCast_div_dvd a b)).trans hb

/-- `1 / b` lies in `Q_ν` exactly when `ofNat b ≤ ν`. -/
theorem inv_mem_ratSubgroup_iff (b : ℕ+) : ((b : ℚ))⁻¹ ∈ ratSubgroup ν ↔ ofNat b ≤ ν := by
  have h : ((b : ℚ))⁻¹.pnatDen = b := by
    rw [Rat.pnatDen_eq_iff_den_eq, Rat.inv_natCast_den]
    simp
  rw [mem_ratSubgroup_iff, h]

/-- **`Q_ν` determines `ν`.** `Q_ν ≤ Q_μ` exactly when `ν ≤ μ`. -/
theorem ratSubgroup_le_ratSubgroup_iff : ratSubgroup ν ≤ ratSubgroup μ ↔ ν ≤ μ := by
  refine ⟨fun h ↦ le_iff.2 fun p ↦ ?_, fun h x hx ↦ (mem_ratSubgroup_iff.1 hx).trans h⟩
  by_contra hlt
  rw [not_le] at hlt
  -- `μ p = k` is finite and `p ^ (k + 1) ∣ ν`, but `p ^ (k + 1) ∤ μ`.
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hlt.trans_le le_top).ne
  have hν : ofNat ⟨(p : ℕ) ^ (k + 1), pow_pos p.prop.pos _⟩ ≤ ν := by
    rw [ofNat_prime_pow, primePower_le_iff, Nat.cast_add, Nat.cast_one, hk]
    exact Order.add_one_le_of_lt (hk ▸ hlt)
  have hμ := (inv_mem_ratSubgroup_iff _).1 (h ((inv_mem_ratSubgroup_iff _).2 hν))
  rw [ofNat_prime_pow, primePower_le_iff, ← hk, Nat.cast_le] at hμ
  omega

/-- `Q_1 = ℤ`. -/
theorem mem_ratSubgroup_one_iff {x : ℚ} : x ∈ ratSubgroup 1 ↔ ∃ a : ℤ, x = a := by
  rw [mem_ratSubgroup_iff, ← ofNat_one, ofNat_le_ofNat_iff, PNat.dvd_one_iff,
    Rat.pnatDen_eq_iff_den_eq, PNat.one_coe]
  exact ⟨fun h ↦ ⟨x.num, (Rat.intCast_num_of_den_eq_one h).symm⟩, fun ⟨a, ha⟩ ↦ ha ▸ rfl⟩

/-- **Check.** `Q_⊤ = ℚ`. -/
theorem ratSubgroup_top : ratSubgroup ⊤ = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_ratSubgroup_iff.2 le_top

/-- **Check.** `Q_(ofNat n) = (1/n) ℤ`: a rational lies in it exactly when `n x` is an integer. -/
theorem mem_ratSubgroup_ofNat_iff (n : ℕ+) {x : ℚ} :
    x ∈ ratSubgroup (ofNat n) ↔ ∃ a : ℤ, x = a / n := by
  rw [mem_ratSubgroup_iff_exists]
  refine ⟨fun ⟨a, b, hb, hx⟩ ↦ ?_, fun ⟨a, hx⟩ ↦ ⟨a, n, le_rfl, hx⟩⟩
  obtain ⟨c, hc⟩ := ofNat_le_ofNat_iff.1 hb
  refine ⟨a * c, ?_⟩
  rw [hx, hc, PNat.mul_coe, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  have hc0 : ((c : ℕ) : ℚ) ≠ 0 := by simp
  rw [mul_div_mul_right _ _ hc0]

/-- **Check.** `Q_(p^∞) = ℤ[1/p]`: a rational lies in it exactly when it is `a / pᵏ`. -/
theorem mem_ratSubgroup_primePower_top_iff (p : Nat.Primes) {x : ℚ} :
    x ∈ ratSubgroup (primePower p ⊤) ↔ ∃ (a : ℤ) (k : ℕ), x = a / (p : ℕ) ^ k := by
  rw [mem_ratSubgroup_iff_exists]
  refine ⟨fun ⟨a, b, hb, hx⟩ ↦ ?_, fun ⟨a, k, hx⟩ ↦ ⟨a, ⟨(p : ℕ) ^ k, pow_pos p.prop.pos k⟩,
    by rw [ofNat_prime_pow, primePower_le_primePower_iff]; exact le_top, by simpa using hx⟩⟩
  -- Every prime factor of `b` is `p`, so `b = p ^ v_p(b)`.
  have hfac : (b : ℕ).factorization =
      Finsupp.single (p : ℕ) ((b : ℕ).factorization (p : ℕ)) := by
    ext q
    by_cases hq : q = (p : ℕ)
    · rw [hq, Finsupp.single_eq_same]
    · simp only [Finsupp.single_apply, Ne.symm hq, ite_false]
      by_cases hq' : q.Prime
      · have h := (ofNat_apply_eq_factorization b ⟨q, hq'⟩).symm.trans_le
          ((le_iff.1 hb) ⟨q, hq'⟩)
        have hne : (⟨q, hq'⟩ : Nat.Primes) ≠ p := fun h ↦ hq (congrArg Subtype.val h)
        exact_mod_cast nonpos_iff_eq_zero.1 (h.trans_eq (primePower_apply_of_ne hne ⊤))
      · exact Nat.factorization_eq_zero_of_not_prime _ hq'
  have hb' : (b : ℕ) = (p : ℕ) ^ (b : ℕ).factorization p :=
    Nat.eq_pow_of_factorization_eq_single b.ne_zero hfac
  exact ⟨a, (b : ℕ).factorization p, by rw [hx, ← Nat.cast_pow, ← hb']⟩

/-- The supernatural invariant of a sequence of matrix sizes: the supremum, in the divisibility
order, of the sizes. -/
noncomputable def supernaturalOfSizes (d : ℕ → ℕ+) : Supernatural :=
  ⨆ n, ofNat (d n)

/-- **Check.** Constant sizes `d` have invariant `ofNat d`. -/
theorem supernaturalOfSizes_const (d : ℕ+) : supernaturalOfSizes (fun _ ↦ d) = ofNat d :=
  iSup_const

/-- **Check.** Sizes `pⁿ` have invariant `p^∞`. -/
theorem supernaturalOfSizes_prime_pow (p : Nat.Primes) :
    supernaturalOfSizes (fun n ↦ ⟨(p : ℕ) ^ n, pow_pos p.prop.pos n⟩) = primePower p ⊤ := by
  simp only [supernaturalOfSizes, ofNat_prime_pow]
  ext q
  rw [iSup_apply]
  by_cases hq : q = p
  · subst hq
    simp only [primePower_apply_self]
    exact ENat.iSup_natCast_eq_top.2 (fun ⟨b, hb⟩ ↦ by
      have := hb ⟨b + 1, rfl⟩
      simp at this)
  · simp [primePower_apply_of_ne hq]

/-- **Check.** Sizes `n!` have invariant `⊤`, the invariant of the universal UHF algebra. -/
theorem supernaturalOfSizes_factorial :
    supernaturalOfSizes (fun n ↦ ⟨n.factorial, n.factorial_pos⟩) = ⊤ := by
  unfold supernaturalOfSizes
  refine eq_top_iff.2 (le_iff.2 fun p ↦ ?_)
  rw [top_apply, iSup_apply]
  -- `p ^ k ∣ (p ^ k)!`, so the exponent of `p` in `(p ^ k)!` is at least `k`.
  refine ENat.forall_natCast_le_iff_le.1 fun k _ ↦ le_iSup_of_le ((p : ℕ) ^ k) ?_
  have h : ofNat ⟨(p : ℕ) ^ k, pow_pos p.prop.pos k⟩ ≤
      ofNat ⟨((p : ℕ) ^ k).factorial, Nat.factorial_pos _⟩ :=
    ofNat_le_ofNat_iff.2 (PNat.dvd_iff.2 (Nat.dvd_factorial (pow_pos p.prop.pos k) le_rfl))
  rw [ofNat_prime_pow, primePower_le_iff] at h
  exact h

end Supernatural

end TauCeti
