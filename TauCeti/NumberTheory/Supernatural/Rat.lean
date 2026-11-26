/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Rat.Lemmas
public import TauCeti.NumberTheory.Supernatural
import TauCeti.Data.Rat.NumDenDvd

/-!
# The rational subgroup of a supernatural number

For a supernatural number `ν`, let `Q_ν` be the set of rationals `a / b` with `a ∈ ℤ`, `b ∈ ℕ+`
and `b ∣ ν`, that is `ofNat b ≤ ν`. Equivalently, `Q_ν` consists of the rationals whose reduced
denominator divides `ν`. It is an additive subgroup of `ℚ`, since the denominator of a sum
divides the lcm of the denominators; it contains `ℤ = Q_1`, grows with `ν`, and determines `ν`:
`Q_ν ≤ Q_μ` exactly when `ν ≤ μ`.

For a UHF algebra with supernatural invariant `ν`, the ordered `K₀`-group with its unit is
`(Q_ν, Q_ν ∩ ℚ≥0, 1)` (Glimm's classification). This file records the number-theoretic side.

## Main definitions

* `TauCeti.Supernatural.ratSubgroup ν`: the additive subgroup `Q_ν` of `ℚ`.

## Main statements

* `TauCeti.Supernatural.mem_ratSubgroup_iff_exists`: `Q_ν` consists of the `a / b` with
  `ofNat b ≤ ν`.
* `TauCeti.Supernatural.ratSubgroup_le_ratSubgroup_iff`: `Q_ν ≤ Q_μ ↔ ν ≤ μ`; in particular
  `ratSubgroup` is injective (`ratSubgroup_injective`).
* `TauCeti.Supernatural.mem_ratSubgroup_one_iff`, `ratSubgroup_top`, `mem_ratSubgroup_ofNat_iff`,
  `mem_ratSubgroup_primePower_top_iff`: `Q_1 = ℤ`, `Q_⊤ = ℚ`, `Q_(ofNat n) = (1/n) ℤ` and
  `Q_(p^∞) = ℤ[1/p]`.

## References

* J. G. Glimm, *On a certain class of operator algebras*, Trans. Amer. Math. Soc. 95 (1960),
  318–340.
-/

public section

namespace TauCeti

namespace Supernatural

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
@[simp]
theorem mem_ratSubgroup_iff {x : ℚ} : x ∈ ratSubgroup ν ↔ ofNat x.pnatDen ≤ ν :=
  Iff.rfl

/-- `Q_ν` grows with `ν`. -/
theorem ratSubgroup_mono : Monotone ratSubgroup :=
  fun _ _ h _ hx ↦ (mem_ratSubgroup_iff.1 hx).trans h

/-- **Check.** `Q_(ofNat n) = (1/n) ℤ`: a rational lies in it exactly when `n x` is an integer. -/
theorem mem_ratSubgroup_ofNat_iff (n : ℕ+) {x : ℚ} :
    x ∈ ratSubgroup (ofNat n) ↔ ∃ a : ℤ, x = a / n := by
  rw [mem_ratSubgroup_iff, ofNat_le_ofNat_iff, PNat.dvd_iff, Rat.coe_pnatDen,
    Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero]

/-- `Q_ν` consists of the rationals `a / b` with `a ∈ ℤ`, `b ∈ ℕ+` and `ofNat b ≤ ν`. -/
theorem mem_ratSubgroup_iff_exists {x : ℚ} :
    x ∈ ratSubgroup ν ↔ ∃ (a : ℤ) (b : ℕ+), ofNat b ≤ ν ∧ x = a / b := by
  refine ⟨fun hx ↦ ⟨x.num, x.pnatDen, hx, ?_⟩, ?_⟩
  · rw [Rat.coe_pnatDen, Rat.num_div_den]
  · rintro ⟨a, b, hb, rfl⟩
    exact ratSubgroup_mono hb ((mem_ratSubgroup_ofNat_iff b).2 ⟨a, rfl⟩)

/-- `1 / b` lies in `Q_ν` exactly when `ofNat b ≤ ν`. -/
theorem inv_mem_ratSubgroup_iff (b : ℕ+) : ((b : ℚ))⁻¹ ∈ ratSubgroup ν ↔ ofNat b ≤ ν := by
  have h : ((b : ℚ))⁻¹.pnatDen = b := by
    rw [Rat.pnatDen_eq_iff_den_eq, Rat.inv_natCast_den]
    simp
  rw [mem_ratSubgroup_iff, h]

/-- **`Q_ν` determines `ν`.** `Q_ν ≤ Q_μ` exactly when `ν ≤ μ`. -/
@[simp]
theorem ratSubgroup_le_ratSubgroup_iff : ratSubgroup ν ≤ ratSubgroup μ ↔ ν ≤ μ := by
  refine ⟨fun h ↦ le_iff.2 fun p ↦ ?_, fun h ↦ ratSubgroup_mono h⟩
  by_contra hlt
  rw [not_le] at hlt
  -- `μ p = k` is finite and `p ^ (k + 1) ∣ ν`, but `p ^ (k + 1) ∤ μ`.
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hlt.trans_le le_top).ne
  have hν : ofNat ((p : ℕ+) ^ (k + 1)) ≤ ν := by
    rw [ofNat_prime_pow_le_iff, Nat.cast_add, Nat.cast_one, hk]
    exact Order.add_one_le_of_lt (hk ▸ hlt)
  have hμ := (inv_mem_ratSubgroup_iff _).1 (h ((inv_mem_ratSubgroup_iff _).2 hν))
  rw [ofNat_prime_pow_le_iff, ← hk, Nat.cast_le] at hμ
  omega

/-- `ratSubgroup` is injective: `Q_ν` determines `ν`. -/
theorem ratSubgroup_injective : Function.Injective ratSubgroup := fun _ _ h ↦
  le_antisymm (ratSubgroup_le_ratSubgroup_iff.1 h.le) (ratSubgroup_le_ratSubgroup_iff.1 h.ge)

/-- `Q_ν = Q_μ` exactly when `ν = μ`. -/
@[simp]
theorem ratSubgroup_inj : ratSubgroup ν = ratSubgroup μ ↔ ν = μ :=
  ratSubgroup_injective.eq_iff

/-- `Q_1 = ℤ`. -/
theorem mem_ratSubgroup_one_iff {x : ℚ} : x ∈ ratSubgroup 1 ↔ ∃ a : ℤ, x = a := by
  simpa [-mem_ratSubgroup_iff] using mem_ratSubgroup_ofNat_iff 1 (x := x)

/-- Every integer lies in `Q_ν`; in particular the unit `1` of the `K₀`-group does. -/
theorem intCast_mem_ratSubgroup (a : ℤ) : (a : ℚ) ∈ ratSubgroup ν :=
  ratSubgroup_mono (one_eq_bot ▸ bot_le) (mem_ratSubgroup_one_iff.2 ⟨a, rfl⟩)

/-- **Check.** `Q_⊤ = ℚ`. -/
@[simp]
theorem ratSubgroup_top : ratSubgroup ⊤ = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_ratSubgroup_iff.2 le_top

/-- **Check.** `Q_(p^∞) = ℤ[1/p]`: a rational lies in it exactly when it is `a / pᵏ`. -/
theorem mem_ratSubgroup_primePower_top_iff (p : Nat.Primes) {x : ℚ} :
    x ∈ ratSubgroup (primePower p ⊤) ↔ ∃ (a : ℤ) (k : ℕ), x = a / (p : ℕ) ^ k := by
  rw [mem_ratSubgroup_iff_exists]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    obtain ⟨k, hk⟩ := ofNat_le_primePower_top_iff.1 hb
    exact ⟨a, k, by rw [hk, Nat.cast_pow]⟩
  · rintro ⟨a, k, rfl⟩
    exact ⟨a, (p : ℕ+) ^ k, ofNat_le_primePower_top_iff.2
      ⟨k, by rw [PNat.pow_coe, Nat.Primes.coe_pnat_nat]⟩,
      by simp [Nat.Primes.coe_pnat_nat]⟩

end Supernatural

end TauCeti
