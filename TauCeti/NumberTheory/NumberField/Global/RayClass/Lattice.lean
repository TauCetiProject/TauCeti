/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus

/-!
# Greatest common divisors and least common multiples of moduli

The divisibility order on number-field moduli is componentwise: the finite ideal divides in the
usual ideal-theoretic sense, while the set of real places grows by inclusion.  This file constructs
the greatest common divisor and least common multiple for that order.  On finite parts these are
the sum and intersection of ideals, respectively; on infinite parts they are intersection and
union.

The least common multiple combines congruence conditions: an element of the field is congruent to
one modulo `lcm 𝔪 𝔫` exactly when it is congruent to one modulo both `𝔪` and `𝔫`.  This is the
form used when several ray conditions are replaced by one modulus.  The support and exponent
formulas record that finite prime exponents combine by `min` for `gcd` and by `max` for `lcm`.

## Main definitions

* `TauCeti.GlobalNumberFields.Modulus.gcd`: the greatest common divisor of two moduli.
* `TauCeti.GlobalNumberFields.Modulus.lcm`: the least common multiple of two moduli.

## Main results

* `Modulus.gcd_dvd_left`, `Modulus.gcd_dvd_right`, and `Modulus.dvd_gcd`: the universal property
  of `gcd`.
* `Modulus.dvd_lcm_left`, `Modulus.dvd_lcm_right`, and `Modulus.lcm_dvd`: the universal property
  of `lcm`.
* `Modulus.support_gcd`, `Modulus.support_lcm`, `Modulus.exponent_gcd`, and
  `Modulus.exponent_lcm`: the primewise formulas.
* `isCongrOne_lcm_iff` and `congruenceSubgroup_lcm`: an `lcm` imposes both congruence conditions.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

noncomputable local instance : DecidableEq {w : InfinitePlace K // w.IsReal} := Classical.decEq _
noncomputable local instance : DecidableEq (HeightOneSpectrum (RingOfIntegers K)) :=
  Classical.decEq _

namespace Modulus

/-! ### Definitions and universal properties -/

/-- The **greatest common divisor of two moduli**.  Its finite part is the sum of the two finite
ideals and its infinite part contains the real places common to both moduli. -/
noncomputable def gcd (m n : Modulus K) : Modulus K where
  finitePart := m.finitePart ⊔ n.finitePart
  finitePart_ne_bot := ne_bot_of_le_ne_bot m.finitePart_ne_bot le_sup_left
  infinitePart := by
    classical exact m.infinitePart ∩ n.infinitePart

/-- The **least common multiple of two moduli**.  Its finite part is the intersection of the two
finite ideals and its infinite part contains every real place occurring in either modulus. -/
noncomputable def lcm (m n : Modulus K) : Modulus K where
  finitePart := m.finitePart ⊓ n.finitePart
  finitePart_ne_bot := Ideal.inf_ne_bot_of_ne_bot m.finitePart_ne_bot n.finitePart_ne_bot
  infinitePart := by
    classical exact m.infinitePart ∪ n.infinitePart

@[simp] theorem gcd_finitePart (m n : Modulus K) :
    (gcd m n).finitePart = m.finitePart ⊔ n.finitePart :=
  by rw [gcd]

@[simp] theorem gcd_infinitePart (m n : Modulus K) :
    (gcd m n).infinitePart = m.infinitePart ∩ n.infinitePart :=
  by classical rw [gcd]

@[simp] theorem lcm_finitePart (m n : Modulus K) :
    (lcm m n).finitePart = m.finitePart ⊓ n.finitePart :=
  by rw [lcm]

@[simp] theorem lcm_infinitePart (m n : Modulus K) :
    (lcm m n).infinitePart = m.infinitePart ∪ n.infinitePart :=
  by classical rw [lcm]

/-- The greatest common divisor divides its left argument. -/
theorem gcd_dvd_left (m n : Modulus K) : gcd m n ∣ m := by
  classical
  exact dvd_iff.mpr ⟨Ideal.dvd_iff_le.mpr le_sup_left, Finset.inter_subset_left⟩

/-- The greatest common divisor divides its right argument. -/
theorem gcd_dvd_right (m n : Modulus K) : gcd m n ∣ n := by
  classical
  exact dvd_iff.mpr ⟨Ideal.dvd_iff_le.mpr le_sup_right, Finset.inter_subset_right⟩

/-- A modulus dividing both arguments divides their greatest common divisor. -/
theorem dvd_gcd {m n p : Modulus K} (hm : p ∣ m) (hn : p ∣ n) : p ∣ gcd m n := by
  classical
  exact dvd_iff.mpr ⟨Ideal.dvd_iff_le.mpr <| sup_le
      (Ideal.le_of_dvd (dvd_iff.mp hm).1) (Ideal.le_of_dvd (dvd_iff.mp hn).1),
    Finset.subset_inter (dvd_iff.mp hm).2 (dvd_iff.mp hn).2⟩

/-- A modulus divides a greatest common divisor exactly when it divides both arguments. -/
@[simp] theorem dvd_gcd_iff {m n p : Modulus K} : p ∣ gcd m n ↔ p ∣ m ∧ p ∣ n :=
  ⟨fun h ↦ ⟨dvd_trans h (gcd_dvd_left m n), dvd_trans h (gcd_dvd_right m n)⟩,
    fun h ↦ dvd_gcd h.1 h.2⟩

/-- The least common multiple is divisible by its left argument. -/
theorem dvd_lcm_left (m n : Modulus K) : m ∣ lcm m n := by
  classical
  exact dvd_iff.mpr ⟨Ideal.dvd_iff_le.mpr inf_le_left, Finset.subset_union_left⟩

/-- The least common multiple is divisible by its right argument. -/
theorem dvd_lcm_right (m n : Modulus K) : n ∣ lcm m n := by
  classical
  exact dvd_iff.mpr ⟨Ideal.dvd_iff_le.mpr inf_le_right, Finset.subset_union_right⟩

/-- The least common multiple divides every common multiple. -/
theorem lcm_dvd {m n p : Modulus K} (hm : m ∣ p) (hn : n ∣ p) : lcm m n ∣ p := by
  classical
  exact dvd_iff.mpr ⟨Ideal.dvd_iff_le.mpr <| le_inf
      (Ideal.le_of_dvd (dvd_iff.mp hm).1) (Ideal.le_of_dvd (dvd_iff.mp hn).1),
    Finset.union_subset (dvd_iff.mp hm).2 (dvd_iff.mp hn).2⟩

/-- A least common multiple divides a modulus exactly when both arguments divide it. -/
@[simp] theorem lcm_dvd_iff {m n p : Modulus K} : lcm m n ∣ p ↔ m ∣ p ∧ n ∣ p :=
  ⟨fun h ↦ ⟨dvd_trans (dvd_lcm_left m n) h, dvd_trans (dvd_lcm_right m n) h⟩,
    fun h ↦ lcm_dvd h.1 h.2⟩

/-- Greatest common divisors of moduli are commutative. -/
theorem gcd_comm (m n : Modulus K) : gcd m n = gcd n m := by
  ext <;> simp [sup_comm, Finset.inter_comm]

/-- Greatest common divisors of moduli are associative. -/
theorem gcd_assoc (m n p : Modulus K) : gcd (gcd m n) p = gcd m (gcd n p) := by
  ext <;> simp [sup_assoc, Finset.inter_assoc]

/-- A modulus is its own greatest common divisor. -/
@[simp] theorem gcd_self (m : Modulus K) : gcd m m = m := by
  ext <;> simp

/-- Least common multiples of moduli are commutative. -/
theorem lcm_comm (m n : Modulus K) : lcm m n = lcm n m := by
  ext <;> simp [inf_comm, Finset.union_comm]

/-- Least common multiples of moduli are associative. -/
theorem lcm_assoc (m n p : Modulus K) : lcm (lcm m n) p = lcm m (lcm n p) := by
  ext <;> simp [inf_assoc, Finset.union_assoc]

/-- A modulus is its own least common multiple. -/
@[simp] theorem lcm_self (m : Modulus K) : lcm m m = m := by
  ext <;> simp

/-- The greatest common divisor with the trivial modulus is trivial. -/
@[simp] theorem gcd_one (m : Modulus K) : gcd m (one K) = one K := by
  ext <;> simp

/-- The greatest common divisor of the trivial modulus and any modulus is trivial. -/
@[simp] theorem one_gcd (m : Modulus K) : gcd (one K) m = one K := by
  rw [gcd_comm, gcd_one]

/-- The least common multiple with the trivial modulus is the original modulus. -/
@[simp] theorem lcm_one (m : Modulus K) : lcm m (one K) = m := by
  ext <;> simp

/-- The least common multiple of the trivial modulus and any modulus is the original modulus. -/
@[simp] theorem one_lcm (m : Modulus K) : lcm (one K) m = m := by
  rw [lcm_comm, lcm_one]

/-! ### Primewise formulas -/

/-- The finite support of a greatest common divisor is the intersection of the supports. -/
@[simp] theorem support_gcd (m n : Modulus K) :
    (gcd m n).support = m.support ∩ n.support := by
  classical
  ext v
  rw [mem_support_iff, gcd_finitePart, Finset.mem_inter, mem_support_iff, mem_support_iff,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, sup_le_iff]

/-- The finite support of a least common multiple is the union of the supports. -/
@[simp] theorem support_lcm (m n : Modulus K) :
    (lcm m n).support = m.support ∪ n.support := by
  classical
  ext v
  rw [mem_support_iff, lcm_finitePart, Finset.mem_union, mem_support_iff, mem_support_iff,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  exact v.isPrime.inf_le

/-- At every finite place, the exponent in a greatest common divisor is the minimum of the two
exponents. -/
@[simp] theorem exponent_gcd (m n : Modulus K) (v : HeightOneSpectrum (RingOfIntegers K)) :
    (gcd m n).exponent v = min (m.exponent v) (n.exponent v) := by
  apply le_antisymm
  · exact le_min (exponent_mono (gcd_dvd_left m n) v) (exponent_mono (gcd_dvd_right m n) v)
  · simp only [exponent_def]
    rw [le_count_associates_iff_le_pow v (gcd m n).finitePart_ne_bot]
    exact sup_le
      ((le_count_associates_iff_le_pow v m.finitePart_ne_bot _).mp (min_le_left _ _))
      ((le_count_associates_iff_le_pow v n.finitePart_ne_bot _).mp (min_le_right _ _))

/-- At every finite place, the exponent in a least common multiple is the maximum of the two
exponents. -/
@[simp] theorem exponent_lcm (m n : Modulus K) (v : HeightOneSpectrum (RingOfIntegers K)) :
    (lcm m n).exponent v = max (m.exponent v) (n.exponent v) := by
  have hmul : (gcd m n).finitePart * (lcm m n).finitePart = m.finitePart * n.finitePart :=
    Ideal.sup_mul_inf m.finitePart n.finitePart
  have hcount : (gcd m n).exponent v + (lcm m n).exponent v =
      m.exponent v + n.exponent v := by
    simp only [exponent_def]
    rw [← Associates.count_mul (Associates.mk_ne_zero.mpr (gcd m n).finitePart_ne_bot)
        (Associates.mk_ne_zero.mpr (lcm m n).finitePart_ne_bot) v.associates_irreducible,
      ← Associates.count_mul (Associates.mk_ne_zero.mpr m.finitePart_ne_bot)
        (Associates.mk_ne_zero.mpr n.finitePart_ne_bot) v.associates_irreducible,
      Associates.mk_mul_mk, Associates.mk_mul_mk, hmul]
  rw [exponent_gcd] at hcount
  omega

/-! ### Combining congruence conditions -/

/-- Congruence to one modulo a least common multiple is equivalent to congruence modulo both
arguments. -/
@[simp] theorem isCongrOne_lcm_iff {m n : Modulus K} {x : Kˣ} :
    IsCongrOne (lcm m n) x ↔ IsCongrOne m x ∧ IsCongrOne n x := by
  constructor
  · exact fun h ↦ ⟨h.mono (dvd_lcm_left m n), h.mono (dvd_lcm_right m n)⟩
  · rintro ⟨hm, hn⟩
    rw [isCongrOne_iff] at hm hn ⊢
    obtain ⟨hmf, hmi⟩ := hm
    obtain ⟨hnf, hni⟩ := hn
    refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · rw [exponent_lcm]
      have hv' : v ∈ m.support ∪ n.support := by
        rwa [← support_lcm, mem_support_iff]
      by_cases hmn : m.exponent v ≤ n.exponent v
      · rw [max_eq_right hmn]
        apply hnf v
        rw [← mem_support_iff]
        rcases Finset.mem_union.mp hv' with hvm | hvn
        · rw [mem_support_iff_exponent_ne_zero]
          have hmpos := exponent_pos_of_mem_support hvm
          omega
        · exact hvn
      · rw [max_eq_left (le_of_not_ge hmn)]
        apply hmf v
        rw [← mem_support_iff]
        rcases Finset.mem_union.mp hv' with hvm | hvn
        · exact hvm
        · rw [mem_support_iff_exponent_ne_zero]
          have hnpos := exponent_pos_of_mem_support hvn
          omega
    · rw [lcm_infinitePart, Finset.mem_union] at hw
      exact hw.elim (hmi w) (hni w)

end Modulus

/-- The congruence subgroup of a least common multiple is the intersection of the two congruence
subgroups. -/
@[simp] theorem congruenceSubgroup_lcm (m n : Modulus K) :
    congruenceSubgroup (Modulus.lcm m n) = congruenceSubgroup m ⊓ congruenceSubgroup n := by
  ext x
  rw [Subgroup.mem_inf, mem_congruenceSubgroup, mem_congruenceSubgroup, mem_congruenceSubgroup,
    Modulus.isCongrOne_lcm_iff]

end TauCeti.GlobalNumberFields
