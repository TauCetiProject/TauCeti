/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Torsion modules over `ℤ[1/2]`

Let `T` be a finitely generated module over `ℤ[1/2] = Localization.Away 2` which is killed by a
nonzero element of `ℤ[1/2]`. Clearing denominators and the powers of two, which act invertibly,
`T` is killed by an odd integer `m`. Since `2` is invertible modulo `m`, every element of
`ℤ[1/2]` acts on `T` as an integer, so `T` is finitely generated as an abelian group. A finitely
generated abelian group killed by `m` is finite, and its order is odd, since by Cauchy's theorem a
group of even order has an element of order two.

These are the torsion summands in the structure theorem for finitely generated `ℤ[1/2]`-modules;
their oddness is what makes them invisible to homology with coefficients in which `2 = 0`.

## Main results

* `TauCeti.LocalizationAwayTwo.exists_odd_smul_eq_zero`: such a module is killed by an odd
  natural number.
* `TauCeti.LocalizationAwayTwo.finite_of_smul_eq_zero`: such a module is finite.
* `TauCeti.LocalizationAwayTwo.odd_natCard_of_smul_eq_zero`: its order is odd.
-/

public section

namespace TauCeti.LocalizationAwayTwo

variable {T : Type*} [AddCommGroup T] [Module (Localization.Away (2 : ℤ)) T]

/-- A `ℤ[1/2]`-module killed by a nonzero element of `ℤ[1/2]` is killed by an odd natural
number. -/
theorem exists_odd_smul_eq_zero {x : Localization.Away (2 : ℤ)} (hx : x ≠ 0)
    (hT : ∀ t : T, x • t = 0) : ∃ m : ℕ, Odd m ∧ ∀ t : T, m • t = 0 := by
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (Submonoid.powers (2 : ℤ)) x
  have hs : IsUnit (algebraMap ℤ (Localization.Away (2 : ℤ)) s) :=
    IsLocalization.map_units _ s
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero, hs.mul_left_eq_zero] at hbs
    exact hx hbs
  obtain ⟨k, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.2 hb)
  refine ⟨m, hm, fun t ↦ ?_⟩
  have hbt : b • t = 0 := by
    rw [← Int.cast_smul_eq_zsmul (Localization.Away (2 : ℤ)),
      ← eq_intCast (algebraMap ℤ (Localization.Away (2 : ℤ))), ← hbs, mul_comm, mul_smul, hT,
      smul_zero]
  have habs : b.natAbs • t = 0 := by
    rcases Int.natAbs_eq b with h | h
    · rw [← natCast_zsmul, ← h, hbt]
    · rw [← natCast_zsmul, show (b.natAbs : ℤ) = -b by omega, neg_zsmul, hbt, neg_zero]
  -- `2ᵏ m` kills `t`, and `2ᵏ` acts invertibly.
  have h2 : IsUnit ((2 ^ k : ℕ) : Localization.Away (2 : ℤ)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (2 : ℤ)) (2 : ℤ)
    rw [map_ofNat] at this
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact this.pow k
  rw [← h2.smul_eq_zero, Nat.cast_smul_eq_nsmul, smul_smul, ← hbm, habs]

/-- On a `ℤ[1/2]`-module killed by an odd number, every element of `ℤ[1/2]` acts as an integer. -/
theorem exists_int_smul_eq_smul {m : ℕ} (hm : Odd m) (hT : ∀ t : T, m • t = 0)
    (r : Localization.Away (2 : ℤ)) : ∃ z : ℤ, ∀ t : T, r • t = z • t := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (2 : ℤ)) r
  dsimp only
  obtain ⟨l, hl⟩ := s.2
  have hr := IsLocalization.mk'_spec (Localization.Away (2 : ℤ)) b s
  rw [← hl] at hr
  simp only [eq_intCast, Int.cast_pow, Int.cast_ofNat] at hr
  generalize IsLocalization.mk' (Localization.Away (2 : ℤ)) b s = r at hr ⊢
  have h2m : IsCoprime (2 : ℤ) m := by
    exact_mod_cast Nat.isCoprime_iff_coprime.2 (Nat.coprime_two_left.2 hm)
  obtain ⟨u, v, huv⟩ := h2m.pow_left (m := l)
  refine ⟨b * u, fun t ↦ ?_⟩
  -- `r = r (u 2ˡ + v m) = b u + r v m`, and `m` kills `t`.
  have h1 : ((u * 2 ^ l + v * m : ℤ) : Localization.Away (2 : ℤ)) = 1 := by
    rw [huv, Int.cast_one]
  push_cast at h1
  have key : r = ((b * u : ℤ) : Localization.Away (2 : ℤ)) + r * v * (m : ℕ) := by
    push_cast
    linear_combination (-r) * h1 + u * hr
  rw [key, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, hT, smul_zero, add_zero,
    Int.cast_smul_eq_zsmul]

/-- A finitely generated `ℤ[1/2]`-module killed by an odd number is finitely generated as an
abelian group. -/
theorem finite_int_of_odd_smul_eq_zero [Module.Finite (Localization.Away (2 : ℤ)) T] {m : ℕ}
    (hm : Odd m) (hT : ∀ t : T, m • t = 0) : Module.Finite ℤ T := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Localization.Away (2 : ℤ)) (M := T)
  refine ⟨⟨s, eq_top_iff.2 fun t _ ↦ ?_⟩⟩
  -- The integer span of the generators is stable under `ℤ[1/2]`, so it is everything.
  let N : Submodule (Localization.Away (2 : ℤ)) T :=
    { carrier := Submodule.span ℤ (s : Set T)
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun r t ht ↦ by
        obtain ⟨z, hz⟩ := exists_int_smul_eq_smul hm hT r
        rw [hz]
        exact Submodule.smul_mem _ z ht }
  have : Submodule.span (Localization.Away (2 : ℤ)) (s : Set T) ≤ N :=
    Submodule.span_le.2 Submodule.subset_span
  exact this (hs ▸ Submodule.mem_top)

/-- A finitely generated `ℤ[1/2]`-module killed by a nonzero element of `ℤ[1/2]` is finite. -/
theorem finite_of_smul_eq_zero [Module.Finite (Localization.Away (2 : ℤ)) T]
    {x : Localization.Away (2 : ℤ)} (hx : x ≠ 0) (hT : ∀ t : T, x • t = 0) : Finite T := by
  obtain ⟨m, hm, hmT⟩ := exists_odd_smul_eq_zero hx hT
  have := finite_int_of_odd_smul_eq_zero hm hmT
  exact Module.finite_of_fg_torsion T fun t ↦
    ⟨⟨m, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm.pos.ne')⟩, by
      rw [Submonoid.smul_def, natCast_zsmul, hmT t]⟩

/-- A finitely generated `ℤ[1/2]`-module killed by a nonzero element of `ℤ[1/2]` has odd
order. -/
theorem odd_natCard_of_smul_eq_zero [Module.Finite (Localization.Away (2 : ℤ)) T]
    {x : Localization.Away (2 : ℤ)} (hx : x ≠ 0) (hT : ∀ t : T, x • t = 0) :
    Odd (Nat.card T) := by
  obtain ⟨m, hm, hmT⟩ := exists_odd_smul_eq_zero hx hT
  have := finite_of_smul_eq_zero hx hT
  have := Fintype.ofFinite T
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd, Nat.card_eq_fintype_card]
  intro h2
  have := Fact.mk Nat.prime_two
  obtain ⟨t, ht⟩ := exists_prime_addOrderOf_dvd_card 2 h2
  have := addOrderOf_dvd_of_nsmul_eq_zero (hmT t)
  rw [ht] at this
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)

end TauCeti.LocalizationAwayTwo
