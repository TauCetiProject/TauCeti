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
# Torsion modules over `ℤ[1/p]`

Let `p` be a prime and let `T` be a finitely generated module over
`ℤ[1/p] = Localization.Away p` which is killed by a nonzero element of `ℤ[1/p]`. Clearing
denominators and the powers of `p`, which act invertibly, `T` is killed by an integer `m` coprime
to `p`. Since `p` is invertible modulo `m`, every element of `ℤ[1/p]` acts on `T` as an integer, so
`T` is finitely generated as an abelian group. A finitely generated abelian group killed by `m` is
finite, and its order is coprime to `p`, since by Cauchy's theorem a group of order divisible by
`p` has an element of order `p`.

These are the torsion summands in the structure theorem for finitely generated `ℤ[1/p]`-modules;
their order being prime to `p` is what makes them invisible to homology with coefficients in which
`p = 0`.

## Main results

* `TauCeti.LocalizationAway.exists_coprime_smul_eq_zero`: such a module is killed by a natural
  number coprime to `p`.
* `TauCeti.LocalizationAway.finite_of_smul_eq_zero`: such a module is finite.
* `TauCeti.LocalizationAway.coprime_natCard_of_smul_eq_zero`: its order is coprime to `p`.
-/

public section

namespace TauCeti.LocalizationAway

variable {p : ℕ} {T : Type*} [AddCommGroup T] [Module (Localization.Away (p : ℤ)) T]

/-- A `ℤ[1/p]`-module killed by a nonzero element of `ℤ[1/p]` is killed by a natural number
coprime to `p`. -/
theorem exists_coprime_smul_eq_zero (hp : p.Prime) {x : Localization.Away (p : ℤ)} (hx : x ≠ 0)
    (hT : ∀ t : T, x • t = 0) : ∃ m : ℕ, p.Coprime m ∧ ∀ t : T, m • t = 0 := by
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (Submonoid.powers (p : ℤ)) x
  have hs : IsUnit (algebraMap ℤ (Localization.Away (p : ℤ)) s) :=
    IsLocalization.map_units _ s
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero, hs.mul_left_eq_zero] at hbs
    exact hx hbs
  obtain ⟨k, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hb) p hp.ne_one
  refine ⟨m, hp.coprime_iff_not_dvd.2 hm, fun t ↦ ?_⟩
  have hbt : b.natAbs • t = 0 := by
    rw [natAbs_nsmul_eq_zero, ← Int.cast_smul_eq_zsmul (Localization.Away (p : ℤ)),
      ← eq_intCast (algebraMap ℤ (Localization.Away (p : ℤ))), ← hbs]
    simp [mul_comm x, mul_smul, hT]
  -- `pᵏ m` kills `t`, and `pᵏ` acts invertibly.
  have hpk : IsUnit ((p ^ k : ℕ) : Localization.Away (p : ℤ)) := by
    simpa using
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : ℤ)) (p : ℤ)).pow k
  rw [← hpk.smul_eq_zero, Nat.cast_smul_eq_nsmul, smul_smul, ← hbm, hbt]

/-- On a `ℤ[1/p]`-module killed by a number coprime to `p`, every element of `ℤ[1/p]` acts as an
integer. -/
theorem exists_int_smul_eq_smul {m : ℕ} (hm : p.Coprime m) (hT : ∀ t : T, m • t = 0)
    (r : Localization.Away (p : ℤ)) : ∃ z : ℤ, ∀ t : T, r • t = z • t := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : ℤ)) r
  dsimp only
  obtain ⟨l, hl⟩ := s.2
  have hr := IsLocalization.mk'_spec (Localization.Away (p : ℤ)) b s
  rw [← hl] at hr
  simp only [eq_intCast, Int.cast_pow, Int.cast_natCast] at hr
  generalize IsLocalization.mk' (Localization.Away (p : ℤ)) b s = r at hr ⊢
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hm).pow_left (m := l)
  refine ⟨b * u, fun t ↦ ?_⟩
  -- `r = r (u pˡ + v m) = b u + r v m`, and `m` kills `t`.
  have h1 : ((u * (p : ℤ) ^ l + v * m : ℤ) : Localization.Away (p : ℤ)) = 1 := by
    rw [huv, Int.cast_one]
  push_cast at h1
  have key : r = ((b * u : ℤ) : Localization.Away (p : ℤ)) + r * v * (m : ℕ) := by
    push_cast
    linear_combination (-r) * h1 + u * hr
  rw [key, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, hT]
  simpa using Int.cast_smul_eq_zsmul (Localization.Away (p : ℤ)) (b * u) t

/-- A finitely generated `ℤ[1/p]`-module killed by a number coprime to `p` is finitely generated
as an abelian group. -/
theorem finite_int_of_coprime_smul_eq_zero [Module.Finite (Localization.Away (p : ℤ)) T] {m : ℕ}
    (hm : p.Coprime m) (hT : ∀ t : T, m • t = 0) : Module.Finite ℤ T := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Localization.Away (p : ℤ)) (M := T)
  refine ⟨⟨s, eq_top_iff.2 fun t _ ↦ ?_⟩⟩
  -- The integer span of the generators is stable under `ℤ[1/p]`, so it is everything.
  let N : Submodule (Localization.Away (p : ℤ)) T :=
    { carrier := Submodule.span ℤ (s : Set T)
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun r t ht ↦ by
        obtain ⟨z, hz⟩ := exists_int_smul_eq_smul hm hT r
        rw [hz]
        exact Submodule.smul_mem _ z ht }
  have : Submodule.span (Localization.Away (p : ℤ)) (s : Set T) ≤ N :=
    Submodule.span_le.2 Submodule.subset_span
  exact this (hs ▸ Submodule.mem_top)

/-- A finitely generated `ℤ[1/p]`-module killed by a nonzero element of `ℤ[1/p]` is finite. -/
theorem finite_of_smul_eq_zero [Module.Finite (Localization.Away (p : ℤ)) T] (hp : p.Prime)
    {x : Localization.Away (p : ℤ)} (hx : x ≠ 0) (hT : ∀ t : T, x • t = 0) : Finite T := by
  obtain ⟨m, hm, hmT⟩ := exists_coprime_smul_eq_zero hp hx hT
  have := finite_int_of_coprime_smul_eq_zero hm hmT
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hp.ne_one (Nat.coprime_zero_right _ |>.1 hm)
  exact Module.finite_of_fg_torsion T fun t ↦
    ⟨⟨m, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm0)⟩, by
      rw [Submonoid.smul_def, natCast_zsmul, hmT t]⟩

/-- A finitely generated `ℤ[1/p]`-module killed by a nonzero element of `ℤ[1/p]` has order
coprime to `p`. -/
theorem coprime_natCard_of_smul_eq_zero [Module.Finite (Localization.Away (p : ℤ)) T]
    (hp : p.Prime) {x : Localization.Away (p : ℤ)} (hx : x ≠ 0) (hT : ∀ t : T, x • t = 0) :
    p.Coprime (Nat.card T) := by
  obtain ⟨m, hm, hmT⟩ := exists_coprime_smul_eq_zero hp hx hT
  have := finite_of_smul_eq_zero hp hx hT
  have := Fintype.ofFinite T
  have := Fact.mk hp
  rw [hp.coprime_iff_not_dvd, Nat.card_eq_fintype_card]
  intro hpT
  obtain ⟨t, ht⟩ := exists_prime_addOrderOf_dvd_card p hpT
  exact hp.coprime_iff_not_dvd.1 hm (ht ▸ addOrderOf_dvd_of_nsmul_eq_zero (hmT t))

end TauCeti.LocalizationAway
