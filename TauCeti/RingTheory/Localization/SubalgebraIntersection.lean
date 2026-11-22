/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import TauCeti.RingTheory.Localization.DenIdeal

/-!
# Intersections of embedded principal localizations

Principal localizations at a family generating the unit ideal intersect in the coefficient ring,
when all are realized inside its total quotient ring. Coefficients may have zero divisors and
the family need not be finite. Membership in each localization puts a power of its denominator
in the existing denominator ideal; the unit-ideal hypothesis then forces that ideal to contain
one. The localizations are Mathlib's actual `Localization.subalgebra` objects.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §5, for denominator patching in a common ambient ring.
-/

public section

open scoped nonZeroDivisors

namespace Localization.subalgebra

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- Membership in the embedded localization is equivalent to a denominator from its monoid
lying in the denominator ideal. This holds in total quotient rings with zero divisors. -/
theorem mem_iff_exists_mem_denIdeal (S : Submonoid R) (hS : S ≤ R⁰) (x : K) :
    x ∈ Localization.subalgebra K S hS ↔ ∃ s ∈ S, s ∈ Algebra.denIdeal K x := by
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    exact ⟨s, hs, (Algebra.mem_denIdeal_iff K).mpr
      ⟨a, IsLocalization.mk'_spec' K a ⟨s, hS hs⟩⟩⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨a, ha⟩ := (Algebra.mem_denIdeal_iff K).mp hx
    refine ⟨a, s, hs, ?_⟩
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    simpa only [mul_comm] using ha

/-- Membership in an embedded principal localization is detected by a power in the
existing denominator ideal. -/
theorem mem_powers_iff_exists_pow_mem_denIdeal (a : R) (ha : a ∈ R⁰) (x : K) :
    x ∈ Localization.subalgebra K (Submonoid.powers a) (Submonoid.powers_le.mpr ha) ↔
      ∃ n : ℕ, a ^ n ∈ Algebra.denIdeal K x := by
  rw [mem_iff_exists_mem_denIdeal]
  simp only [Submonoid.mem_powers_iff, exists_exists_eq_and]

/-- Principal localizations whose denominators generate the unit ideal intersect in the
coefficient ring inside any total quotient ring, including for infinite families. -/
theorem iInf_powers_eq_bot {ι : Type*} (a : ι → R) (ha : ∀ i, a i ∈ R⁰)
    (hcover : Ideal.span (Set.range a) = ⊤) :
    (⨅ i, Localization.subalgebra K (Submonoid.powers (a i))
      (Submonoid.powers_le.mpr (ha i))) = (⊥ : Subalgebra R K) := by
  apply le_antisymm
  · intro x hx
    have hI : Ideal.span (Set.range a) ≤ (Algebra.denIdeal K x).radical := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_radical_iff.mpr
        ((mem_powers_iff_exists_pow_mem_denIdeal (a i) (ha i) x).mp
          (Algebra.mem_iInf.mp hx i))
    rw [hcover] at hI
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hI (show (1 : R) ∈ (⊤ : Ideal R) from trivial))
    rw [one_pow] at hn
    obtain ⟨r, hr⟩ := (Algebra.mem_denIdeal_iff K).mp hn
    exact Algebra.mem_bot.mpr ⟨r, by simpa only [map_one, one_mul] using hr.symm⟩
  · exact bot_le

end Localization.subalgebra
