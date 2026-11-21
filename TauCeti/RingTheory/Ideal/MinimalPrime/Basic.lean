/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Minimal primes, radicals and domains

The zero ideal is the unique minimal prime of an integral domain. Since the minimal primes over an
ideal `I` intersect in `I.radical` (`Ideal.sInf_minimalPrimes`), an element lies outside
`I.radical` if and only if it avoids some minimal prime over `I`. In particular, a reduced ring
embeds into the product of its quotients by its minimal primes. No finiteness of the set of
minimal primes is needed.

A reduced `P`-algebra `B` is torsion-free as soon as `P` maps injectively to `B ⧸ p` for every
minimal prime `p` of `B`: an element killed by a nonzero scalar vanishes on every irreducible
component of `Spec B`, so it is nilpotent.

## Main results

* `IsDomain.uniqueMinimalPrimes`: an integral domain has a unique minimal prime.
* `Ideal.injective_pi_quotient_mk_minimalPrimes`: a reduced ring embeds into the product of its
  quotients by its minimal primes.
* `Ideal.notMem_radical_iff_exists_mem_minimalPrimes_notMem`: an element lies outside `I.radical`
  if and only if some minimal prime over `I` does not contain it.
* `TauCeti.isTorsionFree_of_injective_algebraMap_quotient_minimalPrimes`: a reduced algebra whose
  components all receive `P` injectively is torsion-free over `P`.
-/

public section

/-- The zero ideal is the unique minimal prime of an integral domain. -/
instance IsDomain.uniqueMinimalPrimes (R : Type*) [CommSemiring R] [IsDomain R] :
    Unique (minimalPrimes R) where
  default := ⟨⊥, by simp [IsDomain.minimalPrimes_eq_singleton_bot]⟩
  uniq p := Subtype.ext <| by simpa [IsDomain.minimalPrimes_eq_singleton_bot] using p.property

namespace Ideal

/-- A reduced ring embeds into the product of its quotients by its minimal primes: the
intersection of the minimal primes is the nilradical, which is `0`. -/
theorem injective_pi_quotient_mk_minimalPrimes (A : Type*) [CommRing A] [IsReduced A] :
    Function.Injective (RingHom.pi fun p : minimalPrimes A ↦ Ideal.Quotient.mk p.val) := by
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_Pi_Quotient_mk, iInf_subtype, ← sInf_eq_iInf,
    minimalPrimes, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]

/-- An element lies outside the radical of an ideal `I` if and only if some minimal prime over `I`
does not contain it. -/
theorem notMem_radical_iff_exists_mem_minimalPrimes_notMem {A : Type*} [CommSemiring A]
    (I : Ideal A) {a : A} : a ∉ I.radical ↔ ∃ p ∈ I.minimalPrimes, a ∉ p := by
  simp only [← I.sInf_minimalPrimes, Ideal.mem_sInf, not_forall, exists_prop]

end Ideal

namespace TauCeti

/-- A reduced `P`-algebra `B` is torsion-free as soon as `P` maps injectively to `B ⧸ p` for every
minimal prime `p` of `B`: an element killed by a nonzero scalar vanishes on every irreducible
component of `Spec B`, so it is nilpotent. -/
theorem isTorsionFree_of_injective_algebraMap_quotient_minimalPrimes {P B : Type*} [CommRing P]
    [CommRing B] [Algebra P B] [IsReduced B]
    (h : ∀ p ∈ minimalPrimes B, Function.Injective (algebraMap P (B ⧸ p))) :
    Module.IsTorsionFree P B := by
  cases subsingleton_or_nontrivial P with
  | inl _ =>
    have := Module.subsingleton P B
    exact ⟨fun _ _ _ _ _ ↦ Subsingleton.elim _ _⟩
  | inr _ => ?_
  refine .of_smul_eq_zero fun a b hab ↦ or_iff_not_imp_left.mpr fun ha ↦ ?_
  suffices hb : b ∈ sInf (minimalPrimes B) by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hb
    exact (mem_nilradical.mp hb).eq_zero
  refine Submodule.mem_sInf.mpr fun p hp ↦ ?_
  have := hp.1.1
  have hmul : algebraMap P (B ⧸ p) a * Ideal.Quotient.mk p b = 0 := by
    rw [IsScalarTower.algebraMap_apply P B (B ⧸ p), Ideal.Quotient.algebraMap_eq, ← map_mul,
      ← Algebra.smul_def, hab, map_zero]
  refine Ideal.Quotient.eq_zero_iff_mem.mp ((mul_eq_zero.mp hmul).resolve_left fun h0 ↦ ha ?_)
  exact h p hp (by rw [h0, map_zero])

end TauCeti
