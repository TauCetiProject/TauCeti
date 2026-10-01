/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Exponent
public import TauCeti.RingTheory.SimpleModule.Basic
-- Non-public: Cauchy's theorem `exists_prime_orderOf_dvd_card'`, in its additive form, supplies the
-- element of prime order that pins the exponent, and is used only inside a proof.
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# A finite simple module is an elementary abelian `p`-group

Let `R` be a ring and `M` a **finite** simple `R`-module. In a simple module a natural number `n`
either kills no nonzero element or kills every element, by
`TauCeti.forall_nsmul_eq_zero_of_ne_zero`. Taking for `n` a prime `p` dividing `Nat.card M`,
Cauchy's theorem produces a nonzero element killed by `p`, and that dichotomy forces `p • m = 0` for
every `m`: the additive group of `M` is **elementary abelian of exponent `p`**
(`TauCeti.exists_prime_forall_nsmul_eq_zero`). That prime is unique, by
`TauCeti.eq_of_prime_forall_nsmul_eq_zero`.

With the exponent in hand, the behaviour of `M` at every prime `ℓ` is forced by the coprime
multiplication results of `TauCeti/Algebra/Group/Exponent.lean`, which see neither the ring nor
simplicity: for `ℓ ≠ p` the torsion subgroup `M[ℓ]` vanishes and the reduction `M / ℓM` — Mathlib's
`ModN M ℓ` — is trivial, while for `ℓ = p` the torsion subgroup is everything and `ℓM` is zero, so
the reduction is `M` itself. `TauCeti.exists_prime_torsionBy_modN_dichotomy` packages the two cases.

## Main results

* `TauCeti.exists_prime_forall_nsmul_eq_zero`: **a finite simple module has prime exponent.**
* `TauCeti.exists_prime_torsionBy_modN_dichotomy`: **the torsion subgroup and the reduction of a
  finite simple module at every prime**, the two cases together.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Section VII.3, (7.3.3)(i).
-/

public section

namespace TauCeti

section SimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- **A finite simple module is an elementary abelian `p`-group.** A simple module is nontrivial,
so a prime `p` divides its cardinality; Cauchy's theorem produces an element of additive order `p`,
which is nonzero and killed by `p`, and `TauCeti.forall_nsmul_eq_zero_of_ne_zero` spreads that to
the whole module. -/
theorem exists_prime_forall_nsmul_eq_zero [Finite M] [IsSimpleModule R M] :
    ∃ p : ℕ, p.Prime ∧ ∀ m : M, p • m = 0 := by
  have hnt : Nontrivial M := IsSimpleModule.nontrivial R M
  have hne1 : Nat.card M ≠ 1 := fun h ↦ not_subsingleton M (Nat.card_eq_one_iff_unique.mp h).1
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m₀, hm₀⟩ := exists_prime_addOrderOf_dvd_card' (G := M) p hdvd
  have hm₀ne : m₀ ≠ 0 := fun h ↦ by
    rw [h, addOrderOf_zero] at hm₀
    exact hp.one_lt.ne hm₀
  have hkill : p • m₀ = 0 := by
    rw [← hm₀]
    exact addOrderOf_nsmul_eq_zero m₀
  exact ⟨p, hp, forall_nsmul_eq_zero_of_ne_zero (R := R) hm₀ne hkill⟩

end SimpleModule

/-- **The torsion and the reduction of a finite simple module at a prime.** The prime exponent `p`
of `TauCeti.exists_prime_forall_nsmul_eq_zero` splits the primes in two: at `p` itself the module is
all torsion and the reduction `M / pM` is `M` again, and at every other prime both the torsion
subgroup and the reduction vanish. -/
theorem exists_prime_torsionBy_modN_dichotomy (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [Finite M] [IsSimpleModule R M] :
    ∃ p : ℕ, p.Prime ∧ AddSubgroup.torsionBy M (p : ℤ) = ⊤ ∧
      Nonempty (ModN M p ≃ₗ[ℤ] M) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
        AddSubgroup.torsionBy M (ℓ : ℤ) = ⊥ ∧ Subsingleton (ModN M ℓ) := by
  obtain ⟨p, hp, hkill⟩ := exists_prime_forall_nsmul_eq_zero R M
  refine ⟨p, hp, eq_top_iff.mpr fun m _ ↦ AddSubgroup.torsionBy.nsmul_iff.mpr (hkill m),
    ⟨modNEquiv hkill⟩, fun ℓ hℓ hne ↦ ?_⟩
  have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ hp).mpr hne
  exact ⟨torsionBy_eq_bot_of_coprime hkill hcop, subsingleton_modN_of_coprime hkill hcop⟩

end TauCeti
