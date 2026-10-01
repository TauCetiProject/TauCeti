/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.RingTheory.SimpleModule.Basic
-- Non-public: Cauchy's theorem `exists_prime_orderOf_dvd_card'`, in its additive form, supplies the
-- element of prime order that pins the exponent, and is used only inside a proof.
import Mathlib.GroupTheory.Perm.Cycle.Type
-- Non-public: `Nat.Coprime.isCoprime` turns a coprimality of naturals into a Bézout identity over
-- `ℤ`, again only inside a proof.
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# A finite simple module is an elementary abelian `p`-group

Let `R` be a ring and `M` a **finite** simple `R`-module. Multiplication by a natural number `n` is
`R`-linear, because the canonical `ℕ`-action commutes with the scalars; as an endomorphism it is
`n • LinearMap.id`, and its kernel is therefore an `R`-submodule. In a simple module that submodule
is `⊥` or `⊤`, so `n` either kills no nonzero element or kills everything
(`TauCeti.forall_nsmul_eq_zero_of_ne_zero`). Taking for `n` a prime `p` dividing `Nat.card M`,
Cauchy's theorem produces a nonzero element killed by `p`, and the dichotomy forces `p • m = 0` for
every `m`: the additive group of `M` is **elementary abelian of exponent `p`**
(`TauCeti.exists_prime_forall_nsmul_eq_zero`). The prime is unique, because two coprime naturals
killing `M` kill it twice over and leave nothing
(`TauCeti.subsingleton_of_forall_nsmul_eq_zero_of_coprime`).

With the exponent in hand, the behaviour of `M` at another prime `ℓ` is forced, and this is the
form in which the exponent is used. Multiplication by a natural number coprime to the exponent is
**bijective** (`TauCeti.bijective_nsmul_of_coprime`, a statement about an abelian group that needs
no ring at all): a Bézout identity `a n + b p = 1` makes `m ↦ a • (n • m)` an inverse. So for
`ℓ ≠ p` the `ℓ`-torsion subgroup `M[ℓ]` vanishes and the reduction `M / ℓM` — Mathlib's
`ModN M ℓ` — is trivial, while for `ℓ = p` the torsion subgroup is everything and `ℓM` is zero, so
the reduction is `M` itself. `TauCeti.exists_prime_torsionBy_modN_dichotomy` packages the two cases
for a finite simple module.

## The modular-induction reading

This is the module-theoretic input to the "finite modules" bullet of Layer 3 of the
modular-induction roadmap, which computes the lattice defect
`[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]` of a **finite** `G`-module `V` by running additivity along a
composition series of `V` as a `ℤ[G]`-module: "a factor with `p ≠ ℓ` has `S/ℓS = 0 = S[ℓ]`, one
with `p = ℓ` has `S/ℓS = S = S[ℓ]`". Those four identities are
`TauCeti.subsingleton_modN_of_coprime`, `TauCeti.torsionBy_eq_bot_of_coprime`,
`TauCeti.modNEquiv` and `TauCeti.torsionBy_eq_top_of_forall_nsmul_eq_zero` here, and "hence
elementary abelian `p`-groups" is `TauCeti.exists_prime_forall_nsmul_eq_zero`. Nothing below
mentions a group, a group algebra or a Grothendieck group: the statements are about an arbitrary
ring `R`, and the roadmap's case is `R = ℤ[G]`.

## Main definitions

* `TauCeti.modNEquiv`: at the exponent, the reduction `M / pM` is `M` again.

## Main results

* `TauCeti.forall_nsmul_eq_zero_of_ne_zero`: in a simple module, a natural number killing one
  nonzero element kills every element.
* `TauCeti.exists_prime_forall_nsmul_eq_zero`: **a finite simple module has prime exponent**, with
  `TauCeti.eq_of_prime_forall_nsmul_eq_zero` the uniqueness of that prime.
* `TauCeti.bijective_nsmul_of_coprime`: multiplication by a natural number coprime to an exponent
  of an abelian group is bijective, with
  `TauCeti.subsingleton_of_forall_nsmul_eq_zero_of_coprime` the degenerate case of two coprime
  exponents.
* `TauCeti.torsionBy_eq_bot_of_coprime`, `TauCeti.subsingleton_modN_of_coprime`: at a prime away
  from the exponent both the torsion subgroup and the reduction vanish.
* `TauCeti.torsionBy_eq_top_of_forall_nsmul_eq_zero`: at the exponent itself the torsion subgroup
  is everything.
* `TauCeti.exists_prime_torsionBy_modN_dichotomy`: **the two cases together** for a finite simple
  module, which is the form the roadmap bullet consumes.

## References

* [Modular-induction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ModularInduction/README.md),
  Layer 3, "Finite modules".
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Section VII.3, (7.3.3)(i).
-/

public section

namespace TauCeti

/-! ### Multiplication by a coprime natural number -/

section AddCommGroup

variable {M : Type*} [AddCommGroup M]

/-- **Multiplication by a natural number coprime to an exponent is bijective.** If `p` kills every
element of `M` and `n` is coprime to `p`, a Bézout identity `a n + b p = 1` over `ℤ` exhibits
`m ↦ a • m` as a two-sided inverse of `m ↦ n • m`, because the `b p` term acts by zero. No ring of
scalars is involved: this is a statement about the underlying abelian group.

Mathlib's `Nat.Coprime.nsmul_right_bijective` is the same conclusion from a different hypothesis,
coprimality with `Nat.card M` for a finite `M`. The hypothesis here is the one the exponent of a
simple module supplies, and it asks for no finiteness: an infinite `𝔽_p`-vector space is covered. -/
theorem bijective_nsmul_of_coprime {p n : ℕ} (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    Function.Bijective fun m : M ↦ n • m := by
  obtain ⟨a, b, hab⟩ := h.isCoprime
  have key : ∀ m : M, a • (n • m) = m := by
    intro m
    have h1 : (a * (n : ℤ) + b * (p : ℤ)) • m = m := by rw [hab, one_smul]
    rw [add_smul, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul ℤ n m,
      Nat.cast_smul_eq_nsmul ℤ p m, hp m, smul_zero, add_zero] at h1
    exact h1
  refine ⟨fun x y hxy ↦ ?_, fun m ↦ ⟨a • m, ?_⟩⟩
  · simpa only [key] using congrArg (fun z : M ↦ a • z) hxy
  · change n • a • m = m
    rw [smul_comm]
    exact key m

/-- **Two coprime exponents leave nothing.** If coprime naturals `p` and `q` both kill every
element of `M` then `M` is trivial: multiplication by `q` is bijective by
`TauCeti.bijective_nsmul_of_coprime` and is also the zero map. -/
theorem subsingleton_of_forall_nsmul_eq_zero_of_coprime {p q : ℕ} (hp : ∀ m : M, p • m = 0)
    (hq : ∀ m : M, q • m = 0) (h : Nat.Coprime p q) : Subsingleton M := by
  have hinj := (bijective_nsmul_of_coprime hp h.symm).injective
  refine ⟨fun x y ↦ hinj ?_⟩
  simp only [hq]

end AddCommGroup

/-! ### The exponent of a finite simple module -/

section SimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- Membership in the kernel of multiplication by `n`, read without the `ℕ`-action on linear
maps. -/
private theorem mem_ker_nsmul_id_iff {n : ℕ} {m : M} :
    m ∈ LinearMap.ker (n • (LinearMap.id : M →ₗ[R] M)) ↔ n • m = 0 := by
  rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]

variable {R M}

/-- **In a simple module a natural number that kills one nonzero element kills every element.**
Multiplication by `n` is the `R`-linear endomorphism `n • LinearMap.id`, so its kernel is an
`R`-submodule; a nonzero element of that kernel keeps it from being `⊥`, and in a simple module it
is then `⊤`. -/
theorem forall_nsmul_eq_zero_of_ne_zero [IsSimpleModule R M] {n : ℕ} {m₀ : M} (hm₀ : m₀ ≠ 0)
    (h : n • m₀ = 0) (m : M) : n • m = 0 := by
  have hne : LinearMap.ker (n • (LinearMap.id : M →ₗ[R] M)) ≠ ⊥ := by
    intro hbot
    have hmem : m₀ ∈ (⊥ : Submodule R M) := hbot ▸ (mem_ker_nsmul_id_iff R M).mpr h
    exact hm₀ ((Submodule.mem_bot R).mp hmem)
  have htop : LinearMap.ker (n • (LinearMap.id : M →ₗ[R] M)) = ⊤ :=
    (eq_bot_or_eq_top _).resolve_left hne
  exact (mem_ker_nsmul_id_iff R M).mp (htop ▸ Submodule.mem_top)

variable (R M)

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

variable {R M}

/-- **The exponent of a nontrivial module is a unique prime.** Two primes both killing a nontrivial
module are coprime unless equal, and coprime exponents leave nothing
(`TauCeti.subsingleton_of_forall_nsmul_eq_zero_of_coprime`). -/
theorem eq_of_prime_forall_nsmul_eq_zero [Nontrivial M] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp' : ∀ m : M, p • m = 0) (hq' : ∀ m : M, q • m = 0) : p = q := by
  by_contra hne
  exact (not_subsingleton M)
    (subsingleton_of_forall_nsmul_eq_zero_of_coprime hp' hq' ((Nat.coprime_primes hp hq).mpr hne))

end SimpleModule

/-! ### Torsion and reduction away from the exponent -/

section Torsion

variable {M : Type*} [AddCommGroup M] {p n : ℕ}

/-- **Away from the exponent there is no torsion.** If `p` kills `M` and `n` is coprime to `p`,
multiplication by `n` is injective, so the `n`-torsion subgroup `M[n]` is trivial. -/
theorem torsionBy_eq_bot_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    AddSubgroup.torsionBy M (n : ℤ) = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun m hm ↦ ?_
  have hinj := (bijective_nsmul_of_coprime hp h).injective
  exact hinj (by simpa only [smul_zero] using AddSubgroup.torsionBy.nsmul_iff.mp hm)

/-- **Away from the exponent multiplication is onto.** If `p` kills `M` and `n` is coprime to `p`
then `n M = M`, which is the statement that `TauCeti.subsingleton_modN_of_coprime` quotients by. -/
theorem range_lsmul_eq_top_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    LinearMap.range (LinearMap.lsmul ℤ M (n : ℤ)) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun m ↦ ?_
  obtain ⟨x, hx⟩ := (bijective_nsmul_of_coprime hp h).surjective m
  exact ⟨x, by rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul]; exact hx⟩

/-- **Away from the exponent the reduction vanishes.** If `p` kills `M` and `n` is coprime to `p`
then `M / nM` — Mathlib's `ModN M n` — is trivial. -/
theorem subsingleton_modN_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    Subsingleton (ModN M n) := by
  obtain ⟨hu⟩ :=
    Submodule.unique_quotient_iff_eq_top.mpr (range_lsmul_eq_top_of_coprime hp h)
  exact @Unique.instSubsingleton _ hu

/-- **At the exponent everything is torsion.** -/
theorem torsionBy_eq_top_of_forall_nsmul_eq_zero (hp : ∀ m : M, p • m = 0) :
    AddSubgroup.torsionBy M (p : ℤ) = ⊤ :=
  eq_top_iff.mpr fun m _ ↦ AddSubgroup.torsionBy.nsmul_iff.mpr (hp m)

/-- **At the exponent multiplication is zero.** -/
theorem range_lsmul_eq_bot_of_forall_nsmul_eq_zero (hp : ∀ m : M, p • m = 0) :
    LinearMap.range (LinearMap.lsmul ℤ M (p : ℤ)) = ⊥ := by
  refine LinearMap.range_eq_bot.mpr (LinearMap.ext fun m ↦ ?_)
  rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, hp m, LinearMap.zero_apply]

/-- **At the exponent the reduction is the module itself.** Since `pM = 0`, the quotient
`ModN M p = M / pM` is `M`, linearly over `ℤ`. -/
noncomputable def modNEquiv (hp : ∀ m : M, p • m = 0) : ModN M p ≃ₗ[ℤ] M :=
  Submodule.quotEquivOfEqBot _ (range_lsmul_eq_bot_of_forall_nsmul_eq_zero hp)

end Torsion

/-! ### The dichotomy for a finite simple module -/

/-- **The torsion and the reduction of a finite simple module at a prime.** The prime exponent `p`
of `TauCeti.exists_prime_forall_nsmul_eq_zero` splits the primes in two: at `p` itself the module is
all torsion and the reduction `M / pM` is `M` again, and at every other prime both the torsion
subgroup and the reduction vanish. This is the subquotient computation that the lattice defect of a
finite module is assembled from. -/
theorem exists_prime_torsionBy_modN_dichotomy (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [Finite M] [IsSimpleModule R M] :
    ∃ p : ℕ, p.Prime ∧ AddSubgroup.torsionBy M (p : ℤ) = ⊤ ∧
      Nonempty (ModN M p ≃ₗ[ℤ] M) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
        AddSubgroup.torsionBy M (ℓ : ℤ) = ⊥ ∧ Subsingleton (ModN M ℓ) := by
  obtain ⟨p, hp, hkill⟩ := exists_prime_forall_nsmul_eq_zero R M
  refine ⟨p, hp, torsionBy_eq_top_of_forall_nsmul_eq_zero hkill, ⟨modNEquiv hkill⟩,
    fun ℓ hℓ hne ↦ ?_⟩
  have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ hp).mpr hne
  exact ⟨torsionBy_eq_bot_of_coprime hkill hcop, subsingleton_modN_of_coprime hkill hcop⟩

end TauCeti
