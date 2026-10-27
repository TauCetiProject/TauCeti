/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition

/-!
# The idempotents of the profinite integers

Under the product decomposition `ℤ̂ ≃ ∏_ℓ ℤ_ℓ` (`zHat.ringEquivPiPadicInt`), every factor `ℤ_ℓ` is
a domain, whose only idempotents are `0` and `1`. So the idempotents of `ℤ̂` are exactly the
profinite integers whose components are all `0` or `1`, and they are indexed by the sets of primes
at which the component is `1`. For a set `S` of primes, `zHat.idemOfSet S`, written `ω_S` in
prose, is the profinite integer with component `1` at the primes of `S` and `0` at the others.
For `S = {ℓ}` it is the prime idempotent `ω_ℓ = zHat.idem ℓ`.

The map `S ↦ ω_S` is injective, takes intersections to products and complements to `1 - ω_S`,
and its image is the set of all idempotents (`zHat.isIdempotentElem_iff_exists_idemOfSet`). An
integer that is idempotent is `0` or `1`, so `ω_S` is an integer only for `S = ∅` and for the set
of all primes (`zHat.idemOfSet_mem_range_intCast_iff`).

As an example, the profinite integer with components `1, 0, 1, 0, …` along the primes
`2, 3, 5, 7, …` is `ω_S` for the set `S` of primes `ℓ` with an even number `π'(ℓ)` of primes
below them, since the `n`-th prime has exactly `n` primes below it
(`zHat.component_idemOfSet_even_primeCounting'_nth`). It has infinitely many components equal to
`1` and infinitely many equal to `0`, and it is not an integer
(`zHat.idemOfSet_even_primeCounting'_ne_intCast`).

## Main definitions

* `TauCeti.zHat.idemOfSet`: the idempotent `ω_S` attached to a set `S` of primes.

## Main results

* `TauCeti.zHat.ringEquivPiPadicInt_idemOfSet`, `TauCeti.zHat.component_idemOfSet`: the
  components of `ω_S`.
* `TauCeti.zHat.isIdempotentElem_iff_exists_idemOfSet`, `TauCeti.zHat.idemOfSet_injective`:
  `S ↦ ω_S` is a bijection from the sets of primes onto the idempotents of `ℤ̂`.
* `TauCeti.zHat.idemOfSet_inter`, `TauCeti.zHat.idemOfSet_compl`, `TauCeti.zHat.idemOfSet_union`:
  the Boolean operations on sets of primes become ring operations on idempotents.
* `TauCeti.zHat.idemOfSet_mem_range_intCast_iff`: `ω_S` is an integer exactly when `S` is empty or
  contains every prime.
* `TauCeti.zHat.component_idemOfSet_even_primeCounting'_nth`,
  `TauCeti.zHat.idemOfSet_even_primeCounting'_ne_intCast`: the profinite integer with components
  `1, 0, 1, 0, …` is not an integer.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

namespace zHat

universe u

open scoped Classical in
/-- **The idempotent attached to a set of primes.** `zHat.idemOfSet S`, written `ω_S`, is the
profinite integer whose `ℓ`-adic component is `1` for `ℓ ∈ S` and `0` for `ℓ ∉ S`
(`zHat.component_idemOfSet`). -/
noncomputable def idemOfSet (S : Set Nat.Primes) : Additive zHat.{u} :=
  ringEquivPiPadicInt.symm fun ℓ ↦ if ℓ ∈ S then 1 else 0

variable {S T : Set Nat.Primes}

/-- Under the product decomposition, `ω_S` is the family with `1` at the primes of `S` and `0` at
the others. -/
@[simp]
theorem ringEquivPiPadicInt_idemOfSet (S : Set Nat.Primes) [DecidablePred (· ∈ S)] :
    ringEquivPiPadicInt (idemOfSet.{u} S) =
      (fun ℓ ↦ if ℓ ∈ S then 1 else 0 : ∀ ℓ : Nat.Primes, ℤ_[ℓ]) := by
  rw [idemOfSet, RingEquiv.apply_symm_apply]
  -- The two families differ only in the decidability instance of `ℓ ∈ S`.
  exact funext fun ℓ ↦ by congr

/-- **The components of `ω_S`**: `1` at the primes of `S` and `0` at the others. -/
@[simp]
theorem component_idemOfSet (S : Set Nat.Primes) (ℓ : Nat.Primes) [Decidable (ℓ ∈ S)] :
    component ℓ (idemOfSet.{u} S) = if ℓ ∈ S then 1 else 0 := by
  rw [idemOfSet, component_ringEquivPiPadicInt_symm]
  -- The two sides differ only in the decidability instance of `ℓ ∈ S`.
  congr

/-- The component of `ω_S` at a prime of `S` is `1`. -/
theorem component_idemOfSet_of_mem {ℓ : Nat.Primes} (h : ℓ ∈ S) :
    component ℓ (idemOfSet.{u} S) = 1 := by
  classical
  simp [h]

/-- The component of `ω_S` at a prime outside `S` is `0`. -/
theorem component_idemOfSet_of_notMem {ℓ : Nat.Primes} (h : ℓ ∉ S) :
    component ℓ (idemOfSet.{u} S) = 0 := by
  classical
  simp [h]

/-- `ω_S` is idempotent. -/
theorem isIdempotentElem_idemOfSet (S : Set Nat.Primes) : IsIdempotentElem (idemOfSet.{u} S) := by
  classical
  refine ringEquivPiPadicInt.injective (funext fun ℓ ↦ ?_)
  simp only [map_mul, ringEquivPiPadicInt_apply, component_idemOfSet]
  split_ifs <;> simp

/-- The idempotent of the empty set of primes is `0`. -/
@[simp]
theorem idemOfSet_empty : idemOfSet.{u} ∅ = 0 :=
  ringEquivPiPadicInt.injective (funext fun ℓ ↦ by
    rw [ringEquivPiPadicInt_apply, component_idemOfSet_of_notMem (Set.notMem_empty ℓ), map_zero,
      Pi.zero_apply])

/-- The idempotent of the set of all primes is `1`. -/
@[simp]
theorem idemOfSet_univ : idemOfSet.{u} Set.univ = 1 :=
  ringEquivPiPadicInt.injective (funext fun ℓ ↦ by
    rw [ringEquivPiPadicInt_apply, component_idemOfSet_of_mem (Set.mem_univ ℓ), map_one,
      Pi.one_apply])

/-- The idempotent of a single prime `ℓ` is the prime idempotent `ω_ℓ`. -/
@[simp]
theorem idemOfSet_singleton (ℓ : Nat.Primes) : idemOfSet.{u} {ℓ} = idem ℓ := by
  classical
  refine ringEquivPiPadicInt.injective (funext fun q ↦ ?_)
  simp only [ringEquivPiPadicInt_apply, component_idemOfSet, component_idem, Set.mem_singleton_iff,
    Nat.Primes.coe_nat_inj]

/-- **Intersections of sets of primes become products of idempotents.** -/
theorem idemOfSet_inter (S T : Set Nat.Primes) :
    idemOfSet.{u} (S ∩ T) = idemOfSet S * idemOfSet T := by
  classical
  refine ringEquivPiPadicInt.injective (funext fun ℓ ↦ ?_)
  simp only [map_mul, ringEquivPiPadicInt_apply, component_idemOfSet, Set.mem_inter_iff]
  split_ifs <;> simp_all

/-- **Complements of sets of primes become complementary idempotents.** -/
theorem idemOfSet_compl (S : Set Nat.Primes) : idemOfSet.{u} Sᶜ = 1 - idemOfSet S := by
  classical
  refine ringEquivPiPadicInt.injective (funext fun ℓ ↦ ?_)
  simp only [map_sub, map_one, ringEquivPiPadicInt_apply, component_idemOfSet, Set.mem_compl_iff]
  split_ifs <;> simp_all

/-- **Unions of sets of primes**: `ω_{S ∪ T} = ω_S + ω_T - ω_S ω_T`. -/
theorem idemOfSet_union (S T : Set Nat.Primes) :
    idemOfSet.{u} (S ∪ T) = idemOfSet S + idemOfSet T - idemOfSet S * idemOfSet T := by
  classical
  refine ringEquivPiPadicInt.injective (funext fun ℓ ↦ ?_)
  simp only [map_sub, map_add, map_mul, ringEquivPiPadicInt_apply, component_idemOfSet,
    Set.mem_union]
  split_ifs <;> simp_all

/-- **Distinct sets of primes have distinct idempotents**: a prime in one set and not the other
sees the components `1` and `0`. -/
theorem idemOfSet_injective : Function.Injective idemOfSet.{u} := fun S T h ↦ by
  classical
  ext ℓ
  have h' := congrArg (component ℓ) h
  simp only [component_idemOfSet] at h'
  split_ifs at h' <;> simp_all

/-- Two sets of primes have the same idempotent exactly when they are equal. -/
@[simp]
theorem idemOfSet_inj : idemOfSet.{u} S = idemOfSet T ↔ S = T :=
  idemOfSet_injective.eq_iff

/-- **The idempotents of `ℤ̂` are the `ω_S`.** A profinite integer is idempotent exactly when it is
`ω_S` for some set `S` of primes, necessarily the set of primes at which its component is `1`: each
component of an idempotent is an idempotent of the domain `ℤ_ℓ`, hence `0` or `1`. -/
theorem isIdempotentElem_iff_exists_idemOfSet {a : Additive zHat.{u}} :
    IsIdempotentElem a ↔ ∃ S, idemOfSet S = a := by
  classical
  refine ⟨fun h ↦ ⟨{ℓ | component ℓ a = 1}, ?_⟩, fun ⟨S, hS⟩ ↦ hS ▸ isIdempotentElem_idemOfSet S⟩
  refine ringEquivPiPadicInt.injective (funext fun ℓ ↦ ?_)
  simp only [ringEquivPiPadicInt_apply, component_idemOfSet, Set.mem_ofPred_eq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (h.map (component ℓ)) with h0 | h1 <;> simp [*]

/-- **`ω_S` is an integer exactly when `S` is empty or contains every prime**, that is, when
`ω_S` is `0` or `1`: an idempotent integer is `0` or `1`. -/
theorem idemOfSet_mem_range_intCast_iff :
    idemOfSet.{u} S ∈ Set.range (Int.cast : ℤ → Additive zHat.{u}) ↔ S = ∅ ∨ S = Set.univ := by
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, ?_⟩
  · rcases isIdempotentElem_intCast_iff.mp (hn ▸ isIdempotentElem_idemOfSet S) with rfl | rfl
    · exact Or.inl (idemOfSet_injective (by rw [← hn, idemOfSet_empty, Int.cast_zero]))
    · exact Or.inr (idemOfSet_injective (by rw [← hn, idemOfSet_univ, Int.cast_one]))
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [Int.cast_zero, idemOfSet_empty]⟩
    · exact ⟨1, by rw [Int.cast_one, idemOfSet_univ]⟩

/-- `ω_S` is not an integer when `S` contains some, but not every, prime. -/
theorem idemOfSet_ne_intCast (h₀ : S.Nonempty) (h₁ : S ≠ Set.univ) (n : ℤ) :
    idemOfSet.{u} S ≠ n := fun h ↦
  (idemOfSet_mem_range_intCast_iff.mp ⟨n, h.symm⟩).elim h₀.ne_empty h₁

section Alternating

open Nat (nth primeCounting')

/-- The `k`-th prime has an even number of primes below it exactly when `k` is even. -/
private theorem nth_mem_setOf_even_primeCounting'_iff (k : ℕ) (hk : (nth Nat.Prime k).Prime) :
    (⟨nth Nat.Prime k, hk⟩ : Nat.Primes) ∈ {ℓ : Nat.Primes | Even (primeCounting' ℓ)} ↔
      Even k :=
  Iff.of_eq (congrArg Even (Nat.primeCounting'_nth_eq k))

/-- **The profinite integer with components `1, 0, 1, 0, …`.** Let `S` be the set of primes `ℓ`
with an even number `π'(ℓ)` of primes below `ℓ`. Since the `n`-th prime has exactly `n` primes
below it, the component of `ω_S` at the `n`-th prime, counting from `nth Nat.Prime 0 = 2`, is `1`
for even `n` and `0` for odd `n`. -/
theorem component_nth_idemOfSet_even_primeCounting' (n : ℕ) [Fact (nth Nat.Prime n).Prime]
    [Decidable (Even n)] :
    component (nth Nat.Prime n) (idemOfSet.{u} {ℓ : Nat.Primes | Even (primeCounting' ℓ)}) =
      if Even n then 1 else 0 := by
  classical
  exact (component_idemOfSet _ ⟨nth Nat.Prime n, Fact.out⟩).trans
    (if_congr (nth_mem_setOf_even_primeCounting'_iff n Fact.out) rfl rfl)

/-- **The profinite integer with components `1, 0, 1, 0, …` is not an integer**: it is `ω_S` for a
set `S` of primes containing the prime `nth Nat.Prime 0 = 2` but not the prime
`nth Nat.Prime 1 = 3`. -/
theorem idemOfSet_even_primeCounting'_ne_intCast (n : ℤ) :
    idemOfSet.{u} {ℓ : Nat.Primes | Even (primeCounting' ℓ)} ≠ n := by
  have hmem (k : ℕ) := nth_mem_setOf_even_primeCounting'_iff k (Nat.prime_nth_prime k)
  refine idemOfSet_ne_intCast ⟨_, (hmem 0).mpr .zero⟩ (fun h ↦ ?_) n
  exact Nat.not_even_one ((hmem 1).mp (h ▸ Set.mem_univ _))

end Alternating

end zHat

end TauCeti
