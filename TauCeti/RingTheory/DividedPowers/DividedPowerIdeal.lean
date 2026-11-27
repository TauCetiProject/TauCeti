/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.RingTheory.WittVector.AdicLift
import Mathlib.Data.Nat.Choose.Factorization
import TauCeti.RingTheory.AdicCompletion.Perfection

/-!
# The ideal of elements with divided powers

For a commutative semiring `R`, `TauCeti.dividedPowerIdeal R` is the ideal `𝔡(R)` of elements `x`
such that `n!` divides `xⁿ` for every `n`. Ring maps send `𝔡` into `𝔡`, and every ideal carrying
a divided power structure lies in `𝔡`, since `xⁿ = n! γₙ(x)`. When `R` has no `ℤ`-torsion, `𝔡(R)`
is the set of `x` whose divided powers `xⁿ / n!`, computed in `ℚ ⊗ R`, lie in `R`. Unlike a
divided power ideal, `𝔡(R)` comes with no chosen divided powers, and every ring has one.

Let `p` be a prime and `S` a commutative ring. Every `x ∈ 𝔡(S)` has `x ^ p ∈ p S`, so
`x ↦ x ^ p` induces a ring map `S ⧸ 𝔡(S) → S ⧸ p`, Tau Ceti's `Ideal.frobeniusQuot`. If `p` lies in
the Jacobson radical of `S`, for instance if `S` is `p`-adically complete, then `p ∈ 𝔡(S)`: by
Legendre's formula `n! = p ^ v m` with `v ≤ n` and `m` prime to `p`, hence a unit of `S`. Then
`𝔡(S)` lies in the Jacobson radical, and the reduction `S → S ⧸ 𝔡(S)` reflects units.

If `S` is `p`-adically complete, maps out of perfect objects into `S ⧸ 𝔡(S)` lift uniquely to
`S`, as maps into `S ⧸ p` do: monoid maps from a commutative monoid on which
`x ↦ x ^ p` is bijective, and, through the Witt vectors, ring maps from a perfect ring of
characteristic `p`. These are the Teichmüller construction and the universal property of the Witt
vectors carried out modulo `𝔡(S)` instead of modulo `p`. Rings of the form `S ⧸ 𝔡(S)`, for
`p`-complete and `p`-torsion-free `S`, play the role of divided power thickenings in comparisons
with crystalline period rings.

## Main definitions

* `TauCeti.dividedPowerIdeal R`: the ideal of `x : R` with `n! ∣ xⁿ` for every `n`.

## Main results

* `TauCeti.mem_dividedPowerIdeal`: the defining property.
* `TauCeti.map_mem_dividedPowerIdeal`, `TauCeti.dividedPowerIdeal_le_comap`: ring maps send `𝔡`
  into `𝔡`.
* `DividedPowers.le_dividedPowerIdeal`: an ideal with divided powers lies in `𝔡`.
* `TauCeti.natCast_dvd_pow_of_mem_dividedPowerIdeal`: `n ∣ xⁿ` for `x ∈ 𝔡(R)` and `n ≠ 0`.
* `TauCeti.natCast_mem_dividedPowerIdeal`: `p ∈ 𝔡(S)` when `p` lies in the Jacobson radical.
* `TauCeti.dividedPowerIdeal_le_jacobson`, `TauCeti.isLocalHom_mk_dividedPowerIdeal`: then `𝔡(S)`
  lies in the Jacobson radical, and `S → S ⧸ 𝔡(S)` is a local homomorphism.
* `TauCeti.bijective_mk_dividedPowerIdeal_comp_monoidHom`: for `p`-adically complete `S`, monoid
  maps `M →* S` from a monoid on which `x ↦ x ^ p` is bijective correspond to monoid maps
  `M →* S ⧸ 𝔡(S)`.
* `TauCeti.WittVector.existsUnique_mk_dividedPowerIdeal_comp_eq_comp_constantCoeff`: for
  `p`-adically complete `S` and a perfect ring `k` of characteristic `p`, every ring map
  `k →+* S ⧸ 𝔡(S)` has exactly one lift `𝕎 k →+* S` reducing to it on the `0`-th Witt coordinate.

## References

* P. Berthelot, A. Ogus, *Notes on crystalline cohomology*, Princeton Univ. Press (1978), §3
  (divided powers).
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter II
  (multiplicative representatives and Witt vectors).
* The formal proof whose route this file follows: the folder `grh` of
  https://github.com/lsernau/grh-lean (Apache 2.0) at commit
  72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open scoped Nat

namespace TauCeti

section Semiring

variable (R : Type*) [CommSemiring R]

/-- The ideal `𝔡(R)` of elements `x` such that `n!` divides `xⁿ` for every `n`. When `R` has no
`ℤ`-torsion, these are the elements whose divided powers `xⁿ / n!` lie in `R`; no divided power
structure is chosen. -/
def dividedPowerIdeal : Ideal R where
  carrier := {x | ∀ n, (n ! : R) ∣ x ^ n}
  zero_mem' n := by cases n <;> simp
  add_mem' {x y} hx hy n := by
    -- In `(x + y) ^ n = ∑ (n choose m) xᵐ yⁿ⁻ᵐ`, each term is a multiple of
    -- `(n choose m) m! (n - m)! = n!`.
    rw [add_pow]
    refine Finset.dvd_sum fun m hm ↦ ?_
    obtain ⟨a, ha⟩ := hx m
    obtain ⟨b, hb⟩ := hy (n - m)
    rw [ha, hb, ← Nat.choose_mul_factorial_mul_factorial
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
    exact ⟨a * b, by push_cast; ring⟩
  smul_mem' c x hx n := by
    rw [smul_eq_mul, mul_pow]
    exact dvd_mul_of_dvd_right (hx n) _

variable {R}

/-- `x ∈ 𝔡(R)` if and only if `n!` divides `xⁿ` for every `n`. -/
theorem mem_dividedPowerIdeal {x : R} : x ∈ dividedPowerIdeal R ↔ ∀ n, (n ! : R) ∣ x ^ n :=
  Iff.rfl

/-- Ring maps send elements with divided powers to elements with divided powers. -/
theorem map_mem_dividedPowerIdeal {S F : Type*} [CommSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {x : R} (hx : x ∈ dividedPowerIdeal R) :
    f x ∈ dividedPowerIdeal S := fun n ↦ by
  simpa only [map_pow, map_natCast] using map_dvd f (hx n)

/-- A ring map sends `𝔡` into `𝔡`, so it induces a map of the quotients by `𝔡`. -/
theorem dividedPowerIdeal_le_comap {S : Type*} [CommSemiring S] (f : R →+* S) :
    dividedPowerIdeal R ≤ (dividedPowerIdeal S).comap f :=
  fun _ hx ↦ map_mem_dividedPowerIdeal f hx

/-- If `x ∈ 𝔡(R)` and `n ≠ 0`, then `n` divides `xⁿ`. For a commutative ring `R` and a prime `p`,
this says that `x ↦ x ^ p` induces a ring map `R ⧸ 𝔡(R) → R ⧸ p` (`Ideal.frobeniusQuot`). -/
theorem natCast_dvd_pow_of_mem_dividedPowerIdeal {x : R} (hx : x ∈ dividedPowerIdeal R) {n : ℕ}
    (hn : n ≠ 0) : (n : R) ∣ x ^ n :=
  (Nat.cast_dvd_cast (Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl)).trans (hx n)

end Semiring

/-- **An ideal with divided powers consists of elements with divided powers**: `xⁿ = n! γₙ(x)`. -/
theorem _root_.DividedPowers.le_dividedPowerIdeal {A : Type*} [CommSemiring A] {I : Ideal A}
    (hI : DividedPowers I) : I ≤ dividedPowerIdeal A :=
  fun _ hx n ↦ ⟨hI.dpow n _, (hI.factorial_mul_dpow_eq_pow hx).symm⟩

section Jacobson

variable {S : Type*} [CommRing S] {p : ℕ} [hp : Fact p.Prime]

/-- **`p` has divided powers when it lies in the Jacobson radical**, for instance in a `p`-adically
complete ring: `n! = p ^ v m` with `v ≤ n` by Legendre's formula, and `m` is prime to `p`, hence a
unit. -/
theorem natCast_mem_dividedPowerIdeal (h : (p : S) ∈ Ring.jacobson S) :
    (p : S) ∈ dividedPowerIdeal S := by
  intro n
  have hcop := Nat.coprime_ordCompl hp.out (Nat.factorial_ne_zero n)
  have hv := (Nat.factorization_factorial_le_div_pred hp.out n).trans (Nat.div_le_self _ _)
  have hfac := Nat.ordProj_mul_ordCompl_eq_self (n !) p
  generalize (n !).factorization p = v at hcop hv hfac
  generalize n ! / p ^ v = m at hcop hfac
  -- `n! = p ^ v m` with `v ≤ n`, and `m` is prime to `p`, hence a unit since `p` lies in the
  -- Jacobson radical.
  have hm : IsUnit (m : S) := by
    obtain ⟨a, b, hab⟩ := hcop.isCoprime.map (Int.castRingHom S)
    simp only [map_natCast] at hab
    refine isUnit_of_mul_isUnit_right (x := b) ?_
    rw [show b * (m : S) = p * -a + 1 by linear_combination hab]
    exact Ring.mem_jacobson_iff.mp h (-a)
  rw [← hfac, Nat.cast_mul, Nat.cast_pow,
    show (p : S) ^ n = p ^ v * p ^ (n - v) by rw [← pow_add, Nat.add_sub_cancel' hv]]
  exact mul_dvd_mul_left _ hm.dvd

/-- If `p` lies in the Jacobson radical, so does `𝔡(S)`: every `x ∈ 𝔡(S)` has `x ^ p ∈ p S`. -/
theorem dividedPowerIdeal_le_jacobson (h : (p : S) ∈ Ring.jacobson S) :
    dividedPowerIdeal S ≤ Ring.jacobson S := fun x hx ↦ by
  obtain ⟨c, hc⟩ := natCast_dvd_pow_of_mem_dividedPowerIdeal hx hp.out.ne_zero
  rw [← Ideal.jacobson_bot] at h ⊢
  exact Ideal.isRadical_jacobson ⊥ ⟨p, hc ▸ Ideal.mul_mem_right c _ h⟩

/-- If `p` lies in the Jacobson radical, then `S → S ⧸ 𝔡(S)` is a local homomorphism: an element
is a unit as soon as its class modulo `𝔡(S)` is. -/
theorem isLocalHom_mk_dividedPowerIdeal (h : (p : S) ∈ Ring.jacobson S) :
    IsLocalHom (Ideal.Quotient.mk (dividedPowerIdeal S)) :=
  isLocalHom_of_le_jacobson (dividedPowerIdeal_le_jacobson h)

variable [IsAdicComplete (Ideal.span {(p : S)}) S]

variable (S p) in
/-- In a `p`-adically complete ring, `p S ≤ 𝔡(S)`. -/
private theorem span_le_dividedPowerIdeal :
    Ideal.span {(p : S)} ≤ dividedPowerIdeal S :=
  Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <| natCast_mem_dividedPowerIdeal <|
    IsAdicComplete.le_jacobson _ (Ideal.mem_span_singleton_self _)

/-- **Teichmüller lifts modulo `𝔡`.** Let `S` be `p`-adically complete and `M` a commutative
monoid on which `x ↦ x ^ p` is bijective. Then composition with `S → S ⧸ 𝔡(S)` is a bijection from
monoid maps `M →* S` to monoid maps `M →* S ⧸ 𝔡(S)`. -/
theorem bijective_mk_dividedPowerIdeal_comp_monoidHom {M : Type*} [CommMonoid M]
    [PerfectRing M p] :
    Function.Bijective fun f : M →* S ↦
      (Ideal.Quotient.mk (dividedPowerIdeal S) : S →* S ⧸ dividedPowerIdeal S).comp f :=
  IsAdicComplete.bijective_mk_comp_monoidHom (Ideal.mem_span_singleton_self _)
    (span_le_dividedPowerIdeal S p) fun _ hx ↦
      Ideal.mem_span_singleton.mpr (natCast_dvd_pow_of_mem_dividedPowerIdeal hx hp.out.ne_zero)

/-- **Witt vector lifts modulo `𝔡`.** Let `S` be `p`-adically complete and `k` a perfect ring of
characteristic `p`. Every ring map `f : k →+* S ⧸ 𝔡(S)` has exactly one lift `g : 𝕎 k →+* S` with
`g x ≡ f x₀` modulo `𝔡(S)`, where `x₀` is the `0`-th Witt coordinate of `x`. -/
theorem WittVector.existsUnique_mk_dividedPowerIdeal_comp_eq_comp_constantCoeff {k : Type*}
    [CommRing k] [CharP k p] [PerfectRing k p] (f : k →+* S ⧸ dividedPowerIdeal S) :
    ∃! g : _root_.WittVector p k →+* S,
      (Ideal.Quotient.mk (dividedPowerIdeal S)).comp g = f.comp _root_.WittVector.constantCoeff :=
  existsUnique_mk_comp_eq_comp_constantCoeff (I := Ideal.span {(p : S)})
    (span_le_dividedPowerIdeal S p)
    (fun _ hx ↦
      Ideal.mem_span_singleton.mpr (natCast_dvd_pow_of_mem_dividedPowerIdeal hx hp.out.ne_zero)) f

end Jacobson

end TauCeti
