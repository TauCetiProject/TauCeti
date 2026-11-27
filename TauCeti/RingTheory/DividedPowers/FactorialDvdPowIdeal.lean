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

For a commutative semiring `R`, `TauCeti.factorialDvdPowIdeal R` is the ideal `𝔡(R)` of elements
`x` such that `n!` divides `xⁿ` for every `n`. Ring maps send `𝔡` into `𝔡`, and every ideal
carrying a divided power structure lies in `𝔡`, since `xⁿ = n! γₙ(x)`. When `R` has no
`ℤ`-torsion, `𝔡(R)` is the set of `x` whose divided powers `xⁿ / n!`, computed in `ℚ ⊗ R`, lie in
`R`. The name records the defining condition: `𝔡(R)` is not a divided power ideal in the sense of
Mathlib's `DividedPowers`, as it comes with no chosen divided powers, and every ring has one.

Let `p` be a prime and `S` a commutative ring. Every `x ∈ 𝔡(S)` has `x ^ p ∈ p S`, so
`x ↦ x ^ p` induces a ring map `S ⧸ 𝔡(S) → S ⧸ p`, Tau Ceti's `Ideal.frobeniusQuot`. If a natural
number `n` lies in the Jacobson radical of `S`, for instance if `S` is `n`-adically complete, then
`n ∈ 𝔡(S)`: for every `k`, `k! = g m` with `g ∣ nᵏ` and `m` prime to `n`, hence a unit of `S`,
since by Legendre's formula a prime divides `k!` at most `k` times. If moreover `n ≠ 0`, then
`𝔡(S)` lies in the Jacobson radical, and the reduction `S → S ⧸ 𝔡(S)` reflects units.

If `S` is `p`-adically complete, maps out of perfect objects into `S ⧸ 𝔡(S)` lift uniquely to
`S`, as maps into `S ⧸ p` do: monoid maps from a commutative monoid on which
`x ↦ x ^ p` is bijective, and, through the Witt vectors, ring maps from a perfect ring of
characteristic `p`. These are the Teichmüller construction and the universal property of the Witt
vectors carried out modulo `𝔡(S)` instead of modulo `p`. Rings of the form `S ⧸ 𝔡(S)`, for
`p`-complete and `p`-torsion-free `S`, play the role of divided power thickenings in comparisons
with crystalline period rings.

## Main definitions

* `TauCeti.factorialDvdPowIdeal R`: the ideal of `x : R` with `n! ∣ xⁿ` for every `n`.

## Main results

* `TauCeti.mem_factorialDvdPowIdeal`: the defining property.
* `TauCeti.map_mem_factorialDvdPowIdeal`, `TauCeti.factorialDvdPowIdeal_le_comap`: ring maps send
  `𝔡` into `𝔡`.
* `DividedPowers.le_factorialDvdPowIdeal`: an ideal with divided powers lies in `𝔡`.
* `TauCeti.pow_mem_span_natCast_of_mem_factorialDvdPowIdeal`: `xⁿ ∈ n R` for `x ∈ 𝔡(R)` and
  `n ≠ 0`. For a prime `p`, this is the hypothesis of `Ideal.frobeniusQuot` for the map
  `R ⧸ 𝔡(R) → R ⧸ p`, `x ↦ x ^ p`.
* `TauCeti.natCast_mem_factorialDvdPowIdeal`: `n ∈ 𝔡(S)` when `n` lies in the Jacobson radical.
* `TauCeti.factorialDvdPowIdeal_le_jacobson`, `TauCeti.isLocalHom_mk_factorialDvdPowIdeal`: then,
  for `n ≠ 0`, `𝔡(S)` lies in the Jacobson radical, and `S → S ⧸ 𝔡(S)` is a local homomorphism.
* `TauCeti.span_natCast_le_factorialDvdPowIdeal`: `n S ≤ 𝔡(S)` for `n`-adically complete `S`.
* `TauCeti.bijective_mk_factorialDvdPowIdeal_comp_monoidHom`: for `p`-adically complete `S`,
  monoid maps `M →* S` from a monoid on which `x ↦ x ^ p` is bijective correspond to monoid maps
  `M →* S ⧸ 𝔡(S)`.
* `TauCeti.WittVector.existsUnique_mk_factorialDvdPowIdeal_comp_eq_comp_constantCoeff`: for
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
def factorialDvdPowIdeal : Ideal R where
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
theorem mem_factorialDvdPowIdeal {x : R} : x ∈ factorialDvdPowIdeal R ↔ ∀ n, (n ! : R) ∣ x ^ n :=
  Iff.rfl

/-- Ring maps send elements with divided powers to elements with divided powers. -/
theorem map_mem_factorialDvdPowIdeal {S F : Type*} [CommSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {x : R} (hx : x ∈ factorialDvdPowIdeal R) :
    f x ∈ factorialDvdPowIdeal S := fun n ↦ by
  simpa only [map_pow, map_natCast] using map_dvd f (hx n)

/-- A ring map sends `𝔡` into `𝔡`, so it induces a map of the quotients by `𝔡`. -/
theorem factorialDvdPowIdeal_le_comap {S : Type*} [CommSemiring S] (f : R →+* S) :
    factorialDvdPowIdeal R ≤ (factorialDvdPowIdeal S).comap f :=
  fun _ hx ↦ map_mem_factorialDvdPowIdeal f hx

/-- If `x ∈ 𝔡(R)` and `n ≠ 0`, then `xⁿ ∈ n R`, since `n` divides `n!`. For a commutative ring
`R` and a prime `p`, this is the hypothesis under which `Ideal.frobeniusQuot` is a ring map
`R ⧸ 𝔡(R) →+* R ⧸ p`, `x ↦ x ^ p`. -/
theorem pow_mem_span_natCast_of_mem_factorialDvdPowIdeal {x : R}
    (hx : x ∈ factorialDvdPowIdeal R) {n : ℕ} (hn : n ≠ 0) : x ^ n ∈ Ideal.span {(n : R)} :=
  Ideal.mem_span_singleton.mpr <|
    (Nat.cast_dvd_cast (Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl)).trans (hx n)

end Semiring

/-- **An ideal with divided powers consists of elements with divided powers**: `xⁿ = n! γₙ(x)`. -/
theorem _root_.DividedPowers.le_factorialDvdPowIdeal {A : Type*} [CommSemiring A] {I : Ideal A}
    (hI : DividedPowers I) : I ≤ factorialDvdPowIdeal A :=
  fun _ hx n ↦ ⟨hI.dpow n _, (hI.factorial_mul_dpow_eq_pow hx).symm⟩

section Jacobson

variable {S : Type*} [CommRing S] {n : ℕ}

/-- **`n` has divided powers when it lies in the Jacobson radical**, for instance in an
`n`-adically complete ring. For every `k`, write `k! = g m` with `g = gcd(k!, nᵏ)`. A prime `q`
dividing `n` divides `k!` at most `k` times by Legendre's formula, hence divides `g` as often as
`k!`, and does not divide `m`. So `m` is prime to `n`, hence a unit, and `k! ∣ nᵏ`. -/
theorem natCast_mem_factorialDvdPowIdeal (h : (n : S) ∈ Ring.jacobson S) :
    (n : S) ∈ factorialDvdPowIdeal S := by
  intro k
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left (k !) (n ^ k)
  have hcop : Nat.Coprime n m := Nat.coprime_of_dvd fun q hq hqn hqm ↦ by
    -- `q ^ v ∣ gcd(k!, nᵏ)` for the multiplicity `v ≤ k` of `q` in `k!`, so `q ^ (v + 1) ∣ k!`.
    have hv : q ^ (k !).factorization q ∣ Nat.gcd (k !) (n ^ k) :=
      Nat.dvd_gcd (Nat.ordProj_dvd _ _) <| (Nat.pow_dvd_pow q <|
        (Nat.factorization_factorial_le_div_pred hq k).trans (Nat.div_le_self _ _)).trans
          (pow_dvd_pow_of_dvd hqn k)
    refine Nat.pow_succ_factorization_not_dvd (Nat.factorial_ne_zero k) hq ?_
    rw [pow_succ]
    exact (mul_dvd_mul hv hqm).trans (dvd_of_eq hm.symm)
  -- `m` is prime to `n`, hence a unit since `n` lies in the Jacobson radical.
  have hu : IsUnit (m : S) := by
    obtain ⟨a, b, hab⟩ := hcop.isCoprime.map (Int.castRingHom S)
    simp only [map_natCast] at hab
    refine isUnit_of_mul_isUnit_right (x := b) ?_
    rw [show b * (m : S) = n * -a + 1 by linear_combination hab]
    exact Ring.mem_jacobson_iff.mp h (-a)
  rw [hm, Nat.cast_mul, hu.mul_right_dvd, ← Nat.cast_pow]
  exact Nat.cast_dvd_cast (Nat.gcd_dvd_right _ _)

/-- If a nonzero `n` lies in the Jacobson radical, so does `𝔡(S)`: every `x ∈ 𝔡(S)` has
`xⁿ ∈ n S`. -/
theorem factorialDvdPowIdeal_le_jacobson (hn : n ≠ 0) (h : (n : S) ∈ Ring.jacobson S) :
    factorialDvdPowIdeal S ≤ Ring.jacobson S := fun x hx ↦ by
  rw [← Ideal.jacobson_bot] at h ⊢
  exact Ideal.isRadical_jacobson ⊥ ⟨n, (Ideal.span_singleton_le_iff_mem _).mpr h
    (pow_mem_span_natCast_of_mem_factorialDvdPowIdeal hx hn)⟩

/-- If a nonzero `n` lies in the Jacobson radical, then `S → S ⧸ 𝔡(S)` is a local homomorphism:
an element is a unit as soon as its class modulo `𝔡(S)` is. -/
theorem isLocalHom_mk_factorialDvdPowIdeal (hn : n ≠ 0) (h : (n : S) ∈ Ring.jacobson S) :
    IsLocalHom (Ideal.Quotient.mk (factorialDvdPowIdeal S)) :=
  isLocalHom_of_le_jacobson (factorialDvdPowIdeal_le_jacobson hn h)

variable (S n) in
/-- **`n` has divided powers in an `n`-adically complete ring**: `n S ≤ 𝔡(S)`, so the reduction
`S ⧸ n → S ⧸ 𝔡(S)` is `Ideal.Quotient.factor (span_natCast_le_factorialDvdPowIdeal S n)`. -/
theorem span_natCast_le_factorialDvdPowIdeal [IsAdicComplete (Ideal.span {(n : S)}) S] :
    Ideal.span {(n : S)} ≤ factorialDvdPowIdeal S :=
  (Ideal.span_singleton_le_iff_mem _).mpr <| natCast_mem_factorialDvdPowIdeal <|
    IsAdicComplete.le_jacobson _ (Ideal.mem_span_singleton_self _)

end Jacobson

section Perfect

variable {S : Type*} [CommRing S] {p : ℕ} [hp : Fact p.Prime]
  [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- **Teichmüller lifts modulo `𝔡`.** Let `S` be `p`-adically complete and `M` a commutative
monoid on which `x ↦ x ^ p` is bijective. Then composition with `S → S ⧸ 𝔡(S)` is a bijection from
monoid maps `M →* S` to monoid maps `M →* S ⧸ 𝔡(S)`. -/
theorem bijective_mk_factorialDvdPowIdeal_comp_monoidHom {M : Type*} [CommMonoid M]
    [PerfectRing M p] :
    Function.Bijective fun f : M →* S ↦
      (Ideal.Quotient.mk (factorialDvdPowIdeal S) : S →* S ⧸ factorialDvdPowIdeal S).comp f :=
  IsAdicComplete.bijective_mk_comp_monoidHom
    (span_natCast_le_factorialDvdPowIdeal S p (Ideal.mem_span_singleton_self _))
    (span_natCast_le_factorialDvdPowIdeal S p) fun _ hx ↦
      pow_mem_span_natCast_of_mem_factorialDvdPowIdeal hx hp.out.ne_zero

/-- **Witt vector lifts modulo `𝔡`.** Let `S` be `p`-adically complete and `k` a perfect ring of
characteristic `p`. Every ring map `f : k →+* S ⧸ 𝔡(S)` has exactly one lift `g : 𝕎 k →+* S` with
`g x ≡ f x₀` modulo `𝔡(S)`, where `x₀` is the `0`-th Witt coordinate of `x`. -/
theorem WittVector.existsUnique_mk_factorialDvdPowIdeal_comp_eq_comp_constantCoeff
    {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
    (f : k →+* S ⧸ factorialDvdPowIdeal S) :
    ∃! g : _root_.WittVector p k →+* S,
      (Ideal.Quotient.mk (factorialDvdPowIdeal S)).comp g =
        f.comp _root_.WittVector.constantCoeff :=
  existsUnique_mk_comp_eq_comp_constantCoeff (I := Ideal.span {(p : S)})
    (span_natCast_le_factorialDvdPowIdeal S p)
    (fun _ hx ↦ pow_mem_span_natCast_of_mem_factorialDvdPowIdeal hx hp.out.ne_zero) f

end Perfect

end TauCeti
