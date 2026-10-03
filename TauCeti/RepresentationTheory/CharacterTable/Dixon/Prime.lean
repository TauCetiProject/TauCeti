/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimesCongruentOne
public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.Data.ZMod.ValMinAbs
public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RingTheory.ZMod.PrimitiveRoot
public import TauCeti.RingTheory.ZMod.Torsion

/-!
# Good Dixon primes

The Burnside--Dixon--Schneider algorithm computes the complex character table of a finite group
`G` by working over a finite prime field `ZMod p` and lifting the answer back. The prime it works
over cannot be arbitrary: it has to make `ZMod p` behave, for the purposes of the computation, like
`ℂ`, and it has to be large enough that the lift is unambiguous. This file isolates that condition
as `TauCeti.IsGoodDixonPrime` and proves what it buys.

Three arithmetic conditions do the work. That `p` does not divide `|G|` makes `ZMod p [G]`
semisimple, by Maschke. That the exponent `e` of `G` divides `p - 1` makes every element of `G` act
with eigenvalues in `ZMod p`, because the `e`-th roots of unity are already there: `ZMod p` contains
a primitive `e`-th root of unity and `X ^ e - 1` splits into distinct linear factors over it. And
Dixon's size bound `2⌊√|G|⌋ < p` opens a residue window wide enough that an integer of absolute
value at most `√|G|` -- the size of the coefficients the algorithm has to reconstruct -- is
determined by its residue modulo `p`.

Such primes always exist: there are arbitrarily large primes congruent to `1` modulo `e`
(`Nat.exists_prime_gt_modEq_one`, itself a cyclotomic-polynomial argument), and any of them beyond
`max |G| (2⌊√|G|⌋)` is good. The existence proof is not part of any computation. What the
computation does instead is search: `TauCeti.DixonPrimeData.candidates` tests the numbers
`e + 1, 2e + 1, 3e + 1, …` in turn, keeps the good primes among them, and pairs each with the least
primitive `e`-th root of unity modulo it (`TauCeti.ZMod.primitiveRoot?`). The existence theorem
then says that the search reaches every good prime once it runs far enough
(`TauCeti.DixonPrimeData.exists_mem_candidates`).

## Main definitions

* `TauCeti.IsGoodDixonPrime`: the good-prime predicate.
* `TauCeti.DixonPrimeData`: a good prime together with a choice of primitive `e`-th root of unity
  modulo it, the data the algorithm consumes.
* `TauCeti.DixonPrimeData.ofPrime?`: the Dixon prime data at a given prime, if it is good.
* `TauCeti.DixonPrimeData.candidates`: the Dixon prime data at the good primes among the first
  numbers congruent to `1` modulo the exponent.

## Main results

* `TauCeti.IsGoodDixonPrime.isSemisimpleRing`: the modular group algebra is semisimple.
* `TauCeti.IsGoodDixonPrime.exists_isPrimitiveRoot` and
  `TauCeti.IsGoodDixonPrime.splits_X_pow_exponent_sub_one`: `ZMod p` splits `X ^ e - 1`.
* `TauCeti.IsGoodDixonPrime.card_nthRootsFinset`: that splitting has `e` distinct roots.
* `TauCeti.IsGoodDixonPrime.isSemisimple_apply`: every group element acts semisimply in a
  representation over `ZMod p`.
* `TauCeti.IsGoodDixonPrime.two_mul_natAbs_lt_of_natAbs_le_sqrt`,
  `TauCeti.IsGoodDixonPrime.valMinAbs_intCast_of_natAbs_le_sqrt` and
  `TauCeti.IsGoodDixonPrime.eq_of_intCast_eq_of_natAbs_le_sqrt`: an integer bounded by `√|G|` is
  recovered from, and so determined by, its residue modulo `p`. This is what the size bound is
  for.
* `TauCeti.exists_isGoodDixonPrime`: **good Dixon primes exist** for every finite group.
* `TauCeti.DixonPrimeData.isSome_ofPrime?_iff`: the data at `p` is found exactly when `p` is a
  good Dixon prime.
* `TauCeti.DixonPrimeData.mem_candidates_iff` and `TauCeti.DixonPrimeData.exists_mem_candidates`:
  the search returns the data at every good prime within its range, and nothing else.

## Implementation notes

`TauCeti.DixonPrimeData` carries the primitive root as a field rather than choosing one with the
axiom of choice, because the algorithm that consumes it is meant to run: a noncomputable root would
make every downstream `def` noncomputable. The existence statement is therefore phrased twice, once
as the proposition `TauCeti.exists_isGoodDixonPrime` and once as
`TauCeti.instNonemptyDixonPrimeData`.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "Certified Dixon prime data".
-/

public section

namespace TauCeti

open Polynomial

/-! ### The good-prime predicate -/

/-- **`p` is a good Dixon prime for `G`**: it is prime, it does not divide `|G|`, the exponent of
`G` divides `p - 1`, and it exceeds Dixon's size bound `2⌊√|G|⌋`.

These are exactly the arithmetic hypotheses under which the Burnside--Dixon--Schneider algorithm
runs: `not_dvd_natCard` makes `ZMod p [G]` semisimple, `exponent_dvd` puts the `e`-th roots of
unity into `ZMod p`, and `two_mul_sqrt_lt` makes the lift back to characteristic zero unique. That
the reduced central characters stay pairwise distinct is *not* part of the definition; it is a
consequence, the content of the good-prime structure theorem. -/
structure IsGoodDixonPrime (G : Type*) [Group G] (p : ℕ) : Prop where
  /-- `p` is prime, so that `ZMod p` is a field. -/
  prime : p.Prime
  /-- `p` does not divide `|G|`, so that Maschke applies over `ZMod p`. -/
  not_dvd_natCard : ¬p ∣ Nat.card G
  /-- The exponent of `G` divides `p - 1`, so that the `e`-th roots of unity lie in `ZMod p`. -/
  exponent_dvd : Monoid.exponent G ∣ p - 1
  /-- Dixon's size bound, which makes the lift back to characteristic zero unique. -/
  two_mul_sqrt_lt : 2 * Nat.sqrt (Nat.card G) < p

namespace IsGoodDixonPrime

variable {G : Type*} [Group G] {p : ℕ}

/-- The primality of a good Dixon prime, as the `Fact` that the field structure on `ZMod p` is
found from. -/
theorem fact_prime (hp : IsGoodDixonPrime G p) : Fact p.Prime := ⟨hp.prime⟩

/-- **A group with a good Dixon prime is finite.** Every natural number divides `0`, so `p ∤ |G|`
already rules out `Nat.card G = 0`; finiteness need not be assumed separately. -/
theorem finite (hp : IsGoodDixonPrime G p) : Finite G :=
  Nat.finite_of_card_ne_zero fun h => hp.not_dvd_natCard (h ▸ dvd_zero p)

/-! #### The exponent condition -/

/-- **`ZMod p` contains a primitive root of unity of order the exponent of `G`.** This is the
exponent condition at work: the exponent divides `p - 1`, and `ZMod p` has the roots of unity of
every order dividing `p - 1`, by `TauCeti.ZMod.exists_isPrimitiveRoot_of_dvd_sub_one`. -/
theorem exists_isPrimitiveRoot (hp : IsGoodDixonPrime G p) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ (Monoid.exponent G) :=
  ZMod.exists_isPrimitiveRoot_of_dvd_sub_one hp.prime hp.exponent_dvd

/-! #### The order condition: Maschke -/

/-- The order of `G` is invertible modulo a good Dixon prime. -/
theorem natCast_natCard_ne_zero (hp : IsGoodDixonPrime G p) : (Nat.card G : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hp.not_dvd_natCard

theorem neZero_natCast_natCard (hp : IsGoodDixonPrime G p) : NeZero ((Nat.card G : ZMod p)) :=
  ⟨hp.natCast_natCard_ne_zero⟩

/-- **Maschke's theorem at a good Dixon prime**: the modular group algebra `ZMod p [G]` is a
semisimple ring. -/
theorem isSemisimpleRing (hp : IsGoodDixonPrime G p) :
    IsSemisimpleRing (MonoidAlgebra (ZMod p) G) := by
  have := hp.fact_prime
  have := hp.finite
  have := hp.neZero_natCast_natCard
  infer_instance

/-! #### Splitting the roots of unity -/

/-- **`X ^ e - 1` splits over `ZMod p`**, `e` the exponent of `G`: this is the sense in which a
good Dixon prime makes `ZMod p` a substitute for `ℂ`. -/
theorem splits_X_pow_exponent_sub_one (hp : IsGoodDixonPrime G p) :
    (X ^ Monoid.exponent G - 1 : (ZMod p)[X]).Splits := by
  have := hp.fact_prime
  obtain ⟨ζ, hζ⟩ := hp.exists_isPrimitiveRoot
  simpa using X_pow_sub_one_splits hζ

/-- The `e`-th roots of unity in `ZMod p` are `e` in number: `X ^ e - 1` splits with *distinct*
roots, which is what makes the elements of `G` act semisimply.

The `Fact` instance is redundant with `hp.prime`, but it cannot be dropped:
`Polynomial.nthRootsFinset` is defined only over an `IsDomain`, and `IsDomain (ZMod p)` is found
from `Fact p.Prime`, so without the instance argument the *statement* fails to elaborate. Deriving
it inside the proof is therefore not an option, unlike in
`TauCeti.IsGoodDixonPrime.splits_X_pow_exponent_sub_one`, whose `Polynomial.Splits` is defined over
any commutative ring. -/
theorem card_nthRootsFinset [Fact p.Prime] (hp : IsGoodDixonPrime G p) :
    (nthRootsFinset (Monoid.exponent G) (1 : ZMod p)).card = Monoid.exponent G := by
  obtain ⟨ζ, hζ⟩ := hp.exists_isPrimitiveRoot
  exact hζ.card_nthRootsFinset

/-! #### The size condition: the residue window -/

theorem neZero (hp : IsGoodDixonPrime G p) : NeZero p := ⟨hp.prime.ne_zero⟩

/-- **Dixon's size bound in the shape the residue window asks for.** An integer of absolute value
at most `⌊√|G|⌋` lies strictly inside the window of half-width `p / 2`, since `2⌊√|G|⌋ < p`. -/
theorem two_mul_natAbs_lt_of_natAbs_le_sqrt (hp : IsGoodDixonPrime G p) {z : ℤ}
    (hz : z.natAbs ≤ Nat.sqrt (Nat.card G)) : 2 * z.natAbs < p := by
  have := hp.two_mul_sqrt_lt
  omega

/-- **The certified rational-integer lift at a good Dixon prime.** Dixon's size bound opens a
residue window wide enough that an integer of absolute value at most `⌊√|G|⌋` is returned by
`ZMod.valMinAbs` from its residue. This is the first stage of the cyclotomic lift: a rational
character value, reduced modulo `p`, is recovered exactly. -/
theorem valMinAbs_intCast_of_natAbs_le_sqrt (hp : IsGoodDixonPrime G p) {z : ℤ}
    (hz : z.natAbs ≤ Nat.sqrt (Nat.card G)) : ((z : ZMod p)).valMinAbs = z :=
  ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt (hp.two_mul_natAbs_lt_of_natAbs_le_sqrt hz)

/-- **Dixon's size bound opens a wide enough residue window.** Two integers of absolute value at
most `⌊√|G|⌋` that agree modulo `p` are equal, so an integer of that size is determined by its
residue. This is why the lift is unambiguous. -/
theorem eq_of_intCast_eq_of_natAbs_le_sqrt (hp : IsGoodDixonPrime G p) {z w : ℤ}
    (hz : z.natAbs ≤ Nat.sqrt (Nat.card G)) (hw : w.natAbs ≤ Nat.sqrt (Nat.card G))
    (h : (z : ZMod p) = w) : z = w :=
  ZMod.eq_of_intCast_eq_of_two_mul_natAbs_lt (hp.two_mul_natAbs_lt_of_natAbs_le_sqrt hz)
    (hp.two_mul_natAbs_lt_of_natAbs_le_sqrt hw) h

/-! #### Representations over `ZMod p` -/

section Representation

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- **At a good Dixon prime every group element acts semisimply.** This is
`TauCeti.Representation.isSemisimple_apply` at the invertibility of `|G|` that the good-prime
certificate supplies. -/
theorem isSemisimple_apply (hp : IsGoodDixonPrime G p)
    (ρ : Representation (ZMod p) G V) (g : G) : Module.End.IsSemisimple (ρ g) :=
  have := hp.fact_prime
  Representation.isSemisimple_apply ρ hp.natCast_natCard_ne_zero g

end Representation

end IsGoodDixonPrime

/-! ### Existence -/

/-- **Good Dixon primes exist.** Take a prime congruent to `1` modulo the exponent of `G` and
larger than `max |G| (2⌊√|G|⌋)`, the second half being Dixon's size bound; there are arbitrarily
large such primes. This is a statement about the algorithm, not a step in it: a concrete group is
handed a concrete prime instead. -/
theorem exists_isGoodDixonPrime (G : Type*) [Group G] [Finite G] :
    ∃ p : ℕ, IsGoodDixonPrime G p := by
  obtain ⟨p, hprime, hgt, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (k := Monoid.exponent G)
      (max (Nat.card G) (2 * Nat.sqrt (Nat.card G))) Monoid.exponent_ne_zero_of_finite
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hlt : Nat.card G < p := lt_of_le_of_lt (le_max_left _ _) hgt
  refine ⟨p, hprime, fun hdvd => ?_, ?_, lt_of_le_of_lt (le_max_right _ _) hgt⟩
  · exact absurd (Nat.le_of_dvd hcard hdvd) (by omega)
  · exact (Nat.modEq_iff_dvd' hprime.one_lt.le).1 hmod.symm

/-- The data the Burnside--Dixon--Schneider algorithm runs on: a good Dixon prime `p` for `G`
together with a chosen primitive `e`-th root of unity modulo `p`, `e` the exponent of `G`. The root
is data rather than a choice made by `exists_isPrimitiveRoot`, so that the definitions consuming it
stay computable. -/
@[ext]
structure DixonPrimeData (G : Type*) [Group G] where
  /-- The prime the algorithm reduces modulo. -/
  p : ℕ
  /-- The primitive `e`-th root of unity modulo `p`, `e` the exponent of `G`, that the finite-field
  computation runs with. -/
  root : ZMod p
  /-- The certificate that `p` is a good Dixon prime. -/
  isGoodDixonPrime : IsGoodDixonPrime G p
  /-- The certificate that `root` is a primitive `e`-th root of unity. -/
  isPrimitiveRoot_root : IsPrimitiveRoot root (Monoid.exponent G)

namespace DixonPrimeData

variable {G : Type*} [Group G] (d : DixonPrimeData G)

/-- The prime is prime, as the `Fact` the field structure on `ZMod d.p` is found from. Unlike for
the hypothesis `IsGoodDixonPrime`, this can be an instance, because `d` is data. -/
instance fact_prime : Fact d.p.Prime := ⟨d.isGoodDixonPrime.prime⟩

instance neZero : NeZero d.p := d.isGoodDixonPrime.neZero

/-- The chosen root has order exactly the exponent of `G`. -/
@[simp]
theorem orderOf_root : orderOf d.root = Monoid.exponent G :=
  d.isPrimitiveRoot_root.eq_orderOf.symm

/-- The defining property of the chosen root: it is an `e`-th root of unity, `e` the exponent of
`G`. -/
@[simp]
theorem root_pow_exponent_eq_one : d.root ^ Monoid.exponent G = 1 :=
  d.isPrimitiveRoot_root.pow_eq_one

/-- The chosen root is a unit, so the finite-field computation may divide by it. -/
theorem isUnit_root : IsUnit d.root :=
  have := d.isGoodDixonPrime.finite
  d.isPrimitiveRoot_root.isUnit Monoid.exponent_ne_zero_of_finite

theorem root_ne_zero : d.root ≠ 0 := d.isUnit_root.ne_zero

end DixonPrimeData

/-- Every finite group admits Dixon prime data. The witness is noncomputable; a computation that
needs the data finds it with `TauCeti.DixonPrimeData.candidates` instead. -/
instance instNonemptyDixonPrimeData (G : Type*) [Group G] [Finite G] :
    Nonempty (DixonPrimeData G) := by
  obtain ⟨p, hp⟩ := exists_isGoodDixonPrime G
  obtain ⟨ζ, hζ⟩ := hp.exists_isPrimitiveRoot
  exact ⟨⟨p, ζ, hp, hζ⟩⟩

/-! ### Searching for Dixon prime data

The order and the exponent of `G` enter the search as natural numbers `n` and `e`, together with
proofs that they are `Nat.card G` and `Monoid.exponent G`: Mathlib's `Monoid.exponent` is
noncomputable, and a caller that runs the search supplies the two numbers it already knows. -/

namespace DixonPrimeData

variable {G : Type*} [Group G] (e : ℕ) (he : e = Monoid.exponent G) (n : ℕ) (hn : n = Nat.card G)

/-- **The Dixon prime data at `p`, if `p` is a good Dixon prime.** The four arithmetic conditions
of `TauCeti.IsGoodDixonPrime` are decided on the numbers `n` and `e`, and the primitive root is the
least one modulo `p` (`TauCeti.ZMod.primitiveRoot?`). -/
def ofPrime? (p : ℕ) : Option (DixonPrimeData G) :=
  if hp : p.Prime ∧ ¬p ∣ n ∧ e ∣ p - 1 ∧ 2 * Nat.sqrt n < p then
    (ZMod.primitiveRoot? p e).map fun ζ ↦
      { p
        root := ζ.1
        isGoodDixonPrime := by
          subst he hn
          exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
        isPrimitiveRoot_root := he ▸ ζ.2 }
  else none

variable {e he n hn}

/-- Data returned at `p` lives at the prime `p`. -/
theorem p_eq_of_ofPrime?_eq_some {p : ℕ} {q : DixonPrimeData G}
    (h : ofPrime? e he n hn p = some q) : q.p = p := by
  unfold ofPrime? at h
  split_ifs at h
  obtain ⟨ζ, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- **The data at `p` is found exactly when `p` is a good Dixon prime.** A good prime has a
primitive `e`-th root of unity, so the root search at it cannot fail. -/
theorem isSome_ofPrime?_iff {p : ℕ} : (ofPrime? e he n hn p).isSome ↔ IsGoodDixonPrime G p := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
    exact p_eq_of_ofPrime?_eq_some hq ▸ q.isGoodDixonPrime
  · intro hp
    have := hp.neZero
    have := hp.finite
    subst he hn
    rw [ofPrime?, dite_eq_left_of_eq_true
      (eq_true ⟨hp.prime, hp.not_dvd_natCard, hp.exponent_dvd, hp.two_mul_sqrt_lt⟩),
      Option.isSome_map, ZMod.isSome_primitiveRoot?_iff Monoid.exponent_ne_zero_of_finite]
    exact hp.exists_isPrimitiveRoot

/-- **The search returns given Dixon prime data at its prime** as soon as its root is the one the
primitive-root search finds there. -/
theorem ofPrime?_eq_some {q : DixonPrimeData G}
    (hroot : (ZMod.primitiveRoot? q.p e).map Subtype.val = some q.root) :
    ofPrime? e he n hn q.p = some q := by
  have hp := q.isGoodDixonPrime
  subst he hn
  rw [ofPrime?, dite_eq_left_of_eq_true
    (eq_true ⟨hp.prime, hp.not_dvd_natCard, hp.exponent_dvd, hp.two_mul_sqrt_lt⟩)]
  obtain ⟨ζ, hζ, hval⟩ := Option.map_eq_some_iff.mp hroot
  rw [hζ, Option.map_some]
  exact congrArg some (DixonPrimeData.ext rfl (heq_of_eq hval))

variable (e he n hn)

/-- **The search for Dixon prime data.** The numbers `e (k + 1) + 1` for `k < fuel` are tested in
increasing order, and the Dixon prime data at each good prime among them is kept. When `e ≠ 0`
(for instance when `G` is finite), these are exactly the numbers above `1` and at most
`e · fuel + 1` congruent to `1` modulo `e`. -/
def candidates (fuel : ℕ) : List (DixonPrimeData G) :=
  (List.range fuel).filterMap fun k ↦ ofPrime? e he n hn (e * (k + 1) + 1)

variable {e he n hn}

/-- **The search finds the data at every good prime within its range, and nothing else.** The data
`q` is found within `fuel` steps exactly when it is the data the search computes at its prime and
that prime is at most `e · fuel + 1`. -/
theorem mem_candidates_iff {fuel : ℕ} {q : DixonPrimeData G} :
    q ∈ candidates e he n hn fuel ↔ ofPrime? e he n hn q.p = some q ∧ q.p ≤ e * fuel + 1 := by
  rw [candidates, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hq⟩
    have hp := p_eq_of_ofPrime?_eq_some hq
    rw [List.mem_range] at hk
    refine ⟨hp ▸ hq, hp ▸ ?_⟩
    have : e * (k + 1) ≤ e * fuel := Nat.mul_le_mul_left e hk
    omega
  · rintro ⟨hq, hle⟩
    have hgood := q.isGoodDixonPrime
    have := hgood.finite
    have he0 : 0 < e := he ▸ Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite
    obtain ⟨m, hm⟩ := he ▸ hgood.exponent_dvd
    have htwo := hgood.prime.two_le
    have hm0 : m ≠ 0 := by
      rintro rfl
      omega
    refine ⟨m - 1, List.mem_range.mpr ?_, ?_⟩
    · by_contra hlt
      have hfm : fuel + 1 ≤ m := by omega
      have := Nat.mul_le_mul_left e hfm
      rw [Nat.mul_succ] at this
      omega
    · rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm, Nat.sub_add_cancel (by omega)]

/-- **Every good Dixon prime is reached by the search** once it runs far enough. -/
theorem exists_mem_candidates {p fuel : ℕ} (hp : IsGoodDixonPrime G p) (hfuel : p ≤ e * fuel + 1) :
    ∃ q ∈ candidates e he n hn fuel, q.p = p := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp ((isSome_ofPrime?_iff (he := he) (hn := hn)).mpr hp)
  have hqp := p_eq_of_ofPrime?_eq_some hq
  exact ⟨q, mem_candidates_iff.mpr ⟨hqp ▸ hq, hqp ▸ hfuel⟩, hqp⟩

/-- Running the search longer only appends to what it has already found. -/
theorem candidates_prefix {fuel fuel' : ℕ} (h : fuel ≤ fuel') :
    candidates e he n hn fuel <+: candidates e he n hn fuel' := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [candidates, candidates, List.range_add, List.filterMap_append]
  exact List.prefix_append _ _

end DixonPrimeData

end TauCeti
