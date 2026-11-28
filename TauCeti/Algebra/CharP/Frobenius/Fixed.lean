/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.IntegralDomain

/-!
# The subring and subfield fixed by an iterated Frobenius

Let `A` be a commutative ring of exponential characteristic `p` and let `q = p ^ n`. The elements
of `A` satisfying `a ^ q = a` are the equalizer of the ring homomorphism `iterateFrobenius A p n`
and the identity, hence a subring: this file names it `TauCeti.frobeniusFixedSubring` and records
its elementary properties. Over a field the equalizer is closed under inverses as well, giving
`TauCeti.frobeniusFixedSubfield`.

For `p` prime, `0 < n` and `A` an algebraic closure of `ZMod p` this subring is the field of `q`
elements sitting inside `A`, which is why the construction is the ring-theoretic half of "the fixed
points of the `q`-power Frobenius are the `𝔽_q`-points"; at `n = 0` it is instead the whole of `A`,
since `q = 1`. The general subring statements below are about an arbitrary commutative ring of
exponential characteristic `p` and the subfield ones about an arbitrary field of exponential
characteristic `p`.

The counting statements concern a domain `A` of prime characteristic `p` and `n ≠ 0`. There the
fixed elements are the roots of `X ^ q - X`, so an iterate with `1 < q` moves some element of every
domain, finite or infinite, with more than `q` elements, and the fixed subring is a finite domain,
hence a field. The polynomial `X ^ q - X` has derivative `-1`, so it has no repeated roots: when it
splits over `A`, for instance when `A` is absolutely integrally closed like the tilt of the
valuation ring of `ℂ_p`, the fixed subring has exactly `q` elements.

## Main definitions

* `TauCeti.frobeniusFixedSubring`: the subring of elements fixed by the `p ^ n`-power Frobenius.
* `TauCeti.frobeniusFixedSubfield`: the same elements of a field, as a subfield.

## Main results

* `TauCeti.mem_frobeniusFixedSubring`: membership is the equation `a ^ p ^ n = a`, and
  `TauCeti.mem_frobeniusFixedSubring_one` is its form `a ^ p = a` at `n = 1`.
* `TauCeti.mem_frobeniusFixedSubring_mul_iff_iterate_eq`: at exponent `m * k`, membership is being
  fixed by the `k`-th iterate of the `p ^ m`-power Frobenius.
* `TauCeti.exists_iterateFrobenius_ne`: on a domain of exponential characteristic `p` with more
  than `p ^ n` elements, finite or infinite, the iterate `x ↦ x ^ p ^ n` moves some element when
  `1 < p ^ n`.
* `TauCeti.frobeniusFixedSubring_zero` and `TauCeti.frobeniusFixedSubfield_zero`: the zeroth
  iterate fixes everything.
* `TauCeti.frobeniusFixedSubring_le_of_dvd` and `TauCeti.frobeniusFixedSubfield_le_of_dvd`: the
  fixed subrings and subfields grow along divisibility of the exponent, the inclusion
  `𝔽_{p ^ m} ⊆ 𝔽_{p ^ k}` in the motivating case.
* `TauCeti.frobeniusFixedSubring_inf` and `TauCeti.frobeniusFixedSubfield_inf`: the intersection
  of the fixed structures at exponents `m` and `n` is the one at `m.gcd n`.
* `TauCeti.map_mem_frobeniusFixedSubring` and `TauCeti.map_le_frobeniusFixedSubring`: a monoid
  homomorphism carries fixed elements to fixed elements, and a ring homomorphism maps the fixed
  subring into the fixed subring.
* `TauCeti.mem_frobeniusFixedSubring_iff_mem_roots`: in a domain of characteristic `p` and for
  `n ≠ 0`, the fixed elements are the roots of `X ^ p ^ n - X`.
* `TauCeti.finite_frobeniusFixedSubring` and `TauCeti.isField_frobeniusFixedSubring`: in a domain
  of characteristic `p` and for `n ≠ 0` the fixed subring is finite, and it is a field.
* `TauCeti.natCard_frobeniusFixedSubring_of_splits`: if moreover `X ^ p ^ n - X` splits over the
  domain, the fixed subring has exactly `p ^ n` elements.

## References

Mathlib's `Mathlib/Algebra/CharP/Frobenius.lean` supplies the Frobenius endomorphisms and their
iteration and naturality laws. The fixed subring and subfield use Mathlib's `RingHom.eqLocus` and
`RingHom.eqLocusField` equalizer constructions.
-/

public section

namespace TauCeti

section Ring

variable (A : Type*) [CommRing A] (p n : ℕ) [ExpChar A p]

/-- The subring of elements of `A` fixed by the `p ^ n`-power Frobenius, that is, the solutions of
`a ^ p ^ n = a`. It is the equalizer of `iterateFrobenius A p n` with the identity.

When `p` is prime, `0 < n` and `A` is an algebraic closure of `ZMod p` this is the subring of
`p ^ n` elements, but nothing of the sort is asserted here: `A` is an arbitrary commutative ring of
exponential characteristic `p`, and for `p = 1` — that is, in characteristic zero — or for `n = 0`
the whole of `A` is fixed. -/
def frobeniusFixedSubring : Subring A :=
  (iterateFrobenius A p n).eqLocus (RingHom.id A)

variable {A p n}

/-- Membership in the Frobenius-fixed subring is the equation `a ^ p ^ n = a`. -/
@[simp]
theorem mem_frobeniusFixedSubring {a : A} :
    a ∈ frobeniusFixedSubring A p n ↔ a ^ p ^ n = a := Iff.rfl

/-- Membership in the subring fixed by the `p`-power Frobenius is the equation `a ^ p = a`. -/
theorem mem_frobeniusFixedSubring_one {a : A} :
    a ∈ frobeniusFixedSubring A p 1 ↔ a ^ p = a := by
  rw [mem_frobeniusFixedSubring, pow_one]

/-- At an exponent `m * k`, being fixed by the `p ^ (m * k)`-power Frobenius is being fixed by the
`k`-th iterate of the `p ^ m`-power one, since that iterate *is* the `p ^ (m * k)`-power
Frobenius. -/
theorem mem_frobeniusFixedSubring_mul_iff_iterate_eq {m k : ℕ} {a : A} :
    a ∈ frobeniusFixedSubring A p (m * k) ↔ (iterateFrobenius A p m)^[k] a = a := by
  rw [mem_frobeniusFixedSubring, ← iterateFrobenius_def, iterateFrobenius_mul_apply]

/-- **An iterated Frobenius moves some element of a large domain.** On a domain of exponential
characteristic `p` with more than `p ^ n` elements, finite or infinite, the iterate
`x ↦ x ^ p ^ n` is not the identity, provided `1 < p ^ n`: its fixed elements are roots of
`X ^ p ^ n - X`, of which there are at most `p ^ n`. The witness is a point where this polynomial
does not vanish, supplied by Mathlib's `Polynomial.exists_eval_ne_zero_of_natDegree_lt_card`. -/
theorem exists_iterateFrobenius_ne [IsDomain A] (hq : 1 < p ^ n)
    (hA : (p ^ n : ℕ) < Cardinal.mk A) : ∃ s : A, iterateFrobenius A p n s ≠ s := by
  -- A point where `X ^ p ^ n - X` does not vanish is one that the iterate moves.
  obtain ⟨s, hs⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _
    (Polynomial.X_pow_sub_X_ne_zero (R := A) hq) (by rwa [Polynomial.natDegree_X_pow_sub_X hq])
  refine ⟨s, fun h ↦ hs ?_⟩
  rw [iterateFrobenius_def] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, h, sub_self]

variable (A p n)

/-- The zeroth Frobenius iterate is the identity, so it fixes every element. -/
@[simp]
theorem frobeniusFixedSubring_zero : frobeniusFixedSubring A p 0 = ⊤ := by
  refine Subring.ext fun a => ?_
  simp

variable {A p n}

/-- Fixed subrings grow along divisibility of the exponent: an element fixed by the `p ^ m`-power
Frobenius is fixed by the `p ^ k`-power Frobenius whenever `m ∣ k`. In the motivating case this is
the inclusion `𝔽_{p ^ m} ⊆ 𝔽_{p ^ k}` of subfields of an algebraic closure. -/
theorem frobeniusFixedSubring_le_of_dvd {m k : ℕ} (h : m ∣ k) :
    frobeniusFixedSubring A p m ≤ frobeniusFixedSubring A p k := by
  obtain ⟨c, rfl⟩ := h
  intro a ha
  -- membership is `RingHom.eqLocus` membership by definition, so it *is* the equation
  -- `iterateFrobenius A p m a = a`; Mathlib's `RingHom.mem_eqLocus` is the bridge.
  exact mem_frobeniusFixedSubring_mul_iff_iterate_eq.mpr
    (Function.iterate_fixed (RingHom.mem_eqLocus.mp ha) c)

/-- The intersection of two Frobenius-fixed subrings is the fixed subring at the gcd of their
exponents. This also holds for zero exponents and does not require Frobenius to be injective. -/
@[simp]
theorem frobeniusFixedSubring_inf (m n : ℕ) :
    frobeniusFixedSubring A p m ⊓ frobeniusFixedSubring A p n =
      frobeniusFixedSubring A p (m.gcd n) := by
  refine le_antisymm ?_ (le_inf (frobeniusFixedSubring_le_of_dvd (Nat.gcd_dvd_left m n))
    (frobeniusFixedSubring_le_of_dvd (Nat.gcd_dvd_right m n)))
  rintro a ⟨hm, hn⟩
  -- membership at exponent `k` is `a` being a period-`k` point of the `p`-power Frobenius
  have key (k : ℕ) :
      a ∈ frobeniusFixedSubring A p k ↔ Function.IsPeriodicPt (frobenius A p) k a := by
    rw [mem_frobeniusFixedSubring, Function.IsPeriodicPt, Function.IsFixedPt, iterate_frobenius]
  exact (key _).mpr (((key m).mp hm).gcd ((key n).mp hn))

variable {B : Type*} [CommRing B] [ExpChar B p]

/-- A monoid homomorphism commutes with powers, so it carries elements fixed by the
`p ^ n`-power Frobenius to elements fixed by it. -/
theorem map_mem_frobeniusFixedSubring {F : Type*} [FunLike F A B] [MonoidHomClass F A B] (φ : F)
    {a : A} (ha : a ∈ frobeniusFixedSubring A p n) : φ a ∈ frobeniusFixedSubring B p n := by
  rw [mem_frobeniusFixedSubring, ← map_pow, mem_frobeniusFixedSubring.mp ha]

/-- A ring homomorphism maps the subring fixed by the `p ^ n`-power Frobenius into the
corresponding fixed subring: the subring form of `map_mem_frobeniusFixedSubring`. -/
theorem map_le_frobeniusFixedSubring (φ : A →+* B) :
    (frobeniusFixedSubring A p n).map φ ≤ frobeniusFixedSubring B p n := by
  rintro _ ⟨a, ha, rfl⟩
  exact map_mem_frobeniusFixedSubring φ ha

end Ring

section Domain

open Polynomial

variable (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p] {n : ℕ}

/-- In a domain of characteristic `p` and for `n ≠ 0`, being fixed by the `p ^ n`-power Frobenius
is being a root of `X ^ p ^ n - X`. At `n = 0` the two sides differ: the subring is the whole of
`A`, while `X ^ 1 - X = 0` has no roots. -/
theorem mem_frobeniusFixedSubring_iff_mem_roots (hn : n ≠ 0) {a : A} :
    a ∈ frobeniusFixedSubring A p n ↔ a ∈ (X ^ p ^ n - X : A[X]).roots := by
  rw [mem_roots (X_pow_sub_X_ne_zero (Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt)),
    mem_frobeniusFixedSubring, IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]

/-- The Frobenius-fixed subring of a domain of characteristic `p` is finite once `n ≠ 0`, being a
set of roots of a nonzero polynomial. This is not an instance: at `n = 0` the subring is the whole
of `A`, which need not be finite. -/
theorem finite_frobeniusFixedSubring (n : ℕ) (hn : n ≠ 0) :
    Finite ↥(frobeniusFixedSubring A p n) :=
  ((X ^ p ^ n - X : A[X]).roots.finite_toSet.subset
    fun _ ha ↦ (mem_frobeniusFixedSubring_iff_mem_roots A p hn).mp ha).to_subtype

/-- **The Frobenius-fixed subring of a domain is a field.** In a domain of characteristic `p` and
for `n ≠ 0`, the subring fixed by the `p ^ n`-power Frobenius is a finite domain, hence a field. -/
theorem isField_frobeniusFixedSubring (hn : n ≠ 0) : IsField ↥(frobeniusFixedSubring A p n) :=
  have := finite_frobeniusFixedSubring A p n hn
  Finite.isField_of_domain _

/-- **The field of `q` elements inside a domain over which `X ^ q - X` splits.** In a domain of
characteristic `p` over which `X ^ p ^ n - X` splits, for instance an absolutely integrally closed
one, and for `n ≠ 0`, the subring fixed by the `p ^ n`-power Frobenius has exactly `p ^ n`
elements: the polynomial has derivative `-1`, so its roots are simple and there are as many of
them as its degree. -/
theorem natCard_frobeniusFixedSubring_of_splits (hn : n ≠ 0)
    (hs : (X ^ p ^ n - X : A[X]).Splits) : Nat.card ↥(frobeniusFixedSubring A p n) = p ^ n := by
  classical
  have hnodup : (X ^ p ^ n - X : A[X]).roots.Nodup :=
    nodup_roots (galois_poly_separable p (p ^ n) (dvd_pow_self p hn))
  -- the fixed elements are the distinct roots, of which there are as many as the degree
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun a ↦
      (mem_frobeniusFixedSubring_iff_mem_roots A p hn).trans Multiset.mem_toFinset.symm),
    Nat.card_eq_finsetCard, Multiset.toFinset_card_of_nodup hnodup,
    ← hs.natDegree_eq_card_roots,
    natDegree_X_pow_sub_X (Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt)]

end Domain

section Field

variable (K : Type*) [Field K] (p n : ℕ) [ExpChar K p]

/-- The subfield of elements of a field `K` fixed by the `p ^ n`-power Frobenius, that is, the
solutions of `a ^ p ^ n = a`. It is the equalizer of `iterateFrobenius K p n` with the identity,
taken as a subfield: over a field the equalizer is closed under inverses, since
`(a⁻¹) ^ p ^ n = (a ^ p ^ n)⁻¹`.

As with the subring, nothing about finiteness is asserted at this level of generality: at `n = 0`,
or in characteristic zero, it is the whole of `K`. -/
def frobeniusFixedSubfield : Subfield K :=
  (iterateFrobenius K p n).eqLocusField (RingHom.id K)

variable {K p n}

/-- Membership in the Frobenius-fixed subfield is the equation `a ^ p ^ n = a`. -/
@[simp]
theorem mem_frobeniusFixedSubfield {a : K} :
    a ∈ frobeniusFixedSubfield K p n ↔ a ^ p ^ n = a := Iff.rfl

variable (K p n)

/-- The Frobenius-fixed subfield has the Frobenius-fixed subring as its underlying subring. -/
@[simp]
theorem toSubring_frobeniusFixedSubfield :
    (frobeniusFixedSubfield K p n).toSubring = frobeniusFixedSubring K p n := (rfl)

/-- The zeroth Frobenius iterate is the identity, so it fixes every element. -/
@[simp]
theorem frobeniusFixedSubfield_zero : frobeniusFixedSubfield K p 0 = ⊤ := by
  ext a
  simp

variable {K p n}

/-- Fixed subfields grow along divisibility of the exponent, the subfield form of
`frobeniusFixedSubring_le_of_dvd`: in the motivating case this is the inclusion
`𝔽_{p ^ m} ⊆ 𝔽_{p ^ k}` of subfields of an algebraic closure. -/
theorem frobeniusFixedSubfield_le_of_dvd {m k : ℕ} (h : m ∣ k) :
    frobeniusFixedSubfield K p m ≤ frobeniusFixedSubfield K p k := by
  intro a ha
  rw [← Subfield.mem_toSubring, toSubring_frobeniusFixedSubfield] at ha ⊢
  exact frobeniusFixedSubring_le_of_dvd h ha

/-- The intersection of two Frobenius-fixed subfields is the fixed subfield at the gcd of their
exponents. -/
@[simp]
theorem frobeniusFixedSubfield_inf (m n : ℕ) :
    frobeniusFixedSubfield K p m ⊓ frobeniusFixedSubfield K p n =
      frobeniusFixedSubfield K p (m.gcd n) := by
  ext a
  rw [Subfield.mem_inf]
  simp only [← Subfield.mem_toSubring, toSubring_frobeniusFixedSubfield]
  rw [← Subring.mem_inf, frobeniusFixedSubring_inf]

end Field

end TauCeti
