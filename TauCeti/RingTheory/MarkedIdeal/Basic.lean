/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import TauCeti.RingTheory.Ideal.Order.Basic
public import TauCeti.RingTheory.RegularLocalRing.AssociatedGraded

/-!
# Marked ideals on a commutative ring

A marked ideal `(I, d)` on a commutative ring `R` is an ideal `I` together with a positive integer
mark `d`. Its cosupport is the set of primes `p` at which `I` has local order at least `d`, that
is, at which the localization `I_p` lies in the `d`-th power of the maximal ideal of `R_p`. For
mark one this is the zero locus of `I`; larger marks record the multiplicity of `I` rather than
its reduced support.

Two operations of Bierstone–Milman act on marked ideals:

* rescaling `(I, d) ↦ (Iᵏ, k d)` for `k > 0`, which passes to a common mark;
* the marked sum `(I, a) + (J, b) = (Iᵇ + Jᵃ, a b)`, in which each ideal is raised to the mark of
  the other summand.

At every prime the cosupport only grows under rescaling, and the marked sum cosupport contains
the intersection of the two cosupports. At a prime whose localization is a regular local ring, or
more generally whose local ring has an associated graded ring without zero divisors, the order of
ideals is multiplicative (`Ideal.orderAt_pow`), which turns both inclusions into equalities.
Over a regular ring, rescaling therefore preserves the cosupport and the cosupport of a marked sum
is the intersection of the cosupports. The regularity is needed: in `k[ε] ⧸ (ε²)` the
maximal ideal `𝔪` has order one and `𝔪²` has order `∞`, so `(𝔪, 2)` has empty cosupport while
`(𝔪², 4)` has full cosupport.

## Main definitions

* `TauCeti.MarkedIdeal`: an ideal with a positive integer mark.
* `TauCeti.MarkedIdeal.cosupport`: the primes at which the order of the ideal reaches the mark.
* `TauCeti.MarkedIdeal.pow`: rescaling `(I, d) ↦ (Iᵏ, k d)`.
* `TauCeti.MarkedIdeal.sum`: the marked sum `(Iᵇ + Jᵃ, a b)`.

## Main results

* `TauCeti.MarkedIdeal.cosupport_eq_zeroLocus_of_mark_eq_one`: mark one gives the zero locus.
* `TauCeti.MarkedIdeal.cosupport_pow`: over a regular ring, rescaling preserves the cosupport.
* `TauCeti.MarkedIdeal.cosupport_sum`: over a regular ring, the cosupport of a marked sum is the
  intersection of the cosupports.

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2 and
  Construction 4.23.
-/

public section

namespace TauCeti

open _root_.IsLocalRing

/-- A marked ideal on a commutative ring: an ideal `I` together with a positive integer mark `d`,
recording the condition that `I` vanishes to order at least `d`. -/
@[ext]
structure MarkedIdeal (R : Type*) [CommRing R] where
  /-- The underlying ideal. -/
  ideal : Ideal R
  /-- The mark: the order to which the ideal is required to vanish. -/
  mark : ℕ
  /-- The mark is positive. -/
  mark_pos : 0 < mark

namespace MarkedIdeal

variable {R : Type*} [CommRing R]

/-- The mark of a marked ideal is nonzero. -/
instance (P : MarkedIdeal R) : NeZero P.mark := ⟨P.mark_pos.ne'⟩

/-- The cosupport of a marked ideal `(I, d)`: the primes at which `I` has local order at
least `d`. -/
def cosupport (P : MarkedIdeal R) : Set (PrimeSpectrum R) :=
  {p | (P.mark : ℕ∞) ≤ P.ideal.orderAt p}

/-- The defining threshold locus of `MarkedIdeal.cosupport`. -/
theorem cosupport_def (P : MarkedIdeal R) :
    P.cosupport = {p | (P.mark : ℕ∞) ≤ P.ideal.orderAt p} := (rfl)

/-- A prime lies in the cosupport exactly when the order of the ideal there reaches the mark. -/
@[simp]
theorem mem_cosupport_iff (P : MarkedIdeal R) (p : PrimeSpectrum R) :
    p ∈ P.cosupport ↔ (P.mark : ℕ∞) ≤ P.ideal.orderAt p := (Iff.rfl)

/-- A prime lies in the cosupport exactly when the localized ideal lies in the power of the
maximal ideal given by the mark. -/
theorem mem_cosupport_iff_map_le_pow (P : MarkedIdeal R) (p : PrimeSpectrum R) :
    p ∈ P.cosupport ↔ P.ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      maximalIdeal (Localization.AtPrime p.asIdeal) ^ P.mark := by
  rw [mem_cosupport_iff, Ideal.natCast_le_orderAt_iff]

/-- The cosupport of a marked ideal lies in the zero locus of its ideal, since the mark is
positive. -/
theorem cosupport_subset_zeroLocus (P : MarkedIdeal R) :
    P.cosupport ⊆ PrimeSpectrum.zeroLocus P.ideal := fun p hp ↦ by
  have h1 : (1 : ℕ∞) ≤ P.ideal.orderAt p :=
    le_trans (by exact_mod_cast P.mark_pos) ((P.mem_cosupport_iff p).mp hp)
  exact (Ideal.one_le_orderAt_iff P.ideal p).mp h1

/-- For mark one, the cosupport is the zero locus of the ideal. -/
theorem cosupport_eq_zeroLocus_of_mark_eq_one {P : MarkedIdeal R} (h : P.mark = 1) :
    P.cosupport = PrimeSpectrum.zeroLocus P.ideal := by
  ext p
  simp [h, PrimeSpectrum.mem_zeroLocus]

/-- A marked ideal whose ideal is the unit ideal has empty cosupport. -/
theorem cosupport_eq_empty_of_ideal_eq_top {P : MarkedIdeal R} (h : P.ideal = ⊤) :
    P.cosupport = ∅ :=
  Set.subset_empty_iff.mp <| by
    simpa [h] using P.cosupport_subset_zeroLocus

/-- A marked ideal whose ideal is zero has full cosupport. -/
theorem cosupport_eq_univ_of_ideal_eq_bot {P : MarkedIdeal R} (h : P.ideal = ⊥) :
    P.cosupport = Set.univ := by
  ext p
  simp [h]

/-- The unit ideal with any positive mark has empty cosupport. -/
@[simp]
theorem cosupport_top (d : ℕ) (hd : 0 < d) :
    (⟨⊤, d, hd⟩ : MarkedIdeal R).cosupport = ∅ :=
  cosupport_eq_empty_of_ideal_eq_top rfl

/-- The zero ideal with any positive mark has full cosupport. -/
@[simp]
theorem cosupport_bot (d : ℕ) (hd : 0 < d) :
    (⟨⊥, d, hd⟩ : MarkedIdeal R).cosupport = Set.univ :=
  cosupport_eq_univ_of_ideal_eq_bot rfl

/-- The cosupport is antitone: a smaller ideal with a mark that is not larger has a larger
cosupport. -/
theorem cosupport_anti {P Q : MarkedIdeal R} (hI : P.ideal ≤ Q.ideal) (hd : P.mark ≤ Q.mark) :
    Q.cosupport ⊆ P.cosupport := fun p hp ↦
  le_trans (by exact_mod_cast hd) (hp.trans (Ideal.orderAt_anti hI p))

/-- If the ideal of `S` is the sum of the ideals of `A` and `B`, and all three carry the same
mark, then the cosupport of `S` is the intersection of the cosupports of `A` and `B`. -/
theorem cosupport_eq_inter_of_ideal_eq_sup {S A B : MarkedIdeal R}
    (hI : S.ideal = A.ideal ⊔ B.ideal) (hA : A.mark = S.mark) (hB : B.mark = S.mark) :
    S.cosupport = A.cosupport ∩ B.cosupport := by
  ext p
  simp [hI, hA, hB, Ideal.orderAt_sup]

section Pow

/-- Rescaling a marked ideal `(I, d)` by a positive integer `k` gives `(Iᵏ, k d)`. -/
def pow (P : MarkedIdeal R) (k : ℕ) [NeZero k] : MarkedIdeal R where
  ideal := P.ideal ^ k
  mark := k * P.mark
  mark_pos := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne k)) P.mark_pos

variable (P : MarkedIdeal R)

/-- Rescaling by `1` is the identity. -/
@[simp]
theorem pow_one : P.pow 1 = P :=
  MarkedIdeal.ext (_root_.pow_one P.ideal) (one_mul P.mark)

variable (k : ℕ) [NeZero k]

/-- The ideal of a rescaled marked ideal is the power of the ideal. -/
@[simp]
theorem pow_ideal : (P.pow k).ideal = P.ideal ^ k := (rfl)

/-- The mark of a rescaled marked ideal is the multiple of the mark. -/
@[simp]
theorem pow_mark : (P.pow k).mark = k * P.mark := (rfl)

/-- Rescaling composes multiplicatively. -/
@[simp]
theorem pow_pow (l : ℕ) [NeZero l] :
    (P.pow k).pow l = P.pow (k * l) :=
  MarkedIdeal.ext (pow_mul P.ideal k l).symm (by simp [mul_left_comm, mul_comm])

/-- Rescaling the unit ideal keeps the unit ideal and scales the mark. -/
@[simp]
theorem pow_top (d : ℕ) (hd : 0 < d) :
    (⟨⊤, d, hd⟩ : MarkedIdeal R).pow k =
      ⟨⊤, k * d, Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne k)) hd⟩ :=
  MarkedIdeal.ext (by rw [pow_ideal, Ideal.top_pow]) rfl

/-- Rescaling the zero ideal keeps the zero ideal and scales the mark. -/
@[simp]
theorem pow_bot (d : ℕ) (hd : 0 < d) :
    (⟨⊥, d, hd⟩ : MarkedIdeal R).pow k =
      ⟨⊥, k * d, Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne k)) hd⟩ :=
  MarkedIdeal.ext (by rw [pow_ideal, Ideal.bot_pow (NeZero.ne k)]) rfl

/-- Rescaling a principal marked ideal `(⟨f⟩, d)` by `k` gives `(⟨f ^ k⟩, k * d)`. -/
theorem pow_span_singleton (f : R) (d : ℕ) (hd : 0 < d) :
    (⟨Ideal.span {f}, d, hd⟩ : MarkedIdeal R).pow k =
      ⟨Ideal.span {f ^ k}, k * d, Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne k)) hd⟩ :=
  MarkedIdeal.ext (Ideal.span_singleton_pow f k) rfl

/-- Rescaling never shrinks the cosupport. -/
theorem cosupport_subset_cosupport_pow : P.cosupport ⊆ (P.pow k).cosupport := fun p hp ↦ by
  rw [mem_cosupport_iff, pow_ideal, pow_mark, Nat.cast_mul, ← nsmul_eq_mul]
  exact (nsmul_le_nsmul_right hp k).trans (Ideal.nsmul_orderAt_le_orderAt_pow _ k p)

/-- At a prime whose local ring has an associated graded ring without zero divisors, for instance a
prime with regular localization, rescaling does not change membership in the cosupport. -/
theorem mem_cosupport_pow_iff (p : PrimeSpectrum R)
    [NoZeroDivisors (maximalIdeal (Localization.AtPrime p.asIdeal)).AssociatedGraded] :
    p ∈ (P.pow k).cosupport ↔ p ∈ P.cosupport := by
  simp [nsmul_eq_mul, ENat.mul_le_mul_left_iff, NeZero.ne k]

/-- **Rescaling invariance of the cosupport.** Over a regular ring, `(I, d)` and `(Iᵏ, k d)`
have the same cosupport. -/
@[simp]
theorem cosupport_pow [IsRegularRing R] : (P.pow k).cosupport = P.cosupport := by
  ext p
  exact P.mem_cosupport_pow_iff k p

end Pow

section Sum

/-- The marked sum of `(I, a)` and `(J, b)` is `(Iᵇ + Jᵃ, a b)`: each ideal is raised to the mark
of the other summand, so that both summands carry the common mark `a b`. -/
def sum (P Q : MarkedIdeal R) : MarkedIdeal R where
  ideal := P.ideal ^ Q.mark ⊔ Q.ideal ^ P.mark
  mark := P.mark * Q.mark
  mark_pos := Nat.mul_pos P.mark_pos Q.mark_pos

variable (P Q : MarkedIdeal R)

/-- The ideal of the marked sum of `(I, a)` and `(J, b)` is `Iᵇ + Jᵃ`. -/
@[simp]
theorem sum_ideal : (P.sum Q).ideal = P.ideal ^ Q.mark ⊔ Q.ideal ^ P.mark := (rfl)

/-- The mark of the marked sum of `(I, a)` and `(J, b)` is `a b`. -/
@[simp]
theorem sum_mark : (P.sum Q).mark = P.mark * Q.mark := (rfl)

/-- The marked sum is commutative. -/
theorem sum_comm : P.sum Q = Q.sum P := by
  ext1
  · simp [sup_comm]
  · simp [mul_comm]

/-- Adding a unit summand on the left produces the unit ideal with the product mark. -/
@[simp]
theorem sum_top_left (d : ℕ) (hd : 0 < d) :
    (⟨⊤, d, hd⟩ : MarkedIdeal R).sum P = ⟨⊤, d * P.mark, Nat.mul_pos hd P.mark_pos⟩ :=
  MarkedIdeal.ext (by rw [sum_ideal, Ideal.top_pow, top_sup_eq]) rfl

/-- Adding a unit summand on the right produces the unit ideal with the product mark. -/
@[simp]
theorem sum_top_right (d : ℕ) (hd : 0 < d) :
    P.sum ⟨⊤, d, hd⟩ = ⟨⊤, P.mark * d, Nat.mul_pos P.mark_pos hd⟩ :=
  MarkedIdeal.ext (by rw [sum_ideal, Ideal.top_pow, sup_top_eq]) rfl

/-- Adding a zero summand on the left rescales the other summand by its mark. -/
@[simp]
theorem sum_bot_left (d : ℕ) (hd : 0 < d) :
    haveI : NeZero d := ⟨hd.ne'⟩
    (⟨⊥, d, hd⟩ : MarkedIdeal R).sum P = P.pow d :=
  MarkedIdeal.ext (by rw [sum_ideal, pow_ideal, Ideal.bot_pow P.mark_pos.ne', bot_sup_eq]) rfl

/-- Adding a zero summand on the right rescales the other summand by its mark. -/
@[simp]
theorem sum_bot_right (d : ℕ) (hd : 0 < d) :
    haveI : NeZero d := ⟨hd.ne'⟩
    P.sum ⟨⊥, d, hd⟩ = P.pow d := by
  rw [sum_comm, sum_bot_left]

/-- The marked sum of two principal marked ideals `(⟨f⟩, a)` and `(⟨g⟩, b)` has ideal
`⟨f ^ b, g ^ a⟩` and mark `a * b`. -/
theorem sum_span_singleton (f g : R) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (⟨Ideal.span {f}, a, ha⟩ : MarkedIdeal R).sum ⟨Ideal.span {g}, b, hb⟩ =
      ⟨Ideal.span {f ^ b, g ^ a}, a * b, Nat.mul_pos ha hb⟩ :=
  MarkedIdeal.ext
    (by rw [sum_ideal, Ideal.span_singleton_pow, Ideal.span_singleton_pow, ← Ideal.span_union,
      Set.singleton_union]) rfl

/-- The cosupport of the marked sum of `(I, a)` and `(J, b)` is the intersection of the
cosupports of the rescalings `(Iᵇ, b a)` and `(Jᵃ, a b)`. -/
theorem cosupport_sum_eq_inter_cosupport_pow :
    (P.sum Q).cosupport = (P.pow Q.mark).cosupport ∩ (Q.pow P.mark).cosupport :=
  cosupport_eq_inter_of_ideal_eq_sup (by simp) (by simp [mul_comm]) (by simp)

/-- The cosupport of a marked sum contains the intersection of the cosupports. -/
theorem cosupport_inter_subset_cosupport_sum :
    P.cosupport ∩ Q.cosupport ⊆ (P.sum Q).cosupport := by
  rw [cosupport_sum_eq_inter_cosupport_pow]
  exact Set.inter_subset_inter (P.cosupport_subset_cosupport_pow _)
    (Q.cosupport_subset_cosupport_pow _)

/-- At a prime whose local ring has an associated graded ring without zero divisors, for instance a
prime with regular localization, the prime lies in the cosupport of a marked sum exactly when it
lies in both cosupports. -/
theorem mem_cosupport_sum_iff (p : PrimeSpectrum R)
    [NoZeroDivisors (maximalIdeal (Localization.AtPrime p.asIdeal)).AssociatedGraded] :
    p ∈ (P.sum Q).cosupport ↔ p ∈ P.cosupport ∧ p ∈ Q.cosupport := by
  rw [cosupport_sum_eq_inter_cosupport_pow, Set.mem_inter_iff, mem_cosupport_pow_iff,
    mem_cosupport_pow_iff]

/-- **The cosupport of a marked sum.** Over a regular ring, the cosupport of `(Iᵇ + Jᵃ, a b)` is
the intersection of the cosupports of `(I, a)` and `(J, b)`. -/
@[simp]
theorem cosupport_sum [IsRegularRing R] : (P.sum Q).cosupport = P.cosupport ∩ Q.cosupport := by
  ext p
  exact P.mem_cosupport_sum_iff Q p

end Sum

end MarkedIdeal

end TauCeti
