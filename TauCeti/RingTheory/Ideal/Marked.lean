/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Derivation
public import TauCeti.RingTheory.RegularLocalRing.Order
import Mathlib.Data.ENat.Monoid

/-!
# Affine marked ideals, rescaling, and marked sums

An affine marked ideal over a commutative ring `R` is a pair `(I, d)` consisting of an ideal
`I : Ideal R` and a positive integer mark `d > 0` (`TauCeti.MarkedIdeal`). Its cosupport is the
order-threshold locus `{p ∈ Spec R | d ≤ I.orderAt p}` (`TauCeti.MarkedIdeal.cosupport`).

The basic operations on marked ideals are:

* rescaling (`TauCeti.MarkedIdeal.rescale`), sending `(I, d)` and `k > 0` to `(I ^ k, k * d)`;
* marked sum (`TauCeti.MarkedIdeal.sum`), sending `(I, a)` and `(J, b)` to
  `(I ^ b ⊔ J ^ a, a * b)`.

Over an arbitrary commutative ring, `M.cosupport ⊆ (M.rescale k hk).cosupport` and
`M₁.cosupport ∩ M₂.cosupport ⊆ (M₁.sum M₂).cosupport`. When the localizations are regular local
rings (in particular, when `IsRegularRing R`), multiplicativity of ideal order upgrades both
inclusions to equalities: rescaling leaves the cosupport invariant and the cosupport of a marked
sum is the intersection of the two cosupports. Over a characteristic-zero field, the cosupport of
a marked ideal on a regular ring with finitely generated projective differentials—in particular, on
a smooth algebra or a regular algebra of finite type—is Zariski closed, cut out by the
`(d - 1)`-st iterated derivation ideal.

## Main definitions

* `TauCeti.MarkedIdeal`: an ideal of `R` paired with a positive integer mark.
* `TauCeti.MarkedIdeal.cosupport`: the order-threshold locus
  `{p | (M.mark : ℕ∞) ≤ M.ideal.orderAt p}`.
* `TauCeti.MarkedIdeal.rescale`: `(I, d)` rescaled by `k > 0` to `(I ^ k, k * d)`.
* `TauCeti.MarkedIdeal.sum`: the marked sum `(I ^ b ⊔ J ^ a, a * b)` of `(I, a)` and `(J, b)`.

## Main results

* `TauCeti.MarkedIdeal.cosupport_rescale`: on a regular ring, rescaling preserves cosupport.
* `TauCeti.MarkedIdeal.cosupport_sum`: on a regular ring, the cosupport of a marked sum is the
  intersection of the cosupports.
* `TauCeti.MarkedIdeal.isClosed_cosupport_of_finiteType`: on a regular algebra of finite type over
  a characteristic-zero field, the cosupport of every marked ideal is Zariski closed.

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing up
  the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2 and
  Construction 4.23.
-/

public section

namespace TauCeti

/-- An affine marked ideal over a commutative ring `R`, consisting of an ideal together with a
positive integer mark. -/
@[ext]
structure MarkedIdeal (R : Type*) [CommRing R] where
  /-- The underlying ideal of the marked ideal. -/
  ideal : Ideal R
  /-- The positive integer mark. -/
  mark : ℕ
  /-- The mark is strictly positive. -/
  mark_pos : 0 < mark

namespace MarkedIdeal

section Basic

variable {R : Type*} [CommRing R]

/-- The cosupport of a marked ideal `M`, consisting of the primes at which `M.ideal` has order at
least `M.mark`. -/
def cosupport (M : MarkedIdeal R) : Set (PrimeSpectrum R) :=
  {p | (M.mark : ℕ∞) ≤ M.ideal.orderAt p}

/-- The defining threshold locus of `MarkedIdeal.cosupport`. -/
theorem cosupport_def (M : MarkedIdeal R) :
    M.cosupport = {p | (M.mark : ℕ∞) ≤ M.ideal.orderAt p} := (rfl)

/-- A prime lies in the cosupport of `M` if and only if `M.ideal` has order at least `M.mark`
there. -/
@[simp]
theorem mem_cosupport_iff (M : MarkedIdeal R) (p : PrimeSpectrum R) :
    p ∈ M.cosupport ↔ (M.mark : ℕ∞) ≤ M.ideal.orderAt p := Iff.rfl

/-- Every cosupport is contained in the zero locus of its underlying ideal, because the mark is
positive. -/
theorem cosupport_subset_zeroLocus (M : MarkedIdeal R) :
    M.cosupport ⊆ PrimeSpectrum.zeroLocus (M.ideal : Set R) := by
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, ← Ideal.one_le_orderAt_iff]
  exact le_trans (by exact_mod_cast M.mark_pos) hp

/-- Enlarging the ideal or raising the mark shrinks the cosupport. -/
theorem cosupport_subset_cosupport {M₁ M₂ : MarkedIdeal R} (hI : M₂.ideal ≤ M₁.ideal)
    (hd : M₂.mark ≤ M₁.mark) : M₁.cosupport ⊆ M₂.cosupport := fun p hp ↦
  le_trans (Nat.cast_le.mpr hd) (le_trans hp (Ideal.orderAt_anti hI p))

/-- With mark `1`, the cosupport is the zero locus of the underlying ideal. -/
@[simp]
theorem cosupport_mark_one (I : Ideal R) (h : 0 < 1) :
    (⟨I, 1, h⟩ : MarkedIdeal R).cosupport = PrimeSpectrum.zeroLocus (I : Set R) := by
  ext p
  simp [PrimeSpectrum.mem_zeroLocus]

/-- A marked ideal with underlying ideal `⊤` has empty cosupport. -/
theorem cosupport_eq_empty_of_ideal_eq_top {M : MarkedIdeal R} (h : M.ideal = ⊤) :
    M.cosupport = ∅ := by
  ext p
  simp [h, M.mark_pos.ne']

/-- The unit ideal with any positive mark has empty cosupport. -/
@[simp]
theorem cosupport_top (d : ℕ) (hd : 0 < d) :
    (⟨⊤, d, hd⟩ : MarkedIdeal R).cosupport = ∅ :=
  cosupport_eq_empty_of_ideal_eq_top rfl

/-- A marked ideal with underlying ideal `⊥` has full cosupport. -/
theorem cosupport_eq_univ_of_ideal_eq_bot {M : MarkedIdeal R} (h : M.ideal = ⊥) :
    M.cosupport = Set.univ := by
  ext p
  simp [h]

/-- The zero ideal with any positive mark has full cosupport. -/
@[simp]
theorem cosupport_bot (d : ℕ) (hd : 0 < d) :
    (⟨⊥, d, hd⟩ : MarkedIdeal R).cosupport = Set.univ :=
  cosupport_eq_univ_of_ideal_eq_bot rfl

end Basic

section Rescale

variable {R : Type*} [CommRing R]

/-- Rescaling a marked ideal `(I, d)` by a positive integer `k` gives `(I ^ k, k * d)`. -/
def rescale (M : MarkedIdeal R) (k : ℕ) (hk : 0 < k) : MarkedIdeal R where
  ideal := M.ideal ^ k
  mark := k * M.mark
  mark_pos := Nat.mul_pos hk M.mark_pos

/-- The ideal of `M.rescale k hk` is `M.ideal ^ k`. -/
@[simp]
theorem rescale_ideal (M : MarkedIdeal R) (k : ℕ) (hk : 0 < k) :
    (M.rescale k hk).ideal = M.ideal ^ k := (rfl)

/-- The mark of `M.rescale k hk` is `k * M.mark`. -/
@[simp]
theorem rescale_mark (M : MarkedIdeal R) (k : ℕ) (hk : 0 < k) :
    (M.rescale k hk).mark = k * M.mark := (rfl)

/-- Rescaling by `1` is the identity. -/
@[simp]
theorem rescale_one (M : MarkedIdeal R) (h : 0 < 1) :
    M.rescale 1 h = M :=
  MarkedIdeal.ext (pow_one M.ideal) (one_mul M.mark)

/-- Rescaling composes multiplicatively. -/
theorem rescale_rescale (M : MarkedIdeal R) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    (M.rescale k hk).rescale l hl = M.rescale (k * l) (Nat.mul_pos hk hl) :=
  MarkedIdeal.ext (pow_mul M.ideal k l).symm (by simp [rescale_mark, mul_left_comm, mul_comm])

/-- Rescaling the unit ideal keeps the unit ideal and scales the mark. -/
@[simp]
theorem rescale_top (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    (⟨⊤, d, hd⟩ : MarkedIdeal R).rescale k hk = ⟨⊤, k * d, Nat.mul_pos hk hd⟩ :=
  MarkedIdeal.ext (by rw [rescale_ideal, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top]) rfl

/-- Rescaling the zero ideal keeps the zero ideal and scales the mark. -/
@[simp]
theorem rescale_bot (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    (⟨⊥, d, hd⟩ : MarkedIdeal R).rescale k hk = ⟨⊥, k * d, Nat.mul_pos hk hd⟩ :=
  MarkedIdeal.ext
    (by rw [rescale_ideal, ← Ideal.zero_eq_bot, zero_pow hk.ne', Ideal.zero_eq_bot]) rfl

/-- Rescaling a principal marked ideal `(⟨f⟩, d)` by `k` gives `(⟨f ^ k⟩, k * d)`. -/
theorem rescale_span_singleton (f : R) {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    (⟨Ideal.span {f}, d, hd⟩ : MarkedIdeal R).rescale k hk =
      ⟨Ideal.span {f ^ k}, k * d, Nat.mul_pos hk hd⟩ :=
  MarkedIdeal.ext (Ideal.span_singleton_pow f k) rfl

/-- Over any commutative ring, rescaling can only enlarge the cosupport. -/
theorem cosupport_subset_cosupport_rescale (M : MarkedIdeal R) {k : ℕ} (hk : 0 < k) :
    M.cosupport ⊆ (M.rescale k hk).cosupport := by
  intro p hp
  rw [mem_cosupport_iff, rescale_ideal, rescale_mark, Nat.cast_mul, ← nsmul_eq_mul]
  exact le_trans (nsmul_le_nsmul_right hp k) (Ideal.le_orderAt_pow M.ideal p k)

/-- At any prime whose localization is a regular local ring, rescaling preserves membership in the
cosupport. -/
theorem mem_cosupport_rescale_iff (M : MarkedIdeal R) {k : ℕ} (hk : 0 < k) (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] :
    p ∈ (M.rescale k hk).cosupport ↔ p ∈ M.cosupport := by
  rw [mem_cosupport_iff, mem_cosupport_iff, rescale_ideal, rescale_mark, Ideal.orderAt_pow,
    Nat.cast_mul, nsmul_eq_mul,
    ENat.mul_le_mul_left_iff (by exact_mod_cast hk.ne') (ENat.natCast_ne_top k)]

/-- On a regular ring, rescaling leaves the cosupport unchanged. -/
@[simp]
theorem cosupport_rescale [IsRegularRing R] (M : MarkedIdeal R) {k : ℕ} (hk : 0 < k) :
    (M.rescale k hk).cosupport = M.cosupport :=
  Set.ext fun p ↦ mem_cosupport_rescale_iff M hk p

end Rescale

section Sum

variable {R : Type*} [CommRing R]

/-- The marked sum of `(I, a)` and `(J, b)`, with ideal `I ^ b ⊔ J ^ a` and mark `a * b`. -/
def sum (M₁ M₂ : MarkedIdeal R) : MarkedIdeal R where
  ideal := M₁.ideal ^ M₂.mark ⊔ M₂.ideal ^ M₁.mark
  mark := M₁.mark * M₂.mark
  mark_pos := Nat.mul_pos M₁.mark_pos M₂.mark_pos

/-- The ideal of `M₁.sum M₂` is `M₁.ideal ^ M₂.mark ⊔ M₂.ideal ^ M₁.mark`. -/
@[simp]
theorem sum_ideal (M₁ M₂ : MarkedIdeal R) :
    (M₁.sum M₂).ideal = M₁.ideal ^ M₂.mark ⊔ M₂.ideal ^ M₁.mark := (rfl)

/-- The mark of `M₁.sum M₂` is `M₁.mark * M₂.mark`. -/
@[simp]
theorem sum_mark (M₁ M₂ : MarkedIdeal R) :
    (M₁.sum M₂).mark = M₁.mark * M₂.mark := (rfl)

/-- Marked sum is commutative. -/
theorem sum_comm (M₁ M₂ : MarkedIdeal R) : M₁.sum M₂ = M₂.sum M₁ :=
  MarkedIdeal.ext (sup_comm _ _) (mul_comm _ _)

/-- Adding a unit summand on the left produces the unit ideal with the product mark. -/
@[simp]
theorem sum_top_left (d : ℕ) (hd : 0 < d) (M : MarkedIdeal R) :
    (⟨⊤, d, hd⟩ : MarkedIdeal R).sum M = ⟨⊤, d * M.mark, Nat.mul_pos hd M.mark_pos⟩ :=
  MarkedIdeal.ext
    (by rw [sum_ideal, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top, top_sup_eq]) rfl

/-- Adding a unit summand on the right produces the unit ideal with the product mark. -/
@[simp]
theorem sum_top_right (M : MarkedIdeal R) (d : ℕ) (hd : 0 < d) :
    M.sum ⟨⊤, d, hd⟩ = ⟨⊤, M.mark * d, Nat.mul_pos M.mark_pos hd⟩ :=
  MarkedIdeal.ext
    (by rw [sum_ideal, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top, sup_top_eq]) rfl

/-- Adding a zero summand on the left rescales the other summand by its mark. -/
@[simp]
theorem sum_bot_left (d : ℕ) (hd : 0 < d) (M : MarkedIdeal R) :
    (⟨⊥, d, hd⟩ : MarkedIdeal R).sum M = M.rescale d hd :=
  MarkedIdeal.ext
    (by rw [sum_ideal, rescale_ideal, ← Ideal.zero_eq_bot, zero_pow M.mark_pos.ne',
      Ideal.zero_eq_bot, bot_sup_eq]) rfl

/-- Adding a zero summand on the right rescales the other summand by its mark. -/
@[simp]
theorem sum_bot_right (M : MarkedIdeal R) (d : ℕ) (hd : 0 < d) :
    M.sum ⟨⊥, d, hd⟩ = M.rescale d hd := by
  rw [sum_comm, sum_bot_left]

/-- The marked sum of two principal marked ideals `(⟨f⟩, a)` and `(⟨g⟩, b)` has ideal
`⟨f ^ b, g ^ a⟩` and mark `a * b`. -/
theorem sum_span_singleton (f g : R) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (⟨Ideal.span {f}, a, ha⟩ : MarkedIdeal R).sum ⟨Ideal.span {g}, b, hb⟩ =
      ⟨Ideal.span {f ^ b, g ^ a}, a * b, Nat.mul_pos ha hb⟩ :=
  MarkedIdeal.ext
    (by rw [sum_ideal, Ideal.span_singleton_pow, Ideal.span_singleton_pow, ← Ideal.span_union,
      Set.singleton_union]) rfl

/-- Over any commutative ring, the intersection of two cosupports is contained in the cosupport of
their marked sum. -/
theorem cosupport_inter_subset_cosupport_sum (M₁ M₂ : MarkedIdeal R) :
    M₁.cosupport ∩ M₂.cosupport ⊆ (M₁.sum M₂).cosupport := by
  rintro p ⟨hp₁, hp₂⟩
  rw [mem_cosupport_iff, sum_ideal, sum_mark, Ideal.orderAt_sup, le_min_iff]
  constructor
  · simpa only [mem_cosupport_iff, rescale_ideal, rescale_mark, mul_comm M₁.mark M₂.mark] using
      cosupport_subset_cosupport_rescale M₁ M₂.mark_pos hp₁
  · simpa only [mem_cosupport_iff, rescale_ideal, rescale_mark] using
      cosupport_subset_cosupport_rescale M₂ M₁.mark_pos hp₂

/-- At any prime whose localization is a regular local ring, membership in the cosupport of a
marked sum is equivalent to membership in both cosupports. -/
theorem mem_cosupport_sum_iff (M₁ M₂ : MarkedIdeal R) (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] :
    p ∈ (M₁.sum M₂).cosupport ↔ p ∈ M₁.cosupport ∧ p ∈ M₂.cosupport := by
  refine ⟨fun h ↦ ?_, fun h ↦ cosupport_inter_subset_cosupport_sum M₁ M₂ h⟩
  rw [mem_cosupport_iff, sum_ideal, sum_mark, Ideal.orderAt_sup, le_min_iff] at h
  exact ⟨(mem_cosupport_rescale_iff M₁ M₂.mark_pos p).mp
      (by simpa only [mem_cosupport_iff, rescale_ideal, rescale_mark, mul_comm] using h.1),
    (mem_cosupport_rescale_iff M₂ M₁.mark_pos p).mp h.2⟩

/-- On a regular ring, the cosupport of a marked sum is the intersection of the two cosupports. -/
@[simp]
theorem cosupport_sum [IsRegularRing R] (M₁ M₂ : MarkedIdeal R) :
    (M₁.sum M₂).cosupport = M₁.cosupport ∩ M₂.cosupport :=
  Set.ext fun p ↦ mem_cosupport_sum_iff M₁ M₂ p

end Sum

section Closed

open scoped KaehlerDifferential

variable (k : Type*) {R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

/-- Over a characteristic-zero field, on a regular ring with finitely generated projective
differentials, the cosupport of a marked ideal `M` is the zero locus of the `(M.mark - 1)`-st
iterated derivation ideal of `M.ideal`. -/
theorem cosupport_eq_zeroLocus_iterate_derivationIdeal [Module.Projective R Ω[R⁄k]]
    [Module.Finite R Ω[R⁄k]] [IsRegularRing R] (M : MarkedIdeal R) :
    M.cosupport =
      PrimeSpectrum.zeroLocus (((Ideal.derivationIdeal k)^[M.mark - 1] M.ideal) : Set R) := by
  have hmark : M.mark - 1 + 1 = M.mark := Nat.sub_add_cancel M.mark_pos
  rw [cosupport_def, ← hmark]
  exact Ideal.setOf_natCast_add_one_le_orderAt_eq_zeroLocus k M.ideal (M.mark - 1)

/-- Over a characteristic-zero field, on a regular ring with finitely generated projective
differentials, the cosupport of every marked ideal is Zariski closed. -/
theorem isClosed_cosupport [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    [IsRegularRing R] (M : MarkedIdeal R) :
    IsClosed M.cosupport :=
  Ideal.isClosed_setOf_le_orderAt k M.ideal M.mark

/-- On a smooth algebra over a characteristic-zero field, the cosupport of every marked ideal is
Zariski closed. -/
theorem isClosed_cosupport_of_smooth [Algebra.Smooth k R] (M : MarkedIdeal R) :
    IsClosed M.cosupport :=
  Ideal.isClosed_setOf_le_orderAt_of_smooth k M.ideal M.mark

/-- On a regular algebra of finite type over a characteristic-zero field, the cosupport of every
marked ideal is Zariski closed. -/
theorem isClosed_cosupport_of_finiteType [Algebra.FiniteType k R] [IsRegularRing R]
    (M : MarkedIdeal R) :
    IsClosed M.cosupport :=
  Ideal.isClosed_setOf_le_orderAt_of_finiteType k M.ideal M.mark

end Closed

end MarkedIdeal

end TauCeti
