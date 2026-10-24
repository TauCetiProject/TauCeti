/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Eval.Sign
public import TauCeti.Algebra.Polynomial.LinearFactor
public import TauCeti.Algebra.Polynomial.Thom.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Basic.Sign.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Sign

/-! # One-sided polynomial signs

The first nonzero formal derivative determines a polynomial's sign immediately
to the right of a point. To the left, the parity of its root multiplicity
supplies the additional sign. These algebraic signs allow endpoint root-count
formulas to include multiple roots without choosing nearby evaluation points.

Both signs are zero for the zero polynomial. Over any ordered field they agree
with evaluation on sufficiently small open intervals on the appropriate side.
No completeness or Archimedean assumption is needed. The two signs agree exactly when the root
multiplicity is even, so a nonzero polynomial changes sign at a point exactly when its root
multiplicity there is odd.

In characteristic zero, the one-sided signs of the derivative at `a` are those of the increment
`p - p(a)` on the right and their negatives on the left. In particular, at a root the
derivative has the sign of `p` immediately to the right of the root and the opposite sign
immediately to the left.

## Main definitions

* `Polynomial.derivSignRight p a`: the sign of the first nonzero derivative of `p` at `a`.
* `Polynomial.derivSignLeft p a`: the parity-corrected left-hand sign of `p` at `a`.

## Implementation notes

Mathlib defines the real right-hand sign `Polynomial.signRight x p` analytically, as the eventual
sign of evaluation along `𝓝[>] x`. The signs here are algebraic and need only a commutative ring
with a linear order, so they remain separate. Over `ℝ`, the two right-hand signs agree by
`Polynomial.derivSignRight_eq_signRight` in `TauCeti.Analysis.Polynomial.SignRight`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapters 2 and 10.
-/

public section

open Polynomial SignType Set Topology

namespace Polynomial

section Definitions

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The right-hand sign, computed from the derivative at the root multiplicity.
For a nonzero polynomial over an ordered field this is its first nonzero derivative.
The zero polynomial has sign zero. -/
noncomputable def derivSignRight (p : R[X]) (a : R) : SignType :=
  p.derivativeSign a (p.rootMultiplicity a)

/-- The left-hand sign is the right-hand sign corrected by multiplicity parity. -/
noncomputable def derivSignLeft (p : R[X]) (a : R) : SignType :=
  (-1) ^ p.rootMultiplicity a * p.derivSignRight a

/-- The derivative formula for the right-hand sign. -/
theorem derivSignRight_def (p : R[X]) (a : R) :
    p.derivSignRight a = sign ((derivative^[p.rootMultiplicity a] p).eval a) :=
  derivativeSign_def p a _

/-- The parity formula for the left-hand sign. -/
theorem derivSignLeft_def (p : R[X]) (a : R) :
    p.derivSignLeft a = (-1) ^ p.rootMultiplicity a * p.derivSignRight a := (rfl)

@[simp]
theorem derivSignRight_zero (a : R) : (0 : R[X]).derivSignRight a = 0 := by
  simp [derivSignRight_def]

@[simp]
theorem derivSignLeft_zero (a : R) : (0 : R[X]).derivSignLeft a = 0 := by
  simp [derivSignLeft_def]

@[simp]
theorem derivSignRight_C (c a : R) : (C c).derivSignRight a = sign c := by
  simp [derivSignRight_def]

@[simp]
theorem derivSignLeft_C (c a : R) : (C c).derivSignLeft a = sign c := by
  simp [derivSignLeft_def]

section One

variable [ZeroLEOneClass R] [NeZero (1 : R)]

@[simp]
theorem derivSignRight_one (a : R) : (1 : R[X]).derivSignRight a = 1 := by
  simpa [sign_pos zero_lt_one] using derivSignRight_C (1 : R) a

@[simp]
theorem derivSignLeft_one (a : R) : (1 : R[X]).derivSignLeft a = 1 := by
  simpa [sign_pos zero_lt_one] using derivSignLeft_C (1 : R) a

end One

/-- Away from a root, the right-hand sign is the sign of the value itself. -/
theorem derivSignRight_eq_sign_eval (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    p.derivSignRight a = sign (p.eval a) := by
  simp [derivSignRight_def, rootMultiplicity_eq_zero ha]

/-- Away from a root, the left-hand sign is also the sign of the value. -/
theorem derivSignLeft_eq_sign_eval (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    p.derivSignLeft a = sign (p.eval a) := by
  simp [derivSignLeft_def, rootMultiplicity_eq_zero ha, derivSignRight_eq_sign_eval p ha]

/-- Adding a multiple of a higher power of `X - C a` leaves the right-hand sign at `a` of a
nonzero polynomial unchanged. -/
theorem derivSignRight_add_eq_left_of_dvd {p q : R[X]} {a : R} (hp : p ≠ 0)
    (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).derivSignRight a = p.derivSignRight a := by
  have hq0 : (derivative^[p.rootMultiplicity a] q).eval a = 0 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity
      (Nat.lt_of_succ_le ((le_rootMultiplicity_iff hq0).mpr hq))
  rw [derivSignRight_def, derivSignRight_def, rootMultiplicity_add_eq_left_of_dvd hp hq,
    iterate_map_add derivative, eval_add, hq0, add_zero]

/-- Adding a multiple of a higher power of `X - C a` leaves the left-hand sign at `a` of a
nonzero polynomial unchanged. -/
theorem derivSignLeft_add_eq_left_of_dvd {p q : R[X]} {a : R} (hp : p ≠ 0)
    (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).derivSignLeft a = p.derivSignLeft a := by
  rw [derivSignLeft_def, derivSignLeft_def, rootMultiplicity_add_eq_left_of_dvd hp hq,
    derivSignRight_add_eq_left_of_dvd hp hq]

end Definitions

section Transport

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- Strictly monotone ring embeddings preserve right-hand signs. -/
@[simp]
theorem derivSignRight_map {S : Type*} [CommRing S] [LinearOrder S]
    (p : R[X]) (f : R →+* S) (hf : StrictMono f) (a : R) :
    (p.map f).derivSignRight (f a) = p.derivSignRight a := by
  rw [derivSignRight_def, derivSignRight_def, ← eq_rootMultiplicity_map hf.injective,
    iterate_derivative_map]
  exact sign_eval_map _ f hf a

/-- Strictly monotone ring embeddings preserve left-hand signs. -/
@[simp]
theorem derivSignLeft_map {S : Type*} [CommRing S] [LinearOrder S]
    (p : R[X]) (f : R →+* S) (hf : StrictMono f) (a : R) :
    (p.map f).derivSignLeft (f a) = p.derivSignLeft a := by
  rw [derivSignLeft_def, derivSignLeft_def, ← eq_rootMultiplicity_map hf.injective,
    derivSignRight_map p f hf]

end Transport

section Neg

variable {R : Type*} [CommRing R] [LinearOrder R] [AddLeftMono R]

/-- Negation reverses the right-hand sign. -/
@[simp]
theorem derivSignRight_neg (p : R[X]) (a : R) :
    (-p).derivSignRight a = -p.derivSignRight a := by
  simp only [derivSignRight_def, rootMultiplicity_eq_natTrailingDegree, neg_comp,
    natTrailingDegree_neg, iterate_derivative_neg, eval_neg, Left.sign_neg]

/-- Negation reverses the left-hand sign. -/
@[simp]
theorem derivSignLeft_neg (p : R[X]) (a : R) :
    (-p).derivSignLeft a = -p.derivSignLeft a := by
  simp only [derivSignLeft_def, rootMultiplicity_eq_natTrailingDegree, neg_comp,
    natTrailingDegree_neg, derivSignRight_neg, mul_neg]

end Neg

section Derivative

variable {R : Type*} [CommRing R] [LinearOrder R] [NoZeroDivisors R] [CharZero R]

/-- At a root, the derivative has the right-hand sign of the polynomial. -/
theorem derivSignRight_derivative_of_isRoot {p : R[X]} {a : R} (ha : p.IsRoot a) :
    p.derivative.derivSignRight a = p.derivSignRight a := by
  by_cases hp : p = 0
  · simp [hp]
  have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
  rw [derivSignRight, derivSignRight, derivative_rootMultiplicity_of_root ha,
    derivativeSign_derivative, Nat.sub_add_cancel hm]

/-- At a root, the derivative has the opposite of the left-hand sign of the polynomial. -/
theorem derivSignLeft_derivative_of_isRoot {p : R[X]} {a : R} (ha : p.IsRoot a) :
    p.derivative.derivSignLeft a = -p.derivSignLeft a := by
  by_cases hp : p = 0
  · simp [hp]
  have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [derivSignLeft_def, derivSignLeft_def, derivSignRight_derivative_of_isRoot ha,
    derivative_rootMultiplicity_of_root ha, hk]
  simp [pow_succ]

/-- At any point `a`, the right-hand sign of the derivative equals the right-hand sign of the
increment `p - C (p.eval a)`. Over an ordered field this is the sign of `p(x) - p(a)` just to the
right of `a`; see `exists_sign_eval_derivative`. -/
theorem derivSignRight_derivative (p : R[X]) (a : R) :
    p.derivative.derivSignRight a = (p - C (p.eval a)).derivSignRight a := by
  have h := derivSignRight_derivative_of_isRoot (p := p - C (p.eval a)) (a := a) (by simp)
  rwa [derivative_sub, derivative_C, sub_zero] at h

/-- At any point `a`, the left-hand sign of the derivative equals the negative of the left-hand
sign of the increment `p - C (p.eval a)`. Over an ordered field this is the opposite of the sign
of `p(x) - p(a)` just to the left of `a`; see `exists_sign_eval_derivative`. -/
theorem derivSignLeft_derivative (p : R[X]) (a : R) :
    p.derivative.derivSignLeft a = -(p - C (p.eval a)).derivSignLeft a := by
  have h := derivSignLeft_derivative_of_isRoot (p := p - C (p.eval a)) (a := a) (by simp)
  rwa [derivative_sub, derivative_C, sub_zero] at h

end Derivative

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Removing the full root factor gives the same sign as the first nonzero derivative. -/
theorem derivSignRight_eq_sign_eval_divByMonic (p : R[X]) (a : R) :
    p.derivSignRight a = sign ((p /ₘ (X - C a) ^ p.rootMultiplicity a).eval a) := by
  rw [derivSignRight_def, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul, sign_mul,
    sign_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)), one_mul]

/-- A one-sided sign vanishes exactly when the polynomial is zero. -/
@[simp]
theorem derivSignRight_eq_zero_iff (p : R[X]) (a : R) : p.derivSignRight a = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    rw [derivSignRight_eq_sign_eval_divByMonic, sign_eq_zero_iff] at h
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hp h
  · rintro rfl
    simp

@[simp]
theorem derivSignLeft_eq_zero_iff (p : R[X]) (a : R) : p.derivSignLeft a = 0 ↔ p = 0 := by
  rw [derivSignLeft_def, mul_eq_zero]
  simp

/-- A nonzero polynomial does not vanish where it has its right-hand sign. -/
theorem eval_ne_zero_of_sign_eq_derivSignRight {p : R[X]} (hp : p ≠ 0) {a x : R}
    (h : sign (p.eval x) = p.derivSignRight a) : p.eval x ≠ 0 := fun h0 => by
  rw [h0, sign_zero, eq_comm, derivSignRight_eq_zero_iff] at h
  exact hp h

/-- A nonzero polynomial does not vanish where it has its left-hand sign. -/
theorem eval_ne_zero_of_sign_eq_derivSignLeft {p : R[X]} (hp : p ≠ 0) {a x : R}
    (h : sign (p.eval x) = p.derivSignLeft a) : p.eval x ≠ 0 := fun h0 => by
  rw [h0, sign_zero, eq_comm, derivSignLeft_eq_zero_iff] at h
  exact hp h

omit [IsStrictOrderedRing R] in
/-- An even root multiplicity gives equal signs on the two sides. -/
theorem derivSignLeft_eq_derivSignRight_of_even (p : R[X]) (a : R)
    (h : Even (p.rootMultiplicity a)) : p.derivSignLeft a = p.derivSignRight a := by
  rw [derivSignLeft_def, h.neg_one_pow, one_mul]

omit [IsStrictOrderedRing R] in
/-- An odd root multiplicity gives opposite signs on the two sides. -/
theorem derivSignLeft_eq_neg_derivSignRight_of_odd (p : R[X]) (a : R)
    (h : Odd (p.rootMultiplicity a)) : p.derivSignLeft a = -p.derivSignRight a := by
  rw [derivSignLeft_def, h.neg_one_pow, neg_one_mul]

/-- The one-sided signs agree exactly when the root multiplicity is even. This includes the zero
polynomial, whose one-sided signs are both zero. -/
theorem derivSignLeft_eq_derivSignRight_iff (p : R[X]) (a : R) :
    p.derivSignLeft a = p.derivSignRight a ↔ Even (p.rootMultiplicity a) := by
  rcases Nat.even_or_odd (p.rootMultiplicity a) with h | h
  · simp [derivSignLeft_eq_derivSignRight_of_even p a h, h]
  by_cases hp : p = 0
  · simp [hp] at h
  have hs : p.derivSignRight a ≠ 0 := by simpa using hp
  rw [derivSignLeft_eq_neg_derivSignRight_of_odd p a h, iff_false_intro (Nat.not_even_iff_odd.2 h),
    iff_false]
  generalize p.derivSignRight a = s at hs
  cases s <;> simp_all

/-- For a nonzero polynomial, the one-sided signs are opposite exactly when the root multiplicity
is odd. -/
theorem derivSignLeft_eq_neg_derivSignRight_iff {p : R[X]} (hp : p ≠ 0) (a : R) :
    p.derivSignLeft a = -p.derivSignRight a ↔ Odd (p.rootMultiplicity a) := by
  rcases Nat.even_or_odd (p.rootMultiplicity a) with h | h
  · have hs : p.derivSignRight a ≠ 0 := by simpa using hp
    rw [derivSignLeft_eq_derivSignRight_of_even p a h,
      iff_false_intro (Nat.not_odd_iff_even.2 h), iff_false]
    generalize p.derivSignRight a = s at hs
    cases s <;> simp_all
  · simp [derivSignLeft_eq_neg_derivSignRight_of_odd p a h, h]

/-- Multiplication multiplies right-hand signs, including when a factor is zero. -/
@[simp]
theorem derivSignRight_mul (p q : R[X]) (a : R) :
    (p * q).derivSignRight a = p.derivSignRight a * q.derivSignRight a := by
  simp only [derivSignRight_eq_sign_eval_divByMonic, eval_divByMonic_eq_trailingCoeff_comp,
    mul_comp, trailingCoeff_mul, sign_mul]

/-- Multiplication multiplies left-hand signs, including when a factor is zero. -/
@[simp]
theorem derivSignLeft_mul (p q : R[X]) (a : R) :
    (p * q).derivSignLeft a = p.derivSignLeft a * q.derivSignLeft a := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  simp only [derivSignLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq), pow_add,
    derivSignRight_mul]
  ac_rfl

/-- Powers raise the right-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem derivSignRight_pow (p : R[X]) (a : R) (n : ℕ) :
    (p ^ n).derivSignRight a = p.derivSignRight a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Powers raise the left-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem derivSignLeft_pow (p : R[X]) (a : R) (n : ℕ) :
    (p ^ n).derivSignLeft a = p.derivSignLeft a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

end OrderedRing

section OrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The algebraic one-sided signs are realized on intervals immediately to the
left and right, including at multiple roots and for the zero polynomial. -/
theorem exists_derivSignLeft_derivSignRight (p : R[X]) (a : R) :
    ∃ l u, l < a ∧ a < u ∧
      (∀ x ∈ Ioo l a, sign (p.eval x) = p.derivSignLeft a) ∧
      (∀ x ∈ Ioo a u, sign (p.eval x) = p.derivSignRight a) := by
  by_cases hp : p = 0
  · subst p
    exact ⟨a - 1, a + 1, by simp, by simp, by simp, by simp⟩
  -- Use the order topology only to choose a root-free interval for the cofactor.
  let : TopologicalSpace R := Preorder.topology R
  let : OrderTopology R := ⟨rfl⟩
  let q := p /ₘ (X - C a) ^ p.rootMultiplicity a
  have hq : q.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hc : ContinuousAt (fun x : R => sign (q.eval x)) a :=
    (continuousAt_sign_of_ne_zero hq).comp (x := a) q.continuousAt
  have he : ∀ᶠ x in nhds a, sign (q.eval x) = sign (q.eval a) :=
    hc.eventually ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))
  obtain ⟨l, u, ⟨hla, hau⟩, hlu⟩ := he.exists_Ioo_subset
  have hs : sign (q.eval a) = p.derivSignRight a :=
    (derivSignRight_eq_sign_eval_divByMonic p a).symm
  have hf (x : R) : sign (p.eval x) =
      sign (x - a) ^ p.rootMultiplicity a * sign (q.eval x) := by
    conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq a]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sign_mul, sign_pow, q]
  refine ⟨l, u, hla, hau, ?_, ?_⟩
  · intro x hx
    rw [hf, sign_neg (sub_neg.mpr hx.2), hlu ⟨hx.1, hx.2.trans hau⟩, hs,
      derivSignLeft_def]
  · intro x hx
    rw [hf, sign_pos (sub_pos.mpr hx.1), one_pow, one_mul,
      hlu ⟨hla.trans hx.1, hx.2⟩, hs]

/-- A nonzero polynomial changes sign at `a` exactly when its root multiplicity at `a` is odd:
its signs immediately to the left of `a` are the negatives of those immediately to the right. -/
theorem odd_rootMultiplicity_iff_exists_sign_eval_eq_neg {p : R[X]} (hp : p ≠ 0) (a : R) :
    Odd (p.rootMultiplicity a) ↔ ∃ l u, l < a ∧ a < u ∧
      ∀ x ∈ Ioo l a, ∀ y ∈ Ioo a u, sign (p.eval x) = -sign (p.eval y) := by
  obtain ⟨l, u, hl, hu, hL, hR⟩ := p.exists_derivSignLeft_derivSignRight a
  rw [← derivSignLeft_eq_neg_derivSignRight_iff hp]
  constructor
  · intro h
    exact ⟨l, u, hl, hu, fun x hx y hy => by rw [hL x hx, hR y hy, h]⟩
  · rintro ⟨l', u', hl', hu', h⟩
    obtain ⟨x, hx, hxa⟩ := exists_between (max_lt hl hl')
    obtain ⟨y, hay, hy⟩ := exists_between (lt_min hu hu')
    rw [← hL x ⟨(le_max_left _ _).trans_lt hx, hxa⟩, ← hR y ⟨hay, hy.trans_le (min_le_left _ _)⟩]
    exact h x ⟨(le_max_right _ _).trans_lt hx, hxa⟩ y ⟨hay, hy.trans_le (min_le_right _ _)⟩

/-- Immediately to the right of a point `a`, the derivative has the sign of `p(x) - p(a)`, and
immediately to the left it has the opposite sign. This includes points where `p - p(a)` has a
multiple root, and constant polynomials. -/
theorem exists_sign_eval_derivative (p : R[X]) (a : R) :
    ∃ l u, l < a ∧ a < u ∧
      (∀ x ∈ Ioo l a, sign (p.derivative.eval x) = -sign (p.eval x - p.eval a)) ∧
      (∀ x ∈ Ioo a u, sign (p.derivative.eval x) = sign (p.eval x - p.eval a)) := by
  obtain ⟨l₁, u₁, hl₁, hu₁, hL₁, hR₁⟩ := p.derivative.exists_derivSignLeft_derivSignRight a
  obtain ⟨l₂, u₂, hl₂, hu₂, hL₂, hR₂⟩ := (p - C (p.eval a)).exists_derivSignLeft_derivSignRight a
  refine ⟨max l₁ l₂, min u₁ u₂, max_lt hl₁ hl₂, lt_min hu₁ hu₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hL₁ x ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩, derivSignLeft_derivative,
      ← hL₂ x ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩, eval_sub, eval_C]
  · rw [hR₁ x ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩, derivSignRight_derivative,
      ← hR₂ x ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩, eval_sub, eval_C]

end OrderedField

end Polynomial

namespace List

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A uniform interval immediately to the right of `a` on which every polynomial of a list
has its right-hand sign at `a`. -/
theorem exists_signs_right (cs : List R[X]) (a : R) :
    ∃ u, a < u ∧ ∀ p ∈ cs, ∀ x ∈ Ioo a u, sign (p.eval x) = p.derivSignRight a := by
  -- Use the order topology only to combine the finitely many right-hand intervals.
  let : TopologicalSpace R := Preorder.topology R
  let : OrderTopology R := ⟨rfl⟩
  have he : ∀ᶠ x in 𝓝[>] a, ∀ p ∈ cs, sign (p.eval x) = p.derivSignRight a := by
    refine cs.finite_toSet.eventually_all.mpr fun p _ => ?_
    obtain ⟨-, u, -, hau, -, hu⟩ := p.exists_derivSignLeft_derivSignRight a
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT hau) hu
  obtain ⟨u, hau, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨u, hau, fun p hp x hx => hu hx p hp⟩

/-- A uniform interval immediately to the left of `a` on which every polynomial of a list
has its left-hand sign at `a`. -/
theorem exists_signs_left (cs : List R[X]) (a : R) :
    ∃ l, l < a ∧ ∀ p ∈ cs, ∀ x ∈ Ioo l a, sign (p.eval x) = p.derivSignLeft a := by
  -- Use the order topology only to combine the finitely many left-hand intervals.
  let : TopologicalSpace R := Preorder.topology R
  let : OrderTopology R := ⟨rfl⟩
  have he : ∀ᶠ x in 𝓝[<] a, ∀ p ∈ cs, sign (p.eval x) = p.derivSignLeft a := by
    refine cs.finite_toSet.eventually_all.mpr fun p _ => ?_
    obtain ⟨l, -, hla, -, hl, -⟩ := p.exists_derivSignLeft_derivSignRight a
    exact Filter.mem_of_superset (Ioo_mem_nhdsLT hla) hl
  obtain ⟨l, hla, hl⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  exact ⟨l, hla, fun p hp x hx => hl hx p hp⟩

end List
