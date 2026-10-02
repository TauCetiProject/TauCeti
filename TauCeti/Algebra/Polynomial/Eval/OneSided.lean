/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Eval.Sign
public import TauCeti.Algebra.Polynomial.LinearFactor
public import TauCeti.Algebra.Polynomial.Thom
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
No completeness or Archimedean assumption is needed.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapters 2 and 10.
-/

public section

namespace TauCeti

open Polynomial

open SignType Set Topology

section Definitions

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The right-hand sign, computed from the derivative at the root multiplicity.
For a nonzero polynomial over an ordered field this is its first nonzero derivative.
The zero polynomial has sign zero. -/
noncomputable def _root_.Polynomial.signRight (p : R[X]) (a : R) : SignType :=
  p.derivativeSign a (p.rootMultiplicity a)

/-- The left-hand sign is the right-hand sign corrected by multiplicity parity. -/
noncomputable def _root_.Polynomial.signLeft (p : R[X]) (a : R) : SignType :=
  (-1) ^ p.rootMultiplicity a * p.signRight a

/-- The derivative formula for the right-hand sign. -/
theorem _root_.Polynomial.signRight_def (p : R[X]) (a : R) :
    p.signRight a = sign ((derivative^[p.rootMultiplicity a] p).eval a) :=
  derivativeSign_def p a _

/-- The parity formula for the left-hand sign. -/
theorem _root_.Polynomial.signLeft_def (p : R[X]) (a : R) :
    p.signLeft a = (-1) ^ p.rootMultiplicity a * p.signRight a := (rfl)

@[simp]
theorem _root_.Polynomial.signRight_zero (a : R) : (0 : R[X]).signRight a = 0 := by
  simp [signRight_def]

@[simp]
theorem _root_.Polynomial.signLeft_zero (a : R) : (0 : R[X]).signLeft a = 0 := by
  simp [signLeft_def]

@[simp]
theorem _root_.Polynomial.signRight_C (c a : R) : (C c).signRight a = sign c := by
  simp [signRight_def]

@[simp]
theorem _root_.Polynomial.signLeft_C (c a : R) : (C c).signLeft a = sign c := by
  simp [signLeft_def]

/-- Away from a root, the right-hand sign is the sign of the value itself. -/
theorem _root_.Polynomial.signRight_eq_sign_eval (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    p.signRight a = sign (p.eval a) := by
  simp [signRight_def, rootMultiplicity_eq_zero ha]

/-- Away from a root, the left-hand sign is also the sign of the value. -/
theorem _root_.Polynomial.signLeft_eq_sign_eval (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    p.signLeft a = sign (p.eval a) := by
  simp [signLeft_def, rootMultiplicity_eq_zero ha, signRight_eq_sign_eval p ha]

/-- Adding a multiple of a higher power of `X - C a` leaves the right-hand sign at `a` of a
nonzero polynomial unchanged. -/
theorem _root_.Polynomial.signRight_add_eq_left_of_dvd {p q : R[X]} {a : R} (hp : p ≠ 0)
    (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).signRight a = p.signRight a := by
  have hq0 : (derivative^[p.rootMultiplicity a] q).eval a = 0 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity
      (Nat.lt_of_succ_le ((le_rootMultiplicity_iff hq0).mpr hq))
  rw [signRight_def, signRight_def, rootMultiplicity_add_eq_left_of_dvd hp hq,
    iterate_map_add derivative, eval_add, hq0, add_zero]

/-- Adding a multiple of a higher power of `X - C a` leaves the left-hand sign at `a` of a
nonzero polynomial unchanged. -/
theorem _root_.Polynomial.signLeft_add_eq_left_of_dvd {p q : R[X]} {a : R} (hp : p ≠ 0)
    (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).signLeft a = p.signLeft a := by
  rw [signLeft_def, signLeft_def, rootMultiplicity_add_eq_left_of_dvd hp hq,
    signRight_add_eq_left_of_dvd hp hq]

end Definitions

section Transport

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- Strictly monotone ring embeddings preserve right-hand signs. -/
@[simp]
theorem _root_.Polynomial.signRight_map {S : Type*} [CommRing S] [LinearOrder S]
    (p : R[X]) (f : R →+* S) (hf : StrictMono f) (a : R) :
    (p.map f).signRight (f a) = p.signRight a := by
  rw [signRight_def, signRight_def, ← eq_rootMultiplicity_map hf.injective,
    iterate_derivative_map]
  exact sign_eval_map _ f hf a

/-- Strictly monotone ring embeddings preserve left-hand signs. -/
@[simp]
theorem _root_.Polynomial.signLeft_map {S : Type*} [CommRing S] [LinearOrder S]
    (p : R[X]) (f : R →+* S) (hf : StrictMono f) (a : R) :
    (p.map f).signLeft (f a) = p.signLeft a := by
  rw [signLeft_def, signLeft_def, ← eq_rootMultiplicity_map hf.injective, signRight_map p f hf]

end Transport

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Removing the full root factor gives the same sign as the first nonzero derivative. -/
theorem _root_.Polynomial.signRight_eq_sign_eval_divByMonic (p : R[X]) (a : R) :
    p.signRight a = sign ((p /ₘ (X - C a) ^ p.rootMultiplicity a).eval a) := by
  rw [signRight_def, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul, sign_mul,
    sign_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)), one_mul]

/-- A one-sided sign vanishes exactly when the polynomial is zero. -/
@[simp]
theorem _root_.Polynomial.signRight_eq_zero_iff (p : R[X]) (a : R) : p.signRight a = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    rw [signRight_eq_sign_eval_divByMonic, sign_eq_zero_iff] at h
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hp h
  · rintro rfl
    simp

@[simp]
theorem _root_.Polynomial.signLeft_eq_zero_iff (p : R[X]) (a : R) : p.signLeft a = 0 ↔ p = 0 := by
  rw [signLeft_def, mul_eq_zero]
  simp

/-- A nonzero polynomial does not vanish where it has its right-hand sign. -/
theorem _root_.Polynomial.eval_ne_zero_of_sign_eq_signRight {p : R[X]} (hp : p ≠ 0) {a x : R}
    (h : sign (p.eval x) = p.signRight a) : p.eval x ≠ 0 := fun h0 => by
  rw [h0, sign_zero, eq_comm, signRight_eq_zero_iff] at h
  exact hp h

/-- A nonzero polynomial does not vanish where it has its left-hand sign. -/
theorem _root_.Polynomial.eval_ne_zero_of_sign_eq_signLeft {p : R[X]} (hp : p ≠ 0) {a x : R}
    (h : sign (p.eval x) = p.signLeft a) : p.eval x ≠ 0 := fun h0 => by
  rw [h0, sign_zero, eq_comm, signLeft_eq_zero_iff] at h
  exact hp h

omit [IsStrictOrderedRing R] in
/-- An even root multiplicity gives equal signs on the two sides. -/
theorem _root_.Polynomial.signLeft_eq_signRight_of_even (p : R[X]) (a : R)
    (h : Even (p.rootMultiplicity a)) : p.signLeft a = p.signRight a := by
  rw [signLeft_def, h.neg_one_pow, one_mul]

omit [IsStrictOrderedRing R] in
/-- An odd root multiplicity gives opposite signs on the two sides. -/
theorem _root_.Polynomial.signLeft_eq_neg_signRight_of_odd (p : R[X]) (a : R)
    (h : Odd (p.rootMultiplicity a)) : p.signLeft a = -p.signRight a := by
  rw [signLeft_def, h.neg_one_pow, neg_one_mul]

/-- Multiplication multiplies right-hand signs, including when a factor is zero. -/
@[simp]
theorem _root_.Polynomial.signRight_mul (p q : R[X]) (a : R) :
    (p * q).signRight a = p.signRight a * q.signRight a := by
  simp only [signRight_eq_sign_eval_divByMonic, eval_divByMonic_eq_trailingCoeff_comp,
    mul_comp, trailingCoeff_mul, sign_mul]

/-- Multiplication multiplies left-hand signs, including when a factor is zero. -/
@[simp]
theorem _root_.Polynomial.signLeft_mul (p q : R[X]) (a : R) :
    (p * q).signLeft a = p.signLeft a * q.signLeft a := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  simp only [signLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq), pow_add, signRight_mul]
  ac_rfl

@[simp]
theorem _root_.Polynomial.signRight_one (a : R) : (1 : R[X]).signRight a = 1 := by
  simpa using signRight_C (1 : R) a

@[simp]
theorem _root_.Polynomial.signLeft_one (a : R) : (1 : R[X]).signLeft a = 1 := by
  simpa using signLeft_C (1 : R) a

/-- Negation reverses the right-hand sign. -/
@[simp]
theorem _root_.Polynomial.signRight_neg (p : R[X]) (a : R) :
    (-p).signRight a = -p.signRight a := by
  have h := signRight_mul (C (-1)) p a
  rw [signRight_C, sign_neg (neg_one_lt_zero (R := R))] at h
  simpa using h

/-- Negation reverses the left-hand sign. -/
@[simp]
theorem _root_.Polynomial.signLeft_neg (p : R[X]) (a : R) :
    (-p).signLeft a = -p.signLeft a := by
  have h := signLeft_mul (C (-1)) p a
  rw [signLeft_C, sign_neg (neg_one_lt_zero (R := R))] at h
  simpa using h

/-- Powers raise the right-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem _root_.Polynomial.signRight_pow (p : R[X]) (a : R) (n : ℕ) :
    (p ^ n).signRight a = p.signRight a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Powers raise the left-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem _root_.Polynomial.signLeft_pow (p : R[X]) (a : R) (n : ℕ) :
    (p ^ n).signLeft a = p.signLeft a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

end OrderedRing

section OrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The algebraic one-sided signs are realized on intervals immediately to the
left and right, including at multiple roots and for the zero polynomial. -/
theorem _root_.Polynomial.exists_signLeft_signRight (p : R[X]) (a : R) :
    ∃ l u, l < a ∧ a < u ∧
      (∀ x ∈ Ioo l a, sign (p.eval x) = p.signLeft a) ∧
      (∀ x ∈ Ioo a u, sign (p.eval x) = p.signRight a) := by
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
  have hs : sign (q.eval a) = p.signRight a :=
    (signRight_eq_sign_eval_divByMonic p a).symm
  have hf (x : R) : sign (p.eval x) =
      sign (x - a) ^ p.rootMultiplicity a * sign (q.eval x) := by
    conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq a]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sign_mul, sign_pow, q]
  refine ⟨l, u, hla, hau, ?_, ?_⟩
  · intro x hx
    rw [hf, sign_neg (sub_neg.mpr hx.2), hlu ⟨hx.1, hx.2.trans hau⟩, hs,
      signLeft_def]
  · intro x hx
    rw [hf, sign_pos (sub_pos.mpr hx.1), one_pow, one_mul,
      hlu ⟨hla.trans hx.1, hx.2⟩, hs]

/-- A uniform interval immediately to the right of `a` on which every polynomial of a list
has its right-hand sign at `a`. -/
theorem _root_.List.exists_signs_right (cs : List R[X]) (a : R) :
    ∃ u, a < u ∧ ∀ p ∈ cs, ∀ x ∈ Ioo a u, sign (p.eval x) = p.signRight a := by
  -- Use the order topology only to combine the finitely many right-hand intervals.
  let : TopologicalSpace R := Preorder.topology R
  let : OrderTopology R := ⟨rfl⟩
  have he : ∀ᶠ x in 𝓝[>] a, ∀ p ∈ cs, sign (p.eval x) = p.signRight a := by
    refine cs.finite_toSet.eventually_all.mpr fun p _ => ?_
    obtain ⟨-, u, -, hau, -, hu⟩ := p.exists_signLeft_signRight a
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT hau) hu
  obtain ⟨u, hau, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨u, hau, fun p hp x hx => hu hx p hp⟩

/-- A uniform interval immediately to the left of `a` on which every polynomial of a list
has its left-hand sign at `a`. -/
theorem _root_.List.exists_signs_left (cs : List R[X]) (a : R) :
    ∃ l, l < a ∧ ∀ p ∈ cs, ∀ x ∈ Ioo l a, sign (p.eval x) = p.signLeft a := by
  -- Use the order topology only to combine the finitely many left-hand intervals.
  let : TopologicalSpace R := Preorder.topology R
  let : OrderTopology R := ⟨rfl⟩
  have he : ∀ᶠ x in 𝓝[<] a, ∀ p ∈ cs, sign (p.eval x) = p.signLeft a := by
    refine cs.finite_toSet.eventually_all.mpr fun p _ => ?_
    obtain ⟨l, -, hla, -, hl, -⟩ := p.exists_signLeft_signRight a
    exact Filter.mem_of_superset (Ioo_mem_nhdsLT hla) hl
  obtain ⟨l, hla, hl⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  exact ⟨l, hla, fun p hp x hx => hl hx p hp⟩

end OrderedField

end TauCeti
