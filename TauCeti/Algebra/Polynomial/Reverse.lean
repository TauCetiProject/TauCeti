/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Root multiplicities in reciprocal coordinates

Reflection at a fixed degree bound preserves the multiplicity of each invertible root,
replacing that root by its inverse. For a nonzero polynomial, the multiplicity of zero in
the reflection is exactly the difference between the degree bound and the actual degree.
These statements apply to formal reversals after coefficient specialization, even when
specialization lowers the degree or annihilates the entire polynomial.

The fixed-bound statements are useful for descending root sections from reciprocal
coordinates: a degree drop contributes roots at zero in the reflected family, while
all invertible roots retain their original multiplicities. In a translated reciprocal
coordinate, these correspond to the original finite roots away from the translation center.

The multiplicity transport at invertible roots works over arbitrary commutative rings,
including rings with zero divisors. The zero-root statements work over arbitrary rings.
No splitting hypothesis is needed.
-/

public section

namespace Polynomial

variable {R S : Type*}

/-- Reflection of a power at the corresponding multiple of a degree bound is the power
of the reflection. -/
@[simp]
theorem reflect_pow [Semiring R] (p : R[X]) {N : ℕ} (hN : p.natDegree ≤ N) (k : ℕ) :
    (p ^ k).reflect (k * N) = p.reflect N ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul, reflect_mul _ _ (natDegree_pow_le_of_le k hN) hN,
      ih, pow_succ]

/-- Reflection exchanges an invertible root with its inverse, preserving its multiplicity.
The degree bound can exceed the actual degree, and the zero polynomial is included. -/
@[simp]
theorem rootMultiplicity_reflect [CommRing R] (p : R[X]) {N : ℕ}
    (hN : p.natDegree ≤ N) (u : Rˣ) :
    (p.reflect N).rootMultiplicity (↑u⁻¹) = p.rootMultiplicity (↑u) := by
  by_cases hp : p = 0
  · simp [hp]
  have := Nontrivial.of_polynomial_ne hp
  let : Invertible (↑u : R) := u.isUnit.invertible
  obtain ⟨q, heq, hqroot⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp (↑u)
  let m := p.rootMultiplicity (↑u)
  have hq : q ≠ 0 := right_ne_zero_of_mul (heq ▸ hp)
  have hdeg : p.natDegree = m + q.natDegree := by
    rw [heq, ((monic_X_sub_C (↑u)).pow m).natDegree_mul' hq]
    simp [m, (monic_X_sub_C (↑u : R)).natDegree_pow]
  have hqN : q.natDegree ≤ N - m := by omega
  have hmN : m ≤ N := by omega
  have hlinear : (X - C (↑u : R)).reflect 1 =
      C (-(↑u : R)) * (X - C (↑u⁻¹ : R)) := by
    rw [reflect_sub, reflect_one_X, reflect_C, mul_sub, ← C_mul]
    simp [sub_eq_add_neg, add_comm]
  have hfactor : p.reflect N =
      (C ((-(↑u : R)) ^ m) * q.reflect (N - m)) * (X - C (↑u⁻¹ : R)) ^ m := by
    have hpow : ((X - C (↑u : R)) ^ m).reflect m =
        (C (-(↑u : R)) * (X - C (↑u⁻¹ : R))) ^ m := by
      rw [← hlinear, ← reflect_pow _ (N := 1) (by simp), Nat.mul_one]
    conv_lhs => rw [heq]
    conv_lhs => arg 1; rw [← Nat.add_sub_of_le hmN]
    rw [reflect_mul _ _ (by simp [m, (monic_X_sub_C (↑u : R)).natDegree_pow]) hqN,
      hpow, mul_pow, ← C_pow]
    ring
  have hqeval : (q.reflect (N - m)).eval (↑u⁻¹) ≠ 0 := by
    have hqeval : q.eval (↑u) ≠ 0 := by
      simpa only [dvd_iff_isRoot, IsRoot.def] using hqroot
    simpa only [invOf_units, eval₂_id] using
      (eval₂_reflect_eq_zero_iff (RingHom.id R) (↑u) (N - m) q hqN).not.2 hqeval
  have heval : (C ((-(↑u : R)) ^ m) * q.reflect (N - m)).eval (↑u⁻¹) ≠ 0 := by
    rw [eval_mul, eval_C]
    exact fun h ↦ hqeval (((u.isUnit.neg.pow m).mul_right_eq_zero).1 h)
  have hres : C ((-(↑u : R)) ^ m) * q.reflect (N - m) ≠ 0 := by
    intro h
    exact heval (by rw [h, eval_zero])
  rw [hfactor, rootMultiplicity_mul_X_sub_C_pow hres,
    rootMultiplicity_eq_zero (by simpa only [IsRoot.def] using heval), zero_add]

/-- The excess of a reflection bound over the degree of a nonzero polynomial is exactly
the multiplicity of zero in its reflection. -/
@[simp]
theorem rootMultiplicity_reflect_zero [Ring R] (p : R[X]) (hp : p ≠ 0) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (p.reflect N).rootMultiplicity 0 = N - p.natDegree := by
  rw [rootMultiplicity_eq_natTrailingDegree']
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_reflect, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hN]
    exact leadingCoeff_ne_zero.mpr hp
  · apply le_natTrailingDegree (reflect_eq_zero_iff.not.2 hp)
    intro k hk
    rw [coeff_reflect, revAt_le (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Reversal preserves multiplicity at nonzero roots, replacing each root by its inverse. -/
@[simp]
theorem rootMultiplicity_reverse [Field R] (p : R[X]) {a : R} (ha : a ≠ 0) :
    p.reverse.rootMultiplicity a⁻¹ = p.rootMultiplicity a := by
  simpa only [Units.val_inv_eq_inv_val, Units.val_mk0, reverse] using
    p.rootMultiplicity_reflect le_rfl (Units.mk0 a ha)

/-- Specializing a formal reversal preserves the multiplicities of invertible roots of the
specialized polynomial, even when specialization lowers the degree or gives zero. -/
@[simp]
theorem rootMultiplicity_map_reverse [Semiring R] [CommRing S] (p : R[X])
    (f : R →+* S) (u : Sˣ) :
    (p.reverse.map f).rootMultiplicity (↑u⁻¹) = (p.map f).rootMultiplicity (↑u) := by
  rw [reverse, ← reflect_map]
  exact (p.map f).rootMultiplicity_reflect natDegree_map_le u

/-- When a nonzero specialization drops degree, that degree drop is exactly the multiplicity
of zero in the specialized formal reversal. -/
@[simp]
theorem rootMultiplicity_map_reverse_zero [Semiring R] [Ring S] (p : R[X])
    (f : R →+* S) (hp : p.map f ≠ 0) :
    (p.reverse.map f).rootMultiplicity 0 = p.natDegree - (p.map f).natDegree := by
  rw [reverse, ← reflect_map]
  exact (p.map f).rootMultiplicity_reflect_zero hp natDegree_map_le

end Polynomial
