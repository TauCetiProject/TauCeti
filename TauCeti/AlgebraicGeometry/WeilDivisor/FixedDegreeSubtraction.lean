/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.DegreeOrder
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegreeAddition

/-!
# Subtraction of fixed-degree effective Weil divisors

This file records the residual effective divisor obtained by subtracting an effective
sub-divisor from a fixed-degree effective Weil divisor. If `E ≤ D`, with `D` of degree `e`
and `E` of degree `d`, then `D - E` is effective of degree `e - d`. The cancellation lemmas
show that this operation is inverse to the degree-indexed addition operation from
`TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegreeAddition`, up to the unavoidable casts in
the natural-number degree index.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer C symmetric-power
lane (`TauCetiRoadmap/JacobianChallenge/README.md`, "Relative effective Cartier divisors and
symmetric powers `Symᵈ X`"). The scheme-level construction is later geometry; this file supplies
the elementary residual-divisor API used when separating a fixed effective base divisor from an
unordered collection of points. No external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace EffectiveDivisorOfDegree

variable {X : Type*} {d e : ℕ}

noncomputable section

/-- If a fixed-degree effective divisor is coefficientwise below another, its degree index is
also bounded above. -/
lemma degree_le_of_le {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e}
    (hDE : (D : WeilDivisor X) ≤ E) : d ≤ e := by
  have hdeg : degree (D : WeilDivisor X) ≤ degree (E : WeilDivisor X) :=
    WeilDivisor.degree_le_of_le hDE
  have hde : (d : ℤ) ≤ e := by
    simpa [D.degree_eq, E.degree_eq] using hdeg
  exact_mod_cast hde

/-- The residual fixed-degree effective divisor `D - E`, defined when `E ≤ D`.

If `D` has degree `e` and `E` has degree `d`, the residual has degree `e - d`. -/
abbrev subOfLE (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) : EffectiveDivisorOfDegree X (e - d) :=
  ⟨(D : WeilDivisor X) - E, le_iff_isEffective_sub.mp hED, by
    have hde : d ≤ e := degree_le_of_le hED
    rw [degree_sub, D.degree_eq, E.degree_eq]
    exact (Int.ofNat_sub hde).symm⟩

/-- The underlying Weil divisor of a residual fixed-degree divisor is the difference of the
underlying Weil divisors. -/
@[simp]
lemma coe_subOfLE (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    (subOfLE D E hED : WeilDivisor X) = (D : WeilDivisor X) - E :=
  rfl

/-- The coefficient of a residual fixed-degree divisor is the difference of coefficients. -/
@[simp]
lemma coeff_subOfLE (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) (x : X) :
    coeff (subOfLE D E hED : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x - coeff (E : WeilDivisor X) x := by
  rw [coe_subOfLE, WeilDivisor.coeff_sub]

/-- The degree of the residual divisor is the difference of the degree indices. -/
@[simp]
lemma degree_subOfLE (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    degree (subOfLE D E hED : WeilDivisor X) = ((e - d : ℕ) : ℤ) :=
  (subOfLE D E hED).degree_eq

/-- Adding a sub-divisor back to its residual recovers the original divisor, up to the cast
identifying `d + (e - d)` with `e`. -/
@[simp]
lemma add_subOfLE (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    add E (subOfLE D E hED) =
      EffectiveDivisorOfDegree.cast (Nat.add_sub_of_le (degree_le_of_le hED)).symm D := by
  ext
  simp

/-- Adding the residual on the left also recovers the original divisor, up to the cast
identifying `(e - d) + d` with `e`. -/
@[simp]
lemma subOfLE_add (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    add (subOfLE D E hED) E =
      EffectiveDivisorOfDegree.cast (Nat.sub_add_cancel (degree_le_of_le hED)).symm D := by
  ext
  simp [sub_add_cancel]

/-- Subtracting the zero fixed-degree divisor leaves the original divisor, up to the cast
identifying `d - 0` with `d`. -/
@[simp]
lemma subOfLE_zero (D : EffectiveDivisorOfDegree X d) :
    subOfLE D (zero X) (by
      rw [← WeilDivisor.isEffective_iff_zero_le]
      exact D.isEffective) =
      EffectiveDivisorOfDegree.cast (Nat.sub_zero d).symm D := by
  ext
  simp

/-- Subtracting a fixed-degree divisor from itself gives the zero residual divisor. -/
@[simp]
lemma subOfLE_self (D : EffectiveDivisorOfDegree X d) :
    subOfLE D D le_rfl = EffectiveDivisorOfDegree.cast (Nat.sub_self d).symm (zero X) := by
  ext
  simp

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
