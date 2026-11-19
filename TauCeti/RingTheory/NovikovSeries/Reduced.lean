/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Basic
public import TauCeti.Algebra.MonoidAlgebra.Reduced
public import TauCeti.RingTheory.NovikovSeries.LeadingTerm

/-!
# Reduced Novikov rings

A Novikov ring is reduced exactly when its group ring is reduced
(`TauCeti.NovikovSeries.isReduced_iff`). In particular, over a formally real
commutative semiring such as `ℤ`, it is reduced for every abelian exponent group,
including groups with torsion. Neither finite generation nor injectivity of the
period map is needed.

This supplies reducedness before passing to total quotient rings: retaining
finite deck torsion can introduce zero divisors, but does not introduce nilpotents
over `ℤ`. No field or finite-product decomposition is asserted here.

The reducedness equivalence holds for every semiring `R`, additive monoid `H`,
and period homomorphism `N : H →+ ℝ`: `NovikovSeries R H N` is reduced exactly
when `AddMonoidAlgebra R H` is reduced.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*,
  Forum Math. 14 (2002), Section 2.
* D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977:
  reducedness of group algebras over formally real coefficients is supplied by
  `AddMonoidAlgebra.isReduced_of_isFormallyReal`.
-/

public section

namespace TauCeti.NovikovSeries

variable {R H : Type*} [Semiring R] [AddMonoid H] {N : H →+ ℝ}

/- The argument uses the full finite leading term in the group ring, not a single
leading coefficient. If a nonzero series had square zero, its nonzero leading
term would have square zero as well. -/
/-- Period-controlled completion preserves reducedness of `AddMonoidAlgebra R H`
for every semiring `R`, additive monoid `H`, and period homomorphism `N : H →+ ℝ`. -/
instance instIsReduced [IsReduced (AddMonoidAlgebra R H)] :
    IsReduced (NovikovSeries R H N) := by
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro a ha
  by_contra ha₀
  have hlead : a.leadingTerm * a.leadingTerm ≠ 0 := by
    rw [← pow_two]
    exact fun h => ha₀ (leadingTerm_eq_zero_iff.1 (IsNilpotent.eq_zero ⟨2, h⟩))
  have hmul := leadingTerm_mul_of_ne_zero hlead
  rw [← pow_two, ha, leadingTerm_zero] at hmul
  exact hlead hmul.symm

/-- A Novikov ring is reduced if and only if its group ring is reduced.
This holds for every period homomorphism, including the zero map. -/
theorem isReduced_iff :
    IsReduced (NovikovSeries R H N) ↔ IsReduced (AddMonoidAlgebra R H) := by
  constructor
  · intro h
    -- The injective coefficient-preserving group-ring inclusion reflects reducedness.
    exact isReduced_of_injective (ofAddMonoidAlgebra (N := N))
      ofAddMonoidAlgebra_injective
  · intro h
    infer_instance

end TauCeti.NovikovSeries
