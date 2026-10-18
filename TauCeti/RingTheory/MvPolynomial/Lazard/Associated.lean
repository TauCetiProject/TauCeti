/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Valuation

/-!
# Lazard valuations of associated polynomials

Multiplication by a polynomial unit does not change a Lazard valuation. Thus valuation
invariance of projection polynomials depends only on their associate classes, not on the
normalizations used for polynomial contents or irreducible factors.
-/

public section

namespace TauCeti

variable {σ R : Type*} [LinearOrder σ] [WellFoundedGT σ] [CommSemiring R]
  [NoZeroDivisors R] [Nontrivial R] {p q : MvPolynomial σ R}

/-- Associated polynomials have the same Lazard valuation at every point. -/
theorem lazardValuation_eq_of_associated (h : Associated p q) (a : σ → R) :
    p.lazardValuation a = q.lazardValuation a := by
  obtain ⟨u, rfl⟩ := h
  rw [MvPolynomial.lazardValuation_mul]
  have hu : (u : MvPolynomial σ R).lazardValuation a = 0 :=
    MvPolynomial.lazardValuation_eq_zero_iff.mpr
      ((u.isUnit.map (MvPolynomial.eval a)).ne_zero)
  rw [hu, add_zero]

end TauCeti
