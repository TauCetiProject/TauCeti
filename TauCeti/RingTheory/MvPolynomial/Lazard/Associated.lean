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
  {p q : MvPolynomial σ R}

/-- Associated polynomials have the same Lazard valuation at every point. -/
theorem lazardValuation_eq_of_associated (h : Associated p q) (a : σ → R) :
    p.lazardValuation a = q.lazardValuation a := by
  have hle {f g : MvPolynomial σ R} (hfg : f ∣ g) :
      f.lazardValuation a ≤ g.lazardValuation a := by
    obtain ⟨r, rfl⟩ := hfg
    exact (le_add_of_nonneg_right (MvPolynomial.zero_le_lazardValuation r a)).trans
      (MvPolynomial.le_lazardValuation_mul f r a)
  exact le_antisymm (hle h.dvd) (hle h.symm.dvd)

end TauCeti
