/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting
public import TauCeti.NumberTheory.IntegralLattice.Localization

/-!
# Jordan splittings of a localized integral lattice

Let `L` be a nondegenerate integral lattice and `p` a prime. The localization
`L_p = ℤ_p ⊗[ℤ] L`, with its localized integral form, is an orthogonal direct sum
`L_p = ⊕_i N_i` in which the form on `N_i` is `p ^ i` times a unimodular form
(`TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`). This holds at every prime,
`p = 2` included; at `p = 2` the constituents need not be diagonalizable, and the splitting is
not unique.

## Main results

* `TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`: the localized integral
  form of a nondegenerate lattice has a Jordan splitting at every prime.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 91:9.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, Theorem 4.1.
-/

public section

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

variable (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- **Jordan splittings exist at every prime.** The localized integral form of a nondegenerate
integral lattice is an orthogonal direct sum of constituents `N i` on which it is `p ^ i` times a
unimodular form. -/
theorem exists_isJordanSplitting_localIntegralForm (hL : L.form.Nondegenerate) :
    ∃ N : ℕ → Submodule ℤ_[p] (L.LocalCarrier p),
      (L.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N :=
  (L.isSymm_localIntegralForm p).exists_isJordanSplitting
    ((L.nondegenerate_localIntegralForm_iff p).mpr hL) PadicInt.irreducible_p

end IntegralLattice

end TauCeti
