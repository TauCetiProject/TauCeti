/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic

/-!
# Jordan splittings of a localized integral lattice

Let `L` be a nondegenerate integral lattice and `p` a prime. The localization
`L_p = ℤ_p ⊗[ℤ] L`, with its localized integral form, is an orthogonal direct sum
`L_p = ⊕_i N_i` in which the form on `N_i` is `p ^ i` times a unimodular form
(`TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`). This holds at every prime,
`p = 2` included; at `p = 2` the constituents need not be diagonalizable, and the splitting
need not be unique.

The ranks `n_i` of the constituents are nevertheless invariants of the isometry class of `L_p`:
if the localizations of two lattices are isometric, then Jordan splittings of them have
constituents of equal rank at every scale
(`TauCeti.IntegralLattice.finrank_eq_of_isJordanSplitting_localIntegralForm`). In particular the
ranks do not depend on the chosen splitting, also at `p = 2`.

## Main results

* `TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`: the localized integral
  form of a nondegenerate lattice has a Jordan splitting at every prime.
* `TauCeti.IntegralLattice.finrank_eq_of_isJordanSplitting_localIntegralForm`: the ranks of the
  Jordan constituents are invariants of the local isometry class.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C, for Jordan splittings, and 91:9, for
  the invariance of the ranks of their constituents.
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

/-- **The Jordan ranks are local isometry invariants.** If the localized integral forms of two
lattices are isometric at `p`, then Jordan splittings of them have constituents of equal rank at
every scale. Taking `M = L` shows that these ranks do not depend on the splitting. -/
theorem finrank_eq_of_isJordanSplitting_localIntegralForm {W : Type*} [AddCommGroup W]
    [Module ℚ W] {M : IntegralLattice W}
    (hLM : (L.localIntegralForm p).Equivalent (M.localIntegralForm p))
    {N : ℕ → Submodule ℤ_[p] (L.LocalCarrier p)} {N' : ℕ → Submodule ℤ_[p] (M.LocalCarrier p)}
    (hN : (L.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N)
    (hN' : (M.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N') (i : ℕ) :
    Module.finrank ℤ_[p] (N i) = Module.finrank ℤ_[p] (N' i) :=
  hN.finrank_eq_of_equivalent hN' hLM PadicInt.irreducible_p.ne_zero
    PadicInt.irreducible_p.not_isUnit i

end IntegralLattice

end TauCeti
