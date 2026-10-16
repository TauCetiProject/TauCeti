/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Henselian
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

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

At an odd prime the constituents themselves are invariants up to isometry, and they decide the
local isometry class: the localizations of two lattices are isometric exactly when, for Jordan
splittings of them, the constituents of each scale are isometric
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_forall_equivalent_restrict`). Each
constituent is `p ^ i` times a unimodular form, classified by its rank and the square class of its
determinant, so the Jordan data of a lattice at an odd prime are these ranks and square classes.

## Main results

* `TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`: the localized integral
  form of a nondegenerate lattice has a Jordan splitting at every prime.
* `TauCeti.IntegralLattice.finrank_eq_of_isJordanSplitting_localIntegralForm`: the ranks of the
  Jordan constituents are invariants of the local isometry class.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_forall_equivalent_restrict`: at an odd
  prime, the Jordan constituents up to isometry classify the local isometry class.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C, for Jordan splittings, 91:9, for the
  invariance of the ranks of their constituents, and 92:1--92:2, for the odd-prime case.
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

/-- **Jordan splittings classify localizations at odd primes.** At an odd prime, the localized
integral forms of two lattices are isometric exactly when, for Jordan splittings of them, the
constituents of each scale are isometric. Taking `M = L`, the constituents of a Jordan splitting
are unique up to isometry. Each constituent is `p ^ i` times a unimodular form over `ℤ_p`, which is
classified by its rank and the square class of its determinant. -/
theorem localIntegralForm_equivalent_iff_forall_equivalent_restrict {W : Type*} [AddCommGroup W]
    [Module ℚ W] {M : IntegralLattice W} (hp : p ≠ 2)
    {N : ℕ → Submodule ℤ_[p] (L.LocalCarrier p)} {N' : ℕ → Submodule ℤ_[p] (M.LocalCarrier p)}
    (hN : (L.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N)
    (hN' : (M.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N') :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      ∀ i, ((L.localIntegralForm p).restrict (N i)).Equivalent
        ((M.localIntegralForm p).restrict (N' i)) :=
  hN.equivalent_iff_forall_equivalent_restrict hN' (L.isSymm_localIntegralForm p)
    (PadicInt.isUnit_two hp) PadicInt.irreducible_p.ne_zero PadicInt.irreducible_p.not_isUnit

end IntegralLattice

end TauCeti
