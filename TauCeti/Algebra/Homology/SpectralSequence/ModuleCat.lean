/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.Category.FGModuleCat.Exact
import TauCeti.Algebra.Category.ModuleCat.Rank
import TauCeti.Algebra.Homology.SpectralSequence.SerreClass

/-!
# Cardinal rank and finite generation on pages of spectral sequences of modules

Each page `E_{r+1}` of a spectral sequence `E` in `ModuleCat R` is isomorphic to the homology of
the preceding page `E_r`, so every object `(E.page r').X pq` on a later page `r' ≥ r` is a
subquotient of `(E.page r).X pq`.

Because `ModuleCat.rankLe R μ` is closed under subobjects and quotients, specializing
`CategoryTheory.SpectralSequence.prop_page_X_of_le` to `ModuleCat.rankLe R` shows that over any
ring `R`, cardinal rank does not increase across pages
(`CategoryTheory.SpectralSequence.rank_page_X_le_of_le`). Over a Noetherian ring `R`, the class
`ModuleCat.isFG R` of finitely generated modules is likewise closed under subobjects and quotients,
so finite generation passes to all later pages
(`CategoryTheory.SpectralSequence.finite_page_X_of_le`).

## Main results

* `CategoryTheory.SpectralSequence.rank_page_X_le_of_le`: over any ring, the cardinal rank of an
  object on page `r' ≥ r` is at most its cardinal rank on page `r`.
* `CategoryTheory.SpectralSequence.finite_page_X_of_le`: over a Noetherian ring, a finitely
  generated object on page `r` stays finitely generated on every page `r' ≥ r`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §1.2.
-/

public section

open CategoryTheory

universe u v

namespace CategoryTheory.SpectralSequence

section Rank

variable {R : Type u} [Ring R]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- Over any ring `R`, the cardinal rank of the object at `pq` on page `r'` of a spectral sequence
of modules is at most its cardinal rank on any earlier page `r ≤ r'`. -/
theorem rank_page_X_le_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (r' : ℤ) (hrr' : r ≤ r') :
    Module.rank R ((E.page r' (hr.trans hrr')).X pq) ≤ Module.rank R ((E.page r).X pq) :=
  (ModuleCat.rankLe_iff _).1
    (E.prop_page_X_of_le (ModuleCat.rankLe R (Module.rank R ((E.page r).X pq))) hr
      ((ModuleCat.rankLe_iff _).2 le_rfl) r' hrr')

end Rank

section Finite

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- Over a Noetherian ring, if the object at `pq` on page `r` of a spectral sequence of modules is
finitely generated, then the object at `pq` on every later page `r' ≥ r` is finitely generated. -/
theorem finite_page_X_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : Module.Finite R ((E.page r).X pq)) (r' : ℤ) (hrr' : r ≤ r') :
    Module.Finite R ((E.page r' (hr.trans hrr')).X pq) :=
  (ModuleCat.isFG_iff _).1
    (E.prop_page_X_of_le (ModuleCat.isFG R) hr ((ModuleCat.isFG_iff _).2 h) r' hrr')

end Finite

end CategoryTheory.SpectralSequence
