/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Noetherian

/-!
# Noetherianity and finite generation on pages of spectral sequences of modules

In a spectral sequence `(E_r)` in `ModuleCat R` over an arbitrary ring `R`, each page `E_{r+1}` is
isomorphic at every index `pq` to the homology of `E_r` at `pq`. Consequently, if `(E.page r).X pq`
is a Noetherian `R`-module, then `(E.page r').X pq` is a Noetherian `R`-module
(`CategoryTheory.SpectralSequence.isNoetherian_page_X_of_le`) and hence finitely generated
(`CategoryTheory.SpectralSequence.finite_page_X_of_le`) for every later page `r' ≥ r`, without
assuming that the ring `R` itself is Noetherian. When `[IsNoetherianRing R]` holds, any finitely
generated `(E.page r).X pq` is automatically Noetherian, so finite generation propagates across
pages as a special case.

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4.
* John McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 1.2.
-/

public section

open CategoryTheory

universe u v

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [Ring R] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- **Noetherianity propagates to later pages.** Over any ring `R`, if `(E.page r).X pq` is a
Noetherian `R`-module, then `(E.page r').X pq` is a Noetherian `R`-module for every `r' ≥ r`. -/
theorem isNoetherian_page_X_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    [h : IsNoetherian R ((E.page r).X pq)] (r' : ℤ) (hrr' : r ≤ r') :
    IsNoetherian R ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ s hrs ih =>
    have : IsNoetherian R ((E.page s (hr.trans hrs)).X pq) := ih
    exact isNoetherian_of_linearEquiv (E.iso s (s + 1) pq rfl (hr.trans hrs)).toLinearEquiv

/-- **Finite generation propagates from a Noetherian page term.** Over any ring `R`, if
`(E.page r).X pq` is a Noetherian `R`-module (for instance if `R` is a Noetherian ring and
`(E.page r).X pq` is finitely generated), then `(E.page r').X pq` is finitely generated for every
`r' ≥ r`. -/
theorem finite_page_X_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    [IsNoetherian R ((E.page r).X pq)] (r' : ℤ) (hrr' : r ≤ r') :
    Module.Finite R ((E.page r' (hr.trans hrr')).X pq) :=
  have : IsNoetherian R ((E.page r' (hr.trans hrr')).X pq) := E.isNoetherian_page_X_of_le hr r' hrr'
  Module.IsNoetherian.finite R _

end CategoryTheory.SpectralSequence
