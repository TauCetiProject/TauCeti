/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

import TauCeti.Algebra.Category.FGModuleCat.Basic
import TauCeti.Algebra.Homology.SpectralSequence.SerreClass

/-!
# Spectral sequences of modules

This file records lightweight persistence results for spectral sequences in `ModuleCat R`,
independent of Euler characteristics.

* `CategoryTheory.SpectralSequence.finite_page_X_of_le`: over a Noetherian ring `R`, finite
  generation of an object on page `r` persists to every later page `r' ≥ r`.
-/

public section

namespace CategoryTheory.SpectralSequence

universe v u

variable {R : Type u} [Ring R] [IsNoetherianRing R] {κ : Type*} {c : ℤ → ComplexShape κ}
  {r₀ : ℤ}

/-- Over a Noetherian ring, finite generation of an object on page `r` persists to every later
page `r' ≥ r`. -/
lemma finite_page_X_of_le (E : SpectralSequence (ModuleCat.{v} R) c r₀)
    {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (h : Module.Finite R ((E.page r hr).X pq))
    (r' : ℤ) (hrr' : r ≤ r') :
    Module.Finite R ((E.page r' (hr.trans hrr')).X pq) :=
  (ModuleCat.isFG_iff _).1
    (E.prop_page_X_of_le (ModuleCat.isFG R) hr ((ModuleCat.isFG_iff _).2 h) r' hrr')

end CategoryTheory.SpectralSequence
