/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Schemes over an empty base

Over an empty base scheme `S`, every object of the slice category `Over S` is terminal, so any two
parallel morphisms in `Over S` are equal.

## Main results

* `TauCeti.AlgebraicGeometry.isTerminalOfIsEmpty`: every object of `Over S` is terminal when `S` is
  empty.
* `TauCeti.AlgebraicGeometry.over_hom_ext_of_isEmpty`: parallel morphisms in `Over S` agree when
  `S` is empty.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {S : Scheme.{u}}

/-- Over an empty base every object of `Over S` is terminal. -/
noncomputable def isTerminalOfIsEmpty [IsEmpty S] (X : Over S) : IsTerminal X :=
  have := (isInitialOfIsEmpty (X := S)).isIso_to X.hom
  Over.mkIdTerminal.ofIso (Over.isoMk (asIso X.hom)).symm

/-- Over an empty base every object of `Over S` is terminal, so any two parallel morphisms in
`Over S` are equal. -/
theorem over_hom_ext_of_isEmpty [IsEmpty S] {X Y : Over S} (f g : X ⟶ Y) : f = g :=
  (isTerminalOfIsEmpty Y).hom_ext f g

end TauCeti.AlgebraicGeometry
