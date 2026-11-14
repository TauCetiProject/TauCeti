/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# K-flat complexes of flat modules

Over a commutative ring `R`, specializing `TauCeti.Algebra.Homology.Monoidal.KFlat.Basic` via
`Module.Flat` shows that any flat `R`-module in a single cohomological degree is K-flat
(`CochainComplex.isKFlat_single_of_flat_moduleCat`), and any bounded-above cochain complex of flat
`R`-modules is K-flat (`CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat`).

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4).
-/

public section

open CategoryTheory HomologicalComplex

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

/-- A flat `R`-module placed in a single cohomological degree `n` is K-flat. -/
instance isKFlat_single_of_flat_moduleCat (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℤ) :
    IsKFlat ((single (ModuleCat.{u} R) (.up ℤ) n).obj M) :=
  isKFlat_single_of_flat M n

/-- A bounded-above cochain complex of flat `R`-modules is K-flat. -/
theorem isKFlat_of_boundedAbove_flat_moduleCat (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (hP : ∀ n, Module.Flat R (P.X n)) : P.IsKFlat :=
  letI := hP
  isKFlat_of_boundedAbove_flat P b

end CochainComplex
