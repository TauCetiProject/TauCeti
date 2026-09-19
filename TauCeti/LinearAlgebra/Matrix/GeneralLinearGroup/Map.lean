/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Change of scalars on general linear groups

`Matrix.GeneralLinearGroup.map f : GL n R →* GL n S` applies a ring hom `f : R →+* S` entrywise.
Mathlib gives its functoriality (`map_id`, `map_comp`, `map_comp_apply`) but says nothing about
injectivity, nor about how the map interacts with the positive-determinant subgroup — both of
which a construction transporting a group of matrices along a change of scalars needs.

## Main results

* `Matrix.GeneralLinearGroup.map_injective`: entrywise application of an injective ring hom is
  injective on general linear groups.
* `Matrix.GeneralLinearGroup.map_mem_glpos`: a strictly monotone ring hom carries `GLPos` to
  `GLPos`, so a change of scalars restricts to the positive-determinant subgroups.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R S : Type*} [DecidableEq n] [Fintype n] [CommRing R] [CommRing S]

/-- **Entrywise application of an injective ring hom is injective on `GL n`.** A matrix over `R`
is determined by its image over `S`, and a unit by its underlying matrix. -/
theorem map_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Units.map_injective (Matrix.map_injective hf)

section StrictOrdered

variable [LinearOrder R] [IsStrictOrderedRing R] [LinearOrder S] [IsStrictOrderedRing S]

/-- A strictly monotone change of scalars restricts to the positive-determinant subgroups.

This is the side condition for cutting `Matrix.GeneralLinearGroup.map f` down to a homomorphism
`GLPos n R →* GLPos n S`; for `f = algebraMap ℚ ℝ` the hypothesis is `Rat.cast_strictMono`.
Contrast `Matrix.SpecialLinearGroup.toGLPos`, which lands in `GLPos` because the determinant
is `1`: here it is only positive, and monotonicity of `f` is what keeps it so. -/
theorem map_mem_glpos {f : R →+* S} (hf : StrictMono f) {g : GL n R} (hg : g ∈ GLPos n R) :
    g.map f ∈ GLPos n S := by
  -- the determinant commutes with the ring hom, and a strictly monotone ring hom is positive
  simpa [GeneralLinearGroup.map_det] using hf.lt_iff_lt.mpr hg

end StrictOrdered

end Matrix.GeneralLinearGroup
