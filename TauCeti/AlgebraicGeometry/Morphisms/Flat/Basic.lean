/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Flat morphisms: restrictions and generic points

Flatness on an open subset of the target is equivalent to flatness of the original stalk
maps at all points lying over that open subset.

A flat morphism of schemes is generalizing: every generization of the image of a point lifts to
a generization of that point. Between irreducible schemes this forces the generic point of the
source to map to the generic point of the target, since the generic point of the target
generizes the image of the generic point of the source, and the generic point of the source has no
proper generization. This is the dominance of a flat morphism between irreducible schemes, for
instance of a flat model of a curve over a discrete valuation ring, whose generic point lies in
the generic fibre.

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_restrict_iff`: the stalk criterion for flatness of a
  restriction.
* `AlgebraicGeometry.Scheme.Hom.genericPoint_eq_of_flat`: a flat morphism between irreducible
  schemes sends the generic point to the generic point.

## References

* [The Stacks Project, Lemma 29.25.9](https://stacks.math.columbia.edu/tag/01U1), flat
  morphisms are generalizing.
-/

public section

open AlgebraicGeometry

namespace TauCeti

universe u

/-- A flat morphism between irreducible schemes sends the generic point to the generic point. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.genericPoint_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IrreducibleSpace X] [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by
  -- Flat morphisms are generalizing, so the generic point of `Y` lifts to a generization of the
  -- generic point of `X`, which can only be that generic point itself.
  obtain ⟨η, hη, hfη⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  rw [← hfη, (hη.antisymm (genericPoint_specializes η)).eq]

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

/-- Flatness of a restriction is equivalent to flatness of the original stalk maps
at all points lying above the chosen open subset of the target. -/
theorem flat_restrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Flat (f ∣_ U) ↔ ∀ x : X, f x ∈ U → (f.stalkMap x).hom.Flat := by
  rw [Flat.iff_flat_stalkMap]
  constructor
  · intro h x hx
    exact (CommRingCat.flat.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U ⟨x, hx⟩)).mp (h ⟨x, hx⟩)
  · intro h x
    exact (CommRingCat.flat.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U x)).mpr (h x.1 x.2)

end AlgebraicGeometry.Scheme.Hom
