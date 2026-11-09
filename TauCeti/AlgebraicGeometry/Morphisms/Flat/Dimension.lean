/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.Topology.KrullDimension.Basic

/-!
# Dimension under flat surjective morphisms

A flat morphism of schemes is generalizing, so a flat, surjective morphism `f : X ⟶ Y` cannot
increase dimension, and if it is moreover locally quasi-finite it preserves dimension. The
pointwise dimension formula for generalizing morphisms, which in particular applies to flat ones,
is `AlgebraicGeometry.Scheme.Hom.coheight_eq_coheight_add_coheight_preimage` in
`TauCeti.AlgebraicGeometry.Morphisms.Generalizing.Dimension`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_of_flat_of_surjective`: a flat,
  surjective morphism of schemes cannot increase dimension.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_flat_of_surjective`: a flat,
  surjective, locally quasi-finite morphism of schemes preserves dimension.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_opens_eq_of_flat_of_surjective`: the
  condition that every nonempty open has a prescribed dimension descends along such a morphism.
-/

public section

open CategoryTheory Topology AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The target of a flat, surjective morphism of schemes has Krull dimension at most that of
the source. -/
theorem Scheme.Hom.topologicalKrullDim_le_of_flat_of_surjective (f : X ⟶ Y)
    [Flat f] [Surjective f] : topologicalKrullDim Y ≤ topologicalKrullDim X :=
  (Flat.generalizingMap f).topologicalKrullDim_le_of_surjective f.continuous f.surjective

/-- A flat, surjective, locally quasi-finite morphism of schemes preserves Krull dimension.
In particular, this applies to finite faithfully flat covers. -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_flat_of_surjective (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyQuasiFinite f] :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm f.topologicalKrullDim_le f.topologicalKrullDim_le_of_flat_of_surjective

/-- If every nonempty open of the source of a flat, surjective, locally quasi-finite morphism
has dimension `d`, the same holds for every nonempty open of its target. This is the dimension
condition used together with descent of regularity along finite faithfully flat covers. -/
theorem Scheme.Hom.topologicalKrullDim_opens_eq_of_flat_of_surjective (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyQuasiFinite f] {d : WithBot ℕ∞}
    (hd : ∀ U : X.Opens, Nonempty U → topologicalKrullDim U = d)
    (U : Y.Opens) [Nonempty U] : topologicalKrullDim U = d := by
  have : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹Surjective f› U
  have : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨x, -⟩ := (f ∣_ U).surjective (Classical.choice ‹Nonempty U›)
    exact ⟨x⟩
  rw [← (f ∣_ U).topologicalKrullDim_eq_of_flat_of_surjective]
  exact hd (f ⁻¹ᵁ U) inferInstance

end AlgebraicGeometry
