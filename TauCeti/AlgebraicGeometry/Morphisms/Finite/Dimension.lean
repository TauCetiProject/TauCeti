/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Scheme.ZeroLocusComponents

/-!
# Finiteness of proper generalizing morphisms of equal dimension

A proper generalizing morphism, such as a proper flat morphism, between irreducible schemes
locally of finite type over a field is finite if the schemes have equal Krull dimension.
Closedness bounds the dimension of the closure of the image of a point by the dimension of its
closure in the source. Lifting generalizations similarly bounds the codimension of the image.
The sum of these dimensions is the same in the source and target, so the dimension of the point
closure is constant along each fibre. Properness and finite fibres then give finiteness.

## References

* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS).
-/

public section

open CategoryTheory Order Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A proper generalizing morphism over a field between irreducible schemes of equal Krull
dimension is finite. The target is locally of finite type over the field. -/
theorem isFinite_of_generalizingMap_of_topologicalKrullDim_eq (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IrreducibleSpace X] [IrreducibleSpace Y] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] (hf : GeneralizingMap f)
    (hdim : topologicalKrullDim X = topologicalKrullDim Y) : IsFinite f := by
  have hX : LocallyOfFiniteType (X ↘ Spec (.of k)) := by
    rw [← comp_over f (Spec (.of k))]
    infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have hheight (x : X) : height x = height (f x) := by
    have hle := f.isClosedMap.specializingMap.height_apply_le_height x
    refine le_antisymm (le_of_not_gt fun hlt ↦ ?_) hle
    have hcoheight := hf.coheight_apply_le_coheight f.continuous x
    have hfinite := (TauCeti.AlgebraicGeometry.Scheme.coheight_lt_top (f x)).ne
    have hsum := ENat.add_lt_add_of_le_of_lt hfinite hcoheight hlt
    have hsum' : (coheight (f x) : WithBot ℕ∞) + height (f x) <
        (coheight x : WithBot ℕ∞) + height x := by exact_mod_cast hsum
    rw [TauCeti.AlgebraicGeometry.coheight_add_height_eq_topologicalKrullDim k,
      TauCeti.AlgebraicGeometry.coheight_add_height_eq_topologicalKrullDim k, hdim] at hsum'
    exact lt_irrefl _ hsum'
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦
    TauCeti.AlgebraicGeometry.finite_preimage_singleton_of_height_eq k f y fun x hx ↦
      hx ▸ hheight x
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end AlgebraicGeometry.Scheme.Hom
