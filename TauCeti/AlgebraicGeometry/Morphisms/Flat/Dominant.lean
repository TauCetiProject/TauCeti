/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.RingTheory.Flat.NonZeroDivisors
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.Topology.KrullDimension

/-!
# Dominant morphisms to curves are flat

A dominant morphism `f : X ⟶ Y` from an integral scheme to a scheme whose local rings are
valuation rings is flat. At a point `x` of `X`, the stalk map `𝒪_{Y,f x} → 𝒪_{X,x}` is
injective, because a section of `𝒪_Y` killed by `f` vanishes on the dense image of `f`; so the
domain `𝒪_{X,x}` is a torsion-free module over the valuation ring `𝒪_{Y,f x}`, and torsion-free
modules over a valuation ring are flat.

The local rings of a scheme smooth over a field are regular, and when its dimension is at most one
they are fields or discrete valuation rings. Hence every dominant morphism from an integral scheme
to a curve smooth over a field is flat. Since a nonconstant morphism between proper integral curves
over a field is dominant, this applies to nonconstant morphisms of smooth projective curves over a
field, such as the projective model of an elliptic curve. A morphism that is smooth of relative
dimension one supplies the smoothness and dimension hypotheses through
`TauCeti.AlgebraicGeometry.SyntomicOfRelativeDimension.relativeDimensionLE`.

The hypotheses on `f` and on `Y` are needed. The inclusion of a closed point into a curve is not
dominant and not flat. The closed point `Spec k ⟶ Spec k[ε]/(ε²)` is dominant and not flat; there
the target is not reduced, although its only local ring is a principal ideal ring.

## Main results

* `AlgebraicGeometry.Scheme.Hom.stalkMap_injective_of_isDominant`: the stalk maps of a dominant
  morphism from an integral scheme to a reduced scheme are injective.
* `AlgebraicGeometry.Scheme.Hom.flat_of_isDominant_of_valuationRing`: a dominant morphism from an
  integral scheme to a scheme whose local rings are valuation rings is flat.
* `AlgebraicGeometry.Scheme.Hom.flat_of_isDominant_of_smooth`: a dominant morphism from an integral
  scheme to a scheme smooth over a field, of dimension at most one, is flat.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.7, for flatness over a regular integral
  scheme of dimension one.
-/

public section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

/-- The stalk maps of a dominant morphism from an integral scheme to a reduced scheme are
injective. -/
theorem stalkMap_injective_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsReduced Y] [IsDominant f]
    (x : X) : Function.Injective (f.stalkMap x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (f x))
  refine hU.stalkMap_injective f x hxU fun g hg ↦ ?_
  rw [Scheme.Hom.germ_stalkMap_apply] at hg
  -- `f` kills `g`, since the stalks of the integral scheme `X` see every nonzero section.
  have hfg : f.app U g = 0 :=
    germ_injective_of_isIntegral X (U := f ⁻¹ᵁ U) x hxU (hg.trans (map_zero _).symm)
  -- So no point of the dense image of `f` lies where `g` is nonzero, and `g` vanishes.
  suffices g = 0 by rw [this, map_zero]
  rw [← basicOpen_eq_bot_iff, ← Opens.not_nonempty_iff_eq_bot]
  intro hne
  obtain ⟨x', hx'⟩ := f.denseRange.exists_mem_open (Y.basicOpen g).isOpen hne
  have := f.mem_preimage.mpr hx'
  rw [preimage_basicOpen, hfg, Scheme.basicOpen_zero] at this
  exact this

/-- At a point where the target has a valuation ring as local ring, the stalk map of a dominant
morphism from an integral scheme to a reduced scheme is flat. -/
theorem flat_stalkMap_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsReduced Y] [IsDominant f]
    (x : X) [IsDomain (Y.presheaf.stalk (f x))] [ValuationRing (Y.presheaf.stalk (f x))] :
    (f.stalkMap x).hom.Flat := by
  algebraize [(f.stalkMap x).hom]
  refine Module.Flat.flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout.mpr fun r hr ↦ ?_
  exact mem_nonZeroDivisors_of_ne_zero
    ((map_ne_zero_iff _ (f.stalkMap_injective_of_isDominant x)).mpr hr)

/-- **A dominant morphism to a scheme with valuation rings as local rings is flat.** If `X` is
integral and every local ring of `Y` is a valuation ring, as for a Dedekind scheme, then a
dominant morphism `X ⟶ Y` is flat. -/
theorem flat_of_isDominant_of_valuationRing (f : X ⟶ Y) [IsIntegral X] [IsDominant f]
    [∀ y : Y, IsDomain (Y.presheaf.stalk y)] [∀ y : Y, ValuationRing (Y.presheaf.stalk y)] :
    Flat f :=
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  .of_stalkMap f fun x ↦ f.flat_stalkMap_of_isDominant x

/-- **A dominant morphism to a smooth curve over a field is flat.** If `Y` is smooth over a field
`K` with all fibres of dimension at most one, then every dominant morphism from an integral scheme
to `Y` is flat. The local rings of `Y` are regular of dimension at most one, hence valuation
rings. -/
theorem flat_of_isDominant_of_smooth {K : Type u} [Field K] (f : X ⟶ Y)
    (g : Y ⟶ Spec (.of K)) [Smooth g] [RelativeDimensionLE 1 g] [IsIntegral X] [IsDominant f] :
    Flat f := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := isRegularLocalRing_stalk_of_smooth g
  have hdim : topologicalKrullDim Y ≤ 1 := (relativeDimensionLE_iff_of_field g).mp inferInstance
  have : ∀ y : Y, ValuationRing (Y.presheaf.stalk y) := fun y ↦
    IsRegularLocalRing.valuationRing_of_ringKrullDim_le_one <| by
      rw [ringKrullDim_stalk_eq_coheight]
      exact (coheight_le_topologicalKrullDim y).trans hdim
  exact f.flat_of_isDominant_of_valuationRing

end Scheme.Hom

end AlgebraicGeometry
