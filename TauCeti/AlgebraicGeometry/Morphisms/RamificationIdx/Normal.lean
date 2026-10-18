/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx
public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Ramification indices at points with discrete valuation local rings

At a point `x` of `X` whose image has codimension one on a locally Noetherian normal scheme `Y`,
the local ring `𝒪_{Y,f(x)}` is a discrete valuation ring, so the stalk map of a dominant `f` from
an integral scheme is flat (`AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_isDominant`), and
Mathlib's `Ideal.ramificationIdx_tower` makes ramification indices multiply along a composite.

At a point `x` of codimension one of a locally Noetherian normal integral scheme `X`, the local
ring `𝒪_{X,x}` is a discrete valuation ring, and for a dominant `f` whose image point is not the
generic point, `𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with `e = ramificationIdxAt f x`. When `𝒪_{Y,f(x)}`
is also a discrete valuation ring (for instance when `Y` is locally Noetherian and normal and
`f x` has codimension one), `e` is the ramification index of the extension of discrete valuation
rings (Stacks, Definition 15.113.1 (09E4)).

## Main results

* `TauCeti.NormalSchemes.ramificationIdxAt_comp`: `e_x(f ≫ g) = e_x(f) e_{f(x)}(g)` when `f` is a
  dominant morphism from an integral scheme and `f x` has coheight one on a locally Noetherian
  normal scheme.
* `TauCeti.NormalSchemes.map_maximalIdeal_eq_pow_ramificationIdxAt`: at a point of coheight one of
  a locally Noetherian normal integral scheme, `𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with
  `e = ramificationIdxAt f x`. This is the roadmap target `ramificationIdxAt_eq_dvr`.

## References

* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0): `ramificationIdxAt_comp` is its
  `Pcf.schemeDivisorRamificationIdx_comp` (`lean/Pcf/Bounding/SchemeDynamics.lean`, there with `f`
  finite and `x` of coheight one), and `map_maximalIdeal_eq_pow_ramificationIdxAt` is the scheme
  form of its `Pcf.heightOneRamificationIdx_eq_dvrExponent` (`lean/Pcf/Bounding/Divisors.lean`).
-/

public section

open CategoryTheory AlgebraicGeometry Order IsLocalRing TauCeti.AlgebraicGeometry

namespace TauCeti.NormalSchemes

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Ramification indices multiply in towers.** For a dominant morphism `f : X ⟶ Y` from an
integral scheme and a point `x` whose image has coheight one on the locally Noetherian normal
scheme `Y`, `e_x(f ≫ g) = e_x(f) e_{f(x)}(g)` for every `g : Y ⟶ Z`. The local ring of `Y` at
`f x` is a discrete valuation ring, over which the stalk map of `f` is flat. -/
theorem ramificationIdxAt_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsDominant f] [IsIntegral X]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] (x : X)
    (hfx : coheight (f x) = 1) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  -- `(f ≫ g) x` is `g (f x)` by definition, so the stalk of `Z` at `(f ≫ g) x`, the codomain of
  -- `(f ≫ g).stalkMap x`, is the stalk at `g (f x)`; the algebra structures below rely on this.
  let R := Z.presheaf.stalk (g (f x))
  let S := Y.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  let : Algebra R S := (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra S T := (f.stalkMap x).hom.toAlgebra
  let : Algebra R T := ((f ≫ g).stalkMap x).hom.toAlgebra
  have hcomp : ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    exact CommRingCat.hom_comp _ _
  have : IsScalarTower R S T := .of_algebraMap_eq' hcomp
  have : IsLocalHom (algebraMap S T) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : IsDiscreteValuationRing S := IsNormalScheme.isDiscreteValuationRing_stalk Y (f x) hfx
  have : Module.Flat S T := RingHom.flat_algebraMap_iff.mp (f.flat_stalkMap_of_isDominant x)
  rw [ramificationIdxAt_def, ramificationIdxAt_def, ramificationIdxAt_def, mul_comm]
  exact Ideal.ramificationIdx_tower (R := R) (maximalIdeal S) (maximalIdeal T)

/-- **The ramification index at a codimension-one point.** At a point `x` of coheight one of a
locally Noetherian normal integral scheme `X`, for a dominant `f : X ⟶ Y` to a reduced scheme with
`f x` not of coheight zero, the local ring `𝒪_{X,x}` is a discrete valuation ring and
`𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with `e = ramificationIdxAt f x`. When `𝒪_{Y,f(x)}` is also a
discrete valuation ring, `e` is the ramification index of the extension `𝒪_{Y,f(x)} → 𝒪_{X,x}` of
Stacks, Definition 15.113.1 (09E4). This is the roadmap target `ramificationIdxAt_eq_dvr`. -/
@[stacks 09E4 "the ramification index of the stalk extension"]
theorem map_maximalIdeal_eq_pow_ramificationIdxAt [IsDominant f] [IsIntegral X] [IsReduced Y]
    [IsLocallyNoetherian X] [IsNormalScheme X] (x : X) (hx : coheight x = 1)
    (hfx : coheight (f x) ≠ 0) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsNormalScheme.isDiscreteValuationRing_stalk X x hx
  -- The maximal ideal of `𝒪_{Y,f(x)}` is nonzero, as this local ring has positive dimension, and
  -- the stalk map is injective.
  have hne : maximalIdeal (Y.presheaf.stalk (f x)) ≠ ⊥ := by
    intro hbot
    have hfield : IsField (Y.presheaf.stalk (f x)) :=
      isField_iff_maximalIdeal_eq.mpr hbot
    have hdim := ringKrullDim_stalk_eq_coheight (f x)
    rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact hfx (WithBot.coe_injective hdim).symm
  have hmap : (maximalIdeal (Y.presheaf.stalk (f x))).map
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) ≠ ⊥ := by
    have hinj : Function.Injective
        (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      f.stalkMap_injective_of_isDominant x
    rw [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj, le_bot_iff]
    exact hne
  rw [ramificationIdxAt_def]
  exact IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap

end TauCeti.NormalSchemes
