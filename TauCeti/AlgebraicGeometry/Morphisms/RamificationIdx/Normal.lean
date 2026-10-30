/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# Ramification indices at points with discrete valuation local rings

At a point `x` of `X` whose image has codimension one on a locally Noetherian normal scheme `Y`,
ramification indices multiply along a composite when `f : X ⟶ Y` is dominant and `X` is integral.

At a point `x` of codimension one of a locally Noetherian normal integral scheme `X`, the local
ring `𝒪_{X,x}` is a discrete valuation ring, and for a dominant `f` to a reduced scheme `Y` whose
image point is not the generic point, `𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with
`e = ramificationIdxAt f x`. When `𝒪_{Y,f(x)}` is also a discrete valuation ring (for instance when
`Y` is locally Noetherian and normal and
`f x` has codimension one), `e` is the ramification index of the extension of discrete valuation
rings (Stacks, Definition 15.113.1 (09E4)).

## Main results

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_comp_of_coheight_eq_one`: ramification indices
  multiply for a dominant morphism from an integral scheme when the intermediate point has
  coheight one on a locally Noetherian normal scheme.
* `AlgebraicGeometry.Scheme.Hom.map_maximalIdeal_eq_pow_ramificationIdxAt`: at a point of coheight
  one of a locally Noetherian normal integral scheme and for a dominant map to a reduced scheme
  with non-generic image point, `𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with `e = ramificationIdxAt f x`.

## References

* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0):
  `ramificationIdxAt_comp_of_coheight_eq_one` generalizes its
  `Pcf.schemeDivisorRamificationIdx_comp` (`lean/Pcf/Bounding/SchemeDynamics.lean`, there with `f`
  finite and `x` of coheight one), and `map_maximalIdeal_eq_pow_ramificationIdxAt` is the scheme
  form of its `Pcf.heightOneRamificationIdx_eq_dvrExponent` (`lean/Pcf/Bounding/Divisors.lean`).
-/

public section

open CategoryTheory AlgebraicGeometry Order IsLocalRing TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Ramification indices multiply in towers.** For a dominant morphism `f : X ⟶ Y` from an
integral scheme and a point `x` whose image has coheight one on the locally Noetherian normal
scheme `Y`, `e_x(f ≫ g) = e_x(f) e_{f(x)}(g)` for every `g : Y ⟶ Z`. -/
theorem ramificationIdxAt_comp_of_coheight_eq_one {Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsDominant f] [IsIntegral X]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] (x : X)
    (hfx : coheight (f x) = 1) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  have : IsDiscreteValuationRing (Y.presheaf.stalk (f x)) :=
    IsNormalScheme.isDiscreteValuationRing_stalk Y (f x) hfx
  exact f.ramificationIdxAt_comp_of_flat_stalkMap g x (f.flat_stalkMap_of_isDominant x)

/-- **The ramification index at a codimension-one point.** At a point `x` of coheight one of a
locally Noetherian normal integral scheme `X`, for a dominant `f : X ⟶ Y` to a reduced scheme with
`f x` not of coheight zero, the local ring `𝒪_{X,x}` is a discrete valuation ring and
`𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with `e = ramificationIdxAt f x`. When `𝒪_{Y,f(x)}` is also a
discrete valuation ring, `e` is the ramification index of the extension `𝒪_{Y,f(x)} → 𝒪_{X,x}` of
Stacks, Definition 15.113.1 (09E4). -/
@[stacks 09E4 "the ramification index of the stalk extension"]
theorem map_maximalIdeal_eq_pow_ramificationIdxAt [IsDominant f] [IsIntegral X] [IsReduced Y]
    [IsLocallyNoetherian X] [IsNormalScheme X] (x : X) (hx : coheight x = 1)
    (hfx : coheight (f x) ≠ 0) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
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
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsNormalScheme.isDiscreteValuationRing_stalk X x hx
  exact f.map_maximalIdeal_eq_pow_ramificationIdxAt_of_map_ne_bot x hmap

end AlgebraicGeometry.Scheme.Hom
