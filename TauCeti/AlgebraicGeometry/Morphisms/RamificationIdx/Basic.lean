/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.RamificationInertia.QuasiFinite

/-!
# The ramification index of a morphism at a point

The ramification index `ramificationIdxAt f x` of a morphism of schemes `f : X ⟶ Y` at a point
`x` is Mathlib's ramification index `Ideal.ramificationIdx` of the maximal ideal of the local ring
`𝒪_{X,x}` over `𝒪_{Y,f(x)}` along the stalk map, that is, the length of
`𝒪_{X,x} ⧸ 𝔪_{f(x)} 𝒪_{X,x}` when this length is finite, and `0` when it is infinite. When the stalk
map is a finite injective local homomorphism of discrete valuation rings, this is the usual
ramification index of that extension (Stacks, Definition 15.113.1 (09E4)).

It is finite and positive at every point where `f` is quasi-finite, since the stalk map is then
quasi-finite and `Ideal.ramificationIdx_pos_of_quasiFiniteAt` applies.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt`: the ramification index of a morphism at a point.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_def`: the defining equation.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_pos`: the ramification index is positive at every
  point where the morphism is quasi-finite.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_comp_of_flat_stalkMap`: ramification indices
  multiply in a tower when the first stalk map is flat.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_comp`: ramification indices multiply in a tower
  whose first morphism is flat.
* `AlgebraicGeometry.Scheme.Hom.map_maximalIdeal_eq_pow_ramificationIdxAt_of_map_ne_bot`: when the
  source stalk is a DVR and the mapped maximal ideal is nonzero, it equals the power of the source
  maximal ideal with exponent the ramification index.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_map_maximalIdeal_eq_pow`: when the source
  stalk is a DVR, the index equals any exponent satisfying that maximal-ideal identity.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Bounding/SchemeDynamics.lean`: `ramificationIdxAt` is its
  `Pcf.schemeDivisorRamificationIdx` (there restricted to codimension-one points), and
  `ramificationIdxAt_pos` generalizes its `Pcf.schemeDivisorRamificationIdx_pos` (there for a
  locally quasi-finite morphism). The composition theorem generalizes its
  `Pcf.schemeDivisorRamificationIdx_comp` (there for a finite dominant first morphism with integral
  source and a codimension-one point on a locally Noetherian normal intermediate scheme).
  The maximal-ideal comparison generalizes its `Pcf.heightOneRamificationIdx_eq_dvrExponent`
  (`lean/Pcf/Bounding/Divisors.lean`).
* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The **ramification index of `f` at `x`**: the ramification index (Mathlib
`Ideal.ramificationIdx`) of the maximal ideal of `𝒪_{X,x}` over `𝒪_{Y,f(x)}` along the stalk
map: the length of `𝒪_{X,x} ⧸ 𝔪_{f(x)} 𝒪_{X,x}` when it is finite, and `0` otherwise. -/
noncomputable def ramificationIdxAt (x : X) : ℕ :=
  letI := (f.stalkMap x).hom.toAlgebra
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x))

/-- The ramification index of `f` at `x` is the ramification index of the maximal ideal of
`𝒪_{X,x}` over `𝒪_{Y,f(x)}`, for the algebra structure given by the stalk map. -/
theorem ramificationIdxAt_def (x : X) :
    ramificationIdxAt f x =
      letI := (f.stalkMap x).hom.toAlgebra
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x)) :=
  (rfl)

/-- The ramification index of `f` is positive at every point where `f` is quasi-finite. -/
theorem ramificationIdxAt_pos {x : X} (hx : f.QuasiFiniteAt x) : 0 < ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [Scheme.Hom.QuasiFiniteAt] at hx
  have : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.quasiFinite_algebraMap.mp hx
  rw [ramificationIdxAt_def]
  exact Ideal.ramificationIdx_pos_of_quasiFiniteAt _

/-- Ramification indices multiply along a composite at any point where the first stalk map is
flat. No finiteness, normality, or codimension assumptions are required. -/
theorem ramificationIdxAt_comp_of_flat_stalkMap {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X)
    (hflat : (f.stalkMap x).hom.Flat) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  let sourceStalk := Z.presheaf.stalk (g (f x))
  let middleStalk := Y.presheaf.stalk (f x)
  let targetStalk := X.presheaf.stalk x
  let compositeStalkMap : sourceStalk ⟶ targetStalk :=
    eqToHom (congrArg Z.presheaf.stalk (Scheme.Hom.comp_apply f g x).symm) ≫
      (f ≫ g).stalkMap x
  let : Algebra sourceStalk middleStalk := (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra middleStalk targetStalk := (f.stalkMap x).hom.toAlgebra
  let : Algebra sourceStalk targetStalk := compositeStalkMap.hom.toAlgebra
  have htransport :
      eqToHom (congrArg Z.presheaf.stalk (Scheme.Hom.comp_apply f g x).symm) =
        𝟙 sourceStalk := by
    cases Scheme.Hom.comp_apply f g x
    rfl
  have hcomp : compositeStalkMap.hom =
      (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
    dsimp only [compositeStalkMap]
    erw [htransport, Category.id_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  have : IsScalarTower sourceStalk middleStalk targetStalk := .of_algebraMap_eq' hcomp
  have : IsLocalHom (algebraMap middleStalk targetStalk) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.Flat middleStalk targetStalk := RingHom.flat_algebraMap_iff.mp hflat
  rw [ramificationIdxAt_def, ramificationIdxAt_def, ramificationIdxAt_def, mul_comm]
  exact Ideal.ramificationIdx_tower (R := sourceStalk) (maximalIdeal middleStalk)
    (maximalIdeal targetStalk)

/-- Ramification indices multiply along any composite whose first morphism is flat. -/
@[simp]
theorem ramificationIdxAt_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Flat f] (x : X) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) :=
  f.ramificationIdxAt_comp_of_flat_stalkMap g x (Flat.stalkMap f x)

/-- The maximal-ideal power identity at a point with a DVR stalk, assuming that the mapped
maximal ideal is nonzero. -/
theorem map_maximalIdeal_eq_pow_ramificationIdxAt_of_map_ne_bot
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hmap : (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom ≠ ⊥) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  rw [ramificationIdxAt_def]
  exact TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap

/-- The pointwise ramification index equals the DVR exponent characterized by the maximal-ideal
identity in Stacks, Definition 15.113.1 (09E4).

Divergence from Stacks: only the source stalk needs to be a DVR. No dominance or assumption
on the target is required when the maximal-ideal power identity is supplied. -/
@[stacks 09E4 "comparison with the exponent in the maximal-ideal identity"]
theorem ramificationIdxAt_eq_of_map_maximalIdeal_eq_pow
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {exponent : ℕ}
    (hexponent : (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ exponent) :
    f.ramificationIdxAt x = exponent := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  rw [ramificationIdxAt_def]
  exact TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow hexponent

end AlgebraicGeometry.Scheme.Hom
