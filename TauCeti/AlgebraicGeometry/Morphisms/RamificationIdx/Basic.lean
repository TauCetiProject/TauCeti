/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.RingTheory.RamificationInertia.QuasiFinite

/-!
# The ramification index of a morphism at a point

The ramification index `ramificationIdxAt f x` of a morphism of schemes `f : X ⟶ Y` at a point
`x` is Mathlib's ramification index `Ideal.ramificationIdx` of the maximal ideal of the local ring
`𝒪_{X,x}` over `𝒪_{Y,f(x)}` along the stalk map, that is, the length of
`𝒪_{X,x} ⧸ 𝔪_{f(x)} 𝒪_{X,x}` when this length is finite, and `0` when it is infinite. When the stalk
map is a finite injective local homomorphism of discrete valuation rings, this is the usual
ramification index of that extension (Stacks, Definition 15.113.1 (09E4)); that comparison is not
proved in this file.

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
flat. No finiteness, normality, or codimension assumptions are required.

The tower uses the definitional equality `(f ≫ g) x = g (f x)` to identify the two descriptions
of the source stalk of the composite stalk map. -/
theorem ramificationIdxAt_comp_of_flat_stalkMap {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X)
    (hflat : (f.stalkMap x).hom.Flat) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  let sourceStalk := Z.presheaf.stalk (g (f x))
  let middleStalk := Y.presheaf.stalk (f x)
  let targetStalk := X.presheaf.stalk x
  let : Algebra sourceStalk middleStalk := (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra middleStalk targetStalk := (f.stalkMap x).hom.toAlgebra
  let : Algebra sourceStalk targetStalk := ((f ≫ g).stalkMap x).hom.toAlgebra
  have hcomp : ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    exact CommRingCat.hom_comp _ _
  have : IsScalarTower sourceStalk middleStalk targetStalk := .of_algebraMap_eq' hcomp
  have : IsLocalHom (algebraMap middleStalk targetStalk) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.Flat middleStalk targetStalk := RingHom.flat_algebraMap_iff.mp hflat
  rw [ramificationIdxAt_def, ramificationIdxAt_def, ramificationIdxAt_def, mul_comm]
  exact Ideal.ramificationIdx_tower (R := sourceStalk) (maximalIdeal middleStalk)
    (maximalIdeal targetStalk)

/-- Ramification indices multiply along any composite whose first morphism is flat. -/
theorem ramificationIdxAt_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Flat f] (x : X) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) :=
  f.ramificationIdxAt_comp_of_flat_stalkMap g x (Flat.stalkMap f x)

end AlgebraicGeometry.Scheme.Hom
