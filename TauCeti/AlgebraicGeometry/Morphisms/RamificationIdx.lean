/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.RingTheory.RamificationInertia.QuasiFinite

/-!
# The ramification index of a morphism at a point

The ramification index `ramificationIdxAt f x` of a morphism of schemes `f : X ⟶ Y` at a point
`x` is Mathlib's ramification index `Ideal.ramificationIdx` of the maximal ideal of the local ring
`𝒪_{X,x}` over `𝒪_{Y,f(x)}` along the stalk map, that is, the length of
`𝒪_{X,x} ⧸ 𝔪_{f(x)} 𝒪_{X,x}` when this length is finite, and `0` when it is infinite. At a point
of codimension one of a locally Noetherian normal scheme over such a point, both local rings are
discrete valuation rings, and this length is the ramification index of that extension (Stacks,
Definition 15.113.1 (09E4)); that comparison is not made in this file.

It is finite and positive at every point where `f` is quasi-finite, since the stalk map is then
quasi-finite and `Ideal.ramificationIdx_pos_of_quasiFiniteAt` applies.

## Main definitions

* `Scheme.Hom.ramificationIdxAt`: the ramification index of a morphism at a point.

## Main results

* `Scheme.Hom.ramificationIdxAt_def`: the defining equation.
* `Scheme.Hom.ramificationIdxAt_pos`: the ramification index is positive at every
  point where the morphism is quasi-finite.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Bounding/SchemeDynamics.lean`: `ramificationIdxAt` is its
  `Pcf.schemeDivisorRamificationIdx` (there restricted to codimension-one points), and
  `ramificationIdxAt_pos` generalizes its `Pcf.schemeDivisorRamificationIdx_pos` (there for a
  locally quasi-finite morphism).
-/

public section

open AlgebraicGeometry

namespace Scheme.Hom

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

end Scheme.Hom
