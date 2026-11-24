/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import TauCeti.AlgebraicTopology.Singular.Coefficients.ULift

/-!
# The Hurewicz theorem in degree one in an arbitrary universe

For a path-connected space `X : TopCat.{u}` with a base point `x`, the abelianized fundamental
group `π₁(X, x)ᵃᵇ` is the first singular homology group `H₁(X; ℤ)`, formed in `ModuleCat.{u} ℤ`
with the universe-lifted coefficient module `ModuleCat.of ℤ (ULift.{u} ℤ)`
(`TauCeti.HurewiczOne.hurewiczHomologyUliftAddEquiv`). This is the form of integral singular
homology used for spaces in an arbitrary universe, in which the Hurewicz theorem in higher degrees
is stated (`HomotopyGroup.hurewiczUliftAddEquiv`).

The isomorphism is the Hurewicz isomorphism `TauCeti.HurewiczOne.hurewiczHomologyAddEquiv` over
the coefficient ring `ULift.{u} ℤ`, read through the identification
`TopCat.singularHomologyUliftAddEquiv` of the homology over the ring `ULift.{u} ℤ` with the homology
with coefficients in the `ℤ`-module `ULift.{u} ℤ`. Like its counterpart for spaces in `Type`, it
sends the class of a loop to the homology class of the singular `1`-simplex the loop traces, it is
natural in continuous maps, and it does not depend on the base point.

## Main results

* `TauCeti.HurewiczOne.hurewiczHomologyUliftAddEquiv`: `π₁(X, x)ᵃᵇ ≃+ H₁(X; ℤ)` for a
  path-connected space in any universe.
* `TauCeti.HurewiczOne.hurewiczHomologyUliftAddEquiv_ofMul_of_mk`: the class of a loop goes to
  the class of its `1`-simplex.
* `TauCeti.HurewiczOne.hurewiczHomologyUliftAddEquiv_naturality`: naturality in continuous maps.
* `TauCeti.HurewiczOne.hurewiczHomologyUliftAddEquiv_fundamentalGroupMulEquivOfPath`:
  independence of the base point.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u

namespace TauCeti.HurewiczOne

variable {X Y : TopCat.{u}}

/-- **The Hurewicz theorem in degree one, in an arbitrary universe**: for a path-connected space
`X : TopCat.{u}` with a base point `x`, the Hurewicz map identifies the abelianization of
`π₁(X, x)` with `H₁(X; ℤ)`, the first singular homology group with coefficients in the `ℤ`-module
`ULift.{u} ℤ`. -/
def hurewiczHomologyUliftAddEquiv [PathConnectedSpace X] (x : X) :
    Additive (Group.Abelianization (FundamentalGroup X x)) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X :=
  (hurewiczHomologyAddEquiv x ULift.ringEquiv).trans
    (X.singularHomologyUliftAddEquiv.{u, 0} ℤ 1).symm

/-- `TauCeti.HurewiczOne.hurewiczHomologyUliftAddEquiv` is the Hurewicz isomorphism over the ring
`ULift.{u} ℤ`, followed by the inverse of `TopCat.singularHomologyUliftAddEquiv`. -/
theorem hurewiczHomologyUliftAddEquiv_apply [PathConnectedSpace X] {x : X}
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    hurewiczHomologyUliftAddEquiv x a =
      (X.singularHomologyUliftAddEquiv.{u, 0} ℤ 1).symm
        (hurewiczHomologyAddEquiv x ULift.ringEquiv a) :=
  (rfl)

/-- The Hurewicz isomorphism sends the class of a loop `γ` to the homology class of the singular
`1`-simplex it traces. -/
@[simp]
theorem hurewiczHomologyUliftAddEquiv_ofMul_of_mk [PathConnectedSpace X] {x : X}
    (γ : Path x x) :
    hurewiczHomologyUliftAddEquiv x (Additive.ofMul
      ((Group.Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) =
        (X.singularHomologyUliftAddEquiv.{u, 0} ℤ 1).symm
          (H₁AddEquivHomology (ULift.{u} ℤ) X (loopClass (ULift.{u} ℤ) γ)) := by
  rw [hurewiczHomologyUliftAddEquiv_apply, hurewiczHomologyAddEquiv_ofMul_of_mk]

/-- **Naturality of the Hurewicz isomorphism** in an arbitrary universe: for a continuous map `f`
of path-connected spaces, the map induced on first singular homology corresponds to the map
induced on fundamental groups. -/
theorem hurewiczHomologyUliftAddEquiv_naturality [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) {x : X} (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).map f).hom
        (hurewiczHomologyUliftAddEquiv x a) =
      hurewiczHomologyUliftAddEquiv (f x) (Additive.ofMul (Group.Abelianization.map
        (FundamentalGroup.map f.hom x) a.toMul)) := by
  rw [hurewiczHomologyUliftAddEquiv_apply, hurewiczHomologyUliftAddEquiv_apply,
    ← TopCat.singularHomologyUliftAddEquiv_symm_naturality.{u, 0} ℤ f 1,
    homologyMap_hurewiczHomologyAddEquiv f ULift.ringEquiv a]

/-- **Independence of the base point**: changing the base point along a path does not change the
singular homology class supplied by the Hurewicz isomorphism in an arbitrary universe. -/
theorem hurewiczHomologyUliftAddEquiv_fundamentalGroupMulEquivOfPath [PathConnectedSpace X]
    {x x' : X} (p : Path x x') (a : FundamentalGroup X x) :
    hurewiczHomologyUliftAddEquiv x' (Additive.ofMul (Group.Abelianization.of
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p a))) =
      hurewiczHomologyUliftAddEquiv x (Additive.ofMul (Group.Abelianization.of a)) := by
  rw [hurewiczHomologyUliftAddEquiv_apply, hurewiczHomologyUliftAddEquiv_apply,
    hurewiczHomologyAddEquiv_fundamentalGroupMulEquivOfPath p ULift.ringEquiv a]

end TauCeti.HurewiczOne
