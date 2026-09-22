/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Circle
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange

/-!
# Higher homotopy groups of real projective space

The antipodal quotient `Sⁿ → RPⁿ` is a covering map, and a covering map induces isomorphisms on
homotopy groups in every dimension at least two. So in those dimensions the homotopy groups of
`RPⁿ` are exactly those of the sphere `Sⁿ`:

  `π_k(Sⁿ, y) ≃* π_k(RPⁿ, ⟦y⟧)`   for `k ≥ 2`.

Because `RPⁿ` is path connected, the isomorphism class of the right-hand side does not depend on
the base point, and for `1 ≤ n` neither does that of the left-hand side.

The projective line is settled outright: it is homeomorphic to the circle, whose higher homotopy
groups vanish, so every higher homotopy group of `RP¹` is trivial. In every dimension `n ≥ 2` the
answer is that of `Sⁿ`, whose computation is a separate matter, resting on a degree or Hurewicz
argument.

## Main declarations

* `TauCeti.RealProjectiveSpace.homotopyGroupMulEquiv`: **the antipodal covering induces
  `π_N(Sⁿ, y) ≃* π_N(RPⁿ, ⟦y⟧)`** for an index type with at least two elements, and
  `TauCeti.RealProjectiveSpace.homotopyGroupPiMulEquiv` is its `π_(k + 2)` form.
* `TauCeti.RealProjectiveSpace.nonempty_homotopyGroupMulEquiv_sphere`: for `1 ≤ n` the same
  isomorphism at an arbitrary base point of `RPⁿ` and an arbitrary base point of `Sⁿ`.
* `TauCeti.RealProjectiveSpace.Line.subsingleton_homotopyGroup`: **every higher homotopy group
  of `RP¹` is trivial**, with `TauCeti.RealProjectiveSpace.Line.homotopyGroup_eq_one` and
  `TauCeti.RealProjectiveSpace.Line.homotopyGroupPi_eq_one` the equality forms.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 4.1.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

open Metric
open scoped Topology Topology.Homotopy

noncomputable section

variable {N : Type*} [DecidableEq N] [Nontrivial N] (n : ℕ)

/-- **The antipodal covering identifies the higher homotopy groups of `Sⁿ` and of `RPⁿ`.**
Postcomposition with the quotient map `Sⁿ → RPⁿ` is an isomorphism `π_N(Sⁿ, y) ≃* π_N(RPⁿ, ⟦y⟧)`
whenever the index type `N` has at least two elements. -/
def homotopyGroupMulEquiv (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y ≃*
      HomotopyGroup N (RealProjectiveSpace n) (mk n y) :=
  (isCoveringMap_mk n).homotopyGroupMulEquiv y

@[simp]
theorem homotopyGroupMulEquiv_apply (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (a : HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y) :
    homotopyGroupMulEquiv n y a =
      HomotopyGroup.map (⟨mk n, continuous_mk n⟩ : C(_, RealProjectiveSpace n)) rfl a :=
  (isCoveringMap_mk n).homotopyGroupMulEquiv_apply y a

/-- The `π_(k + 2)` form of `TauCeti.RealProjectiveSpace.homotopyGroupMulEquiv`. -/
def homotopyGroupPiMulEquiv (k : ℕ) (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y ≃*
      π_ (k + 2) (RealProjectiveSpace n) (mk n y) :=
  homotopyGroupMulEquiv n y

@[simp]
theorem homotopyGroupPiMulEquiv_apply (k : ℕ)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (a : π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y) :
    homotopyGroupPiMulEquiv n k y a =
      HomotopyGroup.map (⟨mk n, continuous_mk n⟩ : C(_, RealProjectiveSpace n)) rfl a :=
  (isCoveringMap_mk n).homotopyGroupMulEquiv_apply y a

/-- **The higher homotopy groups of `RPⁿ` are those of `Sⁿ`, at any base points.** For `1 ≤ n`
both spaces are path connected, so the base points of the previous isomorphism may be chosen
independently. -/
theorem nonempty_homotopyGroupMulEquiv_sphere [Finite N] (hn : 1 ≤ n)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (x : RealProjectiveSpace n) :
    Nonempty (HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y ≃*
      HomotopyGroup N (RealProjectiveSpace n) x) := by
  obtain ⟨y', rfl⟩ := mk_surjective n x
  have := pathConnectedSpace_sphere n hn
  obtain ⟨φ⟩ := TauCeti.nonempty_homotopyGroupMulEquiv (N := N) (x := y) (y := y')
  exact ⟨φ.trans (homotopyGroupMulEquiv n y')⟩

end

namespace Line

variable {N : Type*} [Nontrivial N] (x : RealProjectiveSpace 1)

/-- **Every higher homotopy group of the real projective line is trivial.** It is transported
from the circle along `TauCeti.RealProjectiveSpace.Line.homeomorphCircle`. -/
instance subsingleton_homotopyGroup :
    Subsingleton (HomotopyGroup N (RealProjectiveSpace 1) x) :=
  (HomotopyGroup.homeomorphEquiv (N := N) homeomorphCircle x).subsingleton_congr.mpr
    inferInstance

/-- Every higher homotopy class of the real projective line is the identity. -/
theorem homotopyGroup_eq_one [DecidableEq N]
    (a : HomotopyGroup N (RealProjectiveSpace 1) x) : a = 1 :=
  Subsingleton.elim _ _

/-- Every element of `π_(k + 2)` of the real projective line is the identity. -/
theorem homotopyGroupPi_eq_one (k : ℕ) (a : π_ (k + 2) (RealProjectiveSpace 1) x) : a = 1 :=
  homotopyGroup_eq_one x a

end Line

end RealProjectiveSpace

end TauCeti
