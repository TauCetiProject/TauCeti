/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange

/-!
# Higher homotopy groups of real projective space

The antipodal quotient `Sⁿ → RPⁿ` is a covering map, and a covering map induces isomorphisms on
homotopy groups in every dimension at least two. So in those dimensions the homotopy groups of
`RPⁿ` are exactly those of the sphere `Sⁿ`:

  `π_k(Sⁿ, y) ≃* π_k(RPⁿ, ⟦y⟧)`   for `k ≥ 2`.

Real projective space is path connected in every dimension, so the isomorphism class of the
right-hand side does not depend on the base point and the two base points may be chosen
independently.

The projective line is settled outright: it is covered by the circle `S¹`, whose higher homotopy
groups vanish, so every higher homotopy group of `RP¹` is trivial. In every dimension `n ≥ 2` the
answer is that of `Sⁿ`, which is a separate matter: a degree or Hurewicz argument gives
`π_k(Sⁿ) = 0` for `2 ≤ k < n` and `π_n(Sⁿ) ≅ ℤ`, while the groups `π_k(Sⁿ)` with `k > n` are not
reached by either argument and are not treated here.

## Main declarations

* `TauCeti.RealProjectiveSpace.sphereHomotopyGroupMulEquiv`: **the antipodal covering induces
  `π_N(Sⁿ, y) ≃* π_N(RPⁿ, ⟦y⟧)`** for an index type with at least two elements.
* `TauCeti.RealProjectiveSpace.nonempty_homotopyGroupMulEquiv_sphere`: the same isomorphism at
  an arbitrary base point of `RPⁿ` and an arbitrary base point of `Sⁿ`.
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
def sphereHomotopyGroupMulEquiv (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y ≃*
      HomotopyGroup N (RealProjectiveSpace n) (mk n y) :=
  (isCoveringMap_mk n).homotopyGroupMulEquiv y

@[simp]
theorem sphereHomotopyGroupMulEquiv_apply (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (a : HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y) :
    sphereHomotopyGroupMulEquiv n y a =
      HomotopyGroup.map (⟨mk n, continuous_mk n⟩ : C(_, RealProjectiveSpace n)) rfl a :=
  (isCoveringMap_mk n).homotopyGroupMulEquiv_apply y a

/-- **The higher homotopy groups of `RPⁿ` are those of `Sⁿ`, at any base points.** Real
projective space is path connected in every dimension, so the base point on the projective side
may be moved freely; no hypothesis on `n` is needed. -/
theorem nonempty_homotopyGroupMulEquiv_sphere [Finite N]
    (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (x : RealProjectiveSpace n) :
    Nonempty (HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y ≃*
      HomotopyGroup N (RealProjectiveSpace n) x) := by
  obtain ⟨φ⟩ := TauCeti.nonempty_homotopyGroupMulEquiv (N := N) (x := mk n y) (y := x)
  exact ⟨(sphereHomotopyGroupMulEquiv n y).trans φ⟩

end

namespace Line

variable {N : Type*} [Nontrivial N] (x : RealProjectiveSpace 1)

/-- **Every higher homotopy group of the real projective line is trivial.** The projective line
is covered by the unit circle of `EuclideanSpace ℝ (Fin 2)`, whose higher homotopy groups
vanish. -/
instance subsingleton_homotopyGroup :
    Subsingleton (HomotopyGroup N (RealProjectiveSpace 1) x) := by
  classical
  obtain ⟨y, rfl⟩ := mk_surjective 1 x
  exact (sphereHomotopyGroupMulEquiv 1 y).toEquiv.subsingleton_congr.mp
    (EuclideanSpace.subsingleton_homotopyGroup_sphere y)

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
