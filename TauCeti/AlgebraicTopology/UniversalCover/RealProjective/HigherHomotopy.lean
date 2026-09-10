/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Circle
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Higher homotopy groups of real projective space

Real projective space `RPⁿ` is the antipodal quotient of the unit sphere `Sⁿ`, and that
quotient map is a covering map. Since a covering map induces an isomorphism on homotopy groups
in every dimension at least two, the higher homotopy of `RPⁿ` is exactly the higher homotopy
of `Sⁿ`.

This file records that identification, at a matched pair of basepoints and — using
path-connectedness of the sphere and of `RPⁿ` — at arbitrary basepoints, and draws the two
consequences that the identification settles outright:

* `RP⁰` is a point, so all of its homotopy groups are trivial;
* `RP¹` is homeomorphic to a circle, so all of its homotopy groups in dimensions at least two
  are trivial, and so are those of the circle `S¹ ⊆ ℝ²` covering it.

For `2 ≤ n` nothing further is claimed: the vanishing of `π_k(RPⁿ)` for `k ≥ 2` is equivalent
to the vanishing of `π_k(Sⁿ)`, and classically that fails at `k = n`, where `π_n(Sⁿ)` is
infinite cyclic. That computation is not available here — no homotopy group of `Sⁿ` in
dimension `n` is determined anywhere in this library — so neither side of the equivalence is
decided for `2 ≤ n`.

## Main declarations

* `TauCeti.RealProjectiveSpace.homotopyGroupMulEquivMk`: `π_N(Sⁿ, x) ≃* π_N(RPⁿ, ⟦x⟧)` for a
  nontrivial index type `N`, and `TauCeti.RealProjectiveSpace.homotopyGroupPiMulEquivMk` in
  the `π_(k + 2)` form.
* `TauCeti.RealProjectiveSpace.subsingleton_homotopyGroupPi_mk_iff`: a higher homotopy group of
  `RPⁿ` vanishes exactly when the corresponding one of `Sⁿ` does.
* `TauCeti.RealProjectiveSpace.nonempty_homotopyGroupPiMulEquiv`: the same isomorphism between
  arbitrary basepoints of `Sⁿ` and of `RPⁿ`, for `1 ≤ n`.
* `TauCeti.RealProjectiveSpace.isAspherical_iff_sphere`: `RPⁿ` is aspherical exactly when every
  homotopy group of `Sⁿ` in dimension at least two is trivial.
* `TauCeti.RealProjectiveSpace.Line.homeomorphAddCircle`: `RP¹ ≃ₜ ℝ ⧸ 2πℤ`.
* `TauCeti.RealProjectiveSpace.Line.subsingleton_homotopyGroup` and
  `TauCeti.RealProjectiveSpace.Line.subsingleton_homotopyGroup_sphere`: the higher homotopy
  groups of `RP¹` and of its covering circle `S¹ ⊆ ℝ²` vanish.
* `TauCeti.RealProjectiveSpace.Zero.subsingleton_homotopyGroup`: every homotopy group of `RP⁰`
  vanishes.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 4.1 and Example 4.2.
-/

public section

open Metric
open scoped Topology Topology.Homotopy Real

namespace TauCeti

namespace RealProjectiveSpace

section General

variable {N : Type*} [Nontrivial N] [DecidableEq N]

/-- **The higher homotopy groups of real projective space are those of the covering sphere.**
The antipodal projection `Sⁿ → RPⁿ` is a covering map, and postcomposition with a covering map
is an isomorphism on homotopy groups in every dimension at least two, which is what
nontriviality of the index type `N` expresses. -/
noncomputable def homotopyGroupMulEquivMk (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃*
      HomotopyGroup N (RealProjectiveSpace n) (mk n x) :=
  IsCoveringMap.homotopyGroupMulEquiv (isCoveringMap_mk n) x

/-- The isomorphism of `homotopyGroupMulEquivMk` is postcomposition with the antipodal
projection. -/
@[simp]
theorem homotopyGroupMulEquivMk_apply (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (a : HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) :
    homotopyGroupMulEquivMk n x a =
      HomotopyGroup.map (⟨mk n, (isCoveringMap_mk n).continuous⟩ :
        C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, RealProjectiveSpace n)) rfl a :=
  IsCoveringMap.homotopyGroupMulEquiv_apply (isCoveringMap_mk n) x a

end General

/-- The `π_(k + 2)` form of `TauCeti.RealProjectiveSpace.homotopyGroupMulEquivMk`. -/
noncomputable def homotopyGroupPiMulEquivMk (n k : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃*
      π_ (k + 2) (RealProjectiveSpace n) (mk n x) :=
  homotopyGroupMulEquivMk n x

/-- A higher homotopy group of `RPⁿ` is trivial exactly when the corresponding homotopy group
of the covering sphere is. -/
theorem subsingleton_homotopyGroupPi_mk_iff (n k : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Subsingleton (π_ (k + 2) (RealProjectiveSpace n) (mk n x)) ↔
      Subsingleton (π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) :=
  (_root_.IsCoveringMap.subsingleton_homotopyGroup_iff (isCoveringMap_mk n) rfl k).symm

/-- **The higher homotopy groups of `RPⁿ` and of `Sⁿ` agree at arbitrary basepoints**, for
`1 ≤ n`. Both spaces are path-connected in that range, so the matched-basepoint isomorphism
`TauCeti.RealProjectiveSpace.homotopyGroupPiMulEquivMk` can be moved to any pair of
basepoints; the isomorphism itself depends on the connecting path, so only its existence is
asserted. -/
theorem nonempty_homotopyGroupPiMulEquiv {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (y : RealProjectiveSpace n) :
    Nonempty (π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃*
      π_ (k + 2) (RealProjectiveSpace n) y) := by
  obtain ⟨x', rfl⟩ := mk_surjective n y
  have := pathConnectedSpace_sphere n hn
  obtain ⟨e⟩ := nonempty_homotopyGroupMulEquiv (N := Fin (k + 2)) (x := x) (y := x')
  exact ⟨e.trans (homotopyGroupPiMulEquivMk n k x')⟩

/-- **Real projective space is aspherical exactly when its covering sphere is weakly
contractible.** For `2 ≤ n` neither side is decided here: `π_n(Sⁿ)` is not computed in this
library, and it is the only obstruction. -/
theorem isAspherical_iff_sphere {n : ℕ} (hn : 1 ≤ n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (y : RealProjectiveSpace n) :
    IsAspherical (RealProjectiveSpace n) y ↔
      ∀ k : ℕ, Subsingleton (π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) := by
  constructor
  · intro h k
    obtain ⟨e⟩ := nonempty_homotopyGroupPiMulEquiv hn k x y
    exact e.toEquiv.subsingleton_congr.mpr (h.subsingleton_homotopyGroup k)
  · intro h
    refine IsAspherical.mk inferInstance fun k ↦ ?_
    obtain ⟨e⟩ := nonempty_homotopyGroupPiMulEquiv hn k x y
    exact e.toEquiv.subsingleton_congr.mp (h k)

namespace Line

variable {N : Type*} [Nontrivial N]

/-- **The real projective line is homeomorphic to the additive circle `ℝ ⧸ 2πℤ`**, obtained by
composing `TauCeti.RealProjectiveSpace.Line.homeomorphCircle` with Mathlib's identification of
`AddCircle (2 * π)` with the complex unit circle. -/
noncomputable def homeomorphAddCircle : RealProjectiveSpace 1 ≃ₜ AddCircle (2 * π) :=
  homeomorphCircle.trans (AddCircle.homeomorphCircle (T := 2 * π) Real.two_pi_pos.ne').symm

/-- **Every higher homotopy group of the real projective line is trivial.** -/
instance subsingleton_homotopyGroup (x : RealProjectiveSpace 1) :
    Subsingleton (HomotopyGroup N (RealProjectiveSpace 1) x) :=
  (HomotopyGroup.homeomorphEquiv (N := N) homeomorphAddCircle x).subsingleton_congr.mpr
    inferInstance

/-- Every higher homotopy class of the real projective line is the identity. -/
theorem homotopyGroup_eq_one [DecidableEq N] (x : RealProjectiveSpace 1)
    (a : HomotopyGroup N (RealProjectiveSpace 1) x) : a = 1 :=
  Subsingleton.elim _ _

/-- Every element of `π_(k + 2)(RP¹)` is the identity. -/
theorem homotopyGroupPi_eq_one (k : ℕ) (x : RealProjectiveSpace 1)
    (a : π_ (k + 2) (RealProjectiveSpace 1) x) : a = 1 :=
  homotopyGroup_eq_one x a

/-- **Every higher homotopy group of the unit circle `S¹ ⊆ ℝ²` is trivial.** This is the sphere
covering `RP¹`, so the statement transports along the covering isomorphism from the previous
one. -/
instance subsingleton_homotopyGroup_sphere
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) x) := by
  classical
  exact (homotopyGroupMulEquivMk 1 x).toEquiv.subsingleton_congr.mpr inferInstance

/-- Every element of `π_(k + 2)(S¹)` for the unit circle `S¹ ⊆ ℝ²` is the identity. -/
theorem homotopyGroupPi_sphere_eq_one (k : ℕ) (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (a : π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) x) : a = 1 :=
  Subsingleton.elim _ _

end Line

namespace Zero

variable {N : Type*}

/-- The generalized loops of a one-point space are all equal. -/
instance subsingleton_genLoop (x : RealProjectiveSpace 0) :
    Subsingleton (Ω^ N (RealProjectiveSpace 0) x) :=
  ⟨fun _ _ ↦ Subtype.ext (ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _)⟩

/-- **Every homotopy group of `RP⁰` is trivial**, in every dimension: `RP⁰` is a single
point. -/
instance subsingleton_homotopyGroup (x : RealProjectiveSpace 0) :
    Subsingleton (HomotopyGroup N (RealProjectiveSpace 0) x) :=
  ⟨fun a b ↦ Quotient.inductionOn₂ a b fun _ _ ↦
    congrArg (Quotient.mk _) (Subsingleton.elim _ _)⟩

/-- Every homotopy class of `RP⁰` in a positive dimension is the identity. -/
theorem homotopyGroup_eq_one [Nonempty N] [DecidableEq N] (x : RealProjectiveSpace 0)
    (a : HomotopyGroup N (RealProjectiveSpace 0) x) : a = 1 :=
  Subsingleton.elim _ _

/-- Every element of `π_(k + 1)(RP⁰)` is the identity. -/
theorem homotopyGroupPi_eq_one (k : ℕ) (x : RealProjectiveSpace 0)
    (a : π_ (k + 1) (RealProjectiveSpace 0) x) : a = 1 :=
  homotopyGroup_eq_one x a

end Zero

end RealProjectiveSpace

end TauCeti
