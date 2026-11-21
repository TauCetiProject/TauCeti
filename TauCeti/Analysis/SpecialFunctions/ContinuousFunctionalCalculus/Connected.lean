/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
public import TauCeti.Topology.Algebra.Star.Unitary
import Mathlib.Algebra.Order.Star.Real
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Topology.Algebra.IsOpenUnits

/-!
# Polar paths and path-connectedness of groups of units via the continuous functional calculus

In an algebra `A` with a real continuous functional calculus and compatible star order, the set
`{p : A | IsStrictlyPositive p}` of strictly positive elements is convex
(`IsStrictlyPositive.convex_setOf`) and contains `1`: for any strictly positive `p` and
`t ∈ [0, 1]`, the affine interpolation `(1 - t) • 1 + t • p` remains strictly positive
(`IsStrictlyPositive.one_sub_smul_add_smul`).

When `A` is a complete normed `ℝ`-algebra, `Units.val : Aˣ → A` is an open embedding onto
`{a : A | IsUnit a}`, so this straight line lifts to an explicit path
`IsStrictlyPositive.linePathToOne` from `1` to `p.isUnit.unit` in `Aˣ`. Combining the right polar
decomposition `a = a.polarUnitary * √(a⋆ a)` (`Units.polarUnitary_mul_sqrt_star_mul`) with any path
`γ` from `1` to `a.polarUnitary` in `unitary A` yields the explicit polar-linear path

`t ↦ (γ t : A) * ((1 - t) • 1 + t • √(a⋆ a))`

from `1` to `a` inside `Aˣ` (`Units.polarPathToOne`). Consequently, whenever `unitary A` is
path-connected, `Aˣ` and `{a : A | IsUnit a}` are path-connected as well
(`Units.pathConnectedSpace_of_unitary`, `Units.isPathConnected_isUnit_of_unitary`), without needing
an isometric functional calculus or operator logarithms.

When the real continuous functional calculus is isometric (for example in any unital C⋆-algebra),
`Units.polarUnitary : Aˣ → unitary A` is a continuous retraction (`Units.continuous_polarUnitary`),
so `Aˣ` is path-connected if and only if `unitary A` is (`Units.pathConnectedSpace_iff_unitary`).

## Main declarations

* `IsStrictlyPositive.isPathConnected_setOf`: `{p : A | IsStrictlyPositive p}` is path-connected.
* `IsStrictlyPositive.linePathToOne`: the straight-line path `t ↦ (1 - t) • 1 + t • p` from `1` to
  `hp.isUnit.unit` in `Aˣ`.
* `Units.polarPathToOne`: the polar-linear path from `1` to `a : Aˣ` induced by a path from `1` to
  `a.polarUnitary` in `unitary A`.
* `Units.pathConnectedSpace_of_unitary`, `Units.isPathConnected_isUnit_of_unitary`:
  path-connectedness of `unitary A` implies path-connectedness of `Aˣ` and `{a : A | IsUnit a}`.
* `Units.joined_one_iff_joined_polarUnitary`, `Units.pathConnectedSpace_iff_unitary`: equivalence
  under an isometric real continuous functional calculus.

## References

* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, 2nd ed., Springer (1998),
  Proposition 4.29 and Corollary 4.30.
* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6, American Mathematical
  Society (1996), §I.5.
-/

public section

noncomputable section

open Set
open scoped unitInterval

section Convex

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

/-- The set of strictly positive elements in `A` is path-connected. -/
theorem IsStrictlyPositive.isPathConnected_setOf [ContinuousSMul ℝ A] :
    IsPathConnected {p : A | IsStrictlyPositive p} :=
  IsStrictlyPositive.convex_setOf.isPathConnected ⟨1, isStrictlyPositive_one⟩

end Convex

section PolarPath

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- The straight-line path `t ↦ (1 - t) • 1 + t • p` in `Aˣ` from `1` to `hp.isUnit.unit` for a
strictly positive element `p : A`. -/
def IsStrictlyPositive.linePathToOne {p : A} (hp : IsStrictlyPositive p) :
    Path (1 : Aˣ) hp.isUnit.unit where
  toFun t := (hp.one_sub_smul_add_smul t.property).isUnit.unit
  continuous_toFun := by
    rw [(Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff]
    have hEq :
        ((Units.val : Aˣ → A) ∘ fun t : I ↦ (hp.one_sub_smul_add_smul t.property).isUnit.unit) =
        fun t : I ↦ (1 - (t : ℝ)) • (1 : A) + (t : ℝ) • p := by
      ext t
      exact IsUnit.unit_spec _
    rw [hEq]
    fun_prop
  source' := Units.ext <| by simp
  target' := Units.ext <| by simp

/-- Coercing `hp.linePathToOne t` to `A` gives the affine combination `(1 - t) • 1 + t • p`. -/
@[simp]
theorem IsStrictlyPositive.val_linePathToOne_apply {p : A} (hp : IsStrictlyPositive p) (t : I) :
    (hp.linePathToOne t : A) = (1 - (t : ℝ)) • (1 : A) + (t : ℝ) • p :=
  IsUnit.unit_spec _

/-- Every point along `hp.linePathToOne` is strictly positive in `A`. -/
theorem IsStrictlyPositive.isStrictlyPositive_linePathToOne_apply {p : A}
    (hp : IsStrictlyPositive p) (t : I) :
    IsStrictlyPositive (hp.linePathToOne t : A) := by
  rw [hp.val_linePathToOne_apply]
  exact hp.one_sub_smul_add_smul t.property

section ContinuousStar

variable [ContinuousStar A]

namespace Units

/-- Given a unit `a : Aˣ` and a path `γ : Path 1 a.polarUnitary` in `unitary A`, the polar-linear
path `t ↦ γ t * ((1 - t) • 1 + t • √(a⋆ a))` joins `1` to `a` inside `Aˣ`. -/
def polarPathToOne (a : Aˣ) (γ : Path 1 a.polarUnitary) : Path 1 a :=
  ((γ.map Unitary.continuous_toUnits).mul a.isStrictlyPositive_sqrt_star_mul.linePathToOne).cast
    (by simp) <| Units.ext <| by simp [polarUnitary_mul_sqrt_star_mul]

/-- Evaluating `a.polarPathToOne γ` at `t` gives `(γ t : A) * ((1 - t) • 1 + t • √(a⋆ a))`. -/
@[simp]
theorem val_polarPathToOne_apply (a : Aˣ) (γ : Path 1 a.polarUnitary) (t : I) :
    (a.polarPathToOne γ t : A) =
      (γ t : A) * ((1 - (t : ℝ)) • (1 : A) + (t : ℝ) • CFC.sqrt (star (a : A) * a)) := by
  simp [polarPathToOne]

/-- A unit `a : Aˣ` is joined to `1` in `Aˣ` whenever its polar unitary `a.polarUnitary` is joined
to `1` in `unitary A`. -/
theorem joined_one_of_joined_polarUnitary {a : Aˣ} (h : Joined 1 a.polarUnitary) :
    Joined 1 a :=
  let ⟨γ⟩ := h
  ⟨a.polarPathToOne γ⟩

/-- Whenever `unitary A` is path-connected, the group of units `Aˣ` is path-connected. -/
theorem pathConnectedSpace_of_unitary [PathConnectedSpace (unitary A)] :
    PathConnectedSpace Aˣ where
  nonempty := ⟨1⟩
  joined a b :=
    (joined_one_of_joined_polarUnitary (PathConnectedSpace.joined 1 a.polarUnitary)).symm.trans
      (joined_one_of_joined_polarUnitary (PathConnectedSpace.joined 1 b.polarUnitary))

/-- Whenever `unitary A` is path-connected, the set `{a : A | IsUnit a}` of invertible elements in
`A` is path-connected. -/
theorem isPathConnected_isUnit_of_unitary [PathConnectedSpace (unitary A)] :
    IsPathConnected {a : A | IsUnit a} :=
  have := pathConnectedSpace_of_unitary (A := A)
  (Units.isOpenEmbedding_val (R := A)).isEmbedding.isPathConnected_isUnit_iff.2 this

end Units

end ContinuousStar

end PolarPath

section Isometric

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [ContinuousStar A]

namespace Units

/-- Under an isometric real continuous functional calculus, a unit `a : Aˣ` lies in the path
component of `1` in `Aˣ` if and only if `a.polarUnitary` lies in the path component of `1` in
`unitary A`. -/
theorem joined_one_iff_joined_polarUnitary {a : Aˣ} :
    Joined 1 a ↔ Joined 1 a.polarUnitary := by
  refine ⟨fun ⟨γ⟩ ↦ ?_, joined_one_of_joined_polarUnitary⟩
  exact ⟨(γ.map continuous_polarUnitary).cast polarUnitary_one.symm rfl⟩

/-- Under an isometric real continuous functional calculus, the group of units `Aˣ` is
path-connected if and only if the unitary group `unitary A` is path-connected. -/
theorem pathConnectedSpace_iff_unitary :
    PathConnectedSpace Aˣ ↔ PathConnectedSpace (unitary A) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ pathConnectedSpace_of_unitary⟩
  have hsurj : Function.Surjective (polarUnitary : Aˣ → unitary A) :=
    fun u ↦ ⟨Unitary.toUnits u, polarUnitary_toUnits u⟩
  exact hsurj.pathConnectedSpace continuous_polarUnitary

end Units

end Isometric
