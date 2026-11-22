/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Path-connectedness and affine paths in the strictly positive cone

In an algebra `A` with a real continuous functional calculus and compatible star order, the set
`{p : A | IsStrictlyPositive p}` of strictly positive elements is convex
(`TauCeti.convex_setOf_isStrictlyPositive`) and contains `1`, hence is path-connected
(`TauCeti.isPathConnected_setOf_isStrictlyPositive`).

When `A` is a complete normed `ℝ`-algebra, `Units.val : Aˣ → A` is an open embedding onto
`{a : A | IsUnit a}`, so the affine interpolation `(1 - t) • 1 + t • p` lifts to an explicit path
`IsStrictlyPositive.linePathToOne` from `1` to `p.isUnit.unit` inside `Aˣ`.

## Main declarations

* `TauCeti.isPathConnected_setOf_isStrictlyPositive`: `{p : A | IsStrictlyPositive p}` is
  path-connected.
* `IsStrictlyPositive.linePathToOne`: the straight-line path `t ↦ (1 - t) • 1 + t • p` from `1` to
  `hp.isUnit.unit` in `Aˣ`.
* `IsStrictlyPositive.val_linePathToOne_apply`,
  `IsStrictlyPositive.isStrictlyPositive_linePathToOne_apply`: evaluation and strict positivity
  along `IsStrictlyPositive.linePathToOne`.

## References

* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, 2nd ed., Springer (1998),
  Proposition 4.29 and Corollary 4.30.
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
theorem TauCeti.isPathConnected_setOf_isStrictlyPositive [ContinuousSMul ℝ A] :
    IsPathConnected {p : A | IsStrictlyPositive p} :=
  TauCeti.convex_setOf_isStrictlyPositive.isPathConnected ⟨1, isStrictlyPositive_one⟩

end Convex

section LinePath

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

end LinePath
