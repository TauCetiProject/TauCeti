/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.Submonoid.Closure
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.GroupTheory.Finiteness

/-!
# Strict dual chambers of additive monoids

For an additive monoid `P` mapped into a real normed space by `i`, the positive chamber consists
of the continuous real functionals that are strictly positive on the image of every nonzero
element of `P`; the negative chamber is defined by strict negativity. Both are convex. For a
finitely generated monoid, positivity can be tested on its nonzero generators, so both chambers
are open. Neither the construction nor openness requires finite dimension, injectivity of the
monoid map, or a saturated monoid.

The finite test is `AddSubmonoid.forall_pos_iff_of_closure_eq`; the topological and convexity
arguments use Mathlib's continuous evaluation map and convex half-spaces.

## Main results

* `AddSubmonoid.positiveChamber`, `AddSubmonoid.negativeChamber`: the strict dual chambers.
* `AddSubmonoid.convex_positiveChamber`, `AddSubmonoid.convex_negativeChamber`: convexity.
* `AddSubmonoid.isOpen_positiveChamber`, `AddSubmonoid.isOpen_negativeChamber`: openness for
  finitely generated monoids.

## Provenance

Adapted from `Mei/Geometry/Convex/Cone/Chamber.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open Set

namespace AddSubmonoid

variable {M V : Type*} [AddCommMonoid M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (P : AddSubmonoid M) (i : M →+ V)

/-- The continuous real functionals that are strictly positive on the image of every nonzero
element of the monoid `P`. -/
def positiveChamber : Set (V →L[ℝ] ℝ) :=
  {θ | ∀ n ∈ P, n ≠ 0 → 0 < θ (i n)}

/-- The continuous real functionals that are strictly negative on the image of every nonzero
element of the monoid `P`. -/
def negativeChamber : Set (V →L[ℝ] ℝ) :=
  {θ | ∀ n ∈ P, n ≠ 0 → θ (i n) < 0}

/-- Membership in the positive chamber is strict positivity on the nonzero monoid. -/
@[simp]
theorem mem_positiveChamber {θ : V →L[ℝ] ℝ} :
    θ ∈ P.positiveChamber i ↔ ∀ n ∈ P, n ≠ 0 → 0 < θ (i n) := Iff.rfl

/-- Membership in the negative chamber is strict negativity on the nonzero monoid. -/
@[simp]
theorem mem_negativeChamber {θ : V →L[ℝ] ℝ} :
    θ ∈ P.negativeChamber i ↔ ∀ n ∈ P, n ≠ 0 → θ (i n) < 0 := Iff.rfl

/-- The negative chamber is the inverse image of the positive chamber under negation. -/
theorem negativeChamber_eq_preimage_neg :
    P.negativeChamber i = Neg.neg ⁻¹' P.positiveChamber i := by
  ext θ
  simp

/-- On a generated monoid, positive chamber membership is a test on the nonzero generators. -/
theorem mem_positiveChamber_iff_of_closure_eq {s : Set M} (hs : closure s = P)
    {θ : V →L[ℝ] ℝ} :
    θ ∈ P.positiveChamber i ↔ ∀ n ∈ s, n ≠ 0 → 0 < θ (i n) :=
  forall_pos_iff_of_closure_eq hs (θ.toLinearMap.toAddMonoidHom.comp i)

/-- On a generated monoid, negative chamber membership is a test on the nonzero generators. -/
theorem mem_negativeChamber_iff_of_closure_eq {s : Set M} (hs : closure s = P)
    {θ : V →L[ℝ] ℝ} :
    θ ∈ P.negativeChamber i ↔ ∀ n ∈ s, n ≠ 0 → θ (i n) < 0 := by
  rw [negativeChamber_eq_preimage_neg, mem_preimage, P.mem_positiveChamber_iff_of_closure_eq i hs]
  simp

/-- The positive chamber is convex, without finite generation. -/
theorem convex_positiveChamber : Convex ℝ (P.positiveChamber i) := by
  have heq : P.positiveChamber i =
      ⋂ n : {n : M // n ∈ P ∧ n ≠ 0}, {θ : V →L[ℝ] ℝ | 0 < θ (i n)} := by
    ext θ
    simp
  rw [heq]
  exact convex_iInter fun n => convex_halfSpace_gt
    (ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap.isLinear 0

/-- The negative chamber is convex, without finite generation. -/
theorem convex_negativeChamber : Convex ℝ (P.negativeChamber i) := by
  rw [negativeChamber_eq_preimage_neg]
  exact (P.convex_positiveChamber i).linear_preimage (-(LinearMap.id :
    (V →L[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)))

/-- Finite generation makes the positive chamber open in the normed dual. -/
theorem isOpen_positiveChamber (hP : P.FG) : IsOpen (P.positiveChamber i) := by
  classical
  obtain ⟨s, hs⟩ := AddSubmonoid.isAddFG_iff.mp hP
  have heq : P.positiveChamber i =
      ⋂ n : s.erase 0, {θ : V →L[ℝ] ℝ | 0 < θ (i n)} := by
    ext θ
    rw [P.mem_positiveChamber_iff_of_closure_eq i hs]
    simp only [mem_iInter, Subtype.forall, Finset.mem_coe, Finset.mem_erase]
    grind
  rw [heq]
  exact isOpen_iInter_of_finite fun n =>
    isOpen_lt continuous_const (ContinuousLinearMap.apply ℝ ℝ (i n)).continuous

/-- Finite generation makes the negative chamber open in the normed dual. -/
theorem isOpen_negativeChamber (hP : P.FG) : IsOpen (P.negativeChamber i) := by
  rw [negativeChamber_eq_preimage_neg]
  exact (P.isOpen_positiveChamber i hP).preimage continuous_neg

end AddSubmonoid
