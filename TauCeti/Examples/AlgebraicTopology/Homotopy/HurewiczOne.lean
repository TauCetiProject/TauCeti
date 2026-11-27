/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.WedgeCircles
public import TauCeti.CategoryTheory.Limits.Shapes.Products
public import TauCeti.Topology.Connected.Sigma

/-!
# Checks of the Hurewicz isomorphism in degree one

The degree-one Hurewicz isomorphism `TauCeti.HurewiczOne.hurewiczHomologyAddEquiv` identifies the
abelianized fundamental group `π₁(X, x)ᵃᵇ` of a path-connected space with `H₁(X; ℤ)`, a loop going
to the class of the singular `1`-simplex it traces. This file checks it on two spaces.

* **The wedge of two circles.** `π₁(S¹ ∨ S¹)` is the free group on the loops `a`, `b` around the
  two circles (`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`), and `H₁(S¹ ∨ S¹; ℤ) ≅ ℤ²`, the
  loops `a` and `b` going to the two basis vectors (`TauCeti.WedgeSum.circleFirstHomologyEquiv`).
  The commutator `aba⁻¹b⁻¹` is nullhomologous, as every commutator is, since `H₁` is abelian; but
  it is not nullhomotopic, since `⁅a, b⁆ ≠ 1` in the free group. So the Hurewicz map is not
  injective on `π₁` itself, only on its abelianization.
* **A circle and a point.** For the disjoint union `X = S¹ ⊔ pt` with the base point the isolated
  point, `π₁(X, pt)` is trivial, since every loop at the point stays in the clopen summand of the
  point, while `H₁(X; ℤ) ≅ H₁(S¹; ℤ) ≅ ℤ` by additivity of singular homology. So the Hurewicz map
  at `pt` is not surjective: the degree-one Hurewicz theorem needs the space to be path-connected.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1 (the Hurewicz theorem in degree one) and
  Example 1.21 (the fundamental group of a wedge of circles).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TauCeti.HurewiczOne TauCeti.WedgeSum
open scoped commutatorElement

namespace TauCeti.Examples.HurewiczOne

/-! ### The wedge of two circles -/

/-- The wedge of two circles `S¹ ∨ S¹`, as a topological space in the smallest universe. -/
abbrev wedgeTwoCircles : TopCat.{0} :=
  TopCat.of (WedgeSum fun _ : Fin 2 ↦ (1 : Circle))

/-- The loop going once counterclockwise around the `i`-th circle of `S¹ ∨ S¹`, as an element of
its fundamental group: `a` for `i = 0` and `b` for `i = 1`. -/
def wedgeLoop (i : Fin 2) : FundamentalGroup wedgeTwoCircles (base _) :=
  FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))

/-- `π₁(S¹ ∨ S¹)` is the free group on the loops `a` and `b`. -/
example (i : Fin 2) : circleFundamentalGroupMulEquiv (Fin 2) (wedgeLoop i) = FreeGroup.of i :=
  circleFundamentalGroupMulEquiv_expLoop i

/-- `H₁(S¹ ∨ S¹; ℤ) ≅ ℤ²`, the classes of the loops `a` and `b` being the two basis vectors. -/
example (i : Fin 2) :
    circleFirstHomologyEquiv (Fin 2)
      (hurewiczHomologyAddEquiv (base _) (.refl ℤ)
        (Additive.ofMul (Group.Abelianization.of (wedgeLoop i)))) = Finsupp.single i 1 :=
  circleFirstHomologyEquiv_hurewiczHomologyAddEquiv_expLoop i

/-- The commutator `aba⁻¹b⁻¹` is not nullhomotopic: it is a nontrivial element of the free group
on `a` and `b`. -/
example : ⁅wedgeLoop 0, wedgeLoop 1⁆ ≠ 1 := by
  rw [Ne, ← (circleFundamentalGroupMulEquiv (Fin 2)).injective.eq_iff, map_commutatorElement,
    wedgeLoop, wedgeLoop, circleFundamentalGroupMulEquiv_expLoop,
    circleFundamentalGroupMulEquiv_expLoop, map_one]
  decide

/-- The commutator `aba⁻¹b⁻¹` is nullhomologous: the Hurewicz map takes values in the abelian group
`H₁(S¹ ∨ S¹; ℤ)`, so it kills commutators. -/
example : hurewicz₁ ℤ wedgeTwoCircles (base _) ⁅wedgeLoop 0, wedgeLoop 1⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact Commute.all _ _

/-! ### A circle and a point -/

/-- The family of the circle and a point, indexed by `Bool`: its disjoint union `Σ b, X b` is
`S¹ ⊔ pt`, with the circle at `true` and the point at `false`. -/
def circleOrPoint : Bool → TopCat.{0} :=
  fun b ↦ cond b (TopCat.of Circle) (TopCat.of PUnit)

/-- The disjoint union `S¹ ⊔ pt` of the circle and a point. -/
abbrev circleSumPoint : TopCat.{0} :=
  TopCat.of (Σ b, circleOrPoint b)

/-- The isolated point of `S¹ ⊔ pt`. -/
abbrev isolatedPoint : circleSumPoint :=
  ⟨false, PUnit.unit⟩

/-- The fundamental group of `S¹ ⊔ pt` at the isolated point is trivial: a loop there has connected
image, so it stays in the clopen summand of the point. -/
theorem subsingleton_fundamentalGroup_isolatedPoint :
    Subsingleton (FundamentalGroup circleSumPoint isolatedPoint) := by
  refine subsingleton_fundamentalGroup_iff.2 fun γ ↦ ?_
  -- Every point of the loop lies in the summand of the point, which has a single element.
  have hγ : γ = Path.refl _ := Path.ext <| funext fun t ↦ by
    have h : (γ t).1 = false := (γ.continuous.fst_apply_eq_fst_apply t 0).trans (by simp)
    generalize γ t = p at h ⊢
    obtain ⟨b, y⟩ := p
    obtain rfl : b = false := h
    exact congrArg _ (Subsingleton.elim (α := PUnit) y PUnit.unit)
  rw [hγ]

/-- `H₁(S¹ ⊔ pt; ℤ) ≅ ℤ`: by additivity, `H₁(S¹ ⊔ pt; ℤ)` is `H₁(S¹; ℤ) ⊕ H₁(pt; ℤ)`, and the
second summand vanishes, so the inclusion of the circle induces an isomorphism. -/
def circleSumPointHomologyOneIso :
    ((singularChains ℤ).obj circleSumPoint).homology 1 ≅ ModuleCat.of ℤ ℤ :=
  have hc := isColimitCofanSingularHomology circleOrPoint (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) 1
  have : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.sigmaι circleOrPoint true)) :=
    Cofan.IsColimit.isIso_inj_of_isInitial hc true fun j hj ↦ by
      obtain rfl : j = false := by simpa using hj
      exact (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℤ ℤ)
        (TopCat.of PUnit) one_ne_zero).isInitial
  (asIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.sigmaι circleOrPoint true))).symm ≪≫
    Circle.singularHomologyOneIso (ModuleCat.of ℤ ℤ)

/-- **Path-connectedness is needed for the Hurewicz theorem in degree one.** On `S¹ ⊔ pt`, the
Hurewicz map from the abelianized fundamental group at the isolated point to `H₁(S¹ ⊔ pt; ℤ) ≅ ℤ`
is not surjective, since its domain is trivial. -/
example : ¬ Function.Surjective (hurewiczAb ℤ (X := circleSumPoint) isolatedPoint) := by
  intro hsurj
  have := subsingleton_fundamentalGroup_isolatedPoint
  have : Subsingleton (Group.Abelianization (FundamentalGroup circleSumPoint isolatedPoint)) :=
    (Group.Abelianization.surjective_of _).subsingleton
  have : Subsingleton (H₁ ℤ circleSumPoint) := hsurj.subsingleton
  have : Subsingleton (((singularChains ℤ).obj circleSumPoint).homology 1) :=
    (H₁AddEquivHomology ℤ circleSumPoint).symm.injective.subsingleton
  have : Subsingleton ℤ := circleSumPointHomologyOneIso.toLinearEquiv.symm.injective.subsingleton
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

end TauCeti.Examples.HurewiczOne
