/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# The first homology of a wedge of circles

For a type `ι`, the first singular homology group with integer coefficients of the wedge of
circles `⋁_ι S¹` is the free abelian group `ι →₀ ℤ` on the circles
(`TauCeti.WedgeSum.circleFirstHomologyEquiv`). The isomorphism is the composite of the degree-one
Hurewicz isomorphism `H₁(⋁_ι S¹; ℤ) ≅ π₁(⋁_ι S¹)ᵃᵇ`
(`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`) with the computation of the fundamental group of a
wedge of circles as the free group on `ι` (`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`): the
abelianization of a free group is the free abelian group on the same generators. The Hurewicz class
of the loop going once counterclockwise around the `i`-th circle corresponds to the basis vector
`Finsupp.single i 1` (`TauCeti.WedgeSum.circleFirstHomologyEquiv_hurewiczHomologyAddEquiv_expLoop`).

## Main definitions and results

* `TauCeti.WedgeSum.circleFirstHomologyEquiv`: the isomorphism `H₁(⋁_ι S¹; ℤ) ≃ₗ[ℤ] (ι →₀ ℤ)`.
* `TauCeti.WedgeSum.circleFirstHomologyEquiv_hurewiczHomologyAddEquiv_expLoop`,
  `TauCeti.WedgeSum.circleFirstHomologyEquiv_symm_single_one`: the loop around the `i`-th circle
  corresponds to `Finsupp.single i 1`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1 for the Hurewicz isomorphism in degree one, and
  Example 1.21 for the fundamental group of a wedge of circles.
-/

public section

noncomputable section

open CategoryTheory TauCeti.HurewiczOne

namespace TauCeti

namespace WedgeSum

variable (ι : Type)

/-- **The first homology of a wedge of circles.** The first singular homology group with integer
coefficients of the wedge of circles indexed by `ι` is the free abelian group `ι →₀ ℤ`, the
Hurewicz class of the loop around the `i`-th circle going to `Finsupp.single i 1`
(`TauCeti.WedgeSum.circleFirstHomologyEquiv_hurewiczHomologyAddEquiv_expLoop`). -/
def circleFirstHomologyEquiv :
    ((singularChains ℤ).obj (TopCat.of (WedgeSum fun _ : ι ↦ (1 : Circle)))).homology 1 ≃ₗ[ℤ]
      (ι →₀ ℤ) :=
  ((hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : ι ↦ (1 : Circle))) (base _)
      (.refl ℤ)).symm.trans
    ((MulEquiv.toAdditive (circleFundamentalGroupMulEquiv ι).abelianizationCongr).trans
      (FreeAddCommGroup.freeAddCommGroupEquivAdditive.symm.trans
        (FreeAddCommGroup.equivFinsupp ι)))).toIntLinearEquiv

variable {ι}

/-- The Hurewicz class of the loop going once counterclockwise around the `i`-th circle of a wedge
of circles corresponds to the basis vector `Finsupp.single i 1` of `ι →₀ ℤ`. -/
@[simp]
theorem circleFirstHomologyEquiv_hurewiczHomologyAddEquiv_expLoop (i : ι) :
    circleFirstHomologyEquiv ι
        (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : ι ↦ (1 : Circle))) (base _)
          (.refl ℤ) (Additive.ofMul (Group.Abelianization.of
            (FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop)))))) =
      Finsupp.single i 1 := by
  -- The loop goes to the generator `i` of the free group, whose class in the abelianization is
  -- the generator `i` of the free commutative group on `ι` (`FreeCommGroup.of`).
  have h : MulEquiv.toAdditive (circleFundamentalGroupMulEquiv ι).abelianizationCongr
      (Additive.ofMul (Group.Abelianization.of
        (FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))))) =
      Additive.ofMul (Group.Abelianization.of (FreeGroup.of i)) := by
    simp [MulEquiv.toAdditive]
  have hB : (FreeAddCommGroup.freeAddCommGroupEquivAdditive.symm.trans
      (FreeAddCommGroup.equivFinsupp ι)) (Additive.ofMul (FreeCommGroup.of i)) =
      Finsupp.single i 1 := by
    rw [AddEquiv.trans_apply, FreeAddCommGroup.freeAddCommGroupEquivAdditive_symm_ofMul_of,
      FreeAddCommGroup.equivFinsupp_apply, FreeAddCommGroup.toFinsupp_of]
  rw [circleFirstHomologyEquiv, AddEquiv.coe_toIntLinearEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  -- `FreeCommGroup ι` is `Group.Abelianization (FreeGroup ι)` only up to unfolding, so the
  -- composite is not type-correct at reducible transparency and `AddEquiv.trans_apply` cannot
  -- rewrite it; the two steps are composed by unification instead.
  exact (congrArg (FreeAddCommGroup.freeAddCommGroupEquivAdditive.symm.trans
    (FreeAddCommGroup.equivFinsupp ι)) h).trans hB

/-- The inverse of `TauCeti.WedgeSum.circleFirstHomologyEquiv` sends the basis vector
`Finsupp.single i 1` to the Hurewicz class of the loop around the `i`-th circle. -/
theorem circleFirstHomologyEquiv_symm_single_one (i : ι) :
    (circleFirstHomologyEquiv ι).symm (Finsupp.single i 1) =
      hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : ι ↦ (1 : Circle))) (base _)
        (.refl ℤ) (Additive.ofMul (Group.Abelianization.of
          (FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))))) := by
  rw [LinearEquiv.symm_apply_eq, circleFirstHomologyEquiv_hurewiczHomologyAddEquiv_expLoop]

end WedgeSum

end TauCeti
