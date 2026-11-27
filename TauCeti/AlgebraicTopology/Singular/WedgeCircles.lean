/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic
public import TauCeti.GroupTheory.FreeGroup.Abelianization

/-!
# The first homology of a wedge of circles

For a type `ι`, the first singular homology group with integer coefficients of the wedge of
circles `⋁_ι S¹` is the free abelian group `ι →₀ ℤ` on the circles
(`TauCeti.WedgeSum.circleFirstHomologyEquiv`). The isomorphism is the composite of the degree-one
Hurewicz isomorphism `H₁(⋁_ι S¹; ℤ) ≅ π₁(⋁_ι S¹)ᵃᵇ`
(`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`) with the computation of the fundamental group of a
wedge of circles as the free group on `ι` (`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`): the
abelianization of a free group is the free abelian group on the same generators
(`FreeGroupBasis.abelianizationBasis`). The Hurewicz class
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
  (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : ι ↦ (1 : Circle))) (base _)
      (.refl ℤ)).symm.toIntLinearEquiv ≪≫ₗ
    (FreeGroupBasis.ofRepr (circleFundamentalGroupMulEquiv ι)).abelianizationBasis.repr

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
  -- The loop is the `i`-th element of the free basis given by `circleFundamentalGroupMulEquiv`,
  -- so its class is the `i`-th vector of the induced basis of the abelianization.
  have h : (FreeGroupBasis.ofRepr (circleFundamentalGroupMulEquiv ι)) i =
      FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop)) :=
    MulEquiv.symm_apply_eq _ |>.2 (circleFundamentalGroupMulEquiv_expLoop i).symm
  rw [circleFirstHomologyEquiv, LinearEquiv.trans_apply, AddEquiv.coe_toIntLinearEquiv,
    AddEquiv.symm_apply_apply, ← h, ← FreeGroupBasis.abelianizationBasis_apply,
    Module.Basis.repr_self]

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
