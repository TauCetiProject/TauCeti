/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic

/-!
# First homology of loop spaces

For a path-connected based loop space, degree-one Hurewicz and the loop-space shift identify
its integral first homology with the second homotopy group of the original space. The
abelianization disappears because higher homotopy groups are commutative.

When `π₂(X, x)` vanishes, the double Moore loop space is path connected and
`H₁(ΩᴹΩᴹX; ℤ) ≅ π₃(X, x)`. This is the low-degree homological input to detecting higher
homotopy through double loop spaces. The Moore comparisons use the specified normalization
homotopy equivalences; the final `doubleFirstCubicalHomologyAddEquiv` transports the result to
normalized cubical homology through `singularCubicalHomologyIso`. No connectedness assumption
on `X` is needed.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1 and §4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy
open AlgebraicTopology HomotopyGroup

namespace TauCeti

variable {X : Type} [TopologicalSpace X]

/-- Degree-one Hurewicz identifies the first integral homology of a path-connected loop
space with the second homotopy group of the original space. -/
def pathLoopSpaceFirstHomologyAddEquiv (x : X) [PathConnectedSpace (Ω X x)] :
    Additive (π_ 2 X x) ≃+
      ((singularChains ℤ).obj (TopCat.of (Ω X x))).homology 1 :=
  let e : FundamentalGroup (Ω X x) (Path.refl x) ≃* π_ 2 X x :=
    pi1MulEquivFundamentalGroup.symm.trans (pathLoopSpaceMulEquiv 0)
  ((Abelianization.equivOfComm.trans e.symm.abelianizationCongr).toAdditive).trans
    (HurewiczOne.hurewiczHomologyAddEquiv (X := TopCat.of (Ω X x)) (Path.refl x))

/-- The inverse Hurewicz isomorphism sends the homology class of a loop of loops to
its class under the loop-space shift. -/
@[simp]
theorem pathLoopSpaceFirstHomologyAddEquiv_symm_loopClass (x : X)
    [PathConnectedSpace (Ω X x)] (γ : Path (Path.refl x) (Path.refl x)) :
    (pathLoopSpaceFirstHomologyAddEquiv x).symm
        (HurewiczOne.H₁AddEquivHomology (TopCat.of (Ω X x)) (HurewiczOne.loopClass γ)) =
      Additive.ofMul (pathLoopSpaceMulEquiv 0
        (pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk γ))) := by
  rw [AddEquiv.symm_apply_eq]
  simp only [pathLoopSpaceFirstHomologyAddEquiv, AddEquiv.trans_apply,
    MulEquiv.toAdditive_apply_apply, toMul_ofMul, MulEquiv.trans_apply,
    Abelianization.equivOfComm_apply,
    abelianizationCongr_of, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  exact (HurewiczOne.hurewiczHomologyAddEquiv_ofMul_of_mk
    (X := TopCat.of (Ω X x)) γ).symm

namespace MooreLoopSpace

/-- Normalization identifies the first integral homology of a path-connected Moore loop
space with the second homotopy group of the original space. -/
def firstHomologyAddEquiv (x : X) [PathConnectedSpace (MooreLoopSpace X x)] :
    Additive (π_ 2 X x) ≃+
      ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace X x))).homology 1 :=
  letI := (homotopyEquivPath x).pathConnectedSpace
  (pathLoopSpaceFirstHomologyAddEquiv x).trans
    ((homotopyEquivPath x).singularHomologyIso (ModuleCat.of ℤ ℤ) 1).symm.toLinearEquiv.toAddEquiv

/-- When `π₂(X, x)` vanishes, the first integral homology of the double Moore loop space
is the third homotopy group of `X`, using the specified normalization comparisons. -/
def doubleFirstHomologyAddEquiv (x : X) [Subsingleton (π_ 2 X x)] :
    Additive (π_ 3 X x) ≃+
      ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology 1 :=
  letI := pathConnectedSpace_double x
  (homotopyGroupMulEquiv x 1).symm.toAdditive.trans
    (firstHomologyAddEquiv (1 : MooreLoopSpace X x))

/-- The inverse comparison computes a Moore-loop homology class by normalizing it to
fixed-interval loops and applying the inverse Hurewicz isomorphism. -/
theorem firstHomologyAddEquiv_symm_apply (x : X) [PathConnectedSpace (MooreLoopSpace X x)]
    (a : ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace X x))).homology 1) :
    (firstHomologyAddEquiv x).symm a =
      letI := (homotopyEquivPath x).pathConnectedSpace
      (pathLoopSpaceFirstHomologyAddEquiv x).symm
        (((homotopyEquivPath x).singularHomologyIso (ModuleCat.of ℤ ℤ) 1).hom.hom a) := by
  rfl

/-- The inverse double-loop comparison applies the inverse first-homology comparison
and then the Moore loop-space shift. -/
theorem doubleFirstHomologyAddEquiv_symm_apply (x : X) [Subsingleton (π_ 2 X x)]
    (a : ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology 1) :
    (doubleFirstHomologyAddEquiv x).symm a =
      letI := pathConnectedSpace_double x
      (homotopyGroupMulEquiv x 1).toAdditive
        ((firstHomologyAddEquiv (1 : MooreLoopSpace X x)).symm a) := by
  rfl

/-- With normalized cubical chains, the first homology of the double Moore loop space
is the third homotopy group of the original space when its second homotopy group vanishes. -/
def doubleFirstCubicalHomologyAddEquiv (x : X) [Subsingleton (π_ 2 X x)] :
    Additive (π_ 3 X x) ≃+
      ((normalizedCubicalChainComplex ℤ).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology 1 :=
  let e := singularCubicalHomologyIso ℤ (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) 1
  (doubleFirstHomologyAddEquiv x).trans e.toLinearEquiv.toAddEquiv

/-- The cubical isomorphism is the singular isomorphism followed by the homology map
of the named singular-to-cubical comparison. -/
theorem doubleFirstCubicalHomologyAddEquiv_apply (x : X) [Subsingleton (π_ 2 X x)]
    (a : Additive (π_ 3 X x)) :
    doubleFirstCubicalHomologyAddEquiv x a =
      (HomologicalComplex.homologyMap
        ((singularToCubical ℤ).app (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))) 1).hom
          (doubleFirstHomologyAddEquiv x a) := by
  simp only [doubleFirstCubicalHomologyAddEquiv, AddEquiv.trans_apply]
  rw [← singularCubicalHomologyIso_hom]
  rfl

end MooreLoopSpace

end TauCeti
