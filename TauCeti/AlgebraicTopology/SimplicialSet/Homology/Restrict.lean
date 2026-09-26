/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Restrict

/-!
# Relative homology of a restricted pair

For a pair of simplicial sets `P` and a subcomplex `S` of its ambient simplicial set, the
inclusion `P.restrictι S : P.restrict S ⟶ P` of the restricted pair `(S, S ∩ P.left)` induces
isomorphisms on relative homology as soon as the inclusions of `S` and of its preimage in `P.left`
are quasi-isomorphisms on chains (`SSetPair.isIso_homologyMap_restrictι`).  This is the algebraic
step reducing excision for singular homology to the small-chain theorem: restricting the singular
pair of a topological pair to the simplices subordinate to an open cover does not change relative
homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Theorem 2.20.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w

namespace SSetPair

variable {P : SSetPair.{w}} {S : P.right.Subcomplex}
  {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A]

/-- If the inclusions of a subcomplex `S` of the ambient simplicial set of a pair `P` and of its
preimage in the subcomplex of `P` are quasi-isomorphisms on chains, then the inclusion of the
restricted pair induces isomorphisms on relative homology. -/
lemma isIso_homologyMap_restrictι (R : A)
    (h₁ : QuasiIso (SSet.chainComplexMap (S.preimage P.hom).ι R))
    (h₂ : QuasiIso (SSet.chainComplexMap S.ι R)) (n : ℕ) :
    IsIso (SSetPair.homologyMap (P.restrictι S) R n) := by
  have : QuasiIso (SSet.chainComplexMap (P.restrictι S).left R) := by
    rw [restrictι_left]
    exact h₁
  have : QuasiIso (SSet.chainComplexMap (P.restrictι S).right R) := by
    rw [restrictι_right]
    exact h₂
  exact isIso_homologyMap_of_quasiIso _ R n

end SSetPair
