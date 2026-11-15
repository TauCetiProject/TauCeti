/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.WeakContractibility
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead

/-!
# Milnor's countable join and classifying space of a trivial group are contractible

The countable join `universalGSpace G` of a nonempty type `G` is weakly contractible
(`TauCeti.subsingleton_homotopyGroup_universalGSpace`) and carries a CW structure, so it is
contractible by Whitehead's theorem (`TauCeti.instContractibleSpaceUniversalGSpace`). When `G` is a
trivial group, the orbit map `classifyingSpaceProj G` is a homeomorphism
(`TauCeti.universalGSpaceHomeomorphClassifyingSpace`), so `classifyingSpace G` is contractible as
well (`TauCeti.instContractibleSpaceClassifyingSpace`).

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

namespace TauCeti

universe u

/-- **Milnor's countable join is contractible**: it is weakly contractible, and it has CW type
through its CW structure whose cells are the simplices of the countable join, so Whitehead's
theorem applies. -/
instance instContractibleSpaceUniversalGSpace (G : Type u) [Nonempty G] :
    ContractibleSpace (universalGSpace G) :=
  contractibleSpace_of_subsingleton_homotopyGroup (Classical.arbitrary _)
    (subsingleton_homotopyGroup_universalGSpace G · _)

/-- **For a trivial group `G`, the orbit map `classifyingSpaceProj G` is a homeomorphism** from
Milnor's countable join `universalGSpace G` onto `classifyingSpace G`. -/
noncomputable def universalGSpaceHomeomorphClassifyingSpace (G : Type u) [Group G]
    [Subsingleton G] : universalGSpace G ≃ₜ classifyingSpace G where
  toFun := classifyingSpaceProj G
  invFun := classifyingSpaceLift (ContinuousMap.id (universalGSpace G)) fun g x ↦ by
    rw [Subsingleton.elim g 1, one_smul]
  left_inv x := classifyingSpaceLift_apply _ _ x
  right_inv := (classifyingSpaceProj_surjective G).forall.mpr fun _ ↦ by simp
  continuous_toFun := continuous_classifyingSpaceProj G
  continuous_invFun := (classifyingSpaceLift _ _).continuous

/-- The forward map of `universalGSpaceHomeomorphClassifyingSpace G` is `classifyingSpaceProj G`. -/
@[simp]
theorem universalGSpaceHomeomorphClassifyingSpace_apply (G : Type u) [Group G] [Subsingleton G]
    (x : universalGSpace G) :
    universalGSpaceHomeomorphClassifyingSpace G x = classifyingSpaceProj G x :=
  (rfl)

/-- The inverse of `universalGSpaceHomeomorphClassifyingSpace G` recovers points from their
orbits. -/
@[simp]
theorem universalGSpaceHomeomorphClassifyingSpace_symm_proj (G : Type u) [Group G] [Subsingleton G]
    (x : universalGSpace G) :
    (universalGSpaceHomeomorphClassifyingSpace G).symm (classifyingSpaceProj G x) = x :=
  classifyingSpaceLift_apply _ _ x

/-- The inverse of `universalGSpaceHomeomorphClassifyingSpace G` sends
`classifyingSpaceBasepoint G` to `universalGSpaceBasepoint G`. -/
@[simp]
theorem universalGSpaceHomeomorphClassifyingSpace_symm_basepoint (G : Type u) [Group G]
    [Subsingleton G] :
    (universalGSpaceHomeomorphClassifyingSpace G).symm (classifyingSpaceBasepoint G) =
      universalGSpaceBasepoint G := by
  rw [← classifyingSpaceProj_universalGSpaceBasepoint G,
    universalGSpaceHomeomorphClassifyingSpace_symm_proj]

/-- **The classifying space of a trivial group is contractible**, being homeomorphic to Milnor's
contractible countable join `universalGSpace G`. -/
instance instContractibleSpaceClassifyingSpace (G : Type u) [Group G] [Subsingleton G] :
    ContractibleSpace (classifyingSpace G) :=
  (universalGSpaceHomeomorphClassifyingSpace G).symm.contractibleSpace

end TauCeti
