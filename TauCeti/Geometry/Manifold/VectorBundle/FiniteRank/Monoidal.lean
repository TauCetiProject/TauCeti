/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Tensor

/-!
# Smooth coherence equivalences for tensor products of bundle cores

The associator, unitors and symmetry of finite-rank bundle cores are smooth bundle
equivalences. Their underlying maps are exactly those of the existing symmetric monoidal
category, not new identifications of its objects. In particular the naturality, pentagon,
triangle and symmetry laws of that category remain the laws of these smooth comparisons.
Over a complex manifold at regularity `∞` these are biholomorphic bundle equivalences.

The comparisons act in each fibre by the corresponding Kronecker coordinate equivalence.
The tensor product retains the shared core carrier and the tensor unit is the trivial line.
No completeness of the scalar field or manifold structure on the base is required.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open CategoryTheory ContinuousLinearEquiv ContinuousLinearMap
open scoped Manifold ContDiff MonoidalCategory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  (A D C : FiniteRankBundleCore 𝕜 B)
  [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n]

/-- The tensor associator as a smooth bundle equivalence, over the identity on the base. -/
noncomputable def tensorAssociatorDiffeomorph :
    ((A ⊗ D) ⊗ C).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin ((A ⊗ D) ⊗ C).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (A ⊗ (D ⊗ C)).rank → 𝕜)⟯ (A ⊗ (D ⊗ C)).core.TotalSpace := by
  -- Normalize the dependent fibre models to the Kronecker coordinate spaces.
  refine constIsoDiffeomorph (A := tensor (tensor A D) C) (D := tensor A (tensor D C)) ?_ ?_ ?_
  · intro i
    dsimp only [tensor]
    exact Set.inter_assoc _ _ _
  · dsimp only [tensor]
    exact kroneckerAssoc 𝕜 A.rank D.rank C.rank
  · intro i j x hi hj
    dsimp only [tensor]
    exact kroneckerAssoc_comp_kronecker _ _ _

/-- The smooth associator has the same map as the monoidal associator. -/
@[simp]
theorem coe_tensorAssociatorDiffeomorph :
    ⇑(tensorAssociatorDiffeomorph (I := I) (n := n) A D C) = (α_ A D C).hom.totalSpaceMap := by
  funext p
  simp only [tensorAssociatorDiffeomorph, coe_constIsoDiffeomorph,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom,
    fiberMap_associator_hom]
  rfl

/-- The inverse smooth associator has the same map as the inverse monoidal associator. -/
@[simp]
theorem coe_tensorAssociatorDiffeomorph_symm :
    ⇑(tensorAssociatorDiffeomorph (I := I) (n := n) A D C).symm =
      (α_ A D C).inv.totalSpaceMap := by
  funext p
  simp only [tensorAssociatorDiffeomorph, coe_constIsoDiffeomorph_symm,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_inv,
    fiberMap_associator_inv]
  rfl

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The left tensor unitor as a smooth bundle equivalence. -/
noncomputable def tensorLeftUnitorDiffeomorph :
    ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace := by
  -- Normalize the dependent fibre models to the Kronecker coordinate spaces.
  refine constIsoDiffeomorph (A := tensor (trivial 𝕜 B 1) A) (D := A) ?_ ?_ ?_
  · intro i
    dsimp only [tensor, trivial]
    exact Set.univ_inter _
  · dsimp only [tensor, trivial]
    exact kroneckerLid 𝕜 A.rank
  · intro i j x hi hj
    dsimp only [tensor, trivial]
    exact kroneckerLid_comp_kronecker _

/-- The smooth left unitor retains the monoidal left unitor. -/
@[simp]
theorem coe_tensorLeftUnitorDiffeomorph :
    ⇑(tensorLeftUnitorDiffeomorph (I := I) (n := n) A) = (λ_ A).hom.totalSpaceMap := by
  funext p
  simp only [tensorLeftUnitorDiffeomorph, coe_constIsoDiffeomorph,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom,
    fiberMap_leftUnitor_hom]
  rfl

/-- The inverse smooth left unitor retains the inverse monoidal left unitor. -/
@[simp]
theorem coe_tensorLeftUnitorDiffeomorph_symm :
    ⇑(tensorLeftUnitorDiffeomorph (I := I) (n := n) A).symm = (λ_ A).inv.totalSpaceMap := by
  funext p
  simp only [tensorLeftUnitorDiffeomorph, coe_constIsoDiffeomorph_symm,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_inv,
    fiberMap_leftUnitor_inv]
  rfl

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The right tensor unitor as a smooth bundle equivalence. -/
noncomputable def tensorRightUnitorDiffeomorph :
    (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace := by
  -- Normalize the dependent fibre models to the Kronecker coordinate spaces.
  refine constIsoDiffeomorph (A := tensor A (trivial 𝕜 B 1)) (D := A) ?_ ?_ ?_
  · intro i
    dsimp only [tensor, trivial]
    exact Set.inter_univ _
  · dsimp only [tensor, trivial]
    exact kroneckerRid 𝕜 A.rank
  · intro i j x hi hj
    dsimp only [tensor, trivial]
    exact kroneckerRid_comp_kronecker _

/-- The smooth right unitor retains the monoidal right unitor. -/
@[simp]
theorem coe_tensorRightUnitorDiffeomorph :
    ⇑(tensorRightUnitorDiffeomorph (I := I) (n := n) A) = (ρ_ A).hom.totalSpaceMap := by
  funext p
  simp only [tensorRightUnitorDiffeomorph, coe_constIsoDiffeomorph,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom,
    fiberMap_rightUnitor_hom]
  rfl

/-- The inverse smooth right unitor retains the inverse monoidal right unitor. -/
@[simp]
theorem coe_tensorRightUnitorDiffeomorph_symm :
    ⇑(tensorRightUnitorDiffeomorph (I := I) (n := n) A).symm = (ρ_ A).inv.totalSpaceMap := by
  funext p
  simp only [tensorRightUnitorDiffeomorph, coe_constIsoDiffeomorph_symm,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_inv,
    fiberMap_rightUnitor_inv]
  rfl

omit [C.core.IsContMDiff I n] in
/-- The tensor symmetry as a smooth bundle equivalence. -/
noncomputable def tensorBraidingDiffeomorph :
    (A ⊗ D).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (D ⊗ A).rank → 𝕜)⟯ (D ⊗ A).core.TotalSpace := by
  -- Normalize the dependent fibre models to the Kronecker coordinate spaces.
  refine constIsoDiffeomorph (A := tensor A D) (D := tensor D A) ?_ ?_ ?_
  · intro i
    dsimp only [tensor]
    exact Set.inter_comm _ _
  · dsimp only [tensor]
    exact kroneckerComm 𝕜 A.rank D.rank
  · intro i j x hi hj
    dsimp only [tensor]
    exact kroneckerComm_comp_kronecker _ _

/-- The smooth tensor symmetry retains the monoidal braiding. -/
@[simp]
theorem coe_tensorBraidingDiffeomorph :
    ⇑(tensorBraidingDiffeomorph (I := I) (n := n) A D) = (β_ A D).hom.totalSpaceMap := by
  funext p
  simp only [tensorBraidingDiffeomorph, coe_constIsoDiffeomorph,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom,
    fiberMap_braiding_hom]
  rfl

/-- The inverse smooth tensor symmetry retains the inverse monoidal braiding. -/
@[simp]
theorem coe_tensorBraidingDiffeomorph_symm :
    ⇑(tensorBraidingDiffeomorph (I := I) (n := n) A D).symm = (β_ A D).inv.totalSpaceMap := by
  funext p
  simp only [tensorBraidingDiffeomorph, coe_constIsoDiffeomorph_symm,
    VectorBundleCore.CoordinateHom.totalSpaceMap_def, fiberMap_constIso_inv,
    fiberMap_braiding_inv]
  exact congrArg
    (fun e : (Fin (D.rank * A.rank) → 𝕜) ≃L[𝕜] (Fin (A.rank * D.rank) → 𝕜) ↦
      (⟨p.proj, e p.2⟩ : (A ⊗ D).core.TotalSpace)) (kroneckerComm_symm A.rank D.rank)

end TauCeti.FiniteRankBundleCore
