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
# Smooth coherence equivalences and tensor powers of bundle cores

The associator, unitors and symmetry of finite-rank bundle cores are smooth bundle
equivalences. Their underlying maps are exactly those of the existing symmetric monoidal
category, not new identifications of its objects. In particular the naturality, pentagon,
triangle and symmetry laws of that category remain the laws of these smooth comparisons.
Over a complex manifold at regularity `∞` these are biholomorphic bundle equivalences.

Iterated tensor powers `TauCeti.tensorPow A m` inherit `C^n` transition maps from `A`
(`FiniteRankBundleCore.isContMDiff_tensorPow`), tensor powers of `C^n` bundle maps preserve `C^n`
regularity in chart operators (`contMDiffOn_inChartCoordinates_tensorPowMap`) and on total spaces
(`contMDiff_totalSpaceMap_tensorPowMap`), and both the unit comparison `tensorPowUnitIso` and the
block decomposition `tensorPowAddIso` lift to `C^n` bundle equivalences (`tensorPowUnitDiffeomorph`,
`tensorPowAddDiffeomorph`) without completeness assumptions on the scalar field.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open CategoryTheory ContinuousLinearEquiv ContinuousLinearMap VectorBundleCore
open scoped Manifold ContDiff MonoidalCategory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  (A D C : FiniteRankBundleCore 𝕜 B)
  [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n]

-- The monoidal coherence isomorphisms are definitionally `constIso` with the data below;
-- using the same data lets their total-space maps be identified by the generic coe lemmas.

/-- The tensor associator as a smooth bundle equivalence, over the identity on the base. -/
noncomputable def tensorAssociatorDiffeomorph :
    ((A ⊗ D) ⊗ C).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin ((A ⊗ D) ⊗ C).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (A ⊗ (D ⊗ C)).rank → 𝕜)⟯ (A ⊗ (D ⊗ C)).core.TotalSpace :=
  constIsoDiffeomorph (A := tensor (tensor A D) C) (D := tensor A (tensor D C))
    (fun _ ↦ Set.inter_assoc _ _ _) (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
    fun _ _ _ _ _ ↦ kroneckerAssoc_comp_kronecker _ _ _

/-- The smooth associator has the same map as the monoidal associator. -/
@[simp]
theorem coe_tensorAssociatorDiffeomorph :
    ⇑(tensorAssociatorDiffeomorph (I := I) (n := n) A D C) = (α_ A D C).hom.totalSpaceMap :=
  coe_constIsoDiffeomorph _ _ _

/-- The inverse smooth associator has the same map as the inverse monoidal associator. -/
@[simp]
theorem coe_tensorAssociatorDiffeomorph_symm :
    ⇑(tensorAssociatorDiffeomorph (I := I) (n := n) A D C).symm =
      (α_ A D C).inv.totalSpaceMap :=
  coe_constIsoDiffeomorph_symm _ _ _

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The left tensor unitor as a smooth bundle equivalence. -/
noncomputable def tensorLeftUnitorDiffeomorph :
    ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  constIsoDiffeomorph (A := tensor (trivial 𝕜 B 1) A) (D := A)
    (fun _ ↦ Set.univ_inter _) (kroneckerLid 𝕜 A.rank)
    fun _ _ _ _ _ ↦ kroneckerLid_comp_kronecker _

/-- The smooth left unitor retains the monoidal left unitor. -/
@[simp]
theorem coe_tensorLeftUnitorDiffeomorph :
    ⇑(tensorLeftUnitorDiffeomorph (I := I) (n := n) A) = (λ_ A).hom.totalSpaceMap :=
  coe_constIsoDiffeomorph _ _ _

/-- The inverse smooth left unitor retains the inverse monoidal left unitor. -/
@[simp]
theorem coe_tensorLeftUnitorDiffeomorph_symm :
    ⇑(tensorLeftUnitorDiffeomorph (I := I) (n := n) A).symm = (λ_ A).inv.totalSpaceMap :=
  coe_constIsoDiffeomorph_symm _ _ _

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The right tensor unitor as a smooth bundle equivalence. -/
noncomputable def tensorRightUnitorDiffeomorph :
    (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  constIsoDiffeomorph (A := tensor A (trivial 𝕜 B 1)) (D := A)
    (fun _ ↦ Set.inter_univ _) (kroneckerRid 𝕜 A.rank)
    fun _ _ _ _ _ ↦ kroneckerRid_comp_kronecker _

/-- The smooth right unitor retains the monoidal right unitor. -/
@[simp]
theorem coe_tensorRightUnitorDiffeomorph :
    ⇑(tensorRightUnitorDiffeomorph (I := I) (n := n) A) = (ρ_ A).hom.totalSpaceMap :=
  coe_constIsoDiffeomorph _ _ _

/-- The inverse smooth right unitor retains the inverse monoidal right unitor. -/
@[simp]
theorem coe_tensorRightUnitorDiffeomorph_symm :
    ⇑(tensorRightUnitorDiffeomorph (I := I) (n := n) A).symm = (ρ_ A).inv.totalSpaceMap :=
  coe_constIsoDiffeomorph_symm _ _ _

omit [C.core.IsContMDiff I n] in
/-- The tensor symmetry as a smooth bundle equivalence. -/
noncomputable def tensorBraidingDiffeomorph :
    (A ⊗ D).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (D ⊗ A).rank → 𝕜)⟯ (D ⊗ A).core.TotalSpace :=
  constIsoDiffeomorph (A := tensor A D) (D := tensor D A)
    (fun _ ↦ Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
    fun _ _ _ _ _ ↦ kroneckerComm_comp_kronecker _ _

/-- The smooth tensor symmetry retains the monoidal braiding. -/
@[simp]
theorem coe_tensorBraidingDiffeomorph :
    ⇑(tensorBraidingDiffeomorph (I := I) (n := n) A D) = (β_ A D).hom.totalSpaceMap := by
  -- The braiding has one additional named wrapper around the constant isomorphism.
  simpa only [tensorBraidingDiffeomorph, braiding_def] using
    (coe_constIsoDiffeomorph (I := I) (n := n) (A := tensor A D) (D := tensor D A)
      (fun _ ↦ Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
      (fun _ _ _ _ _ ↦ kroneckerComm_comp_kronecker _ _))

/-- The inverse smooth tensor symmetry retains the inverse monoidal braiding. -/
@[simp]
theorem coe_tensorBraidingDiffeomorph_symm :
    ⇑(tensorBraidingDiffeomorph (I := I) (n := n) A D).symm = (β_ A D).inv.totalSpaceMap := by
  simpa only [tensorBraidingDiffeomorph, braiding_def] using
    (coe_constIsoDiffeomorph_symm (I := I) (n := n) (A := tensor A D) (D := tensor D A)
      (fun _ ↦ Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
      (fun _ _ _ _ _ ↦ kroneckerComm_comp_kronecker _ _))

/-! ### Chart-operator regularity of monoidal coherence maps -/

/-- The forward associator has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_associator_hom (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin ((A ⊗ D) ⊗ C).rank → 𝕜) →L[𝕜] (Fin (A ⊗ (D ⊗ C)).rank → 𝕜)) n
      (fun x ↦ ((A ⊗ D) ⊗ C).core.inChartCoordinates (A ⊗ (D ⊗ C)).core i j x
        ((α_ A D C).hom.fiberMap x))
      (((A ⊗ D) ⊗ C).core.baseSet i ∩ (A ⊗ (D ⊗ C)).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_constIso_hom (A := tensor (tensor A D) C)
    (D := tensor A (tensor D C)) (fun _ ↦ Set.inter_assoc _ _ _)
    (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
    (fun _ _ _ _ _ ↦ kroneckerAssoc_comp_kronecker _ _ _) i j

/-- The inverse associator has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_associator_inv (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin (A ⊗ (D ⊗ C)).rank → 𝕜) →L[𝕜] (Fin ((A ⊗ D) ⊗ C).rank → 𝕜)) n
      (fun x ↦ (A ⊗ (D ⊗ C)).core.inChartCoordinates ((A ⊗ D) ⊗ C).core i j x
        ((α_ A D C).inv.fiberMap x))
      ((A ⊗ (D ⊗ C)).core.baseSet i ∩ ((A ⊗ D) ⊗ C).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_constIso_inv (A := tensor (tensor A D) C)
    (D := tensor A (tensor D C)) (fun _ ↦ Set.inter_assoc _ _ _)
    (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
    (fun _ _ _ _ _ ↦ kroneckerAssoc_comp_kronecker _ _ _) i j

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The forward left unitor has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_leftUnitor_hom (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜) →L[𝕜]
      (Fin A.rank → 𝕜)) n
      (fun x ↦ ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.inChartCoordinates A.core i j x
        ((λ_ A).hom.fiberMap x))
      (((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.baseSet i ∩ A.core.baseSet j) :=
  contMDiffOn_inChartCoordinates_constIso_hom (A := tensor (trivial 𝕜 B 1) A) (D := A)
    (fun _ ↦ Set.univ_inter _) (kroneckerLid 𝕜 A.rank)
    (fun _ _ _ _ _ ↦ kroneckerLid_comp_kronecker _) i j

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The inverse left unitor has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_leftUnitor_inv (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜]
      (Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core i j x
        ((λ_ A).inv.fiberMap x))
      (A.core.baseSet i ∩ ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_constIso_inv (A := tensor (trivial 𝕜 B 1) A) (D := A)
    (fun _ ↦ Set.univ_inter _) (kroneckerLid 𝕜 A.rank)
    (fun _ _ _ _ _ ↦ kroneckerLid_comp_kronecker _) i j

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- Left whiskering by a `C^n` finite-rank core preserves `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_whiskerLeft {E E' : FiniteRankBundleCore 𝕜 B} (g : E ⟶ E')
    (hg : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates E'.core i j x (g.fiberMap x))
      (E.core.baseSet i ∩ E'.core.baseSet j)) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin (A ⊗ E).rank → 𝕜) →L[𝕜] (Fin (A ⊗ E').rank → 𝕜)) n
      (fun x ↦ (A ⊗ E).core.inChartCoordinates (A ⊗ E').core i j x ((A ◁ g).fiberMap x))
      ((A ⊗ E).core.baseSet i ∩ (A ⊗ E').core.baseSet j) :=
  contMDiffOn_inChartCoordinates_tensorHom (𝟙 A) g
    CoordinateHom.contMDiffOn_inChartCoordinates_id hg i j

/-! ### Smooth and holomorphic tensor powers -/

omit [C.core.IsContMDiff I n] in
/-- The monoidal tensor product `A ⊗ D` of `C^n` finite-rank cores is `C^n`. -/
instance isContMDiff_tensorObj : (A ⊗ D).core.IsContMDiff I n :=
  inferInstanceAs ((tensor A D).core.IsContMDiff I n)

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The monoidal unit `𝟙_ (FiniteRankBundleCore 𝕜 B)` is `C^n` at every regularity. -/
instance isContMDiff_tensorUnit : (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.IsContMDiff I n :=
  inferInstanceAs ((trivial 𝕜 B 1).core.IsContMDiff I n)

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- Iterated tensor powers of a finite-rank `C^n` core are `C^n`. Over a complex manifold at
regularity `∞`, this equips `tensorPow A m` with its holomorphic vector-bundle structure. -/
instance isContMDiff_tensorPow :
    ∀ m : ℕ, (tensorPow A m).core.IsContMDiff I n
  | 0 => inferInstance
  | m + 1 =>
    letI := isContMDiff_tensorPow m
    inferInstance

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- Tensor powers of a morphism with `C^n` chart operators have `C^n` chart operators, without
completeness or `C^n`-core assumptions on the factors. -/
theorem contMDiffOn_inChartCoordinates_tensorPowMap {E E' : FiniteRankBundleCore 𝕜 B} (f : E ⟶ E')
    (hf : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates E'.core i j x (f.fiberMap x))
      (E.core.baseSet i ∩ E'.core.baseSet j)) :
    ∀ (m : ℕ) (i j : B),
      ContMDiffOn I 𝓘(𝕜, (Fin (tensorPow E m).rank → 𝕜) →L[𝕜] (Fin (tensorPow E' m).rank → 𝕜)) n
        (fun x ↦ (tensorPow E m).core.inChartCoordinates (tensorPow E' m).core i j x
          ((tensorPowMap f m).fiberMap x))
        ((tensorPow E m).core.baseSet i ∩ (tensorPow E' m).core.baseSet j)
  | 0, i, j => by
    rw [tensorPowMap_zero]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_id i j
  | m + 1, i, j => by
    rw [tensorPowMap_succ]
    exact contMDiffOn_inChartCoordinates_tensorHom f (tensorPowMap f m) hf
      (contMDiffOn_inChartCoordinates_tensorPowMap f hf m) i j

omit [C.core.IsContMDiff I n] in
/-- Over a complete scalar field, tensor powers of a `C^n` bundle map between `C^n` finite-rank
cores are `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_tensorPowMap [CompleteSpace 𝕜]
    (f : A ⟶ D)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) (m : ℕ) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (tensorPow A m).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (tensorPow D m).rank → 𝕜)) n (tensorPowMap f m).totalSpaceMap :=
  (tensorPowMap f m).contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_tensorPowMap f (f.contMDiff_totalSpaceMap_iff.1 hf) m)

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The forward unit tensor-power comparison has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_tensorPowUnitIso_hom :
    ∀ (m : ℕ) (i j : B),
      ContMDiffOn I 𝓘(𝕜, (Fin (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).rank → 𝕜) →L[𝕜]
        (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)) n
        (fun x ↦ (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).core.inChartCoordinates
          (𝟙_ (FiniteRankBundleCore 𝕜 B)).core i j x
          ((tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).hom.fiberMap x))
        ((tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).core.baseSet i ∩
          (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.baseSet j)
  | 0, i, j => by
    rw [tensorPowUnitIso_zero, Iso.refl_hom]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_id i j
  | m + 1, i, j => by
    rw [tensorPowUnitIso_succ_hom]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_leftUnitor_hom (I := I) (n := n)
        (𝟙_ (FiniteRankBundleCore 𝕜 B)))
      (contMDiffOn_inChartCoordinates_whiskerLeft (I := I) (n := n)
        (𝟙_ (FiniteRankBundleCore 𝕜 B))
        (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).hom
        (contMDiffOn_inChartCoordinates_tensorPowUnitIso_hom m)) i j

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The inverse unit tensor-power comparison has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_tensorPowUnitIso_inv :
    ∀ (m : ℕ) (i j : B),
      ContMDiffOn I 𝓘(𝕜, (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜) →L[𝕜]
        (Fin (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).rank → 𝕜)) n
        (fun x ↦ (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.inChartCoordinates
          (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).core i j x
          ((tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).inv.fiberMap x))
        ((𝟙_ (FiniteRankBundleCore 𝕜 B)).core.baseSet i ∩
          (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).core.baseSet j)
  | 0, i, j => by
    rw [tensorPowUnitIso_zero, Iso.refl_inv]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_id i j
  | m + 1, i, j => by
    rw [tensorPowUnitIso_succ_inv]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_whiskerLeft (I := I) (n := n)
        (𝟙_ (FiniteRankBundleCore 𝕜 B))
        (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).inv
        (contMDiffOn_inChartCoordinates_tensorPowUnitIso_inv m))
      (contMDiffOn_inChartCoordinates_leftUnitor_inv (I := I) (n := n)
        (𝟙_ (FiniteRankBundleCore 𝕜 B))) i j

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The unit tensor-power comparison `tensorPow (𝟙_ _) m ≅ 𝟙_ _` as a `C^n` bundle equivalence,
without completeness assumptions on `𝕜`. -/
noncomputable def tensorPowUnitDiffeomorph (m : ℕ) :
    (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (tensorPow (𝟙_ (FiniteRankBundleCore 𝕜 B)) m).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)⟯
      (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.TotalSpace :=
  (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).hom.toDiffeomorphOfInv
    (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).inv
    (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).hom_inv_id
    (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).inv_hom_id
    ((tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).hom.contMDiff_totalSpaceMap
      (contMDiffOn_inChartCoordinates_tensorPowUnitIso_hom m))
    ((tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).inv.contMDiff_totalSpaceMap
      (contMDiffOn_inChartCoordinates_tensorPowUnitIso_inv m))

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
@[simp]
theorem coe_tensorPowUnitDiffeomorph (m : ℕ) :
    ⇑(tensorPowUnitDiffeomorph (𝕜 := 𝕜) (B := B) (I := I) (n := n) m) =
      (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
@[simp]
theorem coe_tensorPowUnitDiffeomorph_symm (m : ℕ) :
    ⇑(tensorPowUnitDiffeomorph (𝕜 := 𝕜) (B := B) (I := I) (n := n) m).symm =
      (tensorPowUnitIso (FiniteRankBundleCore 𝕜 B) m).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The forward block decomposition `tensorPow A m ⊗ tensorPow A k ⟶ tensorPow A (k + m)` has
`C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_tensorPowAddIso_hom (k : ℕ) :
    ∀ (m : ℕ) (i j : B),
      ContMDiffOn I 𝓘(𝕜, (Fin (tensorPow A m ⊗ tensorPow A k).rank → 𝕜) →L[𝕜]
        (Fin (tensorPow A (k + m)).rank → 𝕜)) n
        (fun x ↦ (tensorPow A m ⊗ tensorPow A k).core.inChartCoordinates
          (tensorPow A (k + m)).core i j x ((tensorPowAddIso A m k).hom.fiberMap x))
        ((tensorPow A m ⊗ tensorPow A k).core.baseSet i ∩
          (tensorPow A (k + m)).core.baseSet j)
  | 0, i, j => by
    rw [tensorPowAddIso_zero]
    exact contMDiffOn_inChartCoordinates_leftUnitor_hom (tensorPow A k) i j
  | m + 1, i, j => by
    rw [tensorPowAddIso_succ_hom]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_whiskerLeft A (tensorPowAddIso A m k).hom
        (contMDiffOn_inChartCoordinates_tensorPowAddIso_hom k m))
      (contMDiffOn_inChartCoordinates_associator_hom A (tensorPow A m) (tensorPow A k)) i j

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The inverse block decomposition `tensorPow A (k + m) ⟶ tensorPow A m ⊗ tensorPow A k` has
`C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_tensorPowAddIso_inv (k : ℕ) :
    ∀ (m : ℕ) (i j : B),
      ContMDiffOn I 𝓘(𝕜, (Fin (tensorPow A (k + m)).rank → 𝕜) →L[𝕜]
        (Fin (tensorPow A m ⊗ tensorPow A k).rank → 𝕜)) n
        (fun x ↦ (tensorPow A (k + m)).core.inChartCoordinates
          (tensorPow A m ⊗ tensorPow A k).core i j x ((tensorPowAddIso A m k).inv.fiberMap x))
        ((tensorPow A (k + m)).core.baseSet i ∩
          (tensorPow A m ⊗ tensorPow A k).core.baseSet j)
  | 0, i, j => by
    rw [tensorPowAddIso_zero]
    exact contMDiffOn_inChartCoordinates_leftUnitor_inv (tensorPow A k) i j
  | m + 1, i, j => by
    rw [tensorPowAddIso_succ_inv]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_associator_inv A (tensorPow A m) (tensorPow A k))
      (contMDiffOn_inChartCoordinates_whiskerLeft A (tensorPowAddIso A m k).inv
        (contMDiffOn_inChartCoordinates_tensorPowAddIso_inv k m)) i j

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The block decomposition `tensorPow A m ⊗ tensorPow A k ≅ tensorPow A (k + m)` as a `C^n`
bundle equivalence, without completeness assumptions on `𝕜`. -/
noncomputable def tensorPowAddDiffeomorph (m k : ℕ) :
    (tensorPow A m ⊗ tensorPow A k).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (tensorPow A m ⊗ tensorPow A k).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (tensorPow A (k + m)).rank → 𝕜)⟯ (tensorPow A (k + m)).core.TotalSpace :=
  (tensorPowAddIso A m k).hom.toDiffeomorphOfInv
    (tensorPowAddIso A m k).inv
    (tensorPowAddIso A m k).hom_inv_id
    (tensorPowAddIso A m k).inv_hom_id
    ((tensorPowAddIso A m k).hom.contMDiff_totalSpaceMap
      (contMDiffOn_inChartCoordinates_tensorPowAddIso_hom A k m))
    ((tensorPowAddIso A m k).inv.contMDiff_totalSpaceMap
      (contMDiffOn_inChartCoordinates_tensorPowAddIso_inv A k m))

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
@[simp]
theorem coe_tensorPowAddDiffeomorph (m k : ℕ) :
    ⇑(tensorPowAddDiffeomorph (I := I) (n := n) A m k) =
      (tensorPowAddIso A m k).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
@[simp]
theorem coe_tensorPowAddDiffeomorph_symm (m k : ℕ) :
    ⇑(tensorPowAddDiffeomorph (I := I) (n := n) A m k).symm =
      (tensorPowAddIso A m k).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

end TauCeti.FiniteRankBundleCore
