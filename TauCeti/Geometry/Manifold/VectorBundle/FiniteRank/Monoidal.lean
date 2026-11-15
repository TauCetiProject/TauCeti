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
# Smooth coherence equivalences and tensor powers for finite-rank bundle cores

The associator, unitors and symmetry of finite-rank bundle cores are smooth bundle
equivalences. Their underlying maps are exactly those of the existing symmetric monoidal
category, not new identifications of its objects. In particular the naturality, pentagon,
triangle and symmetry laws of that category remain the laws of these smooth comparisons.
Over a complex manifold at regularity `∞` these are biholomorphic bundle equivalences.

Because the model fibre of a `FiniteRankBundleCore` is an explicit coordinate space `Fin r → 𝕜`,
expanding an operator along the standard basis vectors `Pi.single k 1` recovers `C^n` regularity
of all chart operators from `C^n` regularity of the glued total-space map without completeness of
the scalar field (`FiniteRankBundleCore.contMDiff_totalSpaceMap_iff_inChartCoordinates`). Hence
monoidal products and right-recursive tensor powers preserve `C^n` cores and `C^n` bundle maps
without completeness of `𝕜` or manifold assumptions on the base;
`TauCeti.ContMDiffFiniteRankBundleCore` in
`TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Picard` packages this into a symmetric monoidal
category.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle CategoryTheory ContinuousLinearEquiv ContinuousLinearMap Set VectorBundleCore
open scoped Manifold ContDiff MonoidalCategory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
section Coherence

variable (A D C : FiniteRankBundleCore 𝕜 B)
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

theorem contMDiff_totalSpaceMap_associator_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin ((A ⊗ D) ⊗ C).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A ⊗ (D ⊗ C)).rank → 𝕜)) n (α_ A D C).hom.totalSpaceMap :=
  coe_tensorAssociatorDiffeomorph (I := I) (n := n) A D C ▸
    (tensorAssociatorDiffeomorph (I := I) (n := n) A D C).contMDiff

theorem contMDiff_totalSpaceMap_associator_inv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ (D ⊗ C)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin ((A ⊗ D) ⊗ C).rank → 𝕜)) n (α_ A D C).inv.totalSpaceMap :=
  coe_tensorAssociatorDiffeomorph_symm (I := I) (n := n) A D C ▸
    (tensorAssociatorDiffeomorph (I := I) (n := n) A D C).symm.contMDiff

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_leftUnitor_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (λ_ A).hom.totalSpaceMap :=
  coe_tensorLeftUnitorDiffeomorph (I := I) (n := n) A ▸
    (tensorLeftUnitorDiffeomorph (I := I) (n := n) A).contMDiff

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_leftUnitor_inv :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜)) n
      (λ_ A).inv.totalSpaceMap :=
  coe_tensorLeftUnitorDiffeomorph_symm (I := I) (n := n) A ▸
    (tensorLeftUnitorDiffeomorph (I := I) (n := n) A).symm.contMDiff

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_rightUnitor_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (ρ_ A).hom.totalSpaceMap :=
  coe_tensorRightUnitorDiffeomorph (I := I) (n := n) A ▸
    (tensorRightUnitorDiffeomorph (I := I) (n := n) A).contMDiff

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_rightUnitor_inv :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).rank → 𝕜)) n
      (ρ_ A).inv.totalSpaceMap :=
  coe_tensorRightUnitorDiffeomorph_symm (I := I) (n := n) A ▸
    (tensorRightUnitorDiffeomorph (I := I) (n := n) A).symm.contMDiff

omit [C.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_braiding_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D ⊗ A).rank → 𝕜)) n (β_ A D).hom.totalSpaceMap :=
  coe_tensorBraidingDiffeomorph (I := I) (n := n) A D ▸
    (tensorBraidingDiffeomorph (I := I) (n := n) A D).contMDiff

omit [C.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_braiding_inv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (D ⊗ A).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜)) n (β_ A D).inv.totalSpaceMap :=
  coe_tensorBraidingDiffeomorph_symm (I := I) (n := n) A D ▸
    (tensorBraidingDiffeomorph (I := I) (n := n) A D).symm.contMDiff

end Coherence

/-! ### Chart operators and tensor powers of smooth bundle maps -/

section ChartOperators

/-- The monoidal unit of finite-rank cores is `C^n`. -/
instance isContMDiff_tensorUnit :
    (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.IsContMDiff I n :=
  isContMDiff_trivial 1

/-- The monoidal product of `C^n` finite-rank cores is `C^n`. -/
instance isContMDiff_tensorObj (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] :
    (A ⊗ D).core.IsContMDiff I n :=
  isContMDiff_tensor A D

variable {A A' D D' : FiniteRankBundleCore 𝕜 B}
  [A.core.IsContMDiff I n] [A'.core.IsContMDiff I n]
  [D.core.IsContMDiff I n] [D'.core.IsContMDiff I n]

/-- For a morphism between `C^n` finite-rank cores, `C^n` regularity of the glued total-space map
implies `C^n` regularity of every chart operator, without completeness of the scalar field:
expanding an operator on `Fin A.rank → 𝕜` along the standard basis vectors reduces the operator
regularity to that of its columns. -/
theorem contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap (f : A ⟶ A')
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      f.totalSpaceMap) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x))
      (A.core.baseSet i ∩ A'.core.baseSet j) := by
  have : MemTrivializationAtlas (A.core.localTriv i) := ⟨⟨i, rfl⟩⟩
  have : MemTrivializationAtlas (A'.core.localTriv j) := ⟨⟨j, rfl⟩⟩
  set U := A.core.baseSet i ∩ A'.core.baseSet j
  have hU : IsOpen U := (A.core.isOpen_baseSet i).inter (A'.core.isOpen_baseSet j)
  -- Each column is obtained by feeding a constant standard basis section in chart `i` into
  -- `f.totalSpaceMap` and reading the image in chart `j`.
  have hcol (k : Fin A.rank) : ContMDiffOn I 𝓘(𝕜, Fin A'.rank → 𝕜) n
      (fun x ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x) (Pi.single k 1)) U := by
    have hs := (A.core.localTriv i).contMDiffOn_section_symm (IB := I) (n := n) hU
      inter_subset_left (contMDiffOn_const (c := Pi.single k (1 : 𝕜)))
    have hfs : ContMDiffOn I (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin A'.rank → 𝕜) (E := A'.core.Fiber) x
          (f.fiberMap x ((A.core.localTriv i).symm x (Pi.single k 1)))) U :=
      (hf.comp_contMDiffOn hs).congr fun x _ ↦ (f.totalSpaceMap_mk x _).symm
    refine (((A'.core.localTriv j).contMDiffOn_section_iff hU inter_subset_right).mp hfs).congr
      fun x hx ↦ ?_
    simp only [VectorBundleCore.inChartCoordinates_apply, A'.core.localTriv_apply,
      A.core.localTriv_symm_apply i hx.1]
  let Φ : (Fin A.rank → Fin A'.rank → 𝕜) → (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜) :=
    fun g ↦ ∑ k : Fin A.rank, smulRightL 𝕜 (Fin A.rank → 𝕜) (Fin A'.rank → 𝕜) (proj k) (g k)
  have hΦ : ContDiff 𝕜 n Φ :=
    ContDiff.sum fun k _ ↦
      (smulRightL 𝕜 (Fin A.rank → 𝕜) (Fin A'.rank → 𝕜) (proj k)).contDiff.comp
        (contDiff_apply 𝕜 _ k)
  refine (hΦ.contMDiff.comp_contMDiffOn (contMDiffOn_pi_module_iff.mpr hcol)).congr fun x _ ↦ ?_
  ext v m
  have hv : (∑ k : Fin A.rank, v k • Pi.single k (1 : 𝕜)) = v := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  symm
  calc
    (Φ fun k ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x) (Pi.single k 1)) v m
      = (∑ k : Fin A.rank,
          A.core.inChartCoordinates A'.core i j x (f.fiberMap x) (v k • Pi.single k 1)) m := by
        simp only [Φ, sum_apply, smulRightL_apply_apply, smulRight_apply, proj_apply,
          _root_.map_smul]
    _ = A.core.inChartCoordinates A'.core i j x (f.fiberMap x) v m := by rw [← map_sum, hv]

/-- For a morphism between `C^n` finite-rank cores, the glued map of total spaces is `C^n`
if and only if every chart operator is `C^n` on its domain, without completeness of `𝕜`. -/
theorem contMDiff_totalSpaceMap_iff_inChartCoordinates (f : A ⟶ A') :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n f.totalSpaceMap ↔
      ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜)) n
        (fun x ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x))
        (A.core.baseSet i ∩ A'.core.baseSet j) :=
  ⟨contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap f, f.contMDiff_totalSpaceMap⟩

/-- Monoidal tensor products of `C^n` bundle maps between `C^n` finite-rank cores have `C^n`
total-space maps, without completeness of the scalar field. -/
theorem contMDiff_totalSpaceMap_monoidalTensorHom (f : A ⟶ A') (g : D ⟶ D')
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      f.totalSpaceMap)
    (hg : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      g.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (A' ⊗ D').rank → 𝕜)) n
      (f ⊗ₘ g).totalSpaceMap :=
  (tensorHom f g).contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_tensorHom f g
      (contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap f hf)
      (contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap g hg))

omit [A'.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_whiskerLeft (A : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff I n] (g : D ⟶ D')
    (hg : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      g.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (A ⊗ D').rank → 𝕜)) n
      (A ◁ g).totalSpaceMap :=
  contMDiff_totalSpaceMap_monoidalTensorHom (𝟙 A) g
    (CoordinateHom.contMDiff_totalSpaceMap_id A.core) hg

omit [D'.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_whiskerRight (f : A ⟶ A')
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      f.totalSpaceMap) (D : FiniteRankBundleCore 𝕜 B) [D.core.IsContMDiff I n] :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (A' ⊗ D).rank → 𝕜)) n
      (f ▷ D).totalSpaceMap :=
  contMDiff_totalSpaceMap_monoidalTensorHom f (𝟙 D) hf
    (CoordinateHom.contMDiff_totalSpaceMap_id D.core)

end ChartOperators

section TensorPower

variable {A D : FiniteRankBundleCore 𝕜 B} [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]

/-- Every tensor power of a `C^n` finite-rank core is `C^n`. -/
instance isContMDiff_tensorPower (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n] :
    ∀ m : ℕ, (A.tensorPower m).core.IsContMDiff I n
  | 0 => isContMDiff_tensorUnit
  | m + 1 =>
    letI := isContMDiff_tensorPower A m
    isContMDiff_tensorObj (A.tensorPower m) A

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] in
/-- An isomorphism of finite-rank cores whose forward and inverse maps are `C^n` on total spaces
induces a `C^n` diffeomorphism of total spaces, without completeness or smoothness of
transitions. -/
def isoToDiffeomorph (e : A ≅ D)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯ D.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv e.hom e.inv e.hom_inv_id e.inv_hom_id he_hom he_inv

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] in
@[simp] theorem coe_isoToDiffeomorph (e : A ≅ D)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(isoToDiffeomorph e he_hom he_inv) = e.hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

omit [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] in
@[simp] theorem coe_isoToDiffeomorph_symm (e : A ≅ D)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(isoToDiffeomorph e he_hom he_inv).symm = e.inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

/-- Taking the `m`-th tensor power preserves `C^n` regularity of glued total-space maps. -/
theorem contMDiff_totalSpaceMap_tensorPowerHom (f : A ⟶ D)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) :
    ∀ m : ℕ, ContMDiff (I.prod 𝓘(𝕜, Fin (A.tensorPower m).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.tensorPower m).rank → 𝕜)) n (tensorPowerHom f m).totalSpaceMap
  | 0 => by rw [tensorPowerHom_zero]; exact CoordinateHom.contMDiff_totalSpaceMap_id _
  | m + 1 => by
    rw [tensorPowerHom_succ]
    exact contMDiff_totalSpaceMap_monoidalTensorHom (tensorPowerHom f m) f
      (contMDiff_totalSpaceMap_tensorPowerHom f hf m) hf

omit [D.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_isoTensorUnitOfCoordChangeEqId_hom
    (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n]
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)) n
      (isoTensorUnitOfCoordChangeEqId A e h).hom.totalSpaceMap :=
  CoordinateHom.contMDiff_totalSpaceMap _ fun i j ↦
    (contMDiffOn_const (c := e.toContinuousLinearMap)).congr fun x hx ↦
      (CoordinateHom.operator_eq (isoTensorUnitOfCoordChangeEqId A e h).hom i j ⟨x, hx⟩).symm.trans
        (operator_isoTensorUnitOfCoordChangeEqId_hom A e h i j ⟨x, hx⟩)

omit [D.core.IsContMDiff I n] in
theorem contMDiff_totalSpaceMap_isoTensorUnitOfCoordChangeEqId_inv
    (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n]
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      (isoTensorUnitOfCoordChangeEqId A e h).inv.totalSpaceMap :=
  CoordinateHom.contMDiff_totalSpaceMap _ fun i j ↦
    (contMDiffOn_const (c := e.symm.toContinuousLinearMap)).congr fun x hx ↦
      (CoordinateHom.operator_eq (isoTensorUnitOfCoordChangeEqId A e h).inv i j ⟨x, hx⟩).symm.trans
        (operator_isoTensorUnitOfCoordChangeEqId_inv A e h i j ⟨x, hx⟩)

end TensorPower

end TauCeti.FiniteRankBundleCore
