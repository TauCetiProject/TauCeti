/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# Smooth and holomorphic rank-one presentation of scalar line-bundle cores

For any `C^n` scalar line-bundle core `Z : VectorBundleCore 𝕜 B 𝕜 ι`, its point-indexed rank-one
presentation `FiniteRankBundleCore.ofScalarCore Z` is `C^n`, and the topological comparison
`ofScalarCoreHomeomorph Z` refines to a `C^n` bundle equivalence `ofScalarCoreDiffeomorph Z` over
the identity of `B` without completeness assumptions on `𝕜`. Over a complex manifold at regularity
`∞`, this identifies holomorphic line bundles presented by scalar transition cocycles with
holomorphic rank-one cores in `FiniteRankBundleCore ℂ B`.

We also refine `isoTrivialOfCoordChangeEqId` to the `C^n` bundle equivalence
`diffeomorphTrivialOfCoordChangeEqId`, and prove that mutually inverse `C^n` cocycle morphisms
between rank-one `C^n` cores transfer global compatible `C^n` trivializations
(`VectorBundleCore.CoordinateHom.exists_trivialization_baseSet_eq_univ_iff_of_inv`).

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace VectorBundleCore.CoordinateHom

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B]
  {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}
  [Z.IsContMDiff I n] [W.IsContMDiff I n]

/-- Pushing a nowhere-vanishing `C^n` section forward along a `C^n` cocycle morphism with a left
inverse produces a nowhere-vanishing `C^n` section of the target core. -/
private theorem exists_section_ne_zero_of_left_inv (hF : finrank 𝕜 F = 1) (hG : finrank 𝕜 G = 1)
    (a : CoordinateHom Z W) (b : CoordinateHom W Z) (hba : b.comp a = CoordinateHom.id Z)
    (ha : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n a.totalSpaceMap)
    (hZ : ∃ (e : Trivialization F (π F Z.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F I n).maximalAtlas (TotalSpace F Z.Fiber) ∧
        e.baseSet = univ) :
    ∃ (e : Trivialization G (π G W.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B G I n).maximalAtlas (TotalSpace G W.Fiber) ∧
        e.baseSet = univ := by
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero hF] at hZ
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero hG]
  obtain ⟨σ, hσ, hσ₀⟩ := hZ
  have hcomp : (fun x ↦ TotalSpace.mk' G x (a.fiberMap x (σ x))) =
      a.totalSpaceMap ∘ fun x ↦ TotalSpace.mk' F x (σ x) := by
    funext x
    rw [Function.comp_apply, CoordinateHom.totalSpaceMap_def]
  refine ⟨fun x ↦ a.fiberMap x (σ x), hcomp ▸ ha.comp hσ, fun x h0 ↦ hσ₀ x ?_⟩
  let v : F := σ x
  have h1 := DFunLike.congr_fun (congrFun (congrArg CoordinateHom.fiberMap hba) x) v
  have h0' : a.fiberMap x v = (0 : G) := h0
  rw [CoordinateHom.fiberMap_comp, CoordinateHom.fiberMap_id, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, h0', map_zero] at h1
  exact h1.symm

/-- Mutually inverse `C^n` cocycle morphisms between rank-one `C^n` cores preserve the existence of
a global compatible `C^n` trivialization. -/
theorem exists_trivialization_baseSet_eq_univ_iff_of_inv
    (hF : finrank 𝕜 F = 1) (hG : finrank 𝕜 G = 1)
    (a : CoordinateHom Z W) (b : CoordinateHom W Z)
    (hba : b.comp a = CoordinateHom.id Z) (hab : a.comp b = CoordinateHom.id W)
    (ha : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n a.totalSpaceMap)
    (hb : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, F)) n b.totalSpaceMap) :
    (∃ (e : Trivialization F (π F Z.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B F I n).maximalAtlas (TotalSpace F Z.Fiber) ∧
          e.baseSet = univ) ↔
      ∃ (e : Trivialization G (π G W.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B G I n).maximalAtlas (TotalSpace G W.Fiber) ∧
          e.baseSet = univ :=
  ⟨exists_section_ne_zero_of_left_inv hF hG a b hba ha,
    exists_section_ne_zero_of_left_inv hG hF b a hab hb⟩

end VectorBundleCore.CoordinateHom

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The point-indexed rank-one presentation of a `C^n` scalar line-bundle core is `C^n`. -/
instance isContMDiff_ofScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    (ofScalarCore Z).core.IsContMDiff I n where
  contMDiffOn_coordChange x y := by
    dsimp +instances only [ofScalarCore]
    exact (contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm
      |>.toContinuousLinearMap)).clm_comp
      ((Z.contMDiffOn_coordChange I (Z.indexAt x) (Z.indexAt y)).clm_comp
        (contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)
          |>.toContinuousLinearMap)))

/-- The forward comparison `toScalarCore Z` is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_toScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofScalarCore Z).rank → 𝕜)) (I.prod 𝓘(𝕜)) n
      (toScalarCore Z).totalSpaceMap := by
  refine (toScalarCore Z).contMDiff_totalSpaceMap fun x j ↦ ?_
  have hin := fun z ↦ inChartCoordinates_toScalarCore Z x j (z := z)
  dsimp +instances only [ofScalarCore] at hin ⊢
  exact ((Z.contMDiffOn_coordChange I (Z.indexAt x) j).clm_comp
    (contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)
      |>.toContinuousLinearMap))).congr fun z hz ↦ hin z hz.1 hz.2

/-- The inverse comparison `fromScalarCore Z` is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_fromScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    ContMDiff (I.prod 𝓘(𝕜)) (I.prod 𝓘(𝕜, Fin (ofScalarCore Z).rank → 𝕜)) n
      (fromScalarCore Z).totalSpaceMap := by
  refine (fromScalarCore Z).contMDiff_totalSpaceMap fun i y ↦ ?_
  have hin := fun z ↦ inChartCoordinates_fromScalarCore Z i y (z := z)
  dsimp +instances only [ofScalarCore] at hin ⊢
  exact ((contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm
    |>.toContinuousLinearMap)).clm_comp
    (Z.contMDiffOn_coordChange I i (Z.indexAt y))).congr fun z hz ↦ hin z hz.1 hz.2

/-- The `C^n` bundle equivalence identifying `(ofScalarCore Z).core` with `Z` over the identity
of `B`, without completeness assumptions on `𝕜`. -/
noncomputable def ofScalarCoreDiffeomorph (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    (ofScalarCore Z).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofScalarCore Z).rank → 𝕜),
      I.prod 𝓘(𝕜)⟯ Z.TotalSpace :=
  (toScalarCore Z).toDiffeomorphOfInv (fromScalarCore Z)
    (fromScalarCore_comp_toScalarCore Z) (toScalarCore_comp_fromScalarCore Z)
    (contMDiff_totalSpaceMap_toScalarCore Z) (contMDiff_totalSpaceMap_fromScalarCore Z)

@[simp]
theorem coe_ofScalarCoreDiffeomorph (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    ⇑(ofScalarCoreDiffeomorph (I := I) (n := n) Z) = (toScalarCore Z).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp]
theorem coe_ofScalarCoreDiffeomorph_symm (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    ⇑(ofScalarCoreDiffeomorph (I := I) (n := n) Z).symm = (fromScalarCore Z).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

@[simp]
theorem ofScalarCoreDiffeomorph_toHomeomorph (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    (ofScalarCoreDiffeomorph (I := I) (n := n) Z).toHomeomorph = ofScalarCoreHomeomorph Z := by
  apply Homeomorph.ext
  intro p
  change ⇑(ofScalarCoreDiffeomorph (I := I) (n := n) Z) p = ⇑(ofScalarCoreHomeomorph Z) p
  rw [coe_ofScalarCoreDiffeomorph, coe_ofScalarCoreHomeomorph]

/-- The point-indexed rank-one presentation `ofScalarCore Z` admits a global compatible `C^n`
trivialization if and only if `Z` does. -/
theorem exists_trivialization_baseSet_eq_univ_ofScalarCore_iff [CompleteSpace 𝕜]
    (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n] :
    (∃ (e : Trivialization (Fin (ofScalarCore Z).rank → 𝕜) (π _ (ofScalarCore Z).core.Fiber))
        (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B (Fin (ofScalarCore Z).rank → 𝕜) I n).maximalAtlas
            (TotalSpace _ (ofScalarCore Z).core.Fiber) ∧
          e.baseSet = univ) ↔
      ∃ (e : Trivialization 𝕜 (π 𝕜 Z.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B 𝕜 I n).maximalAtlas (TotalSpace 𝕜 Z.Fiber) ∧
          e.baseSet = univ :=
  CoordinateHom.exists_trivialization_baseSet_eq_univ_iff_of_inv
    (by simp) (finrank_self 𝕜) (toScalarCore Z) (fromScalarCore Z)
    (fromScalarCore_comp_toScalarCore Z) (toScalarCore_comp_fromScalarCore Z)
    (contMDiff_totalSpaceMap_toScalarCore Z) (contMDiff_totalSpaceMap_fromScalarCore Z)

/-! ### Smooth triviality of cores with identity transitions -/

/-- A point-indexed finite-rank core whose transition maps are identities on chart overlaps is
`C^n` for every model and every regularity. -/
theorem isContMDiff_of_coordChange_eq_id (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    A.core.IsContMDiff I n where
  contMDiffOn_coordChange i j :=
    (contMDiffOn_const (c := ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))).congr fun x hx ↦
      h i j x hx.1 hx.2

/-- The forward isomorphism `isoTrivialOfCoordChangeEqId A h` has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_isoTrivialOfCoordChangeEqId_hom
    (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin (trivial 𝕜 B A.rank).rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates (trivial 𝕜 B A.rank).core i j x
        ((isoTrivialOfCoordChangeEqId A h).hom.fiberMap x))
      (A.core.baseSet i ∩ (trivial 𝕜 B A.rank).core.baseSet j) := by
  have hin := fun x ↦ inChartCoordinates_isoTrivialOfCoordChangeEqId_hom A h i j (x := x)
  dsimp +instances only [trivial] at hin ⊢
  exact (contMDiffOn_const (c := ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))).congr fun x hx ↦
    hin x hx.1

/-- The inverse isomorphism `isoTrivialOfCoordChangeEqId A h` has `C^n` chart operators. -/
theorem contMDiffOn_inChartCoordinates_isoTrivialOfCoordChangeEqId_inv
    (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin (trivial 𝕜 B A.rank).rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) n
      (fun x ↦ (trivial 𝕜 B A.rank).core.inChartCoordinates A.core i j x
        ((isoTrivialOfCoordChangeEqId A h).inv.fiberMap x))
      ((trivial 𝕜 B A.rank).core.baseSet i ∩ A.core.baseSet j) := by
  have hin := fun x ↦ inChartCoordinates_isoTrivialOfCoordChangeEqId_inv A h i j (x := x)
  dsimp +instances only [trivial] at hin ⊢
  exact (contMDiffOn_const (c := ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))).congr fun x hx ↦
    hin x hx.2

/-- The forward isomorphism `isoTrivialOfCoordChangeEqId A h` glues to a `C^n` map on total
spaces. -/
theorem contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_hom (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (trivial 𝕜 B A.rank).rank → 𝕜)) n
      (isoTrivialOfCoordChangeEqId A h).hom.totalSpaceMap :=
  have := isContMDiff_of_coordChange_eq_id (I := I) (n := n) A h
  (isoTrivialOfCoordChangeEqId A h).hom.contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_isoTrivialOfCoordChangeEqId_hom A h)

/-- The inverse isomorphism `isoTrivialOfCoordChangeEqId A h` glues to a `C^n` map on total
spaces. -/
theorem contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_inv (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (trivial 𝕜 B A.rank).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      (isoTrivialOfCoordChangeEqId A h).inv.totalSpaceMap :=
  have := isContMDiff_of_coordChange_eq_id (I := I) (n := n) A h
  (isoTrivialOfCoordChangeEqId A h).inv.contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_isoTrivialOfCoordChangeEqId_inv A h)

/-- A point-indexed finite-rank core whose transition maps are identities on chart overlaps is
`C^n` bundle-equivalent to `trivial 𝕜 B A.rank`, without completeness assumptions on `𝕜`. -/
noncomputable def diffeomorphTrivialOfCoordChangeEqId (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (trivial 𝕜 B A.rank).rank → 𝕜)⟯ (trivial 𝕜 B A.rank).core.TotalSpace :=
  (isoTrivialOfCoordChangeEqId A h).hom.toDiffeomorphOfInv
    (isoTrivialOfCoordChangeEqId A h).inv
    (isoTrivialOfCoordChangeEqId A h).hom_inv_id
    (isoTrivialOfCoordChangeEqId A h).inv_hom_id
    (contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_hom A h)
    (contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_inv A h)

@[simp]
theorem coe_diffeomorphTrivialOfCoordChangeEqId (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ⇑(diffeomorphTrivialOfCoordChangeEqId (I := I) (n := n) A h) =
      (isoTrivialOfCoordChangeEqId A h).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp]
theorem coe_diffeomorphTrivialOfCoordChangeEqId_symm (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ⇑(diffeomorphTrivialOfCoordChangeEqId (I := I) (n := n) A h).symm =
      (isoTrivialOfCoordChangeEqId A h).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

end TauCeti.FiniteRankBundleCore
