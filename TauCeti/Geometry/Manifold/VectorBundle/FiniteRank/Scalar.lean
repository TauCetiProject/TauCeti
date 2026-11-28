/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom

/-!
# Smooth and holomorphic rank-one presentation of scalar line-bundle cores

For any `C^n` scalar line-bundle core `Z : VectorBundleCore 𝕜 B 𝕜 ι`, its point-indexed rank-one
presentation `FiniteRankBundleCore.ofScalarCore Z` is `C^n`, and the topological comparison
`ofScalarCoreHomeomorph Z` refines to a `C^n` bundle equivalence `ofScalarCoreDiffeomorph Z` over
the identity of `B` without completeness assumptions on `𝕜`. Over a complex manifold at regularity
`∞`, this identifies holomorphic line bundles presented by scalar transition cocycles with
holomorphic rank-one cores in `FiniteRankBundleCore ℂ B`.

Over a complete scalar field, `exists_trivialization_baseSet_eq_univ_ofScalarCore_iff` records
that `ofScalarCore Z` admits a global compatible `C^n` trivialization if and only if `Z` does.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

section ScalarCore

variable (Z : VectorBundleCore 𝕜 B 𝕜 ι) [Z.IsContMDiff I n]

/-- The point-indexed rank-one presentation of a `C^n` scalar line-bundle core is `C^n`. -/
instance isContMDiff_ofScalarCore : (ofScalarCore Z).core.IsContMDiff I n where
  contMDiffOn_coordChange x y := by
    rw [baseSet_ofScalarCore, baseSet_ofScalarCore]
    refine ((contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm
      |>.toContinuousLinearMap)).clm_comp
      ((Z.contMDiffOn_coordChange I (Z.indexAt x) (Z.indexAt y)).clm_comp
        (contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)
          |>.toContinuousLinearMap)))).congr fun z _ ↦
      (coordChange_ofScalarCore Z x y z)

/-- The forward comparison `toScalarCore Z` is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_toScalarCore :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofScalarCore Z).rank → 𝕜)) (I.prod 𝓘(𝕜)) n
      (toScalarCore Z).totalSpaceMap := by
  refine (toScalarCore Z).contMDiff_totalSpaceMap fun x j ↦ ?_
  have hin := fun z ↦ inChartCoordinates_toScalarCore Z x j (z := z)
  rw [baseSet_ofScalarCore] at hin ⊢
  -- Unfold only the rank-one wrapper so `Fin (ofScalarCore Z).rank → 𝕜` reduces to `Fin 1 → 𝕜`.
  dsimp +instances only [ofScalarCore] at hin ⊢
  exact ((Z.contMDiffOn_coordChange I (Z.indexAt x) j).clm_comp
    (contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)
      |>.toContinuousLinearMap))).congr fun z hz ↦ hin z hz.1 hz.2

/-- The inverse comparison `fromScalarCore Z` is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_fromScalarCore :
    ContMDiff (I.prod 𝓘(𝕜)) (I.prod 𝓘(𝕜, Fin (ofScalarCore Z).rank → 𝕜)) n
      (fromScalarCore Z).totalSpaceMap := by
  refine (fromScalarCore Z).contMDiff_totalSpaceMap fun i y ↦ ?_
  have hin := fun z ↦ inChartCoordinates_fromScalarCore Z i y (z := z)
  rw [baseSet_ofScalarCore] at hin ⊢
  -- Unfold only the rank-one wrapper so `Fin (ofScalarCore Z).rank → 𝕜` reduces to `Fin 1 → 𝕜`.
  dsimp +instances only [ofScalarCore] at hin ⊢
  exact ((contMDiffOn_const (c := (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm
    |>.toContinuousLinearMap)).clm_comp
    (Z.contMDiffOn_coordChange I i (Z.indexAt y))).congr fun z hz ↦ hin z hz.1 hz.2

/-- The `C^n` bundle equivalence identifying `(ofScalarCore Z).core` with `Z` over the identity
of `B`, without completeness assumptions on `𝕜`. -/
noncomputable def ofScalarCoreDiffeomorph :
    (ofScalarCore Z).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofScalarCore Z).rank → 𝕜),
      I.prod 𝓘(𝕜)⟯ Z.TotalSpace :=
  (toScalarCore Z).toDiffeomorphOfInv (fromScalarCore Z)
    (fromScalarCore_comp_toScalarCore Z) (toScalarCore_comp_fromScalarCore Z)
    (contMDiff_totalSpaceMap_toScalarCore Z) (contMDiff_totalSpaceMap_fromScalarCore Z)

@[simp] theorem coe_ofScalarCoreDiffeomorph :
    ⇑(ofScalarCoreDiffeomorph (I := I) (n := n) Z) = (toScalarCore Z).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp] theorem coe_ofScalarCoreDiffeomorph_symm :
    ⇑(ofScalarCoreDiffeomorph (I := I) (n := n) Z).symm = (fromScalarCore Z).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

@[simp] theorem ofScalarCoreDiffeomorph_toHomeomorph :
    (ofScalarCoreDiffeomorph (I := I) (n := n) Z).toHomeomorph = ofScalarCoreHomeomorph Z :=
  DFunLike.coe_injective <| by
    rw [Diffeomorph.coe_toHomeomorph, coe_ofScalarCoreDiffeomorph, coe_ofScalarCoreHomeomorph]

/-- The point-indexed rank-one presentation `ofScalarCore Z` admits a global compatible `C^n`
trivialization if and only if `Z` does. -/
theorem exists_trivialization_baseSet_eq_univ_ofScalarCore_iff [CompleteSpace 𝕜] :
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

end ScalarCore

end TauCeti.FiniteRankBundleCore
