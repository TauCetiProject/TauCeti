/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom

/-!
# Smooth constant intertwining maps of finite-rank bundle cores

A fixed linear operator intertwining the transitions of two cores defines a bundle map
`FiniteRankBundleCore.constHom`. For smooth cores this map is smooth: in fixed charts it is
the target transition followed by the fixed operator. A fixed intertwining linear equivalence
therefore gives a diffeomorphism, with no completeness assumption on the field.

These comparisons let coordinate identifications, such as the associator and symmetry of tensor
products, act as smooth (and over the complex field, holomorphic) bundle equivalences.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The trivial finite-rank core is smooth at every regularity. -/
instance isContMDiff_trivial (r : ℕ) : (trivial 𝕜 B r).core.IsContMDiff I n where
  contMDiffOn_coordChange _ _ := contMDiffOn_const

variable {A D : FiniteRankBundleCore 𝕜 B}
  [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]

/-- A constant operator intertwining the transitions of smooth cores defines a smooth map
of total spaces. The source chart domains need only lie in the corresponding target domains. -/
theorem contMDiff_totalSpaceMap_constHom
    (hbase : ∀ i, A.core.baseSet i ⊆ D.core.baseSet i)
    (T : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hT : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      T.comp (A.core.coordChange i j x) = (D.core.coordChange i j x).comp T) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      (constHom hbase T hT).totalSpaceMap := by
  apply CoordinateHom.contMDiff_totalSpaceMap
  intro i j
  refine (((D.core.contMDiffOn_coordChange I i j).mono
    (fun x (hx : x ∈ A.core.baseSet i ∩ D.core.baseSet j) ↦
      ⟨hbase i hx.1, hx.2⟩)).clm_comp (contMDiffOn_const (c := T))).congr ?_
  intro x hx
  rw [← CoordinateHom.operator_eq (constHom hbase T hT) i j ⟨x, hx⟩]
  rw [operator_constHom]
  rfl

/-- A fixed continuous linear equivalence intertwining smooth transition functions induces a
smooth bundle equivalence over the identity, using the existing core total spaces. -/
noncomputable def constIsoDiffeomorph
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯ D.core.TotalSpace where
  toFun := (constIso hbase e he).hom.totalSpaceMap
  invFun := (constIso hbase e he).inv.totalSpaceMap
  left_inv := fun ⟨x, v⟩ ↦ by
    simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom, fiberMap_constIso_inv]
    exact congrArg (fun w : Fin A.rank → 𝕜 ↦ (⟨x, w⟩ : A.core.TotalSpace))
      (e.symm_apply_apply v)
  right_inv := fun ⟨x, v⟩ ↦ by
    simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom, fiberMap_constIso_inv]
    exact congrArg (fun w : Fin D.rank → 𝕜 ↦ (⟨x, w⟩ : D.core.TotalSpace))
      (e.apply_symm_apply v)
  contMDiff_toFun :=
    (contMDiff_totalSpaceMap_constHom (I := I) (n := n) (fun i ↦ (hbase i).le)
      e.toContinuousLinearMap he).congr fun p ↦ by
        simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constHom, fiberMap_constIso_hom]
        rfl
  contMDiff_invFun :=
    (contMDiff_totalSpaceMap_constHom (I := I) (n := n) (fun i ↦ (hbase i).ge)
      e.symm.toContinuousLinearMap (coordChange_intertwines_symm hbase e he)).congr fun p ↦ by
        simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constHom, fiberMap_constIso_inv]
        rfl

/-- The smooth comparison is the original constant core isomorphism on total spaces. -/
@[simp]
theorem coe_constIsoDiffeomorph
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    ⇑(constIsoDiffeomorph (I := I) (n := n) hbase e he) =
      (constIso hbase e he).hom.totalSpaceMap := (rfl)

/-- The inverse smooth comparison is the inverse of the original core isomorphism. -/
@[simp]
theorem coe_constIsoDiffeomorph_symm
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    ⇑(constIsoDiffeomorph (I := I) (n := n) hbase e he).symm =
      (constIso hbase e he).inv.totalSpaceMap := (rfl)

end TauCeti.FiniteRankBundleCore
