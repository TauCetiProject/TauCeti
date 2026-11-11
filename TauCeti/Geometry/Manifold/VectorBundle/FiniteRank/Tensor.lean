/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import TauCeti.Geometry.Manifold.ContMDiff.Kronecker
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom

/-!
# Smooth and holomorphic tensor-product cores

The tensor product of two finite-rank `C^n` bundle cores is `C^n`, on the existing
`FiniteRankBundleCore.tensor` carrier. Its transitions are Kronecker products of the original
transitions in the fixed coordinates `Fin (a * b) → 𝕜`, indexed by `finProdFinEquiv`.
In particular, over a complex manifold at regularity `∞`, this gives the holomorphic tensor
product without changing the underlying continuous bundle.

Tensor products of bundle maps also preserve regularity, both in chart operators and on total
spaces. The chart-operator statement needs no completeness; the total-space statement uses the
finite-dimensional criterion for recovering smooth chart operators from smooth bundle maps.
Identity and composition laws are those of the existing `tensorHom` bifunctor.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Set VectorBundleCore CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- Tensor products of finite-rank `C^n` cores are `C^n`. For complex scalars and `n = ∞`,
this equips the shared tensor core with its holomorphic structure. -/
instance isContMDiff_tensor (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] :
    (tensor A D).core.IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_tensor]
    exact ((A.core.contMDiffOn_coordChange (n := n) I i j).mono
      (inter_subset_inter inter_subset_left inter_subset_left)).clm_kronecker
        ((D.core.contMDiffOn_coordChange (n := n) I i j).mono
          (inter_subset_inter inter_subset_right inter_subset_right))

variable {A A' D D' : FiniteRankBundleCore 𝕜 B}

/-- Tensoring bundle maps whose chart operators are `C^n` gives `C^n` chart operators on
all tensor chart intersections. Neither regularity of the cores nor completeness is needed. -/
theorem contMDiffOn_inChartCoordinates_tensorHom (f : A ⟶ A') (g : D ⟶ D')
    (hf : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x))
      (A.core.baseSet i ∩ A'.core.baseSet j))
    (hg : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) n
      (fun x ↦ D.core.inChartCoordinates D'.core i j x (g.fiberMap x))
      (D.core.baseSet i ∩ D'.core.baseSet j)) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin (tensor A D).rank → 𝕜) →L[𝕜] (Fin (tensor A' D').rank → 𝕜)) n
      (fun x ↦ (tensor A D).core.inChartCoordinates (tensor A' D').core i j x
        ((tensorHom f g).fiberMap x))
      ((tensor A D).core.baseSet i ∩ (tensor A' D').core.baseSet j) := by
  simp only [fiberMap_tensorHom, inChartCoordinates_tensor_kronecker,
    VectorBundleCore.baseSet_at, localTriv_baseSet_tensor]
  exact ((hf i j).mono (inter_subset_inter inter_subset_left inter_subset_left)).clm_kronecker
    ((hg i j).mono (inter_subset_inter inter_subset_right inter_subset_right))

/-- Tensor products of `C^n` bundle maps between finite-rank `C^n` cores are `C^n` on total
spaces. In particular, tensor products of holomorphic bundle maps are holomorphic. -/
theorem contMDiff_totalSpaceMap_tensorHom [CompleteSpace 𝕜]
    [A.core.IsContMDiff I n] [A'.core.IsContMDiff I n]
    [D.core.IsContMDiff I n] [D'.core.IsContMDiff I n]
    (f : A ⟶ A') (g : D ⟶ D')
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      f.totalSpaceMap)
    (hg : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      g.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (tensor A D).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (tensor A' D').rank → 𝕜)) n (tensorHom f g).totalSpaceMap :=
  (tensorHom f g).contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_tensorHom f g
      (f.contMDiff_totalSpaceMap_iff.mp hf) (g.contMDiff_totalSpaceMap_iff.mp hg))

end TauCeti.FiniteRankBundleCore
