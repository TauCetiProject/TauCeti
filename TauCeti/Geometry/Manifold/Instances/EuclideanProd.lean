/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# Euclidean charts on products

Mathlib charts a product `M × N` of spaces charted on `H` and `H'` on the type synonym
`ModelProd H H'`. For spaces charted on Euclidean spaces this file reads those product charts on a
single Euclidean space: `TauCeti.prodEuclideanChartedSpace` charts `M × N` on
`EuclideanSpace 𝕜 (Fin (n + m))` when `M` and `N` are charted on `EuclideanSpace 𝕜 (Fin n)` and
`EuclideanSpace 𝕜 (Fin m)`, by following the product charts with
`EuclideanSpace.finAddEquivProd.symm` through `Homeomorph.chartedSpaceComp`.
`TauCeti.prodEuclideanChartedSpace_chartAt` and `TauCeti.prodEuclideanChartedSpace_extChartAt`
describe its charts and extended charts.

When `M` and `N` are `C^r` manifolds, these composite charts make `M × N` a `C^r` manifold
modelled on `EuclideanSpace 𝕜 (Fin (n + m))` (`TauCeti.isManifold_prodEuclideanChartedSpace`), and
the identity map is a `C^r` diffeomorphism between `TauCeti.prodEuclideanChartedSpace` and the
native product charted space (`TauCeti.prodEuclideanDiffeomorph`).

`TauCeti.prodEuclideanChartedSpace` is a definition rather than an instance, so that the Euclidean
model can be chosen explicitly alongside Mathlib's product model.
-/

public section

open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) M] [ChartedSpace (EuclideanSpace 𝕜 (Fin m)) N]

/-- The product `M × N` of spaces charted on `𝕜ⁿ` and `𝕜ᵐ`, charted on `𝕜ⁿ⁺ᵐ`: the product of
charts of `M` and `N`, followed by the identification `EuclideanSpace.finAddEquivProd` of
`𝕜ⁿ × 𝕜ᵐ` with `𝕜ⁿ⁺ᵐ`. -/
@[instance_reducible]
noncomputable def prodEuclideanChartedSpace :
    ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m))) (M × N) :=
  Homeomorph.chartedSpaceComp (H := ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m)))
    (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph (M × N)

/-- The chart of `TauCeti.prodEuclideanChartedSpace` at `x` is the product of the charts of the
factors at `x.1` and `x.2`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
@[simp, mfld_simps]
theorem prodEuclideanChartedSpace_chartAt (x : M × N) :
    @chartAt _ _ _ _ (prodEuclideanChartedSpace (𝕜 := 𝕜)) x =
      ((chartAt (EuclideanSpace 𝕜 (Fin n)) x.1).prod (chartAt (EuclideanSpace 𝕜 (Fin m)) x.2)).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph :=
  Homeomorph.chartAt_chartedSpaceComp
    (H := ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) _ x

/-- The extended chart of `TauCeti.prodEuclideanChartedSpace` at `x` is the product extended chart
at `x`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
theorem prodEuclideanChartedSpace_extChartAt (x : M × N) :
    (letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
     extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) x) =
      (extChartAt (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) x).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toEquiv.toPartialEquiv := by
  let := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  rw [extChartAt, prodEuclideanChartedSpace_chartAt]
  refine PartialEquiv.ext (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  simp

/-- The identification `EuclideanSpace.finAddEquivProd.symm` of the product model `𝕜ⁿ × 𝕜ᵐ` with
`𝕜ⁿ⁺ᵐ`, as a `C^r` diffeomorphism of models. -/
private noncomputable def finAddEquivProdSymmDiffeomorph (r : ℕ∞ω) :
    ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))
      ≃ₘ^r⟮𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)),
        𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m)))⟯
      EuclideanSpace 𝕜 (Fin (n + m)) where
  toEquiv := (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod]
    exact (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod]
    exact (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).contDiff.contMDiff

/-- When `M` and `N` are `C^r` manifolds modelled on `𝕜ⁿ` and `𝕜ᵐ`,
`TauCeti.prodEuclideanChartedSpace` makes `M × N` a `C^r` manifold modelled on `𝕜ⁿ⁺ᵐ`. -/
theorem isManifold_prodEuclideanChartedSpace (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) r M]
    [IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) r N] :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) r (M × N) :=
  (finAddEquivProdSymmDiffeomorph r).isManifold_chartedSpaceComp (M × N)

/-- The identity map of `M × N` as a `C^r` diffeomorphism between
`TauCeti.prodEuclideanChartedSpace` (modelled on `𝕜ⁿ⁺ᵐ`) and the product charted space (modelled
on `𝕜ⁿ × 𝕜ᵐ`). -/
noncomputable def prodEuclideanDiffeomorph (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    (M × N) ≃ₘ^r⟮𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))),
      𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))⟯ (M × N) :=
  (finAddEquivProdSymmDiffeomorph r).chartedSpaceCompDiffeomorph (M × N)

@[simp]
theorem coe_prodEuclideanDiffeomorph (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ⇑(prodEuclideanDiffeomorph (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N) r) = id :=
  (finAddEquivProdSymmDiffeomorph r).coe_chartedSpaceCompDiffeomorph (M × N)

@[simp]
theorem coe_prodEuclideanDiffeomorph_symm (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ⇑(prodEuclideanDiffeomorph (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N) r).symm = id :=
  (finAddEquivProdSymmDiffeomorph r).coe_chartedSpaceCompDiffeomorph_symm (M × N)

end TauCeti
