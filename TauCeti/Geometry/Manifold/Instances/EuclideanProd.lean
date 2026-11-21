/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# Euclidean charts on products

Mathlib charts a product `M × N` of spaces charted on `H` and `H'` on the type synonym
`ModelProd H H'`. For spaces charted on Euclidean spaces this file reads those product charts on a
single Euclidean space: `TauCeti.prodEuclideanChartedSpace` charts `M × N` on
`EuclideanSpace 𝕜 (Fin (n + m))` when `M` and `N` are charted on `EuclideanSpace 𝕜 (Fin n)` and
`EuclideanSpace 𝕜 (Fin m)`, by composing the product charts with
`EuclideanSpace.finAddEquivProd`. `TauCeti.prodEuclideanChartedSpace_chartAt` and
`TauCeti.prodEuclideanChartedSpace_extChartAt` describe its charts and extended charts.

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
  letI : ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m)))
      (ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph
      |>.singletonChartedSpace (by simp)
  ChartedSpace.comp _ (ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) _

/-- The chart of `TauCeti.prodEuclideanChartedSpace` at `x` is the product of the charts of the
factors at `x.1` and `x.2`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
@[simp, mfld_simps]
theorem prodEuclideanChartedSpace_chartAt (x : M × N) :
    @chartAt _ _ _ _ (prodEuclideanChartedSpace (𝕜 := 𝕜)) x =
      ((chartAt (EuclideanSpace 𝕜 (Fin n)) x.1).prod (chartAt (EuclideanSpace 𝕜 (Fin m)) x.2)).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph :=
  (rfl)

/-- The extended chart of `TauCeti.prodEuclideanChartedSpace` at `x` is the product extended chart
at `x`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
theorem prodEuclideanChartedSpace_extChartAt (x : M × N) :
    (letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
     extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) x) =
      (extChartAt (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) x).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toEquiv.toPartialEquiv := by
  let := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  refine PartialEquiv.ext (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  simp

/-- When `M` and `N` are `C^r` manifolds modelled on `𝕜ⁿ` and `𝕜ᵐ`,
`TauCeti.prodEuclideanChartedSpace` makes `M × N` a `C^r` manifold modelled on `𝕜ⁿ⁺ᵐ`. -/
theorem isManifold_prodEuclideanChartedSpace (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) r M]
    [IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) r N] :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) r (M × N) := by
  let Φ : ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))
      ≃ₘ^r⟮𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)),
        𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m)))⟯
      EuclideanSpace 𝕜 (Fin (n + m)) :=
    { toEquiv := (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod]
        exact (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.contDiff.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod]
        exact (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).contDiff.contMDiff }
  exact Φ.isManifold_chartedSpaceComp (M × N)

/-- The identity map of `M × N` is `C^r` from `TauCeti.prodEuclideanChartedSpace` to the product
charted space. -/
private theorem contMDiff_id_prodEuclidean (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ContMDiff 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m)))
      (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) r
      (id : M × N → M × N) := by
  let := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  intro x
  refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
  refine (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).contDiff.contDiffWithinAt.congr_of_mem
    (fun z hz ↦ ?_) ?_
  · rw [Set.mem_inter_iff, prodEuclideanChartedSpace_extChartAt, PartialEquiv.trans_target] at hz
    simp only [Function.comp_apply, id_eq, prodEuclideanChartedSpace_extChartAt,
      PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.coe_trans]
    exact (extChartAt _ x).right_inv hz.1.2
  · refine ⟨(extChartAt _ x).map_source (mem_extChartAt_source x), trivial, ?_⟩
    rw [Set.mem_preimage, id_eq, (extChartAt _ x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source x

/-- The identity map of `M × N` is `C^r` from the product charted space to
`TauCeti.prodEuclideanChartedSpace`. -/
private theorem contMDiff_id_prodEuclidean_symm (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ContMDiff (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)))
      𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) r (id : M × N → M × N) := by
  let := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  intro x
  refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
  refine (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.contDiff.contDiffWithinAt.congr_of_mem
    (fun z hz ↦ ?_) ?_
  · simp only [Function.comp_apply, id_eq, prodEuclideanChartedSpace_extChartAt,
      PartialEquiv.coe_trans, (extChartAt _ x).right_inv hz.1]
    rfl
  · refine ⟨(extChartAt _ x).map_source (mem_extChartAt_source x), trivial, ?_⟩
    rw [Set.mem_preimage, id_eq, (extChartAt _ x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source x

/-- The identity map of `M × N` as a `C^r` diffeomorphism between
`TauCeti.prodEuclideanChartedSpace` (modelled on `𝕜ⁿ⁺ᵐ`) and the product charted space (modelled
on `𝕜ⁿ × 𝕜ᵐ`). -/
noncomputable def prodEuclideanDiffeomorph (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    (M × N) ≃ₘ^r⟮𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))),
      𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))⟯ (M × N) :=
  letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  { toEquiv := Equiv.refl _
    contMDiff_toFun := contMDiff_id_prodEuclidean r
    contMDiff_invFun := contMDiff_id_prodEuclidean_symm r }

@[simp]
theorem coe_prodEuclideanDiffeomorph (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ⇑(prodEuclideanDiffeomorph (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N) r) = id :=
  (rfl)

@[simp]
theorem coe_prodEuclideanDiffeomorph_symm (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ⇑(prodEuclideanDiffeomorph (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N) r).symm = id :=
  (rfl)

end TauCeti
