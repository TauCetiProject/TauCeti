/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Graph
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Hom
import TauCeti.LinearAlgebra.Prod

/-!
# Graph connections on products of vector spaces

Regard a product `E × F` of normed spaces as the trivial family over `E` with fibre `F`, through
the first projection. A family `A : E × F → (E →L[𝕜] F)` of linear maps defines the graph
distribution `p ↦ {(v, A p v) | v : E}` (`TauCeti.graphDistribution`). It is a complement of the
vertical space `0 × F` at every point, so for a `C^n` family `A` it is a `C^n` Ehresmann
connection on the first projection (`TauCeti.isEhresmannConnection_graphDistribution`), and its
horizontal lift of `v` at `p` is `(v, A p v)` (`TauCeti.horizontalLift_graphDistribution`). A
tangent vector `w` at `p` is horizontal exactly when `w.2 = A p w.1`, so a curve `t ↦ (γ t, y t)`
is horizontal exactly when `y' = A (γ, y) γ'`: this is the coordinate form `dy = A (x, y) dx` of a
connection on a fibred manifold.

The family `A = 0` gives the **product connection**, with horizontal spaces `E × 0`: its
horizontal lifts keep the fibre coordinate fixed. Products `(b, y) ↦ (g b, ψ y)` of differentiable
maps are morphisms of product connections covering `g`
(`TauCeti.isEhresmannConnectionHom_prodMap_graphDistribution_zero`).

## Main results

* `TauCeti.isEhresmannConnection_graphDistribution`: a `C^n` graph distribution is a `C^n`
  Ehresmann connection on the first projection `E × F → E`.
* `TauCeti.horizontalLift_graphDistribution`: its horizontal lift of `v` at `p` is `(v, A p v)`.
* `TauCeti.isEhresmannConnectionHom_prodMap_graphDistribution_zero`: product maps are morphisms
  of product connections.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.3 (the local form `dy = A (x, y) dx` of a connection on a fibred manifold).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the first projection `E × F → E`, read on the model spaces. -/
private theorem mfderiv_fst_eq (p : E × F) :
    mfderiv 𝓘(𝕜, E × F) 𝓘(𝕜, E) Prod.fst p = ContinuousLinearMap.fst 𝕜 E F :=
  (ContinuousLinearMap.fst 𝕜 E F).mfderiv_eq

/-- **Graph connections.** For a `C^n` family `A : E × F → (E →L[𝕜] F)` with `E`
finite-dimensional, the graph distribution `p ↦ {(v, A p v) | v : E}` is a `C^n` Ehresmann
connection on the first projection `E × F → E`. -/
theorem isEhresmannConnection_graphDistribution [FiniteDimensional 𝕜 E] {n : ℕ∞ω}
    {A : E × F → E →L[𝕜] F} (hA : ContDiff 𝕜 n A) :
    IsEhresmannConnection 𝓘(𝕜, E × F) 𝓘(𝕜, E) n Prod.fst (graphDistribution A) where
  mdifferentiable := (ContinuousLinearMap.fst 𝕜 E F).mdifferentiable
  isCompl_ker p := by
    rw [mfderiv_fst_eq, graphDistribution_def]
    exact LinearMap.isCompl_graph_ker_fst _
  surjective_mfderiv p := by
    rw [mfderiv_fst_eq]
    exact Prod.fst_surjective
  isContMDiffDistribution := isContMDiffDistribution_graphDistribution hA

/-- The horizontal lift of the graph connection of `A` sends `v` at `p` to `(v, A p v)`. -/
@[simp]
theorem horizontalLift_graphDistribution [FiniteDimensional 𝕜 E] {n : ℕ∞ω}
    {A : E × F → E →L[𝕜] F} (hA : ContDiff 𝕜 n A) (p : E × F) (v : E) :
    ((isEhresmannConnection_graphDistribution hA).horizontalLift p v :
      TangentSpace 𝓘(𝕜, E × F) p) = (v, A p v) := by
  refine (congrArg Subtype.val ((isEhresmannConnection_graphDistribution hA).eq_horizontalLift_iff
    (w := ⟨(v, A p v), mem_graphDistribution.2 rfl⟩) |>.2 ?_)).symm
  rw [mfderiv_fst_eq]
  -- `rfl` rather than `simp`: the goal applies `ContinuousLinearMap.fst 𝕜 E F` to a vector of
  -- `TangentSpace 𝓘(𝕜, E × F) p`, which is `E × F` only up to unfolding, so `coe_fst'` does not
  -- rewrite. The goal is the first projection of the pair `(v, A p v)`.
  rfl

/-- **Morphisms of product connections.** For differentiable maps `g : E → E'` and
`ψ : F → F'`, the product map `(b, y) ↦ (g b, ψ y)` covering `g` is a morphism from the product
connection on `E × F → E` to the product connection on `E' × F' → E'`. -/
theorem isEhresmannConnectionHom_prodMap_graphDistribution_zero
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {g : E → E'} {ψ : F → F'} (hg : Differentiable 𝕜 g) (hψ : Differentiable 𝕜 ψ) :
    IsEhresmannConnectionHom 𝓘(𝕜, E × F) 𝓘(𝕜, E) 𝓘(𝕜, E' × F') 𝓘(𝕜, E') Prod.fst
      (graphDistribution 0) Prod.fst (graphDistribution 0) (Prod.map g ψ) g := by
  have hd (p : E × F) :
      HasFDerivAt (Prod.map g ψ) ((fderiv 𝕜 g p.1).prodMap (fderiv 𝕜 ψ p.2)) p :=
    (hg p.1).hasFDerivAt.prodMap p (hψ p.2).hasFDerivAt
  refine ⟨Differentiable.mdifferentiable fun p ↦ (hd p).differentiableAt, hg.mdifferentiable, rfl,
    fun p v hv ↦ ?_⟩
  rw [(hd p).hasMFDerivAt.mfderiv]
  refine mem_graphDistribution.2 ?_
  have hv' : v.2 = 0 := by simpa using mem_graphDistribution.1 hv
  -- The second component of `dg.prodMap dψ v` is `dψ v.2`. The vector `v` lives in a tangent space,
  -- so `ContinuousLinearMap.coe_prodMap'` does not rewrite and we unfold it with `change`.
  change fderiv 𝕜 ψ p.2 v.2 = 0
  rw [hv', map_zero]

end TauCeti
