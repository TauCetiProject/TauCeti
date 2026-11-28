/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Prod
public import TauCeti.Topology.FiberBundle.Principal.Prod

/-!
# Smooth fibrewise products of principal bundles

`TauCeti.PrincipalBundle.FiberProd.instContMDiffFiberBundle` gives the smooth bundle structure
on the fibrewise product of two principal bundles. It uses `TauCeti.ContMDiffFiberBundle.prod`
with the same distinguished fibre points as the principal product atlas. The product action
is supplied by `TauCeti.PrincipalBundle.FiberProd.instPrincipalBundle`. With these fibre points
as local `Zero` instances, `TauCeti.ManifoldTotalSpace.contMDiff_prod_iff` and
`TauCeti.ManifoldTotalSpace.existsUnique_contMDiff_of_proj_eq` apply to the principal product.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle.FiberProd

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {B G H : Type*} [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace H]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [ChartedSpace HG G]
  {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] {HH : Type*} [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [ChartedSpace HH H]
  {P Q : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle G P] [FiberBundle H Q] [One G] [One H]

/-- The fibrewise product of two `C^n` principal bundles is a `C^n` bundle for the
product group (Husemoller, *Fibre Bundles*, 3rd ed., Chapter 4, §4). -/
instance instContMDiffFiberBundle
    [ContMDiffFiberBundle n G P IB IG] [ContMDiffFiberBundle n H Q IB IH] :
    ContMDiffFiberBundle n (G × H) (FiberProd P Q) IB (IG.prod IH) :=
  let : ∀ b, Zero (P b) := fun b ↦ ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  let : ∀ b, Zero (Q b) := fun b ↦ ⟨(FiberBundle.homeomorphAt H Q b).symm 1⟩
  ContMDiffFiberBundle.prod

end TauCeti.PrincipalBundle.FiberProd
