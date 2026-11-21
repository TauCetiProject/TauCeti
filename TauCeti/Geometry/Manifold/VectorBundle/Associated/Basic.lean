/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Basic
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension

/-!
# Smooth associated vector bundles

The vector bundle associated to a smooth principal bundle and a smooth linear action is a
native `ContMDiffVectorBundle`. Its topology and atlas are those of the existing associated
fibre bundle; no second total-space construction is used. The transition operators are the
principal transition functions acting on the model vector space.

The smoothness assertion is over the base field. For a complex representation over a real base,
use it with the underlying real normed space; the topological associated-vector-bundle
construction also supplies the compatible complex-linear vector-bundle structure.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

open Bundle MulOpposite Set TauCeti
open scoped Manifold ContDiff

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners 𝕜 EG HG)
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]

/-- A smooth linear action on a finite-dimensional space gives a smooth associated vector
bundle, on precisely the existing associated fibre-bundle carrier and atlas. The group model
is explicit because it is not determined by the conclusion. -/
theorem contMDiffVectorBundle [ContMDiffSMul IG 𝓘(𝕜, F) n G F]
    [ContMDiffFiberBundle n G P IB IG] :
    ContMDiffVectorBundle n F (AssociatedBundle G P F) IB := by
  let := AssociatedBundle.contMDiffFiberBundle (n := n) (G := G) (P := P) (F := F)
    (IB := IB) (IF := 𝓘(𝕜, F)) IG
  constructor
  intro e e' he he' b hb
  apply TauCeti.contMDiffWithinAt_clm_apply.mpr
  intro v
  have h := (ContMDiffFiberBundle.contMDiffOn_coordChange (IB := IB)
    (IF := 𝓘(𝕜, F)) (n := n) e e').comp
    (contMDiffOn_id.prodMk (contMDiffOn_const (c := v))) (fun _ hx ↦ ⟨hx, mem_univ _⟩)
  exact (h.congr fun x hx ↦ e.coordChangeL_apply' e' hx v) b hb

end TauCeti.AssociatedBundle
