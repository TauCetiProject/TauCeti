/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Linear
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import TauCeti.Geometry.Symplectic.Cotangent.MomentMap

/-!
# The cotangent moment map of a linear Lie group action

Let a Lie group `G` act smoothly and linearly on a normed space `V`. The moment map
`⟨μ(q, p), ξ⟩ = p(ξ_V q)` (`TauCeti.CotangentBundle.momentMap`) of the cotangent lift of this
action to the manifold `T*V` is, in the global coordinates `T*V ≃ V × V*`
(`TauCeti.CotangentBundle.modelSpaceDiffeomorph`), the moment map `TauCeti.cotangentMomentMap` of
the cotangent-lifted linear action of `gl(V)`, restricted along the differential `ξ ↦ ξ_V` of the
representation at the identity (`TauCeti.fundamentalLinearMap`):
`TauCeti.CotangentBundle.momentMap_eq_cotangentMomentMap_comp_fundamentalLinearMap`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 12.1.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.CotangentBundle

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DistribMulAction G V] [SMulCommClass G ℝ V] [ContMDiffSMul IG 𝓘(ℝ, V) 1 G V]

/-- **The cotangent moment map of a linear action.** For a smooth linear action of a Lie group `G`
on a normed space `V`, the moment map `⟨μ(q, p), ξ⟩ = p(ξ_V q)` of the cotangent-lifted action on
`T*V` is, in the global coordinates `T*V ≃ V × V*`, the moment map `cotangentMomentMap` of the
cotangent-lifted linear action of `gl(V)`, restricted along the differential `ξ ↦ ξ_V` of the
representation at the identity. -/
theorem momentMap_eq_cotangentMomentMap_comp_fundamentalLinearMap
    (z : CotangentBundle 𝓘(ℝ, V) V) :
    momentMap IG G z =
      (cotangentMomentMap (modelSpaceDiffeomorph V z)).comp (fundamentalLinearMap IG G V) := by
  ext ξ
  rw [momentMap_apply, LinearMap.comp_apply, cotangentMomentMap_apply, modelSpaceDiffeomorph_apply,
    fundamentalLinearMap_apply_eq_fundamentalVectorField]
  -- Both sides are `z.snd (ξ_V z.proj)`, but the left coerces `z.snd` as a form on the fibre
  -- `TangentSpace 𝓘(ℝ, V) z.proj` and the right as an element of `StrongDual ℝ V`. These types
  -- agree only after unfolding `TangentSpace`, which no rewrite or reducible `rfl` performs.
  rfl

end TauCeti.CotangentBundle
