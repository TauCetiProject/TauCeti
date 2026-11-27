/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Exponential.Classification

/-!
# The Lie map of a conjugated homomorphism

Let `φ : K → G` be a smooth homomorphism of Lie groups and `g ∈ G`. The homomorphism
`ψ x = g φ(x) g⁻¹` has differential `dψ = Ad g ∘ dφ` at the identity
(`lieMap_eq_Ad_comp_of_apply_eq`): both sides carry the one-parameter subgroup `exp(t X)` of `K` to
the one-parameter subgroup `g exp(t dφ X) g⁻¹ = exp(t Ad g (dφ X))` of `G`, and a one-parameter
subgroup determines its generator. In particular, conjugating a homomorphism by `g` transports the
data read off from its differential, for instance the coroot and root vectors of a rank-one
homomorphism `SU(2) → G`, by `Ad g`.
-/

public section

noncomputable section

open TauCeti.Lie
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ K]

/-- **The Lie map of a conjugated homomorphism.** If the smooth homomorphisms `φ ψ : K → G`
satisfy `ψ x = g φ(x) g⁻¹` for every `x`, then `dψ = Ad g ∘ dφ`. -/
theorem lieMap_eq_Ad_comp_of_apply_eq (φ ψ : ContMDiffMonoidMorphism I' I ∞ K G) (g : G)
    (h : ∀ x, ψ x = g * φ x * g⁻¹) :
    lieMap ψ = (Ad (I := I) g).toLieHom.comp (lieMap φ) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space K := I'.t2Space_of_lieGroup ∞
  refine LieHom.ext fun X ↦ oneParameterSubgroup_injective (I := I) (G := G) ?_
  ext t
  rw [← ofAdd_toAdd t, oneParameterSubgroup_apply, oneParameterSubgroup_apply, ← map_smul,
    ← map_lieExp, h, map_lieExp, conj_lieExp, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    ← map_smul, ← map_smul]
