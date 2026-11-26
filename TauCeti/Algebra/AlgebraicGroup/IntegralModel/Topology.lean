/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Basic
public import TauCeti.Topology.Algebra.PointTopology.Functoriality
public import TauCeti.Topology.Algebra.PointTopology.Group
public import TauCeti.Topology.Algebra.PointTopology.IntegralPoints

/-!
# Integral points of smooth models are compact open

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`. For a commutative Hopf
`𝒪[E]`-algebra `A`, the integral points `TauCeti.IntegralModel.integralPoints 𝒪[E] E A` are a
compact subgroup of the points of the base change `E ⊗[𝒪[E]] A` for the point topology. The
base-change adjunction `PointTopology.baseChangeConvHomeomorph` identifies these points with
`Hom(A, E)`, carrying the integral points to the image of `Hom(A, 𝒪[E])`, which is compact
(`PointTopology.isCompact_range_mapValue_integer`). Openness holds more generally: over any ring
`E` with a valuative topology, the integral points of a Hopf `𝒪[E]`-algebra of finite type are
open, since the image of `Hom(A, 𝒪[E])` is then open
(`PointTopology.isOpenEmbedding_mapValue_integer`).

For a smooth model `𝒢` of an affine `E`-group `G`, the integral points `𝒢(𝒪[E])` are therefore a
compact open subgroup of `G(E)` for the point topology.

## Main results

* `TauCeti.IntegralModel.isCompact_integralPoints`, `TauCeti.IntegralModel.isOpen_integralPoints`:
  the integral points of a Hopf algebra over `𝒪[E]` are compact, and open for finite type.
* `TauCeti.IntegralModel.SmoothModel.isCompact_integralPoints`,
  `TauCeti.IntegralModel.SmoothModel.isOpen_integralPoints`: the integral points of a smooth model
  form a compact open subgroup of `G(E)`.
-/

public section

open TensorProduct ValuativeRel WithConv

namespace TauCeti.IntegralModel

open scoped TauCeti.PointTopology

section Valuative

variable {E : Type*} [CommRing E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  (A : Type*) [Semiring A] [HopfAlgebra 𝒪[E] A]

/-- The integral points are the preimage, under the base-change adjunction, of the points of `A`
with values in `𝒪[E]`. -/
private theorem coe_integralPoints_eq_preimage :
    (integralPoints 𝒪[E] E A : Set (WithConv (E ⊗[𝒪[E]] A →ₐ[E] E))) =
      PointTopology.baseChangeConvHomeomorph 𝒪[E] E A E ⁻¹'
        Set.range (AlgHom.mapValue (H := A) (Algebra.ofId 𝒪[E] E)) := by
  rw [← Homeomorph.image_symm, PointTopology.coe_baseChangeConvHomeomorph_symm]
  simp [integralPoints_def, AlgHom.pointsBaseChange_def, ← Set.range_comp]

/-- **The integral points are open.** For a Hopf algebra `A` of finite type over the valuation
ring of a ring `E` with a valuative topology, the integral points form an open subgroup of the
points of `E ⊗[𝒪[E]] A`. -/
theorem isOpen_integralPoints [Algebra.FiniteType 𝒪[E] A] :
    IsOpen (integralPoints 𝒪[E] E A : Set (WithConv (E ⊗[𝒪[E]] A →ₐ[E] E))) := by
  rw [coe_integralPoints_eq_preimage]
  exact PointTopology.isOpenEmbedding_mapValue_integer.isOpen_range.preimage
    (PointTopology.baseChangeConvHomeomorph 𝒪[E] E A E).continuous

end Valuative

section LocalField

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  (A : Type*) [CommRing A] [HopfAlgebra 𝒪[E] A]

/-- **The integral points are compact.** For a commutative Hopf algebra `A` over the valuation ring
of a nonarchimedean local field `E`, the integral points form a compact subgroup of the points of
`E ⊗[𝒪[E]] A`. -/
theorem isCompact_integralPoints :
    IsCompact (integralPoints 𝒪[E] E A : Set (WithConv (E ⊗[𝒪[E]] A →ₐ[E] E))) := by
  rw [coe_integralPoints_eq_preimage, Homeomorph.isCompact_preimage]
  exact PointTopology.isCompact_range_mapValue_integer

end LocalField

namespace SmoothModel

universe u

section Valuative

variable {E : Type u} [CommRing E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  {H : FiniteTypeCommHopfAlgCat.{u, u} E} (𝒢 : SmoothModel 𝒪[E] E H)

/-- **The integral points of a smooth model are open.** For a smooth model `𝒢` over the valuation
ring of a ring `E` with a valuative topology, `𝒢(𝒪[E])` is an open subgroup of `G(E)`. -/
theorem isOpen_integralPoints : IsOpen (𝒢.integralPoints : Set (WithConv (H →ₐ[E] E))) := by
  rw [integralPoints_def, Subgroup.coe_comap]
  exact (IntegralModel.isOpen_integralPoints 𝒢.coord).preimage (BialgHom.continuous_mapDomain _)

end Valuative

section LocalField

variable {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {H : FiniteTypeCommHopfAlgCat.{u, u} E}
  (𝒢 : SmoothModel 𝒪[E] E H)

/-- **The integral points of a smooth model are compact.** For a smooth model `𝒢` over the
valuation ring of a nonarchimedean local field `E`, `𝒢(𝒪[E])` is a compact subgroup of `G(E)`. -/
theorem isCompact_integralPoints :
    IsCompact (𝒢.integralPoints : Set (WithConv (H →ₐ[E] E))) := by
  let i := CommHopfAlgCat.ofIso ((CategoryTheory.ObjectProperty.ι _).mapIso 𝒢.genericFiberIso)
  rw [integralPoints_def, Subgroup.coe_comap, ← FiniteTypeCommHopfAlgCat.toBialgHom_ofIso_ι_mapIso,
    BialgEquiv.toBialgHom_eq_coe, ← BialgEquiv.coe_mapDomainContinuousMulEquiv]
  exact (i.mapDomainContinuousMulEquiv.toHomeomorph.isCompact_preimage).2
    (IntegralModel.isCompact_integralPoints 𝒢.coord)

end LocalField

end SmoothModel

end TauCeti.IntegralModel
