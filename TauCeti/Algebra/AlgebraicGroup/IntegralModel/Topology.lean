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
compact subgroup of the points of the base change `E ⊗[𝒪[E]] A` for the point topology, and an
open one when `A` is of finite type. The base-change adjunction `PointTopology.baseChangeHomeomorph`
identifies these points with `Hom(A, E)`, carrying the integral points to the image of
`Hom(A, 𝒪[E])`, which is compact (`PointTopology.isCompact_range_mapValue_integer`) and, for `A`
of finite type, open (`PointTopology.isOpenEmbedding_mapValue_integer`).

For a smooth model `𝒢` of an affine `E`-group `G`, the integral points `𝒢(𝒪[E])` are therefore a
compact open subgroup of `G(E)`: this is the Check *SmoothModel.integralPoints_compat* of
ReductiveGroupsPartII RG2.3.1, for the point topology of RG2.0.

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

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

section HopfAlgebra

variable (A : Type*) [CommRing A] [HopfAlgebra 𝒪[E] A]

/-- The base-change adjunction `Hom_E(E ⊗ A, E) ≃ₜ Hom(A, E)` on the convolution types of
points. -/
private noncomputable def pointsHomeomorph :
    WithConv (E ⊗[𝒪[E]] A →ₐ[E] E) ≃ₜ WithConv (A →ₐ[𝒪[E]] E) :=
  (PointTopology.isHomeomorph_ofConv.homeomorph _).trans
    ((PointTopology.baseChangeHomeomorph 𝒪[E] E A E).trans
      (PointTopology.isHomeomorph_ofConv.homeomorph _).symm)

private theorem pointsHomeomorph_pointsBaseChange (f : WithConv (A →ₐ[𝒪[E]] 𝒪[E])) :
    pointsHomeomorph A (AlgHom.pointsBaseChange E f) = AlgHom.mapValue (Algebra.ofId 𝒪[E] E) f := by
  rw [pointsHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_eq]
  ext a
  simp [AlgHom.mapValue_apply]

/-- The integral points are the preimage, under the base-change adjunction, of the points of `A`
with values in `𝒪[E]`. -/
private theorem coe_integralPoints_eq_preimage :
    (integralPoints 𝒪[E] E A : Set (WithConv (E ⊗[𝒪[E]] A →ₐ[E] E))) =
      pointsHomeomorph A ⁻¹' Set.range (AlgHom.mapValue (H := A) (Algebra.ofId 𝒪[E] E)) := by
  ext g
  rw [SetLike.mem_coe, mem_integralPoints_iff_exists, Set.mem_preimage, Set.mem_range]
  refine exists_congr fun f ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, pointsHomeomorph_pointsBaseChange]
  · exact (pointsHomeomorph A).injective (by rw [pointsHomeomorph_pointsBaseChange, h])

/-- **The integral points are compact.** For a commutative Hopf algebra `A` over the valuation ring
of a nonarchimedean local field `E`, the integral points form a compact subgroup of the points of
`E ⊗[𝒪[E]] A`. -/
theorem isCompact_integralPoints :
    IsCompact (integralPoints 𝒪[E] E A : Set (WithConv (E ⊗[𝒪[E]] A →ₐ[E] E))) := by
  rw [coe_integralPoints_eq_preimage, Homeomorph.isCompact_preimage]
  exact PointTopology.isCompact_range_mapValue_integer

/-- **The integral points are open.** For a commutative Hopf algebra `A` of finite type over the
valuation ring of a nonarchimedean local field `E`, the integral points form an open subgroup of
the points of `E ⊗[𝒪[E]] A`. -/
theorem isOpen_integralPoints [Algebra.FiniteType 𝒪[E] A] :
    IsOpen (integralPoints 𝒪[E] E A : Set (WithConv (E ⊗[𝒪[E]] A →ₐ[E] E))) := by
  rw [coe_integralPoints_eq_preimage]
  exact PointTopology.isOpenEmbedding_mapValue_integer.isOpen_range.preimage
    (pointsHomeomorph A).continuous

end HopfAlgebra

namespace SmoothModel

universe u

variable {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {H : FiniteTypeCommHopfAlgCat.{u, u} E}
  (𝒢 : SmoothModel 𝒪[E] E H)

/-- **The integral points of a smooth model are compact.** For a smooth model `𝒢` over the
valuation ring of a nonarchimedean local field `E`, `𝒢(𝒪[E])` is a compact subgroup of `G(E)`. -/
theorem isCompact_integralPoints :
    IsCompact (𝒢.integralPoints : Set (WithConv (H →ₐ[E] E))) := by
  set φ := FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom with hφ
  set ψ := FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.inv with hψ
  have hφψ (x : WithConv (E ⊗[𝒪[E]] 𝒢.coord →ₐ[E] E)) :
      BialgHom.mapDomain φ (BialgHom.mapDomain ψ x) = x := by
    rw [← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp, hφ, hψ,
      ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, CategoryTheory.Iso.hom_inv_id,
      FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.mapDomain_id, MonoidHom.id_apply]
  have hψφ (g : WithConv (H →ₐ[E] E)) :
      BialgHom.mapDomain ψ (BialgHom.mapDomain φ g) = g := by
    rw [← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp, hφ, hψ,
      ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, CategoryTheory.Iso.inv_hom_id,
      FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.mapDomain_id, MonoidHom.id_apply]
  have h : (𝒢.integralPoints : Set (WithConv (H →ₐ[E] E))) =
      BialgHom.mapDomain ψ '' (IntegralModel.integralPoints 𝒪[E] E 𝒢.coord : Set _) := by
    ext g
    rw [SetLike.mem_coe, mem_integralPoints_iff_mapDomain]
    refine ⟨fun hg ↦ ⟨_, hg, hψφ g⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    rwa [hφψ]
  rw [h]
  exact (IntegralModel.isCompact_integralPoints 𝒢.coord).image (BialgHom.continuous_mapDomain ψ)

/-- **The integral points of a smooth model are open.** For a smooth model `𝒢` over the valuation
ring of a nonarchimedean local field `E`, `𝒢(𝒪[E])` is an open subgroup of `G(E)`. -/
theorem isOpen_integralPoints : IsOpen (𝒢.integralPoints : Set (WithConv (H →ₐ[E] E))) := by
  rw [integralPoints_def, Subgroup.coe_comap]
  exact (IntegralModel.isOpen_integralPoints 𝒢.coord).preimage (BialgHom.continuous_mapDomain _)

end SmoothModel

end TauCeti.IntegralModel
