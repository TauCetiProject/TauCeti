/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Blowup
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Normalization

/-!
# Normalized blowups of models over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`, let `M` be a model over `R` of a
scheme `C` over `K`, and let `I` be an ideal sheaf on `M.total` whose support `V(I)` is disjoint
from the generic fibre `C ⊆ M.total`. When the normalization of the blowup `M.blowup I hC` in `C`
is finite — in particular, unconditionally over any discrete valuation ring whenever `C` is smooth
of relative dimension `1` over `K` (`TauCeti.Model.isFinite_fromNormalization_genericι`) — the
*normalized blowup* `M.normalizedBlowup I hC` is `(M.blowup I hC).normalization`, with canonical
morphism `M.normalizedBlowupHom I hC : M.normalizedBlowup I hC ⟶ M`.

Iterating normalized blowups in non-regular closed points of the special fibre is Lipman's and
Liu's resolution procedure producing a regular proper model of a smooth proper curve over `K`.
This file establishes the basic properties of a single normalized-blowup step:

* every effective Cartier divisor on a model pulls back to an effective Cartier divisor along every
  morphism of models (`TauCeti.Model.isEffectiveCartier_comap_hom`), without assuming flatness of
  the morphism, integrality of the source, or a support restriction;
* consequently, the centre `I` pulls back to an effective Cartier divisor on the normalized blowup
  (`TauCeti.Model.isEffectiveCartier_comap_normalizedBlowupHom`);
* as an abbreviation for `(M.blowup I hC).normalization`, the normalized blowup preserves
  properness via `TauCeti.Model.isProper_normalization` and has normal total space when `C` is
  smooth over `K` via `TauCeti.Model.isNormalScheme_normalization_of_smooth`;
* when `M.total` is already normal, `M.normalizedBlowupHom I hC` is an isomorphism if and only if
  `I` is already an effective Cartier divisor on `M.total`
  (`TauCeti.Model.isIso_normalizedBlowupHom_iff`).

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.3
  and Chapter 10.
* [Stacks Project, Section 55.8 (0C2T)](https://stacks.math.columbia.edu/tag/0C2T).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- Along any morphism of models `f : N ⟶ M`, every effective Cartier divisor `E` on `M.total`
pulls back to an effective Cartier divisor on `N.total`. Neither flatness of `f.hom`, integrality
of `N.total`, nor a support restriction is required: local equations remain regular on the common
generic fibre by flatness of `M.genericι`, and the generic fibre is scheme-theoretically dense in
`N.total`. -/
theorem isEffectiveCartier_comap_hom {M N : Model R K C toK} (f : N ⟶ M)
    {E : M.total.IdealSheafData} (hE : E.IsEffectiveCartier) :
    (E.comap f.hom).IsEffectiveCartier := by
  rw [Scheme.IdealSheafData.isEffectiveCartier_iff]
  intro x
  obtain ⟨U, hxU, a, ha, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff E).mp hE (f.hom x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU'⟩ :=
    N.total.isBasis_affineOpens.exists_subset_of_mem_open hxU (f.hom ⁻¹ᵁ U.val).isOpen
  have hVU : V ≤ f.hom ⁻¹ᵁ U.val := hVU'
  let b : Γ(N.total, V) := f.hom.appLE U.val V hVU a
  have hEV : (E.comap f.hom).ideal ⟨V, hV⟩ = Ideal.span {b} := by
    rw [E.ideal_comap_of_le f.hom U ⟨V, hV⟩ hVU, hUa, Ideal.map_span, Set.image_singleton]
  refine ⟨⟨V, hV⟩, hxV, b, fun u v huv ↦ N.genericι.app_injective V ?_, hEV⟩
  have hflat : Flat (N.genericι ≫ f.hom) := by
    rw [genericι_hom]
    have := M.isOpenImmersion_genericι
    infer_instance
  have hWU : N.genericι ⁻¹ᵁ V ≤ (N.genericι ≫ f.hom) ⁻¹ᵁ U.val := N.genericι.preimage_mono hVU
  let : Algebra Γ(M.total, U.val) Γ(C, N.genericι ⁻¹ᵁ V) :=
    ((N.genericι ≫ f.hom).appLE U.val (N.genericι ⁻¹ᵁ V) hWU).hom.toAlgebra
  have : Module.Flat Γ(M.total, U.val) Γ(C, N.genericι ⁻¹ᵁ V) :=
    (N.genericι ≫ f.hom).flat_appLE U.property (hV.preimage N.genericι) hWU
  have hreg : IsSMulRegular Γ(C, N.genericι ⁻¹ᵁ V) (N.genericι.app V b) := by
    have hcomm : N.genericι.app V b =
        algebraMap Γ(M.total, U.val) Γ(C, N.genericι ⁻¹ᵁ V) a := by
      rw [RingHom.algebraMap_toAlgebra]
      have hnat : f.hom.appLE U.val V hVU ≫ N.genericι.app V =
          (N.genericι ≫ f.hom).appLE U.val (N.genericι ⁻¹ᵁ V) hWU := by
        rw [N.genericι.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      exact ConcreteCategory.congr_hom hnat a
    rw [hcomm]
    intro y z hyz
    exact ha.of_flat (S := Γ(C, N.genericι ⁻¹ᵁ V)) (by simpa [Algebra.smul_def] using hyz)
  exact hreg (by simpa [smul_eq_mul, map_mul] using congrArg (N.genericι.app V) huv)

variable (M : Model R K C toK) (I : M.total.IdealSheafData)
  (hC : Disjoint (Set.range M.genericι) (I.support : Set M.total))
  [IsFinite (M.blowup I hC).genericι.fromNormalization]

/-- **The normalized blowup of a model** along an ideal sheaf `I` supported away from the generic
fibre: the normalization of `M.blowup I hC` in `C`. When `SmoothOfRelativeDimension 1 toK`, the
finiteness hypothesis is synthesized automatically over any discrete valuation ring `R`. -/
abbrev normalizedBlowup : Model R K C toK :=
  (M.blowup I hC).normalization

/-- **The normalized-blowup morphism of models** `M.normalizedBlowup I hC ⟶ M`. -/
def normalizedBlowupHom : M.normalizedBlowup I hC ⟶ M :=
  (M.blowup I hC).normalizationHom ≫ M.blowupHom I hC

/-- The centre `I` pulls back to an effective Cartier divisor on the normalized blowup. -/
theorem isEffectiveCartier_comap_normalizedBlowupHom :
    (I.comap (M.normalizedBlowupHom I hC).hom).IsEffectiveCartier := by
  rw [normalizedBlowupHom, comp_hom, Scheme.IdealSheafData.comap_comp, blowupHom_hom]
  exact isEffectiveCartier_comap_hom (M.blowup I hC).normalizationHom
    I.isEffectiveCartier_comap_blowupToBase

/-- When the total space of `M` is normal, the normalized-blowup morphism is an isomorphism if and
only if the centre `I` is already an effective Cartier divisor on `M.total`. -/
theorem isIso_normalizedBlowupHom_iff [TauCeti.AlgebraicGeometry.IsNormalScheme M.total] :
    IsIso (M.normalizedBlowupHom I hC) ↔ I.IsEffectiveCartier := by
  refine ⟨fun _ ↦ ?_, fun hI ↦ ?_⟩
  · have : IsIso (M.normalizedBlowupHom I hC).hom := (isIso_iff_isIso_hom _).mp ‹_›
    have hEC := (M.isEffectiveCartier_comap_normalizedBlowupHom I hC).comap
      (inv (M.normalizedBlowupHom I hC).hom)
    rwa [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id] at hEC
  · have : IsIso (M.blowupHom I hC) := (M.isIso_blowupHom_iff I hC).mpr hI
    have : IsIso (M.blowupHom I hC).hom := (isIso_iff_isIso_hom _).mp ‹_›
    have : TauCeti.AlgebraicGeometry.IsNormalScheme (M.blowup I hC).total :=
      .of_isOpenImmersion (M.blowupHom I hC).hom
    have : IsIso (M.blowup I hC).normalizationHom :=
      (M.blowup I hC).isIso_normalizationHom_of_isNormalScheme
    rw [normalizedBlowupHom]
    infer_instance

end TauCeti.Model
