/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Blowup
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Normalization

import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

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

* any effective Cartier divisor on a model whose support misses the generic fibre pulls back to an
  effective Cartier divisor along every morphism of models
  (`TauCeti.Model.isEffectiveCartier_comap_hom`), without assuming flatness of the morphism or
  integrality of the source;
* consequently, the centre `I` pulls back to an effective Cartier divisor on the normalized blowup
  (`TauCeti.Model.isEffectiveCartier_comap_normalizedBlowupHom`);
* the normalized blowup preserves properness (`TauCeti.Model.isProper_normalizedBlowup`) and has
  normal total space when `C` is smooth over `K`
  (`TauCeti.Model.isNormalScheme_normalizedBlowup_total`);
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

/-- Along any morphism of models `f : N ⟶ M`, an effective Cartier divisor `E` on `M.total` whose
support is disjoint from the generic fibre pulls back to an effective Cartier divisor on `N.total`.
Neither flatness of `f.hom` nor integrality of `N.total` is required: local equations invert on the
generic fibre, which is scheme-theoretically dense in `N.total`. -/
theorem isEffectiveCartier_comap_hom {M N : Model R K C toK} (f : N ⟶ M)
    {E : M.total.IdealSheafData} (hE : E.IsEffectiveCartier)
    (hEC : Disjoint (Set.range M.genericι) (E.support : Set M.total)) :
    (E.comap f.hom).IsEffectiveCartier := by
  rw [Scheme.IdealSheafData.isEffectiveCartier_iff]
  intro x
  obtain ⟨U, hxU, a, -, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff E).mp hE (f.hom x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    N.total.isBasis_affineOpens.exists_subset_of_mem_open hxU (f.hom ⁻¹ᵁ U.1).isOpen
  let b : Γ(N.total, V) := f.hom.appLE U.1 V hVU a
  have hEV : (E.comap f.hom).ideal ⟨V, hV⟩ = Ideal.span {b} := by
    rw [E.ideal_comap_of_le f.hom U ⟨V, hV⟩ hVU, hUa, Ideal.map_span, Set.image_singleton]
  refine ⟨⟨V, hV⟩, hxV, b, fun u v huv ↦ N.genericι.app_injective V ?_, hEV⟩
  have htopE : (E.comap f.hom).comap N.genericι = ⊤ := by
    rw [← E.comap_comp, genericι_hom, E.comap_eq_top_iff]
    ext c
    exact iff_of_true (fun hc ↦ hEC.le_bot ⟨⟨c, rfl⟩, hc⟩) trivial
  let W : C.affineOpens := ⟨N.genericι ⁻¹ᵁ V, hV.preimage N.genericι⟩
  have hspan : Ideal.span {(N.genericι.app V).hom b} = (⊤ : Ideal Γ(C, W)) := by
    have hW := congrArg (fun J : C.IdealSheafData ↦ J.ideal W) htopE
    rw [Scheme.IdealSheafData.ideal_comap_of_le _ N.genericι ⟨V, hV⟩ W le_rfl, hEV,
      Ideal.map_span, Set.image_singleton, Scheme.IdealSheafData.ideal_top, Pi.top_apply,
      ← Scheme.Hom.app_eq_appLE] at hW
    exact hW
  exact (Ideal.span_singleton_eq_top.mp hspan).mul_right_inj.mp
    (by simpa [smul_eq_mul, map_mul] using congrArg (N.genericι.app V) huv)

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

/-- The total space of `M.normalizedBlowup I hC` is the normalization of `I.blowup` in `C`. -/
@[simp]
lemma normalizedBlowup_total :
    (M.normalizedBlowup I hC).total = (M.blowup I hC).genericι.normalization :=
  rfl

/-- The structure morphism of `M.normalizedBlowup I hC` factors through the normalization and
blowup morphisms. -/
@[simp]
lemma normalizedBlowup_toBase :
    (M.normalizedBlowup I hC).toBase =
      (M.blowup I hC).genericι.fromNormalization ≫ I.blowupToBase ≫ M.toBase :=
  rfl

/-- The underlying scheme morphism of `M.normalizedBlowupHom I hC` is the composite of the
normalization morphism and `I.blowupToBase`. -/
@[simp]
lemma normalizedBlowupHom_hom :
    (M.normalizedBlowupHom I hC).hom =
      (M.blowup I hC).genericι.fromNormalization ≫ I.blowupToBase := by
  simp [normalizedBlowupHom]

/-- The normalized blowup of a proper model is a proper model. -/
lemma isProper_normalizedBlowup [M.IsProper] : (M.normalizedBlowup I hC).IsProper := by
  have := M.isProper_blowup I hC
  exact (M.blowup I hC).isProper_normalization

/-- When the generic fibre is smooth over `K`, the normalized blowup has normal total space. -/
instance isNormalScheme_normalizedBlowup_total [Smooth toK] :
    TauCeti.AlgebraicGeometry.IsNormalScheme (M.normalizedBlowup I hC).total :=
  (M.blowup I hC).isNormalScheme_normalization_total

/-- The centre `I` pulls back to an effective Cartier divisor on the normalized blowup. -/
theorem isEffectiveCartier_comap_normalizedBlowupHom :
    (I.comap (M.normalizedBlowupHom I hC).hom).IsEffectiveCartier := by
  rw [normalizedBlowupHom, comp_hom, Scheme.IdealSheafData.comap_comp, blowupHom_hom]
  refine isEffectiveCartier_comap_hom (M.blowup I hC).normalizationHom
    I.isEffectiveCartier_comap_blowupToBase ?_
  rw [Set.disjoint_left]
  rintro _ ⟨c, rfl⟩ hc
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Set.mem_preimage] at hc
  exact hC.le_bot ⟨⟨c, congrArg (· c) (M.genericι_blowupToBase I hC).symm⟩, hc⟩

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
