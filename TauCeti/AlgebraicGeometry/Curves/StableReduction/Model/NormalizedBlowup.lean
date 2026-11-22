/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Blowup
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.CartierDivisor
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
  morphism of models (`TauCeti.Model.isEffectiveCartier_comap_hom`, in `Model.CartierDivisor`),
  without assuming flatness of the morphism, integrality of the source, or a support restriction;
* consequently, the centre `I` pulls back to an effective Cartier divisor on the normalized blowup
  (`TauCeti.Model.isEffectiveCartier_comap_normalizedBlowupHom`);
* as an abbreviation for `(M.blowup I hC).normalization`, the normalized blowup preserves
  properness via `TauCeti.Model.isProper_normalization` and has normal total space when `C` is
  smooth over `K` via `TauCeti.Model.isNormalScheme_normalization_of_smooth`;
* `M.normalizedBlowupHom I hC` factors as `(M.blowup I hC).normalizationHom ≫ M.blowupHom I hC`
  (`TauCeti.Model.normalizedBlowupHom_def`);
* any morphism from a normal model along which `I` pulls back to an effective Cartier divisor
  factors uniquely through `M.normalizedBlowup I hC` (`TauCeti.Model.normalizedBlowupLift`,
  `TauCeti.Model.normalizedBlowupLift_normalizationHom`,
  `TauCeti.Model.normalizedBlowupLift_normalizedBlowupHom`, and
  `TauCeti.Model.eq_normalizedBlowupLift`);
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

/-- The normalized-blowup morphism factors as the normalization morphism followed by the blowup
morphism. -/
lemma normalizedBlowupHom_def :
    M.normalizedBlowupHom I hC = (M.blowup I hC).normalizationHom ≫ M.blowupHom I hC :=
  (rfl)

/-- The normalized-blowup morphism of models has the composite of the normalization and blowup
morphisms as its underlying scheme morphism. -/
@[simp]
lemma normalizedBlowupHom_hom :
    (M.normalizedBlowupHom I hC).hom =
      (M.blowup I hC).genericι.fromNormalization ≫ I.blowupToBase := by
  rw [normalizedBlowupHom, comp_hom, normalizationHom_hom, blowupHom_hom]

/-- The normalized-blowup morphism of models is proper on total spaces. -/
instance isProper_normalizedBlowupHom_hom :
    AlgebraicGeometry.IsProper (M.normalizedBlowupHom I hC).hom := by
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  rw [normalizedBlowupHom_hom]
  infer_instance

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
    rw [normalizedBlowupHom]
    infer_instance

variable {M I hC} {N : Model R K C toK}

/-- **The universal property of the normalized blowup: the lift.** A morphism of models
`f : N ⟶ M` from a normal model `N` along which `I` pulls back to an effective Cartier divisor
factors through `M.normalizedBlowup I hC`. -/
def normalizedBlowupLift [TauCeti.AlgebraicGeometry.IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    N ⟶ M.normalizedBlowup I hC :=
  liftToNormalization (blowupLift (hC := hC) f hf)

/-- Composing the lift to the normalized blowup with the normalization morphism recovers the lift to
the blowup. -/
@[reassoc (attr := simp)]
lemma normalizedBlowupLift_normalizationHom
    [TauCeti.AlgebraicGeometry.IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    normalizedBlowupLift (hC := hC) f hf ≫ (M.blowup I hC).normalizationHom =
      blowupLift (hC := hC) f hf :=
  liftToNormalization_normalizationHom _

/-- The lift to the normalized blowup commutes with `M.normalizedBlowupHom I hC`. -/
@[reassoc (attr := simp)]
lemma normalizedBlowupLift_normalizedBlowupHom
    [TauCeti.AlgebraicGeometry.IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    normalizedBlowupLift (hC := hC) f hf ≫ M.normalizedBlowupHom I hC = f := by
  rw [normalizedBlowupLift, normalizedBlowupHom, ← Category.assoc,
    liftToNormalization_normalizationHom, blowupLift_blowupHom]

/-- **The universal property of the normalized blowup: uniqueness.** Every morphism of models
from a normal model `N` to `M.normalizedBlowup I hC` lying over `f : N ⟶ M` equals
`normalizedBlowupLift`. -/
theorem eq_normalizedBlowupLift [TauCeti.AlgebraicGeometry.IsNormalScheme N.total]
    {f : N ⟶ M} (hf : (I.comap f.hom).IsEffectiveCartier)
    {g : N ⟶ M.normalizedBlowup I hC} (hg : g ≫ M.normalizedBlowupHom I hC = f) :
    g = normalizedBlowupLift f hf := by
  refine eq_liftToNormalization (eq_blowupLift hf ?_)
  simpa [normalizedBlowupHom, Category.assoc] using hg

end TauCeti.Model
