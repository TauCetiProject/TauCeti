/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Normalization.IsIso
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Isomorphism

/-!
# Normalizing a model in its generic fibre

Let `R` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `M` be a
model over `R` of a scheme `C` over `K`, with total space `X`. The generic fibre `C ⊆ X` is the
open subscheme where `π` is invertible, and the inclusion `ι : C ⟶ X` is affine. Let
`ν : X^ν ⟶ X` be the normalization of `X` in `C` along `ι`: over an affine open `Spec A` of `X`,
the scheme `X^ν` is the spectrum of the integral closure of `A` in `A[1/π]`. When `ν` is finite,
`X^ν` is again a model of `C`:

* its generic fibre is still `C`, since normalizing in an open subscheme does not change that
  open (`AlgebraicGeometry.Scheme.Hom.isPullback_toNormalization`);
* it is flat over `R`, since `C` is scheme-theoretically dense in `X^ν`, flat over `R`, and `R`
  is a principal ideal domain
  (`AlgebraicGeometry.Scheme.Hom.flat_of_isSchemeTheoreticallyDominant_of_flat_comp`);
* it is of finite presentation over `R`, since `ν` is finite and `X` is locally noetherian.

The morphism `ν` is a morphism of models, proper when `M` is. It is the initial model among
models integral over `M`: every morphism of models `N ⟶ M` that is integral on total spaces
receives a unique morphism of models from `X^ν` over `M`. When `X` is reduced and `C` is normal,
`A[1/π]` is integrally closed in the total ring of fractions of `A`, so `X^ν` is the normalization
of `X` in the usual sense; normalized blowups of models, which resolve the singularities of a
model of a smooth curve, alternate this construction with blowups in closed points of the special
fibre.

Finiteness of `ν` is a hypothesis of the construction: it is what makes `X^ν` of finite
presentation over `R`. It holds when `C` is reduced and the rings of sections of `X` are Nagata,
and over an arbitrary discrete valuation ring when `C` is smooth over `K`.

## Main definitions

* `TauCeti.Model.normalization M`: the normalization of the total space of `M` in its generic
  fibre, as a model of `C`.
* `TauCeti.Model.normalizationHom M`: the normalization morphism, as a morphism of models.
* `TauCeti.Model.normalizationLift`: the morphism of models out of the normalization given by the
  universal property of relative normalization.

## Main results

* `TauCeti.Model.genericι_normalization`: the generic fibre of the normalization is included
  through the canonical morphism to the normalization.
* `TauCeti.Model.isProper_normalization`: the normalization of a proper model is a proper model.
* `TauCeti.Model.normalizationLift_comp` and `TauCeti.Model.eq_normalizationLift`: the universal
  property of the normalization, in the category of models.

## References

* The Stacks Project, Tag 035H (relative normalization) and Lemma 29.53.5 (03GV).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 4.1.2
  (normalization) and Chapter 10 (models of curves); Section 8.3 for desingularization by
  normalized blowups.
* [Stacks Project, Chapter 55](https://stacks.math.columbia.edu/tag/0C2P), *Semistable
  Reduction*.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable (M : Model R K C toK)

/-- The generic fibre of the normalization of the total space of `M` in `C`, over the fraction
field, is `C`. -/
private lemma isPullback_toNormalization_toBase :
    IsPullback M.genericι.toNormalization toK (M.genericι.fromNormalization ≫ M.toBase)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have := M.isOpenImmersion_genericι
  simpa using M.genericι.isPullback_toNormalization.paste_vert M.isPullback_genericι

/-- The identification of the generic fibre of the normalization of the total space of `M` in its
generic fibre with `C`. -/
def normalizationGenericFiberIso :
    genericFiber R K (M.genericι.fromNormalization ≫ M.toBase) ≅ Over.mk toK :=
  Over.isoMk (isPullback_toNormalization_toBase M).isoPullback.symm (by simp)

variable [IsFinite M.genericι.fromNormalization]

/-- **The normalization of a model in its generic fibre.** When the normalization of the total
space of `M` in the generic fibre `C` is finite, it is a model of `C`, with structure morphism
through the normalization morphism. -/
abbrev normalization : Model R K C toK where
  total := M.genericι.normalization
  toBase := M.genericι.fromNormalization ≫ M.toBase
  flat := by
    have := M.isOpenImmersion_genericι
    have : Flat (M.genericι.toNormalization ≫ M.genericι.fromNormalization ≫ M.toBase) := by
      rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
      infer_instance
    exact M.genericι.toNormalization.flat_of_isSchemeTheoreticallyDominant_of_flat_comp _
  locallyOfFinitePresentation := by
    have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
    infer_instance
  quasiCompact := inferInstance
  quasiSeparated := inferInstance
  genericFiberIso := M.normalizationGenericFiberIso

/-- The total space of the normalization model is the normalization of the total space of `M` in
the generic fibre. -/
@[simp]
lemma normalization_total : M.normalization.total = M.genericι.normalization :=
  (rfl)

/-- The structure morphism of the normalization model factors through the normalization
morphism. -/
@[simp]
lemma normalization_toBase :
    M.normalization.toBase = M.genericι.fromNormalization ≫ M.toBase :=
  (rfl)

/-- The generic fibre of the normalization model is included through the canonical morphism from
`C` to the normalization. -/
@[simp]
lemma genericι_normalization : M.normalization.genericι = M.genericι.toNormalization := by
  simp only [genericι_def, normalization, normalizationGenericFiberIso, Over.isoMk_inv_left,
    Iso.symm_inv]
  exact IsPullback.isoPullback_hom_fst _

/-- The normalization of a proper model is a proper model. -/
lemma isProper_normalization [hM : M.IsProper] : M.normalization.IsProper := by
  have : AlgebraicGeometry.IsProper M.toBase := hM
  rw [Model.IsProper, normalization_toBase]
  infer_instance

/-- **The normalization morphism of models.** The normalization morphism `X^ν ⟶ X` is a morphism
from the normalization model to `M`. -/
def normalizationHom : M.normalization ⟶ M where
  hom := M.genericι.fromNormalization
  overBase := (rfl)
  genericFiber := baseChangeHom_genericFiberIso_hom_left _ _ (by simp)

/-- The normalization morphism of models has the normalization morphism as underlying
morphism. -/
@[simp]
lemma normalizationHom_hom : M.normalizationHom.hom = M.genericι.fromNormalization :=
  (rfl)

/-- The normalization morphism of models is finite on total spaces. -/
instance isFinite_normalizationHom_hom : IsFinite M.normalizationHom.hom := by
  rw [normalizationHom_hom]
  infer_instance

/-- **The normalization step changes the model exactly when the total space is not integrally
closed in the generic fibre.** The normalization morphism of models is an isomorphism if and only
if, over every affine open `U` of the total space of `M`, every section of the generic fibre over
`U ∩ C` that is integral over `Γ(X, U)` comes from `Γ(X, U)`. -/
theorem isIso_normalizationHom_iff : IsIso M.normalizationHom ↔
    ∀ U : M.total.Opens, IsAffineOpen U →
      ∀ s, (M.genericι.app U).hom.IsIntegralElem s → s ∈ (M.genericι.app U).hom.range := by
  -- The restriction maps to the scheme-theoretically dense generic fibre are injective.
  rw [isIso_iff_isIso_hom, normalizationHom_hom, Scheme.Hom.isIso_fromNormalization_iff]
  refine forall₂_congr fun U hU ↦ and_iff_right ?_
  rw [RingHom.injective_iff_ker_eq_bot, ← M.genericι.ker_apply ⟨U, hU⟩,
    IsSchemeTheoreticallyDominant.ker_eq_bot M.genericι, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply]

variable {M} {N : Model R K C toK}

/-- **The universal property of the normalization model: the lift.** A morphism of models
`f : N ⟶ M` that is integral on total spaces receives a morphism of models from the normalization
of `M`. -/
def normalizationLift (f : N ⟶ M) [IsIntegralHom f.hom] : M.normalization ⟶ N where
  hom := M.genericι.normalizationDesc N.genericι f.hom (genericι_hom f).symm
  overBase := by
    rw [normalization_toBase, ← f.overBase, Scheme.Hom.normalizationDesc_comp_assoc]
  genericFiber := baseChangeHom_genericFiberIso_hom_left _ _ (by
    rw [genericι_normalization, Scheme.Hom.toNormalization_normalizationDesc])

/-- The lift out of the normalization model has the canonical morphism out of the relative
normalization as underlying morphism. -/
@[simp]
lemma normalizationLift_hom (f : N ⟶ M) [IsIntegralHom f.hom] :
    (normalizationLift f).hom =
      M.genericι.normalizationDesc N.genericι f.hom (genericι_hom f).symm :=
  (rfl)

/-- The lift out of the normalization model is a morphism over `M`. -/
@[reassoc (attr := simp)]
lemma normalizationLift_comp (f : N ⟶ M) [IsIntegralHom f.hom] :
    normalizationLift f ≫ f = M.normalizationHom :=
  Hom.ext (by simp)

/-- **The universal property of the normalization model: uniqueness.** Every morphism of models
from the normalization of `M` to a model `N` integral over `M`, lying over `M`, is the lift
`normalizationLift`. -/
theorem eq_normalizationLift {f : N ⟶ M} [IsIntegralHom f.hom] {g : M.normalization ⟶ N}
    (hg : g ≫ f = M.normalizationHom) : g = normalizationLift f := by
  refine Hom.ext (Scheme.Hom.normalization.hom_ext M.genericι _ _ f.hom ?_ ?_ ?_)
  · rw [← genericι_normalization, genericι_hom, genericι_hom]
  · rw [← comp_hom, hg, normalizationHom_hom]
  · rw [← comp_hom, normalizationLift_comp, normalizationHom_hom]

end Model

end TauCeti
