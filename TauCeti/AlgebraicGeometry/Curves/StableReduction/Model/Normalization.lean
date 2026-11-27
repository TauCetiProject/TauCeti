/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Normalization.IsIso
public import TauCeti.AlgebraicGeometry.Normalization.Normal
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Isomorphism
public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension

import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.RingTheory.IntegralClosure.SeparatingCoordinate
import TauCeti.RingTheory.LocalRing.ResidueField.Fiber
import TauCeti.RingTheory.Smooth.MinimalPrime

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
and over an arbitrary, possibly non-excellent, discrete valuation ring when `C` is smooth of
relative dimension one over `K` (`TauCeti.Model.isFinite_fromNormalization_genericι`). Over an
affine open `Spec A` of `X`, the special fibre `A ⧸ πA` then has dimension at most one, since the
special fibre of a model is no larger than its generic fibre
(`TauCeti.Model.relativeDimensionLE_toBase`), and at every minimal prime of `A[1/π]` the
residue field is a function field of one variable over `K` with one-dimensional Kähler
differentials (`TauCeti.transcendental_and_finrank_kaehlerDifferential_residueField_eq_one`); these
are the hypotheses of the ring-level finiteness theorem
`TauCeti.finite_integralClosure_of_forall_transcendental_and_finrank_kaehlerDifferential_eq_one`.

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
* `TauCeti.Model.isNormalScheme_normalization_of_smooth`: normalizing a model with smooth
  generic fibre gives a normal total space, including for disconnected generic fibres.
* `TauCeti.Model.isFinite_fromNormalization_genericι`: the normalization of a model whose
  generic fibre is smooth of relative dimension one is finite, over any discrete valuation ring.

## References

* The Stacks Project, Tag 035H (relative normalization) and Lemma 29.53.5 (03GV).
* The Stacks Project, Lemma 55.8.2 (0C2T), for the finiteness of the normalization.
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

/-- The normalization of a model with smooth generic fibre is normal, even if that fibre is
disconnected. No excellence or finiteness of normalization hypothesis is needed. -/
theorem isNormalScheme_normalization_of_smooth [Smooth toK] :
    AlgebraicGeometry.IsNormalScheme M.genericι.normalization := by
  have := AlgebraicGeometry.IsRegular.of_smooth toK
  exact M.genericι.isNormalScheme_normalization

section Finite

open _root_.IsLocalRing

variable {M} {U : M.total.Opens}

/-- Over an affine open `U` of the total space of a model of relative dimension at most one, the
special fibre `Γ(U) ⧸ π Γ(U)` has Krull dimension at most one. -/
private lemma krullDimLE_sections_quotient [AlgebraicGeometry.RelativeDimensionLE 1 M.toBase]
    (hU : IsAffineOpen U) {π : R} (hπ : Irreducible π) :
    letI := M.toBase.sectionsAlgebra U
    Ring.KrullDimLE 1 (Γ(M.total, U) ⧸ Ideal.span {algebraMap R Γ(M.total, U) π}) := by
  let := M.toBase.sectionsAlgebra U
  -- `Spec Γ(U) ⟶ Spec R` is the restriction of the structure morphism to `U`.
  have : AlgebraicGeometry.RelativeDimensionLE 1
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(M.total, U)))) :=
    M.toBase.fromSpec_toSpec hU ▸ inferInstance
  have hdim :=
    (AlgebraicGeometry.relativeDimensionLE_SpecMap_iff R Γ(M.total, U)).mp this (maximalIdeal R)
  -- The fibre over the closed point is `Γ(U) ⧸ 𝔪 Γ(U)`, and `𝔪 = (π)`.
  have hmap : (maximalIdeal R).map (algebraMap R Γ(M.total, U)) =
      Ideal.span {algebraMap R Γ(M.total, U) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  rw [← hmap, Ring.krullDimLE_iff, ← ringKrullDim_eq_of_ringEquiv
    (Ideal.Fiber.algEquivQuotientMap (B := Γ(M.total, U)) (maximalIdeal R)).toRingEquiv]
  exact_mod_cast hdim

/-- The two maps from `R` to the sections of the generic fibre over `U ∩ C`, through the sections
of the total space over `U` and through the fraction field, agree. -/
private lemma appLE_comp_app_genericι (U : M.total.Opens) :
    (Scheme.ΓSpecIso (.of R)).inv ≫ M.toBase.appLE ⊤ U (le_top.trans M.toBase.preimage_top.ge) ≫
        M.genericι.app U =
      CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        toK.appLE ⊤ (M.genericι ⁻¹ᵁ U) (le_top.trans toK.preimage_top.ge) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [M.genericι_toBase, Scheme.Hom.comp_appLE]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]
  -- The two sides differ only in writing `⊤` as `Spec.map _ ⁻¹ᵁ ⊤`.
  rfl

/-- **The normalization of a model of a smooth curve is finite.** If the generic fibre `C` is
smooth of relative dimension one over `K`, then the normalization of the total space in `C` is
finite, over an arbitrary, possibly non-excellent, discrete valuation ring. -/
instance isFinite_fromNormalization_genericι [SmoothOfRelativeDimension 1 toK] :
    IsFinite M.genericι.fromNormalization := by
  have := M.isOpenImmersion_genericι
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [Scheme.Hom.isFinite_fromNormalization_iff]
  intro U hU
  -- Over the affine open `U`, set `A = Γ(U)` and `B = Γ(U ∩ C)` with their algebra structures
  -- over `R` and `K`; then `B = A[1/π]`, and the ring-level theorem applies.
  let := (M.genericι.app U).hom.toAlgebra
  let := M.toBase.sectionsAlgebra U
  let : Algebra R Γ(C, M.genericι ⁻¹ᵁ U) :=
    ((algebraMap Γ(M.total, U) _).comp (algebraMap R Γ(M.total, U))).toAlgebra
  have : IsScalarTower R Γ(M.total, U) Γ(C, M.genericι ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  let := toK.sectionsAlgebra (M.genericι ⁻¹ᵁ U)
  have : IsScalarTower R K Γ(C, M.genericι ⁻¹ᵁ U) :=
    .of_algebraMap_eq' <| by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, M.toBase.algebraMap_sections,
        toK.algebraMap_sections]
      exact congr(($(appLE_comp_app_genericι U)).hom)
  have : Algebra.FiniteType R Γ(M.total, U) := RingHom.finiteType_algebraMap.mp <|
    M.toBase.algebraMap_sections U ▸ M.toBase.finiteType_ΓSpecIso_inv_comp_appLE hU
  have := krullDimLE_sections_quotient (M := M) hU hπ
  have : IsLocalization.Away (algebraMap R Γ(M.total, U) π) Γ(C, M.genericι ⁻¹ᵁ U) := by
    refine M.genericι.isLocalization_app_of_inf_opensRange_eq hU.isCompact hU.isQuasiSeparated ?_
    -- The generic fibre is the basic open of the pullback of `π`.
    have hrange : M.genericι.opensRange =
        M.toBase ⁻¹ᵁ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π) := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.preimage_basicOpen_top,
        M.range_genericι_eq_basicOpen ((mem_maximalIdeal π).mpr hπ.not_isUnit) hπ.ne_zero]
    rw [hrange, M.toBase.algebraMap_sections]
    exact (Scheme.basicOpen_appLE _ _ _ _ _).symm
  have hB := toK.locally_isStandardSmoothOfRelativeDimension_sections 1 (hU.preimage M.genericι)
  have := SmoothOfRelativeDimension.smooth 1 toK
  have := AlgebraicGeometry.IsRegular.of_smooth toK
  exact finite_integralClosure_of_forall_transcendental_and_finrank_kaehlerDifferential_eq_one
    (K := K) (π := π) fun p _ hp ↦
      transcendental_and_finrank_kaehlerDifferential_residueField_eq_one hB p hp

end Finite

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
  exact forall₂_congr fun U _ ↦ and_iff_right (M.genericι.app_injective U)

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
