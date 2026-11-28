/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Blowup
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.CartierDivisor
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.RegularLocus

import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Normalized blowups of models of curves

Let `R` be a discrete valuation ring with fraction field `K`, and let `M` be a model over `R` of a
scheme `C` over `K`, with total space `X`. Given an ideal sheaf `I` on `X` whose support `V(I)` is
disjoint from the generic fibre `C ⊆ X`, when the normalization of the blowup `M.blowup I hC` in
`C` is finite — in particular, unconditionally over any discrete valuation ring whenever `C` is
smooth of relative dimension `1` over `K` (`TauCeti.Model.isFinite_fromNormalization_genericι`) —
the **normalized blowup** `M.normalizedBlowupOfIdeal I hC` is `(M.blowup I hC).normalization`,
with canonical morphism `M.normalizedBlowupOfIdealHom I hC : M.normalizedBlowupOfIdeal I hC ⟶ M`.

In particular, for a smooth curve `C` and a point `x` of the special fibre, typically a closed
point, the **normalized blowup** `M.normalizedBlowup x hx` of `M` in `x` blows up `X` along the
closure of `x`, with its reduced structure, and normalizes the result in the generic fibre. It is
again a model of `C`, proper when `M` is, its total space is normal with finitely many singular
points, and when `X` is normal the normalized blowup changes nothing away from the closure of `x`.

Iterating normalized blowups in non-regular closed points of the special fibre is Lipman's and
Liu's resolution procedure producing a regular proper model of a smooth proper curve over `K`.
Normalizing does nothing over a normal open of `X`
(`TauCeti.Model.le_isoLocus_fromNormalization_genericι`), so when `X` is normal the normalized
blowup is the blowup away from the closure of `x`.

## Main definitions

* `TauCeti.Model.normalizedBlowupOfIdeal M I hC`: the normalized blowup of `M` along an ideal
  sheaf `I` supported away from the generic fibre, as a model of `C`.
* `TauCeti.Model.normalizedBlowupOfIdealHom M I hC`: the normalized-blowup morphism for an ideal
  sheaf `I`, as a morphism of models.
* `TauCeti.Model.normalizedBlowupOfIdealLift`: the unique factorization through
  `M.normalizedBlowupOfIdeal I hC` of a morphism from a normal model along which `I` pulls back
  to an effective Cartier divisor.
* `TauCeti.Model.normalizedBlowup M x hx`: the normalized blowup of `M` in a point `x` of the
  special fibre, as a model of `C`.
* `TauCeti.Model.normalizedBlowupHom M x hx`: the normalized blowup morphism at `x`, as a morphism
  of models.

## Main results

* `TauCeti.Model.isEffectiveCartier_comap_normalizedBlowupOfIdealHom`: the centre `I` pulls back
  to an effective Cartier divisor on `M.normalizedBlowupOfIdeal I hC`.
* `TauCeti.Model.isIso_normalizedBlowupOfIdealHom_iff`: when `M.total` is normal,
  `M.normalizedBlowupOfIdealHom I hC` is an isomorphism if and only if `I` is already an effective
  Cartier divisor.
* `TauCeti.Model.centre_normalizedBlowupOfIdealHom_subset`: a normalized blowup of a normal model
  along `I` is an isomorphism away from `I.support`.
* `TauCeti.Model.normalizedBlowupOfIdealLift_normalizedBlowupOfIdealHom` and
  `TauCeti.Model.eq_normalizedBlowupOfIdealLift`: the universal property of the normalized blowup
  along `I` for morphisms from normal models.
* `TauCeti.Model.isNormalScheme_normalizedBlowup` and
  `TauCeti.Model.finite_compl_regularLocus_normalizedBlowup`: a normalized blowup of a model in
  `x` is a normal model with finitely many singular points (and proper when `M` is).
* `TauCeti.Model.centre_normalizedBlowupHom_subset`: a normalized blowup of a normal model in `x`
  is an isomorphism away from the closure of `x`.

## References

* The Stacks Project, Section 54.14 (resolution of two-dimensional schemes by normalized
  blowups, Theorem 0BGP) and Lemmas 55.8.2 (0C2T) and 55.8.3 (0C2U).
* J. Lipman, *Desingularization of two-dimensional schemes*, Ann. of Math. (2) 107 (1978),
  151–207.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.3
  and Chapter 10 (desingularization of arithmetic surfaces).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

section NormalizedBlowupOfIdeal

variable (M : Model R K C toK) (I : M.total.IdealSheafData)
  (hC : Disjoint (Set.range M.genericι) (I.support : Set M.total))
  [IsFinite (M.blowup I hC).genericι.fromNormalization]

/-- **The normalized blowup of a model** along an ideal sheaf `I` supported away from the generic
fibre: the normalization of `M.blowup I hC` in `C`. When `SmoothOfRelativeDimension 1 toK`, the
finiteness hypothesis is synthesized automatically over any discrete valuation ring `R`. -/
abbrev normalizedBlowupOfIdeal : Model R K C toK :=
  (M.blowup I hC).normalization

/-- **The normalized-blowup morphism of models** `M.normalizedBlowupOfIdeal I hC ⟶ M`. -/
def normalizedBlowupOfIdealHom : M.normalizedBlowupOfIdeal I hC ⟶ M :=
  (M.blowup I hC).normalizationHom ≫ M.blowupHom I hC

/-- The normalized-blowup morphism of models factors as the normalization morphism followed by the
blowup morphism. -/
@[reassoc]
lemma normalizedBlowupOfIdealHom_eq :
    M.normalizedBlowupOfIdealHom I hC = (M.blowup I hC).normalizationHom ≫ M.blowupHom I hC :=
  (rfl)

/-- The normalized-blowup morphism of models has the composite of the normalization and blowup
morphisms as its underlying scheme morphism. -/
@[simp]
lemma normalizedBlowupOfIdealHom_hom :
    (M.normalizedBlowupOfIdealHom I hC).hom =
      (M.blowup I hC).genericι.fromNormalization ≫ I.blowupToBase := by
  rw [normalizedBlowupOfIdealHom_eq, comp_hom, normalizationHom_hom, blowupHom_hom]

/-- The normalized-blowup morphism of models is proper on total spaces. -/
instance isProper_normalizedBlowupOfIdealHom_hom :
    AlgebraicGeometry.IsProper (M.normalizedBlowupOfIdealHom I hC).hom := by
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  rw [normalizedBlowupOfIdealHom_hom]
  infer_instance

/-- The centre `I` pulls back to an effective Cartier divisor on the normalized blowup. -/
theorem isEffectiveCartier_comap_normalizedBlowupOfIdealHom :
    (I.comap (M.normalizedBlowupOfIdealHom I hC).hom).IsEffectiveCartier := by
  rw [normalizedBlowupOfIdealHom_eq, comp_hom, Scheme.IdealSheafData.comap_comp, blowupHom_hom]
  exact isEffectiveCartier_comap_hom (M.blowup I hC).normalizationHom
    I.isEffectiveCartier_comap_blowupToBase

/-- When the total space of `M` is normal, the normalized-blowup morphism is an isomorphism if and
only if the centre `I` is already an effective Cartier divisor on `M.total`. -/
theorem isIso_normalizedBlowupOfIdealHom_iff [IsNormalScheme M.total] :
    IsIso (M.normalizedBlowupOfIdealHom I hC) ↔ I.IsEffectiveCartier := by
  refine ⟨fun _ ↦ ?_, fun hI ↦ ?_⟩
  · have : IsIso (M.normalizedBlowupOfIdealHom I hC).hom := (isIso_iff_isIso_hom _).mp ‹_›
    have hEC := (M.isEffectiveCartier_comap_normalizedBlowupOfIdealHom I hC).comap
      (inv (M.normalizedBlowupOfIdealHom I hC).hom)
    rwa [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id] at hEC
  · have : IsIso (M.blowupHom I hC) := (M.isIso_blowupHom_iff I hC).mpr hI
    have : IsIso (M.blowupHom I hC).hom := (isIso_iff_isIso_hom _).mp ‹_›
    have : IsNormalScheme (M.blowup I hC).total :=
      .of_isOpenImmersion (M.blowupHom I hC).hom
    rw [normalizedBlowupOfIdealHom_eq]
    infer_instance

/-- **A normalized blowup of a normal model changes nothing away from its centre.** If the total
space of `M` is normal, the normalized blowup of `M` along `I` is an isomorphism over the
complement of `I.support`. -/
theorem centre_normalizedBlowupOfIdealHom_subset [IsNormalScheme M.total] :
    (M.normalizedBlowupOfIdealHom I hC).hom.centre ⊆ (I.support : Set M.total) := by
  -- Over the complement `W` of the centre the blowup is an isomorphism, so its preimage in the
  -- blowup is normal and the normalization changes nothing over it.
  let W := I.support.compl
  have : IsNormalScheme (I.blowupToBase ⁻¹ᵁ W) := .of_isOpenImmersion (I.blowupToBase ∣_ W)
  have h := (Scheme.Hom.le_isoLocus_iff _).mp
    ((M.blowup I hC).le_isoLocus_fromNormalization_genericι (I.blowupToBase ⁻¹ᵁ W))
  have hW : IsIso ((M.normalizedBlowupOfIdealHom I hC).hom ∣_ W) := by
    rw [normalizedBlowupOfIdealHom_hom, morphismRestrict_comp]
    exact IsIso.comp_isIso' h I.isIso_blowupToBase_restrict_compl_support
  have hdisj := (Scheme.Hom.disjoint_centre_iff _).mpr hW
  rwa [TopologicalSpace.Closeds.coe_compl, Set.disjoint_compl_left_iff_subset] at hdisj

variable {M I hC} {N : Model R K C toK}

/-- **The universal property of the normalized blowup: the lift.** A morphism of models
`f : N ⟶ M` from a normal model `N` along which `I` pulls back to an effective Cartier divisor
factors through `M.normalizedBlowupOfIdeal I hC`. -/
def normalizedBlowupOfIdealLift [IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    N ⟶ M.normalizedBlowupOfIdeal I hC :=
  normalizationLift (blowupLift (hC := hC) f hf)

/-- The lift to the normalized blowup is the lift to the normalization of the lift to the
blowup. -/
lemma normalizedBlowupOfIdealLift_eq [IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    normalizedBlowupOfIdealLift (hC := hC) f hf =
      normalizationLift (blowupLift (hC := hC) f hf) :=
  (rfl)

/-- Composing the lift to the normalized blowup with the normalization morphism recovers the lift to
the blowup. -/
@[reassoc (attr := simp)]
lemma normalizedBlowupOfIdealLift_normalizationHom
    [IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    normalizedBlowupOfIdealLift (hC := hC) f hf ≫ (M.blowup I hC).normalizationHom =
      blowupLift (hC := hC) f hf :=
  normalizationLift_normalizationHom _

/-- The lift to the normalized blowup commutes with `M.normalizedBlowupOfIdealHom I hC`. -/
@[reassoc (attr := simp)]
lemma normalizedBlowupOfIdealLift_normalizedBlowupOfIdealHom
    [IsNormalScheme N.total]
    (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    normalizedBlowupOfIdealLift (hC := hC) f hf ≫ M.normalizedBlowupOfIdealHom I hC = f := by
  rw [normalizedBlowupOfIdealLift_eq, normalizedBlowupOfIdealHom_eq, ← Category.assoc,
    normalizationLift_normalizationHom, blowupLift_blowupHom]

/-- **The universal property of the normalized blowup: uniqueness.** Every morphism of models
from a normal model `N` to `M.normalizedBlowupOfIdeal I hC` lying over `f : N ⟶ M` equals
`normalizedBlowupOfIdealLift`. -/
theorem eq_normalizedBlowupOfIdealLift [IsNormalScheme N.total]
    {f : N ⟶ M} (hf : (I.comap f.hom).IsEffectiveCartier)
    {g : N ⟶ M.normalizedBlowupOfIdeal I hC}
    (hg : g ≫ M.normalizedBlowupOfIdealHom I hC = f) :
    g = normalizedBlowupOfIdealLift f hf := by
  refine eq_normalizationLift (eq_blowupLift hf ?_)
  simpa [normalizedBlowupOfIdealHom_eq, Category.assoc] using hg

end NormalizedBlowupOfIdeal

section NormalizedBlowup

variable (M : Model R K C toK) {x : M.total}

/-- The closure of a point of the special fibre of a model does not meet the generic fibre: it is
the support of the ideal sheaf of the centre of the normalized blowup in that point. -/
lemma disjoint_range_genericι_support_vanishingIdeal (hx : M.toBase x = closedPoint R) :
    Disjoint (Set.range M.genericι)
      ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).support :
        Set M.total) := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
    M.range_genericι_eq_setOf_base_ne_closedPoint]
  -- The special fibre is closed and contains `x`, hence the closure of `x`.
  have hcl : closure {x} ⊆ M.toBase ⁻¹' {closedPoint R} :=
    closure_minimal (Set.singleton_subset_iff.mpr hx)
      ((isClosed_singleton_closedPoint R).preimage M.toBase.continuous)
  exact Set.disjoint_left.mpr fun y hy hyx ↦ hy (hcl hyx)

variable [SmoothOfRelativeDimension 1 toK]

/-- **The normalized blowup of a model in a point of its special fibre.** For a point `x` of the
special fibre of a model `M` of a smooth curve, blow up the total space along the closure of `x`,
with its reduced structure, and normalize the result in the generic fibre. -/
abbrev normalizedBlowup (x : M.total) (hx : M.toBase x = closedPoint R) : Model R K C toK :=
  M.normalizedBlowupOfIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩)
    (M.disjoint_range_genericι_support_vanishingIdeal hx)

/-- **The normalized blowup morphism.** The normalization morphism followed by the blowup
morphism, as a morphism of models from the normalized blowup of `M` to `M`. -/
def normalizedBlowupHom (x : M.total) (hx : M.toBase x = closedPoint R) :
    M.normalizedBlowup x hx ⟶ M :=
  M.normalizedBlowupOfIdealHom _ _

/-- The normalized blowup morphism of models is the normalization morphism followed by the
blowup morphism of total spaces. -/
@[simp]
lemma normalizedBlowupHom_hom (hx : M.toBase x = closedPoint R) :
    (M.normalizedBlowupHom x hx).hom =
      (M.blowup (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩)
        (M.disjoint_range_genericι_support_vanishingIdeal hx)).genericι.fromNormalization ≫
        (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).blowupToBase := by
  simp [normalizedBlowupHom]

/-- The total space of a normalized blowup is normal. -/
instance isNormalScheme_normalizedBlowup (hx : M.toBase x = closedPoint R) :
    IsNormalScheme (M.normalizedBlowup x hx).total := by
  have := SmoothOfRelativeDimension.smooth 1 toK
  exact isNormalScheme_normalization_of_smooth _

/-- The total space of a normalized blowup has only finitely many non-regular points. -/
theorem finite_compl_regularLocus_normalizedBlowup (hx : M.toBase x = closedPoint R) :
    (M.normalizedBlowup x hx).total.regularLocusᶜ.Finite :=
  finite_compl_regularLocus_normalization _

/-- **A normalized blowup of a normal model changes nothing away from its centre.** If the total
space of `M` is normal, the normalized blowup of `M` in a point `x` of the special fibre is an
isomorphism over the complement of the closure of `x`; for a closed point `x`, over the complement
of `x`. -/
theorem centre_normalizedBlowupHom_subset [IsNormalScheme M.total]
    (hx : M.toBase x = closedPoint R) :
    (M.normalizedBlowupHom x hx).hom.centre ⊆ closure {x} := by
  have h := M.centre_normalizedBlowupOfIdealHom_subset
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩)
    (M.disjoint_range_genericι_support_vanishingIdeal hx)
  simpa [normalizedBlowupHom] using h

end NormalizedBlowup

end Model

end TauCeti
