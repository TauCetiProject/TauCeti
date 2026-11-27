/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Blowup
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.RegularLocus
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Normal

/-!
# Normalized blowups of models of curves

Let `R` be a discrete valuation ring with fraction field `K`, and let `M` be a model over `R` of a
smooth curve `C` over `K`, with total space `X`. For a point `x` of the special fibre, typically a
closed point, the **normalized blowup** of `M` in `x` blows up `X` along the closure of `x`, with
its reduced structure, and then normalizes the result in the generic fibre. It is again a model of
`C`, proper when `M` is, its total space is normal with finitely many singular points, and when `X`
is normal the normalized blowup changes nothing away from the closure of `x`.

These are the steps of Lipman's resolution of the singularities of a normal model: starting from a
normal proper model, repeatedly take normalized blowups in its finitely many singular points until
the total space is regular. Over an arbitrary, possibly non-excellent, discrete valuation ring each
step is a model because the generic fibre is smooth
(`TauCeti.Model.isFinite_fromNormalization_genericι`).

The first step is that normalizing does nothing over a normal open `V` of `X`: over an affine open
`Spec A ⊆ V`, the generic fibre is `Spec A[1/π]` for a uniformizer `π`, and the normal ring `A` is
integrally closed in its localization `A[1/π]` at the nonzerodivisor `π`.

## Main definitions

* `TauCeti.Model.normalizedBlowup M x hx`: the normalized blowup of `M` in a point `x` of the
  special fibre, as a model of `C`.
* `TauCeti.Model.normalizedBlowupHom M x hx`: the normalized blowup morphism, as a morphism of
  models.

## Main results

* `TauCeti.Model.le_isoLocus_fromNormalization_genericι`: normalizing the total space in the
  generic fibre is an isomorphism over every normal open of the total space.
* `TauCeti.Model.isIso_normalizationHom`: normalizing a normal model changes nothing.
* `TauCeti.Model.isProper_normalizedBlowup`, `TauCeti.Model.isNormalScheme_normalizedBlowup` and
  `TauCeti.Model.finite_compl_regularLocus_normalizedBlowup`: a normalized blowup of a proper model
  is a proper normal model with finitely many singular points.
* `TauCeti.Model.centre_normalizedBlowupHom_subset`: a normalized blowup of a normal model in `x`
  is an isomorphism away from the closure of `x`.

## References

* The Stacks Project, Section 54.14 (resolution of two-dimensional schemes by normalized
  blowups, Theorem 0BGP) and Lemma 55.8.3 (0C2U).
* J. Lipman, *Desingularization of two-dimensional schemes*, Ann. of Math. (2) 107 (1978),
  151–207.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.3
  (desingularization of arithmetic surfaces).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable (M : Model R K C toK)

section Normal

/-- **Normalization changes nothing over the normal locus.** Over an open `V` of the total space
of a model `M` which is a normal scheme, the normalization of the total space in the generic fibre
is an isomorphism. -/
theorem le_isoLocus_fromNormalization_genericι (V : M.total.Opens) [IsNormalScheme V] :
    V ≤ M.genericι.fromNormalization.isoLocus := by
  intro y hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    M.total.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
  refine M.genericι.fromNormalization.mem_isoLocus_iff.mpr ⟨U, hyU, ?_⟩
  rw [Scheme.Hom.isIso_morphismRestrict_fromNormalization_iff _ hU]
  -- Over `U`, the generic fibre is `Spec Γ(X, U)[1/π]`, with `π` a nonzerodivisor.
  have := M.isOpenImmersion_genericι
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := (M.genericι.app U).hom.toAlgebra
  let := M.toBase.sectionsAlgebra U
  have := M.isLocalization_away_app_genericι hU hπ
  -- The ring `Γ(X, U)` is normal, since `U` is an open of the normal scheme `V`.
  have : IsNormalScheme U := .of_isOpenImmersion (M.total.homOfLE (show U ≤ V from hUV))
  have : IsNormalScheme (Spec Γ(M.total, U)) := .of_isOpenImmersion hU.isoSpec.inv
  have : IsIntegrallyClosedIn Γ(M.total, U) Γ(C, M.genericι ⁻¹ᵁ U) := by
    refine Spec.isIntegrallyClosedIn_of_presheaf_map_leTop_bijective
      (Submonoid.powers_le.mpr (M.algebraMap_mem_nonZeroDivisors_sections hU hπ.ne_zero)) ⊤
      (fun p _ ↦ (isNormalScheme_Spec_iff_forall_localization _).mp ‹_› p.asIdeal) ?_
    -- Restriction from `Spec Γ(X, U)` to its top open is the identity.
    rw [show (⊤ : (Spec (.of Γ(M.total, U))).Opens).leTop = 𝟙 ⊤ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    exact ConcreteCategory.bijective_of_isIso _
  refine ⟨M.genericι.app_injective U, fun s hs ↦ ?_⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hs
  exact ⟨a, rfl⟩

/-- **Normalizing a normal model changes nothing.** If the total space of `M` is normal, the
normalization morphism of models is an isomorphism. -/
instance isIso_normalizationHom [IsFinite M.genericι.fromNormalization]
    [IsNormalScheme M.total] : IsIso M.normalizationHom := by
  rw [isIso_iff_isIso_hom, normalizationHom_hom, ← Scheme.Hom.isoLocus_eq_top_iff, eq_top_iff]
  exact M.le_isoLocus_fromNormalization_genericι ⊤

end Normal

section NormalizedBlowup

variable {x : M.total}

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
  (M.blowup (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩)
    (M.disjoint_range_genericι_support_vanishingIdeal hx)).normalization

/-- **The normalized blowup morphism.** The normalization morphism followed by the blowup
morphism, as a morphism of models from the normalized blowup of `M` to `M`. -/
def normalizedBlowupHom (x : M.total) (hx : M.toBase x = closedPoint R) :
    M.normalizedBlowup x hx ⟶ M :=
  normalizationHom _ ≫ blowupHom _ _ _

/-- The normalized blowup morphism of models is the normalization morphism followed by the
blowup morphism of total spaces. -/
@[simp]
lemma normalizedBlowupHom_hom (hx : M.toBase x = closedPoint R) :
    (M.normalizedBlowupHom x hx).hom =
      (M.blowup (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩)
        (M.disjoint_range_genericι_support_vanishingIdeal hx)).genericι.fromNormalization ≫
        (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).blowupToBase := by
  simp [normalizedBlowupHom]

/-- The normalized blowup of a proper model is a proper model. -/
instance isProper_normalizedBlowup [M.IsProper] (hx : M.toBase x = closedPoint R) :
    (M.normalizedBlowup x hx).IsProper :=
  isProper_normalization _

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
  set I := Scheme.IdealSheafData.vanishingIdeal (X := M.total) ⟨closure {x}, isClosed_closure⟩
  set N := M.blowup I (M.disjoint_range_genericι_support_vanishingIdeal hx)
  -- Over the complement `W` of the centre the blowup is an isomorphism, so its preimage in the
  -- blowup is normal and the normalization changes nothing over it.
  let W := I.support.compl
  have : IsNormalScheme (I.blowupToBase ⁻¹ᵁ W) := .of_isOpenImmersion (I.blowupToBase ∣_ W)
  have h := (Scheme.Hom.le_isoLocus_iff _).mp
    (N.le_isoLocus_fromNormalization_genericι (I.blowupToBase ⁻¹ᵁ W))
  have hW : IsIso ((M.normalizedBlowupHom x hx).hom ∣_ W) := by
    rw [normalizedBlowupHom_hom, morphismRestrict_comp]
    exact IsIso.comp_isIso' h I.isIso_blowupToBase_restrict_compl_support
  have h := (Scheme.Hom.disjoint_centre_iff _).mpr hW
  rwa [TopologicalSpace.Closeds.coe_compl, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_mk, Set.disjoint_compl_left_iff_subset] at h

end NormalizedBlowup

end Model

end TauCeti
