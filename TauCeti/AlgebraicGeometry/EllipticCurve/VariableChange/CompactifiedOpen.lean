/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Groupoid
public import TauCeti.AlgebraicGeometry.EllipticCurve.Invariants.Hartogs
public import TauCeti.AlgebraicGeometry.Restrict

/-!
# The smooth-or-nodal open of the Weierstrass groupoid

The open `U = D(c₄) ∪ D(Δ)` of the universal cubic atlas is invariant under changes of
variables. Its inverse images under the source and target projections coincide, so both
projections restrict to smooth surjections onto `U`. Identity arrows and inversion restrict
as well. The boundary `Δ = 0, c₄ ≠ 0` is retained; this is not the discriminant-open atlas.

Hartogs extension also applies to this open in the arrow scheme. Thus regular functions on
the restricted arrow scheme extend uniquely to the full arrow ring. In particular, a
polynomial's weight-`k` transformation law can be checked after restriction to this open.
This is the equivariance comparison needed when extending invariant functions across the
cuspidal locus. No quotient stack or descent of the Hodge line is constructed here.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3.
* P. Goerss, *Topological modular forms [after Hopkins, Miller, and Lurie]*, §3.1.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.WeierstrassHopfAlgebroid

open _root_.WeierstrassCurve WeierstrassChange.ChangeRing

/-- The smooth-or-nodal locus has the same inverse image under source and target. -/
@[simp]
theorem target_preimage_compactifiedOpen :
    target ⁻¹ᵁ Universal.compactifiedOpen = source ⁻¹ᵁ Universal.compactifiedOpen := by
  rw [SetLike.ext_iff]
  intro p
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage]
  erw [Universal.mem_compactifiedOpen, Universal.mem_compactifiedOpen]
  simp only [source_def, target_def, Spec.map_apply]
  have h := congrArg (fun I : Ideal ArrowRing ↦ I ≤ p.asIdeal)
    (span_variableChange_c₄_Δ
      (Universal.curve.map (algebraMap (MvPolynomial Coeff ℤ) ArrowRing))
      (universalChange (MvPolynomial Coeff ℤ)))
  rw [← map_rightUnit, map_c₄, map_Δ, map_c₄, map_Δ] at h
  simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff,
    SetLike.mem_coe] at h
  tauto

/-- Arrows whose source (equivalently, target) lies in the smooth-or-nodal cubic atlas. -/
def compactifiedArrowOpen : (Spec (.of ArrowRing)).Opens :=
  source ⁻¹ᵁ Universal.compactifiedOpen

/-- Membership in the restricted arrow scheme is the condition on the source. -/
@[simp]
theorem mem_compactifiedArrowOpen {p : PrimeSpectrum ArrowRing} :
    p ∈ compactifiedArrowOpen ↔ source p ∈ Universal.compactifiedOpen := Iff.rfl

/-- The source projection on the smooth-or-nodal atlas. -/
def compactifiedSource : compactifiedArrowOpen.toScheme ⟶ Universal.compactifiedOpen :=
  source ∣_ Universal.compactifiedOpen

/-- The target projection on the same restricted arrow scheme. -/
def compactifiedTarget : compactifiedArrowOpen.toScheme ⟶ Universal.compactifiedOpen :=
  target.resLE _ _ target_preimage_compactifiedOpen.symm.le

/-- The restricted source is the base change of the full source projection. -/
theorem isPullback_compactifiedSource :
    IsPullback compactifiedSource compactifiedArrowOpen.ι Universal.compactifiedOpen.ι source :=
  isPullback_morphismRestrict source Universal.compactifiedOpen

/-- The restricted target is the base change of the full target projection. -/
theorem isPullback_compactifiedTarget :
    IsPullback compactifiedTarget compactifiedArrowOpen.ι Universal.compactifiedOpen.ι target :=
  target.isPullback_resLE_of_eq _ target_preimage_compactifiedOpen.symm

/-- Restriction of the source commutes with the inclusions of the opens. -/
@[reassoc (attr := simp)]
theorem compactifiedSource_ι :
    compactifiedSource ≫ Universal.compactifiedOpen.ι = compactifiedArrowOpen.ι ≫ source :=
  isPullback_compactifiedSource.w

/-- Restriction of the target commutes with the inclusions of the opens. -/
@[reassoc (attr := simp)]
theorem compactifiedTarget_ι :
    compactifiedTarget ≫ Universal.compactifiedOpen.ι = compactifiedArrowOpen.ι ≫ target :=
  isPullback_compactifiedTarget.w

/-- The restricted source remains smooth of relative dimension four. -/
instance smoothOfRelativeDimension_compactifiedSource :
    SmoothOfRelativeDimension 4 compactifiedSource :=
  MorphismProperty.of_isPullback isPullback_compactifiedSource.flip inferInstance

/-- The restricted target remains smooth of relative dimension four. -/
instance smoothOfRelativeDimension_compactifiedTarget :
    SmoothOfRelativeDimension 4 compactifiedTarget :=
  MorphismProperty.of_isPullback isPullback_compactifiedTarget.flip inferInstance

/-- The restricted source is smooth. -/
instance smooth_compactifiedSource : Smooth compactifiedSource :=
  SmoothOfRelativeDimension.smooth 4 _

/-- The restricted target is smooth. -/
instance smooth_compactifiedTarget : Smooth compactifiedTarget :=
  SmoothOfRelativeDimension.smooth 4 _

/-- Every curve in the open remains the source of an arrow in the open. -/
instance surjective_compactifiedSource : Surjective compactifiedSource :=
  MorphismProperty.of_isPullback isPullback_compactifiedSource.flip inferInstance

/-- Every curve in the open remains the target of an arrow in the open. -/
instance surjective_compactifiedTarget : Surjective compactifiedTarget :=
  MorphismProperty.of_isPullback isPullback_compactifiedTarget.flip inferInstance

/-- Identity arrows remain in the restricted arrow scheme. -/
@[simp]
theorem identity_preimage_compactifiedArrowOpen :
    identity ⁻¹ᵁ compactifiedArrowOpen = Universal.compactifiedOpen := by
  rw [compactifiedArrowOpen, ← Scheme.Hom.comp_preimage, identity_source]
  simp

/-- Inversion preserves the restricted arrow scheme. -/
@[simp]
theorem inversion_preimage_compactifiedArrowOpen :
    inversion.hom ⁻¹ᵁ compactifiedArrowOpen = compactifiedArrowOpen := by
  rw [compactifiedArrowOpen, ← Scheme.Hom.comp_preimage, inversion_hom_source,
    target_preimage_compactifiedOpen]

/-- The identity section on the smooth-or-nodal atlas. -/
def compactifiedIdentity : Universal.compactifiedOpen.toScheme ⟶ compactifiedArrowOpen :=
  identity.resLE _ _ identity_preimage_compactifiedArrowOpen.symm.le

/-- The restricted identity section commutes with the inclusions. -/
@[reassoc (attr := simp)]
theorem compactifiedIdentity_ι :
    compactifiedIdentity ≫ compactifiedArrowOpen.ι = Universal.compactifiedOpen.ι ≫ identity :=
  Scheme.Hom.resLE_comp_ι _ _

/-- Identity arrows on the open have the original curve as source. -/
@[simp]
theorem compactifiedIdentity_source : compactifiedIdentity ≫ compactifiedSource = 𝟙 _ := by
  rw [← cancel_mono Universal.compactifiedOpen.ι]
  simp [Category.assoc]

/-- Identity arrows on the open have the original curve as target. -/
@[simp]
theorem compactifiedIdentity_target : compactifiedIdentity ≫ compactifiedTarget = 𝟙 _ := by
  rw [← cancel_mono Universal.compactifiedOpen.ι]
  simp [Category.assoc]

/-- Inversion on the restricted arrow scheme. -/
def compactifiedInversion : compactifiedArrowOpen.toScheme ≅ compactifiedArrowOpen :=
  (Spec (.of ArrowRing)).isoOfEq inversion_preimage_compactifiedArrowOpen.symm ≪≫
    inversion.hom.preimageIso compactifiedArrowOpen

/-- Restricted inversion agrees with inversion on the full arrow scheme. -/
@[reassoc (attr := simp)]
theorem compactifiedInversion_hom_ι :
    compactifiedInversion.hom ≫ compactifiedArrowOpen.ι =
      compactifiedArrowOpen.ι ≫ inversion.hom := by
  simp [compactifiedInversion]

/-- Inversion exchanges the restricted source and target. -/
@[reassoc (attr := simp)]
theorem compactifiedInversion_hom_source :
    compactifiedInversion.hom ≫ compactifiedSource = compactifiedTarget := by
  rw [← cancel_mono Universal.compactifiedOpen.ι]
  simp

/-- Inversion exchanges the restricted target and source. -/
@[reassoc (attr := simp)]
theorem compactifiedInversion_hom_target :
    compactifiedInversion.hom ≫ compactifiedTarget = compactifiedSource := by
  rw [← cancel_mono Universal.compactifiedOpen.ι]
  simp

/-- Inverting an arrow in the open twice returns that arrow. -/
@[simp]
theorem compactifiedInversion_hom_comp_self :
    compactifiedInversion.hom ≫ compactifiedInversion.hom = 𝟙 _ := by
  rw [← cancel_mono compactifiedArrowOpen.ι]
  simp [Category.assoc]

/-- Restricted inversion is its own inverse. -/
@[simp]
theorem compactifiedInversion_inv : compactifiedInversion.inv = compactifiedInversion.hom := by
  rw [← cancel_epi compactifiedInversion.hom]
  simp

/-- Inversion on the open fixes identity arrows. -/
@[simp]
theorem compactifiedIdentity_inversion_hom :
    compactifiedIdentity ≫ compactifiedInversion.hom = compactifiedIdentity := by
  rw [← cancel_mono compactifiedArrowOpen.ι]
  simp [Category.assoc]

/-- Hartogs extension on the restricted arrow scheme: restriction of global functions is
an isomorphism, not merely injective. -/
instance isIso_appTop_compactifiedArrowOpen_ι : IsIso compactifiedArrowOpen.ι.appTop := by
  have : IsIso (Limits.pullback.fst source Universal.compactifiedOpen.ι).appTop := by
    rw [source_def]
    exact Universal.isIso_appTop_pullback_compactifiedOpen ArrowRing
  have : IsIso (pullbackRestrictIsoRestrict source Universal.compactifiedOpen).inv.appTop :=
    inferInstanceAs
      (IsIso ((pullbackRestrictIsoRestrict source Universal.compactifiedOpen).inv.app ⊤))
  unfold compactifiedArrowOpen
  rw [← pullbackRestrictIsoRestrict_inv_fst source Universal.compactifiedOpen,
    Scheme.Hom.comp_appTop]
  infer_instance

/-- Restriction identifies the full arrow ring with the global functions on its
smooth-or-nodal open. -/
def compactifiedArrowSectionsEquiv : ArrowRing ≃+* Γ(compactifiedArrowOpen, ⊤) :=
  ((Scheme.ΓSpecIso (.of ArrowRing)).symm ≪≫
    asIso compactifiedArrowOpen.ι.appTop).commRingCatIsoToRingEquiv

/-- The Hartogs isomorphism sends an arrow polynomial to its restriction. -/
@[simp]
theorem compactifiedArrowSectionsEquiv_apply (f : ArrowRing) :
    compactifiedArrowSectionsEquiv f =
      compactifiedArrowOpen.ι.appTop ((Scheme.ΓSpecIso (.of ArrowRing)).inv f) := (rfl)

end TauCeti.WeierstrassHopfAlgebroid

namespace WeierstrassCurve

open TauCeti.WeierstrassHopfAlgebroid TauCeti.WeierstrassChange.ChangeRing

/-- A polynomial satisfies the weight-`k` transformation law on the full cubic groupoid
if and only if its regular sections satisfy that law on the smooth-or-nodal arrow open.
Thus Hartogs extension does not introduce extra polynomial invariants at the cusp. -/
theorem isIntegralModularForm_iff_compactifiedArrowSections {k : ℕ}
    {f : MvPolynomial Coeff ℤ} : IsIntegralModularForm k f ↔
      compactifiedArrowSectionsEquiv (rightUnit f) =
        compactifiedArrowSectionsEquiv (↑(universalChange (MvPolynomial Coeff ℤ)).u⁻¹) ^ k *
          compactifiedArrowSectionsEquiv
            (algebraMap (MvPolynomial Coeff ℤ) ArrowRing f) := by
  rw [isIntegralModularForm_iff_rightUnit]
  simp only [← map_pow, ← map_mul, EmbeddingLike.apply_eq_iff_eq]

end WeierstrassCurve
