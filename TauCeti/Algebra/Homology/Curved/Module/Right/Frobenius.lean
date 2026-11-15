/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Exact
public import TauCeti.CategoryTheory.Exact.Frobenius

/-!
# The Frobenius structure on curved right modules

For the graded-split exact structure, the relatively projective and injective objects are
exactly the contractible modules. A contraction gives extensions and lifts by taking the
closed boundary of its composite with a graded retraction or section. Cones of identities
provide enough such objects.

No centrality of the curvature or linearity of the differential over the algebra is assumed.
The splittings used here are graded right-linear maps, while their closed boundaries commute
with the curved differentials.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Frobenius`: the extension, lift,
  and retract arguments adapt its componentwise split Frobenius construction.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- Closed and homotopy objects keep the original module carrier in contraction formulas.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- A contractible module is injective relative to the graded-split exact structure. -/
theorem gradedSplitExact_isInjective_of_isZero_homotopy
    {P : CurvedDGRightModuleCat.{u, u, u} h} (hP : IsZero (DGHomotopyCategory.of R P)) :
    (gradedSplitExact (h := h)).isInjective
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P) := by
  obtain ⟨k, hk⟩ := (isZero_homotopy_iff_exists_contraction P).mp hP
  apply ExactStructure.isInjective_iff.mpr
  intro X Y i hi g
  let F := forgetDifferential (h := h)
  let : IsSplitMono (F.map i) := ExactStructure.isSplitMono_of_split_isInflation
    ((gradedSplitExact_isInflation_iff i).mp hi)
  let r := retraction (F.map i)
  have hr (x : (ForgetEnrichment.to _ X : CurvedDGRightModuleCat.{u, u, u} h)) :
      r.hom (closedHom i x) = x := by
    have hx := congrArg (fun l ↦ l.hom x) (IsSplitMono.id (F.map i))
    exact hx
  let t : dgRightModuleCochains (R := R) (A := A)
      (ℳ := (ForgetEnrichment.to _ Y).grading) (ℳN := P.grading) (-1) :=
    ⟨k.1.comp ((closedHom g).comp r.hom), dgRightModuleCochains.mem_iff.mpr
      (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
        have hx' : x ∈ (F.obj Y).grading.piece p := by
          simpa only [F, forgetDifferential, toGradedModuleCat_piece] using hx
        have hrx := GradedModuleCat.map_mem r hx'
        have hrx' : r.hom x ∈ (ForgetEnrichment.to _ X).grading p := by
          simpa only [F, forgetDifferential, toGradedModuleCat_piece] using hrx
        exact dgRightModuleCochains.map_mem k (closedHom_mem g hrx'))⟩
  refine ⟨closedHomotopyBoundary t, ?_⟩
  apply closedHom_ext
  intro x
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_closedHomotopyBoundary_apply]
  -- Evaluate the cochain's underlying composite with the graded retraction on original carriers.
  change P.differential (k.1 (closedHom g (r.hom (closedHom i x)))) +
    k.1 (closedHom g (r.hom ((ForgetEnrichment.to _ Y).differential (closedHom i x)))) = _
  erw [differential_closedHom i, hr, hr, ← differential_closedHom g]
  exact hk (closedHom g x)

/-- A contractible module is projective relative to the graded-split exact structure. -/
theorem gradedSplitExact_isProjective_of_isZero_homotopy
    {P : CurvedDGRightModuleCat.{u, u, u} h} (hP : IsZero (DGHomotopyCategory.of R P)) :
    (gradedSplitExact (h := h)).isProjective
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P) := by
  obtain ⟨k, hk⟩ := (isZero_homotopy_iff_exists_contraction P).mp hP
  apply ExactStructure.isProjective_iff.mpr
  intro X Y p hp g
  let F := forgetDifferential (h := h)
  let : IsSplitEpi (F.map p) := ExactStructure.isSplitEpi_of_split_isDeflation
    ((gradedSplitExact_isDeflation_iff p).mp hp)
  let s := section_ (F.map p)
  have hs (x : (ForgetEnrichment.to _ Y : CurvedDGRightModuleCat.{u, u, u} h)) :
      closedHom p (s.hom x) = x := by
    have hx := congrArg (fun l ↦ l.hom x) (IsSplitEpi.id (F.map p))
    exact hx
  let t : dgRightModuleCochains (R := R) (A := A)
      (ℳ := P.grading) (ℳN := (ForgetEnrichment.to _ X).grading) (-1) :=
    ⟨s.hom.comp ((closedHom g).comp k.1), dgRightModuleCochains.mem_iff.mpr
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        have hgx := closedHom_mem g (dgRightModuleCochains.map_mem k hx)
        have hgx' : closedHom g (k.1 x) ∈ (F.obj Y).grading.piece (q + -1) := by
          -- The graded forgetful functor's pieces are those of the original curved module.
          change closedHom g (k.1 x) ∈
            (toGradedModuleCat (ForgetEnrichment.to _ Y)).grading.piece (q + -1)
          rw [toGradedModuleCat_piece]
          exact hgx
        have hsx := GradedModuleCat.map_mem s hgx'
        -- Express the section's target degree in the same original-module grading.
        change s.hom (closedHom g (k.1 x)) ∈
          (toGradedModuleCat (ForgetEnrichment.to _ X)).grading.piece (q + -1) at hsx
        rw [toGradedModuleCat_piece] at hsx
        exact hsx)⟩
  refine ⟨closedHomotopyBoundary t, ?_⟩
  apply closedHom_ext
  intro x
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_closedHomotopyBoundary_apply]
  rw [map_add]
  -- Evaluate the lifted cochain's underlying composite with the graded section.
  change closedHom p ((ForgetEnrichment.to _ X).differential
    (s.hom (closedHom g (k.1 x)))) + closedHom p (s.hom (closedHom g (k.1 (P.differential x)))) = _
  erw [← differential_closedHom p, hs, hs, differential_closedHom g,
    ← map_add, hk]

/-- The injective presentation `M → Cone(id M) → M[1]`. -/
-- Exposed so that its middle and cokernel terms are definitionally the identity cone and the
-- shift, which the typing of the maps between these presentations requires.
@[expose] noncomputable def coneIdentityInjectivePresentation
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (gradedSplitExact (h := h)).InjectivePresentation
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) where
  I := ForgetEnrichment.of _ (cone (𝟙 (ForgetEnrichment.of _ M)))
  K := ForgetEnrichment.of _ (M.shift 1)
  i := coneInclusion (𝟙 (ForgetEnrichment.of _ M))
  p := coneProjection (𝟙 (ForgetEnrichment.of _ M))
  zero := coneInclusion_comp_coneProjection _
  conflation := (gradedSplitExact (h := h)).conflation_of_iso
    (ShortComplex.isoMk
      (eqToIso (coneShortComplex_X₁ (𝟙 (ForgetEnrichment.of _ M))))
      (eqToIso (coneShortComplex_X₂ (𝟙 (ForgetEnrichment.of _ M))))
      (eqToIso (coneShortComplex_X₃ (𝟙 (ForgetEnrichment.of _ M))))
      (by
        apply (cancel_epi
          (eqToHom (coneShortComplex_X₁ (𝟙 (ForgetEnrichment.of _ M))).symm)).mp
        simpa only [eqToIso.hom, ← Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.id_comp] using (coneShortComplex_f (𝟙 (ForgetEnrichment.of _ M))).symm)
      (by
        apply (cancel_epi
          (eqToHom (coneShortComplex_X₂ (𝟙 (ForgetEnrichment.of _ M))).symm)).mp
        simpa only [eqToIso.hom, ← Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.id_comp] using (coneShortComplex_g (𝟙 (ForgetEnrichment.of _ M))).symm))
    (coneShortComplex_conflation (𝟙 (ForgetEnrichment.of _ M)))
  isInjective := gradedSplitExact_isInjective_of_isZero_homotopy (isZero_homotopy_cone_isIso _)

/-- The injective object in the presentation is the cone of the identity. -/
@[simp]
theorem coneIdentityInjectivePresentation_I (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (coneIdentityInjectivePresentation M).I = ForgetEnrichment.of
      (CochainComplex (ModuleCat R) ℤ) (cone (𝟙 (ForgetEnrichment.of _ M))) :=
  (rfl)

/-- The cokernel object in the presentation is the shifted module. -/
@[simp]
theorem coneIdentityInjectivePresentation_K (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (coneIdentityInjectivePresentation M).K =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift 1) :=
  (rfl)

/-- After identifying its target, the presentation map is the identity-cone inclusion. -/
@[simp]
theorem coneIdentityInjectivePresentation_i (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (coneIdentityInjectivePresentation M).i ≫ eqToHom (coneIdentityInjectivePresentation_I M) =
      coneInclusion (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)) := by
  -- The characteristic object equality is the constructor's reflexive equation,
  -- so its transport is the identity on the explicitly specified injective object.
  change coneInclusion (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)) ≫
    (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
      (cone (𝟙 (ForgetEnrichment.of _ M))))) = _
  exact Category.comp_id _

/-- After identifying its endpoints, the presentation map is the identity-cone projection. -/
@[simp]
theorem coneIdentityInjectivePresentation_p (M : CurvedDGRightModuleCat.{u, u, u} h) :
    eqToHom (coneIdentityInjectivePresentation_I M).symm ≫
        (coneIdentityInjectivePresentation M).p ≫
          eqToHom (coneIdentityInjectivePresentation_K M) =
      coneProjection (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)) := by
  -- Both characteristic object equalities are reflexive constructor equations.
  -- Identify the two transports with identities before applying the category laws.
  change (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
      (cone (𝟙 (ForgetEnrichment.of _ M))))) ≫
    coneProjection (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)) ≫
      (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift 1))) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Every curved module is a graded-split quotient of a contractible cone of an identity. -/
theorem exists_gradedSplitExact_isDeflation_contractible
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (P : CurvedDGRightModuleCat.{u, u, u} h)
      (p : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M),
      (gradedSplitExact (h := h)).IsDeflation p ∧ IsZero (DGHomotopyCategory.of R P) := by
  let f := 𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift (-1)))
  let e₀ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift (-1 + 1)) ≅
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift 0) := eqToIso (by norm_num)
  let e := (closedShiftAddIso M (-1) 1).symm ≪≫ e₀ ≪≫ closedShiftZeroIso M
  refine ⟨cone f, coneProjection f ≫ e.hom, ?_, isZero_homotopy_cone_isIso f⟩
  exact MorphismProperty.RespectsIso.postcomp (gradedSplitExact (h := h)).deflations e.hom _
    (gradedSplitExact_isDeflation_coneProjection f)

/-- The graded-split exact structure has enough relative injectives. -/
theorem gradedSplitExact_enoughInjectives : (gradedSplitExact (h := h)).EnoughInjectives where
  presentation X := ⟨coneIdentityInjectivePresentation (ForgetEnrichment.to _ X)⟩

/-- The graded-split exact structure has enough relative projectives. -/
theorem gradedSplitExact_enoughProjectives : (gradedSplitExact (h := h)).EnoughProjectives where
  presentation X := by
    obtain ⟨P, p, hp, hP⟩ :=
      exists_gradedSplitExact_isDeflation_contractible (ForgetEnrichment.to _ X)
    obtain ⟨Z, i, hi, hS⟩ :=
      (ConflationClass.isDeflation_iff (gradedSplitExact (h := h)).toConflationClass p).mp hp
    exact ⟨⟨Z, _, i, p, hi, hS, gradedSplitExact_isProjective_of_isZero_homotopy hP⟩⟩

/-- The relatively injective modules are exactly the contractible modules. -/
theorem gradedSplitExact_isInjective_iff
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (gradedSplitExact (h := h)).isInjective
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) ↔
      IsZero (DGHomotopyCategory.of R M) := by
  refine ⟨fun hM ↦ ?_, gradedSplitExact_isInjective_of_isZero_homotopy⟩
  obtain ⟨r, hr⟩ := ExactStructure.isInjective_iff.mp hM
    (gradedSplitExact_isInflation_coneInclusion (𝟙 (ForgetEnrichment.of _ M))) (𝟙 _)
  apply (IsZero.iff_id_eq_zero _).mpr
  have hI := isZero_homotopy_cone_isIso (𝟙 (ForgetEnrichment.of _ M))
  have hz : (dgClosedToHomotopy R).map (coneInclusion (𝟙 (ForgetEnrichment.of _ M))) ≫
      (dgClosedToHomotopy R).map r = 0 := by
    rw [hI.eq_of_src ((dgClosedToHomotopy R).map r) 0, comp_zero]
  rw [← Functor.map_comp, hr, CategoryTheory.Functor.map_id] at hz
  exact hz

/-- The relatively projective modules are exactly the contractible modules. -/
theorem gradedSplitExact_isProjective_iff
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (gradedSplitExact (h := h)).isProjective
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) ↔
      IsZero (DGHomotopyCategory.of R M) := by
  refine ⟨fun hM ↦ ?_, gradedSplitExact_isProjective_of_isZero_homotopy⟩
  obtain ⟨P, p, hp, hP⟩ := exists_gradedSplitExact_isDeflation_contractible M
  obtain ⟨s, hs⟩ := ExactStructure.isProjective_iff.mp hM hp (𝟙 _)
  apply (IsZero.iff_id_eq_zero _).mpr
  have hz : (dgClosedToHomotopy R).map s ≫ (dgClosedToHomotopy R).map p = 0 := by
    rw [hP.eq_of_src ((dgClosedToHomotopy R).map p) 0, comp_zero]
  rw [← Functor.map_comp, hs, CategoryTheory.Functor.map_id] at hz
  exact hz

/-- The graded-split exact structure on curved right modules is Frobenius. -/
theorem gradedSplitExact_isFrobenius : (gradedSplitExact (h := h)).IsFrobenius where
  enoughProjectives := gradedSplitExact_enoughProjectives
  enoughInjectives := gradedSplitExact_enoughInjectives
  projective_iff_injective X :=
    (gradedSplitExact_isProjective_iff (ForgetEnrichment.to _ X)).trans
      (gradedSplitExact_isInjective_iff (ForgetEnrichment.to _ X)).symm

end TauCeti.CurvedDGRightModuleCat
