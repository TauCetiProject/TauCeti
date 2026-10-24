/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Triangle
public import TauCeti.Algebra.Homology.Curved.Module.Right.Triangulated
public import TauCeti.CategoryTheory.Triangulated.Signs

/-!
# Distinguished mapping-cone triangles of curved DG right modules

The existing triangulation is transported from the graded-split Frobenius stable category using
its canonical suspension comparison. An extension of a conflation to the identity-cone
presentation computes its connecting arrow with positive sign. Applying this to the cone
sequence gives the triangle with arrows inclusion, projection, and shifted original map.
Negating its third object identifies it with the rotation of the mapping-cone triangle, whose
third arrow is therefore the negative cone projection.

Every distinguished triangle is isomorphic to one of these concrete cone triangles. All
structures, objects, shifts, and suspension comparisons used here are the existing ones, and
the curvature is unrestricted.

## References

* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Periodic.Triangulated`: the concrete
  triangle comparison follows the periodic cone construction, with the same negative projection.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Module.Right.Suspension`: the
  canonical stable-suspension comparison supplies the connecting-map sign.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The homotopy quotient retains the underlying curved modules as objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying coneIdentityInjectivePresentation
  EnrichedFunctor.ofDGMap EnrichedFunctor.mapDGHomotopyCategory

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}
  {S : ShortComplex (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
    (CurvedDGRightModuleCat.{u, u, u} h))}

/-- The identity-cone connecting map gives the transported stable conflation triangle. -/
private noncomputable def mapStableConflationTriangleIso
    (hS : (gradedSplitExact (h := h)).Conflation S)
    (a : S.X₂ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).I)
    (δ : S.X₃ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).K)
    (ha : S.f ≫ a = (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).i)
    (hδ : S.g ≫ δ = a ≫ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).p) :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    Triangle.mk ((dgClosedToHomotopy R).map S.f) ((dgClosedToHomotopy R).map S.g)
        ((dgClosedToHomotopy R).map δ ≫ eqToHom (by
          simp only [coneIdentityInjectivePresentation_K, dgClosedToHomotopy_obj,
            shiftFunctor_eq_homotopyShiftFunctor, homotopyShiftFunctor_obj_of,
            ForgetEnrichment.to_of])) ≅
      (gradedSplitStableToHomotopy (h := h)).mapTriangle.obj
        ((gradedSplitExact_isFrobenius (h := h)).stableConflationTriangle S hS) := by
  letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  letI := gradedSplitStableToHomotopyCommShift (h := h)
  have key := congrArg ((gradedSplitStableToHomotopy (h := h)).map)
    ((gradedSplitExact_isFrobenius (h := h)).projectiveStableFunctor_map_eq_connectingMap_comp
      hS (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)) a δ ha hδ)
  -- The represented endpoints occur in dependent hom types. Rewrite there before normalizing
  -- the public object-transport equations of the stable-to-homotopy comparison.
  erw [gradedSplitStableToHomotopy_map_projectiveStableFunctor_map (h := h) δ] at key
  simp only [gradedSplitStableToHomotopy_map_projectiveStableFunctor_map, Functor.map_comp,
    ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [ExactStructure.IsFrobenius.stableConflationTriangle_eq_mk]
  refine Triangle.isoMk _ _ (eqToIso (by simp)) (eqToIso (by simp)) (eqToIso (by simp))
    ?_ ?_ ?_
  · simp [gradedSplitStableToHomotopy_map_projectiveStableFunctor_map]
  · simp [gradedSplitStableToHomotopy_map_projectiveStableFunctor_map]
  · simp only [Triangle.mk_obj₃, Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_mor₃,
      eqToIso.hom, Category.assoc, Functor.map_comp,
      gradedSplitStableToHomotopy_map_projectiveStableFunctor_map,
      gradedSplitStableToHomotopyCommShift_iso_one, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.comp_obj,
      Functor.whiskerRight_app, stableSuspensionCompGradedSplitStableToHomotopyIso_hom_app,
      gradedSplitStableSuspensionIsoShift_hom_app,
      Iso.inv_hom_id_app_map_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [eqToHom_comp_iff, comp_eqToHom_iff] at key
    simp only [key, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc,
      eqToHom_map]
    simp only [dgClosedToHomotopy_commShiftIso_hom_app, eqToHom_trans]

/-- A graded-split conflation gives a distinguished triangle whose third arrow is the class of
the cokernel map induced by an extension to the first object's identity cone. The canonical
suspension comparison gives this connecting arrow with positive sign. -/
theorem mk_distinguished_of_conflation
    (hS : (gradedSplitExact (h := h)).Conflation S)
    (a : S.X₂ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).I)
    (δ : S.X₃ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).K)
    (ha : S.f ≫ a = (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).i)
    (hδ : S.g ≫ δ = a ≫ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).p) :
    Triangle.mk ((dgClosedToHomotopy R).map S.f) ((dgClosedToHomotopy R).map S.g)
        ((dgClosedToHomotopy R).map δ ≫ eqToHom (by
          simp only [coneIdentityInjectivePresentation_K, dgClosedToHomotopy_obj,
            shiftFunctor_eq_homotopyShiftFunctor, homotopyShiftFunctor_obj_of,
            ForgetEnrichment.to_of])) ∈
      distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  let := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  let := gradedSplitStableToHomotopyCommShift (h := h)
  exact isomorphic_distinguished _ (map_stableConflationTriangle_mem_distTriang S hS) _
    (mapStableConflationTriangleIso hS a δ ha hδ)

private theorem coneShortComplex_mk_conflation {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    (gradedSplitExact (h := h)).Conflation
      (ShortComplex.mk (coneInclusion f) (coneProjection f)
        (coneInclusion_comp_coneProjection f)) :=
  (gradedSplitExact (h := h)).conflation_of_iso
    (ShortComplex.isoMk
      (eqToIso (coneShortComplex_X₁ f))
      (eqToIso (coneShortComplex_X₂ f))
      (eqToIso (coneShortComplex_X₃ f))
      (by
        apply (cancel_epi (eqToHom (coneShortComplex_X₁ f).symm)).mp
        simpa only [eqToIso.hom, ← Category.assoc, eqToHom_trans,
          eqToHom_refl, Category.id_comp] using (coneShortComplex_f f).symm)
      (by
        apply (cancel_epi (eqToHom (coneShortComplex_X₂ f).symm)).mp
        simpa only [eqToIso.hom, ← Category.assoc, eqToHom_trans,
          eqToHom_refl, Category.id_comp] using (coneShortComplex_g f).symm))
    (coneShortComplex_conflation f)

private noncomputable def coneIdentityExtension {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f) ⟶
      (coneIdentityInjectivePresentation N).I :=
  coneMap f (𝟙 (ForgetEnrichment.of _ N)) f (𝟙 _) 0 (by intro x; simp) ≫
    eqToHom (coneIdentityInjectivePresentation_I N).symm

private noncomputable def coneShiftConnecting {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    (closedShiftFunctor 1).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) ⟶
      (coneIdentityInjectivePresentation N).K :=
  (closedShiftFunctor 1).map f ≫ eqToHom (coneIdentityInjectivePresentation_K N).symm

private theorem coneIdentityExtension_inclusion {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneInclusion f ≫ coneIdentityExtension f = (coneIdentityInjectivePresentation N).i := by
  apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_I N))).mp
  simpa only [coneIdentityExtension, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, coneInclusion_comp_coneMap, Category.id_comp] using
    (coneIdentityInjectivePresentation_i N).symm

private theorem coneIdentityExtension_projection {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneProjection f ≫ coneShiftConnecting f =
      coneIdentityExtension f ≫ (coneIdentityInjectivePresentation N).p := by
  apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_K N))).mp
  dsimp only [coneIdentityExtension, coneShiftConnecting]
  simp only [Category.assoc]
  rw [coneIdentityInjectivePresentation_p]
  simpa only [eqToHom_trans, eqToHom_refl, Category.comp_id] using
    (coneMap_comp_coneProjection f (𝟙 (ForgetEnrichment.of _ N)) f (𝟙 _) 0
      (by intro x; simp)).symm

private theorem coneInclusion_coneProjection_shift_distinguished
    {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    Triangle.mk ((dgClosedToHomotopy R).map (coneInclusion f))
        ((dgClosedToHomotopy R).map (coneProjection f))
        ((dgClosedToHomotopy R).map ((closedShiftFunctor 1).map f)) ∈
      distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  have hT := mk_distinguished_of_conflation (coneShortComplex_mk_conflation f)
    (coneIdentityExtension f) (coneShiftConnecting f)
    (coneIdentityExtension_inclusion f) (coneIdentityExtension_projection f)
  -- The target of the connecting map is the identity-cone cokernel N[1], identified by its
  -- public K equation with the closed shift of N. Expose the composite before mapping it,
  -- then cancel the resulting object transports.
  dsimp only [coneShiftConnecting] at hT
  rw [Functor.map_comp, eqToHom_map] at hT
  simpa only [Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] using hT

/-- Every mapping-cone triangle with its negative projection is distinguished, for arbitrary
curvature, in the canonical triangulation of the curved homotopy category. -/
theorem coneTriangle_distinguished {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneTriangle f ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  apply (rotate_distinguished_triangle (coneTriangle f)).mpr
  refine isomorphic_distinguished _ (coneInclusion_coneProjection_shift_distinguished f) _ ?_
  rw [coneTriangle_rotate]
  exact Triangle.isoNegThird _ _ _

/-- Distinguished triangles are precisely those isomorphic to the concrete mapping-cone
triangles of closed maps, with the negative cone projection as third arrow. -/
theorem mem_distTriang_iff_nonempty_iso_coneTriangle
    (T : Triangle (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))) :
    T ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) ↔
      ∃ (M N : CurvedDGRightModuleCat.{u, u, u} h)
        (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N),
        Nonempty (T ≅ coneTriangle f) := by
  refine ⟨fun hT ↦ ?_, fun ⟨M, N, f, ⟨e⟩⟩ ↦
    isomorphic_distinguished _ (coneTriangle_distinguished f) _ e⟩
  let Q := dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R
  let M := DGHomotopyCategory.underlying R T.obj₁
  let N := DGHomotopyCategory.underlying R T.obj₂
  let X := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M
  let Y := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N
  let e₁ : Q.obj X ≅ T.obj₁ := eqToIso (DGHomotopyCategory.of_underlying R T.obj₁)
  let e₂ : Q.obj Y ≅ T.obj₂ := eqToIso (DGHomotopyCategory.of_underlying R T.obj₂)
  let f := Q.preimage (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  refine ⟨M, N, f,
    ⟨(isoTriangleOfIso₁₂ _ _ (coneTriangle_distinguished f) hT e₁ e₂ ?_).symm⟩⟩
  -- The triangle's first arrow is a quotient map, so fullness identifies this representative.
  change Q.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁
  simp [f, Category.assoc]

end TauCeti.CurvedDGRightModuleCat
