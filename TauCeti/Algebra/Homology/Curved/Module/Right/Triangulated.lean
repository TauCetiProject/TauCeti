/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.StableShift
public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Triangle
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated
public import TauCeti.CategoryTheory.Localization.Triangulated

/-!
# The homotopy category of curved DG right modules is triangulated

The graded-split exact structure on closed curved DG right modules is Frobenius. Its stable
category is equivalent to the existing `DGHomotopyCategory`, coherently with the existing
cohomological shifts by `ℤ`. Transporting Happel's stable triangulation therefore gives an
actual pretriangulated and triangulated structure on this homotopy category.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Triangulated`: the transport and
  comparison with conflation triangles follow the corresponding curved-duplex construction.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Cone.Triangle`: the characterization
  of distinguished triangles uses fullness of the quotient and uniqueness of cone triangles.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying
  EnrichedFunctor.ofDGMap EnrichedFunctor.mapDGHomotopyCategory

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- Happel's stable triangles give a pretriangulated structure on the existing curved-module
homotopy category, with its actual cohomological integer shift. -/
noncomputable instance instPretriangulatedHomotopyCategory :
    Pretriangulated (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  letI := (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctor_additive
  letI := (gradedSplitExact_isFrobenius (h := h)).stablePretriangulated
  letI := gradedSplitStableToHomotopyCommShift (h := h)
  Triangulated.Localization.pretriangulated gradedSplitStableToHomotopy
    (MorphismProperty.isomorphisms _)

/-- The stable-to-homotopy equivalence takes distinguished triangles to distinguished triangles. -/
theorem gradedSplitStableToHomotopy_isTriangulated :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctor_additive
    letI := (gradedSplitExact_isFrobenius (h := h)).stablePretriangulated
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    (gradedSplitStableToHomotopy (h := h)).IsTriangulated :=
  letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  letI := (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctor_additive
  letI := (gradedSplitExact_isFrobenius (h := h)).stablePretriangulated
  letI := gradedSplitStableToHomotopyCommShift (h := h)
  Triangulated.Localization.isTriangulated_functor _ (MorphismProperty.isomorphisms _)

/-- The existing homotopy category of general curved DG right modules is triangulated. -/
instance instIsTriangulatedHomotopyCategory :
    IsTriangulated (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  letI := (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctor_additive
  letI := (gradedSplitExact_isFrobenius (h := h)).stablePretriangulated
  letI := gradedSplitStableToHomotopyCommShift (h := h)
  haveI := (gradedSplitExact_isFrobenius (h := h)).stableIsTriangulated
  haveI := gradedSplitStableToHomotopy_isTriangulated (h := h)
  Triangulated.Localization.isTriangulated gradedSplitStableToHomotopy
    (MorphismProperty.isomorphisms _)

variable {S : ShortComplex (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
  (CurvedDGRightModuleCat.{u, u, u} h))}

/-- Compare a stable conflation triangle with the triangle computed using an identity cone. -/
private noncomputable def mapStableConflationTriangleIso
    (hS : (gradedSplitExact (h := h)).Conflation S)
    (a : S.X₂ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).I)
    (δ : S.X₃ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).K)
    (ha : S.f ≫ a = (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).i)
    (hδ : S.g ≫ δ = a ≫ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).p) :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    Triangle.mk ((dgClosedToHomotopy R).map S.f) ((dgClosedToHomotopy R).map S.g)
        (-((dgClosedToHomotopy R).map δ ≫ eqToHom (by
          simp only [coneIdentityInjectivePresentation_K, dgClosedToHomotopy_obj,
            shiftFunctor_eq_homotopyShiftFunctor, homotopyShiftFunctor_obj_of,
            ForgetEnrichment.to_of]))) ≅
      (gradedSplitStableToHomotopy (h := h)).mapTriangle.obj
        ((gradedSplitExact_isFrobenius (h := h)).stableConflationTriangle S hS) := by
  letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  letI := gradedSplitStableToHomotopyCommShift (h := h)
  have key := congrArg ((gradedSplitStableToHomotopy (h := h)).map)
    ((gradedSplitExact_isFrobenius (h := h)).projectiveStableFunctor_map_eq_connectingMap_comp
      hS (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)) a δ ha hδ)
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
      Iso.inv_hom_id_app_map_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Preadditive.comp_neg]
    rw [eqToHom_comp_iff, comp_eqToHom_iff] at key
    simp only [key, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc,
      eqToHom_map]
    simp only [eqToHom_trans, eqToHom_refl, Category.comp_id, Preadditive.neg_comp,
      Category.assoc]

/-- Graded-split conflations give distinguished triangles. The third arrow is the negative
class of the cokernel map induced by an extension to the first object's identity cone.
The public cokernel equation identifies its endpoint with the cohomological shift. -/
theorem mk_distinguished_of_conflation
    (hS : (gradedSplitExact (h := h)).Conflation S)
    (a : S.X₂ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).I)
    (δ : S.X₃ ⟶ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).K)
    (ha : S.f ≫ a = (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).i)
    (hδ : S.g ≫ δ = a ≫ (coneIdentityInjectivePresentation (ForgetEnrichment.to _ S.X₁)).p) :
    Triangle.mk ((dgClosedToHomotopy R).map S.f) ((dgClosedToHomotopy R).map S.g)
        (-((dgClosedToHomotopy R).map δ ≫ eqToHom (by
          simp only [coneIdentityInjectivePresentation_K, dgClosedToHomotopy_obj,
            shiftFunctor_eq_homotopyShiftFunctor, homotopyShiftFunctor_obj_of,
            ForgetEnrichment.to_of]))) ∈
      distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  let := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
  let := (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctor_additive
  let := (gradedSplitExact_isFrobenius (h := h)).stablePretriangulated
  let := gradedSplitStableToHomotopyCommShift (h := h)
  refine ⟨_, mapStableConflationTriangleIso hS a δ ha hδ, ?_⟩
  rw [ExactStructure.IsFrobenius.stablePretriangulated_distinguishedTriangles]
  exact (gradedSplitExact_isFrobenius (h := h)).stableConflationTriangle_mem S hS

/-- Every concrete mapping-cone triangle is distinguished, for arbitrary curvature. -/
theorem coneTriangle_distinguished {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    coneTriangle f ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) := by
  let k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1) := 0
  have hsq : ∀ x : M,
      closedHom (𝟙 (ForgetEnrichment.of _ N)) (closedHom f x) -
        closedHom (𝟙 (ForgetEnrichment.of _ N)) (closedHom f x) =
          N.differential (k.1 x) + k.1 (M.differential x) := by
    intro x
    simp [k]
  let S := ShortComplex.mk (coneInclusion f) (coneProjection f)
    (coneInclusion_comp_coneProjection f)
  have hS : (gradedSplitExact (h := h)).Conflation S :=
    (gradedSplitExact (h := h)).conflation_of_iso
      (ShortComplex.isoMk
        (eqToIso (coneShortComplex_X₁ f))
        (eqToIso (coneShortComplex_X₂ f))
        (eqToIso (coneShortComplex_X₃ f))
        (by
          apply (cancel_epi (eqToHom (coneShortComplex_X₁ f).symm)).mp
          simpa only [S, eqToIso.hom, ← Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.id_comp] using (coneShortComplex_f f).symm)
        (by
          apply (cancel_epi (eqToHom (coneShortComplex_X₂ f).symm)).mp
          simpa only [S, eqToIso.hom, ← Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.id_comp] using (coneShortComplex_g f).symm))
      (coneShortComplex_conflation f)
  let a := coneMap f (𝟙 (ForgetEnrichment.of _ N)) f (𝟙 _) k hsq ≫
    eqToHom (coneIdentityInjectivePresentation_I N).symm
  let δ := (closedShiftFunctor 1).map f ≫
    eqToHom (coneIdentityInjectivePresentation_K N).symm
  have ha : S.f ≫ a = (coneIdentityInjectivePresentation N).i := by
    apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_I N))).mp
    simp [S, a, Category.assoc]
  have hδ : S.g ≫ δ = a ≫ (coneIdentityInjectivePresentation N).p := by
    apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_K N))).mp
    simp [S, a, δ, Category.assoc]
  have hT := mk_distinguished_of_conflation hS a δ ha hδ
  apply (rotate_distinguished_triangle (coneTriangle f)).mpr
  simpa only [S, δ, coneTriangle_rotate, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hT

/-- Distinguished triangles are precisely those isomorphic to concrete mapping-cone triangles
of closed maps of curved DG right modules. -/
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
  -- Reduce the concrete triangle before using fullness of the homotopy quotient.
  dsimp only [coneTriangle, Triangle.mk_mor₁, Triangle.mk_obj₁]
  change Q.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁
  simp [f, Category.assoc]

end TauCeti.CurvedDGRightModuleCat
