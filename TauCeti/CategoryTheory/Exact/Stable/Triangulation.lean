/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Shift
public import TauCeti.CategoryTheory.Exact.Stable.Cone
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Standard triangles in the stable category

This file gives the standard Happel triangles in the projective stable quotient of a
Frobenius exact category. A conflation is sent to a triangle in the stable category by the
quotient functor, its connecting map, and the comparison between the chosen suspension object and
the stable suspension. The cone of an arbitrary morphism is identified with the standard triangle
of its cone conflation, and the cone triangle on the inflation of any conflation is identified
with that conflation's stable triangle. This construction follows Happel, *Triangulated
Categories in the Representation Theory of Finite Dimensional Algebras*, Chapter I, Section 2.
Morphisms between
objects in the stable category are handled by choosing a representative in the exact category.

The isomorphism-closed class of distinguished triangles records the triangles arising from
conflations. The cone construction shows that the standard cone triangles belong to this class.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti
namespace ExactStructure.IsFrobenius
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {E : ExactStructure C} (hE : E.IsFrobenius)
/-- The stable image of a conflation, with its connecting map transported to the suspension
shift. -/
noncomputable def stableConflationTriangle (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory := by
  letI := hE.stableHasShift
  let q := E.projectiveStableFunctor
  let e := hE.stableShiftFunctorOneIso
  let bridge : q.obj (hE.suspensionObj S.X₁) = hE.stableSuspension.obj (q.obj S.X₁) :=
    (hE.stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm
  exact CategoryTheory.Pretriangulated.Triangle.mk (q.map S.f) (q.map S.g)
    (q.map (hE.connectingMap hS) ≫ eqToHom bridge ≫ e.symm.hom.app (q.obj S.X₁))

/-- The stable conflation triangle written with its three explicit arrows. -/
theorem stableConflationTriangle_eq_mk (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    hE.stableConflationTriangle S hS = CategoryTheory.Pretriangulated.Triangle.mk
      (E.projectiveStableFunctor.map S.f) (E.projectiveStableFunctor.map S.g)
      (E.projectiveStableFunctor.map (hE.connectingMap hS) ≫
        eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm ≫
        hE.stableShiftFunctorOneIso.inv.app (E.projectiveStableFunctor.obj S.X₁)) := (rfl)

/-- The first object of the stable conflation triangle. -/
@[simp]
theorem stableConflationTriangle_obj₁ (S : ShortComplex C) (hS : E.Conflation S) :
    (letI := hE.stableHasShift; (hE.stableConflationTriangle S hS).obj₁) =
      E.projectiveStableFunctor.obj S.X₁ := by
  simp [stableConflationTriangle]

/-- The second object of the stable conflation triangle. -/
@[simp]
theorem stableConflationTriangle_obj₂ (S : ShortComplex C) (hS : E.Conflation S) :
    (letI := hE.stableHasShift; (hE.stableConflationTriangle S hS).obj₂) =
      E.projectiveStableFunctor.obj S.X₂ := by
  simp [stableConflationTriangle]

/-- The third object of the stable conflation triangle. -/
@[simp]
theorem stableConflationTriangle_obj₃ (S : ShortComplex C) (hS : E.Conflation S) :
    (letI := hE.stableHasShift; (hE.stableConflationTriangle S hS).obj₃) =
      E.projectiveStableFunctor.obj S.X₃ := by
  simp [stableConflationTriangle]

/-- The first morphism of the stable conflation triangle. -/
@[simp]
theorem stableConflationTriangle_mor₁ (S : ShortComplex C) (hS : E.Conflation S) :
    HEq (letI := hE.stableHasShift; (hE.stableConflationTriangle S hS).mor₁)
      (E.projectiveStableFunctor.map S.f) := by
  simp [stableConflationTriangle]

/-- The second morphism of the stable conflation triangle. -/
@[simp]
theorem stableConflationTriangle_mor₂ (S : ShortComplex C) (hS : E.Conflation S) :
    HEq (letI := hE.stableHasShift; (hE.stableConflationTriangle S hS).mor₂)
      (E.projectiveStableFunctor.map S.g) := by
  simp [stableConflationTriangle]

/-- The third morphism of the stable conflation triangle. -/
@[simp]
theorem stableConflationTriangle_mor₃ (S : ShortComplex C) (hS : E.Conflation S) :
    HEq (letI := hE.stableHasShift; (hE.stableConflationTriangle S hS).mor₃)
      (E.projectiveStableFunctor.map (hE.connectingMap hS) ≫
        eqToHom ((hE.stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm) ≫
        hE.stableShiftFunctorOneIso.inv.app (E.projectiveStableFunctor.obj S.X₁)) := by
  simp [stableConflationTriangle]
/-- The distinguished triangles generated by conflations, up to isomorphism. -/
noncomputable def stableDistinguishedTriangles :
    letI := hE.stableHasShift
    Set (CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory) :=
  letI := hE.stableHasShift
  { T | ∃ S : ShortComplex C, ∃ hS : E.Conflation S,
      Nonempty (T ≅ (hE.stableConflationTriangle S hS)) }

/-- Membership in the distinguished stable triangles means being isomorphic to a conflation
triangle. -/
theorem mem_stableDistinguishedTriangles_iff
    (T : (letI := hE.stableHasShift;
      CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory)) :
    T ∈ hE.stableDistinguishedTriangles ↔
      ∃ S : ShortComplex C, ∃ hS : E.Conflation S,
        Nonempty (T ≅ hE.stableConflationTriangle S hS) := Iff.rfl

/-- A standard conflation triangle is distinguished. -/
@[simp]
theorem stableConflationTriangle_mem (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    (hE.stableConflationTriangle S hS) ∈ (hE.stableDistinguishedTriangles) := by
  let := hE.stableHasShift
  exact (hE.mem_stableDistinguishedTriangles_iff _).2 ⟨S, hS, ⟨by rfl⟩⟩

/-- Distinguished triangles are closed under isomorphism in the stable category. -/
theorem stableDistinguishedTriangles_isomorphic
    {T₁ T₂ : (letI : HasShift E.ProjectiveStableCategory ℤ := hE.stableHasShift;
      CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory)}
    (hT₁ : (letI : HasShift E.ProjectiveStableCategory ℤ := hE.stableHasShift;
      T₁ ∈ hE.stableDistinguishedTriangles)) (e : T₁ ≅ T₂) :
    (letI : HasShift E.ProjectiveStableCategory ℤ := hE.stableHasShift;
      T₂ ∈ hE.stableDistinguishedTriangles) := by
  let := hE.stableHasShift
  rcases hT₁ with ⟨S, hS, ⟨iso⟩⟩
  exact ⟨S, hS, ⟨(iso.symm.trans e).symm⟩⟩

variable {X Y : C}

/-- The stable triangle associated to an arbitrary morphism through its cone. -/
noncomputable def stableConeTriangle (f : X ⟶ Y) :
    letI := hE.stableHasShift
    CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory := by
  letI := hE.stableHasShift
  let q := E.projectiveStableFunctor
  let e := hE.stableShiftFunctorOneIso
  let bridge : q.obj (hE.suspensionObj X) =
      hE.stableSuspension.obj (q.obj X) :=
    (hE.stableSuspension_obj_projectiveStableFunctor_obj X).symm
  exact CategoryTheory.Pretriangulated.Triangle.mk (q.map f)
    (q.map (hE.coneInclusion f))
    (q.map (hE.coneConnectingMap f) ≫ eqToHom bridge ≫
      e.symm.hom.app (q.obj X))

/-- The stable cone triangle written using the canonical comparison from the chosen suspension
object to the shift. -/
theorem stableConeTriangle_eq_mk (f : X ⟶ Y) :
    letI := hE.stableHasShift
    hE.stableConeTriangle f = CategoryTheory.Pretriangulated.Triangle.mk
      (E.projectiveStableFunctor.map f)
      (E.projectiveStableFunctor.map (hE.coneInclusion f))
      (E.projectiveStableFunctor.map (hE.coneConnectingMap f) ≫
        (hE.stableSuspensionObjIsoShift X).hom) := by
  simp only [stableConeTriangle, stableSuspensionObjIsoShift_hom, Iso.symm_hom]

/-- The first object of the stable cone triangle. -/
@[simp]
theorem stableConeTriangle_obj₁ (f : X ⟶ Y) :
    (letI := hE.stableHasShift; (hE.stableConeTriangle f).obj₁) =
      E.projectiveStableFunctor.obj X := by
  simp [stableConeTriangle]

/-- The second object of the stable cone triangle. -/
@[simp]
theorem stableConeTriangle_obj₂ (f : X ⟶ Y) :
    (letI := hE.stableHasShift; (hE.stableConeTriangle f).obj₂) =
      E.projectiveStableFunctor.obj Y := by
  simp [stableConeTriangle]

/-- The third object of the stable cone triangle. -/
@[simp]
theorem stableConeTriangle_obj₃ (f : X ⟶ Y) :
    (letI := hE.stableHasShift; (hE.stableConeTriangle f).obj₃) =
      E.projectiveStableFunctor.obj (hE.coneObj f) := by
  simp [stableConeTriangle]

/-- The first morphism of the stable cone triangle. -/
@[simp]
theorem stableConeTriangle_mor₁ (f : X ⟶ Y) :
    HEq (letI := hE.stableHasShift; (hE.stableConeTriangle f).mor₁)
      (E.projectiveStableFunctor.map f) := by
  simp [stableConeTriangle]

/-- The second morphism of the stable cone triangle. -/
@[simp]
theorem stableConeTriangle_mor₂ (f : X ⟶ Y) :
    HEq (letI := hE.stableHasShift; (hE.stableConeTriangle f).mor₂)
      (E.projectiveStableFunctor.map (hE.coneInclusion f)) := by
  simp [stableConeTriangle]

/-- The third morphism of the stable cone triangle. -/
@[simp]
theorem stableConeTriangle_mor₃ (f : X ⟶ Y) :
    HEq (letI := hE.stableHasShift; (hE.stableConeTriangle f).mor₃)
      (E.projectiveStableFunctor.map (hE.coneConnectingMap f) ≫
        eqToHom ((hE.stableSuspension_obj_projectiveStableFunctor_obj X).symm) ≫
        hE.stableShiftFunctorOneIso.inv.app (E.projectiveStableFunctor.obj X)) := by
  simp [stableConeTriangle]


/-- The cone triangle is isomorphic to the standard triangle of the cone conflation. -/
noncomputable def stableConeTriangleIsoConflation (f : X ⟶ Y) :
    letI := hE.stableHasShift
    stableConeTriangle (hE := hE) f ≅
      hE.stableConflationTriangle
        (ShortComplex.mk (hE.coneInflation f) (hE.coneDeflation f)
          (hE.coneInflation_comp_coneDeflation f)) (hE.conflation_cone f) := by
  letI := hE.stableHasShift
  let S := ShortComplex.mk (hE.coneInflation f) (hE.coneDeflation f)
    (hE.coneInflation_comp_coneDeflation f)
  let hS := hE.conflation_cone f
  let T₁ : CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory :=
    CategoryTheory.Pretriangulated.Triangle.mk
      (E.projectiveStableFunctor.map f)
      (E.projectiveStableFunctor.map (hE.coneInclusion f))
      (E.projectiveStableFunctor.map (hE.coneConnectingMap f) ≫
        eqToHom ((hE.stableSuspension_obj_projectiveStableFunctor_obj X).symm) ≫
        hE.stableShiftFunctorOneIso.symm.hom.app (E.projectiveStableFunctor.obj X))
  let T₂ : CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory :=
    CategoryTheory.Pretriangulated.Triangle.mk
      (E.projectiveStableFunctor.map (hE.coneInflation f))
      (E.projectiveStableFunctor.map (hE.coneDeflation f))
      (E.projectiveStableFunctor.map (hE.connectingMap (hE.conflation_cone f)) ≫
        eqToHom ((hE.stableSuspension_obj_projectiveStableFunctor_obj X).symm) ≫
        hE.stableShiftFunctorOneIso.symm.hom.app (E.projectiveStableFunctor.obj X))
  have hT₁ : T₁ = hE.stableConeTriangle f := by
    dsimp [T₁]
    cases hE.stableConeTriangle_obj₁ f
    cases hE.stableConeTriangle_obj₂ f
    cases hE.stableConeTriangle_obj₃ f
    cases hE.stableConeTriangle_mor₁ f
    cases hE.stableConeTriangle_mor₂ f
    cases hE.stableConeTriangle_mor₃ f
    rfl
  have hT₂ : T₂ = hE.stableConflationTriangle S hS := by
    dsimp [T₂, S, hS]
    cases hE.stableConflationTriangle_obj₁ S hS
    cases hE.stableConflationTriangle_obj₂ S hS
    cases hE.stableConflationTriangle_obj₃ S hS
    cases hE.stableConflationTriangle_mor₁ S hS
    cases hE.stableConflationTriangle_mor₂ S hS
    cases hE.stableConflationTriangle_mor₃ S hS
    rfl
  let i := E.projectiveStableIsoBiprod
    (hE.isProjective_I (hE.suspensionPresentation X)) Y
  have hIso : T₁ ≅ T₂ := by
    refine CategoryTheory.Pretriangulated.Triangle.isoMk T₁ T₂
      (Iso.refl _) i (Iso.refl _) ?_ ?_ ?_
    · dsimp [T₁, T₂]
      simp only [Category.id_comp]
      rw [hE.projectiveStableFunctor_map_coneInflation]
    · dsimp [T₁, T₂]
      simp only [Category.comp_id]
      dsimp [i]
      simp only [E.projectiveStableIsoBiprod_hom]
      rw [← Functor.map_comp]
      simp [coneDeflation]
    · dsimp [T₁, T₂]
      simp only [Category.assoc]
      rw [hE.projectiveStableFunctor_map_connectingMap_cone]
      simp
  simpa only [hT₁, hT₂] using hIso

/-- The cone triangle on the inflation of a conflation is isomorphic to that conflation's
stable triangle. The third component is the stable isomorphism from the cone to the cokernel. -/
noncomputable def stableConeTriangleIsoStableConflation (S : ShortComplex C)
    (hS : E.Conflation S) :
    letI := hE.stableHasShift
    hE.stableConeTriangle S.f ≅ hE.stableConflationTriangle S hS := by
  letI := hE.stableHasShift
  let coneS := ShortComplex.mk (hE.coneInflation S.f) (hE.coneDeflation S.f)
    (hE.coneInflation_comp_coneDeflation S.f)
  let φ : coneS ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := biprod.desc 0 (𝟙 _)
      τ₃ := hE.coneComparison S
      comm₁₂ := by simp [coneS, coneInflation]
      comm₂₃ := by
        dsimp [coneS, coneDeflation]
        apply biprod.hom_ext' <;> simp }
  -- Naturality of connecting maps identifies the last arrows after the cone comparison.
  have hconnecting :
      E.projectiveStableFunctor.map (hE.coneComparison S) ≫
          E.projectiveStableFunctor.map (hE.connectingMap hS) =
        E.projectiveStableFunctor.map (hE.coneConnectingMap S.f) := by
    have h := hE.projectiveStableFunctor_map_connectingMap_naturality
      (hE.conflation_cone S.f) hS φ
    dsimp [φ, coneS] at h
    rw [Functor.map_comp, Functor.map_comp,
      hE.projectiveStableFunctor_map_connectingMap_cone,
      E.projectiveStableFunctor_map_cokernelMap_id _
        (hE.isProjective_I (hE.suspensionPresentation S.X₁))] at h
    simpa only [Category.comp_id] using h
  -- Writing both triangles explicitly keeps the three components of the comparison visible.
  let J := (hE.stableSuspensionObjIsoShift S.X₁).hom
  let T₁ : CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory :=
    CategoryTheory.Pretriangulated.Triangle.mk
      (E.projectiveStableFunctor.map S.f)
      (E.projectiveStableFunctor.map (hE.coneInclusion S.f))
      (E.projectiveStableFunctor.map (hE.coneConnectingMap S.f) ≫ J)
  let T₂ : CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory :=
    CategoryTheory.Pretriangulated.Triangle.mk
      (E.projectiveStableFunctor.map S.f)
      (E.projectiveStableFunctor.map S.g)
      (E.projectiveStableFunctor.map (hE.connectingMap hS) ≫ J)
  have hT₁ : T₁ = hE.stableConeTriangle S.f := by
    simpa only [T₁, J] using (hE.stableConeTriangle_eq_mk S.f).symm
  have hT₂ : T₂ = hE.stableConflationTriangle S hS := by
    simpa only [T₂, J, stableSuspensionObjIsoShift_hom, Category.assoc] using
      (hE.stableConflationTriangle_eq_mk S hS).symm
  -- The first two components are identities; the third is the stable cone comparison.
  have hIso : T₁ ≅ T₂ := by
    let _ := hE.isIso_projectiveStableFunctor_map_coneComparison hS
    refine CategoryTheory.Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso (E.projectiveStableFunctor.map (hE.coneComparison S))) ?_ ?_ ?_
    · simp [T₁, T₂]
    · dsimp [T₁, T₂]
      simp only [Category.id_comp, ← Functor.map_comp]
      rw [hE.coneInclusion_comp_coneComparison]
    · dsimp [T₁, T₂]
      rw [reassoc_of% hconnecting]
      simp
  simpa only [hT₁, hT₂] using hIso

/-- The cone triangle is distinguished. -/
@[simp]
theorem stableConeTriangle_mem (f : X ⟶ Y) :
    (letI : HasShift E.ProjectiveStableCategory ℤ := hE.stableHasShift;
      (hE.stableConeTriangle f) ∈ hE.stableDistinguishedTriangles) := by
  let := hE.stableHasShift
  exact (hE.mem_stableDistinguishedTriangles_iff _).2
    ⟨_, hE.conflation_cone f, ⟨hE.stableConeTriangleIsoConflation f⟩⟩

/-- A cone triangle for a morphism between objects in the projective stable category, represented
by a morphism in the Frobenius exact category. -/
noncomputable def stableConeTriangleOf
    (f : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y) :
    letI := hE.stableHasShift
    CategoryTheory.Pretriangulated.Triangle E.ProjectiveStableCategory :=
  hE.stableConeTriangle (Classical.choose (E.projectiveStableFunctor.map_surjective f))

/-- A chosen stable cone triangle is the cone triangle of a representative of its morphism. -/
theorem stableConeTriangleOf_exists_rep
    (f : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y) :
    ∃ g : X ⟶ Y, E.projectiveStableFunctor.map g = f ∧
      (letI := hE.stableHasShift; hE.stableConeTriangleOf f = hE.stableConeTriangle g) := by
  refine ⟨Classical.choose (E.projectiveStableFunctor.map_surjective f),
    Classical.choose_spec (E.projectiveStableFunctor.map_surjective f), ?_⟩
  rfl

/-- The first morphism of the chosen stable cone triangle is the given stable-category morphism. -/
@[simp]
theorem stableConeTriangleOf_mor₁
    (f : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y) :
    HEq (letI := hE.stableHasShift; (hE.stableConeTriangleOf f).mor₁) f := by
  rcases hE.stableConeTriangleOf_exists_rep f with ⟨g, hfg, htriangle⟩
  rw [htriangle]
  exact (hE.stableConeTriangle_mor₁ g).trans (heq_of_eq hfg)

/-- The first object of the chosen stable cone triangle. -/
@[simp]
theorem stableConeTriangleOf_obj₁
    (f : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y) :
    (letI := hE.stableHasShift; (hE.stableConeTriangleOf f).obj₁) =
      E.projectiveStableFunctor.obj X := by
  rcases hE.stableConeTriangleOf_exists_rep f with ⟨g, _, htriangle⟩
  rw [htriangle]
  exact hE.stableConeTriangle_obj₁ g

/-- The second object of the chosen stable cone triangle. -/
@[simp]
theorem stableConeTriangleOf_obj₂
    (f : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y) :
    (letI := hE.stableHasShift; (hE.stableConeTriangleOf f).obj₂) =
      E.projectiveStableFunctor.obj Y := by
  rcases hE.stableConeTriangleOf_exists_rep f with ⟨g, _, htriangle⟩
  rw [htriangle]
  exact hE.stableConeTriangle_obj₂ g

/-- The cone triangle of any stable-category morphism is distinguished. -/
@[simp]
theorem stableConeTriangleOf_mem
    (f : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y) :
    (letI := hE.stableHasShift;
      (hE.stableConeTriangleOf f) ∈ hE.stableDistinguishedTriangles) := by
  rcases hE.stableConeTriangleOf_exists_rep f with ⟨g, _, hfg⟩
  rw [hfg]
  exact hE.stableConeTriangle_mem g

end ExactStructure.IsFrobenius
end TauCeti
