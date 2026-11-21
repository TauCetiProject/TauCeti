/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import TauCeti.Algebra.Homology.DerivedCategory.HomologySequence
public import TauCeti.Algebra.Homology.DerivedCategory.MappingCone
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Triangle

/-!
# Derived fixed points of cochain endomorphisms

An algebra for the identity endofunctor on cochain complexes is a complex `K` with a cochain
endomorphism `φ`, not necessarily an automorphism. Its derived fixed points are the mapping
cocone of `φ - 𝟙 K`, viewed in the derived category. This gives a functor on strict equivariant
maps that inverts underlying quasi-isomorphisms. In particular it applies to Frobenius after
restricting to coefficients on which Frobenius acts trivially. Its fibre triangle gives
`Triangle.homologyKernelCokernelSequence` for the cohomology of the derived fixed points.

We use the fibre description of Bhatt–Scholze, *Prisms and prismatic cohomology*, Lemma 9.2,
and Mathlib's `CochainComplex.mappingCocone.triangle` for the sign convention.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex

namespace CategoryTheory.Endofunctor.Algebra

variable {C : Type*} [Category* C] [Preadditive C]

/-- The difference `φ - 𝟙` on objects with an endomorphism, as a natural transformation of the
forgetful functor. -/
def endomorphismSubId : forget (𝟭 C) ⟶ forget (𝟭 C) where
  app K := (fun (φ : K.a ⟶ K.a) ↦ φ - 𝟙 K.a) K.str
  naturality K L f := by
    let φ : K.a ⟶ K.a := K.str
    let ψ : L.a ⟶ L.a := L.str
    have h : f.f ≫ ψ = φ ≫ f.f := f.h
    -- The source of `str` is an identity-functor application; use the carrier hom types
    -- explicitly so that the preadditive composition lemmas match.
    change f.f ≫ (ψ - 𝟙 _) = (φ - 𝟙 _) ≫ f.f
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp, h]

@[simp]
theorem endomorphismSubId_app (K : Algebra (𝟭 C)) :
    endomorphismSubId.app K = (fun (φ : K.a ⟶ K.a) ↦ φ - 𝟙 K.a) K.str := (rfl)

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The derived fixed-point functor on cochain complexes equipped with an endomorphism. -/
noncomputable def derivedFixedPoints : Algebra (𝟭 (CochainComplex A ℤ)) ⥤ DerivedCategory A :=
  NatTrans.mappingCoconeFunctor endomorphismSubId ⋙ DerivedCategory.Q

@[simp]
theorem derivedFixedPoints_obj (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    derivedFixedPoints.obj K = DerivedCategory.Q.obj (mappingCocone (endomorphismSubId.app K)) :=
  (rfl)

/-- The projection from the derived fixed points to the underlying complex, natural in strict
endomorphism-equivariant maps. -/
noncomputable def derivedFixedPointsι : derivedFixedPoints (A := A) ⟶
    forget (𝟭 (CochainComplex A ℤ)) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (NatTrans.mappingCoconeFunctorFst endomorphismSubId) DerivedCategory.Q

/-- The distinguished fibre triangle of `φ - 𝟙` in the derived category. Its object fields
are reducible so that the structure maps can be used at their stated source and target. -/
@[expose, implicit_reducible]
noncomputable def derivedFixedPointsTriangle (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    Triangle (DerivedCategory A) :=
  Triangle.mk (derivedFixedPointsι.app K) (DerivedCategory.Q.map (endomorphismSubId.app K))
    (by
      rw [derivedFixedPoints_obj]
      exact (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle
        (endomorphismSubId.app K))).mor₃)

@[simp]
theorem derivedFixedPointsTriangle_obj₁ (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle.obj₁ = derivedFixedPoints.obj K := (rfl)

@[simp]
theorem derivedFixedPointsTriangle_obj₂ (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle.obj₂ = DerivedCategory.Q.obj K.a := (rfl)

@[simp]
theorem derivedFixedPointsTriangle_obj₃ (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle.obj₃ = DerivedCategory.Q.obj K.a := (rfl)

@[simp]
theorem derivedFixedPointsTriangle_mor₁ (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle.mor₁ = derivedFixedPointsι.app K := (rfl)

@[simp]
theorem derivedFixedPointsTriangle_mor₂ (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle.mor₂ = DerivedCategory.Q.map (endomorphismSubId.app K) := (rfl)

/-- The defining triangle is the image of the cochain mapping cocone triangle. -/
theorem derivedFixedPointsTriangle_eq (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle =
      DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle (endomorphismSubId.app K)) :=
  (rfl)

/-- The fibre triangles of `φ - 𝟙` are functorial in strictly equivariant cochain maps. -/
noncomputable def derivedFixedPointsTriangleFunctor :
    Algebra (𝟭 (CochainComplex A ℤ)) ⥤ Triangle (DerivedCategory A) :=
  NatTrans.mappingCoconeTriangleFunctor endomorphismSubId ⋙ DerivedCategory.Q.mapTriangle

@[simp]
theorem derivedFixedPointsTriangleFunctor_obj (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    derivedFixedPointsTriangleFunctor.obj K = K.derivedFixedPointsTriangle := (rfl)

@[simp]
theorem derivedFixedPointsTriangleFunctor_comp_π₁ :
    derivedFixedPointsTriangleFunctor (A := A) ⋙ Triangle.π₁ = derivedFixedPoints := (rfl)

@[simp]
theorem derivedFixedPointsTriangleFunctor_comp_π₂ :
    derivedFixedPointsTriangleFunctor (A := A) ⋙ Triangle.π₂ =
      forget (𝟭 (CochainComplex A ℤ)) ⋙ DerivedCategory.Q := (rfl)

@[simp]
theorem derivedFixedPointsTriangleFunctor_comp_π₃ :
    derivedFixedPointsTriangleFunctor (A := A) ⋙ Triangle.π₃ =
      forget (𝟭 (CochainComplex A ℤ)) ⋙ DerivedCategory.Q := (rfl)

/-- The fibre triangle of the endomorphism minus the identity is distinguished. -/
theorem derivedFixedPointsTriangle_distinguished (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    K.derivedFixedPointsTriangle ∈ distTriang _ := by
  rw [derivedFixedPointsTriangle_eq]
  exact DerivedCategory.mappingCocone_triangle_distinguished _

/-- The fixed-point projection is annihilated by the endomorphism minus the identity. -/
@[reassoc (attr := simp)]
theorem derivedFixedPointsι_comp (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    derivedFixedPointsι.app K ≫
      DerivedCategory.Q.map ((fun (φ : K.a ⟶ K.a) ↦ φ - 𝟙 K.a) K.str) = 0 := by
  have h : derivedFixedPointsι.app K ≫ DerivedCategory.Q.map (endomorphismSubId.app K) = 0 := by
    simpa only [derivedFixedPointsTriangle_mor₁, derivedFixedPointsTriangle_mor₂] using
      comp_distTriang_mor_zero₁₂ _ K.derivedFixedPointsTriangle_distinguished
  exact h

/-- An equivariant quasi-isomorphism induces an isomorphism on derived fixed points. -/
theorem isIso_derivedFixedPoints_map {K L : Algebra (𝟭 (CochainComplex A ℤ))} (f : K ⟶ L)
    [QuasiIso ((forget (𝟭 (CochainComplex A ℤ))).map f)] :
    IsIso (derivedFixedPoints.map f) := by
  rw [derivedFixedPoints, Functor.comp_map, DerivedCategory.isIso_Q_map_iff_quasiIso]
  have h := NatTrans.mappingCoconeFunctor_map endomorphismSubId f
  exact h ▸ (quasiIso_shift_iff _ (-1)).2
    (mappingCone.quasiIso_map _ _ _ _ (endomorphismSubId.naturality f).symm)

/-- The derived fixed points vanish exactly when `φ - 𝟙` is a quasi-isomorphism. -/
theorem isZero_derivedFixedPoints_iff (K : Algebra (𝟭 (CochainComplex A ℤ))) :
    IsZero (derivedFixedPoints.obj K) ↔ QuasiIso (endomorphismSubId.app K) := by
  simpa only [derivedFixedPointsTriangle_obj₁, derivedFixedPointsTriangle_mor₂,
    DerivedCategory.isIso_Q_map_iff_quasiIso] using
    Triangle.isZero₁_iff_isIso₂ _ K.derivedFixedPointsTriangle_distinguished

section Amplitude

variable (K : Algebra (𝟭 (CochainComplex A ℤ))) {i : ℤ}

/-- If the original complex has zero cohomology in degrees `i - 1` and `i`, the derived
fixed points have zero cohomology in degree `i`. -/
theorem isZero_homology_derivedFixedPoints
    (hprev : IsZero ((DerivedCategory.homologyFunctor A (i - 1)).obj (DerivedCategory.Q.obj K.a)))
    (hi : IsZero ((DerivedCategory.homologyFunctor A i).obj (DerivedCategory.Q.obj K.a))) :
    IsZero ((DerivedCategory.homologyFunctor A i).obj (derivedFixedPoints.obj K)) := by
  have h := K.derivedFixedPointsTriangle.homologyKernelCokernelSequence_shortExact
    K.derivedFixedPointsTriangle_distinguished i
  exact h.exact.isZero_of_both_isZero (IsZero.of_epi (cokernel.π _) hprev)
    (IsZero.of_mono (kernel.ι _) hi)

/-- Taking derived fixed points preserves a cohomological lower bound. -/
theorem isGE_derivedFixedPoints (a : ℤ) [(DerivedCategory.Q.obj K.a).IsGE a] :
    (derivedFixedPoints.obj K).IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact K.isZero_homology_derivedFixedPoints
    (DerivedCategory.isZero_of_isGE _ a _ (by omega))
    (DerivedCategory.isZero_of_isGE _ a _ hi)

/-- Taking derived fixed points raises a cohomological upper bound by at most one. -/
theorem isLE_derivedFixedPoints (b : ℤ) [(DerivedCategory.Q.obj K.a).IsLE b] :
    (derivedFixedPoints.obj K).IsLE (b + 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact K.isZero_homology_derivedFixedPoints
    (DerivedCategory.isZero_of_isLE _ b _ (by omega))
    (DerivedCategory.isZero_of_isLE _ b _ (by omega))

end Amplitude

end CategoryTheory.Endofunctor.Algebra
