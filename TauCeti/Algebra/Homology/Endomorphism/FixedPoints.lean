/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import TauCeti.Algebra.Homology.DerivedCategory.CohomologySequence
public import TauCeti.Algebra.Homology.DerivedCategory.MappingCone
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic

/-!
# Derived fixed points of an endomorphism

An algebra for the identity endofunctor on cochain complexes is a complex `M` with an
endomorphism `φ`. Its derived fixed points are the mapping cocone of `φ - 1`, viewed in
the derived category. For a semilinear Frobenius, this construction is applied after
restriction to a ring of Frobenius-fixed scalars; subtraction of the identity is linear
over those scalars, but generally not over the original coefficient ring.

The construction is functorial in strictly commuting maps. Its distinguished triangle
gives the long exact cohomology sequence and bounds its amplitude. In particular a
complex concentrated in degree zero can have fixed-point cohomology in degree one.
The kernel/cokernel sequence and its vanishing isomorphisms are the general triangle API:
`M.fixedPointsTriangle.cohomologySequence M.fixedPointsTriangle_distinguished n`,
`Triangle.cohomologyIsoKernel` and `Triangle.cohomologyIsoCokernel`.
No enhancement or category of homotopy-coherent endomorphisms is constructed here.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, §9, Lemma 9.2.
* B. Bhatt and J. Lurie, *Absolute prismatic cohomology*, Example 8.1.3.
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.Algebra

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- The natural endomorphism `φ - 1` of the forgetful functor on complexes with an
endomorphism. This is formed in the category of the fixed scalars. -/
@[expose]
def fixedPointsDifference :
    forget (𝟭 (CochainComplex C ℤ)) ⟶ forget (𝟭 (CochainComplex C ℤ)) where
  -- `id` fixes the arrow type before subtraction: `str` is natively typed from
  -- the identity functor's value, which elaboration need not reduce at this point.
  app M := id (α := M.a ⟶ M.a) M.str - 𝟙 M.a
  naturality M N f := by
    -- Re-elaborate at the carrier: the native forgetful functor and identity functor
    -- have definitionally equal carriers which are not reduced by `simp`'s transparency.
    change f.f ≫ (id (α := N.a ⟶ N.a) N.str - 𝟙 N.a) =
      (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) ≫ f.f
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp]
    exact congrArg (· - f.f) f.h

@[simp]
lemma fixedPointsDifference_app (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    fixedPointsDifference.app M = id (α := M.a ⟶ M.a) M.str - 𝟙 M.a := (rfl)

variable [HasBinaryBiproducts C]

/-- The cochain model for derived fixed points: the mapping cone of `φ - 1`, shifted
by `-1`. Morphisms are induced by the same equivariant map on both cone terms. -/
@[expose, implicit_reducible]
def fixedPointsComplexFunctor :
    Algebra (𝟭 (CochainComplex C ℤ)) ⥤ CochainComplex C ℤ :=
  NatTrans.mappingCoconeFunctor fixedPointsDifference

/-- The cochain model of the derived fixed points of an endomorphism. -/
abbrev fixedPointsComplex (M : Algebra (𝟭 (CochainComplex C ℤ))) : CochainComplex C ℤ :=
  fixedPointsComplexFunctor.obj M

/-- The canonical projection from the fixed-point complex to the original complex. -/
@[implicit_reducible]
def fixedPointsComplexι :
    fixedPointsComplexFunctor (C := C) ⟶ forget (𝟭 (CochainComplex C ℤ)) :=
  NatTrans.mappingCoconeFunctorFst fixedPointsDifference

@[simp]
lemma fixedPointsComplex_eq (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsComplex =
      CochainComplex.mappingCocone (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := (rfl)

@[simp]
lemma fixedPointsComplexι_app (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    fixedPointsComplexι.app M =
      CochainComplex.mappingCocone.fst (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := (rfl)

@[simp]
lemma fixedPointsComplexFunctor_map {M N : Algebra (𝟭 (CochainComplex C ℤ))} (f : M ⟶ N) :
    fixedPointsComplexFunctor.map f =
      (CochainComplex.mappingCone.map (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a)
        (id (α := N.a ⟶ N.a) N.str - 𝟙 N.a) f.f f.f
        (fixedPointsDifference.naturality f).symm)⟦(-1 : ℤ)⟧' := (rfl)

end Preadditive

variable [Abelian C] [HasDerivedCategory.{w} C]

/-- Derived fixed points as a functor to the derived category of the fixed scalars. -/
@[expose, implicit_reducible]
def fixedPointsFunctor :
    Algebra (𝟭 (CochainComplex C ℤ)) ⥤ DerivedCategory C :=
  fixedPointsComplexFunctor ⋙ DerivedCategory.Q

@[simp]
lemma fixedPointsFunctor_map {M N : Algebra (𝟭 (CochainComplex C ℤ))} (f : M ⟶ N) :
    fixedPointsFunctor.map f = DerivedCategory.Q.map (fixedPointsComplexFunctor.map f) := (rfl)

/-- The derived fixed points `fib(φ - 1)`. -/
abbrev fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) : DerivedCategory C :=
  fixedPointsFunctor.obj M

/-- The projection from derived fixed points to the original complex. -/
@[implicit_reducible]
def fixedPointsι (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPoints ⟶ DerivedCategory.Q.obj M.a :=
  DerivedCategory.Q.map (fixedPointsComplexι.app M)

/-- The fixed-point fibre triangle, with second map `φ - 1`. -/
@[expose, implicit_reducible]
def fixedPointsTriangle (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    Triangle (DerivedCategory C) :=
  DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a))

@[simp]
lemma fixedPointsTriangle_obj₁ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.obj₁ = M.fixedPoints := (rfl)

@[simp]
lemma fixedPointsTriangle_obj₂ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.obj₂ = DerivedCategory.Q.obj M.a := (rfl)

@[simp]
lemma fixedPointsTriangle_obj₃ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.obj₃ = DerivedCategory.Q.obj M.a := (rfl)

@[simp]
lemma fixedPointsTriangle_mor₁ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.mor₁ = M.fixedPointsι := (rfl)

@[simp]
lemma fixedPointsTriangle_mor₂ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.mor₂ = DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) - 𝟙 _ := by
  simp [fixedPointsTriangle]

@[simp]
lemma fixedPointsTriangle_mor₃ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.mor₃ =
      DerivedCategory.Q.map
        (CochainComplex.mappingCocone.triangle (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app M.fixedPointsComplex := (rfl)

/-- The fixed-point fibre triangle is distinguished. -/
theorem fixedPointsTriangle_distinguished (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle ∈ distTriang (DerivedCategory C) :=
  DerivedCategory.mappingCocone_triangle_distinguished _

@[reassoc]
lemma fixedPointsι_comp (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsι ≫ (DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) - 𝟙 _) = 0 := by
  rw [← fixedPointsTriangle_mor₂]
  exact comp_distTriang_mor_zero₁₂ _ M.fixedPointsTriangle_distinguished

@[reassoc (attr := simp)]
lemma fixedPointsι_comp_map_str (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsι ≫ DerivedCategory.Q.map M.str = M.fixedPointsι := by
  simpa only [Preadditive.comp_sub, Category.comp_id, sub_eq_zero, id_eq] using M.fixedPointsι_comp

@[reassoc]
lemma fixedPointsι_naturality {M N : Algebra (𝟭 (CochainComplex C ℤ))} (f : M ⟶ N) :
    fixedPointsFunctor.map f ≫ N.fixedPointsι = M.fixedPointsι ≫ DerivedCategory.Q.map f.f := by
  exact (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.Q.map) (fixedPointsComplexι.naturality f)).trans
      (DerivedCategory.Q.map_comp _ _))

/-- An equivariant quasi-isomorphism induces an isomorphism on derived fixed points. -/
instance isIso_fixedPointsFunctor_map {M N : Algebra (𝟭 (CochainComplex C ℤ))}
    (f : M ⟶ N) [QuasiIso f.f] : IsIso (fixedPointsFunctor.map f) := by
  let φ : M.a ⟶ M.a := fixedPointsDifference.app M
  let ψ : N.a ⟶ N.a := fixedPointsDifference.app N
  have h : φ ≫ f.f = f.f ≫ ψ := (fixedPointsDifference.naturality f).symm
  have : QuasiIso (CochainComplex.mappingCone.map φ ψ f.f f.f h) :=
    CochainComplex.mappingCone.quasiIso_map (C := C) φ ψ f.f f.f h
  -- The fixed-point map is definitionally `Q.map` of the shifted cone map. Giving the
  -- cochain morphism explicitly avoids unfolding forgetful carriers during instance synthesis.
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    ((CochainComplex.mappingCone.map φ ψ f.f f.f h)⟦(-1 : ℤ)⟧')))

/-- Derived fixed points vanish precisely when `φ - 1` is a quasi-isomorphism. -/
theorem isZero_fixedPoints_iff (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    IsZero M.fixedPoints ↔ QuasiIso (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact M.fixedPointsTriangle.isZero₁_iff_isIso₂ M.fixedPointsTriangle_distinguished

/-- Derived fixed points preserve a lower cohomological bound. -/
theorem isGE_fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) (a : ℤ)
    [(DerivedCategory.Q.obj M.a).IsGE a] : M.fixedPoints.IsGE a := by
  have : M.fixedPointsTriangle.obj₂.IsGE a := by simpa using (inferInstance :
    (DerivedCategory.Q.obj M.a).IsGE a)
  have : M.fixedPointsTriangle.obj₃.IsGE a := by simpa using (inferInstance :
    (DerivedCategory.Q.obj M.a).IsGE a)
  exact M.fixedPointsTriangle.isGE_obj₁ M.fixedPointsTriangle_distinguished a

/-- Derived fixed points increase an upper cohomological bound by at most one. -/
theorem isLE_fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) (b : ℤ)
    [(DerivedCategory.Q.obj M.a).IsLE b] : M.fixedPoints.IsLE (b + 1) := by
  have : M.fixedPointsTriangle.obj₂.IsLE b := by simpa using (inferInstance :
    (DerivedCategory.Q.obj M.a).IsLE b)
  have : M.fixedPointsTriangle.obj₃.IsLE b := by simpa using (inferInstance :
    (DerivedCategory.Q.obj M.a).IsLE b)
  exact M.fixedPointsTriangle.isLE_obj₁ M.fixedPointsTriangle_distinguished b

/-! The identity on an object in degree zero has that object as its degree-one
fixed-point cohomology. In particular this applies to a nonzero `𝔽_p`-module. -/

example (X : C) :
    let M : Algebra (𝟭 (CochainComplex C ℤ)) :=
      ⟨(CochainComplex.singleFunctor C 0).obj X, 𝟙 _⟩
    (DerivedCategory.homologyFunctor C 1).obj M.fixedPoints ≅ X := by
  intro M
  have hz : IsZero ((DerivedCategory.homologyFunctor C 1).obj
      (DerivedCategory.Q.obj M.a)) :=
    DerivedCategory.isZero_of_isLE _ 0 1 (by omega)
  have hφ : (DerivedCategory.homologyFunctor C 0).map M.fixedPointsTriangle.mor₂ = 0 := by
    simp [M]
  exact M.fixedPointsTriangle.cohomologyIsoCokernel M.fixedPointsTriangle_distinguished 1 hz ≪≫
    cokernelIsoOfEq hφ ≪≫ cokernelZeroIsoTarget ≪≫
    (DerivedCategory.homologyFunctorFactors C 0).app M.a ≪≫
    (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).app X

/-! Zero Frobenius has no derived fixed points, even on an unbounded complex. -/

example (K : CochainComplex C ℤ) :
    IsZero (fixedPoints (⟨K, 0⟩ : Algebra (𝟭 (CochainComplex C ℤ)))) := by
  rw [isZero_fixedPoints_iff]
  simp only [id_eq, zero_sub]
  have : IsIso (-𝟙 K) := inferInstanceAs (IsIso (-Iso.refl K).hom)
  infer_instance

end CategoryTheory.Endofunctor.Algebra
