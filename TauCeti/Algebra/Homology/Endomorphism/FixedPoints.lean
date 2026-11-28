/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import TauCeti.Algebra.Homology.DerivedCategory.MappingCone
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic
public import TauCeti.CategoryTheory.Triangulated.HomologyShortExactSequence
import TauCeti.CategoryTheory.Triangulated.TStructure.Bounds

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
`Triangle.homologyShortExactSequence`, applied to the fixed-point triangle and
`DerivedCategory.homologyFunctor C 0`, and `Triangle.homologyIsoKernel` and
`Triangle.homologyIsoCokernel`. The functor `TauCeti.fixedPointsTriangleFunctor` gives the map of
fixed-point triangles and hence the map of short exact sequences.
No enhancement or category of homotopy-coherent endomorphisms is constructed here.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, §9, Lemma 9.2.
* B. Bhatt and J. Lurie, *Absolute prismatic cohomology*, Example 8.1.3.
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Endofunctor.Algebra (forget)

namespace TauCeti

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

-- The endpoint types of the characteristic equations for fixed-point maps require
-- the object parts of the difference and the fixed-point functors to reduce.
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
lemma fixedPointsDifference_app (M : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))) :
    fixedPointsDifference.app M = id (α := M.a ⟶ M.a) M.str - 𝟙 M.a := (rfl)

variable [HasBinaryBiproducts C]

/-- The cochain model for derived fixed points: the mapping cone of `φ - 1`, shifted
by `-1`. Morphisms are induced by the same equivariant map on both cone terms. -/
@[expose, implicit_reducible]
def fixedPointsComplexFunctor :
    Endofunctor.Algebra (𝟭 (CochainComplex C ℤ)) ⥤ CochainComplex C ℤ :=
  NatTrans.mappingCoconeFunctor fixedPointsDifference

/-- The canonical projection from the fixed-point complex to the original complex. -/
@[expose, implicit_reducible]
def fixedPointsComplexι :
    fixedPointsComplexFunctor (C := C) ⟶ forget (𝟭 (CochainComplex C ℤ)) :=
  NatTrans.mappingCoconeFunctorFst fixedPointsDifference

@[simp]
lemma fixedPointsComplexι_app (M : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))) :
    fixedPointsComplexι.app M =
      CochainComplex.mappingCocone.fst (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := (rfl)

@[simp]
lemma fixedPointsComplexFunctor_map {M N : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))}
    (f : M ⟶ N) :
    fixedPointsComplexFunctor.map f =
      (CochainComplex.mappingCone.map (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a)
        (id (α := N.a ⟶ N.a) N.str - 𝟙 N.a) f.f f.f
        (fixedPointsDifference.naturality f).symm)⟦(-1 : ℤ)⟧' := (rfl)

end Preadditive

variable [Abelian C] [HasDerivedCategory.{w} C]

/-- Derived fixed points as a functor to the derived category of the fixed scalars. -/
@[expose, implicit_reducible]
def fixedPointsFunctor :
    Endofunctor.Algebra (𝟭 (CochainComplex C ℤ)) ⥤ DerivedCategory C :=
  fixedPointsComplexFunctor ⋙ DerivedCategory.Q

@[simp]
lemma fixedPointsFunctor_map {M N : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))} (f : M ⟶ N) :
    fixedPointsFunctor.map f = DerivedCategory.Q.map (fixedPointsComplexFunctor.map f) := (rfl)

open CochainComplex in
/-- The distinguished fixed-point fibre triangles and their induced morphisms. -/
@[expose]
def fixedPointsTriangleFunctor :
    Endofunctor.Algebra (𝟭 (CochainComplex C ℤ)) ⥤ Triangle (DerivedCategory C) where
  obj M := DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle (fixedPointsDifference.app M))
  map {M N} f := DerivedCategory.Q.mapTriangle.map
    (show mappingCocone.triangle (fixedPointsDifference.app M) ⟶
        mappingCocone.triangle (fixedPointsDifference.app N) from
    { hom₁ := fixedPointsComplexFunctor.map f
      hom₂ := f.f
      hom₃ := f.f
      comm₁ := (fixedPointsComplexι.naturality f).symm
      comm₂ := (fixedPointsDifference.naturality f).symm
      comm₃ := by
        -- The third arrow is the cone inclusion followed by the inverse double-shift
        -- comparison. Use naturality of that comparison and the cone triangle map.
        let e := shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)
        let α := mappingCone.triangleMap _ _ f.f f.f (fixedPointsDifference.naturality f).symm
        let S : ℤ → _ := CategoryTheory.shiftFunctor (CochainComplex C ℤ)
        change ((mappingCone.triangle (fixedPointsDifference.app M)).mor₂ ≫ e.inv.app _) ≫
          (S (-1) ⋙ S 1).map α.hom₃ =
            f.f ≫ (mappingCone.triangle (fixedPointsDifference.app N)).mor₂ ≫ e.inv.app _
        rw [Category.assoc]
        calc
          _ = _ ≫ (α.hom₃ ≫ e.inv.app _) :=
            congrArg (_ ≫ ·) (e.inv.naturality α.hom₃).symm
          _ = (_ ≫ α.hom₃) ≫ _ := (Category.assoc _ _ _).symm
          _ = (α.hom₂ ≫ _) ≫ _ := congrArg (· ≫ _) α.comm₂
          _ = _ := Category.assoc _ _ _ })
  map_id M := by
    ext
    · exact fixedPointsFunctor.map_id M
    · exact DerivedCategory.Q.map_id _
    · exact DerivedCategory.Q.map_id _
  map_comp f g := by
    refine TriangleMorphism.ext ?_ ?_ ?_
    · exact fixedPointsFunctor.map_comp f g
    · exact DerivedCategory.Q.map_comp _ _
    · exact DerivedCategory.Q.map_comp _ _

@[simp]
lemma fixedPointsTriangleFunctor_map_hom₁ {M N : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))}
    (f : M ⟶ N) : (fixedPointsTriangleFunctor.map f).hom₁ = fixedPointsFunctor.map f := (rfl)

@[simp]
lemma fixedPointsTriangleFunctor_map_hom₂ {M N : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))}
    (f : M ⟶ N) : (fixedPointsTriangleFunctor.map f).hom₂ = DerivedCategory.Q.map f.f := (rfl)

@[simp]
lemma fixedPointsTriangleFunctor_map_hom₃ {M N : Endofunctor.Algebra (𝟭 (CochainComplex C ℤ))}
    (f : M ⟶ N) : (fixedPointsTriangleFunctor.map f).hom₃ = DerivedCategory.Q.map f.f := (rfl)

end TauCeti

namespace CategoryTheory.Endofunctor.Algebra

open TauCeti

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The cochain model of the derived fixed points of an endomorphism. -/
abbrev fixedPointsComplex (M : Algebra (𝟭 (CochainComplex C ℤ))) : CochainComplex C ℤ :=
  fixedPointsComplexFunctor.obj M

@[simp]
lemma fixedPointsComplex_eq (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsComplex =
      CochainComplex.mappingCocone (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := (rfl)

end Preadditive

variable [Abelian C] [HasDerivedCategory.{w} C]

/-- The derived fixed points `fib(φ - 1)`. -/
abbrev fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) : DerivedCategory C :=
  fixedPointsFunctor.obj M

/-- Derived fixed points are the localization of their cochain model. -/
lemma fixedPoints_eq (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPoints = DerivedCategory.Q.obj M.fixedPointsComplex := (rfl)

/-- The projection from derived fixed points to the original complex. -/
@[implicit_reducible]
def fixedPointsι (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPoints ⟶ DerivedCategory.Q.obj M.a :=
  DerivedCategory.Q.map (fixedPointsComplexι.app M)

/-- The derived projection is the localization of the cochain projection. -/
lemma fixedPointsι_eq (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsι = DerivedCategory.Q.map (fixedPointsComplexι.app M) := (rfl)

/-- The fixed-point fibre triangle, with second map `φ - 1`. -/
@[expose, implicit_reducible]
def fixedPointsTriangle (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    Triangle (DerivedCategory C) :=
  fixedPointsTriangleFunctor.obj M

@[simp]
lemma fixedPointsTriangleFunctor_obj (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    fixedPointsTriangleFunctor.obj M = M.fixedPointsTriangle := (rfl)

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
  -- The mapping cocone's second arrow is its defining map. Unfold the localized
  -- triangle's second arrow so that additivity of Q applies to the cochain difference.
  change DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) = _
  calc
    _ = DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) -
        DerivedCategory.Q.map (𝟙 M.a) := Functor.map_sub _
    _ = _ := congrArg (_ - ·) (DerivedCategory.Q.map_id M.a)

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
lemma fixedPointsι_comp_sub_eq_zero (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsι ≫ (DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) - 𝟙 _) = 0 := by
  calc
    _ = M.fixedPointsTriangle.mor₁ ≫ M.fixedPointsTriangle.mor₂ :=
      congrArg (M.fixedPointsι ≫ ·) M.fixedPointsTriangle_mor₂.symm
    _ = 0 := comp_distTriang_mor_zero₁₂ _ M.fixedPointsTriangle_distinguished

@[reassoc (attr := simp)]
lemma fixedPointsι_comp_map_str (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsι ≫ DerivedCategory.Q.map M.str = M.fixedPointsι := by
  simpa only [Preadditive.comp_sub, Category.comp_id, sub_eq_zero, id_eq]
    using M.fixedPointsι_comp_sub_eq_zero

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
  rw [← M.fixedPointsTriangle_obj₁]
  refine (M.fixedPointsTriangle.isZero₁_iff_isIso₂ M.fixedPointsTriangle_distinguished).trans ?_
  have h : DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) =
      DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) - 𝟙 (DerivedCategory.Q.obj M.a) :=
    (Functor.map_sub DerivedCategory.Q).trans (congrArg (_ - ·) (DerivedCategory.Q.map_id M.a))
  exact Iff.of_eq (congrArg IsIso (M.fixedPointsTriangle_mor₂.trans h.symm))

/-- Derived fixed points preserve a lower cohomological bound. -/
theorem isGE_fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) (a : ℤ)
    [(DerivedCategory.Q.obj M.a).IsGE a] : M.fixedPoints.IsGE a := by
  rw [← fixedPointsTriangle_obj₁]
  refine DerivedCategory.TStructure.t.isGE₁ _ M.fixedPointsTriangle_distinguished a ?_ ?_
  · simpa using (inferInstance : (DerivedCategory.Q.obj M.a).IsGE a)
  · simpa using DerivedCategory.TStructure.t.isGE_of_ge (DerivedCategory.Q.obj M.a) (a - 1) a

/-- Derived fixed points increase an upper cohomological bound by at most one. -/
theorem isLE_fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) (b : ℤ)
    [(DerivedCategory.Q.obj M.a).IsLE b] : M.fixedPoints.IsLE (b + 1) := by
  rw [← fixedPointsTriangle_obj₁]
  refine DerivedCategory.TStructure.t.isLE₁ _ M.fixedPointsTriangle_distinguished (b + 1) ?_ ?_
  · simpa using DerivedCategory.TStructure.t.isLE_of_le (DerivedCategory.Q.obj M.a) b (b + 1)
  · simpa using (inferInstance : (DerivedCategory.Q.obj M.a).IsLE b)

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
    rw [M.fixedPointsTriangle_mor₂]
    -- The local algebra M was constructed with identity structure map. Reduce that
    -- projection to the identity on M.a so that Functor.map_id matches.
    change (DerivedCategory.homologyFunctor C 0).map
      (DerivedCategory.Q.map (𝟙 M.a) - 𝟙 (DerivedCategory.Q.obj M.a)) = 0
    rw [Functor.map_id, sub_self, Functor.map_zero]
  have : Mono (((DerivedCategory.homologyFunctor C 0).shift (1 : ℤ)).map
      M.fixedPointsTriangle.mor₂) :=
    mono_of_source_iso_zero _ (by
      rw [fixedPointsTriangle_obj₂]
      exact hz.isoZero)
  exact M.fixedPointsTriangle.homologyIsoCokernel (DerivedCategory.homologyFunctor C 0)
    M.fixedPointsTriangle_distinguished 1 ≪≫
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
