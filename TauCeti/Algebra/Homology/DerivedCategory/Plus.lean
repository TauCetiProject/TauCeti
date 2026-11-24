/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import TauCeti.Algebra.Homology.CochainComplex.Plus

/-!
# Localization infrastructure for the bounded-below derived category

Mathlib defines `DerivedCategory.Plus C` as the localization of `CochainComplex.Plus C` at
quasi-isomorphisms. Building on the complex-level lifts in
`TauCeti/Algebra/Homology/CochainComplex/Plus.lean`, this file supplies the localization
compatibilities needed to compute and compare functors on `DerivedCategory.Plus C`:

* the compatibility `DerivedCategory.Plus.singleFunctorIsoCompQ` between
  `DerivedCategory.Plus.singleFunctor` and `CochainComplex.Plus.singleFunctor ⋙ Q`;
* the factorization `DerivedCategory.Plus.homologyFunctorFactors` of
  `DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n` through complex cohomology,
  together with quasi-isomorphism inversion (`DerivedCategory.Plus.isIso_Q_map_iff_quasiIso`),
  chain-homotopy invariance (`DerivedCategory.Plus.Q_map_eq_of_homotopy`), and `t`-structure support
  characterizations (`DerivedCategory.Plus.isGE_Q_obj_iff`, `DerivedCategory.Plus.isLE_Q_obj_iff`);
* distinguished triangles in `DerivedCategory.Plus C` attached to short exact sequences of
  bounded-below complexes (`DerivedCategory.Plus.triangleOfSES`) and to mapping cones
  (`DerivedCategory.Plus.mappingCone_triangle_distinguished`).

## References

* The Stacks Project, Derived Categories, Section 13.11 (tag 05RU) and Section 13.12 (tag 05S7).
-/

public section

noncomputable section

open CategoryTheory Category Functor Limits Pretriangulated Triangulated HomologicalComplex

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

variable (C) in
/-- The single functor into `DerivedCategory.Plus C` factors through
`CochainComplex.Plus.singleFunctor C n` and localization `DerivedCategory.Plus.Q`. -/
def singleFunctorIsoCompQ (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.Plus.singleFunctor C n ⋙ Q :=
  ((_root_.DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.whiskeringRight C).preimageIso
    (singleFunctorιIso C n ≪≫ DerivedCategory.singleFunctorIsoCompQ C n ≪≫
      isoWhiskerRight (CochainComplex.Plus.singleFunctorCompιIso C n).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (QCompιIso C).symm ≪≫ (Functor.associator _ _ _).symm)

variable (C) in
/-- On `CochainComplex.Plus C`, the derived-category cohomology functor after `Q` is naturally
isomorphic to complex cohomology. -/
def homologyFunctorFactors (n : ℤ) :
    Q ⋙ homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n :=
  (Functor.associator Q ι (DerivedCategory.homologyFunctor C n)).symm ≪≫
    isoWhiskerRight (QCompιIso C) (DerivedCategory.homologyFunctor C n) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.homologyFunctorFactors C n)

/-- A morphism in `CochainComplex.Plus C` becomes an isomorphism in `DerivedCategory.Plus C` if
and only if its underlying morphism of complexes is a quasi-isomorphism. -/
lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex.Plus C} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ.hom := by
  rw [← isIso_iff_of_reflects_iso (Q.map φ) ι]
  exact ((MorphismProperty.isomorphisms (DerivedCategory C)).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (QCompιIso C)).app (Arrow.mk φ))).trans
    (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.hom)

instance {K L : CochainComplex.Plus C} (φ : K ⟶ L) [QuasiIso φ.hom] : IsIso (Q.map φ) :=
  (isIso_Q_map_iff_quasiIso φ).2 inferInstance

/-- Chain-homotopic morphisms in `CochainComplex.Plus C` map to the same morphism in
`DerivedCategory.Plus C`. -/
lemma Q_map_eq_of_homotopy {K L : CochainComplex.Plus C} {f g : K ⟶ L}
    (h : Homotopy f.hom g.hom) : Q.map f = Q.map g := by
  ext : 1
  have hf := NatIso.naturality_2 (QCompιIso C) f
  have hg := NatIso.naturality_2 (QCompιIso C) g
  dsimp at hf hg
  rw [← hf, ← hg, DerivedCategory.Q_map_eq_of_homotopy C h]

/-- `Q.obj K` lies in `D^{≥ n}` if and only if the underlying complex `K.obj` is cohomologically
`≥ n`. -/
lemma isGE_Q_obj_iff (K : CochainComplex.Plus C) (n : ℤ) :
    (Q.obj K).IsGE n ↔ K.obj.IsGE n := by
  rw [← isGE_ι_obj_iff, ← DerivedCategory.isGE_Q_obj_iff K.obj n]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : DerivedCategory.TStructure.t.IsGE ((Q ⋙ ι).obj K) n := h
    exact DerivedCategory.TStructure.t.isGE_of_iso ((QCompιIso C).app K) n
  · have : DerivedCategory.TStructure.t.IsGE
        ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q).obj K) n := h
    exact DerivedCategory.TStructure.t.isGE_of_iso ((QCompιIso C).symm.app K) n

/-- `Q.obj K` lies in `D^{≤ n}` if and only if the underlying complex `K.obj` is cohomologically
`≤ n`. -/
lemma isLE_Q_obj_iff (K : CochainComplex.Plus C) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.obj.IsLE n := by
  rw [← isLE_ι_obj_iff, ← DerivedCategory.isLE_Q_obj_iff K.obj n]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : DerivedCategory.TStructure.t.IsLE ((Q ⋙ ι).obj K) n := h
    exact DerivedCategory.TStructure.t.isLE_of_iso ((QCompιIso C).app K) n
  · have : DerivedCategory.TStructure.t.IsLE
        ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q).obj K) n := h
    exact DerivedCategory.TStructure.t.isLE_of_iso ((QCompιIso C).symm.app K) n

instance (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsGE n] : (Q.obj K).IsGE n :=
  (isGE_Q_obj_iff K n).2 inferInstance

instance (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsStrictlyGE n] : (Q.obj K).IsGE n :=
  (isGE_Q_obj_iff K n).2 inferInstance

instance (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsLE n] : (Q.obj K).IsLE n :=
  (isLE_Q_obj_iff K n).2 inferInstance

instance (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsStrictlyLE n] : (Q.obj K).IsLE n :=
  (isLE_Q_obj_iff K n).2 inferInstance

/-- The image in `DerivedCategory.Plus C` of the mapping cone triangle of a morphism in
`CochainComplex.Plus C` is distinguished. -/
lemma mappingCone_triangle_distinguished {K L : CochainComplex.Plus C} (φ : K ⟶ L) :
    Q.mapTriangle.obj (CochainComplex.Plus.mappingConeTriangle φ) ∈
      distTriang (DerivedCategory.Plus C) :=
  (ι.map_distinguished_iff _).1 <| isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished φ.hom) _
    ((Functor.mapTriangleCompIso Q ι).symm.app _ ≪≫
      (Functor.mapTriangleIso (QCompιIso C)).app _ ≪≫
      (Functor.mapTriangleCompIso (CochainComplex.Plus.ι C) DerivedCategory.Q).app _ ≪≫
      DerivedCategory.Q.mapTriangle.mapIso (CochainComplex.Plus.mappingConeTriangleιIso φ))

/-- The connecting morphism `Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦1⟧` in `DerivedCategory.Plus C` attached to
a short exact sequence in `CochainComplex.Plus C`. -/
def triangleOfSESδ {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk ((QCompιIso C).hom.app S.X₃ ≫ DerivedCategory.triangleOfSESδ hS ≫
    ((QCompιIso C).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫ (ι.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁))

@[simp]
lemma triangleOfSESδ_hom {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    (triangleOfSESδ hS).hom = (QCompιIso C).hom.app S.X₃ ≫ DerivedCategory.triangleOfSESδ hS ≫
      ((QCompιIso C).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫ (ι.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁) :=
  (rfl)

/-- The triangle in `DerivedCategory.Plus C` attached to a short exact sequence of bounded-below
cochain complexes. -/
abbrev triangleOfSES {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

/-- Inclusion into `DerivedCategory C` identifies `DerivedCategory.Plus.triangleOfSES hS` with
`DerivedCategory.triangleOfSES hS`. -/
def triangleOfSESιIso {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    ι.mapTriangle.obj (triangleOfSES hS) ≅ DerivedCategory.triangleOfSES hS :=
  Triangle.isoMk _ _ ((QCompιIso C).app S.X₁) ((QCompιIso C).app S.X₂) ((QCompιIso C).app S.X₃)
    ((QCompιIso C).hom.naturality S.f) ((QCompιIso C).hom.naturality S.g) <| by
    dsimp only [triangleOfSES, DerivedCategory.triangleOfSES]
    simp only [Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_mor₃,
      ObjectProperty.ι_map, triangleOfSESδ_hom, Iso.app_hom, assoc]
    rw [Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    refine (?_ : _ = (QCompιIso C).hom.app S.X₃ ≫
        DerivedCategory.triangleOfSESδ hS ≫ 𝟙 _).trans (by simp)
    congr 2
    exact (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id _

/-- A short exact sequence of bounded-below complexes induces a distinguished triangle in
`DerivedCategory.Plus C`. -/
lemma triangleOfSES_distinguished {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    triangleOfSES hS ∈ distTriang (DerivedCategory.Plus C) :=
  (ι.map_distinguished_iff (triangleOfSES hS)).1 <|
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
      (triangleOfSESιIso hS)

/-- Naturality of the connecting morphism `triangleOfSESδ` with respect to morphisms of short
exact sequences in `CochainComplex.Plus C`. -/
@[reassoc]
lemma triangleOfSESδ_naturality {S₁ S₂ : ShortComplex (CochainComplex.Plus C)}
    (hS₁ : (S₁.map (CochainComplex.Plus.ι C)).ShortExact)
    (hS₂ : (S₂.map (CochainComplex.Plus.ι C)).ShortExact) (φ : S₁ ⟶ S₂) :
    triangleOfSESδ hS₁ ≫ (Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      Q.map φ.τ₃ ≫ triangleOfSESδ hS₂ := by
  ext : 1
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    triangleOfSESδ_hom, triangleOfSESδ_hom]
  have hcomm := (ι.commShiftIso (1 : ℤ)).inv.naturality (Q.map φ.τ₁)
  have h1 := (QCompιIso C).inv.naturality φ.τ₁
  have h2 := DerivedCategory.triangleOfSESδ_naturality hS₁ hS₂
    ((CochainComplex.Plus.ι C).mapShortComplex.map φ)
  have h3 := (QCompιIso C).hom.naturality φ.τ₃
  dsimp at hcomm h1 h2 h3
  simp only [assoc]
  rw [← hcomm, ← cancel_mono ((ι.commShiftIso (1 : ℤ)).hom.app (Q.obj S₂.X₁))]
  simp only [assoc, Iso.inv_hom_id_app]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← h1, CategoryTheory.Functor.map_comp_assoc,
    reassoc_of% h2, reassoc_of% h3]

end DerivedCategory.Plus
