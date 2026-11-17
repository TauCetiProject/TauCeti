/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc

/-!
# Infrastructure for bounded-below complexes and the bounded-below derived category

Mathlib defines the full subcategory `CochainComplex.Plus C` of bounded-below `ℤ`-indexed cochain
complexes and its localization `DerivedCategory.Plus C` at quasi-isomorphisms. This file supplies
the complex-level lifts and localization compatibilities needed to compute and compare functors on
`DerivedCategory.Plus C`:

* single-complex and nonnegative-extension functors into `CochainComplex.Plus C`
  (`CochainComplex.Plus.singleFunctor`, `CochainComplex.Plus.extendNat`), together with the
  compatibility `DerivedCategory.Plus.singleFunctorIsoCompQ` between
  `DerivedCategory.Plus.singleFunctor` and `CochainComplex.Plus.singleFunctor ⋙ Q`;
* canonical downward truncation (`CochainComplex.Plus.truncLE`) and downward stupid truncation
  (`CochainComplex.Plus.stupidTruncLE`) within `CochainComplex.Plus C`;
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

namespace CochainComplex.Plus

section HasZeroMorphisms

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- Bundle a `ℤ`-indexed cochain complex strictly supported in degrees `≥ b` as an object of
`CochainComplex.Plus C`. -/
abbrev ofIsStrictlyGE (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b] : CochainComplex.Plus C :=
  ⟨K, b, inferInstance⟩

@[simp]
lemma ofIsStrictlyGE_obj (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b] :
    (ofIsStrictlyGE K b).obj = K := (rfl)

instance (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b] :
    (ofIsStrictlyGE K b).obj.IsStrictlyGE b := by
  dsimp [ofIsStrictlyGE]
  infer_instance

section HasZeroObject

variable [HasZeroObject C]

variable (C) in
/-- Extending a nonnegative cochain complex by zeros in negative degrees lands in
`CochainComplex.Plus C`. -/
abbrev extendNat : CochainComplex C ℕ ⥤ CochainComplex.Plus C where
  obj K := ⟨K.extend ComplexShape.embeddingUpNat,
    (CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩
  map φ := ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  map_id K := by
    ext : 1
    exact HomologicalComplex.extendMap_id K ComplexShape.embeddingUpNat
  map_comp f g := by
    ext : 1
    exact HomologicalComplex.extendMap_comp f g ComplexShape.embeddingUpNat

@[simp]
lemma extendNat_obj_obj (K : CochainComplex C ℕ) :
    ((extendNat C).obj K).obj = K.extend ComplexShape.embeddingUpNat := (rfl)

@[simp]
lemma extendNat_map_hom {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    ((extendNat C).map φ).hom = HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat := (rfl)

variable (C) in
/-- Forgetting the lower bound after `extendNat` recovers extension along `ℕ ↪ ℤ`. -/
def extendNatCompιIso :
    extendNat C ⋙ ι C ≅ ComplexShape.embeddingUpNat.extendFunctor C :=
  Iso.refl _

@[simp]
lemma extendNatCompιIso_hom_app (K : CochainComplex C ℕ) :
    (extendNatCompιIso C).hom.app K = 𝟙 (K.extend ComplexShape.embeddingUpNat) := (rfl)

@[simp]
lemma extendNatCompιIso_inv_app (K : CochainComplex C ℕ) :
    (extendNatCompιIso C).inv.app K = 𝟙 (K.extend ComplexShape.embeddingUpNat) := (rfl)

instance (X : CochainComplex C ℕ) : ((extendNat C).obj X).obj.IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE (X.extend ComplexShape.embeddingUpNat) 0)

/-- Downward stupid truncation `σ_{≤ n}` preserves `CochainComplex.Plus C`. -/
abbrev stupidTruncLE (K : CochainComplex.Plus C) (n : ℤ) : CochainComplex.Plus C :=
  ⟨K.obj.stupidTrunc (ComplexShape.embeddingUpIntLE n),
    let ⟨b, _⟩ := K.property
    ⟨b, inferInstance⟩⟩

instance (K : CochainComplex.Plus C) (n b : ℤ) [K.obj.IsStrictlyGE b] :
    (K.stupidTruncLE n).obj.IsStrictlyGE b := by
  dsimp [stupidTruncLE]
  infer_instance

instance (K : CochainComplex.Plus C) (n : ℤ) :
    (K.stupidTruncLE n).obj.IsStrictlyLE n := by
  dsimp [stupidTruncLE]
  infer_instance

/-- The canonical quotient map `K ⟶ K.stupidTruncLE n` in `CochainComplex.Plus C`. -/
abbrev πStupidTruncLE (K : CochainComplex.Plus C) (n : ℤ) : K ⟶ K.stupidTruncLE n :=
  ObjectProperty.homMk (K.obj.πStupidTrunc (ComplexShape.embeddingUpIntLE n))

@[simp]
lemma πStupidTruncLE_hom (K : CochainComplex.Plus C) (n : ℤ) :
    (K.πStupidTruncLE n).hom = K.obj.πStupidTrunc (ComplexShape.embeddingUpIntLE n) := (rfl)

/-- The morphism `K.stupidTruncLE n ⟶ L.stupidTruncLE n` induced by `φ : K ⟶ L`. -/
def stupidTruncLEMap {K L : CochainComplex.Plus C} (φ : K ⟶ L) (n : ℤ) :
    K.stupidTruncLE n ⟶ L.stupidTruncLE n :=
  ObjectProperty.homMk (HomologicalComplex.stupidTruncMap φ.hom (ComplexShape.embeddingUpIntLE n))

@[simp]
lemma stupidTruncLEMap_hom {K L : CochainComplex.Plus C} (φ : K ⟶ L) (n : ℤ) :
    (stupidTruncLEMap φ n).hom =
      HomologicalComplex.stupidTruncMap φ.hom (ComplexShape.embeddingUpIntLE n) := (rfl)

@[reassoc (attr := simp)]
lemma πStupidTruncLE_naturality {K L : CochainComplex.Plus C} (φ : K ⟶ L) (n : ℤ) :
    K.πStupidTruncLE n ≫ stupidTruncLEMap φ n = φ ≫ L.πStupidTruncLE n := by
  ext : 1
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    πStupidTruncLE_hom, stupidTruncLEMap_hom, πStupidTruncLE_hom]
  exact HomologicalComplex.πStupidTrunc_naturality φ.hom (ComplexShape.embeddingUpIntLE n)

section Trunc

variable (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]

/-- Canonical truncation `τ_{≤ n}` preserves `CochainComplex.Plus C`. -/
abbrev truncLE (n : ℤ) : CochainComplex.Plus C :=
  ⟨K.obj.truncLE n,
    let ⟨b, _⟩ := K.property
    ⟨b, inferInstance⟩⟩

instance (n b : ℤ) [K.obj.IsStrictlyGE b] : (K.truncLE n).obj.IsStrictlyGE b := by
  dsimp [truncLE]
  infer_instance

instance (n : ℤ) : (K.truncLE n).obj.IsLE n := by
  dsimp [truncLE]
  infer_instance

/-- The canonical embedding `K.truncLE n ⟶ K` in `CochainComplex.Plus C`. -/
abbrev ιTruncLE (n : ℤ) : K.truncLE n ⟶ K :=
  ObjectProperty.homMk (K.obj.ιTruncLE n)

@[simp]
lemma ιTruncLE_hom (n : ℤ) : (K.ιTruncLE n).hom = K.obj.ιTruncLE n := (rfl)

variable {K} {L : CochainComplex.Plus C} [∀ i, L.obj.HasHomology i]

/-- The morphism `K.truncLE n ⟶ L.truncLE n` induced by `φ : K ⟶ L`. -/
def truncLEMap (φ : K ⟶ L) (n : ℤ) : K.truncLE n ⟶ L.truncLE n :=
  ObjectProperty.homMk (CochainComplex.truncLEMap φ.hom n)

@[simp]
lemma truncLEMap_hom (φ : K ⟶ L) (n : ℤ) :
    (truncLEMap φ n).hom = CochainComplex.truncLEMap φ.hom n := (rfl)

@[reassoc (attr := simp)]
lemma ιTruncLE_naturality (φ : K ⟶ L) (n : ℤ) :
    truncLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ := by
  ext : 1
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    truncLEMap_hom, ιTruncLE_hom, ιTruncLE_hom]
  exact CochainComplex.ιTruncLE_naturality φ.hom n

end Trunc

variable (C) in
/-- Extending a nonnegative complex to `CochainComplex.Plus C` and taking `(n : ℤ)`-th cohomology
is naturally isomorphic to `n`-th cohomology on `CochainComplex C ℕ`. -/
def extendNatHomologyIso [CategoryWithHomology C] (n : ℕ) :
    extendNat C ⋙ ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) (n : ℤ) ≅
      HomologicalComplex.homologyFunctor C (.up ℕ) n :=
  NatIso.ofComponents
    (fun K ↦ K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp))
    fun φ ↦ HomologicalComplex.extendHomologyIso_hom_naturality φ
      ComplexShape.embeddingUpNat (by simp)

/-- The short complex `0 ⟶ ker(π_{≤ n}) ⟶ K ⟶ K.stupidTruncLE n ⟶ 0` in
`CochainComplex.Plus C`. -/
abbrev shortComplexStupidTruncLE [HasEqualizers C] (K : CochainComplex.Plus C) (n : ℤ) :
    ShortComplex (CochainComplex.Plus C) :=
  ShortComplex.mk
    (ObjectProperty.homMk
      (X := ofIsStrictlyGE
        (Limits.kernel (K.obj.πStupidTrunc (ComplexShape.embeddingUpIntLE n))) (n + 1))
      (Limits.kernel.ι (K.obj.πStupidTrunc (ComplexShape.embeddingUpIntLE n))))
    (K.πStupidTruncLE n)
    (by ext : 1; exact Limits.kernel.condition _)

end HasZeroObject

end HasZeroMorphisms

section Preadditive

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C]

/-- The functor sending `X : C` to the bounded-below single complex concentrated in degree `n`. -/
abbrev singleFunctor (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C n) fun _ ↦
    (CochainComplex.plus_iff C _).2 ⟨n, inferInstance⟩

@[simp]
lemma singleFunctor_obj_obj (n : ℤ) (X : C) :
    ((singleFunctor C n).obj X).obj = (CochainComplex.singleFunctor C n).obj X := (rfl)

@[simp]
lemma singleFunctor_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((singleFunctor C n).map f).hom = (CochainComplex.singleFunctor C n).map f := (rfl)

/-- Forgetting the lower bound after `CochainComplex.Plus.singleFunctor` recovers
`CochainComplex.singleFunctor`. -/
def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ CochainComplex.singleFunctor C n :=
  Iso.refl _

@[simp]
lemma singleFunctorCompιIso_hom_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).hom.app X = 𝟙 ((CochainComplex.singleFunctor C n).obj X) := (rfl)

@[simp]
lemma singleFunctorCompιIso_inv_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).inv.app X = 𝟙 ((CochainComplex.singleFunctor C n).obj X) := (rfl)

instance (n : ℤ) : (singleFunctor C n).Additive :=
  have := Functor.additive_of_iso (singleFunctorCompιIso C n).symm
  Functor.additive_of_comp_faithful _ (ι C)

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).obj.IsStrictlyGE n :=
  inferInstanceAs (((CochainComplex.singleFunctor C n).obj X).IsStrictlyGE n)

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).obj.IsStrictlyLE n :=
  inferInstanceAs (((CochainComplex.singleFunctor C n).obj X).IsStrictlyLE n)

/-- Extending a degree-`0` single `ℕ`-indexed cochain complex into `CochainComplex.Plus C`
identifies with `CochainComplex.Plus.singleFunctor C 0`. -/
def extendNatSingle₀Iso :
    CochainComplex.single₀ C ⋙ extendNat C ≅ singleFunctor C 0 :=
  NatIso.ofComponents
    (fun X ↦ (CochainComplex.plus C).isoMk
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 (0 : ℤ) (by simp)))
    fun {X Y} f ↦ by
      ext : 1
      refine HomologicalComplex.to_single_hom_ext ?_
      simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, singleFunctor_map_hom,
        HomologicalComplex.comp_f]
      rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (by simp),
        HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f]
      simp [CochainComplex.single₀, CochainComplex.singleFunctor, HomologicalComplex.single,
        HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

@[simp]
lemma extendNatSingle₀Iso_hom_app_hom (X : C) :
    ((extendNatSingle₀Iso C).hom.app X).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 (0 : ℤ)
        (by simp)).hom := (rfl)

@[simp]
lemma extendNatSingle₀Iso_inv_app_hom (X : C) :
    ((extendNatSingle₀Iso C).inv.app X).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 (0 : ℤ)
        (by simp)).inv := (rfl)

variable {C} in
instance quasiIso_shift_hom [CategoryWithHomology C] {K L : CochainComplex.Plus C} (φ : K ⟶ L)
    [QuasiIso φ.hom] (k : ℤ) : QuasiIso (φ⟦k⟧').hom :=
  (MorphismProperty.IsCompatibleWithShift.iff (CochainComplex.Plus.quasiIso C) φ k).2 ‹_›

variable {C} in
instance quasiIso_extendNatSingle₀Iso_inv_comp_extendNat_map [CategoryWithHomology C] {X : C}
    {K : CochainComplex C ℕ} (ι₀ : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ι₀] :
    QuasiIso (((extendNatSingle₀Iso C).inv.app X ≫ (extendNat C).map ι₀).hom) := by
  have : IsIso (((extendNatSingle₀Iso C).inv.app X).hom) :=
    inferInstanceAs (IsIso ((ι C).map ((extendNatSingle₀Iso C).inv.app X)))
  have : QuasiIso (((extendNat C).map ι₀).hom) :=
    inferInstanceAs (QuasiIso (HomologicalComplex.extendMap ι₀ ComplexShape.embeddingUpNat))
  rw [ObjectProperty.FullSubcategory.comp_hom]
  infer_instance

end Preadditive

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- The short complex `0 ⟶ ker(π_{≤ n}) ⟶ K ⟶ K.stupidTruncLE n ⟶ 0` in `CochainComplex.Plus C`
is short exact in `CochainComplex C ℤ`. -/
lemma shortComplexStupidTruncLE_shortExact (K : CochainComplex.Plus C) (n : ℤ) :
    ((shortComplexStupidTruncLE K n).map (ι C)).ShortExact :=
  let π₀ := K.obj.πStupidTrunc (ComplexShape.embeddingUpIntLE n)
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (Limits.kernelIsKernel π₀))
    (inferInstanceAs (Mono (Limits.kernel.ι π₀)))
    (inferInstanceAs (Epi π₀))

end Abelian

section MappingCone

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The mapping cone of a morphism in `CochainComplex.Plus C`, lifted to `CochainComplex.Plus C`. -/
abbrev mappingCone {K L : CochainComplex.Plus C} (φ : K ⟶ L) : CochainComplex.Plus C :=
  ⟨CochainComplex.mappingCone φ.hom, by
    obtain ⟨a, _⟩ := K.property
    obtain ⟨b, _⟩ := L.property
    exact ⟨min (a - 1) b,
      CochainComplex.isStrictlyGE_mappingCone φ.hom a b (min (a - 1) b) (by lia) (by lia)⟩⟩

/-- The triangle `K ⟶ L ⟶ mappingCone φ ⟶ K⟦1⟧` in `CochainComplex.Plus C`. -/
abbrev mappingConeTriangle {K L : CochainComplex.Plus C} (φ : K ⟶ L) :
    Triangle (CochainComplex.Plus C) :=
  Triangle.mk φ (ObjectProperty.homMk (Y := mappingCone φ) (CochainComplex.mappingCone.inr φ.hom))
    (ObjectProperty.homMk (X := mappingCone φ)
      (HomComplex.Cocycle.homOf
        ((-CochainComplex.mappingCone.fst φ.hom).rightShift 1 0 (zero_add 1)) ≫
        ((ι C).commShiftIso (1 : ℤ)).inv.app K))

/-- Inclusion into `CochainComplex C ℤ` identifies `mappingConeTriangle φ` with
`CochainComplex.mappingCone.triangle φ.hom`. -/
def mappingConeTriangleιIso {K L : CochainComplex.Plus C} (φ : K ⟶ L) :
    (ι C).mapTriangle.obj (mappingConeTriangle φ) ≅
      CochainComplex.mappingCone.triangle φ.hom := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp
  · simp [CochainComplex.mappingCone.triangle]
  · dsimp [mappingConeTriangle, CochainComplex.mappingCone.triangle, ι]
    simp

end MappingCone

end CochainComplex.Plus

namespace CategoryTheory.ShortComplex.ShortExact

/-- In an abelian category, if `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` is a short exact sequence of `ℤ`-indexed
cochain complexes and `K₂` is strictly supported in degrees `≥ b`, then so is `K₃`. -/
lemma isStrictlyGE_X₃ {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (b : ℤ) [S.X₂.IsStrictlyGE b] :
    S.X₃.IsStrictlyGE b := by
  have hSq := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  have : Epi (S.g.f q) := (hSq q).epi_g
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (S.g.f q), comp_id, comp_zero]
  exact (S.X₂.isZero_of_isStrictlyGE b q hq).eq_of_src _ _

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.Functor

section ExtendNat

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroObject C] [HasZeroMorphisms D] [HasZeroObject D]

private def extendNatMapComponentIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex C ℕ) (i' : ℤ) :
    F.obj ((K.extend ComplexShape.embeddingUpNat).X i') ≅
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat).X i' :=
  if hi' : 0 ≤ i' then
    F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := i'.toNat) (i' := i')
        (by simp [Int.toNat_of_nonneg hi'])) ≪≫
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat
        (i := i'.toNat) (i' := i') (by simp [Int.toNat_of_nonneg hi'])).symm
  else
    IsZero.iso
      (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i' fun n hn ↦
        hi' (hn ▸ Int.natCast_nonneg n)))
      (((F.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X ComplexShape.embeddingUpNat i'
        fun n hn ↦ hi' (hn ▸ Int.natCast_nonneg n))

/-- Extending `ℕ`-indexed complexes to `CochainComplex.Plus` commutes with applying an additive
(or zero-morphism-preserving) functor degreewise. -/
def extendNatMapCochainComplexPlusIso (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    CochainComplex.Plus.extendNat C ⋙ F.mapCochainComplexPlus ≅
      F.mapHomologicalComplex (.up ℕ) ⋙ CochainComplex.Plus.extendNat D :=
  NatIso.ofComponents
    (fun K ↦ (CochainComplex.plus D).isoMk <|
      HomologicalComplex.Hom.isoOfComponents
        (C₁ := (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))
        (C₂ := ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat)
        (extendNatMapComponentIso F K) fun i' j' _ ↦ by
          by_cases hi' : 0 ≤ i'
          · by_cases hj' : 0 ≤ j'
            · dsimp only [Functor.mapHomologicalComplex_obj_d]
              unfold extendNatMapComponentIso
              simp only [hi', hj', ↓reduceDIte, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
              rw [K.extend_d_eq ComplexShape.embeddingUpNat (i := i'.toNat) (j := j'.toNat)
                  (by simp [Int.toNat_of_nonneg hi']) (by simp [Int.toNat_of_nonneg hj']),
                ((F.mapHomologicalComplex (.up ℕ)).obj K).extend_d_eq ComplexShape.embeddingUpNat
                  (i := i'.toNat) (j := j'.toNat)
                  (by simp [Int.toNat_of_nonneg hi']) (by simp [Int.toNat_of_nonneg hj'])]
              simp only [CategoryTheory.Functor.map_comp, Functor.mapHomologicalComplex_obj_d,
                assoc, Iso.inv_hom_id_assoc, ← Functor.mapIso_inv, ← Functor.mapIso_hom]
            · exact (((F.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
                ComplexShape.embeddingUpNat j' fun n hn ↦
                  hj' (hn ▸ Int.natCast_nonneg n)).eq_of_tgt _ _
          · exact (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i' fun n hn ↦
              hi' (hn ▸ Int.natCast_nonneg n))).eq_of_src _ _)
    fun {K L} φ ↦ by
      ext i'
      by_cases hi' : 0 ≤ i'
      · simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
          ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
          Functor.mapCochainComplexPlus_map_hom, HomologicalComplex.comp_f,
          HomologicalComplex.Hom.isoOfComponents_hom_f, Functor.mapHomologicalComplex_map_f]
        unfold extendNatMapComponentIso
        simp only [hi', ↓reduceDIte, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
        rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (i := i'.toNat)
            (by simp [Int.toNat_of_nonneg hi']),
          HomologicalComplex.extendMap_f ((F.mapHomologicalComplex (.up ℕ)).map φ)
            ComplexShape.embeddingUpNat (i := i'.toNat) (by simp [Int.toNat_of_nonneg hi'])]
        simp only [CategoryTheory.Functor.map_comp, Functor.mapHomologicalComplex_map_f, assoc,
          Iso.inv_hom_id_assoc, ← Functor.mapIso_inv, ← Functor.mapIso_hom]
      · exact (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i' fun n hn ↦
          hi' (hn ▸ Int.natCast_nonneg n))).eq_of_src _ _

@[simp]
lemma extendNatMapCochainComplexPlusIso_hom_app_f
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℕ) (n : ℕ) :
    ((F.extendNatMapCochainComplexPlusIso.hom.app K).hom).f (n : ℤ) =
      F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)).hom ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)).inv := by
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapCochainComplexPlus_obj_obj,
    Functor.mapHomologicalComplex_obj_X, CochainComplex.Plus.extendNat_obj_obj]
  simp only [extendNatMapCochainComplexPlusIso, NatIso.ofComponents_hom_app,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  unfold extendNatMapComponentIso
  simp

@[simp]
lemma extendNatMapCochainComplexPlusIso_inv_app_f
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℕ) (n : ℕ) :
    ((F.extendNatMapCochainComplexPlusIso.inv.app K).hom).f (n : ℤ) =
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)).hom ≫
        F.map (K.extendXIso ComplexShape.embeddingUpNat
          (i := n) (i' := (n : ℤ)) (by simp)).inv := by
  have h := congrArg (fun φ ↦ φ.hom.f (n : ℤ))
    (F.extendNatMapCochainComplexPlusIso.hom_inv_id_app K)
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    HomologicalComplex.comp_f, HomologicalComplex.id_f] at h
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapCochainComplexPlus_obj_obj,
    Functor.mapHomologicalComplex_obj_X, CochainComplex.Plus.extendNat_obj_obj] at h ⊢
  rw [extendNatMapCochainComplexPlusIso_hom_app_f] at h
  rw [← cancel_epi (F.map (K.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) (by simp)).hom ≫
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
      ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)).inv), h]
  simp [← CategoryTheory.Functor.map_comp]

end ExtendNat

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [Preadditive D] [HasZeroObject D]
  {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive]

/-- `Functor.extendNatMapCochainComplexPlusIso` is natural with respect to additive natural
transformations `τ : F₁ ⟶ F₂`. -/
@[reassoc]
lemma mapCochainComplexPlus_extendNat_comp_hom (τ : F₁ ⟶ F₂) (K : CochainComplex C ℕ) :
    τ.mapCochainComplexPlus.app ((CochainComplex.Plus.extendNat C).obj K) ≫
      F₂.extendNatMapCochainComplexPlusIso.hom.app K =
    F₁.extendNatMapCochainComplexPlusIso.hom.app K ≫
      (CochainComplex.Plus.extendNat D).map ((τ.mapHomologicalComplex (.up ℕ)).app K) := by
  ext i'
  by_cases hi' : 0 ≤ i'
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi'
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      HomologicalComplex.comp_f, NatTrans.mapCochainComplexPlus_app_hom,
      NatTrans.mapHomologicalComplex_app_f]
    rw [Functor.extendNatMapCochainComplexPlusIso_hom_app_f,
      Functor.extendNatMapCochainComplexPlusIso_hom_app_f,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) (by simp)]
    simp [τ.naturality_assoc]
  · exact (F₁.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i' fun n hn ↦
      hi' (hn ▸ Int.natCast_nonneg n))).eq_of_src _ _

end CategoryTheory.NatTrans

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
      distTriang (DerivedCategory.Plus C) := by
  rw [← ι.map_distinguished_iff]
  refine isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished φ.hom) _ ?_
  exact (Functor.mapTriangleCompIso Q ι).symm.app _ ≪≫
    (Functor.mapTriangleIso (QCompιIso C)).app _ ≪≫
    (Functor.mapTriangleCompIso (CochainComplex.Plus.ι C) DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (CochainComplex.Plus.mappingConeTriangleιIso φ)

/-- The connecting morphism `Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦1⟧` in `DerivedCategory.Plus C` attached to
a short exact sequence in `CochainComplex.Plus C`. -/
def triangleOfSESδ {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk
    ((QCompιIso C).hom.app S.X₃ ≫
      DerivedCategory.triangleOfSESδ hS ≫
      ((QCompιIso C).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
      (ι.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁))

@[simp]
lemma triangleOfSESδ_hom {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    (triangleOfSESδ hS).hom =
      (QCompιIso C).hom.app S.X₃ ≫
        DerivedCategory.triangleOfSESδ hS ≫
        ((QCompιIso C).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
        (ι.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁) := (rfl)

/-- The triangle in `DerivedCategory.Plus C` attached to a short exact sequence of bounded-below
cochain complexes. -/
abbrev triangleOfSES {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    Triangle (DerivedCategory.Plus C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

/-- Inclusion into `DerivedCategory C` identifies `DerivedCategory.Plus.triangleOfSES hS` with
`DerivedCategory.triangleOfSES hS`. -/
def triangleOfSESιIso {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    ι.mapTriangle.obj (triangleOfSES hS) ≅ DerivedCategory.triangleOfSES hS := by
  refine Triangle.isoMk _ _ ((QCompιIso C).app S.X₁) ((QCompιIso C).app S.X₂)
    ((QCompιIso C).app S.X₃) ?_ ?_ ?_
  · exact (QCompιIso C).hom.naturality S.f
  · exact (QCompιIso C).hom.naturality S.g
  · dsimp only [triangleOfSES, DerivedCategory.triangleOfSES]
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
