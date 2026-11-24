/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Complex-level infrastructure for bounded-below cochain complexes

Mathlib defines the full subcategory `CochainComplex.Plus C` of bounded-below `ℤ`-indexed cochain
complexes. This file supplies complex-level lifts and functoriality compatibilities on
`CochainComplex.Plus C` without requiring derived-category or localization imports:

* single-complex and nonnegative-extension functors into `CochainComplex.Plus C`
  (`CochainComplex.Plus.singleFunctor`, `CochainComplex.Plus.extendNat`,
  `CochainComplex.Plus.extendNatSingle₀Iso`, `CochainComplex.Plus.extendNatHomologyIso`);
* canonical downward truncation (`CochainComplex.Plus.truncLE`) and downward stupid truncation
  (`CochainComplex.Plus.stupidTruncLE`) within `CochainComplex.Plus C`, with functoriality laws for
  their lifted maps (`CochainComplex.Plus.truncLEMap`, `CochainComplex.Plus.stupidTruncLEMap`);
* mapping cones in `CochainComplex.Plus C` (`CochainComplex.Plus.mappingCone`,
  `CochainComplex.Plus.mappingConeTriangle`);
* compatibility of `CochainComplex.Plus.extendNat` with degreewise functor application and
  cohomology (`CategoryTheory.Functor.extendNatMapCochainComplexPlusIso`,
  `CategoryTheory.Functor.extendNatMapCochainComplexPlusHomologyIso`), natural in complex morphisms
  and additive natural transformations.

## References

* The Stacks Project, Derived Categories, Section 13.11 (tag 05RU) and Section 13.12 (tag 05S7).
-/

public section

noncomputable section

open CategoryTheory Category Functor Limits Pretriangulated HomologicalComplex

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
    (ofIsStrictlyGE K b).obj.IsStrictlyGE b :=
  inferInstanceAs (K.IsStrictlyGE b)

section HasZeroObject

variable [HasZeroObject C]

variable (C) in
/-- Extending a nonnegative cochain complex by zeros in negative degrees lands in
`CochainComplex.Plus C`. -/
abbrev extendNat : CochainComplex C ℕ ⥤ CochainComplex.Plus C where
  obj K := ⟨K.extend ComplexShape.embeddingUpNat,
    (CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩
  map φ := ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  map_id K := by ext : 1; exact HomologicalComplex.extendMap_id K ComplexShape.embeddingUpNat
  map_comp f g := by
    ext : 1; exact HomologicalComplex.extendMap_comp f g ComplexShape.embeddingUpNat

@[simp]
lemma extendNat_obj_obj (K : CochainComplex C ℕ) :
    ((extendNat C).obj K).obj = K.extend ComplexShape.embeddingUpNat := (rfl)

@[simp]
lemma extendNat_map_hom {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    ((extendNat C).map φ).hom = HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat := (rfl)

variable (C) in
/-- Forgetting the lower bound after `extendNat` recovers extension along `ℕ ↪ ℤ`. -/
def extendNatCompιIso : extendNat C ⋙ ι C ≅ ComplexShape.embeddingUpNat.extendFunctor C :=
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
    let ⟨b, _⟩ := K.property; ⟨b, inferInstance⟩⟩

instance (K : CochainComplex.Plus C) (n b : ℤ) [K.obj.IsStrictlyGE b] :
    (K.stupidTruncLE n).obj.IsStrictlyGE b := by dsimp [stupidTruncLE]; infer_instance

instance (K : CochainComplex.Plus C) (n : ℤ) : (K.stupidTruncLE n).obj.IsStrictlyLE n := by
  dsimp [stupidTruncLE]; infer_instance

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

@[simp]
lemma stupidTruncLEMap_id (K : CochainComplex.Plus C) (n : ℤ) :
    stupidTruncLEMap (𝟙 K) n = 𝟙 (K.stupidTruncLE n) := by
  ext : 1; exact HomologicalComplex.stupidTruncMap_id K.obj (ComplexShape.embeddingUpIntLE n)

@[simp, reassoc]
lemma stupidTruncLEMap_comp {K L M : CochainComplex.Plus C} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) :
    stupidTruncLEMap (φ ≫ ψ) n = stupidTruncLEMap φ n ≫ stupidTruncLEMap ψ n := by
  ext : 1
  exact HomologicalComplex.stupidTruncMap_comp φ.hom ψ.hom (ComplexShape.embeddingUpIntLE n)

@[reassoc (attr := simp)]
lemma πStupidTruncLE_naturality {K L : CochainComplex.Plus C} (φ : K ⟶ L) (n : ℤ) :
    K.πStupidTruncLE n ≫ stupidTruncLEMap φ n = φ ≫ L.πStupidTruncLE n := by
  ext : 1; exact HomologicalComplex.πStupidTrunc_naturality φ.hom (ComplexShape.embeddingUpIntLE n)

section Trunc

variable (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]

/-- Canonical truncation `τ_{≤ n}` preserves `CochainComplex.Plus C`. -/
abbrev truncLE (n : ℤ) : CochainComplex.Plus C :=
  ⟨K.obj.truncLE n, let ⟨b, _⟩ := K.property; ⟨b, inferInstance⟩⟩

instance (n b : ℤ) [K.obj.IsStrictlyGE b] : (K.truncLE n).obj.IsStrictlyGE b := by
  dsimp [truncLE]; infer_instance

instance (n : ℤ) : (K.truncLE n).obj.IsLE n := by dsimp [truncLE]; infer_instance

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

variable (K) in
@[simp]
lemma truncLEMap_id (n : ℤ) : truncLEMap (𝟙 K) n = 𝟙 (K.truncLE n) := by
  ext : 1; exact HomologicalComplex.truncLEMap_id K.obj (ComplexShape.embeddingUpIntLE n)

@[simp, reassoc]
lemma truncLEMap_comp {M : CochainComplex.Plus C} [∀ i, M.obj.HasHomology i]
    (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) :
    truncLEMap (φ ≫ ψ) n = truncLEMap φ n ≫ truncLEMap ψ n := by
  ext : 1; exact HomologicalComplex.truncLEMap_comp φ.hom ψ.hom (ComplexShape.embeddingUpIntLE n)

@[reassoc (attr := simp)]
lemma ιTruncLE_naturality (φ : K ⟶ L) (n : ℤ) :
    truncLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ := by
  ext : 1; exact CochainComplex.ιTruncLE_naturality φ.hom n

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
    (K.πStupidTruncLE n) (by ext : 1; exact Limits.kernel.condition _)

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
def singleFunctorCompιIso (n : ℤ) : singleFunctor C n ⋙ ι C ≅ CochainComplex.singleFunctor C n :=
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
def extendNatSingle₀Iso : CochainComplex.single₀ C ⋙ extendNat C ≅ singleFunctor C 0 :=
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
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 (by simp)).hom := (rfl)

@[simp]
lemma extendNatSingle₀Iso_inv_app_hom (X : C) :
    ((extendNatSingle₀Iso C).inv.app X).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 (by simp)).inv := (rfl)

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
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (Limits.kernelIsKernel π₀))
    (inferInstanceAs (Mono (Limits.kernel.ι π₀))) (inferInstanceAs (Epi π₀))

end Abelian

section MappingCone

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The mapping cone of a morphism in `CochainComplex.Plus C`, lifted to `CochainComplex.Plus C`. -/
abbrev mappingCone {K L : CochainComplex.Plus C} (φ : K ⟶ L) : CochainComplex.Plus C :=
  ⟨CochainComplex.mappingCone φ.hom, by
    obtain ⟨a, _⟩ := K.property; obtain ⟨b, _⟩ := L.property
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
    (ι C).mapTriangle.obj (mappingConeTriangle φ) ≅ CochainComplex.mappingCone.triangle φ.hom :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simp [CochainComplex.mappingCone.triangle])
    (by dsimp [mappingConeTriangle, CochainComplex.mappingCone.triangle, ι]; simp)

end MappingCone

end CochainComplex.Plus

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
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat
          (i := n) (i' := (n : ℤ)) (by simp)).inv := by
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapCochainComplexPlus_obj_obj,
    Functor.mapHomologicalComplex_obj_X, CochainComplex.Plus.extendNat_obj_obj]
  simp only [extendNatMapCochainComplexPlusIso, NatIso.ofComponents_hom_app,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  unfold extendNatMapComponentIso; simp

@[simp]
lemma extendNatMapCochainComplexPlusIso_inv_app_f
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℕ) (n : ℕ) :
    ((F.extendNatMapCochainComplexPlusIso.inv.app K).hom).f (n : ℤ) =
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat
          (i := n) (i' := (n : ℤ)) (by simp)).hom ≫
        F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := n) (by simp)).inv := by
  have h := congrArg (fun φ ↦ φ.hom.f (n : ℤ))
    (F.extendNatMapCochainComplexPlusIso.hom_inv_id_app K)
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    HomologicalComplex.comp_f, HomologicalComplex.id_f] at h
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapCochainComplexPlus_obj_obj,
    Functor.mapHomologicalComplex_obj_X, CochainComplex.Plus.extendNat_obj_obj] at h ⊢
  rw [extendNatMapCochainComplexPlusIso_hom_app_f] at h
  rw [← cancel_epi (F.map (K.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) (by simp)).hom ≫
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) (by simp)).inv), h]
  simp [← CategoryTheory.Functor.map_comp]

/-- Extending a nonnegative complex to `CochainComplex.Plus C`, applying `F.mapCochainComplexPlus`,
and taking `(n : ℤ)`-th cohomology is naturally isomorphic to applying `F` on `CochainComplex C ℕ`
and taking `n`-th cohomology. -/
def extendNatMapCochainComplexPlusHomologyIso [CategoryWithHomology D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    CochainComplex.Plus.extendNat C ⋙ F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ) ≅
      F.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.homologyFunctor D (.up ℕ) n :=
  NatIso.ofComponents
    (fun K ↦ (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
        ((CochainComplex.Plus.ι D).mapIso (F.extendNatMapCochainComplexPlusIso.app K)) ≪≫
      (CochainComplex.Plus.extendNatHomologyIso D n).app ((F.mapHomologicalComplex (.up ℕ)).obj K))
    fun φ ↦ by
      have hExt := congrArg (fun g ↦ (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).map
        ((CochainComplex.Plus.ι D).map g)) (F.extendNatMapCochainComplexPlusIso.hom.naturality φ)
      have hHom := (CochainComplex.Plus.extendNatHomologyIso D n).hom.naturality
        ((F.mapHomologicalComplex (.up ℕ)).map φ)
      dsimp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
        Iso.app_hom] at hExt hHom ⊢
      simp only [CategoryTheory.Functor.map_comp] at hExt
      rw [reassoc_of% hExt, hHom, assoc]

/-- Naturality of `Functor.extendNatMapCochainComplexPlusHomologyIso` in morphisms of `ℕ`-indexed
cochain complexes. -/
@[reassoc]
lemma extendNatMapCochainComplexPlusHomologyIso_hom_naturality [CategoryWithHomology D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).map ((CochainComplex.Plus.ι D).map
        (F.mapCochainComplexPlus.map ((CochainComplex.Plus.extendNat C).map φ))) ≫
      (F.extendNatMapCochainComplexPlusHomologyIso n).hom.app L =
    (F.extendNatMapCochainComplexPlusHomologyIso n).hom.app K ≫
      (HomologicalComplex.homologyFunctor D (.up ℕ) n).map
        ((F.mapHomologicalComplex (.up ℕ)).map φ) :=
  (F.extendNatMapCochainComplexPlusHomologyIso n).hom.naturality φ

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

/-- `Functor.extendNatMapCochainComplexPlusHomologyIso` is natural with respect to additive natural
transformations `τ : F₁ ⟶ F₂`. -/
@[reassoc]
lemma extendNatMapCochainComplexPlusHomologyIso_hom_naturality [CategoryWithHomology D]
    (τ : F₁ ⟶ F₂) (n : ℕ) (K : CochainComplex C ℕ) :
    (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).map ((CochainComplex.Plus.ι D).map
        (τ.mapCochainComplexPlus.app ((CochainComplex.Plus.extendNat C).obj K))) ≫
      (F₂.extendNatMapCochainComplexPlusHomologyIso n).hom.app K =
    (F₁.extendNatMapCochainComplexPlusHomologyIso n).hom.app K ≫
      (HomologicalComplex.homologyFunctor D (.up ℕ) n).map
        ((τ.mapHomologicalComplex (.up ℕ)).app K) := by
  have hExt := congrArg (fun g ↦ (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).map
    ((CochainComplex.Plus.ι D).map g)) (τ.mapCochainComplexPlus_extendNat_comp_hom K)
  have hHom := (CochainComplex.Plus.extendNatHomologyIso D n).hom.naturality
    ((τ.mapHomologicalComplex (.up ℕ)).app K)
  simp only [CategoryTheory.Functor.map_comp] at hExt
  dsimp only [Functor.extendNatMapCochainComplexPlusHomologyIso, NatIso.ofComponents_hom_app,
    Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] at hExt hHom ⊢
  rw [reassoc_of% hExt, hHom, assoc]

end CategoryTheory.NatTrans
