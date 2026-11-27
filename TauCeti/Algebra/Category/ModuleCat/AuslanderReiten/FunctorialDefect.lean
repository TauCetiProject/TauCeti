/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.StableEquivalence
public import TauCeti.Algebra.Module.AuslanderReiten.Defect.Formula

/-!
# Auslander's defect formula on stable categories

The covariant defect of a monomorphism descends to modules modulo injectives. The dual
contravariant defect of an epimorphism descends to modules modulo projectives. For a short
exact sequence, Auslander's defect formula identifies the two functors on finitely presented
modules after composing the covariant defect with the stable translate `D Tr`. Morphisms of
short exact sequences give commutative squares of these natural isomorphisms.

The component formula uses `Function.Exact.dualContravariantDefectEquivCovariantDefect` and
`TauCeti.stableTranslateObjIsoMatlisDualTranspose`. The defect functors expose their object
definitions so that their morphisms can be applied directly to quotient classes and linear forms.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270, Theorem and the functoriality argument on p. 269.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits LinearMap TauCeti

open scoped ModuleCat.Algebra

universe u v

namespace ModuleCat

variable (R : Type v) [CommRing R] {A : Type u} [Ring A] [Algebra R A]

section Covariant

variable {L M : ModuleCat.{max u v} A} (f : L ⟶ M)

/-- The covariant defect functor of `f` sends a module `Y` to the cokernel of
`Hom(f, Y)` and acts on morphisms by postcomposition. -/
@[expose]
def covariantDefectFunctor : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} R where
  obj Y := of R (covariantDefect R f.hom Y)
  map g := ofHom (homCokernelMap R f.hom g.hom)
  map_id _ := by simp
  map_comp g h := by simp [homCokernelMap_comp]

instance : (covariantDefectFunctor R f).Additive where
  map_add := by
    intro X Y g h
    unfold covariantDefectFunctor
    apply ModuleCat.hom_ext
    simp only [hom_add, hom_ofHom]
    ext x
    simp [LinearMap.add_comp, Submodule.Quotient.mk_add]

variable [Mono f]

/-- The covariant defect of a monomorphism vanishes on injective modules. -/
theorem isZero_covariantDefectFunctor_obj (I : ModuleCat.{max u v} A) [Injective I] :
    IsZero ((covariantDefectFunctor R f).obj I) := by
  have h : Function.Surjective (f.hom.lcomp R I) := fun x ↦
    ⟨(Injective.factorThru (ofHom x) f).hom, congrArg Hom.hom
      (Injective.comp_factorThru (ofHom x) f)⟩
  have : Subsingleton (covariantDefect R f.hom I) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr h)
  exact ModuleCat.isZero_of_subsingleton (of R (covariantDefect R f.hom I))

/-- The covariant defect of a monomorphism, acting on modules modulo maps through injectives. -/
@[expose]
def stableCovariantDefect :
    (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory ⥤
      ModuleCat.{max u v} R :=
  (ExactStructure.abelian _).injectiveStableIdeal.lift (covariantDefectFunctor R f) (by
    intro X Y g hg
    rw [ExactStructure.mem_injectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at hg
    obtain ⟨I, hI, a, b, rfl⟩ := hg
    have : Injective I := (ExactStructure.abelian_isInjective_iff I).1 hI
    have hzero := isZero_covariantDefectFunctor_obj R f I
    rw [Functor.mem_kerIdeal_hom, Functor.map_comp,
      hzero.eq_of_src ((covariantDefectFunctor R f).map b) 0, Limits.comp_zero])

/-- The stable covariant defect on the class of a module is its covariant defect. -/
@[simp]
theorem stableCovariantDefect_obj
    (Y : (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory) :
    (stableCovariantDefect R f).obj Y = of R (covariantDefect R f.hom Y.as) :=
  (rfl)

/-- The stable covariant defect acts on representatives by postcomposition. -/
@[simp]
theorem stableCovariantDefect_map {Y Y' : ModuleCat.{max u v} A} (a : Y ⟶ Y') :
    (stableCovariantDefect R f).map ((ExactStructure.abelian _).injectiveStableFunctor.map a) =
      ofHom (homCokernelMap R f.hom a.hom) :=
  (rfl)

end Covariant

section Contravariant

variable (Q : Type v) [AddCommGroup Q] [Module R Q]
variable {M N : ModuleCat.{max u v} A} (g : M ⟶ N)

/-- The dual contravariant defect functor of `g` sends a module `X` to the `Q`-valued dual of the
cokernel of `Hom(X, g)`. On morphisms it acts by the dual of precomposition. -/
@[expose]
def dualContravariantDefectFunctor : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} R where
  obj X := of R (contravariantDefect R g.hom X →ₗ[R] Q)
  map a := ofHom ((contravariantDefectComap R g.hom a.hom).lcomp R Q)
  map_id _ := by
    ext χ x
    simp [lcomp_apply']
  map_comp a b := by
    ext χ x
    simp [lcomp_apply', contravariantDefectComap_comp]

instance : (dualContravariantDefectFunctor R Q g).Additive where
  map_add := by
    intro X Y a b
    unfold dualContravariantDefectFunctor
    apply ModuleCat.hom_ext
    simp only [hom_add, hom_ofHom]
    ext χ x
    simp [lcomp_apply', LinearMap.comp_add, Submodule.Quotient.mk_add]

variable [Epi g]

/-- The dual contravariant defect of an epimorphism vanishes on projective modules. -/
theorem isZero_dualContravariantDefectFunctor_obj (P : ModuleCat.{max u v} A) [Projective P] :
    IsZero ((dualContravariantDefectFunctor R Q g).obj P) := by
  have h : Function.Surjective (g.hom.compRight R :
      (P →ₗ[A] M) →ₗ[R] (P →ₗ[A] N)) := fun x ↦
    ⟨(Projective.factorThru (ofHom x) g).hom, congrArg Hom.hom
      (Projective.factorThru_comp (ofHom x) g)⟩
  have : Subsingleton (contravariantDefect R g.hom P) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr h)
  exact ModuleCat.isZero_of_subsingleton (of R (contravariantDefect R g.hom P →ₗ[R] Q))

/-- The dual contravariant defect of an epimorphism, acting on modules modulo maps through
projectives. -/
@[expose]
def stableDualContravariantDefect :
    (ExactStructure.abelian (ModuleCat.{max u v} A)).ProjectiveStableCategory ⥤
      ModuleCat.{max u v} R :=
  (ExactStructure.abelian _).projectiveStableIdeal.lift (dualContravariantDefectFunctor R Q g) (by
    intro X Y a ha
    rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at ha
    obtain ⟨P, hP, b, c, rfl⟩ := ha
    have : Projective P := (ExactStructure.abelian_isProjective_iff P).1 hP
    have hzero := isZero_dualContravariantDefectFunctor_obj R Q g P
    rw [Functor.mem_kerIdeal_hom, Functor.map_comp,
      hzero.eq_of_tgt ((dualContravariantDefectFunctor R Q g).map b) 0, Limits.zero_comp])

/-- The stable dual contravariant defect on the class of a module is its dual contravariant
defect. -/
@[simp]
theorem stableDualContravariantDefect_obj
    (X : (ExactStructure.abelian (ModuleCat.{max u v} A)).ProjectiveStableCategory) :
    (stableDualContravariantDefect R Q g).obj X =
      of R (contravariantDefect R g.hom X.as →ₗ[R] Q) :=
  (rfl)

/-- The stable dual contravariant defect acts on representatives by the dual of precomposition. -/
@[simp]
theorem stableDualContravariantDefect_map {X X' : ModuleCat.{max u v} A} (a : X ⟶ X') :
    (stableDualContravariantDefect R Q g).map
        ((ExactStructure.abelian _).projectiveStableFunctor.map a) =
      ofHom ((contravariantDefectComap R g.hom a.hom).lcomp R Q) :=
  (rfl)

end Contravariant

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

open ModuleCat

variable {R : Type v} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {Q : Type v} [AddCommGroup Q] [Module R Q] [Module.Injective R Q]
  {S : ShortComplex (ModuleCat.{max u v} A)} (hS : S.ShortExact)

-- The target is the bundled translate. The formula for linear maps uses the native base
-- action of the dual of the transpose, so transport via the underlying `A`-linear equivalence.
/-- Auslander's defect formula for a specified finite projective presentation, with the
covariant defect evaluated at the bundled translate `D Tr X`. -/
def defectFormulaEquiv {X : ModuleCat.{max u v} A} (P : FiniteProjectivePresentation X) :
    (contravariantDefect R S.g.hom X →ₗ[R] Q) ≃ₗ[R]
      covariantDefect R S.f.hom (matlisDualTranspose R Q P) :=
  Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
      ((moduleCat_exact_iff_function_exact S).1 hS.exact) ≪≫ₗ
    LinearEquiv.ofLinearMap
      (homCokernelMap R S.f.hom (matlisDualTransposeEquiv R Q P).toLinearMap)
      (homCokernelMap R S.f.hom (matlisDualTransposeEquiv R Q P).symm.toLinearMap)
      (by rw [← homCokernelMap_comp, LinearEquiv.comp_symm, homCokernelMap_id])
      (by rw [← homCokernelMap_comp, LinearEquiv.symm_comp, homCokernelMap_id])

/-- On linear forms, the bundled defect formula is the linear-map formula followed by the
change of target to the bundled `D Tr X`. -/
theorem defectFormulaEquiv_apply {X : ModuleCat.{max u v} A} (P : FiniteProjectivePresentation X)
    (χ : contravariantDefect R S.g.hom X →ₗ[R] Q) :
    hS.defectFormulaEquiv P χ =
      homCokernelMap R S.f.hom (matlisDualTransposeEquiv R Q P).toLinearMap
        (Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
          hS.moduleCat_injective_f hS.moduleCat_surjective_g
          ((moduleCat_exact_iff_function_exact S).1 hS.exact) χ) :=
  (rfl)

private theorem defectFormulaEquiv_naturality {X Y : ModuleCat.{max u v} A}
    (P : FiniteProjectivePresentation X) (P' : FiniteProjectivePresentation Y) (a : X ⟶ Y)
    {a₀ : P.P₀ →ₗ[A] P'.P₀} {a₁ : P.P₁ →ₗ[A] P'.P₁}
    (h₀ : P'.π ∘ₗ a₀ = a.hom ∘ₗ P.π) (h₁ : a₀ ∘ₗ P.p = P'.p ∘ₗ a₁)
    (χ : contravariantDefect R S.g.hom X →ₗ[R] Q) :
    hS.defectFormulaEquiv P' (χ ∘ₗ contravariantDefectComap R S.g.hom a.hom) =
      homCokernelMap R S.f.hom (matlisDualTransposeMap R Q P P' h₁).hom
        (hS.defectFormulaEquiv P χ) := by
  simp only [defectFormulaEquiv_apply,
    Function.Exact.dualContravariantDefectEquivCovariantDefect_comap P.exact P.surjective
      P'.exact P'.surjective _ _ _ h₀ h₁,
    matlisDualTransposeMap_eq, hom_ofHom, ← LinearMap.comp_apply, ← homCokernelMap_comp,
    LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id]

/-- The component of the stable defect formula is the presentation formula, transported
along the canonical comparison between the stable translate and `D Tr X`. -/
def stableDefectFormulaApp (X : FinitelyPresentedStableModule.{u, max u v} A) :
    letI := hS.epi_g
    letI := hS.mono_f
    ((ObjectProperty.ι _ ⋙ stableDualContravariantDefect R Q S.g).obj X) ≅
      ((stableTranslate R A Q ⋙ stableCovariantDefect R S.f).obj X) :=
  letI := hS.epi_g
  letI := hS.mono_f
  (hS.defectFormulaEquiv (FinitelyPresentedStableModule.presentation X)).toModuleIso ≪≫
    (stableCovariantDefect R S.f).mapIso (stableTranslateObjIsoMatlisDualTranspose X).symm

/-- The forward map of the stable defect formula at a module. -/
theorem stableDefectFormulaApp_hom (X : FinitelyPresentedStableModule.{u, max u v} A) :
    letI := hS.mono_f
    (hS.stableDefectFormulaApp (R := R) (Q := Q) X).hom =
      (hS.defectFormulaEquiv (FinitelyPresentedStableModule.presentation X)).toModuleIso.hom ≫
        (stableCovariantDefect R S.f).map
          (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X).inv :=
  (rfl)

/-- **Auslander's defect formula on the stable category.** For a short exact sequence
`δ : 0 → L → M → N → 0`, the dual of its contravariant defect on finitely presented
modules modulo projectives is naturally isomorphic to its covariant defect applied to the
stable translate `D Tr`. -/
def stableDefectFormula :
    letI := hS.epi_g
    letI := hS.mono_f
    ObjectProperty.ι _ ⋙ stableDualContravariantDefect R Q S.g ≅
      stableTranslate R A Q ⋙ stableCovariantDefect R S.f := by
  letI := hS.epi_g
  letI := hS.mono_f
  refine NatIso.ofComponents (hS.stableDefectFormulaApp (R := R) (Q := Q)) ?_
  intro X Y t
  obtain ⟨a, ha⟩ := (ExactStructure.abelian (ModuleCat.{max u v} A)).projectiveStableFunctor
    |>.map_surjective t.hom
  have ht : ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map a) = t :=
    ObjectProperty.hom_ext _ ha
  subst t
  let P := FinitelyPresentedStableModule.presentation X
  let P' := FinitelyPresentedStableModule.presentation Y
  obtain ⟨a₀, a₁, h₀, h₁⟩ :=
    exists_lift_projective_presentation P.exact.linearMap_comp_eq_zero P'.exact P'.surjective a.hom
  have h := congrArg (stableCovariantDefect R S.f).map
    (stableTranslateObjIsoMatlisDualTranspose_naturality (R := R) (E := Q) a h₀ h₁)
  simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom]
  rw [stableDefectFormulaApp_hom, stableDefectFormulaApp_hom]
  -- Postcompose with the comparison isomorphism to read the square on module representatives.
  apply (cancel_mono ((stableCovariantDefect R S.f).map
    (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) Y).hom)).1
  simp only [Functor.map_comp] at h
  -- The stable defect objects reduce to the same module on representatives at default
  -- transparency. Use `erw` to match associativity through those object definitions.
  erw [Category.assoc, Category.assoc, Category.assoc, h,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
    stableDualContravariantDefect_map, stableCovariantDefect_map]
  ext χ
  exact hS.defectFormulaEquiv_naturality P P' a h₀ h₁ χ

/-- The component of the natural isomorphism is the bundled defect formula at the chosen
presentation, composed with the inverse comparison to the stable translate. -/
@[simp]
theorem stableDefectFormula_app (X : FinitelyPresentedStableModule.{u, max u v} A) :
    (hS.stableDefectFormula (R := R) (Q := Q)).app X =
      hS.stableDefectFormulaApp X := by
  rw [stableDefectFormula, NatIso.ofComponents.app]

section SequenceNaturality

variable {S' : ShortComplex (ModuleCat.{max u v} A)} (hS' : S'.ShortExact)

include hS hS' in
/-- A morphism of short exact sequences acts contravariantly on the stable covariant defects,
by precomposition with its first component. -/
def stableCovariantDefectNatTrans (b : S ⟶ S') :
    letI := hS.mono_f
    letI := hS'.mono_f
    stableCovariantDefect R S'.f ⟶ stableCovariantDefect R S.f := by
  letI := hS.mono_f
  letI := hS'.mono_f
  refine ⟨fun Y ↦ ofHom (covariantDefectMap R (congrArg Hom.hom b.comm₁₂.symm) Y.as), ?_⟩
  intro Y Y' a
  obtain ⟨a₀, rfl⟩ := (ExactStructure.abelian _).injectiveStableFunctor.map_surjective a
  rw [stableCovariantDefect_map, stableCovariantDefect_map]
  apply ModuleCat.hom_ext
  -- Expose the cokernel carriers for quotient extensionality after passing to linear maps.
  change covariantDefectMap R (congrArg Hom.hom b.comm₁₂.symm) _ ∘ₗ
      homCokernelMap R S'.f.hom a₀.hom =
    homCokernelMap R S.f.hom a₀.hom ∘ₗ covariantDefectMap R (congrArg Hom.hom b.comm₁₂.symm) _
  ext x
  simp [LinearMap.comp_assoc]

omit [Module.Injective R Q] in
include hS hS' in
/-- A morphism of short exact sequences acts contravariantly on the dual contravariant defects,
by dualizing postcomposition with its last component. -/
def stableDualContravariantDefectNatTrans (b : S ⟶ S') :
    letI := hS.epi_g
    letI := hS'.epi_g
    stableDualContravariantDefect R Q S'.g ⟶ stableDualContravariantDefect R Q S.g := by
  letI := hS.epi_g
  letI := hS'.epi_g
  refine ⟨fun X ↦ ofHom (lcomp R Q
    (contravariantDefectMap R (congrArg Hom.hom b.comm₂₃.symm) X.as)), ?_⟩
  intro X X' a
  obtain ⟨a₀, rfl⟩ := (ExactStructure.abelian _).projectiveStableFunctor.map_surjective a
  rw [stableDualContravariantDefect_map, stableDualContravariantDefect_map]
  apply ModuleCat.hom_ext
  -- Read the composites on the duals of the defining cokernels for quotient extensionality.
  change lcomp R Q (contravariantDefectMap R (congrArg Hom.hom b.comm₂₃.symm) X'.as) ∘ₗ
      lcomp R Q (contravariantDefectComap R S'.g.hom a₀.hom) =
    lcomp R Q (contravariantDefectComap R S.g.hom a₀.hom) ∘ₗ
      lcomp R Q (contravariantDefectMap R (congrArg Hom.hom b.comm₂₃.symm) X.as)
  ext χ x
  simp [lcomp_apply', LinearMap.comp_assoc]

variable (b : S ⟶ S')

omit [Module.Injective R Q] in
/-- The map of dual contravariant defects evaluates a functional on the defect map induced by
the last component of the morphism of short exact sequences. -/
@[simp]
theorem stableDualContravariantDefectNatTrans_app
    (X : (ExactStructure.abelian (ModuleCat.{max u v} A)).ProjectiveStableCategory) :
    (hS.stableDualContravariantDefectNatTrans (R := R) (Q := Q) hS' b).app X =
      ofHom ((contravariantDefectMap R (congrArg Hom.hom b.comm₂₃.symm) X.as).lcomp R Q) :=
  (rfl)

/-- The map of covariant defects on an object is precomposition with the first component
of the morphism of short exact sequences. -/
@[simp]
theorem stableCovariantDefectNatTrans_app
    (Y : (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory) :
    (hS.stableCovariantDefectNatTrans (R := R) hS' b).app Y =
      ofHom (covariantDefectMap R (congrArg Hom.hom b.comm₁₂.symm) Y.as) :=
  (rfl)

include hS hS' in
private theorem defectFormulaEquiv_naturality_sequence {X : ModuleCat.{max u v} A}
    (P : FiniteProjectivePresentation X) (χ : contravariantDefect R S'.g.hom X →ₗ[R] Q) :
    hS.defectFormulaEquiv P
        (χ ∘ₗ contravariantDefectMap R (congrArg Hom.hom b.comm₂₃.symm) X) =
      covariantDefectMap R (congrArg Hom.hom b.comm₁₂.symm) _
        (hS'.defectFormulaEquiv P χ) := by
  rw [defectFormulaEquiv_apply, defectFormulaEquiv_apply,
    Function.Exact.dualContravariantDefectEquivCovariantDefect_naturality P.exact P.surjective
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
      ((moduleCat_exact_iff_function_exact S).1 hS.exact)
      hS'.moduleCat_injective_f hS'.moduleCat_surjective_g
      ((moduleCat_exact_iff_function_exact S').1 hS'.exact)
      (congrArg Hom.hom b.comm₁₂.symm) (congrArg Hom.hom b.comm₂₃.symm)]
  generalize Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
    hS'.moduleCat_injective_f hS'.moduleCat_surjective_g
    ((moduleCat_exact_iff_function_exact S').1 hS'.exact) χ = y
  induction y using Submodule.Quotient.induction_on with
  | _ y => simp [LinearMap.comp_assoc]

/-- The stable defect formula commutes with the maps of defects induced by a morphism of short
exact sequences, with the covariant defect evaluated after the stable translate. -/
theorem stableDefectFormula_naturality :
    (Functor.whiskerLeft (ObjectProperty.ι _)
        (hS.stableDualContravariantDefectNatTrans (R := R) (Q := Q) hS' b)) ≫
      (hS.stableDefectFormula (R := R) (Q := Q)).hom =
    (hS'.stableDefectFormula (R := R) (Q := Q)).hom ≫
      Functor.whiskerLeft (stableTranslate R A Q)
        (hS.stableCovariantDefectNatTrans (R := R) hS' b) := by
  apply NatTrans.ext
  funext X
  let _ := hS.mono_f
  let e := stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X
  let F := stableCovariantDefect R S.f
  let η := hS.stableCovariantDefectNatTrans (R := R) hS' b
  have h := η.naturality e.hom
  -- Postcompose with the comparison at the common stable translate and use naturality of η.
  apply (cancel_mono (F.map e.hom)).1
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, ← Iso.app_hom, stableDefectFormula_app,
    stableDefectFormulaApp_hom]
  erw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    Category.comp_id]
  erw [Category.assoc, Category.assoc, ← h, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  rw [stableDualContravariantDefectNatTrans_app, stableCovariantDefectNatTrans_app]
  ext χ
  exact hS.defectFormulaEquiv_naturality_sequence hS' b _ χ

end SequenceNaturality

end CategoryTheory.ShortComplex.ShortExact
