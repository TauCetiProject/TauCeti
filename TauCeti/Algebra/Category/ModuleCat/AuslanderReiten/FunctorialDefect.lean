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
`TauCeti.stableTranslateObjIsoMatlisDualTranspose`. The map formulas use the object equalities
to identify the sources and targets with the corresponding cokernels and duals.

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
def covariantDefectFunctor : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} R where
  obj Y := of R (covariantDefect R f.hom Y)
  map g := ofHom (homCokernelMap R f.hom g.hom)
  map_id _ := by simp
  map_comp g h := by simp [homCokernelMap_comp]

/-- The object of the covariant defect functor is the cokernel of precomposition with `f`. -/
@[simp]
theorem covariantDefectFunctor_obj (Y : ModuleCat.{max u v} A) :
    (covariantDefectFunctor R f).obj Y = of R (covariantDefect R f.hom Y) :=
  (rfl)

/-- The covariant defect functor acts by postcomposition on cokernels. -/
@[simp]
theorem covariantDefectFunctor_map {Y Y' : ModuleCat.{max u v} A} (a : Y ⟶ Y') :
    (covariantDefectFunctor R f).map a =
      eqToHom (covariantDefectFunctor_obj R f Y) ≫ ofHom (homCokernelMap R f.hom a.hom) ≫
        eqToHom (covariantDefectFunctor_obj R f Y').symm :=
  (rfl)

/-- On a quotient class, the covariant defect functor postcomposes its representative. -/
theorem covariantDefectFunctor_map_mk {Y Y' : ModuleCat.{max u v} A} (a : Y ⟶ Y')
    (x : L →ₗ[A] Y) :
    (eqToHom (covariantDefectFunctor_obj R f Y).symm ≫ (covariantDefectFunctor R f).map a ≫
      eqToHom (covariantDefectFunctor_obj R f Y')).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (a.hom ∘ₗ x) := by
  exact homCokernelMap_mk f.hom a.hom x

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
      eqToHom (stableCovariantDefect_obj R f _) ≫ ofHom (homCokernelMap R f.hom a.hom) ≫
        eqToHom (stableCovariantDefect_obj R f _).symm :=
  (rfl)

end Covariant

section Contravariant

variable (Q : Type v) [AddCommGroup Q] [Module R Q]
variable {M N : ModuleCat.{max u v} A} (g : M ⟶ N)

/-- The dual contravariant defect functor of `g` sends a module `X` to the `Q`-valued dual of the
cokernel of `Hom(X, g)`. On morphisms it acts by the dual of precomposition. -/
def dualContravariantDefectFunctor : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} R where
  obj X := of R (contravariantDefect R g.hom X →ₗ[R] Q)
  map a := ofHom ((contravariantDefectComap R g.hom a.hom).lcomp R Q)
  map_id _ := by
    ext χ x
    simp [lcomp_apply']
  map_comp a b := by
    ext χ x
    simp [lcomp_apply', contravariantDefectComap_comp]

/-- The object of the dual contravariant defect functor is the dual of the defining cokernel. -/
@[simp]
theorem dualContravariantDefectFunctor_obj (X : ModuleCat.{max u v} A) :
    (dualContravariantDefectFunctor R Q g).obj X =
      of R (contravariantDefect R g.hom X →ₗ[R] Q) :=
  (rfl)

/-- The dual contravariant defect functor acts by dualizing precomposition. -/
@[simp]
theorem dualContravariantDefectFunctor_map {X X' : ModuleCat.{max u v} A} (a : X ⟶ X') :
    (dualContravariantDefectFunctor R Q g).map a =
      eqToHom (dualContravariantDefectFunctor_obj R Q g X) ≫
        ofHom ((contravariantDefectComap R g.hom a.hom).lcomp R Q) ≫
          eqToHom (dualContravariantDefectFunctor_obj R Q g X').symm :=
  (rfl)

/-- On a linear form, the dual contravariant defect functor composes with the defect comap. -/
@[simp↓]
theorem dualContravariantDefectFunctor_map_apply {X X' : ModuleCat.{max u v} A} (a : X ⟶ X')
    (χ : contravariantDefect R g.hom X →ₗ[R] Q) :
    (eqToHom (dualContravariantDefectFunctor_obj R Q g X).symm ≫
      (dualContravariantDefectFunctor R Q g).map a ≫
        eqToHom (dualContravariantDefectFunctor_obj R Q g X')).hom χ =
      χ ∘ₗ contravariantDefectComap R g.hom a.hom :=
  (rfl)

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
      eqToHom (stableDualContravariantDefect_obj R Q g _) ≫
        ofHom ((contravariantDefectComap R g.hom a.hom).lcomp R Q) ≫
          eqToHom (stableDualContravariantDefect_obj R Q g _).symm :=
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

/-- The presentation defect formula commutes with a module morphism lifted to the chosen
finite projective presentations. -/
theorem defectFormulaEquiv_naturality {X Y : ModuleCat.{max u v} A}
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
private def stableDefectFormulaApp (X : FinitelyPresentedStableModule.{u, max u v} A) :
    letI := hS.epi_g
    letI := hS.mono_f
    ((ObjectProperty.ι _ ⋙ stableDualContravariantDefect R Q S.g).obj X) ≅
      ((stableTranslate R A Q ⋙ stableCovariantDefect R S.f).obj X) :=
  letI := hS.epi_g
  letI := hS.mono_f
  (hS.defectFormulaEquiv (FinitelyPresentedStableModule.presentation X)).toModuleIso ≪≫
    (stableCovariantDefect R S.f).mapIso (stableTranslateObjIsoMatlisDualTranspose X).symm

@[reassoc]
private theorem stableDefectFormulaApp_hom_comp (X : FinitelyPresentedStableModule.{u, max u v} A) :
    letI := hS.mono_f
    (hS.stableDefectFormulaApp (R := R) (Q := Q) X).hom ≫
        (stableCovariantDefect R S.f).map
          (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X).hom =
      (hS.defectFormulaEquiv (FinitelyPresentedStableModule.presentation X)).toModuleIso.hom := by
  let _ := hS.mono_f
  let F := stableCovariantDefect R S.f
  let e := F.mapIso (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X)
  let P := FinitelyPresentedStableModule.presentation X
  let p : of R (contravariantDefect R S.g.hom X.obj.as →ₗ[R] Q) ⟶
      F.obj ((ExactStructure.abelian _).injectiveStableFunctor.obj (matlisDualTranspose R Q P)) :=
    (hS.defectFormulaEquiv P).toModuleIso.hom
  have h : (p ≫ e.inv) ≫ e.hom = p := by
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact h

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
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at *
  simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom]
  -- Postcompose with the comparison isomorphism to read the square on module representatives.
  apply (cancel_mono ((stableCovariantDefect R S.f).map
    (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) Y).hom)).1
  simp only [Functor.map_comp] at h
  simp only [Category.assoc, h, stableDefectFormulaApp_hom_comp,
    stableDefectFormulaApp_hom_comp_assoc, stableDualContravariantDefect_map,
    stableCovariantDefect_map]
  ext χ
  exact hS.defectFormulaEquiv_naturality P P' a h₀ h₁ χ

private theorem stableDefectFormula_hom_app_eq (X : FinitelyPresentedStableModule.{u, max u v} A) :
    (hS.stableDefectFormula (R := R) (Q := Q)).hom.app X = (hS.stableDefectFormulaApp X).hom :=
  (rfl)

/-- The forward component is the presentation defect formula composed with the inverse of
the comparison between the stable translate and the chosen `D Tr X`. -/
@[simp]
theorem stableDefectFormula_hom_app (X : FinitelyPresentedStableModule.{u, max u v} A) :
    letI := hS.epi_g
    letI := hS.mono_f
    (hS.stableDefectFormula (R := R) (Q := Q)).hom.app X =
      eqToHom (stableDualContravariantDefect_obj R Q S.g X.obj) ≫
        (hS.defectFormulaEquiv (FinitelyPresentedStableModule.presentation X)).toModuleIso.hom ≫
          eqToHom (stableCovariantDefect_obj R S.f _).symm ≫
            (stableCovariantDefect R S.f).map
              (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X).inv :=
  (rfl)

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
      letI := hS.epi_g
      letI := hS'.epi_g
      eqToHom (stableDualContravariantDefect_obj R Q S'.g X) ≫
        ofHom ((contravariantDefectMap R (congrArg Hom.hom b.comm₂₃.symm) X.as).lcomp R Q) ≫
          eqToHom (stableDualContravariantDefect_obj R Q S.g X).symm :=
  (rfl)

/-- The map of covariant defects on an object is precomposition with the first component
of the morphism of short exact sequences. -/
@[simp]
theorem stableCovariantDefectNatTrans_app
    (Y : (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory) :
    (hS.stableCovariantDefectNatTrans (R := R) hS' b).app Y =
      letI := hS.mono_f
      letI := hS'.mono_f
      eqToHom (stableCovariantDefect_obj R S'.f Y) ≫
        ofHom (covariantDefectMap R (congrArg Hom.hom b.comm₁₂.symm) Y.as) ≫
          eqToHom (stableCovariantDefect_obj R S.f Y).symm :=
  (rfl)

include hS hS' in
/-- The presentation defect formula commutes with the maps of defects induced by a morphism
of short exact sequences. -/
theorem defectFormulaEquiv_naturality_sequence {X : ModuleCat.{max u v} A}
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
  have h := (hS.stableCovariantDefectNatTrans (R := R) hS' b).naturality
    (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X).hom
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at *
  -- Postcompose with the comparison at the common stable translate and use naturality of η.
  apply (cancel_mono ((stableCovariantDefect R S.f).map
    (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := Q) X).hom)).1
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, stableDefectFormula_hom_app_eq,
    Category.assoc, ← h, stableDefectFormulaApp_hom_comp, stableDefectFormulaApp_hom_comp_assoc]
  simp only [stableDualContravariantDefectNatTrans_app, stableCovariantDefectNatTrans_app]
  ext χ
  exact hS.defectFormulaEquiv_naturality_sequence hS' b _ χ

end SequenceNaturality

end CategoryTheory.ShortComplex.ShortExact
