/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Stable.Basic
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.FiniteLength
public import TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.FinitelyPresented
public import TauCeti.Algebra.Category.ModuleCat.InjectiveStable.FinitelyGenerated
public import TauCeti.Algebra.Module.Projective.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective
import TauCeti.CategoryTheory.Exact.Injective
import TauCeti.CategoryTheory.Exact.Projective
import TauCeti.RingTheory.Artinian.FiniteLength
public import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# The stable Matlis duality over an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`, and `E` an injective `R`-module
such that `Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪` of `R`. Then
`D = Hom_R(-, E)` is a duality between finitely generated right and left `A`-modules
(`ModuleCat.matlisDualityOn`), and it exchanges projectives and injectives. So the stable Matlis
dual (`TauCeti.stableMatlisDualOp`) restricts to an equivalence between the opposite of finitely
presented right modules modulo projectives and finitely generated left modules modulo injectives.

Faithfulness: if `D f` factors through an injective, it extends across the monomorphism `D π`
(`ModuleCat.mono_matlisDualOp_map_of_surjective`) for a surjection `π : P ⟶ N` from a finitely
generated projective; the extension is the dual of a map `N' ⟶ P`, since `D` is full on maps into
a module of finite length (`ModuleCat.bijective_matlisDualOpMap`), and `f` factors through it
since `D` is faithful. Fullness and essential surjectivity come from biduality.

## Main definitions

* `TauCeti.finiteStableMatlisDualOp`: the stable Matlis dual from finitely presented right modules
  modulo projectives to finitely generated left modules modulo injectives.
* `TauCeti.finiteStableMatlisDualEquivalence`: over an Artin algebra, it is an equivalence.
* `TauCeti.matlisDualStableObj` and `TauCeti.finiteStableMatlisDualEquivalenceInverseObjIso`:
  the chosen quasi-inverse sends `M` to the class of `D M`.

## Main results

* `TauCeti.projectiveStableFunctor_map_eq_zero_of_matlisDualOp`: a map into a finitely generated
  right module whose dual factors through an injective factors through a projective.
* `TauCeti.bijective_stableMatlisDualOp_map`: the stable Matlis dual is bijective on stable maps
  into a finitely generated right module.
* `TauCeti.finiteStableMatlisDualEquivalenceInverseObjIso_naturality`: the quasi-inverse acts on
  maps as `D`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections II.3 and IV.1.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type*) [CommRing R] {A : Type u} [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{v} R]

section Artin

variable {R E} [IsArtinianRing R] [Module.Finite R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **A map whose dual factors through an injective factors through a projective.** For a map
`f : N' ⟶ N` of right modules over an Artin algebra with `N` finitely generated, if `D f` factors
through an injective left module, then `f` factors through a projective right module. -/
theorem projectiveStableFunctor_map_eq_zero_of_matlisDualOp {N N' : ModuleCat.{max u v} Aᵐᵒᵖ}
    [Module.Finite Aᵐᵒᵖ N] (f : N' ⟶ N)
    (hf : (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.map
      ((ModuleCat.matlisDualOp R E).map f.op) = 0) :
    (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map f = 0 := by
  have : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
  have := Module.finitePresentation_of_finite Aᵐᵒᵖ N
  let P : FiniteProjectivePresentation N := .ofFinitePresentation
  let π : P.P₀ ⟶ N := ModuleCat.ofHom P.π
  have hπ := ModuleCat.mono_matlisDualOp_map_of_surjective R E π P.surjective
  have hinj := isInjective_matlisDualOpObj_of_projective R E (ModuleCat.of Aᵐᵒᵖ P.P₀)
  rw [ExactStructure.injectiveStableFunctor_map_eq_zero_iff,
    ExactStructure.factorsThrough_injective_iff_exists_extension _ _
      ((ExactStructure.abelian_isInflation_iff _).mpr hπ) hinj] at hf
  obtain ⟨g, hg⟩ := hf
  have hP := isFiniteLength_of_finite_trans R Aᵐᵒᵖ P.P₀
  have hN := isFiniteLength_of_finite_trans R Aᵐᵒᵖ N
  obtain ⟨h, rfl⟩ := (ModuleCat.bijective_matlisDualOpMap hE hP).2 g
  have hf : h ≫ π = f := (ModuleCat.bijective_matlisDualOpMap hE hN).1
    (((ModuleCat.matlisDualOp R E).map_comp π.op h.op).trans hg)
  rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff, ← hf]
  exact ObjectProperty.factorsThrough_comp _
    ((ExactStructure.abelian_isProjective_iff _).mpr inferInstance) h π

/-- **The stable Matlis dual is bijective on stable maps** `N' ⟶ N` of right modules over an
Artin algebra, for `N` finitely generated. -/
theorem bijective_stableMatlisDualOp_map (N N' : ModuleCat.{max u v} Aᵐᵒᵖ)
    [Module.Finite Aᵐᵒᵖ N] :
    Function.Bijective
      (fun f : (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.obj N' ⟶
          (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.obj N ↦
        (stableMatlisDualOp R E).map f.op) := by
  refine ⟨fun f g h ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := Functor.map_surjective (ExactStructure.abelian _).projectiveStableFunctor f
    obtain ⟨g, rfl⟩ := Functor.map_surjective (ExactStructure.abelian _).projectiveStableFunctor g
    rw [← sub_eq_zero, ← Functor.map_sub]
    refine projectiveStableFunctor_map_eq_zero_of_matlisDualOp hE _ ?_
    have h' := congrArg (fun φ ↦ (stableMatlisDualOpObjIso R E N).inv ≫ φ ≫
      (stableMatlisDualOpObjIso R E N').hom) h
    simp only [stableMatlisDualOp_map_projectiveStableFunctor_map, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at h'
    rw [op_sub, Functor.map_sub, Functor.map_sub, h', sub_self]
  · obtain ⟨ψ, hψ⟩ := Functor.map_surjective (ExactStructure.abelian _).injectiveStableFunctor
      ((stableMatlisDualOpObjIso R E N).inv ≫ φ ≫ (stableMatlisDualOpObjIso R E N').hom)
    obtain ⟨f, rfl⟩ := (ModuleCat.bijective_matlisDualOpMap hE
      (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N)).2 ψ
    refine ⟨(ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map f, ?_⟩
    simp only [stableMatlisDualOp_map_projectiveStableFunctor_map, ModuleCat.matlisDualOp_map,
      Quiver.Hom.unop_op]
    rw [hψ]
    simp

end Artin

section Functor

variable [IsNoetherianRing R] [Module.Finite R A] [Module.Finite R E]

variable (A) in
/-- **The stable Matlis dual on finitely generated modules**: `D = Hom_R(-, E)` from the opposite
of finitely presented right modules modulo projectives to finitely generated left modules modulo
injectives. On objects it is the class of `D N`; it is isomorphic to the stable Matlis dual
(`TauCeti.finiteStableMatlisDualOpCompιIso`). -/
@[expose] def finiteStableMatlisDualOp :
    (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ ⥤
      FinitelyGeneratedInjectiveStableModule.{u, max u v} A :=
  ObjectProperty.lift _
    (((ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E).copyObj
      (fun N ↦ (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.obj
        ((ModuleCat.matlisDualOp R E).obj (op N.unop.obj.as)))
      (fun N ↦ stableMatlisDualOpObjIso R E N.unop.obj.as))
    fun N ↦ by
      have : Module.Finite R N.unop.obj.as :=
        have := N.unop.property
        Module.Finite.trans Aᵐᵒᵖ _
      have := Module.Finite.of_restrictScalars_finite R A (MatlisDual R E N.unop.obj.as)
      exact Module.Finite.equiv (ModuleCat.matlisDualOpObjEquiv R E _).symm

@[simp]
theorem finiteStableMatlisDualOp_obj_obj (N : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    ((finiteStableMatlisDualOp R A E).obj N).obj =
      (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.obj
        ((ModuleCat.matlisDualOp R E).obj (op N.unop.obj.as)) :=
  (rfl)

theorem finiteStableMatlisDualOp_map_hom
    {N N' : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ} (f : N ⟶ N') :
    ((finiteStableMatlisDualOp R A E).map f).hom =
      (stableMatlisDualOpObjIso R E N.unop.obj.as).inv ≫
        (stableMatlisDualOp R E).map f.unop.hom.op ≫
          (stableMatlisDualOpObjIso R E N'.unop.obj.as).hom :=
  (rfl)

/-- The stable Matlis dual on finitely generated modules is the stable Matlis dual, up to the
identification of `D N` with its class. -/
def finiteStableMatlisDualOpCompιIso :
    finiteStableMatlisDualOp R A E ⋙ ObjectProperty.ι _ ≅
      (ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E :=
  (Functor.isoCopyObj _ _ _).symm

@[simp]
theorem finiteStableMatlisDualOpCompιIso_hom_app
    (N : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    (finiteStableMatlisDualOpCompιIso R E).hom.app N =
      (stableMatlisDualOpObjIso R E N.unop.obj.as).inv :=
  (rfl)

instance : (finiteStableMatlisDualOp R A E).Additive :=
  have := Functor.additive_of_iso (finiteStableMatlisDualOpCompιIso R E (A := A)).symm
  Functor.additive_of_comp_faithful _ (ObjectProperty.ι _)

variable {R E} [IsArtinianRing R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- The stable Matlis dual on finitely generated modules is bijective on morphisms. -/
theorem bijective_finiteStableMatlisDualOp_map
    (N N' : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    Function.Bijective ((finiteStableMatlisDualOp R A E).map : (N ⟶ N') → _) := by
  have := N.unop.property
  convert (((ObjectProperty.fullyFaithfulι _).homEquiv
      (X := (finiteStableMatlisDualOp R A E).obj N)
      (Y := (finiteStableMatlisDualOp R A E).obj N')).symm.bijective.comp
    ((Iso.homCongr (stableMatlisDualOpObjIso R E N.unop.obj.as)
      (stableMatlisDualOpObjIso R E N'.unop.obj.as)).bijective.comp
      ((bijective_stableMatlisDualOp_map hE N.unop.obj.as N'.unop.obj.as).comp
        ((ObjectProperty.fullyFaithfulι _).homEquiv.bijective.comp
          Quiver.Hom.opEquiv.symm.bijective)))) using 1
  funext f
  exact ObjectProperty.hom_ext _ (finiteStableMatlisDualOp_map_hom R E f)

omit hE in
variable (R E) in
/-- The class of the dual `D M` of a finitely generated left module, as a finitely presented right
module modulo projectives. -/
noncomputable abbrev matlisDualStableObj
    (M : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ :=
  ⟨⟨(ModuleCat.matlisDual R E).obj (op M.obj.as)⟩, by
    have := M.property
    have : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
    have : Module.Finite R M.obj.as := Module.Finite.trans A _
    have := Module.Finite.of_restrictScalars_finite R Aᵐᵒᵖ (MatlisDual R E M.obj.as)
    have : Module.Finite Aᵐᵒᵖ ((ModuleCat.matlisDual R E).obj (op M.obj.as)) :=
      Module.Finite.equiv (ModuleCat.matlisDualObjEquiv R E _).symm
    exact Module.finitePresentation_of_finite Aᵐᵒᵖ
      ((ModuleCat.matlisDual R E).obj (op M.obj.as))⟩

/-- **Biduality modulo injectives**: the stable Matlis dual of `D M` is `M`, through evaluation
`M ≅ D (D M)`. -/
noncomputable def finiteStableMatlisDualOpObjIso
    (M : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (finiteStableMatlisDualOp R A E).obj (op (matlisDualStableObj R E M)) ≅ M :=
  ObjectProperty.isoMk _ ((ExactStructure.abelian _).injectiveStableFunctor.mapIso
    (ModuleCat.matlisDualEvalIso hE M.obj.as
      (have := M.property; isFiniteLength_of_finite_trans R A _)).symm)

theorem finiteStableMatlisDualOpObjIso_hom_hom
    (M : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (finiteStableMatlisDualOpObjIso hE M).hom.hom =
      (ExactStructure.abelian _).injectiveStableFunctor.map
        (ModuleCat.matlisDualEvalIso hE M.obj.as
          (have := M.property; isFiniteLength_of_finite_trans R A _)).inv :=
  (rfl)

/-- Every finitely generated module is, modulo injectives, the dual of a finitely presented right
module: `M ≅ D (D M)`. -/
theorem essSurj_finiteStableMatlisDualOp : (finiteStableMatlisDualOp R A E).EssSurj where
  mem_essImage M := ⟨op (matlisDualStableObj R E M), ⟨finiteStableMatlisDualOpObjIso hE M⟩⟩

omit [IsNoetherianRing R] [Module.Finite R E] in
variable (R E A) in
/-- **The stable Matlis duality over an Artin algebra**: `D = Hom_R(-, E)` is an equivalence from
the opposite of finitely presented right modules modulo projectives to finitely generated left
modules modulo injectives. -/
@[expose] def finiteStableMatlisDualEquivalence :
    (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ ≌
      FinitelyGeneratedInjectiveStableModule.{u, max u v} A :=
  haveI := finite_of_forall_isMaximal hE
  haveI : (finiteStableMatlisDualOp R A E).IsEquivalence :=
    { faithful := ⟨fun h ↦ (bijective_finiteStableMatlisDualOp_map hE _ _).1 h⟩
      full := ⟨fun φ ↦ (bijective_finiteStableMatlisDualOp_map hE _ _).2 φ⟩
      essSurj := essSurj_finiteStableMatlisDualOp hE }
  (finiteStableMatlisDualOp R A E).asEquivalence

@[simp]
theorem finiteStableMatlisDualEquivalence_functor :
    (finiteStableMatlisDualEquivalence R A E hE).functor = finiteStableMatlisDualOp R A E :=
  (rfl)

/-- **The inverse of the stable Matlis duality is the Matlis dual of left modules.** The chosen
quasi-inverse of `TauCeti.finiteStableMatlisDualEquivalence` sends `M` to the class of `D M`. -/
noncomputable def finiteStableMatlisDualEquivalenceInverseObjIso
    (M : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (finiteStableMatlisDualEquivalence R A E hE).inverse.obj M ≅ op (matlisDualStableObj R E M) :=
  (finiteStableMatlisDualEquivalence R A E hE).inverse.mapIso
      (finiteStableMatlisDualOpObjIso hE M).symm ≪≫
    (finiteStableMatlisDualEquivalence R A E hE).unitIso.symm.app _

theorem finiteStableMatlisDualEquivalenceInverseObjIso_hom
    (M : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (finiteStableMatlisDualEquivalenceInverseObjIso hE M).hom =
      (finiteStableMatlisDualEquivalence R A E hE).inverse.map
          (finiteStableMatlisDualOpObjIso hE M).inv ≫
        (finiteStableMatlisDualEquivalence R A E hE).unitIso.inv.app _ :=
  (rfl)

/-- **The square of biduality modulo injectives**: for a representative `g₀` of `g : M ⟶ M'`, the
stable Matlis dual of the class of `D g₀` corresponds to `g`. -/
theorem finiteStableMatlisDualOpObjIso_naturality
    {M M' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : M ⟶ M')
    (g₀ : M.obj.as ⟶ M'.obj.as)
    (hg : (ExactStructure.abelian _).injectiveStableFunctor.map g₀ = g.hom) :
    (finiteStableMatlisDualOp R A E).map
        (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map
          ((ModuleCat.matlisDual R E).map g₀.op)) :
            matlisDualStableObj R E M' ⟶ matlisDualStableObj R E M).op ≫
      (finiteStableMatlisDualOpObjIso hE M').hom =
    (finiteStableMatlisDualOpObjIso hE M).hom ≫ g := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, finiteStableMatlisDualOp_map_hom,
    Quiver.Hom.unop_op]
  rw [ObjectProperty.homMk_hom, stableMatlisDualOp_map_projectiveStableFunctor_map,
    finiteStableMatlisDualOpObjIso_hom_hom, finiteStableMatlisDualOpObjIso_hom_hom, ← hg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  -- Evaluation lives in `ModuleCat.{max v u}` and the stable categories in `ModuleCat.{max u v}`;
  -- `rw` does not match across the two spellings, so the remaining steps are applied as terms.
  refine (Functor.map_comp _ _ _).symm.trans
    ((congrArg (ExactStructure.abelian _).injectiveStableFunctor.map ?_).trans
      (Functor.map_comp _ _ _))
  refine (Iso.eq_inv_comp _).mpr ((Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).mpr ?_))
  exact (ModuleCat.matlisDualEvalIso_hom_naturality hE g₀ _ _).symm

/-- **Naturality of the inverse of the stable Matlis duality.** For a representative `g₀` of
`g : M ⟶ M'`, the chosen quasi-inverse sends `g` to the class of `D g₀`. -/
theorem finiteStableMatlisDualEquivalenceInverseObjIso_naturality
    {M M' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : M ⟶ M')
    (g₀ : M.obj.as ⟶ M'.obj.as)
    (hg : (ExactStructure.abelian _).injectiveStableFunctor.map g₀ = g.hom) :
    (finiteStableMatlisDualEquivalence R A E hE).inverse.map g ≫
        (finiteStableMatlisDualEquivalenceInverseObjIso hE M').hom =
      (finiteStableMatlisDualEquivalenceInverseObjIso hE M).hom ≫
        (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map
          ((ModuleCat.matlisDual R E).map g₀.op)) :
            matlisDualStableObj R E M' ⟶ matlisDualStableObj R E M).op := by
  have h := congrArg (fun k ↦ (finiteStableMatlisDualOpObjIso hE M).inv ≫ k ≫
    (finiteStableMatlisDualOpObjIso hE M').inv)
    (finiteStableMatlisDualOpObjIso_naturality hE g g₀ hg)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
  have h' := congrArg (finiteStableMatlisDualEquivalence R A E hE).inverse.map h
  rw [Functor.map_comp, Functor.map_comp] at h'
  rw [finiteStableMatlisDualEquivalenceInverseObjIso_hom,
    finiteStableMatlisDualEquivalenceInverseObjIso_hom]
  -- The composites produced by `Functor.map_comp` use the instance `Category.opposite`, while the
  -- statement uses `CategoryStruct.opposite`; `rw` does not identify the two, so the associativity
  -- steps are applied as terms, checked up to definitional unfolding.
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h'.symm).trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((finiteStableMatlisDualEquivalence R A E hE).unitIso.inv.naturality _)).trans ?_)
  exact (Category.assoc _ _ _).symm

end Functor

end TauCeti
