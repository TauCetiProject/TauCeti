/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Stable.Basic
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.FiniteLength
public import TauCeti.Algebra.Module.AuslanderReiten.Functor
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective
import TauCeti.CategoryTheory.Exact.Injective
import TauCeti.CategoryTheory.Exact.Projective
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# The stable Matlis duality over an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`, and `E` an injective `R`-module
such that each `Hom_R(R ⧸ 𝔪, E)` has length one. Then `D = Hom_R(-, E)` is a duality between
finitely generated right and left `A`-modules (`ModuleCat.matlisDualityOn`), and it exchanges
projectives and injectives. So the stable Matlis dual (`TauCeti.stableMatlisDualOp`) restricts to
an equivalence between the opposite of finitely presented right modules modulo projectives and
finitely generated left modules modulo injectives.

Faithfulness: if `D f` factors through an injective, it extends across the monomorphism `D π`
for a surjection `π : P ⟶ N` from a finitely generated projective; the extension is the dual of a
map `N' ⟶ P` by fullness of `D`, and `f` factors through it by faithfulness. Fullness and essential
surjectivity come from the duality itself.

## Main definitions

* `TauCeti.FinitelyGeneratedInjectiveStableModule`: finitely generated modules in the injective
  stable quotient.
* `TauCeti.finiteStableMatlisDualOp`: the stable Matlis dual from finitely presented right modules
  modulo projectives to finitely generated left modules modulo injectives.
* `TauCeti.finiteStableMatlisDualEquivalence`: over an Artin algebra, it is an equivalence.

## Main results

* `TauCeti.projectiveStableFunctor_map_eq_zero_of_matlisDualOp`: a map of finitely generated right
  modules whose dual factors through an injective factors through a projective.
* `TauCeti.bijective_stableMatlisDualOp_map`: the stable Matlis dual is bijective on stable maps
  between finitely generated right modules.

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

variable (A : Type u) [Ring A] in
/-- Finitely generated modules, with morphisms taken modulo maps through injective modules. This
is a full subcategory of the injective stable quotient of `ModuleCat`. -/
abbrev FinitelyGeneratedInjectiveStableModule :=
  ObjectProperty.FullSubcategory
    (fun M : (ExactStructure.abelian (ModuleCat.{v} A)).InjectiveStableCategory ↦
      Module.Finite A M.as)

variable (R : Type*) [CommRing R] {A : Type u} [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{v} R]

section Artin

variable {R E} [IsArtinianRing R] [Module.Finite R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **A map whose dual factors through an injective factors through a projective.** For a map
`f : N' ⟶ N` of finitely generated right modules over an Artin algebra, if `D f` factors through
an injective left module, then `f` factors through a projective right module. -/
theorem projectiveStableFunctor_map_eq_zero_of_matlisDualOp {N N' : ModuleCat.{max u v} Aᵐᵒᵖ}
    [Module.Finite Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N'] (f : N' ⟶ N)
    (hf : (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.map
      ((ModuleCat.matlisDualOp R E).map f.op) = 0) :
    (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map f = 0 := by
  have : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
  have := Module.finitePresentation_of_finite Aᵐᵒᵖ N
  let P : FiniteProjectivePresentation N := .ofFinitePresentation
  let π : P.P₀ ⟶ N := ModuleCat.ofHom P.π
  have hπ : Mono ((ModuleCat.matlisDualOp R E).map π.op) := by
    rw [ModuleCat.mono_iff_injective]
    intro φ ψ h
    rw [ModuleCat.matlisDualOp_map, Quiver.Hom.unop_op] at h
    apply (ModuleCat.matlisDualOpObjEquiv R E N).injective
    refine (MatlisDual.equivLinearMap R E N).injective
      (LinearMap.lcomp_injective_of_surjective (S := R) (N := E) (P.π.restrictScalars R)
        P.surjective (LinearMap.ext fun y ↦ ?_))
    rw [LinearMap.lcomp_apply, LinearMap.lcomp_apply]
    exact (ModuleCat.matlisDualOpObjEquiv_map_apply R E π φ y).symm.trans
      ((congrArg (fun χ ↦ MatlisDual.equivLinearMap R E _
        (ModuleCat.matlisDualOpObjEquiv R E _ χ) y) h).trans
          (ModuleCat.matlisDualOpObjEquiv_map_apply R E π ψ y))
  have hinj := isInjective_matlisDualOpObj_of_projective R E (ModuleCat.of Aᵐᵒᵖ P.P₀)
  rw [ExactStructure.injectiveStableFunctor_map_eq_zero_iff,
    ExactStructure.factorsThrough_injective_iff_exists_extension _ _
      ((ExactStructure.abelian_isInflation_iff _).mpr hπ) hinj] at hf
  obtain ⟨g, hg⟩ := hf
  have hN' := isFiniteLength_of_finite_trans R Aᵐᵒᵖ N'
  have hP := isFiniteLength_of_finite_trans R Aᵐᵒᵖ P.P₀
  have hN := isFiniteLength_of_finite_trans R Aᵐᵒᵖ N
  obtain ⟨h, rfl⟩ := (ModuleCat.bijective_matlisDualOpMap hE hN' hP).2 g
  have hf : h ≫ π = f := (ModuleCat.bijective_matlisDualOpMap hE hN' hN).1
    (((ModuleCat.matlisDualOp R E).map_comp π.op h.op).trans hg)
  rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff, ← hf]
  exact ObjectProperty.factorsThrough_comp _
    ((ExactStructure.abelian_isProjective_iff _).mpr inferInstance) h π

/-- **The stable Matlis dual is bijective on stable maps** between finitely generated right
modules over an Artin algebra. -/
theorem bijective_stableMatlisDualOp_map (N N' : ModuleCat.{max u v} Aᵐᵒᵖ)
    [Module.Finite Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N'] :
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
      (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N') (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N)).2 ψ
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
  have := N'.unop.property
  obtain ⟨hi, hs⟩ := bijective_stableMatlisDualOp_map hE N.unop.obj.as N'.unop.obj.as
  refine ⟨fun f g h ↦ ?_, fun φ ↦ ?_⟩
  · have h' := congrArg (fun φ ↦ φ.hom) h
    simp only [finiteStableMatlisDualOp_map_hom] at h'
    exact Quiver.Hom.unop_inj
      (ObjectProperty.hom_ext _ (hi ((cancel_mono _).1 ((cancel_epi _).1 h'))))
  · obtain ⟨f, hf⟩ := hs ((stableMatlisDualOpObjIso R E _).hom ≫ φ.hom ≫
      (stableMatlisDualOpObjIso R E _).inv)
    refine ⟨(ObjectProperty.homMk f : N'.unop ⟶ N.unop).op, ObjectProperty.hom_ext _ ?_⟩
    simp only at hf
    rw [finiteStableMatlisDualOp_map_hom]
    simp only [Quiver.Hom.unop_op, ObjectProperty.homMk_hom]
    rw [hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    -- `φ.hom` is stated between the objects of the full subcategory, which are those classes.
    exact (Category.assoc φ.hom _ _).trans
      ((congrArg (fun k ↦ φ.hom ≫ k) (Iso.inv_hom_id _)).trans (Category.comp_id _))

/-- Every finitely generated module is, modulo injectives, the dual of a finitely presented right
module: `M ≅ D (D M)`. -/
theorem essSurj_finiteStableMatlisDualOp : (finiteStableMatlisDualOp R A E).EssSurj where
  mem_essImage M := by
    have := M.property
    have : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
    have : Module.Finite R M.obj.as := Module.Finite.trans A _
    let X := (ModuleCat.matlisDual R E).obj (op M.obj.as)
    have := Module.Finite.of_restrictScalars_finite R Aᵐᵒᵖ (MatlisDual R E M.obj.as)
    have : Module.Finite Aᵐᵒᵖ X := Module.Finite.equiv (ModuleCat.matlisDualObjEquiv R E _).symm
    have := Module.finitePresentation_of_finite Aᵐᵒᵖ X
    exact ⟨op ⟨(ExactStructure.abelian _).projectiveStableFunctor.obj X, this⟩,
      ⟨ObjectProperty.isoMk _ (Functor.mapIso (ExactStructure.abelian _).injectiveStableFunctor
        (ModuleCat.matlisDualEvalIso hE M.obj.as
          (isFiniteLength_of_finite_trans R A _)).symm)⟩⟩

omit [IsNoetherianRing R] [Module.Finite R E] in
variable (R E A) in
/-- **The stable Matlis duality over an Artin algebra**: `D = Hom_R(-, E)` is an equivalence from
the opposite of finitely presented right modules modulo projectives to finitely generated left
modules modulo injectives. -/
def finiteStableMatlisDualEquivalence :
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

end Functor

end TauCeti
