/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe

/-!
# Evaluations of central sections are determined locally

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a prestack for a Grothendieck topology `J` and
`ZF(U)` its group of intrinsic central sections over `U`
(`CategoryTheory.Pseudofunctor.IntrinsicBandSections`). The evaluation `ev_(a, x)(s)` of a section
at `a : V ⟶ U` and `x` over `V` is an automorphism of `x`, and morphisms of the fibre are
determined by their pullbacks along a covering sieve. Since the pullback of `ev_(a, x)(s)` along
`g : W ⟶ V` is `ev_(g ≫ a, g^* x)(s)`, two sections with the same evaluations at the pulled-back
objects along a covering sieve of `V` have the same evaluation at `(a, x)`
(`IntrinsicBandSections.evaluation_eq_of_cover`). No groupoid, gerbe or commutativity hypothesis
is needed.

If `F` is a gerbe, evaluation at a single object `x` over `U` is injective on `ZF(U)`
(`IntrinsicBandSections.evaluation_injective`), without any commutativity of the automorphism
groups: equality at `x` pulls back to equality at every `a^* x`; any `y` over `V` is locally
isomorphic to `a^* x`, conjugation along a local isomorphism carries the evaluations at the
pullbacks of `a^* x` to those at the pullbacks of `y`, and the previous result glues.

## Main results

* `IntrinsicBandSections.evaluation_eq_of_cover`: evaluations agreeing on a covering sieve agree.
* `IntrinsicBandSections.evaluation_injective`: on a gerbe, evaluation at one object is
  injective.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.IntrinsicBandSections

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {U : C}

/-- **Evaluations are determined on a cover.** For a prestack, if two central sections have the
same evaluations at `(g ≫ a, g^* x)` for every arrow `g` of a covering sieve of `V`, they have the
same evaluation at `(a, x)`. -/
theorem evaluation_eq_of_cover [F.IsPrestack J] {V : C} (a : V ⟶ U) (x : F.obj (.mk (op V)))
    {s t : IntrinsicBandSections F U} {R : Sieve V} (hR : R ∈ J V)
    (h : ∀ ⦃W : C⦄ (g : W ⟶ V), R g →
      evaluation (g ≫ a) ((F.map g.op.toLoc).toFunctor.obj x) s =
        evaluation (g ≫ a) ((F.map g.op.toLoc).toFunctor.obj x) t) :
    evaluation a x s = evaluation a x t := by
  refine Aut.ext (Iso.ext ((F.isPrestackFor' R hR).fullyFaithful.map_injective
    (DescentData.hom_ext fun i ↦ ?_)))
  have hi := congrArg (fun e : Aut _ ↦ e.asIso.hom) (h i.obj.hom i.property)
  simp only [evaluation_asIso_hom] at hi
  simp only [toDescentData_map_hom, evaluation_asIso_hom, map_app]
  exact hi

/-- **Evaluation at one object of a gerbe is injective**: two central sections over `U` with the
same evaluation at an object `x` over `U` are equal. No commutativity of the automorphism groups is
needed. -/
theorem evaluation_injective [F.IsGerbe J] (x : F.obj (.mk (op U))) :
    Function.Injective (evaluation (𝟙 U) x) := by
  intro s t hst
  refine ext_evaluation fun V a y ↦ ?_
  have h₁ : evaluation a ((F.map a.op.toLoc).toFunctor.obj x) s =
      evaluation a ((F.map a.op.toLoc).toFunctor.obj x) t := by
    have h := congrArg ((F.map a.op.toLoc).toFunctor.mapAut x) hst
    rwa [mapAut_evaluation, mapAut_evaluation, Category.comp_id] at h
  obtain ⟨R, hR, hiso⟩ := IsGerbe.exists_covering_iso (J := J)
    ((F.map a.op.toLoc).toFunctor.obj x) y
  refine evaluation_eq_of_cover a y hR fun W g hg ↦ ?_
  obtain ⟨e⟩ := hiso g hg
  have h₂ : evaluation (g ≫ a)
      ((F.map g.op.toLoc).toFunctor.obj ((F.map a.op.toLoc).toFunctor.obj x)) s =
      evaluation (g ≫ a)
        ((F.map g.op.toLoc).toFunctor.obj ((F.map a.op.toLoc).toFunctor.obj x)) t := by
    rw [← mapAut_evaluation, h₁, mapAut_evaluation]
  rw [← autMulEquivOfIso_evaluation (g ≫ a) e s, ← autMulEquivOfIso_evaluation (g ≫ a) e t, h₂]

end CategoryTheory.Pseudofunctor.IntrinsicBandSections
