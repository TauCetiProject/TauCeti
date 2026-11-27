/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.ComponentCenter
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.Constant
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe

/-!
# Central sections of a constant diagram of disjoint copies of `B G`

For a type `I` and a commutative group `G`, consider the constant pseudofunctor on a category `C`
with fibre the groupoid `Discrete I × SingleObj G`: `I` disjoint copies of the one-object groupoid
`B G`. Its central sections over every `U` are the profiles `I → G`
(`BandFixtures.componentSectionsEquiv`): the section of a profile `a` evaluates at every arrow and
at an object over the label `i` to the automorphism `(𝟙, a i)`, and restricts to the section of
the same profile.

With one label, evaluation at the canonical object over `U` is a bijection from central sections
to automorphisms (`BandFixtures.component_eval_bijective`). With two labels it is not injective
(`BandFixtures.component_eval_not_injective`): the profiles `(1, g)` and `(1, 1)` have the same
evaluation on the `false` component. The two canonical objects are not isomorphic
(`BandFixtures.fibre_no_cross_iso`), so the two-component diagram is not a gerbe for the bottom
topology (`BandFixtures.constant_two_components_not_gerbe`). These are the disconnected fixtures
for the intrinsic band of the Stacks Project, Lemma 8.11.8 (0CJY), which needs the gerbe
hypothesis.

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.BandFixtures`:

* `componentObj V i`: the object `(i, ⋆)` of the fibre over `V`.
* `componentSectionsEquiv C I G U`: the profiles `I → G` as the central sections over `U`.

## Main results

* `evaluation_componentSectionsEquiv`, `evaluation_componentSectionsEquiv_snd`,
  `restrict_componentSectionsEquiv`, `componentSectionsEquiv_symm_apply`.
* `component_eval_bijective`, `component_eval_not_injective`.
* `fibre_no_cross_iso`, `constant_two_components_not_gerbe`.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.BandFixtures

variable {C : Type u} [Category.{v} C] {I : Type u'} {G : Type v'}

/-- The object `(i, ⋆)` of the fibre over `V` of the constant diagram with fibre
`Discrete I × SingleObj G`. -/
@[expose]
def componentObj [Monoid G] (V : C) (i : I) :
    (constant C (Discrete I × SingleObj G)).obj (.mk (op V)) :=
  (⟨i⟩, SingleObj.star G)

/-- **No isomorphism between components**: the canonical objects of the `false` and `true`
components of `Discrete Bool × SingleObj G` are not isomorphic. -/
theorem fibre_no_cross_iso [Monoid G] :
    IsEmpty (((⟨false⟩, SingleObj.star G) : Discrete Bool × SingleObj G) ≅
      (⟨true⟩, SingleObj.star G)) :=
  ⟨fun e ↦ Bool.false_ne_true (Discrete.eq_of_hom e.hom.1)⟩

/-- **Two components do not form a gerbe**: on any category with an object `U`, the constant
diagram with fibre `Discrete Bool × SingleObj G` is not a gerbe for the bottom topology, whose
only covering sieve is the maximal one, since its two canonical objects over `U` are not
isomorphic. -/
theorem constant_two_components_not_gerbe [Monoid G] (U : C) :
    ¬ (constant C (Discrete Bool × SingleObj G)).IsGerbe ⊥ := by
  intro h
  obtain ⟨R, hR, hiso⟩ := h.exists_covering_iso (componentObj U false) (componentObj U true)
  rw [GrothendieckTopology.bot_covering] at hR
  obtain ⟨e⟩ := hiso (𝟙 U) (by rw [hR]; trivial)
  exact (fibre_no_cross_iso (G := G)).false e

variable [CommGroup G]

variable (C I G) in
/-- **The central sections of the constant diagram of `I` copies of `B G` are the profiles**
`I → G`: the profile `a` gives the constant section of the centre unit acting by `a i` on the
component `i`. -/
def componentSectionsEquiv (U : C) :
    (I → G) ≃* IntrinsicBandSections (constant C (Discrete I × SingleObj G)) U :=
  (componentCenterEquiv I G).trans (constantSectionsEquiv C _ U)

theorem componentSectionsEquiv_apply (U : C) (a : I → G) :
    componentSectionsEquiv C I G U a = constantSection U (componentCenterUnit a) := by
  rw [componentSectionsEquiv, MulEquiv.trans_apply, componentCenterEquiv_apply,
    constantSectionsEquiv_apply]

/-- The inverse of `componentSectionsEquiv` reads the group component at `(i, ⋆)` of the value at
the identity of `U`. -/
@[simp]
theorem componentSectionsEquiv_symm_apply (U : C)
    (s : IntrinsicBandSections (constant C (Discrete I × SingleObj G)) U) (i : I) :
    (componentSectionsEquiv C I G U).symm s i =
      ((s.val U (𝟙 U)).val.app (componentObj U i)).2 := by
  rw [componentSectionsEquiv, MulEquiv.symm_trans_apply, constantSectionsEquiv_symm_apply]
  exact componentCenterEquiv_symm_apply (s.val U (𝟙 U)) i

/-- The evaluation of the section of a profile `a` at any arrow `f` and any object `x` is the
component of the centre of `a` at `x`. -/
theorem evaluation_componentSectionsEquiv {U V : C} (f : V ⟶ U) (a : I → G)
    (x : (constant C (Discrete I × SingleObj G)).obj (.mk (op V))) :
    (IntrinsicBandSections.evaluation f x (componentSectionsEquiv C I G U a)).asIso.hom =
      (componentCenter a).app x := by
  rw [IntrinsicBandSections.evaluation_asIso_hom, componentSectionsEquiv_apply,
    val_constantSection, val_componentCenterUnit]

/-- **Band evaluation of a profile**: the group component of the evaluation of the section of `a`
at any arrow and at `(i, ⋆)` is `a i`. -/
theorem evaluation_componentSectionsEquiv_snd {U V : C} (f : V ⟶ U) (a : I → G) (i : I) :
    ((IntrinsicBandSections.evaluation f (componentObj V i)
      (componentSectionsEquiv C I G U a)).asIso.hom).2 =
      (a i : SingleObj.star G ⟶ SingleObj.star G) := by
  rw [evaluation_componentSectionsEquiv]
  exact componentCenter_app_snd a (componentObj V i)

/-- Restricting the section of a profile gives the section of the same profile. -/
@[simp]
theorem restrict_componentSectionsEquiv {U V : C} (f : V ⟶ U) (a : I → G) :
    IntrinsicBandSections.restrict f (componentSectionsEquiv C I G U a) =
      componentSectionsEquiv C I G V a := by
  rw [componentSectionsEquiv_apply, componentSectionsEquiv_apply, restrict_constantSection]

/-- The profile of a central section `s` at `i` is the group component of its evaluation at the
identity of `U` and `(i, ⋆)`. -/
theorem componentSectionsEquiv_symm_apply_eq_evaluation (U : C)
    (s : IntrinsicBandSections (constant C (Discrete I × SingleObj G)) U) (i : I) :
    (componentSectionsEquiv C I G U).symm s i =
      ((IntrinsicBandSections.evaluation (𝟙 U) (componentObj U i) s).asIso.hom).2 := by
  rw [componentSectionsEquiv_symm_apply, IntrinsicBandSections.evaluation_asIso_hom]

/-- **One component: evaluation is bijective.** If `I` has at most one element, evaluation at the
identity of `U` and the canonical object over a label `i` is a bijection from the central
sections to the automorphisms of that object. -/
theorem component_eval_bijective [Subsingleton I] (U : C) (i : I) :
    Function.Bijective (IntrinsicBandSections.evaluation
      (F := constant C (Discrete I × SingleObj G)) (𝟙 U) (componentObj U i)) := by
  refine ⟨fun s t h ↦ (componentSectionsEquiv C I G U).symm.injective (funext fun j ↦ ?_),
    fun g ↦ ⟨componentSectionsEquiv C I G U fun _ ↦ g.asIso.hom.2, ?_⟩⟩
  · obtain rfl := Subsingleton.elim i j
    rw [componentSectionsEquiv_symm_apply_eq_evaluation,
      componentSectionsEquiv_symm_apply_eq_evaluation, h]
  · refine Aut.ext (Iso.ext (Prod.hom_ext (Subsingleton.elim _ _) ?_))
    rw [evaluation_componentSectionsEquiv]
    exact componentCenter_app_snd _ (componentObj U i)

/-- **Two components: evaluation on one component is not injective.** For `g ≠ 1`, the profiles
`(1, g)` and `(1, 1)` give distinct central sections with the same evaluation at the identity of
`U` and the canonical object of the `false` component. -/
theorem component_eval_not_injective (U : C) {g : G} (hg : g ≠ 1) :
    ¬ Function.Injective (IntrinsicBandSections.evaluation
      (F := constant C (Discrete Bool × SingleObj G)) (𝟙 U) (componentObj U false)) := by
  intro hinj
  let a : Bool → G := fun b ↦ if b then g else 1
  have h : componentSectionsEquiv C Bool G U a = componentSectionsEquiv C Bool G U 1 :=
    hinj (Aut.ext (Iso.ext (Prod.hom_ext (Subsingleton.elim _ _) (by
      rw [evaluation_componentSectionsEquiv, evaluation_componentSectionsEquiv]
      have h₁ := componentCenter_app_snd a (componentObj U false)
      have h₂ := componentCenter_app_snd (1 : Bool → G) (componentObj U false)
      have h₃ : a false = (1 : Bool → G) false := by simp [a]
      exact h₁.trans (h₃.trans h₂.symm)))))
  exact hg (congrFun ((componentSectionsEquiv C Bool G U).injective h) true)

end CategoryTheory.Pseudofunctor.BandFixtures
