/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import TauCeti.CategoryTheory.Sites.LocallyConstant

/-!
# Tensor products of locally constant sheaves

Let `J` be a Grothendieck topology on `C` and `A` a monoidal category for which sheafification is
compatible with tensor products (`(J.W (A := A)).IsMonoidal`), so that `Sheaf J A` carries the
monoidal structure `CategoryTheory.Sheaf.monoidalCategory`: the tensor product of two sheaves is
the sheafification of their sectionwise tensor product.

* `CategoryTheory.Sheaf.constantSheafTensorIso`: the tensor product of the constant sheaves on `M`
  and `N` is the constant sheaf on `M ⊗ N`.
* `CategoryTheory.Sheaf.overPresheafToSheafIso`: the restriction to `Over X` of the
  sheafification of `P` is the sheafification of the restriction of `P`.
* `CategoryTheory.Sheaf.overTensorIso`: the restriction of `F ⊗ G` to `Over X` is the
  sheafification of the sectionwise tensor product of the restrictions of `F` and `G`. Hence it
  only depends on the restrictions of `F` and `G` (`CategoryTheory.Sheaf.overTensorIsoOfIso`).
* `CategoryTheory.Sheaf.IsLocallyConstantIn.tensor`: the tensor product of a sheaf which is
  locally constant with values in `P` and one which is locally constant with values in `Q` is
  locally constant with values in any `R` containing the tensor products `M ⊗ N` with `P M`
  and `Q N`.

No monoidal structure on the sheaves on `Over X` is needed. For a concrete category `A` in which
the morphisms inverted by sheafification are the locally bijective ones, on `C` and on each
`Over X` (`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`), restriction to `Over X`
commutes with sheafification (`CategoryTheory.Sheaf.overPresheafToSheafIso`), because restriction
along the cocontinuous functor `Over.forget X` preserves local bijectivity.

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe v u v' u'

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

variable (J) in
/-- The tensor product of two constant sheaves is the constant sheaf on the tensor product. -/
noncomputable def constantSheafTensorIso (M N : A) :
    (constantSheaf J A).obj M ⊗ (constantSheaf J A).obj N ≅ (constantSheaf J A).obj (M ⊗ N) :=
  Functor.Monoidal.μIso (presheafToSheaf J A) _ _ ≪≫
    (presheafToSheaf J A).mapIso (NatIso.ofComponents fun _ ↦ Iso.refl _)

section LocallyBijective

variable {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA] [J.WEqualsLocallyBijective A] [∀ X : C, HasWeakSheafify (J.over X) A]
  [∀ X : C, (J.over X).WEqualsLocallyBijective A]

include FA CA

omit [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]
  [∀ X : C, HasWeakSheafify (J.over X) A] in
/-- Restriction to `Over X` sends morphisms of presheaves which become isomorphisms after
sheafification to morphisms with the same property. -/
theorem _root_.CategoryTheory.GrothendieckTopology.W.whiskerLeft_over_forget {P Q : Cᵒᵖ ⥤ A}
    {f : P ⟶ Q} (hf : J.W f) (X : C) : (J.over X).W (Functor.whiskerLeft (Over.forget X).op f) :=
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  have := Presheaf.isLocallyInjective_whisker (J.over X) J (Over.forget X) f
  have := Presheaf.isLocallySurjective_whisker (J.over X) J (Over.forget X) f
  GrothendieckTopology.W_of_isLocallyBijective _ _

/-- **Restriction of a sheafification.** The restriction to `Over X` of the sheafification of a
presheaf `P` is the sheafification of the restriction of `P`. -/
noncomputable def overPresheafToSheafIso (P : Cᵒᵖ ⥤ A) (X : C) :
    ((presheafToSheaf J A).obj P).over X ≅
      (presheafToSheaf (J.over X) A).obj ((Over.forget X).op ⋙ P) :=
  have := ((J.over X).W_iff _).1 ((J.W_toSheafify P).whiskerLeft_over_forget X)
  sheafificationIso _ ≪≫
    (asIso ((presheafToSheaf (J.over X) A).map
      (Functor.whiskerLeft (Over.forget X).op (toSheafify J P)))).symm

/-- **Restriction of a tensor product.** The restriction of `F ⊗ G` to `Over X` is the
sheafification of the sectionwise tensor product of the restrictions of `F` and `G`. -/
noncomputable def overTensorIso (F G : Sheaf J A) (X : C) :
    (F ⊗ G).over X ≅ (presheafToSheaf (J.over X) A).obj ((F.over X).obj ⊗ (G.over X).obj) :=
  (J.overPullback A X).mapIso ((sheafificationIso F ⊗ᵢ sheafificationIso G) ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J A) _ _) ≪≫
    overPresheafToSheafIso (F.obj ⊗ G.obj) X ≪≫
    (presheafToSheaf (J.over X) A).mapIso (Iso.refl _)

/-- The restriction of `F ⊗ G` to `Over X` only depends on the restrictions of `F` and `G`. -/
noncomputable def overTensorIsoOfIso {F F' G G' : Sheaf J A} {X : C} (e : F.over X ≅ F'.over X)
    (e' : G.over X ≅ G'.over X) : (F ⊗ G).over X ≅ (F' ⊗ G').over X :=
  overTensorIso F G X ≪≫
    (presheafToSheaf (J.over X) A).mapIso
      ((sheafToPresheaf _ A).mapIso e ⊗ᵢ (sheafToPresheaf _ A).mapIso e') ≪≫
    (overTensorIso F' G' X).symm

/-- **Tensor products of locally constant sheaves.** If `F` is locally constant with values in
`P` and `G` is locally constant with values in `Q`, then `F ⊗ G` is locally constant with values
in any `R` containing the tensor products `M ⊗ N` with `P M` and `Q N`. -/
theorem IsLocallyConstantIn.tensor {P Q R : ObjectProperty A}
    (hPQ : ∀ M N, P M → Q N → R (M ⊗ N)) {F G : Sheaf J A} (hF : F.IsLocallyConstantIn J P)
    (hG : G.IsLocallyConstantIn J Q) : (F ⊗ G).IsLocallyConstantIn J R := by
  rw [isLocallyConstantIn_iff] at hF hG ⊢
  refine fun X ↦ J.superset_covering ?_ (J.intersection_covering (hF X) (hG X))
  rintro Y f ⟨hf, hf'⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := (locallyConstantSieve_apply P F f).1 hf
  obtain ⟨N, hN, ⟨e'⟩⟩ := (locallyConstantSieve_apply Q G f).1 hf'
  exact (locallyConstantSieve_apply R (F ⊗ G) f).2 ⟨M ⊗ N, hPQ M N hM hN,
    ⟨overTensorIsoOfIso e e' ≪≫ (J.overPullback A Y).mapIso (constantSheafTensorIso J M N)⟩⟩

end LocallyBijective

end CategoryTheory.Sheaf
