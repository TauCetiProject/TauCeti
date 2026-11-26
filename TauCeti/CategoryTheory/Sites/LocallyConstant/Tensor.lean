/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Basic
public import TauCeti.CategoryTheory.Sites.CoverLifting

/-!
# Tensor products of locally constant sheaves

Let `J` be a Grothendieck topology on `C` and `A` a monoidal category for which sheafification is
compatible with tensor products (`(J.W (A := A)).IsMonoidal`), so that `Sheaf J A` carries the
monoidal structure `CategoryTheory.Sheaf.monoidalCategory`: the tensor product of two sheaves is
the sheafification of their sectionwise tensor product.

* `CategoryTheory.constantSheafTensorIso`: the tensor product of the constant sheaves on `M`
  and `N` is the constant sheaf on `M ⊗ N`.
* `CategoryTheory.Sheaf.overTensorIso`: the restriction of `F ⊗ G` to `Over X` is the
  sheafification of the sectionwise tensor product of the restrictions of `F` and `G`. Hence it
  only depends on the restrictions of `F` and `G` (`CategoryTheory.Sheaf.overTensorIsoOfIso`).
* `CategoryTheory.Sheaf.IsLocallyConstantIn.tensor`: the tensor product of a sheaf which is
  locally constant with values in `P` and one which is locally constant with values in `Q` is
  locally constant with values in any `R` containing the tensor products `M ⊗ N` with `P M`
  and `Q N`.

No monoidal structure on the sheaves on `Over X` is needed. The restriction results assume a
concrete category `A` in which the morphisms inverted by sheafification are the locally bijective
ones, on `C` and on each `Over X` (`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`),
so that restriction to `Over X` commutes with sheafification
(`CategoryTheory.Functor.sheafPushforwardContinuousPresheafToSheafIso`).

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe v u v' u'

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

variable (J) in
/-- The tensor product of two constant sheaves is the constant sheaf on the tensor product. -/
noncomputable def constantSheafTensorIso (M N : A) :
    (constantSheaf J A).obj M ⊗ (constantSheaf J A).obj N ≅ (constantSheaf J A).obj (M ⊗ N) :=
  Functor.Monoidal.μIso (presheafToSheaf J A) _ _ ≪≫
    (presheafToSheaf J A).mapIso (NatIso.ofComponents fun _ ↦ Iso.refl _)

end CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

section LocallyBijective

variable {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA] [J.WEqualsLocallyBijective A] [∀ X : C, HasWeakSheafify (J.over X) A]
  [∀ X : C, (J.over X).WEqualsLocallyBijective A]

include FA CA

/-- **Restriction of a tensor product.** The restriction of `F ⊗ G` to `Over X` is the
sheafification of the sectionwise tensor product of the restrictions of `F` and `G`. -/
noncomputable def overTensorIso (F G : Sheaf J A) (X : C) :
    (F ⊗ G).over X ≅ (presheafToSheaf (J.over X) A).obj ((F.over X).obj ⊗ (G.over X).obj) :=
  (J.overPullback A X).mapIso ((sheafificationIso F ⊗ᵢ sheafificationIso G) ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J A) _ _) ≪≫
    (Over.forget X).sheafPushforwardContinuousPresheafToSheafIso (J.over X) J (F.obj ⊗ G.obj) ≪≫
    (presheafToSheaf (J.over X) A).mapIso
      (Functor.Monoidal.μIso ((Functor.whiskeringLeft _ _ A).obj (Over.forget X).op)
        F.obj G.obj).symm

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
