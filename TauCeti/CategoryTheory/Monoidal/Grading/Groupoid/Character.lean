/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Classification
public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.SingleObj

/-!
# Groupoid characters of the universal grading groupoid and monoidal automorphisms

For a finite semisimple linear monoidal category `C` without assuming `𝟙_ C` is simple, a
`kˣ`-valued groupoid character of `universalGradingGroupoid C` is a functor
`universalGradingGroupoid C ⥤ SingleObj kˣ` (`CategoryTheory.SingleObj.functorCommGroup`).

Composing `universalGradingGroupoid.singleObjFunctorMulEquiv` with `characterMonoidalAut` and
`monoidalAutCharacterEquiv` identifies `Aut (LaxMonoidalFunctor.of (𝟭 C))` with
`universalGradingGroupoid C ⥤ SingleObj kˣ` whenever `TauCeti.HasScalarSimpleEnd k C` holds
(Penneys, Lemma 3.19(1)).

## Main declarations

* `TauCeti.groupoidCharacterMonoidalAut`: extends an `Rˣ`-valued character to `Aut_⊗(𝟭 C)`.
* `TauCeti.monoidalAutGroupoidCharacter`: extracts the `kˣ`-valued character from `Aut_⊗(𝟭 C)`.
* `TauCeti.monoidalAutGroupoidCharacterEquiv`: group isomorphism
  `Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroupoid C ⥤ SingleObj kˣ)`.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §3.3, Lemma 3.19
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace TauCeti

section Semiring

variable (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C]

/-- Extend an `Rˣ`-valued character of `universalGradingGroupoid C` to a monoidal natural
automorphism of the identity functor `𝟭 C`. -/
def groupoidCharacterMonoidalAut :
    (universalGradingGroupoid C ⥤ SingleObj Rˣ) →* Aut (LaxMonoidalFunctor.of (𝟭 C)) :=
  (characterMonoidalAut R).comp
    (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) Rˣ).toMonoidHom

variable {R}

theorem groupoidCharacterMonoidalAut_eq_characterMonoidalAut
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) : groupoidCharacterMonoidalAut R F =
      characterMonoidalAut R (universalGradingGroupoid.singleObjFunctorMulEquiv Rˣ F) := (rfl)

/-- Precomposed with a morphism `s : S ⟶ X` out of a simple object `S`, the monoidal automorphism
associated to a groupoid character `F` scales `s` by `F.map (degreeOf S)`. -/
@[reassoc] theorem comp_groupoidCharacterMonoidalAut_app
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) {S X : C} [Simple S] (s : S ⟶ X) :
    s ≫ (LaxMonoidalFunctor.forgetAut (𝟭 C) (groupoidCharacterMonoidalAut R F)).asIso.hom.app X =
      Units.val (F.map (universalGradingGroupoid.degreeOf S)) • s := by
  rw [groupoidCharacterMonoidalAut_eq_characterMonoidalAut, comp_characterMonoidalAut_app,
    universalGradingGroupoid.singleObjFunctorMulEquiv_apply_degree_classOf]

/-- The monoidal automorphism associated to a groupoid character `F` acts on each simple object `X`
as multiplication by `F.map (degreeOf X)`. -/
@[simp] theorem groupoidCharacterMonoidalAut_app_of_simple
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) (X : C) [Simple X] :
    (LaxMonoidalFunctor.forgetAut (𝟭 C) (groupoidCharacterMonoidalAut R F)).asIso.hom.app X =
      Units.val (F.map (universalGradingGroupoid.degreeOf X)) • 𝟙 X := by
  rw [groupoidCharacterMonoidalAut_eq_characterMonoidalAut, characterMonoidalAut_app_of_simple,
    universalGradingGroupoid.singleObjFunctorMulEquiv_apply_degree_classOf]

/-- If units of `R` act faithfully by scalar multiplication on the identity of every simple
representative, distinct `Rˣ`-valued characters of `universalGradingGroupoid C` induce distinct
monoidal automorphisms of the identity functor. -/
theorem groupoidCharacterMonoidalAut_injective_of_smul_injective (R) [CommSemiring R]
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [Linear R C] [MonoidalLinear R C] [IsFiniteSemisimpleCategory C]
    (hinj : ∀ S : SimpleClasses C, Function.Injective (fun u : Rˣ ↦ (u : R) • 𝟙 S.repr)) :
    Function.Injective (groupoidCharacterMonoidalAut R (C := C)) :=
  (characterMonoidalAut_injective_of_smul_injective R hinj).comp
    (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) Rˣ).injective

end Semiring

/-- Over a field, distinct `kˣ`-valued characters of `universalGradingGroupoid C` induce distinct
monoidal automorphisms of the identity functor. -/
theorem groupoidCharacterMonoidalAut_injective (k : Type w) [Field k]
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [Linear k C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C] :
    Function.Injective (groupoidCharacterMonoidalAut k (C := C)) :=
  groupoidCharacterMonoidalAut_injective_of_smul_injective k fun S _ _ h ↦
    Units.ext (smul_left_injective k (CategoryTheory.id_ne_zero S.repr) h)

section Classification

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C]
  [HasScalarSimpleEnd k C]

/-- Extract the `kˣ`-valued character of `universalGradingGroupoid C` from a monoidal natural
automorphism of the identity functor when simple objects have scalar endomorphisms. -/
def monoidalAutGroupoidCharacter :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm.toMonoidHom.comp
    (monoidalAutCharacter k)

/-- The structure map sends the value of `monoidalAutGroupoidCharacter` at `degree S` to the
component of the automorphism at `S.repr`. -/
theorem algebraMap_monoidalAutGroupoidCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) : algebraMap k (End S.repr)
      (Units.val ((monoidalAutGroupoidCharacter k a).map (universalGradingGroupoid.degree S))) =
      End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) := by
  simp [monoidalAutGroupoidCharacter, algebraMap_monoidalAutCharacter_degree]

/-- The value of the groupoid character on `degree S` is the scalar of the component of the
monoidal automorphism at `S.repr`. -/
theorem monoidalAutGroupoidCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    Units.val ((monoidalAutGroupoidCharacter k a).map (universalGradingGroupoid.degree S)) =
      endAlgEquivOfSurjective k S.repr (HasScalarSimpleEnd.surjective_algebraMap S.repr)
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) := by
  simp [monoidalAutGroupoidCharacter, monoidalAutCharacter_degree]

/-- Evaluating `monoidalAutGroupoidCharacter` on `degreeOf X` for a simple object `X` recovers the
component of the monoidal automorphism at `X`. -/
@[simp] theorem monoidalAutGroupoidCharacter_degreeOf_smul_id
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    Units.val ((monoidalAutGroupoidCharacter k a).map (universalGradingGroupoid.degreeOf X)) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X := by
  simp [monoidalAutGroupoidCharacter]

/-- In a finite semisimple category where simple objects have scalar endomorphisms, a monoidal
automorphism of `𝟭 C` is uniquely determined by its groupoid character on
`universalGradingGroupoid C`. -/
theorem monoidalAutGroupoidCharacter_injective :
    Function.Injective (monoidalAutGroupoidCharacter k (C := C)) :=
  (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm.injective.comp
    (monoidalAutCharacter_injective k)

@[simp] theorem monoidalAutGroupoidCharacter_groupoidCharacterMonoidalAut
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    monoidalAutGroupoidCharacter k (groupoidCharacterMonoidalAut k F) = F := by
  simp [monoidalAutGroupoidCharacter, groupoidCharacterMonoidalAut]
@[simp] theorem groupoidCharacterMonoidalAut_monoidalAutGroupoidCharacter
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    groupoidCharacterMonoidalAut k (monoidalAutGroupoidCharacter k a) = a := by
  simp [monoidalAutGroupoidCharacter, groupoidCharacterMonoidalAut]

/-- Monoidal natural automorphisms of `𝟭 C` are isomorphic as a group to `kˣ`-valued characters of
`universalGradingGroupoid C` whenever simple objects have scalar endomorphisms (Penneys,
Lemma 3.19(1)). Neither simplicity of `𝟙_ C`, rigidity, finiteness of `SimpleClasses C`, nor
characteristic zero is required. -/
def monoidalAutGroupoidCharacterEquiv :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  (monoidalAutCharacterEquiv k).trans
    (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm

@[simp] theorem monoidalAutGroupoidCharacterEquiv_apply (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutGroupoidCharacterEquiv k a = monoidalAutGroupoidCharacter k a := by
  simp [monoidalAutGroupoidCharacterEquiv, monoidalAutGroupoidCharacter]
@[simp] theorem monoidalAutGroupoidCharacterEquiv_symm_apply
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    (monoidalAutGroupoidCharacterEquiv k).symm F = groupoidCharacterMonoidalAut k F := by
  simp [monoidalAutGroupoidCharacterEquiv, groupoidCharacterMonoidalAut]

end Classification

end TauCeti
