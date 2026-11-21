/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Character
public import TauCeti.CategoryTheory.Monoidal.Grading.Classification
public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.Basic

/-!
# Groupoid characters of the universal grading groupoid and monoidal automorphisms

For a finite semisimple linear monoidal category `C` without assuming `𝟙_ C` is simple, a
`kˣ`-valued groupoid character of `universalGradingGroupoid C` is a functor
`universalGradingGroupoid C ⥤ SingleObj kˣ` (equipped with the pointwise abelian group structure
`CategoryTheory.SingleObj.functorCommGroup`).

Composing the universal comparison `universalGradingGroupoid.singleObjFunctorMulEquiv` with
`characterMonoidalAut` and `monoidalAutCharacterEquiv` identifies monoidal natural automorphisms of
the identity functor `Aut_⊗(𝟭_C)` with `universalGradingGroupoid C ⥤ SingleObj kˣ` over an
algebraically closed field `k` with finite-dimensional simple endomorphism spaces (Penneys,
Lemma 3.19(1)).

## Main declarations

* `TauCeti.groupoidCharacterMonoidalAut`: extends an `Rˣ`-valued functor on
  `universalGradingGroupoid C` to a monoidal natural automorphism of `𝟭 C`.
* `TauCeti.monoidalAutGroupoidCharacter`: extracts the `kˣ`-valued functor on
  `universalGradingGroupoid C` from a monoidal natural automorphism of `𝟭 C`.
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
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) :
    groupoidCharacterMonoidalAut R F =
      characterMonoidalAut R (universalGradingGroupoid.singleObjFunctorMulEquiv Rˣ F) :=
  (rfl)

/-- Precomposed with a morphism `s : S ⟶ X` out of a simple object `S`, the monoidal automorphism
associated to a groupoid character `F` scales `s` by `F.map (degreeOf S)`. -/
@[reassoc]
theorem comp_groupoidCharacterMonoidalAut_app
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) {S X : C} [Simple S] (s : S ⟶ X) :
    s ≫ (LaxMonoidalFunctor.forgetAut (𝟭 C) (groupoidCharacterMonoidalAut R F)).asIso.hom.app X =
      Units.val (F.map (universalGradingGroupoid.degreeOf S)) • s := by
  rw [groupoidCharacterMonoidalAut_eq_characterMonoidalAut, comp_characterMonoidalAut_app,
    universalGradingGroupoid.singleObjFunctorMulEquiv_apply_degree_classOf]

/-- The monoidal automorphism associated to a groupoid character `F` acts on each simple object `X`
as multiplication by `F.map (degreeOf X)`. -/
@[simp]
theorem groupoidCharacterMonoidalAut_app_of_simple
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) (X : C) [Simple X] :
    (LaxMonoidalFunctor.forgetAut (𝟭 C) (groupoidCharacterMonoidalAut R F)).asIso.hom.app X =
      Units.val (F.map (universalGradingGroupoid.degreeOf X)) • 𝟙 X := by
  rw [groupoidCharacterMonoidalAut_eq_characterMonoidalAut, characterMonoidalAut_app_of_simple,
    universalGradingGroupoid.singleObjFunctorMulEquiv_apply_degree_classOf]

end Semiring

section Field

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C]

/-- Over a field, distinct `kˣ`-valued characters of `universalGradingGroupoid C` induce distinct
monoidal automorphisms of the identity functor. -/
theorem groupoidCharacterMonoidalAut_injective :
    Function.Injective (groupoidCharacterMonoidalAut k (C := C)) :=
  (characterMonoidalAut_injective k).comp
    (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).injective

end Field

section Classification

variable (k : Type w) [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C]

/-- Extract the `kˣ`-valued character of `universalGradingGroupoid C` from a monoidal natural
automorphism of the identity functor. -/
def monoidalAutGroupoidCharacter :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm.toMonoidHom.comp
    (monoidalAutCharacter (hfin := hfin) k)

theorem monoidalAutGroupoidCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    Units.val ((monoidalAutGroupoidCharacter (hfin := hfin) k a).map
        (universalGradingGroupoid.degree S)) =
      endAlgEquivOfSimple k S.repr
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) := by
  simp only [monoidalAutGroupoidCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    universalGradingGroupoid.singleObjFunctorMulEquiv_symm_map_degree,
    monoidalAutCharacter_degree]

/-- Evaluating `monoidalAutGroupoidCharacter` on `degreeOf X` for a simple object `X` recovers the
component of the monoidal automorphism at `X`. -/
@[simp]
theorem monoidalAutGroupoidCharacter_degreeOf_smul_id (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    Units.val ((monoidalAutGroupoidCharacter (hfin := hfin) k a).map
        (universalGradingGroupoid.degreeOf X)) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X := by
  simp only [monoidalAutGroupoidCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    universalGradingGroupoid.singleObjFunctorMulEquiv_symm_map_degreeOf,
    monoidalAutCharacter_degree_smul_id]

/-- In a finite semisimple category, a monoidal automorphism of `𝟭 C` is uniquely determined by its
groupoid character on `universalGradingGroupoid C`. -/
theorem monoidalAutGroupoidCharacter_injective :
    Function.Injective (monoidalAutGroupoidCharacter (hfin := hfin) k (C := C)) :=
  (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm.injective.comp
    (monoidalAutCharacter_injective (hfin := hfin) k)

@[simp]
theorem monoidalAutGroupoidCharacter_groupoidCharacterMonoidalAut
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    monoidalAutGroupoidCharacter (hfin := hfin) k (groupoidCharacterMonoidalAut k F) = F := by
  simp [monoidalAutGroupoidCharacter, groupoidCharacterMonoidalAut]

@[simp]
theorem groupoidCharacterMonoidalAut_monoidalAutGroupoidCharacter
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    groupoidCharacterMonoidalAut k (monoidalAutGroupoidCharacter (hfin := hfin) k a) = a := by
  simp [monoidalAutGroupoidCharacter, groupoidCharacterMonoidalAut]

/-- Monoidal natural automorphisms of `𝟭 C` are isomorphic as a group to `kˣ`-valued characters of
`universalGradingGroupoid C` (Penneys, Lemma 3.19(1)). Neither simplicity of `𝟙_ C`, rigidity,
finiteness of `SimpleClasses C`, nor characteristic zero is required. -/
def monoidalAutGroupoidCharacterEquiv :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  (monoidalAutCharacterEquiv (hfin := hfin) k).trans
    (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm

@[simp]
theorem monoidalAutGroupoidCharacterEquiv_apply (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutGroupoidCharacterEquiv (hfin := hfin) k a =
      monoidalAutGroupoidCharacter (hfin := hfin) k a := by
  simp [monoidalAutGroupoidCharacterEquiv, monoidalAutGroupoidCharacter]

@[simp]
theorem monoidalAutGroupoidCharacterEquiv_symm_apply
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    (monoidalAutGroupoidCharacterEquiv (hfin := hfin) k).symm F =
      groupoidCharacterMonoidalAut k F := by
  simp [monoidalAutGroupoidCharacterEquiv, groupoidCharacterMonoidalAut]

end Classification

end TauCeti
