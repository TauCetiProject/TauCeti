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
`universalGradingGroupoid C ⥤ SingleObj kˣ` over an algebraically closed field `k` with
finite-dimensional simple endomorphism spaces (Penneys, Lemma 3.19(1)).

## Main declarations

* `TauCeti.groupoidCharacterMonoidalAut`: extends an `Rˣ`-valued character to `Aut_⊗(𝟭 C)`.
* `TauCeti.monoidalAutGroupoidCharacter`, `TauCeti.monoidalAutGroupoidCharacterOfSurjective`:
  extracts the `kˣ`-valued character from `Aut_⊗(𝟭 C)`.
* `TauCeti.monoidalAutGroupoidCharacterEquiv`,
  `TauCeti.monoidalAutGroupoidCharacterEquivOfSurjective`: group isomorphism
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

section ClassificationGeneral

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C]
  (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))

/-- Extract the `kˣ`-valued character of `universalGradingGroupoid C` from a monoidal natural
automorphism of the identity functor when every simple object has scalar endomorphisms. -/
def monoidalAutGroupoidCharacterOfSurjective :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm.toMonoidHom.comp
    (monoidalAutCharacterOfSurjective k hscalar)

/-- `monoidalAutGroupoidCharacterOfSurjective` sends `a` to the functor corresponding to
`monoidalAutCharacterOfSurjective k hscalar a`. -/
theorem monoidalAutGroupoidCharacterOfSurjective_eq
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutGroupoidCharacterOfSurjective k hscalar a =
      (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm
        (monoidalAutCharacterOfSurjective k hscalar a) :=
  (rfl)

/-- The structure map sends the value of `monoidalAutGroupoidCharacterOfSurjective` at `degree S`
to the component of the automorphism at `S.repr`. -/
theorem algebraMap_monoidalAutGroupoidCharacterOfSurjective_degree
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (S : SimpleClasses C) :
    algebraMap k (End S.repr)
        (Units.val ((monoidalAutGroupoidCharacterOfSurjective k hscalar a).map
          (universalGradingGroupoid.degree S))) =
      End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) := by
  apply End.ext
  rw [End.algebraMap_asHom]
  simpa only [SimpleClasses.classOf_repr, monoidalAutGroupoidCharacterOfSurjective,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    universalGradingGroupoid.singleObjFunctorMulEquiv_symm_map_degree] using
    monoidalAutCharacterOfSurjective_degree_smul_id k hscalar a S.repr

/-- Evaluating `monoidalAutGroupoidCharacterOfSurjective` on `degreeOf X` for a simple object `X`
recovers the component of the monoidal automorphism at `X`. -/
@[simp] theorem monoidalAutGroupoidCharacterOfSurjective_degreeOf_smul_id
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    Units.val ((monoidalAutGroupoidCharacterOfSurjective k hscalar a).map
        (universalGradingGroupoid.degreeOf X)) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X := by
  simp [monoidalAutGroupoidCharacterOfSurjective]

/-- In a finite semisimple category where simple objects have scalar endomorphisms, a monoidal
automorphism of `𝟭 C` is uniquely determined by its groupoid character on
`universalGradingGroupoid C`. -/
theorem monoidalAutGroupoidCharacterOfSurjective_injective :
    Function.Injective (monoidalAutGroupoidCharacterOfSurjective k hscalar (C := C)) :=
  (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm.injective.comp
    (monoidalAutCharacterOfSurjective_injective k hscalar)

/-- Extracting the groupoid character of the automorphism extended from a groupoid character
recovers that groupoid character. -/
@[simp] theorem monoidalAutGroupoidCharacterOfSurjective_groupoidCharacterMonoidalAut
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    monoidalAutGroupoidCharacterOfSurjective k hscalar (groupoidCharacterMonoidalAut k F) = F := by
  simp [monoidalAutGroupoidCharacterOfSurjective, groupoidCharacterMonoidalAut]

/-- Extending the groupoid character extracted from an automorphism recovers that automorphism. -/
@[simp] theorem groupoidCharacterMonoidalAut_monoidalAutGroupoidCharacterOfSurjective
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    groupoidCharacterMonoidalAut k (monoidalAutGroupoidCharacterOfSurjective k hscalar a) = a := by
  simp [monoidalAutGroupoidCharacterOfSurjective, groupoidCharacterMonoidalAut]

/-- When every simple object has scalar endomorphisms over a field `k`, monoidal natural
automorphisms of `𝟭 C` are isomorphic as a group to `kˣ`-valued characters of
`universalGradingGroupoid C`. -/
def monoidalAutGroupoidCharacterEquivOfSurjective :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  (monoidalAutCharacterEquivOfSurjective k hscalar).trans
    (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm

/-- The groupoid character classification sends an automorphism to
`monoidalAutGroupoidCharacterOfSurjective`. -/
@[simp] theorem monoidalAutGroupoidCharacterEquivOfSurjective_apply
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutGroupoidCharacterEquivOfSurjective k hscalar a =
      monoidalAutGroupoidCharacterOfSurjective k hscalar a := by
  simp [monoidalAutGroupoidCharacterEquivOfSurjective, monoidalAutGroupoidCharacterOfSurjective]

/-- The inverse groupoid character classification extends a character to a monoidal
automorphism. -/
@[simp] theorem monoidalAutGroupoidCharacterEquivOfSurjective_symm_apply
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    (monoidalAutGroupoidCharacterEquivOfSurjective k hscalar).symm F =
      groupoidCharacterMonoidalAut k F := by
  simp [monoidalAutGroupoidCharacterEquivOfSurjective, groupoidCharacterMonoidalAut]

end ClassificationGeneral

section Classification

variable (k : Type w) [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C]

/-- Extract the `kˣ`-valued character of `universalGradingGroupoid C` from a monoidal natural
automorphism of the identity functor. -/
def monoidalAutGroupoidCharacter :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  monoidalAutGroupoidCharacterOfSurjective k
    fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective

/-- `monoidalAutGroupoidCharacter` sends `a` to the functor corresponding to
`monoidalAutCharacter (hfin := hfin) k a`. -/
theorem monoidalAutGroupoidCharacter_eq (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutGroupoidCharacter (hfin := hfin) k a =
      (universalGradingGroupoid.singleObjFunctorMulEquiv (C := C) kˣ).symm
        (monoidalAutCharacter (hfin := hfin) k a) := by
  rw [monoidalAutCharacter_eq]
  rfl

/-- The structure map sends the value of `monoidalAutGroupoidCharacter` at `degree S` to the
component of the automorphism at `S.repr`. -/
theorem algebraMap_monoidalAutGroupoidCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) : algebraMap k (End S.repr)
      (Units.val ((monoidalAutGroupoidCharacter (hfin := hfin) k a).map
        (universalGradingGroupoid.degree S))) =
      End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) :=
  algebraMap_monoidalAutGroupoidCharacterOfSurjective_degree k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) a S

/-- The value of the groupoid character on `degree S` is the scalar of the component of the
monoidal automorphism at `S.repr`. -/
theorem monoidalAutGroupoidCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    Units.val ((monoidalAutGroupoidCharacter (hfin := hfin) k a).map
        (universalGradingGroupoid.degree S)) =
      endAlgEquivOfSimple k S.repr
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) := by
  rw [monoidalAutGroupoidCharacter, monoidalAutGroupoidCharacterOfSurjective]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    universalGradingGroupoid.singleObjFunctorMulEquiv_symm_map_degree]
  rw [← monoidalAutCharacter_eq (hfin := hfin), monoidalAutCharacter_degree]

/-- Evaluating `monoidalAutGroupoidCharacter` on `degreeOf X` for a simple object `X` recovers the
component of the monoidal automorphism at `X`. -/
@[simp] theorem monoidalAutGroupoidCharacter_degreeOf_smul_id
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    Units.val ((monoidalAutGroupoidCharacter (hfin := hfin) k a).map
        (universalGradingGroupoid.degreeOf X)) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X :=
  monoidalAutGroupoidCharacterOfSurjective_degreeOf_smul_id k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) a X

/-- In a finite semisimple category, a monoidal automorphism of `𝟭 C` is uniquely determined by its
groupoid character on `universalGradingGroupoid C`. -/
theorem monoidalAutGroupoidCharacter_injective :
    Function.Injective (monoidalAutGroupoidCharacter (hfin := hfin) k (C := C)) :=
  monoidalAutGroupoidCharacterOfSurjective_injective k
    fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective

/-- Extracting the groupoid character of `groupoidCharacterMonoidalAut k F` recovers `F`. -/
@[simp] theorem monoidalAutGroupoidCharacter_groupoidCharacterMonoidalAut
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    monoidalAutGroupoidCharacter (hfin := hfin) k (groupoidCharacterMonoidalAut k F) = F :=
  monoidalAutGroupoidCharacterOfSurjective_groupoidCharacterMonoidalAut k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) F

/-- Extending the groupoid character of `a` recovers `a`. -/
@[simp] theorem groupoidCharacterMonoidalAut_monoidalAutGroupoidCharacter
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    groupoidCharacterMonoidalAut k (monoidalAutGroupoidCharacter (hfin := hfin) k a) = a :=
  groupoidCharacterMonoidalAut_monoidalAutGroupoidCharacterOfSurjective k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) a

/-- Monoidal natural automorphisms of `𝟭 C` are isomorphic as a group to `kˣ`-valued characters of
`universalGradingGroupoid C` (Penneys, Lemma 3.19(1)). Neither simplicity of `𝟙_ C`, rigidity,
finiteness of `SimpleClasses C`, nor characteristic zero is required. -/
def monoidalAutGroupoidCharacterEquiv :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  monoidalAutGroupoidCharacterEquivOfSurjective k
    fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective

/-- `monoidalAutGroupoidCharacterEquiv` sends `a` to `monoidalAutGroupoidCharacter`. -/
@[simp] theorem monoidalAutGroupoidCharacterEquiv_apply (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutGroupoidCharacterEquiv (hfin := hfin) k a =
      monoidalAutGroupoidCharacter (hfin := hfin) k a :=
  monoidalAutGroupoidCharacterEquivOfSurjective_apply k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) a

/-- The inverse of `monoidalAutGroupoidCharacterEquiv` sends `F` to
`groupoidCharacterMonoidalAut`. -/
@[simp] theorem monoidalAutGroupoidCharacterEquiv_symm_apply
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    (monoidalAutGroupoidCharacterEquiv (hfin := hfin) k).symm F =
      groupoidCharacterMonoidalAut k F :=
  monoidalAutGroupoidCharacterEquivOfSurjective_symm_apply k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) F

end Classification

end TauCeti
