/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Center.OfHom
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Semisimple.DualBasis

/-!
# The induction functor to the Drinfeld centre of a fusion category

Let `C` be a rigid monoidal category which is `k`-linear, abelian and finite semisimple over an
algebraically closed field `k`, with finite-dimensional morphism spaces and finitely many
isomorphism classes of simple objects. For each simple class `S` fix its representative, again
written `S`. The **induction** of an object `X` of `C` is

`I X = ⨁ S, S ⊗ X ⊗ Sᘁ`,

with the canonical half-braiding `I X ⊗ U ≅ U ⊗ I X`. Its component from the summand of `S` to
the summand of `T` is

`∑ i, b i ⊗ X ⊗ (b.homDual i)^∨ : S ⊗ X ⊗ Sᘁ ⊗ U ⟶ U ⊗ T ⊗ X ⊗ Tᘁ`,

where `b` is any basis of `S ⟶ U ⊗ T`, `b.homDual` is the dual basis of `U ⊗ T ⟶ S` under the
composition pairing, and `f^∨ : Sᘁ ⊗ U ⟶ Tᘁ` is the morphism corresponding to `f : U ⊗ T ⟶ S` by
Frobenius reciprocity on both sides (`TauCeti.dualMate`). Each summand of this sum is
`TauCeti.CenterInduction.term X (b.homDual i) (b i)`, and the sum does not depend on `b`, because
the canonical element `∑ i, b.homDual i ⊗ b i` does not (`Module.Basis.sum_homDual_eq`).

Naturality of these components in `U` is the naturality of the canonical element in its target
(`Module.Basis.sum_homDual_comp`). Monoidality in `U` holds because the composites of a basis of
`S ⟶ U ⊗ T` with bases of `T ⟶ V ⊗ R`, over all simple classes `T`, compute the canonical
element of `S ⟶ U ⊗ V ⊗ R` (`TauCeti.sum_homDual_eq_sum_map_homDual`), and the components at the
unit object are the unitors, since `S ⟶ 𝟙_ C ⊗ T` vanishes for `S ≠ T` and is spanned by the
unitor for `S = T`. A natural, monoidal and unital family is invertible in a rigid category
(`CategoryTheory.HalfBraiding.ofHom`), so this is a half-braiding. Morphisms `X ⟶ Y` act on each
summand and commute with the half-braidings, which makes induction a functor
`TauCeti.centerInduction k C : C ⥤ Center C`.

The induction functor is both left and right adjoint to the forgetful functor `Center C ⥤ C`
(Etingof–Nikshych–Ostrik, §2), which is how the centre of a fusion category is compared with the
category itself, for instance to show that it is semisimple; this file constructs the functor.

## Main declarations

* `TauCeti.CenterInduction.term`: the morphism `S ⊗ X ⊗ Sᘁ ⊗ U ⟶ V ⊗ T ⊗ X ⊗ Tᘁ` built from
  `f : U ⊗ T ⟶ S` and `e : S ⟶ V ⊗ T`, with its naturality, its composition law
  `TauCeti.CenterInduction.term_monoidal`, and its value
  `TauCeti.CenterInduction.term_leftUnitor` at the unitors;
* `TauCeti.CenterInduction.component`: the components of the half-braiding, computed in any
  basis by `TauCeti.CenterInduction.component_eq`;
* `TauCeti.CenterInduction.halfBraidingHom` and `TauCeti.CenterInduction.halfBraiding`: the
  canonical half-braiding of `⨁ S, S ⊗ X ⊗ Sᘁ`, with components
  `TauCeti.CenterInduction.ι_whiskerRight_halfBraidingHom_whiskerLeft_π`;
* `TauCeti.centerInduction`: the induction functor `C ⥤ Center C`, with
  `TauCeti.centerInductionObjIso` identifying its underlying objects with `⨁ S, S ⊗ X ⊗ Sᘁ`
  naturally in `X`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.2
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Module

universe w v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti

namespace CenterInduction

section Term

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (X : C)

/-- The building block of the canonical half-braiding of `⨁ S, S ⊗ X ⊗ Sᘁ`: given
`f : U ⊗ T ⟶ S` and `e : S ⟶ V ⊗ T`, the morphism `S ⊗ X ⊗ Sᘁ ⊗ U ⟶ V ⊗ T ⊗ X ⊗ Tᘁ` which applies
`e` to `S` and the morphism `Sᘁ ⊗ U ⟶ Tᘁ` corresponding to `f` by Frobenius reciprocity to
`Sᘁ ⊗ U`. -/
def term {S T U V : C} [HasRightDual S] [HasRightDual T] (f : U ⊗ T ⟶ S) (e : S ⟶ V ⊗ T) :
    (S ⊗ X ⊗ Sᘁ) ⊗ U ⟶ V ⊗ T ⊗ X ⊗ Tᘁ :=
  𝟙 _ ⊗≫ e ▷ (X ⊗ Sᘁ ⊗ U) ⊗≫ (V ⊗ T ⊗ X) ◁ dualMate f ⊗≫ 𝟙 _

variable {X}

/-- Postcomposing `term X f e` with a morphism `g : V ⟶ V'` postcomposes `e` with `g ▷ T`. -/
theorem term_comp_whiskerRight {S T U V V' : C} [HasRightDual S] [HasRightDual T]
    (f : U ⊗ T ⟶ S) (e : S ⟶ V ⊗ T) (g : V ⟶ V') :
    term X f e ≫ g ▷ (T ⊗ X ⊗ Tᘁ) = term X f (e ≫ g ▷ T) := by
  calc
    _ = 𝟙 _ ⊗≫ e ▷ (X ⊗ Sᘁ ⊗ U) ⊗≫
          ((V ⊗ T ⊗ X) ◁ dualMate f ≫ (g ▷ (T ⊗ X)) ▷ Tᘁ) ⊗≫ 𝟙 _ := by
      rw [term]; monoidal
    _ = _ := by
      rw [whisker_exchange, term]; monoidal

/-- Precomposing `term X f e` with a morphism `g : U ⟶ U'` precomposes `f` with `g ▷ T`. -/
theorem whiskerLeft_comp_term {S T U U' V : C} [HasRightDual S] [HasRightDual T]
    (g : U ⟶ U') (f : U' ⊗ T ⟶ S) (e : S ⟶ V ⊗ T) :
    (S ⊗ X ⊗ Sᘁ) ◁ g ≫ term X f e = term X (g ▷ T ≫ f) e := by
  calc
    _ = 𝟙 _ ⊗≫ (S ◁ (X ⊗ Sᘁ) ◁ g ≫ e ▷ ((X ⊗ Sᘁ) ⊗ U')) ⊗≫
          (V ⊗ T ⊗ X) ◁ dualMate f ⊗≫ 𝟙 _ := by
      rw [term]; monoidal
    _ = 𝟙 _ ⊗≫ e ▷ ((X ⊗ Sᘁ) ⊗ U) ⊗≫ (V ⊗ T ⊗ X) ◁ ((Sᘁ : C) ◁ g ≫ dualMate f) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [whiskerLeft_comp_dualMate, term]; monoidal

/-- `term` is natural in the middle object: a morphism `h : X ⟶ Y` acting on `S ⊗ X ⊗ Sᘁ` before
and on `T ⊗ X ⊗ Tᘁ` after give the same result. -/
theorem whiskerRight_comp_term {S T U V Y : C} [HasRightDual S] [HasRightDual T] (h : X ⟶ Y)
    (f : U ⊗ T ⟶ S) (e : S ⟶ V ⊗ T) :
    (S ◁ h ▷ Sᘁ) ▷ U ≫ term Y f e = term X f e ≫ V ◁ T ◁ h ▷ Tᘁ := by
  calc
    _ = 𝟙 _ ⊗≫ (S ◁ h ▷ ((Sᘁ : C) ⊗ U) ≫ e ▷ (Y ⊗ Sᘁ ⊗ U)) ⊗≫ (V ⊗ T ⊗ Y) ◁ dualMate f ⊗≫
          𝟙 _ := by
      rw [term]; monoidal
    _ = 𝟙 _ ⊗≫ e ▷ (X ⊗ Sᘁ ⊗ U) ⊗≫
          (((V ⊗ T) ◁ h) ▷ ((Sᘁ : C) ⊗ U) ≫ ((V ⊗ T) ⊗ Y) ◁ dualMate f) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [← whisker_exchange, term]; monoidal

/-- The composition law of `term`: applying `term X f e` and then `term X f' e'` composes the
morphisms `e` and `e'` out of the simple objects, and the morphisms `f` and `f'` into them. -/
theorem term_monoidal {S T R U U' V V' : C} [HasRightDual S] [HasRightDual T] [HasRightDual R]
    (f : U ⊗ T ⟶ S) (e : S ⟶ U' ⊗ T) (f' : V ⊗ R ⟶ T) (e' : T ⟶ V' ⊗ R) :
    (α_ _ _ _).inv ≫ term X f e ▷ V ≫ (α_ _ _ _).hom ≫ U' ◁ term X f' e' ≫ (α_ _ _ _).inv =
      term X ((α_ _ _ _).hom ≫ U ◁ f' ≫ f) (e ≫ U' ◁ e' ≫ (α_ _ _ _).inv) := by
  calc
    _ = 𝟙 _ ⊗≫ e ▷ (X ⊗ Sᘁ ⊗ U ⊗ V) ⊗≫
          (((U' ⊗ T) ⊗ X) ◁ (dualMate f ▷ V) ≫ ((U' ◁ e') ▷ X) ▷ ((Tᘁ : C) ⊗ V)) ⊗≫
          (U' ⊗ V' ⊗ R ⊗ X) ◁ dualMate f' ⊗≫ 𝟙 _ := by
      simp only [term]; monoidal
    _ = 𝟙 _ ⊗≫ e ▷ (X ⊗ Sᘁ ⊗ U ⊗ V) ⊗≫ ((U' ◁ e') ▷ X) ▷ (((Sᘁ : C) ⊗ U) ⊗ V) ⊗≫
          (U' ⊗ V' ⊗ R ⊗ X) ◁ ((α_ _ _ _).inv ≫ dualMate f ▷ V ≫ dualMate f') ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [dualMate_tensor, term]; monoidal

/-- At the unitors of `S`, `term` is the composite of the unitors. -/
theorem term_leftUnitor (S : C) [HasRightDual S] :
    term X (λ_ S).hom (λ_ S).inv = (ρ_ _).hom ≫ (λ_ _).inv := by
  rw [term, dualMate_leftUnitor]; monoidal

variable (k : Type w) [CommSemiring k] [Preadditive C] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C]

variable (X) in
/-- `term X f e` is `k`-bilinear in `f` and `e`. -/
def termₗ {S T U V : C} [HasRightDual S] [HasRightDual T] :
    (U ⊗ T ⟶ S) →ₗ[k] (S ⟶ V ⊗ T) →ₗ[k] ((S ⊗ X ⊗ Sᘁ) ⊗ U ⟶ V ⊗ T ⊗ X ⊗ Tᘁ) :=
  LinearMap.mk₂ k (term X)
    (fun _ _ _ ↦ by simp [term, dualMate_add, monoidalComp])
    (fun _ _ _ ↦ by simp [term, dualMate_smul, monoidalComp])
    (fun _ _ _ ↦ by simp [term, monoidalComp])
    (fun _ _ _ ↦ by simp [term, monoidalComp])

/-- `CenterInduction.termₗ` evaluates to `CenterInduction.term`. -/
@[simp]
theorem termₗ_apply {S T U V : C} [HasRightDual S] [HasRightDual T] (f : U ⊗ T ⟶ S)
    (e : S ⟶ V ⊗ T) : termₗ X k f e = term X f e :=
  (rfl)

end Term

section Component

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
  [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- The component at `U` of the canonical half-braiding of `⨁ S, S ⊗ X ⊗ Sᘁ`, from the summand of
the simple class `S` to that of the simple class `T`: the sum of `term X (b.homDual i) (b i)` over
the basis `b = Module.finBasis k (S ⟶ U ⊗ T)`. By `CenterInduction.component_eq` any basis of
`S ⟶ U ⊗ T` gives the same sum. -/
def component (X : C) (S T : SimpleClasses C) (U : C) :
    (S.repr ⊗ X ⊗ S.reprᘁ) ⊗ U ⟶ U ⊗ T.repr ⊗ X ⊗ T.reprᘁ :=
  ∑ i, term X ((finBasis k (S.repr ⟶ U ⊗ T.repr)).homDual i) (finBasis k (S.repr ⟶ U ⊗ T.repr) i)

variable {k}

/-- The component of the canonical half-braiding, computed in an arbitrary basis `b` of
`S ⟶ U ⊗ T`. -/
theorem component_eq {X : C} {S T : SimpleClasses C} {U : C} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι k (S.repr ⟶ U ⊗ T.repr)) :
    component k X S T U = ∑ i, term X (b.homDual i) (b i) := by
  simpa [component] using Basis.sum_homDual_eq (finBasis k (S.repr ⟶ U ⊗ T.repr)) b (termₗ X k)

variable (k)

/-- The components of the canonical half-braiding are natural in `U`. -/
theorem whiskerLeft_comp_component (X : C) (S T : SimpleClasses C) {U U' : C} (g : U ⟶ U') :
    (S.repr ⊗ X ⊗ S.reprᘁ) ◁ g ≫ component k X S T U' =
      component k X S T U ≫ g ▷ (T.repr ⊗ X ⊗ T.reprᘁ) := by
  simp only [component, Preadditive.comp_sum, Preadditive.sum_comp, whiskerLeft_comp_term,
    term_comp_whiskerRight]
  simpa using (Basis.sum_homDual_comp (finBasis k (S.repr ⟶ U ⊗ T.repr))
    (finBasis k (S.repr ⟶ U' ⊗ T.repr)) (g ▷ T.repr) (termₗ X k)).symm

omit [MonoidalPreadditive C] [MonoidalLinear k C] in
/-- The components of the canonical half-braiding are natural in `X`. -/
theorem whiskerRight_comp_component {X Y : C} (h : X ⟶ Y) (S T : SimpleClasses C) (U : C) :
    (S.repr ◁ h ▷ S.reprᘁ) ▷ U ≫ component k Y S T U =
      component k X S T U ≫ U ◁ T.repr ◁ h ▷ T.reprᘁ := by
  simp only [component, Preadditive.comp_sum, Preadditive.sum_comp, whiskerRight_comp_term]

/-- The components of the canonical half-braiding are monoidal in `U`: the component at `U ⊗ V`
is the sum over the simple classes `T` of the composites of the components from `S` to `T` at
`U` and from `T` to `R` at `V`. -/
theorem component_tensor [Fintype (SimpleClasses C)] (X : C) (S R : SimpleClasses C) (U V : C) :
    component k X S R (U ⊗ V) =
      ∑ T, (α_ _ _ _).inv ≫ component k X S T U ▷ V ≫ (α_ _ _ _).hom ≫
        U ◁ component k X T R V ≫ (α_ _ _ _).inv := by
  classical
  let a := fun T : SimpleClasses C ↦ finBasis k (S.repr ⟶ U ⊗ T.repr)
  let b := fun T : SimpleClasses C ↦ finBasis k (T.repr ⟶ V ⊗ R.repr)
  let c := finBasis k (S.repr ⟶ (U ⊗ V) ⊗ R.repr)
  let c' := finBasis k (S.repr ⟶ U ⊗ V ⊗ R.repr)
  -- Move the associator from the basis of `S ⟶ (U ⊗ V) ⊗ R` to that of `S ⟶ U ⊗ V ⊗ R`.
  have h₁ := c.sum_homDual_comp c' (α_ U V R.repr).hom
    ((termₗ X k).compl₂ (Linear.rightComp k S.repr (α_ U V R.repr).inv))
  -- Compute the canonical element of `S ⟶ U ⊗ (V ⊗ R)` through the simple summands of `V ⊗ R`.
  have h₂ := sum_homDual_eq_sum_map_homDual (tensorLeft U) (V ⊗ R.repr) S.repr c' b a
    (((termₗ X k).comp (Linear.leftComp k S.repr (α_ U V R.repr).hom)).compl₂
      (Linear.rightComp k S.repr (α_ U V R.repr).inv))
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Linear.leftComp_apply,
    Linear.rightComp_apply, termₗ_apply, curriedTensor_obj_map, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] at h₁ h₂
  calc
    _ = ∑ i, term X (c.homDual i) (c i) := (rfl)
    _ = ∑ T, ∑ l, ∑ j, term X ((α_ _ _ _).hom ≫ U ◁ (b T).homDual l ≫ (a T).homDual j)
          (a T j ≫ U ◁ b T l ≫ (α_ _ _ _).inv) := by
      rw [h₁, h₂]
    _ = _ := by
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      rw [component_eq (a T), component_eq (b T)]
      simp only [sum_whiskerRight, whiskerLeft_sum, Preadditive.comp_sum, Preadditive.sum_comp,
        term_monoidal]

/-- The components of the canonical half-braiding at the unit object between distinct simple
classes vanish. -/
theorem component_tensorUnit_of_ne (X : C) {S T : SimpleClasses C} (h : S ≠ T) :
    component k X S T (𝟙_ C) = 0 := by
  have := SimpleClasses.homOrthogonal_repr (D := C) h
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hz : finBasis k (S.repr ⟶ 𝟙_ C ⊗ T.repr) i = 0 := by
    rw [← cancel_mono (λ_ T.repr).hom]
    exact Subsingleton.elim _ _
  rw [hz, ← termₗ_apply k, map_zero]

/-- The component of the canonical half-braiding at the unit object from a simple class to itself
is the composite of the unitors. -/
theorem component_tensorUnit_self (X : C) (S : SimpleClasses C) :
    component k X S S (𝟙_ C) = (ρ_ _).hom ≫ (λ_ _).inv := by
  have hrank : finrank k (S.repr ⟶ 𝟙_ C ⊗ S.repr) = 1 := by
    rw [(Linear.homCongr k (Iso.refl S.repr) (λ_ S.repr)).finrank_eq]
    exact finrank_endomorphism_simple_eq_one k S.repr
  have hne : (λ_ S.repr).inv ≠ 0 := fun h ↦ Simple.not_isZero S.repr <|
    (IsZero.iff_id_eq_zero _).2 (by simpa [h] using ((λ_ S.repr).inv_hom_id).symm)
  let b := FiniteDimensional.basisSingleton (Fin 1) hrank (λ_ S.repr).inv hne
  have hb : b 0 = (λ_ S.repr).inv := by simp [b]
  have hb' : b.homDual 0 = (λ_ S.repr).hom := by
    symm
    rw [Basis.eq_homDual_iff]
    intro i
    fin_cases i
    simp [hb]
  rw [component_eq b, Fin.sum_univ_one, hb, hb', term_leftUnitor]

variable [Fintype (SimpleClasses C)]

/-- The component at `U` of the canonical half-braiding of `⨁ S, S ⊗ X ⊗ Sᘁ`, assembled from
`CenterInduction.component` on the summands. -/
def halfBraidingHom (X U : C) :
    (⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) ⊗ U ⟶
      U ⊗ ⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ :=
  ∑ S, ∑ T, biproduct.π (fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) S ▷ U ≫
    component k X S T U ≫ U ◁ biproduct.ι (fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) T

omit [MonoidalLinear k C] in
/-- The component of `halfBraidingHom` from the summand of `S` to the summand of `T` is
`CenterInduction.component`. -/
@[reassoc (attr := simp)]
theorem ι_whiskerRight_halfBraidingHom_whiskerLeft_π (X U : C) (S T : SimpleClasses C) :
    biproduct.ι (fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) S ▷ U ≫ halfBraidingHom k X U ≫
      U ◁ biproduct.π (fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) T =
      component k X S T U := by
  classical
  simp only [halfBraidingHom, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single S]
  · rw [Finset.sum_eq_single T]
    · simp [← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp]
    · intro T' _ hT'
      simp [← MonoidalCategory.whiskerLeft_comp, biproduct.ι_π_ne _ hT']
    · simp
  · intro S' _ hS'
    refine Finset.sum_eq_zero fun T' _ ↦ ?_
    simp [← comp_whiskerRight_assoc, biproduct.ι_π_ne _ (Ne.symm hS')]
  · simp

/-- The canonical half-braiding is the composite of the unitors at the unit object. -/
theorem halfBraidingHom_tensorUnit (X : C) :
    halfBraidingHom k X (𝟙_ C) = (ρ_ _).hom ≫ (λ_ _).inv := by
  classical
  refine biproduct.whiskerRight_hom_ext fun S ↦ biproduct.whiskerLeft_hom_ext fun T ↦ ?_
  rw [Category.assoc, ι_whiskerRight_halfBraidingHom_whiskerLeft_π]
  by_cases h : S = T
  · subst h
    simp [component_tensorUnit_self]
  · simp [component_tensorUnit_of_ne k X h, biproduct.ι_π_ne_assoc _ h]

/-- The canonical half-braiding is monoidal. -/
theorem halfBraidingHom_tensor (X U V : C) :
    halfBraidingHom k X (U ⊗ V) = (α_ _ _ _).inv ≫ halfBraidingHom k X U ▷ V ≫ (α_ _ _ _).hom ≫
      U ◁ halfBraidingHom k X V ≫ (α_ _ _ _).inv := by
  refine biproduct.whiskerRight_hom_ext fun S ↦ biproduct.whiskerLeft_hom_ext fun R ↦ ?_
  rw [Category.assoc, ι_whiskerRight_halfBraidingHom_whiskerLeft_π, component_tensor]
  -- Insert the identity of `⨁ S, S ⊗ X ⊗ Sᘁ` as the sum of its projections and inclusions.
  rw [← Category.comp_id (halfBraidingHom k X U), ← MonoidalCategory.whiskerLeft_id,
    ← biproduct.total]
  simp only [whiskerLeft_sum, Preadditive.comp_sum, sum_whiskerRight, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [← ι_whiskerRight_halfBraidingHom_whiskerLeft_π k X U S T,
    ← ι_whiskerRight_halfBraidingHom_whiskerLeft_π k X V T R]
  monoidal

/-- The canonical half-braiding is natural. -/
theorem whiskerLeft_comp_halfBraidingHom (X : C) {U U' : C} (g : U ⟶ U') :
    (⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) ◁ g ≫ halfBraidingHom k X U' =
      halfBraidingHom k X U ≫ g ▷ ⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ := by
  refine biproduct.whiskerRight_hom_ext fun S ↦ biproduct.whiskerLeft_hom_ext fun T ↦ ?_
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ι_whiskerRight_halfBraidingHom_whiskerLeft_π, ← whisker_exchange,
    ι_whiskerRight_halfBraidingHom_whiskerLeft_π_assoc, whiskerLeft_comp_component]

omit [MonoidalLinear k C] in
/-- The canonical half-braidings commute with the morphism `⨁ S, S ⊗ X ⊗ Sᘁ ⟶ ⨁ S, S ⊗ Y ⊗ Sᘁ`
induced by `h : X ⟶ Y`. -/
theorem biproductMap_whiskerRight_comp_halfBraidingHom {X Y : C} (h : X ⟶ Y) (U : C) :
    (biproduct.map fun S : SimpleClasses C ↦ S.repr ◁ h ▷ S.reprᘁ) ▷ U ≫ halfBraidingHom k Y U =
      halfBraidingHom k X U ≫ U ◁ biproduct.map fun S : SimpleClasses C ↦ S.repr ◁ h ▷ S.reprᘁ := by
  refine biproduct.whiskerRight_hom_ext fun S ↦ biproduct.whiskerLeft_hom_ext fun T ↦ ?_
  simp only [Category.assoc, biproduct.ι_whiskerRight_map_whiskerRight_assoc,
    biproduct.whiskerLeft_map_whiskerLeft_π, ι_whiskerRight_halfBraidingHom_whiskerLeft_π,
    ι_whiskerRight_halfBraidingHom_whiskerLeft_π_assoc, whiskerRight_comp_component]

/-- The canonical half-braiding of `⨁ S, S ⊗ X ⊗ Sᘁ`, the sum over the simple classes `S` of
their representatives `S`. -/
def halfBraiding (X : C) : HalfBraiding (⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ) :=
  HalfBraiding.ofHom (halfBraidingHom_tensorUnit k X) (halfBraidingHom_tensor k X)
    (whiskerLeft_comp_halfBraidingHom k X)

/-- The components of `CenterInduction.halfBraiding` are `CenterInduction.halfBraidingHom`. -/
@[simp]
theorem halfBraiding_β_hom (X U : C) : ((halfBraiding k X).β U).hom = halfBraidingHom k X U :=
  HalfBraiding.ofHom_β_hom _ _ _ U

end Component

end CenterInduction

section Functor

variable (k : Type w) [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
  [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [Fintype (SimpleClasses C)]

/-- The **induction functor** `C ⥤ Center C` of a fusion category: it sends `X` to
`⨁ S, S ⊗ X ⊗ Sᘁ`, the sum over the simple classes `S` of their representatives, with its
canonical half-braiding `CenterInduction.halfBraiding`, and acts on morphisms summandwise.
Its underlying objects are described by `centerInductionObjIso`. -/
def centerInduction : C ⥤ Center C where
  obj X := ⟨⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ, CenterInduction.halfBraiding k X⟩
  map h :=
    { f := biproduct.map fun S : SimpleClasses C ↦ S.repr ◁ h ▷ S.reprᘁ
      comm U := by
        simpa using CenterInduction.biproductMap_whiskerRight_comp_halfBraidingHom k h U }
  -- `Center.id_f` and `Center.comp_f` only match the identity and composite of the centre here
  -- up to unfolding the functor's object field, hence `erw`.
  map_id X := by
    ext : 1
    erw [Center.id_f]
    exact biproduct.hom_ext _ _ fun S ↦ by simp
  map_comp f g := by
    ext : 1
    erw [Center.comp_f]
    exact biproduct.hom_ext _ _ fun S ↦ by simp

variable {C}

/-- The object underlying the induction of `X` is `⨁ S, S ⊗ X ⊗ Sᘁ`. -/
def centerInductionObjIso (X : C) :
    ((centerInduction k C).obj X).1 ≅ ⨁ fun S : SimpleClasses C ↦ S.repr ⊗ X ⊗ S.reprᘁ :=
  Iso.refl _

/-- `centerInductionObjIso` is natural: under it, the induction of a morphism `h` acts on the
summand of `S` as `S ◁ h ▷ Sᘁ`. -/
@[reassoc (attr := simp)]
theorem centerInductionObjIso_hom_naturality {X Y : C} (h : X ⟶ Y) :
    ((centerInduction k C).map h).f ≫ (centerInductionObjIso k Y).hom =
      (centerInductionObjIso k X).hom ≫
        biproduct.map fun S : SimpleClasses C ↦ S.repr ◁ h ▷ S.reprᘁ :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The inverse form of `centerInductionObjIso_hom_naturality`. -/
@[reassoc (attr := simp)]
theorem centerInductionObjIso_inv_naturality {X Y : C} (h : X ⟶ Y) :
    (centerInductionObjIso k X).inv ≫ ((centerInduction k C).map h).f =
      (biproduct.map fun S : SimpleClasses C ↦ S.repr ◁ h ▷ S.reprᘁ) ≫
        (centerInductionObjIso k Y).inv :=
  (Category.id_comp _).trans (Category.comp_id _).symm

/-- The half-braiding of the induction of `X` is `CenterInduction.halfBraidingHom`, transported
along `centerInductionObjIso`. -/
@[simp]
theorem centerInduction_obj_snd_β_hom (X U : C) :
    (((centerInduction k C).obj X).2.β U).hom = (centerInductionObjIso k X).hom ▷ U ≫
      CenterInduction.halfBraidingHom k X U ≫ U ◁ (centerInductionObjIso k X).inv := by
  calc
    _ = CenterInduction.halfBraidingHom k X U := CenterInduction.halfBraiding_β_hom k X U
    _ = 𝟙 _ ▷ U ≫ CenterInduction.halfBraidingHom k X U ≫ U ◁ 𝟙 _ := by simp
    _ = _ := (rfl)

end Functor

end TauCeti
