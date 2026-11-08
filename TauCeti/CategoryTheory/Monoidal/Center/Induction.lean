/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.Center.OfHom
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Semisimple.DualBasis

/-!
# The induction functor into the Drinfeld centre

Let `C` be a rigid, `k`-linear, finite semisimple abelian monoidal category over an algebraically
closed field `k`, with finitely many simple classes and finite-dimensional morphism spaces, as a
fusion category is (simplicity of the unit is not needed). For `X : C` the object

`I X = ⨁ S, S ⊗ X ⊗ Sᘁ`,

summed over the simple classes `S` of `C`, carries a canonical half-braiding, and `X ↦ I X` is a
functor `C ⥤ Center C`, the induction functor. Mathematically it is adjoint on both sides to the
forgetful functor `Center C ⥤ C`, which makes it the basic tool for studying the centre of a
fusion category: for instance, it is the functor `G` to which the semisimplicity criterion
`TauCeti.IsFiniteSemisimpleCategory.of_natTrans` is applied for the centre. This file constructs
the functor, not the adjunctions.

The component of the half-braiding `I X ⊗ Y ⟶ Y ⊗ I X` from the summand of `S` to that of `T` is,
up to associators,

`∑ i, bᵢ ▷ X ▷ Sᘁ ▷ Y ≫ Y ◁ T ◁ X ◁ m(bᵢ*) : (S ⊗ X ⊗ Sᘁ) ⊗ Y ⟶ Y ⊗ T ⊗ X ⊗ Tᘁ`,

where `bᵢ` runs over a basis of `S ⟶ Y ⊗ T`, `bᵢ*` over the dual basis of `Y ⊗ T ⟶ S`, and
`m(g) : Sᘁ ⊗ Y ⟶ Tᘁ` is the mate of `g : Y ⊗ T ⟶ S`, obtained by inserting the coevaluation of
`T` and evaluating against `Sᘁ`. This element does not depend on the basis. Naturality in `Y`
is the naturality of the canonical element `∑ i, bᵢ* ⊗ bᵢ`, and compatibility with tensor
products of `Y` follows by computing the canonical element of `S ⟶ Y ⊗ Z ⊗ R` through the simple
constituents `T` of `Z ⊗ R`; both are supplied by `TauCeti.CategoryTheory.Semisimple.DualBasis`.
At the unit object the components are the unitors, so `HalfBraiding.ofHom` turns this natural
monoidal family into a half-braiding, with inverses built from left duals.

## Main declarations

* `CategoryTheory.Center.inductionMate` and `CategoryTheory.Center.inductionTerm`: the mate
  `m(g)` and the `k`-bilinear building block of the half-braiding, with their naturality,
  tensor and unit identities;
* `CategoryTheory.Center.inductionβComponent`: the components of the half-braiding, independent
  of the chosen basis by `CategoryTheory.Center.inductionβComponent_eq`;
* `CategoryTheory.Center.inductionObj` and `CategoryTheory.Center.inductionβHom`: the object
  `⨁ S, S ⊗ X ⊗ Sᘁ` and its half-braiding, characterized by its components
  (`CategoryTheory.Center.ι_whiskerRight_inductionβHom_whiskerLeft_π`), natural
  (`CategoryTheory.Center.inductionβHom_naturality`), monoidal
  (`CategoryTheory.Center.inductionβHom_tensor`) and unital
  (`CategoryTheory.Center.inductionβHom_tensorUnit`);
* `CategoryTheory.Center.inductionHalfBraiding` and `CategoryTheory.Center.inductionCenterObj`:
  the resulting object of the Drinfeld centre;
* `CategoryTheory.Center.induction`: the induction functor `C ⥤ Center C`.

## References

* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003)
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Module TauCeti

universe w v u

namespace CategoryTheory.Center

section Term

variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RightRigidCategory C]

/-- The mate `Aᘁ ⊗ Y ⟶ Bᘁ` of a morphism `g : Y ⊗ B ⟶ A`: insert the coevaluation of `B`, apply
`g`, and evaluate against `Aᘁ`. It is the composite of the two Frobenius reciprocities
`(Y ⊗ B ⟶ A) ≃ (Y ⟶ A ⊗ Bᘁ) ≃ (Aᘁ ⊗ Y ⟶ Bᘁ)`. -/
def inductionMate (Y : C) {A B : C} : (Y ⊗ B ⟶ A) →ₗ[k] (Aᘁ ⊗ Y ⟶ Bᘁ) :=
  ((tensorRightHomLinearEquiv k Y B Bᘁ A).trans (tensorLeftHomLinearEquiv k Y A Aᘁ Bᘁ).symm)

/-- The mate of `g : Y ⊗ B ⟶ A` inserts the coevaluation of `B`, applies `g`, and evaluates
against `Aᘁ`. -/
theorem inductionMate_apply {Y A B : C} (g : Y ⊗ B ⟶ A) :
    inductionMate k Y g =
      𝟙 _ ⊗≫ (Aᘁ : C) ◁ Y ◁ η_ B Bᘁ ⊗≫ Aᘁ ◁ g ▷ Bᘁ ⊗≫ ε_ A Aᘁ ▷ Bᘁ ⊗≫ 𝟙 _ := by
  simp only [inductionMate, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    tensorRightHomLinearEquiv_apply, tensorLeftHomLinearEquiv_symm_apply, tensorRightHomEquiv,
    tensorLeftHomEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  monoidal

/-- The mate is natural in `Y`. -/
theorem whiskerLeft_comp_inductionMate {Y Y' A B : C} (h : Y ⟶ Y') (g : Y' ⊗ B ⟶ A) :
    (Aᘁ : C) ◁ h ≫ inductionMate k Y' g = inductionMate k Y (h ▷ B ≫ g) := by
  rw [inductionMate_apply, inductionMate_apply]
  calc
    _ = 𝟙 _ ⊗≫ (Aᘁ : C) ◁ (h ▷ 𝟙_ C ≫ Y' ◁ η_ B Bᘁ) ⊗≫ Aᘁ ◁ g ▷ Bᘁ ⊗≫
          ε_ A Aᘁ ▷ Bᘁ ⊗≫ 𝟙 _ := by
      monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

/-- Evaluating the mate of `g` against `B` is evaluating `g` against `Aᘁ`. -/
theorem inductionMate_whiskerRight_evaluation {Y A B : C} (g : Y ⊗ B ⟶ A) :
    inductionMate k Y g ▷ B ≫ ε_ B Bᘁ = (α_ _ _ _).hom ≫ (Aᘁ : C) ◁ g ≫ ε_ A Aᘁ := by
  rw [inductionMate_apply]
  calc
    _ = 𝟙 _ ⊗≫ (Aᘁ : C) ◁ Y ◁ η_ B Bᘁ ▷ B ⊗≫ (Aᘁ ◁ g) ▷ (Bᘁ ⊗ B) ⊗≫
          (ε_ A Aᘁ ▷ (Bᘁ ⊗ B) ≫ 𝟙_ C ◁ ε_ B Bᘁ) ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (Aᘁ : C) ◁ Y ◁ η_ B Bᘁ ▷ B ⊗≫ ((Aᘁ ◁ g) ▷ (Bᘁ ⊗ B) ≫ (Aᘁ ⊗ A) ◁ ε_ B Bᘁ) ⊗≫
          ε_ A Aᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ (Aᘁ : C) ◁ Y ◁ (η_ B Bᘁ ▷ B ⊗≫ B ◁ ε_ B Bᘁ) ⊗≫ Aᘁ ◁ g ⊗≫ ε_ A Aᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [ExactPairing.evaluation_coevaluation'']; monoidal

/-- The mate of a composite `(Y ⊗ Z) ⊗ R ⟶ Y ⊗ T ⟶ S` is the composite of the mates. -/
theorem inductionMate_tensor {Y Z S T R : C} (g : Y ⊗ T ⟶ S) (g' : Z ⊗ R ⟶ T) :
    inductionMate k (Y ⊗ Z) ((α_ Y Z R).hom ≫ Y ◁ g' ≫ g) =
      (α_ _ _ _).inv ≫ inductionMate k Y g ▷ Z ≫ inductionMate k Z g' := by
  symm
  rw [inductionMate_apply k g']
  calc
    _ = 𝟙 _ ⊗≫ (inductionMate k Y g ▷ Z ▷ 𝟙_ C ≫ (Tᘁ ⊗ Z) ◁ η_ R Rᘁ) ⊗≫ Tᘁ ◁ g' ▷ Rᘁ ⊗≫
          ε_ T Tᘁ ▷ Rᘁ ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (Sᘁ : C) ◁ Y ◁ Z ◁ η_ R Rᘁ ⊗≫
          (inductionMate k Y g ▷ ((Z ⊗ R) ⊗ Rᘁ) ≫ Tᘁ ◁ (g' ▷ Rᘁ)) ⊗≫ ε_ T Tᘁ ▷ Rᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ (Sᘁ : C) ◁ Y ◁ Z ◁ η_ R Rᘁ ⊗≫ Sᘁ ◁ Y ◁ g' ▷ Rᘁ ⊗≫
          (inductionMate k Y g ▷ T ≫ ε_ T Tᘁ) ▷ Rᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [inductionMate_whiskerRight_evaluation, inductionMate_apply]; monoidal

variable (X : C)

/-- The building block of the half-braiding of the induced object: for `g : Y ⊗ B ⟶ A` and
`f : A ⟶ Y' ⊗ B`, the morphism `(A ⊗ X ⊗ Aᘁ) ⊗ Y ⟶ Y' ⊗ B ⊗ X ⊗ Bᘁ` which applies `f` to `A`
and the mate `Aᘁ ⊗ Y ⟶ Bᘁ` of `g` to the remaining factors. It is `k`-bilinear in `g` and `f`. -/
def inductionTerm {A B Y Y' : C} :
    (Y ⊗ B ⟶ A) →ₗ[k] (A ⟶ Y' ⊗ B) →ₗ[k] ((A ⊗ X ⊗ Aᘁ) ⊗ Y ⟶ Y' ⊗ B ⊗ X ⊗ Bᘁ) :=
  LinearMap.mk₂ k (fun g f ↦ 𝟙 _ ⊗≫ f ▷ X ▷ Aᘁ ▷ Y ⊗≫ Y' ◁ B ◁ X ◁ inductionMate k Y g)
    (fun g₁ g₂ f ↦ by simp [monoidalComp])
    (fun c g f ↦ by simp [monoidalComp])
    (fun g f₁ f₂ ↦ by simp [monoidalComp])
    (fun c g f ↦ by simp [monoidalComp])

/-- `inductionTerm` applies `f` to `A` and the mate of `g` to `Aᘁ ⊗ Y`. -/
theorem inductionTerm_apply {A B Y Y' : C} (g : Y ⊗ B ⟶ A) (f : A ⟶ Y' ⊗ B) :
    inductionTerm k X g f = 𝟙 _ ⊗≫ f ▷ X ▷ Aᘁ ▷ Y ⊗≫ Y' ◁ B ◁ X ◁ inductionMate k Y g :=
  (rfl)

/-- `inductionTerm` is natural in the object braided past from the left. -/
theorem whiskerLeft_comp_inductionTerm {A B Y Y₁ Y' : C} (h : Y ⟶ Y₁) (g : Y₁ ⊗ B ⟶ A)
    (f : A ⟶ Y' ⊗ B) :
    (A ⊗ X ⊗ Aᘁ) ◁ h ≫ inductionTerm k X g f = inductionTerm k X (h ▷ B ≫ g) f := by
  rw [inductionTerm_apply, inductionTerm_apply, ← whiskerLeft_comp_inductionMate]
  calc
    _ = 𝟙 _ ⊗≫ ((A ⊗ X ⊗ Aᘁ) ◁ h ≫ (f ▷ (X ⊗ Aᘁ)) ▷ Y₁) ⊗≫ Y' ◁ B ◁ X ◁ inductionMate k Y₁ g :=
      by monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- `inductionTerm` is natural in the object braided past to the right. -/
theorem inductionTerm_comp_whiskerRight {A B Y Y' Y'' : C} (g : Y ⊗ B ⟶ A) (f : A ⟶ Y' ⊗ B)
    (h : Y' ⟶ Y'') :
    inductionTerm k X g f ≫ h ▷ (B ⊗ X ⊗ Bᘁ) = inductionTerm k X g (f ≫ h ▷ B) := by
  rw [inductionTerm_apply, inductionTerm_apply]
  calc
    _ = 𝟙 _ ⊗≫ f ▷ X ▷ Aᘁ ▷ Y ⊗≫ (Y' ◁ (B ◁ X ◁ inductionMate k Y g) ≫ h ▷ (B ⊗ X ⊗ Bᘁ)) :=
      by monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- `inductionTerm` is natural in `X`. -/
theorem whiskerRight_comp_inductionTerm {X' A B Y Y' : C} (h : X ⟶ X') (g : Y ⊗ B ⟶ A)
    (f : A ⟶ Y' ⊗ B) :
    (A ◁ h ▷ Aᘁ) ▷ Y ≫ inductionTerm k X' g f =
      inductionTerm k X g f ≫ Y' ◁ B ◁ h ▷ Bᘁ := by
  rw [inductionTerm_apply, inductionTerm_apply]
  calc
    _ = 𝟙 _ ⊗≫ (A ◁ (h ▷ (Aᘁ ⊗ Y)) ≫ f ▷ (X' ⊗ Aᘁ ⊗ Y)) ⊗≫
          Y' ◁ B ◁ X' ◁ inductionMate k Y g ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ f ▷ X ▷ Aᘁ ▷ Y ⊗≫ Y' ◁ B ◁ (h ▷ (Aᘁ ⊗ Y) ≫ X' ◁ inductionMate k Y g) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

/-- `inductionTerm` of composites through `Y ⊗ T` and `Z ⊗ R` is the composite of the terms for
`Y` and for `Z`. -/
theorem inductionTerm_tensor {Y Z S T R : C} (g : Y ⊗ T ⟶ S) (f : S ⟶ Y ⊗ T)
    (g' : Z ⊗ R ⟶ T) (f' : T ⟶ Z ⊗ R) :
    inductionTerm k X ((α_ Y Z R).hom ≫ Y ◁ g' ≫ g) (f ≫ Y ◁ f' ≫ (α_ Y Z R).inv) =
      (α_ _ _ _).inv ≫ inductionTerm k X g f ▷ Z ≫ (α_ _ _ _).hom ≫
        Y ◁ inductionTerm k X g' f' ≫ (α_ _ _ _).inv := by
  rw [inductionTerm_apply, inductionTerm_apply, inductionTerm_apply, inductionMate_tensor]
  symm
  calc
    _ = 𝟙 _ ⊗≫ f ▷ X ▷ Sᘁ ▷ Y ▷ Z ⊗≫
          Y ◁ (T ◁ (X ◁ inductionMate k Y g ▷ Z) ≫ f' ▷ (X ⊗ Tᘁ ⊗ Z)) ⊗≫
            Y ◁ Z ◁ R ◁ X ◁ inductionMate k Z g' ⊗≫ 𝟙 _ := by
      monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- At the unit object, `inductionTerm` of the left unitor and its inverse is the composite of the
unitors. -/
theorem inductionTerm_leftUnitor (A : C) :
    inductionTerm k X (λ_ A).hom (λ_ A).inv = (ρ_ _).hom ≫ (λ_ _).inv := by
  have h : inductionMate k (𝟙_ C) (λ_ A).hom = (ρ_ _).hom := by
    rw [inductionMate_apply]
    calc
      _ = 𝟙 _ ⊗≫ ((Aᘁ : C) ◁ η_ A Aᘁ ⊗≫ ε_ A Aᘁ ▷ Aᘁ) ⊗≫ 𝟙 _ := by monoidal
      _ = _ := by rw [ExactPairing.coevaluation_evaluation'']; monoidal
  rw [inductionTerm_apply, h]
  monoidal

end Term

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (X : C)

/-- The component `(S ⊗ X ⊗ Sᘁ) ⊗ Y ⟶ Y ⊗ T ⊗ X ⊗ Tᘁ` of the half-braiding of `inductionObj X`,
for simple classes `S` and `T`: the sum of `inductionTerm` over a basis of `S ⟶ Y ⊗ T` and its
dual basis. It does not depend on the basis (`inductionβComponent_eq`). -/
def inductionβComponent (Y : C) (S T : SimpleClasses C) :
    (S.repr ⊗ X ⊗ S.reprᘁ) ⊗ Y ⟶ Y ⊗ T.repr ⊗ X ⊗ T.reprᘁ :=
  ∑ i, inductionTerm k X ((Module.finBasis k (S.repr ⟶ Y ⊗ T.repr)).homDual i)
    (Module.finBasis k (S.repr ⟶ Y ⊗ T.repr) i)

/-- `inductionβComponent` may be computed with any basis of `S ⟶ Y ⊗ T`. -/
theorem inductionβComponent_eq (Y : C) (S T : SimpleClasses C) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι k (S.repr ⟶ Y ⊗ T.repr)) :
    inductionβComponent k X Y S T = ∑ i, inductionTerm k X (b.homDual i) (b i) :=
  Basis.sum_homDual_eq _ _ _

/-- The components of the half-braiding are natural in the object braided past. -/
theorem whiskerLeft_comp_inductionβComponent {Y Y' : C} (f : Y ⟶ Y') (S T : SimpleClasses C) :
    (S.repr ⊗ X ⊗ S.reprᘁ) ◁ f ≫ inductionβComponent k X Y' S T =
      inductionβComponent k X Y S T ≫ f ▷ (T.repr ⊗ X ⊗ T.reprᘁ) := by
  simp only [inductionβComponent, Preadditive.comp_sum, Preadditive.sum_comp,
    whiskerLeft_comp_inductionTerm, inductionTerm_comp_whiskerRight]
  exact (Basis.sum_homDual_comp _ _ (f ▷ T.repr) (inductionTerm k X)).symm

/-- The components of the half-braiding are natural in `X`. -/
theorem whiskerRight_comp_inductionβComponent {X' : C} (h : X ⟶ X') (Y : C)
    (S T : SimpleClasses C) :
    (S.repr ◁ h ▷ S.reprᘁ) ▷ Y ≫ inductionβComponent k X' Y S T =
      inductionβComponent k X Y S T ≫ Y ◁ T.repr ◁ h ▷ T.reprᘁ := by
  simp only [inductionβComponent, Preadditive.comp_sum, Preadditive.sum_comp,
    whiskerRight_comp_inductionTerm]

/-- At the unit object, the diagonal components of the half-braiding are the unitors. -/
theorem inductionβComponent_tensorUnit_self (S : SimpleClasses C) :
    inductionβComponent k X (𝟙_ C) S S = (ρ_ _).hom ≫ (λ_ _).inv := by
  -- Compute with the basis of `S ⟶ 𝟙 ⊗ S` formed by the inverse left unitor alone.
  have hv : (λ_ S.repr).inv ≠ 0 := fun h ↦
    id_ne_zero S.repr (by simpa [h] using (λ_ S.repr).inv_hom_id.symm)
  let b : Basis (Fin 1) k (S.repr ⟶ 𝟙_ C ⊗ S.repr) :=
    Basis.mk (v := fun _ ↦ (λ_ S.repr).inv) (linearIndependent_unique_iff.2 hv) <| by
      rintro f -
      obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (f ≫ (λ_ _).hom)
      rw [Set.range_const, Submodule.mem_span_singleton]
      exact ⟨c, by simpa using hc =≫ (λ_ _).inv⟩
  have hd : b.homDual 0 = (λ_ S.repr).hom :=
    ((b.eq_homDual_iff _ 0).2 fun i ↦ by simp [b, Fin.fin_one_eq_zero i]).symm
  rw [inductionβComponent_eq k X _ S S b, Fin.sum_univ_one, hd, Basis.mk_apply,
    inductionTerm_leftUnitor]

/-- At the unit object, the off-diagonal components of the half-braiding vanish. -/
theorem inductionβComponent_tensorUnit_of_ne {S T : SimpleClasses C} (h : S ≠ T) :
    inductionβComponent k X (𝟙_ C) S T = 0 := by
  have := SimpleClasses.homOrthogonal_repr (D := C) h
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← Category.comp_id (Module.finBasis k _ i), ← (λ_ T.repr).hom_inv_id, ← Category.assoc,
    Subsingleton.elim (_ ≫ (λ_ T.repr).hom) 0, zero_comp, map_zero]

variable [Fintype (SimpleClasses C)]

/-- The components of the half-braiding at `Y ⊗ Z` are composites of those at `Y` and at `Z`,
summed over the intermediate simple class. -/
theorem inductionβComponent_tensor (Y Z : C) (S R : SimpleClasses C) :
    inductionβComponent k X (Y ⊗ Z) S R =
      ∑ T, (α_ _ _ _).inv ≫ inductionβComponent k X Y S T ▷ Z ≫ (α_ _ _ _).hom ≫
        Y ◁ inductionβComponent k X Z T R ≫ (α_ _ _ _).inv := by
  -- Transport the basis of `S ⟶ (Y ⊗ Z) ⊗ R` to one of `S ⟶ Y ⊗ Z ⊗ R` along the associator.
  set c' := Module.finBasis k (S.repr ⟶ Y ⊗ Z ⊗ R.repr)
  have h₁ : inductionβComponent k X (Y ⊗ Z) S R = ∑ j, inductionTerm k X
      ((α_ Y Z R.repr).hom ≫ c'.homDual j) (c' j ≫ (α_ Y Z R.repr).inv) := by
    simpa [inductionβComponent] using
      Basis.sum_homDual_comp (Module.finBasis k (S.repr ⟶ (Y ⊗ Z) ⊗ R.repr)) c'
        (α_ Y Z R.repr).hom
        ((inductionTerm k X).compl₂ (Linear.rightComp k S.repr (α_ Y Z R.repr).inv))
  -- Compute the canonical element of `S ⟶ Y ⊗ Z ⊗ R` through the simple constituents of `Z ⊗ R`.
  have h₂ := sum_homDual_eq_sum_map_homDual (tensorLeft Y) (Z ⊗ R.repr) S.repr c'
    (fun T ↦ Module.finBasis k (T.repr ⟶ Z ⊗ R.repr))
    (fun T ↦ Module.finBasis k (S.repr ⟶ Y ⊗ T.repr))
    (((inductionTerm k X).comp (Linear.leftComp k S.repr (α_ Y Z R.repr).hom)).compl₂
      (Linear.rightComp k S.repr (α_ Y Z R.repr).inv))
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Linear.leftComp_apply,
    Linear.rightComp_apply, curriedTensor_obj_map, Category.assoc, inductionTerm_tensor] at h₂
  rw [h₁, h₂]
  simp only [inductionβComponent, sum_whiskerRight, whiskerLeft_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]

/-- The summand `S ⊗ X ⊗ Sᘁ` of `inductionObj X` indexed by the simple class `S`. -/
abbrev inductionSummand (S : SimpleClasses C) : C :=
  S.repr ⊗ X ⊗ S.reprᘁ

/-- The object `⨁ S, S ⊗ X ⊗ Sᘁ` of `C`, summed over the simple classes `S` of `C`. It underlies
the image of `X` under the induction functor. -/
abbrev inductionObj : C :=
  ⨁ inductionSummand X

/-- The half-braiding of `inductionObj X` at `Y`, assembled from the components
`inductionβComponent`. -/
def inductionβHom (Y : C) : inductionObj X ⊗ Y ⟶ Y ⊗ inductionObj X :=
  ∑ S, ∑ T, biproduct.π (inductionSummand X) S ▷ Y ≫ inductionβComponent k X Y S T ≫
    Y ◁ biproduct.ι (inductionSummand X) T

/-- The components of `inductionβHom` are `inductionβComponent`. -/
@[reassoc (attr := simp)]
theorem ι_whiskerRight_inductionβHom_whiskerLeft_π (Y : C) (S T : SimpleClasses C) :
    biproduct.ι (inductionSummand X) S ▷ Y ≫ inductionβHom k X Y ≫
      Y ◁ biproduct.π (inductionSummand X) T = inductionβComponent k X Y S T := by
  classical
  simp only [inductionβHom, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
    ← whiskerLeft_comp, ← comp_whiskerRight_assoc, biproduct.ι_π]
  rw [Finset.sum_eq_single S, Finset.sum_eq_single T]
  · simp
  · intro T' _ hT'
    simp [hT']
  · simp
  · intro S' _ hS'
    simp [Ne.symm hS']
  · simp

omit [IsFiniteSemisimpleCategory C] in
/-- Morphisms `inductionObj X ⊗ Y ⟶ Y' ⊗ inductionObj X'` are determined by their components. -/
theorem inductionObj_hom_ext {X' Y Y' : C} {f g : inductionObj X ⊗ Y ⟶ Y' ⊗ inductionObj X'}
    (h : ∀ S T, biproduct.ι (inductionSummand X) S ▷ Y ≫ f ≫
      Y' ◁ biproduct.π (inductionSummand X') T =
        biproduct.ι (inductionSummand X) S ▷ Y ≫ g ≫ Y' ◁ biproduct.π (inductionSummand X') T) :
    f = g := by
  have key (φ : inductionObj X ⊗ Y ⟶ Y' ⊗ inductionObj X') : φ = ∑ S, ∑ T,
      biproduct.π (inductionSummand X) S ▷ Y ≫ (biproduct.ι (inductionSummand X) S ▷ Y ≫ φ ≫
        Y' ◁ biproduct.π (inductionSummand X') T) ≫ Y' ◁ biproduct.ι (inductionSummand X') T := by
    calc
      φ = (∑ S, biproduct.π (inductionSummand X) S ≫ biproduct.ι (inductionSummand X) S) ▷ Y ≫
          φ ≫ Y' ◁ ∑ T, biproduct.π (inductionSummand X') T ≫
            biproduct.ι (inductionSummand X') T := by
        simp only [biproduct.total, id_whiskerRight, whiskerLeft_id, Category.id_comp,
          Category.comp_id]
      _ = _ := by
        simp only [sum_whiskerRight, whiskerLeft_sum, Preadditive.sum_comp,
          Preadditive.comp_sum, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
        exact Finset.sum_comm
  rw [key f, key g]
  simp only [h]

/-- The half-braiding of `inductionObj X` is natural in the object braided past. -/
theorem inductionβHom_naturality {Y Y' : C} (f : Y ⟶ Y') :
    inductionObj X ◁ f ≫ inductionβHom k X Y' = inductionβHom k X Y ≫ f ▷ inductionObj X := by
  refine inductionObj_hom_ext X fun S T ↦ ?_
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ι_whiskerRight_inductionβHom_whiskerLeft_π,
    ← whisker_exchange, ι_whiskerRight_inductionβHom_whiskerLeft_π_assoc,
    whiskerLeft_comp_inductionβComponent]

/-- The half-braiding of `inductionObj X` is monoidal in the object braided past. -/
theorem inductionβHom_tensor (Y Z : C) :
    inductionβHom k X (Y ⊗ Z) = (α_ _ _ _).inv ≫ inductionβHom k X Y ▷ Z ≫ (α_ _ _ _).hom ≫
      Y ◁ inductionβHom k X Z ≫ (α_ _ _ _).inv := by
  refine inductionObj_hom_ext X fun S R ↦ ?_
  rw [ι_whiskerRight_inductionβHom_whiskerLeft_π, inductionβComponent_tensor]
  -- Insert the decomposition of the identity of `inductionObj X` between the two half-braidings.
  calc
    _ = ∑ T, (α_ _ _ _).inv ≫ (biproduct.ι (inductionSummand X) S ▷ Y ≫ inductionβHom k X Y ≫
          Y ◁ biproduct.π (inductionSummand X) T) ▷ Z ≫ (α_ _ _ _).hom ≫
            Y ◁ (biproduct.ι (inductionSummand X) T ▷ Z ≫ inductionβHom k X Z ≫
              Z ◁ biproduct.π (inductionSummand X) R) ≫ (α_ _ _ _).inv := by
      simp only [ι_whiskerRight_inductionβHom_whiskerLeft_π]
    _ = (α_ _ _ _).inv ≫ (biproduct.ι (inductionSummand X) S ▷ Y ≫ inductionβHom k X Y ≫
          Y ◁ ∑ T, biproduct.π (inductionSummand X) T ≫ biproduct.ι (inductionSummand X) T) ▷ Z ≫
            (α_ _ _ _).hom ≫ Y ◁ (inductionβHom k X Z ≫
              Z ◁ biproduct.π (inductionSummand X) R) ≫ (α_ _ _ _).inv := by
      simp only [whiskerLeft_sum, Preadditive.comp_sum, sum_whiskerRight, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      monoidal
    _ = _ := by
      simp only [biproduct.total, whiskerLeft_id, Category.comp_id]
      monoidal

/-- At the unit object, the half-braiding of `inductionObj X` is the composite of the unitors. -/
theorem inductionβHom_tensorUnit : inductionβHom k X (𝟙_ C) = (ρ_ _).hom ≫ (λ_ _).inv := by
  classical
  refine inductionObj_hom_ext X fun S T ↦ ?_
  simp only [Category.assoc]
  rw [ι_whiskerRight_inductionβHom_whiskerLeft_π, rightUnitor_naturality_assoc,
    ← leftUnitor_inv_naturality]
  by_cases h : S = T
  · subst h
    simp [inductionβComponent_tensorUnit_self]
  · rw [biproduct.ι_π_ne_assoc _ h, zero_comp, comp_zero,
      inductionβComponent_tensorUnit_of_ne k X h]

/-- The half-braiding of `inductionObj X = ⨁ S, S ⊗ X ⊗ Sᘁ`. Its components are
`inductionβHom k X`, and its inverse components are obtained from them using left duals
(`CategoryTheory.HalfBraiding.ofHom`). -/
def inductionHalfBraiding : HalfBraiding (inductionObj X) :=
  HalfBraiding.ofHom (inductionβHom_tensorUnit k X) (inductionβHom_tensor k X)
    (inductionβHom_naturality k X)

/-- The components of `inductionHalfBraiding k X` are `inductionβHom k X`. -/
@[simp]
theorem inductionHalfBraiding_β_hom (Y : C) :
    ((inductionHalfBraiding k X).β Y).hom = inductionβHom k X Y :=
  HalfBraiding.ofHom_β_hom _ _ _ Y

/-- The morphism `⨁ S, S ⊗ X ⊗ Sᘁ ⟶ ⨁ S, S ⊗ X' ⊗ Sᘁ` induced by `h : X ⟶ X'`. -/
abbrev inductionMap {X X' : C} (h : X ⟶ X') : inductionObj X ⟶ inductionObj X' :=
  biproduct.map fun S ↦ S.repr ◁ h ▷ S.reprᘁ

/-- `inductionMap h` commutes with the half-braidings of `inductionObj X` and `inductionObj X'`. -/
theorem inductionMap_whiskerRight_comp_inductionβHom {X' : C} (h : X ⟶ X') (Y : C) :
    inductionMap h ▷ Y ≫ inductionβHom k X' Y = inductionβHom k X Y ≫ Y ◁ inductionMap h := by
  refine inductionObj_hom_ext X fun S T ↦ ?_
  simp only [← comp_whiskerRight_assoc, biproduct.ι_map, Category.assoc, ← whiskerLeft_comp,
    biproduct.map_π]
  rw [comp_whiskerRight_assoc, ι_whiskerRight_inductionβHom_whiskerLeft_π, whiskerLeft_comp,
    ι_whiskerRight_inductionβHom_whiskerLeft_π_assoc, whiskerRight_comp_inductionβComponent]

/-- The object `⨁ S, S ⊗ X ⊗ Sᘁ` of the Drinfeld centre, with the half-braiding
`inductionHalfBraiding`. -/
@[expose]
def inductionCenterObj : Center C :=
  ⟨inductionObj X, inductionHalfBraiding k X⟩

/-- The object of `C` underlying `inductionCenterObj k X` is `inductionObj X`. -/
@[simp]
theorem inductionCenterObj_fst : (inductionCenterObj k X).1 = inductionObj X :=
  rfl

/-- The half-braiding of `inductionCenterObj k X` is `inductionHalfBraiding k X`. -/
@[simp]
theorem inductionCenterObj_snd : (inductionCenterObj k X).2 = inductionHalfBraiding k X :=
  rfl

variable (C) in
/-- The **induction functor** `C ⥤ Center C` of a fusion category `C`: it sends `X` to
`⨁ S, S ⊗ X ⊗ Sᘁ`, summed over the simple classes `S`, with the half-braiding
`inductionHalfBraiding` built from dual bases of the spaces `S ⟶ Y ⊗ T`. -/
@[expose]
def induction : C ⥤ Center C where
  obj X := inductionCenterObj k X
  map h :=
    { f := inductionMap h
      comm U := by simpa using inductionMap_whiskerRight_comp_inductionβHom k _ h U }
  map_id X := by
    ext : 1
    exact biproduct.hom_ext _ _ fun S ↦ by simp
  map_comp f g := by
    ext : 1
    exact biproduct.hom_ext _ _ fun S ↦ by simp

/-- The induction functor sends `X` to `inductionCenterObj k X`. -/
@[simp]
theorem induction_obj : (induction k C).obj X = inductionCenterObj k X :=
  rfl

/-- The morphism underlying the induction of `h` is `inductionMap h`. -/
@[simp]
theorem induction_map_f {X' : C} (h : X ⟶ X') : ((induction k C).map h).f = inductionMap h :=
  rfl

end Fusion

end CategoryTheory.Center
