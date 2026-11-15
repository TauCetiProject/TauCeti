/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Monoidal.Scalar
public import TauCeti.CategoryTheory.Semisimple.Basic
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Bidual traces, squared norms, and pivot-free global dimension

In a right rigid monoidal category `C` without a chosen pivotal structure, an endomorphism of an
object `X` has no canonical categorical trace, because closing up a loop requires identifying `X`
with its double right dual `Xᘁᘁ`. Instead, any morphism `a : X ⟶ Xᘁᘁ` can be closed against the
evaluation of `(Xᘁ, Xᘁᘁ)` to produce a scalar

`doubleDualTrace a := η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ : 𝟙_ C ⟶ 𝟙_ C`.

Following Etingof, Nikshych, and Ostrik (*On fusion categories*, §2.1), the *squared norm* of an
isomorphism `a : X ≅ Xᘁᘁ` is the composite scalar

`squaredNorm a := doubleDualTrace a.hom ≫ doubleDualTrace (a.inv)ᘁ : 𝟙_ C ⟶ 𝟙_ C`.

Although `doubleDualTrace a.hom` and `doubleDualTrace (a.inv)ᘁ` individually scale by `c` and
`c⁻¹` when `a` is multiplied by a unit scalar `c`, their composite cancels that ambiguity: when
`X` has scalar endomorphisms over a commutative semiring `R`, `squaredNorm a` is independent of the
choice of isomorphism `a : X ≅ Xᘁᘁ` (`TauCeti.squaredNorm_congr`). For a general object whose
endomorphism algebra is non-scalar, `squaredNorm a` genuinely depends on `a`.

We develop the basic calculus of `doubleDualTrace` and `squaredNorm`:

* **Dinaturality and invariance**: `doubleDualTrace (a ≫ gᘁᘁ) = doubleDualTrace (g ≫ a)`, so
  conjugating `a` by an isomorphism `e : X ≅ Y` preserves both `doubleDualTrace` and `squaredNorm`.
* **Double-mate invariance and duality**: because `doubleRightDualFunctor C` preserves scalars
  under its unit comparison, `doubleDualTrace (aᘁᘁ) = doubleDualTrace a`, and passing from
  `a : X ≅ Xᘁᘁ` to `a.rightAdjointMate.symm : Xᘁ ≅ Xᘁᘁᘁ` preserves `squaredNorm`
  (`TauCeti.squaredNorm_rightDual`).
* **Unit**: at the unit comparison `εIso (doubleRightDualFunctor C)`, both `doubleDualTrace` and
  `squaredNorm` equal `𝟙 (𝟙_ C)`.
* **Linearity and biproducts**: `doubleDualTrace` is additive, `R`-linear, and sums over the
  diagonal components of finite and binary biproducts.
* **Invertibility on simple objects**: when `η_ X Xᘁ` splits and every endomorphism of `X` is a
  scalar multiple of `𝟙 X`, `doubleDualTrace a.hom` is an isomorphism (hence a unit in
  `End (𝟙_ C)`). In a finite semisimple rigid abelian category with simple tensor unit, both
  `doubleDualTrace a.hom` and `squaredNorm a` are isomorphisms and nonzero for any split simple
  object `X`.
* **Pivot-free global dimension**: when `SimpleClasses C` is finite, summing `squaredNorm (a S)`
  over a family `a : ∀ S : SimpleClasses C, S.repr ≅ S.reprᘁᘁ` defines `TauCeti.normGlobalDim C a`,
  which is independent of `a` whenever the simple representatives have scalar endomorphisms.

## Main declarations

* `TauCeti.doubleDualTrace` and `TauCeti.squaredNorm`: the bidual trace of `X ⟶ Xᘁᘁ` and the
  squared norm of `X ≅ Xᘁᘁ`;
* `TauCeti.doubleDualTrace_comp_rightAdjointMate_rightAdjointMate`, `TauCeti.doubleDualTrace_conj`,
  and `TauCeti.squaredNorm_conj`: dinaturality and isomorphism invariance;
* `TauCeti.doubleDualTrace_rightAdjointMate_rightAdjointMate` and `TauCeti.squaredNorm_rightDual`:
  invariance under the double right adjoint mate and under right duality;
* `TauCeti.doubleDualTrace_unit_ε` and `TauCeti.squaredNorm_unit_εIso`: values at the tensor unit;
* `TauCeti.squaredNorm_congr`: independence of `a : X ≅ Xᘁᘁ` for objects with scalar
  endomorphisms;
* `TauCeti.isIso_doubleDualTrace_of_isSplitMono`, `TauCeti.isIso_doubleDualTrace_of_simple`,
  `TauCeti.isIso_squaredNorm_of_simple`, and `TauCeti.squaredNorm_ne_zero_of_simple`:
  invertibility and nonvanishing on simple objects;
* `TauCeti.normGlobalDim`, `TauCeti.normGlobalDim_congr_of_bijective`, and
  `TauCeti.normGlobalDim_congr`: the global dimension without a pivotal structure and its
  independence of the chosen double-dual isomorphisms.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  §2.1, Proposition 2.1 and Definition 2.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21,
  Definition 7.21.3
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped ZeroObject

universe w v u

namespace TauCeti

section RightRigid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The trace of a morphism `a : X ⟶ Xᘁᘁ`, closed against the evaluation of `(Xᘁ, Xᘁᘁ)`. -/
noncomputable def doubleDualTrace {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ : C) ≫ a ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)

/-- **The squared norm** of `X` with respect to an isomorphism `a : X ≅ Xᘁᘁ`
(Etingof–Nikshych–Ostrik, *On fusion categories*, §2.1): `Tr(a) ≫ Tr((a⁻¹)ᘁ)`. -/
noncomputable def squaredNorm {X : C} (a : X ≅ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv)

/-- The defining formula of `TauCeti.doubleDualTrace`. -/
theorem doubleDualTrace_def {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace a = η_ X (Xᘁ : C) ≫ a ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  (rfl)

/-- The defining formula of `TauCeti.squaredNorm`. -/
theorem squaredNorm_def {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv) :=
  (rfl)

/-- Since scalars commute, the two trace factors of `TauCeti.squaredNorm` commute. -/
theorem squaredNorm_eq_comm {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = doubleDualTrace (rightAdjointMate a.inv) ≫ doubleDualTrace a.hom :=
  scalar_comm _ _

/-- **Dinaturality of the bidual trace**: sliding `gᘁᘁ` across the evaluation and coevaluation
turns `doubleDualTrace (a ≫ gᘁᘁ)` into `doubleDualTrace (g ≫ a)`. -/
theorem doubleDualTrace_comp_rightAdjointMate_rightAdjointMate {X Y : C}
    (a : X ⟶ (Yᘁ : C)ᘁ) (g : Y ⟶ X) :
    doubleDualTrace (a ≫ gᘁᘁ) = doubleDualTrace (g ≫ a) := by
  rw [doubleDualTrace_def, doubleDualTrace_def, comp_whiskerRight, Category.assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    coevaluation_comp_rightAdjointMate_assoc, ← comp_whiskerRight_assoc]

/-- Conjugating `a : X ⟶ Xᘁᘁ` by an isomorphism `e : X ≅ Y` leaves `doubleDualTrace` unchanged. -/
theorem doubleDualTrace_conj {X Y : C} (e : X ≅ Y) (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (e.inv ≫ a ≫ (e.hom)ᘁᘁ) = doubleDualTrace a := by
  rw [← Category.assoc, doubleDualTrace_comp_rightAdjointMate_rightAdjointMate, e.hom_inv_id_assoc]

/-- Transporting `a : X ≅ Xᘁᘁ` along an isomorphism `e : X ≅ Y` preserves `squaredNorm`. -/
theorem squaredNorm_conj {X Y : C} (e : X ≅ Y) (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm (e.symm ≪≫ a ≪≫ (doubleRightDualFunctor C).mapIso e) = squaredNorm a := by
  rw [squaredNorm_def, squaredNorm_def]
  congr 1
  · exact doubleDualTrace_conj e a.hom
  · have h : doubleDualTrace (rightAdjointMate (((e.inv)ᘁᘁ ≫ a.inv) ≫ e.hom)) =
        doubleDualTrace (rightAdjointMate a.inv) := by
      simpa only [comp_rightAdjointMate, Iso.symm_inv, Iso.symm_hom, Iso.rightAdjointMate_hom,
        Iso.rightAdjointMate_inv] using
        doubleDualTrace_conj e.rightAdjointMate.symm (rightAdjointMate a.inv)
    exact h

/-- A scalar acting on `X` from the left factors out of `doubleDualTrace`. -/
theorem doubleDualTrace_scalar_whiskerRight_comp {X : C} (d : 𝟙_ C ⟶ 𝟙_ C)
    (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace ((λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom ≫ a) = d ≫ doubleDualTrace a := by
  have h : η_ X Xᘁ ≫ ((λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom ≫ a) ▷ (Xᘁ : C) =
      d ≫ η_ X Xᘁ ≫ a ▷ (Xᘁ : C) := by
    calc _ = (η_ X Xᘁ ≫ (λ_ (X ⊗ (Xᘁ : C))).inv) ≫ d ▷ (X ⊗ (Xᘁ : C)) ≫
          (λ_ (X ⊗ (Xᘁ : C))).hom ≫ a ▷ (Xᘁ : C) := by monoidal
      _ = _ := by rw [comp_scalar_whiskerRight_assoc]; simp
  rw [doubleDualTrace_def, doubleDualTrace_def, reassoc_of% h]

/-- **Double-mate invariance**: the bidual trace of `aᘁᘁ` equals the bidual trace of `a`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_rightAdjointMate {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (aᘁᘁ) = doubleDualTrace a := by
  -- Apply `doubleRightDualFunctor C` to the loop of `a`; its tensor comparisons cancel in the
  -- middle and its unit comparisons cancel against `doubleRightDualFunctor_ε_map_η`.
  let F := doubleRightDualFunctor C
  have hmid : μ F X (Xᘁ : C) ≫ F.map (a ▷ (Xᘁ : C)) ≫ δ F ((Xᘁ : C)ᘁ : C) (Xᘁ : C) =
      F.map a ▷ F.obj (Xᘁ : C) := by
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  have hmap : F.map (doubleDualTrace a) = η F ≫ doubleDualTrace (aᘁᘁ) ≫ ε F := by
    rw [doubleDualTrace_def, F.map_comp, F.map_comp,
      doubleRightDualFunctor_map_coevaluation, doubleRightDualFunctor_map_evaluation]
    simp only [Category.assoc, doubleDualTrace_def]
    exact _ ≫= (Category.assoc _ _ _).trans (_ ≫= (reassoc_of% hmid) _)
  calc doubleDualTrace (aᘁᘁ)
      = ε F ≫ (η F ≫ doubleDualTrace (aᘁᘁ) ≫ ε F) ≫ η F := by
        simp only [Category.assoc, Functor.Monoidal.ε_η_assoc, Functor.Monoidal.ε_η,
          Category.comp_id]
    _ = ε F ≫ F.map (doubleDualTrace a) ≫ η F := by rw [hmap]
    _ = doubleDualTrace a := doubleRightDualFunctor_ε_map_η (doubleDualTrace a)

/-- **Duality of squared norms** (`|Xᘁ|² = |X|²`): passing from `a : X ≅ Xᘁᘁ` to the induced
isomorphism `a.rightAdjointMate.symm : Xᘁ ≅ Xᘁᘁᘁ` preserves the squared norm. -/
@[simp]
theorem squaredNorm_rightDual {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a.rightAdjointMate.symm = squaredNorm a := by
  rw [squaredNorm_def, Iso.symm_hom, Iso.symm_inv, Iso.rightAdjointMate_inv,
    Iso.rightAdjointMate_hom, doubleDualTrace_rightAdjointMate_rightAdjointMate,
    ← squaredNorm_eq_comm]

/-- At the unit comparison of `doubleRightDualFunctor C`, the bidual trace is `𝟙 (𝟙_ C)`. -/
@[simp]
theorem doubleDualTrace_unit_ε :
    doubleDualTrace (ε (doubleRightDualFunctor C)) = 𝟙 (𝟙_ C) := by
  dsimp only [doubleDualTrace]
  rw [doubleRightDualFunctor_ε, comp_whiskerRight, Category.assoc,
    rightMate_comp_evaluation, ← whisker_exchange_assoc, ← rightDualUnitIso_hom,
    coevaluation_comp_whiskerLeft_rightDualUnitIso_hom_assoc,
    rightDualIso_inv_whiskerRight_evaluation, ExactPairing.unit_evaluation, Iso.inv_hom_id]

/-- At the unit comparison isomorphism `εIso (doubleRightDualFunctor C)`, the squared norm is
`𝟙 (𝟙_ C)` (`|𝟙_ C|² = 1`). -/
@[simp]
theorem squaredNorm_unit_εIso :
    squaredNorm (Functor.Monoidal.εIso (doubleRightDualFunctor C)) = 𝟙 (𝟙_ C) := by
  dsimp only [squaredNorm, Functor.Monoidal.εIso_hom, Functor.Monoidal.εIso_inv]
  rw [doubleDualTrace_unit_ε, Category.id_comp]
  -- Conjugate the mate of `η` by `rightDualUnitIso C : (𝟙_ C)ᘁ ≅ 𝟙_ C` to reduce it to `ε`.
  let p₁ := (RightRigidCategory.rightDual (𝟙_ C)).exact
  let u : (RightRigidCategory.rightDual (𝟙_ C)).rightDual ≅ 𝟙_ C := rightDualUnitIso C
  let η₀ : ((RightRigidCategory.rightDual (𝟙_ C)).rightDual)ᘁ ⟶ 𝟙_ C :=
    rightMate p₁ HasRightDual.exact u.inv ≫ u.hom
  have hη : η (doubleRightDualFunctor C) = η₀ := by
    rw [doubleRightDualFunctor_η, ← rightDualUnitIso_inv, ← rightDualUnitIso_hom]
  have hε : u.inv ≫ rightMate HasRightDual.exact p₁ u.hom = ε (doubleRightDualFunctor C) := by
    rw [doubleRightDualFunctor_ε, ← rightDualUnitIso_inv, ← rightDualUnitIso_hom]
  have key : u.inv ≫
      @rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) η₀ ≫
      (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) u.hom)ᘁ =
        u.inv ≫ rightMate HasRightDual.exact p₁ u.hom := by
    rw [@rightAdjointMate_eq_rightMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) η₀,
      @rightAdjointMate_eq_rightMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) u.hom,
      rightAdjointMate_eq_rightMate, ← comp_rightMate]
    dsimp only [η₀]
    rw [← Category.assoc (rightMate HasRightDual.exact p₁ u.hom), ← comp_rightMate, u.inv_hom_id,
      rightMate_id, Category.id_comp]
  have hu : u.inv ≫
      @rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
        (η (doubleRightDualFunctor C)) ≫
      (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) u.hom)ᘁ =
        ε (doubleRightDualFunctor C) :=
    (congrArg (fun f ↦ u.inv ≫
      @rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) f ≫
      (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) u.hom)ᘁ) hη).trans
      (key.trans hε)
  have hconj := @doubleDualTrace_conj C _ _ _ _ (𝟙_ C) u
    (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
      (η (doubleRightDualFunctor C)))
  -- At `Y = 𝟙_ C`, `doubleDualTrace_conj` uses `RightRigidCategory.rightDual (𝟙_ C)` on `u.hom`.
  exact hconj.symm.trans ((congrArg doubleDualTrace hu).trans doubleDualTrace_unit_ε)

section Zero

variable [HasZeroMorphisms C]

/-- The bidual trace of the zero morphism is zero. -/
@[simp]
theorem doubleDualTrace_zero (X : C) : doubleDualTrace (0 : X ⟶ (Xᘁ : C)ᘁ) = 0 := by
  simp [doubleDualTrace_def]

/-- Any isomorphism of the zero object with its double dual has squared norm zero. -/
@[simp]
theorem squaredNorm_zero [HasZeroObject C] (a : (0 : C) ≅ (((0 : C)ᘁ : C)ᘁ : C)) :
    squaredNorm a = 0 := by
  rw [squaredNorm_def, Subsingleton.elim a.hom 0, doubleDualTrace_zero, zero_comp]

end Zero

section Linear

variable [Preadditive C] [MonoidalPreadditive C]

/-- The bidual trace is additive. -/
@[simp]
theorem doubleDualTrace_add {X : C} (a b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (a + b) = doubleDualTrace a + doubleDualTrace b := by
  simp [doubleDualTrace_def]

/-- The bidual trace commutes with finite sums. -/
@[simp]
theorem doubleDualTrace_sum {ι : Type*} {X : C} (s : Finset ι) (a : ι → (X ⟶ (Xᘁ : C)ᘁ)) :
    doubleDualTrace (∑ i ∈ s, a i) = ∑ i ∈ s, doubleDualTrace (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- The bidual trace commutes with negation. -/
@[simp]
theorem doubleDualTrace_neg {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (-a) = -doubleDualTrace a :=
  eq_neg_of_add_eq_zero_left (by rw [← doubleDualTrace_add, neg_add_cancel, doubleDualTrace_zero])

/-- The bidual trace commutes with subtraction. -/
@[simp]
theorem doubleDualTrace_sub {X : C} (a b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (a - b) = doubleDualTrace a - doubleDualTrace b := by
  rw [sub_eq_add_neg, doubleDualTrace_add, doubleDualTrace_neg, sub_eq_add_neg]

/-- The bidual trace is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem doubleDualTrace_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]
    {X : C} (r : R) (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (r • a) = r • doubleDualTrace a := by
  simp [doubleDualTrace_def]

/-- The bidual trace of a morphism out of a finite biproduct is the sum of the bidual traces of
its diagonal components. -/
theorem doubleDualTrace_biproduct {ι : Type*} [Fintype ι] {X : ι → C} [HasBiproduct X]
    (a : ⨁ X ⟶ ((⨁ X)ᘁ : C)ᘁ) :
    doubleDualTrace a = ∑ i, doubleDualTrace (biproduct.ι X i ≫ a ≫ (biproduct.π X i)ᘁᘁ) := by
  calc doubleDualTrace a
      = doubleDualTrace ((∑ i, biproduct.π X i ≫ biproduct.ι X i) ≫ a) := by simp
    _ = ∑ i, doubleDualTrace ((biproduct.π X i ≫ biproduct.ι X i) ≫ a) := by
        rw [Preadditive.sum_comp, doubleDualTrace_sum]
    _ = ∑ i, doubleDualTrace (biproduct.ι X i ≫ a ≫ (biproduct.π X i)ᘁᘁ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Category.assoc, ← doubleDualTrace_comp_rightAdjointMate_rightAdjointMate,
          Category.assoc]

/-- The bidual trace of a morphism out of a binary biproduct is the sum of the bidual traces of
its two diagonal components. -/
theorem doubleDualTrace_biprod {X Y : C} [HasBinaryBiproduct X Y]
    (a : X ⊞ Y ⟶ ((X ⊞ Y)ᘁ : C)ᘁ) :
    doubleDualTrace a =
      doubleDualTrace (biprod.inl ≫ a ≫ (biprod.fst)ᘁᘁ) +
        doubleDualTrace (biprod.inr ≫ a ≫ (biprod.snd)ᘁᘁ) := by
  calc doubleDualTrace a
      = doubleDualTrace ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ a) := by simp
    _ = _ := by
        rw [Preadditive.add_comp, doubleDualTrace_add, Category.assoc, Category.assoc,
          ← doubleDualTrace_comp_rightAdjointMate_rightAdjointMate (biprod.inl ≫ a) biprod.fst,
          ← doubleDualTrace_comp_rightAdjointMate_rightAdjointMate (biprod.inr ≫ a) biprod.snd,
          Category.assoc, Category.assoc]

end Linear

section ScalarEnd

variable {R : Type w} [CommSemiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C] {X : C}

/-- Precomposing `a : X ⟶ Xᘁᘁ` with an endomorphism `f : X ⟶ X` of an object with scalar
endomorphisms scales `doubleDualTrace a` by the scalar of `f`. -/
theorem doubleDualTrace_comp_of_bijective
    (hX : Function.Bijective (algebraMap R (End X))) (f : X ⟶ X) (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (f ≫ a) = endAlgEquivOfBijective hX (End.of f) • doubleDualTrace a := by
  conv_lhs => rw [← endAlgEquivOfBijective_of_smul_id hX f]
  rw [Linear.smul_comp, Category.id_comp, doubleDualTrace_smul]

/-- Postcomposing `g : Xᘁᘁ ⟶ X` with an endomorphism `f : X ⟶ X` of an object with scalar
endomorphisms scales `doubleDualTrace (rightAdjointMate g)` by the scalar of `f`. -/
theorem doubleDualTrace_rightAdjointMate_comp_of_bijective
    (hX : Function.Bijective (algebraMap R (End X))) (g : (Xᘁ : C)ᘁ ⟶ X) (f : X ⟶ X) :
    doubleDualTrace (rightAdjointMate (g ≫ f)) =
      endAlgEquivOfBijective hX (End.of f) • doubleDualTrace (rightAdjointMate g) := by
  conv_lhs => rw [← endAlgEquivOfBijective_of_smul_id hX f]
  rw [Linear.comp_smul, Category.comp_id, rightAdjointMate_smul, doubleDualTrace_smul]

variable (R) in
/-- **Independence of the isomorphism**: for an object `X` with scalar endomorphisms over a
commutative semiring `R`, `squaredNorm a` does not depend on the chosen isomorphism
`a : X ≅ Xᘁᘁ`. -/
theorem squaredNorm_congr (hX : Function.Bijective (algebraMap R (End X)))
    (a b : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = squaredNorm b := by
  -- Write `a.hom = (a ≪≫ b.symm).hom ≫ b.hom` and `a.inv = b.inv ≫ (a ≪≫ b.symm).inv`; their
  -- scalars are inverse to each other in `R`.
  let u : X ≅ X := a ≪≫ b.symm
  have ha : a.hom = u.hom ≫ b.hom := by simp [u]
  have hainv : a.inv = b.inv ≫ u.inv := by simp [u]
  rw [squaredNorm_def, squaredNorm_def, ha, hainv, doubleDualTrace_comp_of_bijective hX,
    doubleDualTrace_rightAdjointMate_comp_of_bijective hX, Linear.smul_comp, Linear.comp_smul,
    smul_smul, endAlgEquivOfBijective_hom_mul_inv hX u, one_smul]

end ScalarEnd

section SplitMono

variable {R : Type w} [CommSemiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C] {X : C}

/-- If `η_ X Xᘁ` is a split monomorphism and every endomorphism of `X` is a scalar multiple of
`𝟙 X`, then some scalar multiple of `doubleDualTrace a.hom` equals `𝟙 (𝟙_ C)`. -/
theorem exists_smul_doubleDualTrace_eq_id [IsSplitMono (η_ X Xᘁ)]
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    ∃ r : R, r • doubleDualTrace a.hom = 𝟙 (𝟙_ C) := by
  let p : ExactPairing Xᘁ X := exactPairingCongrRight a
  obtain ⟨r, hr⟩ := @hom_tensorUnit_eq_smul_evaluation_of_surjective_right C _ _ _ _ R _ _ _ Xᘁ X p
    hX (retraction (η_ X Xᘁ))
  refine ⟨r, ?_⟩
  rw [doubleDualTrace_def, ← exactPairingCongrRight_evaluation a, ← Linear.comp_smul, ← hr]
  exact IsSplitMono.id (η_ X Xᘁ)

/-- If `η_ X Xᘁ` is a split monomorphism and every endomorphism of `X` is a scalar multiple of
`𝟙 X`, then `doubleDualTrace a.hom` is an isomorphism in `C` (equivalently, a unit of
`End (𝟙_ C)` by `CategoryTheory.isUnit_iff_isIso`). -/
theorem isIso_doubleDualTrace_of_isSplitMono [IsSplitMono (η_ X Xᘁ)]
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace a.hom) := by
  obtain ⟨r, hr⟩ := exists_smul_doubleDualTrace_eq_id hX a
  exact ⟨⟨r • 𝟙 (𝟙_ C),
    by rw [Linear.comp_smul, Category.comp_id, hr],
    by rw [Linear.smul_comp, Category.id_comp, hr]⟩⟩

end SplitMono

end RightRigid

section Simple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

section CommSemiring

variable {R : Type w} [CommSemiring R] [Linear R C] [MonoidalLinear R C]

/-- In a finite semisimple rigid abelian category with simple tensor unit, if `X` is simple and
`algebraMap R (End X)` is surjective, then `doubleDualTrace a.hom` is an isomorphism. -/
theorem isIso_doubleDualTrace_of_surjective_of_simple {X : C} [Simple X]
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace a.hom) := by
  have : IsSplitMono (η_ X Xᘁ) :=
    isSplitMono_of_nonzero_from_simple (coevaluation_ne_zero (Simple.not_isZero X))
  exact isIso_doubleDualTrace_of_isSplitMono hX a

/-- In a finite semisimple rigid abelian category with simple tensor unit, if `X` is simple and
`algebraMap R (End X)` is surjective, then `squaredNorm a` is an isomorphism. -/
theorem isIso_squaredNorm_of_surjective_of_simple {X : C} [Simple X]
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (squaredNorm a) := by
  rw [squaredNorm_def, ← Iso.rightAdjointMate_inv, ← Iso.symm_hom]
  have : IsIso (doubleDualTrace a.hom) := isIso_doubleDualTrace_of_surjective_of_simple hX a
  have : IsIso (doubleDualTrace a.rightAdjointMate.symm.hom) :=
    isIso_doubleDualTrace_of_surjective_of_simple (surjective_algebraMap_end_rightDual hX)
      a.rightAdjointMate.symm
  exact IsIso.comp_isIso

end CommSemiring

section Field

variable (k : Type w) [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]

include k in
/-- For a split simple object `X` in a finite semisimple rigid category with simple tensor unit,
`doubleDualTrace a.hom` is an isomorphism. -/
theorem isIso_doubleDualTrace_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : IsIso (doubleDualTrace a.hom) :=
  isIso_doubleDualTrace_of_surjective_of_simple
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple rigid category with simple tensor unit,
`End.of (doubleDualTrace a.hom)` is a unit in `End (𝟙_ C)`. -/
theorem isUnit_of_doubleDualTrace_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : IsUnit (End.of (doubleDualTrace a.hom)) :=
  (CategoryTheory.isUnit_iff_isIso _).2 (isIso_doubleDualTrace_of_simple k a)

include k in
/-- For a split simple object `X` in a finite semisimple rigid category with simple tensor unit,
`doubleDualTrace a.hom` is nonzero. -/
theorem doubleDualTrace_ne_zero_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : doubleDualTrace a.hom ≠ 0 := by
  have := isIso_doubleDualTrace_of_simple k a
  exact (isIso_iff_ne_zero _).1 this

include k in
/-- For a split simple object `X` in a finite semisimple rigid category with simple tensor unit,
`squaredNorm a` is an isomorphism. -/
theorem isIso_squaredNorm_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : IsIso (squaredNorm a) :=
  isIso_squaredNorm_of_surjective_of_simple
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple rigid category with simple tensor unit,
`squaredNorm a` is nonzero. -/
theorem squaredNorm_ne_zero_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : squaredNorm a ≠ 0 := by
  have := isIso_squaredNorm_of_simple k a
  exact (isIso_iff_ne_zero _).1 this

end Field

end Simple

section NormGlobalDim

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] [Preadditive C]
  [Fintype (SimpleClasses C)]

/-- **The global dimension without a pivotal structure** (Etingof–Nikshych–Ostrik, Definition 2.2;
Etingof–Gelaki–Nikshych–Ostrik, Definition 7.21.3): the sum of the squared norms of the simple
representatives, for a family of isomorphisms to their double right duals. When the simple
representatives have scalar endomorphisms, its value is independent of the family `a` by
`TauCeti.normGlobalDim_congr_of_bijective`. -/
noncomputable def normGlobalDim (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  ∑ S : SimpleClasses C, squaredNorm (a S)

/-- The defining formula of `TauCeti.normGlobalDim`. -/
theorem normGlobalDim_def (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = ∑ S : SimpleClasses C, squaredNorm (a S) :=
  (rfl)

/-- When every simple representative has scalar endomorphisms over a commutative semiring `R`,
`TauCeti.normGlobalDim` is independent of the chosen double-dual isomorphisms. -/
theorem normGlobalDim_congr_of_bijective (R : Type w) [CommSemiring R] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Bijective (algebraMap R (End S.repr)))
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  Finset.sum_congr rfl fun S _ ↦ squaredNorm_congr R (hS S) (a S) (b S)

/-- Over an algebraically closed field `k`, if each simple representative has finite-dimensional
endomorphisms, `TauCeti.normGlobalDim` is independent of the chosen double-dual isomorphisms. -/
theorem normGlobalDim_congr (k : Type w) [Field k] [IsAlgClosed k] [MonoidalPreadditive C]
    [Linear k C] [MonoidalLinear k C] [HasKernels C]
    [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  normGlobalDim_congr_of_bijective C k (fun S ↦ bijective_algebraMap_end_of_simple k S.repr) a b

end NormGlobalDim

end TauCeti
