/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Scalar

/-!
# Bidual traces and squared norms without a pivotal structure

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
  (`TauCeti.squaredNorm_rightAdjointMate_symm`).
* **Unit**: at the unit comparison `εIso (doubleRightDualFunctor C)`, both trace factors and
  `squaredNorm` equal `𝟙 (𝟙_ C)`.
* **Linearity and biproducts**: `doubleDualTrace` is additive, `R`-linear, and sums over the
  diagonal components of finite and binary biproducts.
* **Invertibility from split coevaluation**: when `η_ X Xᘁ` is a split monomorphism and every
  endomorphism of `X` is a scalar multiple of `𝟙 X`, `doubleDualTrace a.hom` is an isomorphism in
  `C` and a unit in `End (𝟙_ C)`.

The resulting invertibility and nonvanishing properties in finite semisimple categories live in
`TauCeti.CategoryTheory.Monoidal.Rigid.Semisimple`, and the pivot-free global dimension lives in
`TauCeti.CategoryTheory.Monoidal.Rigid.GlobalDim`.

## Main declarations

* `TauCeti.doubleDualTrace` and `TauCeti.squaredNorm`: the bidual trace of `X ⟶ Xᘁᘁ` and the
  squared norm of `X ≅ Xᘁᘁ`;
* `TauCeti.doubleDualTrace_comp_rightAdjointMate_rightAdjointMate`, `TauCeti.doubleDualTrace_conj`,
  and `TauCeti.squaredNorm_conj`: dinaturality and isomorphism invariance;
* `TauCeti.doubleDualTrace_rightAdjointMate_rightAdjointMate` and
  `TauCeti.squaredNorm_rightAdjointMate_symm`: invariance under the double right adjoint mate and
  under passing to `a.rightAdjointMate.symm`;
* `TauCeti.doubleDualTrace_ε_doubleRightDualFunctor`,
  `TauCeti.doubleDualTrace_rightAdjointMate_η_doubleRightDualFunctor`, and
  `TauCeti.squaredNorm_εIso_doubleRightDualFunctor`: values at the tensor unit;
* `TauCeti.squaredNorm_congr`: independence of `a : X ≅ Xᘁᘁ` for objects with scalar
  endomorphisms;
* `TauCeti.isIso_doubleDualTrace_of_isSplitMono` and
  `TauCeti.isUnit_endOf_doubleDualTrace_of_isSplitMono`: invertibility when `η_ X Xᘁ` splits.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  §2.1, Proposition 2.1 and Definition 2.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
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

/-- Since scalars commute, `TauCeti.squaredNorm` is also the product of its two trace factors in
the reverse order. -/
theorem squaredNorm_def' {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
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
  have hmap_hom : ((doubleRightDualFunctor C).mapIso e).hom = (e.hom)ᘁᘁ := by
    rw [Functor.mapIso_hom, doubleRightDualFunctor_map]
  have hmap_inv : ((doubleRightDualFunctor C).mapIso e).inv = (e.inv)ᘁᘁ := by
    rw [Functor.mapIso_inv, doubleRightDualFunctor_map]
  have hhom : (e.symm ≪≫ a ≪≫ (doubleRightDualFunctor C).mapIso e).hom =
      e.inv ≫ a.hom ≫ (e.hom)ᘁᘁ :=
    (Iso.trans_hom _ _).trans <| (Iso.symm_hom e =≫ _).trans <|
      e.inv ≫= (Iso.trans_hom a _).trans (a.hom ≫= hmap_hom)
  have hinv : (e.symm ≪≫ a ≪≫ (doubleRightDualFunctor C).mapIso e).inv =
      (e.inv)ᘁᘁ ≫ a.inv ≫ e.hom :=
    (Iso.trans_inv _ _).trans <| (_ ≫= Iso.symm_inv e).trans <|
      ((Iso.trans_inv a _).trans (hmap_inv =≫ a.inv) =≫ e.hom).trans (Category.assoc _ _ _)
  rw [squaredNorm_def, squaredNorm_def]
  congr 1
  · -- `(doubleRightDualFunctor C).obj Y` and `(Yᘁ : C)ᘁ` are definitionally equal
    -- (`doubleRightDualFunctor_obj`), aligning the target of `hhom` with `doubleDualTrace`.
    exact (congrArg doubleDualTrace hhom).trans (doubleDualTrace_conj e a.hom)
  · -- Similarly, the source `(doubleRightDualFunctor C).obj Y` of `hinv` aligns with `(Yᘁ : C)ᘁ`
    -- in `rightAdjointMate`.
    refine (congrArg (fun f : (Yᘁ : C)ᘁ ⟶ Y ↦ doubleDualTrace (rightAdjointMate f)) hinv).trans ?_
    rw [comp_rightAdjointMate, comp_rightAdjointMate, ← Iso.rightAdjointMate_inv e,
      ← Iso.symm_hom e.rightAdjointMate, ← Iso.rightAdjointMate_hom e,
      ← Iso.symm_inv e.rightAdjointMate, Category.assoc]
    exact doubleDualTrace_conj e.rightAdjointMate.symm (rightAdjointMate a.inv)

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
    -- `hmid` whiskers by `F.obj (Xᘁ : C)` whereas `doubleDualTrace (aᘁᘁ)` writes the same object
    -- as `(((Xᘁ : C)ᘁ : C)ᘁ : C)` (`doubleRightDualFunctor_obj`), preventing direct `rw`.
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
theorem squaredNorm_rightAdjointMate_symm {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a.rightAdjointMate.symm = squaredNorm a := by
  rw [squaredNorm_def, Iso.symm_hom, Iso.symm_inv, Iso.rightAdjointMate_inv,
    Iso.rightAdjointMate_hom, doubleDualTrace_rightAdjointMate_rightAdjointMate,
    ← squaredNorm_def']

/-- At the unit comparison of `doubleRightDualFunctor C`, the bidual trace is `𝟙 (𝟙_ C)`. -/
@[simp]
theorem doubleDualTrace_ε_doubleRightDualFunctor :
    doubleDualTrace (ε (doubleRightDualFunctor C)) = 𝟙 (𝟙_ C) := by
  -- Rewrite `ε` in term mode first because `(doubleRightDualFunctor C).obj (𝟙_ C)` aligns with
  -- `((𝟙_ C)ᘁ : C)ᘁ` via `doubleRightDualFunctor_obj`.
  refine (congrArg doubleDualTrace (doubleRightDualFunctor_ε C)).trans ?_
  rw [doubleDualTrace_def, comp_whiskerRight, Category.assoc,
    rightMate_comp_evaluation, ← whisker_exchange_assoc, ← rightDualUnitIso_hom,
    coevaluation_comp_whiskerLeft_rightDualUnitIso_hom_assoc,
    rightDualIso_inv_whiskerRight_evaluation, ExactPairing.unit_evaluation, Iso.inv_hom_id]

/-- At the right adjoint mate of the inverse unit comparison of `doubleRightDualFunctor C`, the
bidual trace is `𝟙 (𝟙_ C)`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_η_doubleRightDualFunctor :
    doubleDualTrace
      (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
        (η (doubleRightDualFunctor C))) = 𝟙 (𝟙_ C) := by
  -- Rewrite `η` in term mode first for the same `(doubleRightDualFunctor C).obj` alignment.
  refine (congrArg (fun f ↦
    doubleDualTrace (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) f))
    (doubleRightDualFunctor_η C)).trans ?_
  rw [doubleDualTrace_def,
    @rightAdjointMate_comp_evaluation C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)),
    MonoidalCategory.whiskerLeft_comp, Category.assoc, coevaluation_comp_rightMate_assoc,
    ← whisker_exchange_assoc, ← rightDualUnitIso_hom,
    coevaluation_comp_whiskerLeft_rightDualUnitIso_hom_assoc,
    rightDualIso_inv_whiskerRight_evaluation, ExactPairing.unit_evaluation, Iso.inv_hom_id]

/-- At the unit comparison isomorphism `εIso (doubleRightDualFunctor C)`, the squared norm is
`𝟙 (𝟙_ C)` (`|𝟙_ C|² = 1`). -/
@[simp]
theorem squaredNorm_εIso_doubleRightDualFunctor :
    squaredNorm (Functor.Monoidal.εIso (doubleRightDualFunctor C)) = 𝟙 (𝟙_ C) := by
  -- Apply `squaredNorm_def`, `εIso_hom`, and `εIso_inv` in term mode because `εIso` has target
  -- `(doubleRightDualFunctor C).obj (𝟙_ C)` (`doubleRightDualFunctor_obj`).
  refine (squaredNorm_def (Functor.Monoidal.εIso (doubleRightDualFunctor C))).trans ?_
  have h1 : doubleDualTrace (Functor.Monoidal.εIso (doubleRightDualFunctor C)).hom = 𝟙 (𝟙_ C) :=
    (congrArg doubleDualTrace (Functor.Monoidal.εIso_hom (doubleRightDualFunctor C))).trans
      doubleDualTrace_ε_doubleRightDualFunctor
  have h2 : doubleDualTrace
      (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
        (Functor.Monoidal.εIso (doubleRightDualFunctor C)).inv) = 𝟙 (𝟙_ C) :=
    (congrArg (fun f ↦
        doubleDualTrace (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) f))
      (Functor.Monoidal.εIso_inv (doubleRightDualFunctor C))).trans
      doubleDualTrace_rightAdjointMate_η_doubleRightDualFunctor
  exact (h1 =≫ _).trans ((Category.id_comp _).trans h2)

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
  conv_lhs => rw [← endAlgEquivOfBijective_endOf_smul_id hX f]
  rw [Linear.smul_comp, Category.id_comp, doubleDualTrace_smul]

/-- Postcomposing `g : Xᘁᘁ ⟶ X` with an endomorphism `f : X ⟶ X` of an object with scalar
endomorphisms scales `doubleDualTrace (rightAdjointMate g)` by the scalar of `f`. -/
theorem doubleDualTrace_rightAdjointMate_comp_of_bijective
    (hX : Function.Bijective (algebraMap R (End X))) (g : (Xᘁ : C)ᘁ ⟶ X) (f : X ⟶ X) :
    doubleDualTrace (rightAdjointMate (g ≫ f)) =
      endAlgEquivOfBijective hX (End.of f) • doubleDualTrace (rightAdjointMate g) := by
  conv_lhs => rw [← endAlgEquivOfBijective_endOf_smul_id hX f]
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
`𝟙 X`, then `doubleDualTrace a.hom` is an isomorphism in `C`. -/
theorem isIso_doubleDualTrace_of_isSplitMono [IsSplitMono (η_ X Xᘁ)]
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace a.hom) := by
  obtain ⟨r, hr⟩ := exists_smul_doubleDualTrace_eq_id hX a
  exact ⟨⟨r • 𝟙 (𝟙_ C),
    by rw [Linear.comp_smul, Category.comp_id, hr],
    by rw [Linear.smul_comp, Category.id_comp, hr]⟩⟩

/-- If `η_ X Xᘁ` is a split monomorphism and every endomorphism of `X` is a scalar multiple of
`𝟙 X`, then `End.of (doubleDualTrace a.hom)` is a unit in `End (𝟙_ C)`. -/
theorem isUnit_endOf_doubleDualTrace_of_isSplitMono [IsSplitMono (η_ X Xᘁ)]
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsUnit (End.of (doubleDualTrace a.hom)) :=
  (CategoryTheory.isUnit_iff_isIso _).2 (isIso_doubleDualTrace_of_isSplitMono hX a)

end SplitMono

end RightRigid

end TauCeti
