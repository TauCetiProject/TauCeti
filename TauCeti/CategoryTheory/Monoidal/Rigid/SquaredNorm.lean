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

Although `doubleDualTrace a.hom` and `doubleDualTrace (a.inv)ᘁ` individually scale by `r` and its
inverse when `a` is multiplied by a unit scalar `r`, their composite cancels that ambiguity: when
every endomorphism of `X` is a scalar multiple of `𝟙 X` over a commutative semiring `R`
(`Function.Surjective (algebraMap R (End X))`), `squaredNorm a` is independent of the choice of
isomorphism `a : X ≅ Xᘁᘁ` (`TauCeti.squaredNorm_congr`). For an object with more endomorphisms it
genuinely depends on `a`: for `X = k²` in finite-dimensional vector spaces, the canonical
isomorphism `X ≅ Xᘁᘁ` gives `2 · 2 = 4`, whereas its composite with `diag(1, 2)` gives
`3 · (3/2) = 9/2`.

We develop the basic calculus of `doubleDualTrace` and `squaredNorm`:

* **Cyclicity and invariance**: `doubleDualTrace (f ≫ b) = doubleDualTrace (b ≫ (fᘁ)ᘁ)`
  (`TauCeti.doubleDualTrace_comm`), so conjugating `a` by an isomorphism `e : X ≅ Y` preserves both
  `doubleDualTrace` and `squaredNorm`.
* **Double-mate invariance and duality**: because `doubleRightDualFunctor C` preserves scalars
  under its unit comparison, `doubleDualTrace (aᘁᘁ) = doubleDualTrace a`, and passing from
  `a : X ≅ Xᘁᘁ` to `a.rightAdjointMate.symm : Xᘁ ≅ Xᘁᘁᘁ` preserves `squaredNorm`
  (`TauCeti.squaredNorm_rightAdjointMate_symm`).
* **Unit**: at the unit comparison `εIso (doubleRightDualFunctor C)`, both trace factors and
  `squaredNorm` equal `𝟙 (𝟙_ C)`.
* **Linearity and biproducts**: `doubleDualTrace` is additive, `R`-linear, and sums over the
  diagonal components of finite and binary biproducts.

Comparison with pivotal traces and dimensions lives in
`TauCeti.CategoryTheory.Monoidal.Pivotal.Trace`, invertibility and nonvanishing in finite
semisimple categories live in `TauCeti.CategoryTheory.Monoidal.Rigid.Semisimple`, and the
pivot-free global dimension lives in `TauCeti.CategoryTheory.Monoidal.Rigid.GlobalDim`.

## Main declarations

* `TauCeti.doubleDualTrace` and `TauCeti.squaredNorm`: the bidual trace of `X ⟶ Xᘁᘁ` and the
  squared norm of `X ≅ Xᘁᘁ`;
* `TauCeti.doubleDualTrace_comm`, `TauCeti.doubleDualTrace_rightAdjointMate`,
  `TauCeti.doubleDualTrace_conj`, and `TauCeti.squaredNorm_conj`: cyclicity, mate unfolding, and
  isomorphism invariance;
* `TauCeti.doubleDualTrace_rightAdjointMate_rightAdjointMate` and
  `TauCeti.squaredNorm_rightAdjointMate_symm`: invariance under the double right adjoint mate and
  under passing to `a.rightAdjointMate.symm`;
* `TauCeti.doubleDualTrace_ε_doubleRightDualFunctor`,
  `TauCeti.doubleDualTrace_rightAdjointMate_η_doubleRightDualFunctor`, and
  `TauCeti.squaredNorm_εIso_doubleRightDualFunctor`: values at the tensor unit;
* `TauCeti.squaredNorm_congr`: independence of `a : X ≅ Xᘁᘁ` when `algebraMap R (End X)` is
  surjective.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  [arXiv:math/0203060](https://arxiv.org/abs/math/0203060), §2.1, Proposition 2.1 and Definition 2.2
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

/-- The trace of a morphism `b : X ⟶ Xᘁᘁ`, closed against the evaluation of `(Xᘁ, Xᘁᘁ)`. -/
noncomputable def doubleDualTrace {X : C} (b : X ⟶ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ : C) ≫ b ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)

/-- **The squared norm** of `X` with respect to an isomorphism `a : X ≅ Xᘁᘁ`
(Etingof–Nikshych–Ostrik, *On fusion categories*, §2.1): `Tr(a) ≫ Tr((a⁻¹)ᘁ)`. -/
noncomputable def squaredNorm {X : C} (a : X ≅ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  doubleDualTrace a.hom ≫ doubleDualTrace (a.invᘁ)

/-- The defining formula of `TauCeti.doubleDualTrace`. -/
theorem doubleDualTrace_def {X : C} (b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace b = η_ X (Xᘁ : C) ≫ b ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  (rfl)

/-- The defining formula of `TauCeti.squaredNorm`. -/
theorem squaredNorm_def {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (a.invᘁ) :=
  (rfl)

/-- Since scalars commute, `TauCeti.squaredNorm` is also the product of its two trace factors in
the reverse order. -/
theorem squaredNorm_def' {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = doubleDualTrace (a.invᘁ) ≫ doubleDualTrace a.hom :=
  scalar_comm _ _

/-- **Cyclicity**: for `f : X ⟶ Y` and `b : Y ⟶ Xᘁᘁ`, the bidual trace of `f ≫ b` is the bidual
trace of `b ≫ (fᘁ)ᘁ`. -/
theorem doubleDualTrace_comm {X Y : C} (f : X ⟶ Y) (b : Y ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (f ≫ b) = doubleDualTrace (b ≫ (fᘁ)ᘁ) := by
  rw [doubleDualTrace_def, doubleDualTrace_def, comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc]
  -- Slide `f` around the loop: at the coevaluation `f ▷ Xᘁ` becomes `Y ◁ fᘁ`, which passes `b`
  -- and reaches the evaluation of `Xᘁ` as `fᘁᘁ ▷ Yᘁ`.
  rw [← coevaluation_comp_rightAdjointMate_assoc, whisker_exchange_assoc,
    ← rightAdjointMate_comp_evaluation]

/-- The bidual trace of the right adjoint mate of `b : Xᘁᘁ ⟶ X` closes `b` up with the
coevaluation of `Xᘁ` and the evaluation of `X`. -/
theorem doubleDualTrace_rightAdjointMate {X : C} (b : (Xᘁ : C)ᘁ ⟶ X) :
    doubleDualTrace (bᘁ) =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ (Xᘁ : C) ◁ b ≫ ε_ X (Xᘁ : C) := by
  rw [doubleDualTrace_def, rightAdjointMate_comp_evaluation]

/-- Conjugating `a : X ⟶ Xᘁᘁ` by an isomorphism `e : X ≅ Y` leaves `doubleDualTrace` unchanged. -/
theorem doubleDualTrace_conj {X Y : C} (e : X ≅ Y) (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (e.inv ≫ a ≫ (e.hom)ᘁᘁ) = doubleDualTrace a := by
  rw [← Category.assoc, ← doubleDualTrace_comm, e.hom_inv_id_assoc]

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
    refine (congrArg (fun f : (Yᘁ : C)ᘁ ⟶ Y ↦ doubleDualTrace (fᘁ)) hinv).trans ?_
    rw [comp_rightAdjointMate, comp_rightAdjointMate, ← Iso.rightAdjointMate_inv e,
      ← Iso.symm_hom e.rightAdjointMate, ← Iso.rightAdjointMate_hom e,
      ← Iso.symm_inv e.rightAdjointMate, Category.assoc]
    exact doubleDualTrace_conj e.rightAdjointMate.symm (a.invᘁ)

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
        rw [Category.assoc, doubleDualTrace_comm, Category.assoc]

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
          doubleDualTrace_comm biprod.fst (biprod.inl ≫ a),
          doubleDualTrace_comm biprod.snd (biprod.inr ≫ a),
          Category.assoc, Category.assoc]

end Linear

section ScalarEnd

variable {R : Type w} [CommSemiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C] {X : C}

variable (R) in
/-- **The squared norm does not depend on the isomorphism** `X ≅ Xᘁᘁ` when every endomorphism
of `X` is a scalar multiple of `𝟙 X` over a commutative semiring `R`: two such isomorphisms differ
by a scalar `r`, their inverses by an inverse scalar `s` on `X`, and the two factors of the squared
norm scale by `r` and `s`. -/
theorem squaredNorm_congr (hX : Function.Surjective (algebraMap R (End X)))
    (a b : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = squaredNorm b := by
  obtain ⟨r, hr⟩ := End.exists_smul_id_eq_of_surjective hX (b.hom ≫ a.inv)
  obtain ⟨s, hs⟩ := End.exists_smul_id_eq_of_surjective hX (a.hom ≫ b.inv)
  have hb : b.hom = r • a.hom := by
    rw [← Category.comp_id b.hom, ← a.inv_hom_id, ← Category.assoc, ← hr, Linear.smul_comp,
      Category.id_comp]
  have hb' : b.inv = s • a.inv := by
    rw [← Category.id_comp b.inv, ← a.inv_hom_id, Category.assoc, ← hs, Linear.comp_smul,
      Category.comp_id]
  -- The scalars `r` and `s` act inversely to each other on `X`, so `(r * s) • a.hom = a.hom`.
  have hrs : (r * s) • a.hom = a.hom := by
    have h : (r • 𝟙 X) ≫ (s • 𝟙 X) = 𝟙 X := by
      rw [hr, hs, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at h
    rw [← Category.id_comp a.hom, ← Linear.smul_comp, h]
  rw [squaredNorm_def, squaredNorm_def, hb, hb']
  simp only [rightAdjointMate_smul, doubleDualTrace_smul, Linear.comp_smul, Linear.smul_comp,
    smul_smul]
  rw [← Linear.smul_comp, ← doubleDualTrace_smul, mul_comm, hrs]

end ScalarEnd

end RightRigid

end TauCeti
