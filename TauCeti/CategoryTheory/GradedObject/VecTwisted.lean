/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.CategoryTheory.GradedObject.Module
public import TauCeti.Algebra.Category.FGModuleCat.Rigid
public import TauCeti.CategoryTheory.GradedObject.Twisted.Rigid
public import TauCeti.CategoryTheory.Monoidal.Rigid.Subcategory

/-!
# Finitely supported cocycle-twisted graded vector spaces

`VecTwisted k G c` is the full subcategory of cocycle-twisted graded vector spaces whose
components are finite-dimensional and whose categorical support is finite. Convolution and the
unit preserve both conditions, so the twisted associator restricts to a monoidal structure.
No finiteness assumption on the grading monoid is required. For a group this is the underlying
monoidal category of the pointed tensor category usually denoted `Vec^ω_G`.

The category is realized inside graded modules, which have arbitrary coproducts; the finiteness
proofs ensure that convolution remains in the finite-dimensional subcategory. Objects concentrated
in one degree, including the one-dimensional objects `VecTwisted.delta`, belong to it.

When `G` is a group, `VecTwisted k G c` is rigid. The left and right dual of `X` are both the
graded dual `VecTwisted.dual X`, whose component in degree `g` is the dual space of the component
of `X` in degree `g⁻¹`; the pairings (`VecTwisted.gradedPairing` and
`VecTwisted.leftGradedPairing`) are assembled from those of the components by
`TauCeti.TwistedGradedObject.exactPairing`, with the evaluation twisted by the cocycle. In
particular the dual of `δ_g` is `δ_{g⁻¹}` (`VecTwisted.dualDeltaIso`).

## Main declarations

* `TauCeti.VecTwisted.instMonoidalCategory`: the cocycle-twisted monoidal structure;
* `TauCeti.VecTwisted.dual` and `TauCeti.VecTwisted.instRigidCategory`: the graded dual and the
  rigid structure it defines, with `TauCeti.VecTwisted.dualDeltaIso : dual (delta g) ≅ delta g⁻¹`;
* `TauCeti.VecTwisted.coevaluation_hom`, `TauCeti.VecTwisted.evaluation_hom`,
  `TauCeti.VecTwisted.leftCoevaluation_hom` and `TauCeti.VecTwisted.leftEvaluation_hom`: the
  structure maps are `TauCeti.TwistedGradedObject.dualCoevaluation` and
  `TauCeti.TwistedGradedObject.dualEvaluation` of the componentwise pairings
  `TauCeti.VecTwisted.componentPairing` and `TauCeti.VecTwisted.leftComponentPairing`;
* `TauCeti.VecTwisted.dualDeltaIso_hom_hom_apply` and
  `TauCeti.VecTwisted.dualDeltaIso_inv_hom_apply`: the components of `dualDeltaIso` in degree
  `g⁻¹`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§2.3, 2.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u

namespace TauCeti

variable (k G : Type u) [Field k] [Monoid G]

/-- The objects of `VecTwisted`: finitely supported graded vector spaces with finite components.
The grading is written additively using `Additive G`, so that convolution uses multiplication
in `G`. -/
def VecTwisted.objects (c : GradedObject.TwistingCocycle (Additive G) k) :
    ObjectProperty (TwistedGradedObject c (ModuleCat.{u} k)) :=
  fun X ↦ CategoryTheory.GradedObject.HasFiniteSupport X ∧ ∀ g, Module.Finite k (X g)

/-- The category of finitely supported finite-dimensional `G`-graded vector spaces, with
associator twisted by the normalized three-cocycle `c`. -/
abbrev VecTwisted (c : GradedObject.TwistingCocycle (Additive G) k) :=
  (VecTwisted.objects k G c).FullSubcategory

namespace VecTwisted

variable {k G} (c : GradedObject.TwistingCocycle (Additive G) k)

/-- Membership in the defining full subcategory is exactly finite support and finiteness of
every homogeneous component. -/
theorem objects_iff (X : TwistedGradedObject c (ModuleCat.{u} k)) :
    objects k G c X ↔
      CategoryTheory.GradedObject.HasFiniteSupport X ∧ ∀ g, Module.Finite k (X g) :=
  Iff.rfl

section Monoidal

variable [DecidableEq G]

/-- Convolution and the unit preserve the finiteness conditions defining `VecTwisted`. -/
instance objects_isMonoidal : (objects k G c).IsMonoidal := by
  refine { prop_unit := ?_, prop_tensor := ?_ }
  · refine ⟨CategoryTheory.GradedObject.hasFiniteSupport_single 0 _, ?_⟩
    intro g
    exact CategoryTheory.GradedObject.finite_single_obj 0 (𝟙_ (ModuleCat k)) g
  · intro X Y hX hY
    have := hX.2
    have := hY.2
    exact ⟨hX.1.tensorObj hY.1, fun g ↦ hX.1.finite_tensorObj hY.1 g⟩

/-- The cocycle-twisted monoidal structure on finite-dimensional, finitely supported objects. -/
instance instMonoidalCategory : MonoidalCategory (VecTwisted k G c) := by
  infer_instance

end Monoidal

/-- The fully faithful inclusion into all cocycle-twisted graded vector spaces. -/
abbrev forget : VecTwisted k G c ⥤ TwistedGradedObject c (ModuleCat.{u} k) :=
  (objects k G c).ι

variable {c}

/-- The underlying graded vector space of an object of `VecTwisted` has finite support. -/
theorem hasFiniteSupport (X : VecTwisted k G c) :
    CategoryTheory.GradedObject.HasFiniteSupport X.obj :=
  X.property.1

/-- Every homogeneous component is finite-dimensional. -/
instance finite_component (X : VecTwisted k G c) (g : Additive G) :
    Module.Finite k (X.obj g) :=
  X.property.2 g

/-- Form an object of `VecTwisted` from a finitely supported graded vector space with finite
components. -/
@[expose] def of (X : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} k))
    (hX : X.HasFiniteSupport) [∀ g, Module.Finite k (X g)] : VecTwisted k G c :=
  ⟨X, (objects_iff c X).2 ⟨hX, inferInstance⟩⟩

@[simp]
theorem of_obj (X : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} k))
    (hX : X.HasFiniteSupport) [∀ g, Module.Finite k (X g)] :
    (of (c := c) X hX).obj = X :=
  (rfl)

variable [DecidableEq G]

/-- A finite-dimensional vector space concentrated in degree `g`. -/
@[expose] def single (g : G) (V : ModuleCat.{u} k) [Module.Finite k V] : VecTwisted k G c := by
  letI (i : Additive G) := CategoryTheory.GradedObject.finite_single_obj (Additive.ofMul g) V i
  exact of ((CategoryTheory.GradedObject.single (Additive.ofMul g)).obj V)
    (CategoryTheory.GradedObject.hasFiniteSupport_single _ _)

@[simp]
theorem single_obj (g : G) (V : ModuleCat.{u} k) [Module.Finite k V] :
    (single (c := c) g V).obj =
      (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj V :=
  (rfl)

/-- A nonzero finite-dimensional vector space concentrated in degree `g` has singleton support. -/
theorem support_single (g : G) (V : ModuleCat.{u} k) [Module.Finite k V]
    (hV : ¬ IsZero V) : (single (c := c) g V).obj.support = {Additive.ofMul g} := by
  rw [single_obj]
  exact CategoryTheory.GradedObject.support_single _ V hV

/-- The one-dimensional graded object concentrated in degree `g`. -/
@[expose] def delta (g : G) : VecTwisted k G c :=
  single g (ModuleCat.of k k)

/-- The underlying graded vector space of `δ_g` is the single-degree copy of the field. -/
theorem delta_obj (g : G) : (delta (c := c) g).obj =
    (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj (ModuleCat.of k k) :=
  (rfl)

/-- The support of `δ_g` is exactly the degree `g`; in particular these objects are nonzero
also when the grading group is infinite. -/
@[simp]
theorem support_delta (g : G) : (delta (c := c) g).obj.support = {Additive.ofMul g} := by
  apply support_single
  intro hz
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact zero_ne_one (Subsingleton.elim (0 : k) 1)

end VecTwisted

end TauCeti

/-! ### Duals -/

namespace TauCeti.VecTwisted

variable {k G : Type u} [Field k] [Group G] {c : GradedObject.TwistingCocycle (Additive G) k}

/-- The graded dual of `X`: its component in degree `g` is the dual space of the component of `X`
in degree `g⁻¹`. It is both the left and the right dual of `X`. -/
@[expose] def dual (X : VecTwisted k G c) : VecTwisted k G c :=
  of (fun g ↦ ModuleCat.of k (Module.Dual k (X.obj (-g)))) <| by
    classical
    obtain ⟨s, hs⟩ := (CategoryTheory.GradedObject.hasFiniteSupport_iff _).1 X.hasFiniteSupport
    refine (CategoryTheory.GradedObject.hasFiniteSupport_iff _).2 ⟨s.image (-·), fun g hg ↦ ?_⟩
    have := ModuleCat.isZero_iff_subsingleton.1
      (hs _ fun h ↦ hg (Finset.mem_image.2 ⟨-g, h, neg_neg g⟩))
    exact ModuleCat.isZero_of_subsingleton _

/-- The component of the graded dual in degree `g` is the dual space of the component in
degree `g⁻¹`. -/
@[simp]
theorem dual_obj (X : VecTwisted k G c) (g : Additive G) :
    (dual X).obj g = ModuleCat.of k (Module.Dual k (X.obj (-g))) :=
  (rfl)

/-- The pairing of the component of `X` in degree `i` with the component of its graded dual in
degree `j`, for `i + j = 0`: the pairing `ModuleCat.exactPairingDual` of `X.obj i` with its dual
space, which is the component of `dual X` in degree `j = -i`. -/
@[instance_reducible]
def componentPairing (X : VecTwisted k G c) (i j : Additive G) (h : i + j = 0) :
    ExactPairing (X.obj i) ((dual X).obj j) :=
  letI := ModuleCat.exactPairingDual (X.obj i)
  exactPairingCongrRight (Y' := ModuleCat.of k (Module.Dual k (X.obj i)))
    (eqToIso (by rw [dual_obj, neg_eq_of_add_eq_zero_left h]))

/-- The pairing of the component of the graded dual of `X` in degree `i` with the component of
`X` in degree `j`, for `i + j = 0`: the pairing `ModuleCat.leftExactPairingDual` of the dual space
of `X.obj j`, which is the component of `dual X` in degree `i = -j`, with `X.obj j`. -/
@[instance_reducible]
def leftComponentPairing (X : VecTwisted k G c) (i j : Additive G) (h : i + j = 0) :
    ExactPairing ((dual X).obj i) (X.obj j) :=
  letI := ModuleCat.leftExactPairingDual (X.obj j)
  exactPairingCongrLeft (X' := ModuleCat.of k (Module.Dual k (X.obj j)))
    (eqToIso (by rw [dual_obj, neg_eq_of_add_eq_zero_right h]))

/-- The evaluation of `VecTwisted.componentPairing`: the contraction of
`ModuleCat.exactPairingDual`, after identifying the component of the graded dual with the dual
space. -/
@[simp]
theorem componentPairing_evaluation (X : VecTwisted k G c) (i j : Additive G) (h : i + j = 0) :
    @ExactPairing.evaluation _ _ _ _ _ (componentPairing X i j h) =
      eqToHom (by rw [dual_obj, neg_eq_of_add_eq_zero_left h]) ▷ X.obj i ≫
        @ExactPairing.evaluation _ _ _ (X.obj i) (ModuleCat.of k (Module.Dual k (X.obj i)))
          (ModuleCat.exactPairingDual (X.obj i)) :=
  (rfl)

/-- The coevaluation of `VecTwisted.componentPairing`: the coevaluation of
`ModuleCat.exactPairingDual`, after identifying the dual space with the component of the graded
dual. -/
@[simp]
theorem componentPairing_coevaluation (X : VecTwisted k G c) (i j : Additive G) (h : i + j = 0) :
    @ExactPairing.coevaluation _ _ _ _ _ (componentPairing X i j h) =
      @ExactPairing.coevaluation _ _ _ (X.obj i) (ModuleCat.of k (Module.Dual k (X.obj i)))
          (ModuleCat.exactPairingDual (X.obj i)) ≫
        X.obj i ◁ eqToHom (by rw [dual_obj, neg_eq_of_add_eq_zero_left h]) :=
  (rfl)

/-- The evaluation of `VecTwisted.leftComponentPairing`: the evaluation of
`ModuleCat.leftExactPairingDual`, after identifying the component of the graded dual with the dual
space. -/
@[simp]
theorem leftComponentPairing_evaluation (X : VecTwisted k G c) (i j : Additive G)
    (h : i + j = 0) :
    @ExactPairing.evaluation _ _ _ _ _ (leftComponentPairing X i j h) =
      X.obj j ◁ eqToHom (by rw [dual_obj, neg_eq_of_add_eq_zero_right h]) ≫
        @ExactPairing.evaluation _ _ _ (ModuleCat.of k (Module.Dual k (X.obj j))) (X.obj j)
          (ModuleCat.leftExactPairingDual (X.obj j)) :=
  (rfl)

/-- The coevaluation of `VecTwisted.leftComponentPairing`: the coevaluation of
`ModuleCat.leftExactPairingDual`, after identifying the dual space with the component of the
graded dual. -/
@[simp]
theorem leftComponentPairing_coevaluation (X : VecTwisted k G c) (i j : Additive G)
    (h : i + j = 0) :
    @ExactPairing.coevaluation _ _ _ _ _ (leftComponentPairing X i j h) =
      @ExactPairing.coevaluation _ _ _ (ModuleCat.of k (Module.Dual k (X.obj j))) (X.obj j)
          (ModuleCat.leftExactPairingDual (X.obj j)) ≫
        eqToHom (by rw [dual_obj, neg_eq_of_add_eq_zero_right h]) ▷ X.obj j :=
  (rfl)

variable [DecidableEq G]

/-- The pairing of the graded vector space underlying `X` with that underlying its graded dual:
componentwise the pairing of a finite-dimensional space with its dual
(`VecTwisted.componentPairing`), twisted by the cocycle through
`TauCeti.TwistedGradedObject.exactPairing`. -/
@[instance_reducible]
def gradedPairing (X : VecTwisted k G c) : ExactPairing X.obj (dual X).obj :=
  TwistedGradedObject.exactPairing c X.obj (dual X).obj X.hasFiniteSupport (componentPairing X)

/-- The pairing of the graded vector space underlying the graded dual of `X` with that underlying
`X`: componentwise the pairing of the dual of a finite-dimensional space with the space
(`VecTwisted.leftComponentPairing`), twisted by the cocycle through
`TauCeti.TwistedGradedObject.exactPairing`. -/
@[instance_reducible]
def leftGradedPairing (X : VecTwisted k G c) : ExactPairing (dual X).obj X.obj :=
  TwistedGradedObject.exactPairing c (dual X).obj X.obj (dual X).hasFiniteSupport
    (leftComponentPairing X)

/-- The pairing of `X` with its graded dual, lifted from `VecTwisted.gradedPairing`. -/
instance instHasRightDual (X : VecTwisted k G c) : HasRightDual X where
  rightDual := dual X
  exact :=
    letI := gradedPairing X
    inferInstance

/-- The pairing of the graded dual with `X`, lifted from `VecTwisted.leftGradedPairing`. -/
instance instHasLeftDual (X : VecTwisted k G c) : HasLeftDual X where
  leftDual := dual X
  exact :=
    letI := leftGradedPairing X
    inferInstance

/-- The coevaluation of `X` with its right dual is the graded coevaluation
`TauCeti.TwistedGradedObject.dualCoevaluation` of the componentwise pairings.

Not a `simp` lemma: `simp` already reaches the right-hand side through
`CategoryTheory.ObjectProperty.exactPairingFullSubcategory_coevaluation_hom` and
`TauCeti.TwistedGradedObject.exactPairing_coevaluation`. -/
theorem coevaluation_hom (X : VecTwisted k G c) :
    (η_ X Xᘁ).hom = TwistedGradedObject.dualCoevaluation (Y := (dual X).obj) X.hasFiniteSupport
      (componentPairing X) :=
  letI := gradedPairing X
  (ObjectProperty.exactPairingFullSubcategory_coevaluation_hom X (dual X)).trans
    (TwistedGradedObject.exactPairing_coevaluation c _ _ _ _)

/-- The evaluation of `X` with its right dual is the twisted graded evaluation
`TauCeti.TwistedGradedObject.dualEvaluation` of the componentwise pairings.

Not a `simp` lemma: `simp` already reaches the right-hand side through
`CategoryTheory.ObjectProperty.exactPairingFullSubcategory_evaluation_hom` and
`TauCeti.TwistedGradedObject.exactPairing_evaluation`. -/
theorem evaluation_hom (X : VecTwisted k G c) :
    (ε_ X Xᘁ).hom =
      TwistedGradedObject.dualEvaluation (X := X.obj) (Y := (dual X).obj) c (componentPairing X) :=
  letI := gradedPairing X
  (ObjectProperty.exactPairingFullSubcategory_evaluation_hom X (dual X)).trans
    (TwistedGradedObject.exactPairing_evaluation c _ _ _ _)

/-- The coevaluation of the left dual of `X` with `X` is the graded coevaluation
`TauCeti.TwistedGradedObject.dualCoevaluation` of the componentwise pairings.

Not a `simp` lemma: `simp` already reaches the right-hand side through
`CategoryTheory.ObjectProperty.exactPairingFullSubcategory_coevaluation_hom` and
`TauCeti.TwistedGradedObject.exactPairing_coevaluation`. -/
theorem leftCoevaluation_hom (X : VecTwisted k G c) :
    (η_ (ᘁX) X).hom = TwistedGradedObject.dualCoevaluation (X := (dual X).obj) (Y := X.obj)
      (dual X).hasFiniteSupport (leftComponentPairing X) :=
  letI := leftGradedPairing X
  (ObjectProperty.exactPairingFullSubcategory_coevaluation_hom (dual X) X).trans
    (TwistedGradedObject.exactPairing_coevaluation c _ _ _ _)

/-- The evaluation of `X` with its left dual is the twisted graded evaluation
`TauCeti.TwistedGradedObject.dualEvaluation` of the componentwise pairings.

Not a `simp` lemma: `simp` already reaches the right-hand side through
`CategoryTheory.ObjectProperty.exactPairingFullSubcategory_evaluation_hom` and
`TauCeti.TwistedGradedObject.exactPairing_evaluation`. -/
theorem leftEvaluation_hom (X : VecTwisted k G c) :
    (ε_ (ᘁX) X).hom = TwistedGradedObject.dualEvaluation (X := (dual X).obj) (Y := X.obj) c
      (leftComponentPairing X) :=
  letI := leftGradedPairing X
  (ObjectProperty.exactPairingFullSubcategory_evaluation_hom (dual X) X).trans
    (TwistedGradedObject.exactPairing_evaluation c _ _ _ _)

/-- Finitely supported finite-dimensional graded vector spaces with cocycle-twisted associator
form a rigid monoidal category. -/
instance instRigidCategory : RigidCategory (VecTwisted k G c) where

/-- The graded dual of `δ_g` is `δ_{g⁻¹}`. In degree `g⁻¹` the isomorphism is the identification
of the dual of the field with the field; in the other degrees both objects are zero. -/
def dualDeltaIso (g : G) : dual (delta (c := c) g) ≅ delta g⁻¹ :=
  ObjectProperty.isoMk _ <| CategoryTheory.GradedObject.isoMk _ _ fun h ↦
    if hh : h = Additive.ofMul g⁻¹ then
      (LinearEquiv.dualMap (CategoryTheory.GradedObject.singleObjApplyIsoOfEq
          (Additive.ofMul g) (ModuleCat.of k k) (-h)
          (by rw [hh, ofMul_inv, neg_neg])).symm.toLinearEquiv ≪≫ₗ
        LinearMap.ringLmapEquivSelf k k k).toModuleIso ≪≫
        (CategoryTheory.GradedObject.singleObjApplyIsoOfEq _ (ModuleCat.of k k) h hh).symm
    else
      have : Subsingleton ((delta (c := c) g).obj (-h)) := ModuleCat.isZero_iff_subsingleton.1
        (CategoryTheory.GradedObject.isInitialSingleObjApply (Additive.ofMul g) (ModuleCat.of k k)
          (-h) (by rwa [ne_eq, neg_eq_iff_eq_neg, ← ofMul_inv])).isZero
      (ModuleCat.isZero_of_subsingleton
          (ModuleCat.of k (Module.Dual k ((delta (c := c) g).obj (-h))))).iso
        (CategoryTheory.GradedObject.isInitialSingleObjApply _ _ _ hh).isZero

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, `VecTwisted.dualDeltaIso` evaluates a linear
functional on the field at `1`: it sends `φ` to the element of `δ_{g⁻¹}` corresponding to the
value of `φ` at the element of `δ_g` corresponding to `1`. -/
@[simp]
theorem dualDeltaIso_hom_hom_apply (g : G)
    (φ : Module.Dual k ((delta (c := c) g).obj (- -Additive.ofMul g))) :
    ((dualDeltaIso (c := c) g).hom.hom (-Additive.ofMul g)).hom φ =
      (CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g⁻¹) (ModuleCat.of k k)
          (-Additive.ofMul g) (ofMul_inv g).symm).inv.hom
        (φ ((CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g)
          (ModuleCat.of k k) (- -Additive.ofMul g) (neg_neg _)).inv.hom 1)) := by
  -- The first-branch isomorphism, for arbitrary identifications `e` and `f` with the field.
  have key {A B : ModuleCat k} (e : A ≅ ModuleCat.of k k) (f : B ≅ ModuleCat.of k k)
      (φ : Module.Dual k A) :
      ((e.symm.toLinearEquiv.dualMap ≪≫ₗ LinearMap.ringLmapEquivSelf k k k).toModuleIso ≪≫
        f.symm).hom.hom φ = f.inv.hom (φ (e.inv.hom 1)) := by
    rw [Iso.trans_hom, Iso.symm_hom, LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearMap.ringLmapEquivSelf_apply, LinearEquiv.dualMap_apply, Iso.toLinearEquiv_apply,
      Iso.symm_hom]
  -- In this degree the defining `dite` takes its first branch (`dite_eq_left`). The goal is not
  -- type-correct at reducible transparency, since a component of a morphism of
  -- `TwistedGradedObject` is only a function after unfolding that type synonym, so `rw` and
  -- `simp` cannot rewrite with `ObjectProperty.isoMk_hom` and `GradedObject.isoMk_hom`; these
  -- `isoMk` projections are instead reduced definitionally by `congrArg`.
  exact (congrArg (fun e : ((dual (delta (c := c) g)).obj (-Additive.ofMul g) : ModuleCat k) ≅
      (delta g⁻¹).obj (-Additive.ofMul g) ↦ e.hom.hom φ) (dite_eq_left (ofMul_inv g).symm)).trans
    (key _ _ φ)

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, the inverse of `VecTwisted.dualDeltaIso` sends
`x` to the linear functional on `δ_g` that multiplies by the scalar corresponding to `x`. -/
@[simp]
theorem dualDeltaIso_inv_hom_apply (g : G)
    (x : (delta (c := c) g⁻¹).obj (-Additive.ofMul g))
    (v : (delta (c := c) g).obj (- -Additive.ofMul g)) :
    ((dualDeltaIso (c := c) g).inv.hom (-Additive.ofMul g)).hom
      (B := ModuleCat.of k (Module.Dual k ((delta (c := c) g).obj (- -Additive.ofMul g)))) x v =
      (CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g) (ModuleCat.of k k)
          (- -Additive.ofMul g) (neg_neg _)).hom.hom v *
        (CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g⁻¹)
          (ModuleCat.of k k) (-Additive.ofMul g) (ofMul_inv g).symm).hom.hom x := by
  -- The first-branch isomorphism, for arbitrary identifications `e` and `f` with the field.
  have key {A B : ModuleCat k} (e : A ≅ ModuleCat.of k k) (f : B ≅ ModuleCat.of k k)
      (x : B) (v : A) :
      ((e.symm.toLinearEquiv.dualMap ≪≫ₗ LinearMap.ringLmapEquivSelf k k k).toModuleIso ≪≫
        f.symm).inv.hom (B := ModuleCat.of k (Module.Dual k A)) x v =
        e.hom.hom v * f.hom.hom x := by
    rw [Iso.trans_inv, Iso.symm_inv, LinearEquiv.toModuleIso_inv, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_symm,
      LinearEquiv.trans_apply, LinearMap.ringLmapEquivSelf_symm_apply, LinearEquiv.dualMap_symm,
      LinearEquiv.dualMap_apply, LinearMap.smulRight_apply, one_apply_eq_self,
      Iso.toLinearEquiv_symm, Iso.symm_symm_eq, Iso.toLinearEquiv_apply, smul_eq_mul]
  -- As in `dualDeltaIso_hom_hom_apply`: `dite_eq_left` picks the first branch, and `congrArg`
  -- reduces the `isoMk` projections definitionally because the goal is not type-correct at
  -- reducible transparency.
  exact (congrArg (fun e : ((dual (delta (c := c) g)).obj (-Additive.ofMul g) : ModuleCat k) ≅
      (delta g⁻¹).obj (-Additive.ofMul g) ↦
    e.inv.hom (B := ModuleCat.of k (Module.Dual k ((delta (c := c) g).obj (- -Additive.ofMul g))))
      x v) (dite_eq_left (ofMul_inv g).symm)).trans (key _ _ x v)

/-- The right dual of `X` is its graded dual. -/
@[simp]
theorem rightDual_eq (X : VecTwisted k G c) : (Xᘁ : VecTwisted k G c) = dual X :=
  (rfl)

/-- The left dual of `X` is its graded dual. -/
@[simp]
theorem leftDual_eq (X : VecTwisted k G c) : (ᘁX : VecTwisted k G c) = dual X :=
  (rfl)

end TauCeti.VecTwisted
