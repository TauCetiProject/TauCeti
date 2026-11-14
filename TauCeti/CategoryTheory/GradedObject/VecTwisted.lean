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
of `X` in degree `g⁻¹`; the pairings are assembled from those of the components by
`TauCeti.TwistedGradedObject.exactPairing`, with the evaluation twisted by the cocycle. In
particular the dual of `δ_g` is `δ_{g⁻¹}` (`VecTwisted.dualDeltaIso`).

## Main declarations

* `TauCeti.VecTwisted.instMonoidalCategory`: the cocycle-twisted monoidal structure;
* `TauCeti.VecTwisted.dual` and `TauCeti.VecTwisted.instRigidCategory`: the graded dual and the
  rigid structure it defines, with `TauCeti.VecTwisted.dualDeltaIso : dual (delta g) ≅ delta g⁻¹`.

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
def of (X : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} k))
    (hX : X.HasFiniteSupport) [∀ g, Module.Finite k (X g)] : VecTwisted k G c :=
  ⟨X, hX, inferInstance⟩

@[simp]
theorem of_obj (X : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} k))
    (hX : X.HasFiniteSupport) [∀ g, Module.Finite k (X g)] :
    (of (c := c) X hX).obj = X :=
  (rfl)

variable [DecidableEq G]

/-- A finite-dimensional vector space concentrated in degree `g`. -/
def single (g : G) (V : ModuleCat.{u} k) [Module.Finite k V] : VecTwisted k G c := by
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
def delta (g : G) : VecTwisted k G c :=
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
def dual (X : VecTwisted k G c) : VecTwisted k G c :=
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

variable [DecidableEq G]

/-- The pairing of `X` with its graded dual: componentwise the pairing of a finite-dimensional
space with its dual, twisted by the cocycle through `TauCeti.TwistedGradedObject.exactPairing`. -/
instance instHasRightDual (X : VecTwisted k G c) : HasRightDual X where
  rightDual := dual X
  exact :=
    letI : ExactPairing X.obj (dual X).obj :=
      TwistedGradedObject.exactPairing c X.obj (dual X).obj X.hasFiniteSupport fun i j h ↦
        letI := ModuleCat.exactPairingDual (X.obj i)
        exactPairingCongrRight (Y' := ModuleCat.of k (Module.Dual k (X.obj i)))
          (eqToIso (by rw [dual_obj, neg_eq_of_add_eq_zero_left h]))
    inferInstance

/-- The pairing of the graded dual with `X`: componentwise the pairing of the dual of a
finite-dimensional space with the space, twisted by the cocycle through
`TauCeti.TwistedGradedObject.exactPairing`. -/
instance instHasLeftDual (X : VecTwisted k G c) : HasLeftDual X where
  leftDual := dual X
  exact :=
    letI : ExactPairing (dual X).obj X.obj :=
      TwistedGradedObject.exactPairing c (dual X).obj X.obj (dual X).hasFiniteSupport
        fun i j h ↦
          letI := ModuleCat.leftExactPairingDual (X.obj j)
          exactPairingCongrLeft (X' := ModuleCat.of k (Module.Dual k (X.obj j)))
            (eqToIso (by rw [dual_obj, neg_eq_of_add_eq_zero_right h]))
    inferInstance

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

/-- The right dual of `X` is its graded dual. -/
@[simp]
theorem rightDual_eq (X : VecTwisted k G c) : (Xᘁ : VecTwisted k G c) = dual X :=
  (rfl)

/-- The left dual of `X` is its graded dual. -/
@[simp]
theorem leftDual_eq (X : VecTwisted k G c) : (ᘁX : VecTwisted k G c) = dual X :=
  (rfl)

end TauCeti.VecTwisted
