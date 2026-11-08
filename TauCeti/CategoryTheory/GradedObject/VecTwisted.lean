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
public import TauCeti.CategoryTheory.GradedObject.Twisted

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

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.3.
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
