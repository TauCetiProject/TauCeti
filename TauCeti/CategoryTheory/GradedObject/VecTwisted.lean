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
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Dualizable
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.CategoryTheory.GradedObject.Module
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

When `G` is a group, `VecTwisted k G c` is rigid (`VecTwisted.rigidCategory`). The right dual
`VecTwisted.rightDual X` has the dual of `X g⁻¹` in degree `g`, and the left dual
`VecTwisted.leftDual X` has its left dual there. The pairings are the general duality of
cocycle-twisted graded objects, `TwistedGradedObject.exactPairing`: the right dual of `δ_g` is
concentrated in degree `g⁻¹`, and its coevaluation carries the scalar `ω(g, g⁻¹, g)⁻¹`.
`VecTwisted.rightDual_eq`, `VecTwisted.rightDual_evaluation_hom`,
`VecTwisted.rightDual_coevaluation_hom` and their left analogues identify the chosen duals and
their structure maps; `VecTwisted.rightDual_obj_evaluation` and
`VecTwisted.rightDual_obj_coevaluation` describe the pairings of the components.
`VecTwisted.rightDualDeltaIso` and `VecTwisted.leftDualDeltaIso` identify the right and left
duals of `δ_g` with `δ_{g⁻¹}`, by evaluating linear functionals on the field at `1`; the
component of `δ_g` in degree `g` is identified with the field by `VecTwisted.deltaObjIso`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.3 and §2.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u

namespace TauCeti

variable (k G : Type u) [Field k]

section Monoid

variable [Monoid G]

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

/-- The component of `δ_g` in a degree `h` equal to `g` is the field. -/
def deltaObjIso (g : G) (h : Additive G) (hh : h = Additive.ofMul g) :
    (delta (c := c) g).obj h ≅ ModuleCat.of k k :=
  CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g) (ModuleCat.of k k) h hh

/-- `VecTwisted.deltaObjIso` is `GradedObject.singleObjApplyIsoOfEq` after rewriting by
`VecTwisted.delta_obj`. -/
theorem deltaObjIso_hom (g : G) (h : Additive G) (hh : h = Additive.ofMul g) :
    (deltaObjIso (c := c) g h hh).hom = eqToHom (congrFun (delta_obj g) h) ≫
      (CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g)
        (ModuleCat.of k k) h hh).hom :=
  -- `delta_obj` holds by `rfl`, so the `eqToHom` is the identity.
  (Category.id_comp _).symm

/-- The inverse of `VecTwisted.deltaObjIso` is that of `GradedObject.singleObjApplyIsoOfEq`
after rewriting by `VecTwisted.delta_obj`. -/
theorem deltaObjIso_inv (g : G) (h : Additive G) (hh : h = Additive.ofMul g) :
    (deltaObjIso (c := c) g h hh).inv =
      (CategoryTheory.GradedObject.singleObjApplyIsoOfEq (Additive.ofMul g)
        (ModuleCat.of k k) h hh).inv ≫ eqToHom (congrFun (delta_obj g) h).symm :=
  -- As for `deltaObjIso_hom`, the `eqToHom` is the identity.
  (Category.comp_id _).symm

/-- The support of `δ_g` is exactly the degree `g`; in particular these objects are nonzero
also when the grading group is infinite. -/
@[simp]
theorem support_delta (g : G) : (delta (c := c) g).obj.support = {Additive.ofMul g} := by
  apply support_single
  intro hz
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact zero_ne_one (Subsingleton.elim (0 : k) 1)

end VecTwisted

end Monoid

section Rigid

variable {k G} [Group G] {c : GradedObject.TwistingCocycle (Additive G) k}

namespace VecTwisted

/-- The right dual of an object of `VecTwisted`: its component in degree `g` is the dual of the
component of `X` in degree `g⁻¹`. -/
def rightDual (X : VecTwisted k G c) : VecTwisted k G c where
  obj g := (X.obj (-g))ᘁ
  property := ⟨X.hasFiniteSupport.of_injective neg_injective fun _ ↦ isZero_right_of_isZero_left,
    fun _ ↦ (ModuleCat.finite_projective_of_hasLeftDual _).1⟩

/-- The component of the right dual in degree `g` is the dual of the component in degree `g⁻¹`. -/
@[simp]
theorem rightDual_obj (X : VecTwisted k G c) (g : Additive G) :
    (rightDual X).obj g = (X.obj (-g))ᘁ :=
  (rfl)

/-- The left dual of an object of `VecTwisted`: its component in degree `g` is the left dual of
the component of `X` in degree `g⁻¹`. -/
def leftDual (X : VecTwisted k G c) : VecTwisted k G c where
  obj g := ᘁ(X.obj (-g))
  property := ⟨X.hasFiniteSupport.of_injective neg_injective fun _ ↦ isZero_left_of_isZero_right,
    fun _ ↦ (ModuleCat.finite_projective_of_hasRightDual _).1⟩

/-- The component of the left dual in degree `g` is the left dual of the component in degree
`g⁻¹`. -/
@[simp]
theorem leftDual_obj (X : VecTwisted k G c) (g : Additive G) :
    (leftDual X).obj g = ᘁ(X.obj (-g)) :=
  (rfl)

/-- The component of `X` in degree `g` is paired with the component of `VecTwisted.rightDual X`
in degree `g⁻¹`, which is its dual. -/
instance exactPairingObjRightDualObj (X : VecTwisted k G c) (g : Additive G) :
    ExactPairing (X.obj g) ((rightDual X).obj (-g)) :=
  exactPairingCongrRight (Y' := (X.obj g)ᘁ) (eqToIso (by rw [rightDual_obj, neg_neg]))

/-- The evaluation pairing a component of `X` with the component of its right dual in the
opposite degree is the evaluation of the dual of that component. -/
theorem rightDual_obj_evaluation (X : VecTwisted k G c) (g : Additive G) :
    ε_ (X.obj g) ((rightDual X).obj (-g)) =
      eqToHom (by rw [rightDual_obj, neg_neg]) ▷ X.obj g ≫ ε_ (X.obj g) (X.obj g)ᘁ :=
  (rfl)

/-- The coevaluation pairing a component of `X` with the component of its right dual in the
opposite degree is the coevaluation of the dual of that component. -/
theorem rightDual_obj_coevaluation (X : VecTwisted k G c) (g : Additive G) :
    η_ (X.obj g) ((rightDual X).obj (-g)) =
      η_ (X.obj g) (X.obj g)ᘁ ≫ X.obj g ◁ eqToHom (by rw [rightDual_obj, neg_neg]) :=
  (rfl)

/-- The component of `VecTwisted.leftDual X` in degree `g` is paired with the component of `X` in
degree `g⁻¹`, of which it is the left dual. -/
instance exactPairingLeftDualObjObj (X : VecTwisted k G c) (g : Additive G) :
    ExactPairing ((leftDual X).obj g) (X.obj (-g)) :=
  inferInstanceAs (ExactPairing ᘁ(X.obj (-g)) (X.obj (-g)))

variable [DecidableEq G]

/-- Every object of `VecTwisted` has a right dual, `VecTwisted.rightDual`, paired with it by
`TwistedGradedObject.exactPairing`. -/
instance hasRightDual (X : VecTwisted k G c) : HasRightDual X where
  rightDual := rightDual X
  exact := @ObjectProperty.exactPairingFullSubcategory _ _ _ _ _ X (rightDual X)
    (TwistedGradedObject.exactPairing (rightDual X).obj X.hasFiniteSupport)

/-- Every object of `VecTwisted` has a left dual, `VecTwisted.leftDual`, paired with it by
`TwistedGradedObject.exactPairing`. -/
instance hasLeftDual (X : VecTwisted k G c) : HasLeftDual X where
  leftDual := leftDual X
  exact := @ObjectProperty.exactPairingFullSubcategory _ _ _ _ _ (leftDual X) X
    (TwistedGradedObject.exactPairing X.obj (leftDual X).hasFiniteSupport)

/-- The chosen right dual of an object of `VecTwisted` is `VecTwisted.rightDual`. -/
@[simp]
theorem rightDual_eq (X : VecTwisted k G c) : Xᘁ = rightDual X :=
  (rfl)

/-- The chosen left dual of an object of `VecTwisted` is `VecTwisted.leftDual`. -/
@[simp]
theorem leftDual_eq (X : VecTwisted k G c) : (ᘁX) = leftDual X :=
  (rfl)

/-- The evaluation of the right dual is `TwistedGradedObject.evaluation` on underlying graded
objects. -/
theorem rightDual_evaluation_hom (X : VecTwisted k G c) :
    (ε_ X Xᘁ).hom = TwistedGradedObject.evaluation X.obj (rightDual X).obj :=
  (@ObjectProperty.exactPairingFullSubcategory_evaluation_hom _ _ _ _ _ X (rightDual X)
    (TwistedGradedObject.exactPairing (rightDual X).obj X.hasFiniteSupport)).trans
    (TwistedGradedObject.exactPairing_evaluation _ _)

/-- The coevaluation of the right dual is `TwistedGradedObject.coevaluation` on underlying graded
objects. -/
theorem rightDual_coevaluation_hom (X : VecTwisted k G c) :
    (η_ X Xᘁ).hom = TwistedGradedObject.coevaluation c (rightDual X).obj X.hasFiniteSupport :=
  (@ObjectProperty.exactPairingFullSubcategory_coevaluation_hom _ _ _ _ _ X (rightDual X)
    (TwistedGradedObject.exactPairing (rightDual X).obj X.hasFiniteSupport)).trans
    (TwistedGradedObject.exactPairing_coevaluation _ _)

/-- The evaluation of the left dual is `TwistedGradedObject.evaluation` on underlying graded
objects. -/
theorem leftDual_evaluation_hom (X : VecTwisted k G c) :
    (ε_ (ᘁX) X).hom = TwistedGradedObject.evaluation (leftDual X).obj X.obj :=
  (@ObjectProperty.exactPairingFullSubcategory_evaluation_hom _ _ _ _ _ (leftDual X) X
    (TwistedGradedObject.exactPairing X.obj (leftDual X).hasFiniteSupport)).trans
    (TwistedGradedObject.exactPairing_evaluation _ _)

/-- The coevaluation of the left dual is `TwistedGradedObject.coevaluation` on underlying graded
objects. -/
theorem leftDual_coevaluation_hom (X : VecTwisted k G c) :
    (η_ (ᘁX) X).hom = TwistedGradedObject.coevaluation c X.obj (leftDual X).hasFiniteSupport :=
  (@ObjectProperty.exactPairingFullSubcategory_coevaluation_hom _ _ _ _ _ (leftDual X) X
    (TwistedGradedObject.exactPairing X.obj (leftDual X).hasFiniteSupport)).trans
    (TwistedGradedObject.exactPairing_coevaluation _ _)

/-- `Vec^ω_G` is rigid: the duals of an object are graded by inverse degrees. -/
instance rigidCategory : RigidCategory (VecTwisted k G c) where

/-- The component in degree `h` of `VecTwisted.rightDualDeltaIso`: in degree `g⁻¹` it is
`ModuleCat.ihomObjUnitIsoOfIsoSelf` (the dual of the field is by definition its internal Hom
into the unit, `ModuleCat.rightDual_of_finite_projective`) followed by the identification of
`δ_{g⁻¹}` with the field there, and in the other degrees both objects are zero. The components
of the left dual of `δ_g` are definitionally the same, so this is also the component of
`VecTwisted.leftDualDeltaIso`. -/
private def rightDualDeltaIsoApp (g : G) (h : Additive G) :
    (rightDual (delta (c := c) g)).obj h ≅ (delta (c := c) g⁻¹).obj h :=
  if hh : h = Additive.ofMul g⁻¹ then
    ModuleCat.ihomObjUnitIsoOfIsoSelf (deltaObjIso g (-h) (by rw [hh, ofMul_inv, neg_neg])) ≪≫
      (deltaObjIso g⁻¹ h hh).symm
  else
    (show IsZero ((delta (c := c) g).obj (-h))ᘁ from
      isZero_right_of_isZero_left (X := (delta (c := c) g).obj (-h))
        (CategoryTheory.GradedObject.isInitialSingleObjApply (Additive.ofMul g) (ModuleCat.of k k)
          (-h) (by rwa [ne_eq, neg_eq_iff_eq_neg, ← ofMul_inv])).isZero).iso
      (CategoryTheory.GradedObject.isInitialSingleObjApply _ _ _ hh).isZero

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, the component `rightDualDeltaIsoApp` is the
first branch of its defining `dite`. -/
private lemma rightDualDeltaIsoApp_neg_ofMul (g : G) :
    rightDualDeltaIsoApp (c := c) g (-Additive.ofMul g) =
      ModuleCat.ihomObjUnitIsoOfIsoSelf (deltaObjIso g (- -Additive.ofMul g) (neg_neg _)) ≪≫
        (deltaObjIso g⁻¹ (-Additive.ofMul g) (ofMul_inv g).symm).symm :=
  dite_eq_left (ofMul_inv g).symm

/-- The right dual of `δ_g` is `δ_{g⁻¹}`. In degree `g⁻¹` the isomorphism is the identification
of the dual of the field with the field; in the other degrees both objects are zero. -/
def rightDualDeltaIso (g : G) : rightDual (delta (c := c) g) ≅ delta g⁻¹ :=
  ObjectProperty.isoMk _ <| CategoryTheory.GradedObject.isoMk _ _ (rightDualDeltaIsoApp g)

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, `VecTwisted.rightDualDeltaIso` evaluates a
linear functional on the field at `1`: it sends `φ` to the element of `δ_{g⁻¹}` corresponding to
the value of `φ` at the element of `δ_g` corresponding to `1`. -/
@[simp]
theorem rightDualDeltaIso_hom_hom_apply (g : G)
    (φ : (rightDual (delta (c := c) g)).obj (-Additive.ofMul g)) :
    ((rightDualDeltaIso (c := c) g).hom.hom (-Additive.ofMul g)).hom φ =
      (deltaObjIso g⁻¹ (-Additive.ofMul g) (ofMul_inv g).symm).inv.hom
        (((eqToHom (rightDual_obj (delta (c := c) g) (-Additive.ofMul g))).hom φ :
          (delta (c := c) g).obj (- -Additive.ofMul g) ⟶ ModuleCat.of k k).hom
          ((deltaObjIso g (- -Additive.ofMul g) (neg_neg _)).inv.hom 1)) := by
  -- The component of `rightDualDeltaIso` is `rightDualDeltaIsoApp` by definition of the `isoMk`s,
  -- and the `eqToHom` along the `rfl` lemma `rightDual_obj` is the identity. A component of a
  -- morphism of `TwistedGradedObject` is only a function after unfolding that type synonym, so
  -- `change` checks this step up to unfolding.
  change (rightDualDeltaIsoApp g (-Additive.ofMul g)).hom.hom φ = _
  rw [rightDualDeltaIsoApp_neg_ofMul]
  exact congrArg _ (ModuleCat.ihomObjUnitIsoOfIsoSelf_hom_apply _ _)

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, the inverse of `VecTwisted.rightDualDeltaIso`
sends `x` to the linear functional on `δ_g` that multiplies by the scalar corresponding to `x`. -/
theorem rightDualDeltaIso_inv_hom_apply (g : G)
    (x : (delta (c := c) g⁻¹).obj (-Additive.ofMul g))
    (v : (delta (c := c) g).obj (- -Additive.ofMul g)) :
    ((eqToHom (rightDual_obj (delta (c := c) g) (-Additive.ofMul g))).hom
        (((rightDualDeltaIso (c := c) g).inv.hom (-Additive.ofMul g)).hom x) :
        (delta (c := c) g).obj (- -Additive.ofMul g) ⟶ ModuleCat.of k k).hom v =
      (deltaObjIso g (- -Additive.ofMul g) (neg_neg _)).hom.hom v *
        (deltaObjIso g⁻¹ (-Additive.ofMul g) (ofMul_inv g).symm).hom.hom x := by
  -- As in `rightDualDeltaIso_hom_hom_apply`, the component is `rightDualDeltaIsoApp` by
  -- definition and the `eqToHom` is the identity.
  change ((rightDualDeltaIsoApp g (-Additive.ofMul g)).inv.hom x :
    (delta (c := c) g).obj (- -Additive.ofMul g) ⟶ ModuleCat.of k k).hom v = _
  rw [rightDualDeltaIsoApp_neg_ofMul]
  exact ModuleCat.ihomObjUnitIsoOfIsoSelf_inv_apply _ _ v

/-- The left dual of `δ_g` is `δ_{g⁻¹}`. Its components are those of
`VecTwisted.rightDualDeltaIso`, since the left and right duals of a finite-dimensional vector
space are the same module of linear functionals. -/
def leftDualDeltaIso (g : G) : leftDual (delta (c := c) g) ≅ delta g⁻¹ :=
  ObjectProperty.isoMk _ <| CategoryTheory.GradedObject.isoMk _ _ (rightDualDeltaIsoApp g)

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, `VecTwisted.leftDualDeltaIso` evaluates a
linear functional on the field at `1`, as `VecTwisted.rightDualDeltaIso` does. -/
@[simp]
theorem leftDualDeltaIso_hom_hom_apply (g : G)
    (φ : (leftDual (delta (c := c) g)).obj (-Additive.ofMul g)) :
    ((leftDualDeltaIso (c := c) g).hom.hom (-Additive.ofMul g)).hom φ =
      (deltaObjIso g⁻¹ (-Additive.ofMul g) (ofMul_inv g).symm).inv.hom
        (((eqToHom (leftDual_obj (delta (c := c) g) (-Additive.ofMul g))).hom φ :
          (delta (c := c) g).obj (- -Additive.ofMul g) ⟶ ModuleCat.of k k).hom
          ((deltaObjIso g (- -Additive.ofMul g) (neg_neg _)).inv.hom 1)) :=
  -- The components of `leftDualDeltaIso` and `rightDualDeltaIso` are both `rightDualDeltaIsoApp`.
  rightDualDeltaIso_hom_hom_apply g φ

/-- In degree `g⁻¹`, written `-Additive.ofMul g`, the inverse of `VecTwisted.leftDualDeltaIso`
sends `x` to the linear functional on `δ_g` that multiplies by the scalar corresponding to `x`. -/
theorem leftDualDeltaIso_inv_hom_apply (g : G)
    (x : (delta (c := c) g⁻¹).obj (-Additive.ofMul g))
    (v : (delta (c := c) g).obj (- -Additive.ofMul g)) :
    ((eqToHom (leftDual_obj (delta (c := c) g) (-Additive.ofMul g))).hom
        (((leftDualDeltaIso (c := c) g).inv.hom (-Additive.ofMul g)).hom x) :
        (delta (c := c) g).obj (- -Additive.ofMul g) ⟶ ModuleCat.of k k).hom v =
      (deltaObjIso g (- -Additive.ofMul g) (neg_neg _)).hom.hom v *
        (deltaObjIso g⁻¹ (-Additive.ofMul g) (ofMul_inv g).symm).hom.hom x :=
  -- As for `leftDualDeltaIso_hom_hom_apply`, the components agree with those of the right dual.
  rightDualDeltaIso_inv_hom_apply g x v

end VecTwisted

end Rigid

end TauCeti
