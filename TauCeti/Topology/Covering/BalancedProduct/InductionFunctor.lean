/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.BalancedProduct.Induction
public import TauCeti.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Induction of group actions is left adjoint to restriction

Let `K` be a subgroup of a group `G`. For a `K`-set `Z`, the balanced product
`TauCeti.BalancedProduct K G Z`, the quotient of `G × Z` by `h • (g, z) = (h g, h • z)`, is a
`G`-set under `a • ⟦g, z⟧ = ⟦g a⁻¹, z⟧` (`TauCeti.BalancedProduct.inducedMulAction`). Through
`⟦g, z⟧ ↦ ⟦g⁻¹, z⟧` it is the induced `G`-set `G ×_K Z`, with `G` acting on the left factor.

This file makes induction a functor `Action (Type u) K ⥤ Action (Type u) G`
(`TauCeti.BalancedProduct.inductionFunctor`), left adjoint to Mathlib's restriction
`Action.res (Type u) K.subtype` (`TauCeti.BalancedProduct.inductionAdjunction`). The
hom-equivalence (`TauCeti.BalancedProduct.inductionHomEquiv`) sends a `G`-map `f` out of the
induced `G`-set to its restriction `z ↦ f ⟦1, z⟧`, and a `K`-map `ι` to
`TauCeti.BalancedProduct.inducedLift`, `⟦g, z⟧ ↦ g⁻¹ • ι z`. That these are inverse bijections
is the universal property of induction, `TauCeti.bijOn_balancedProduct_lift`, in the form of its
characteristic lemmas `TauCeti.BalancedProduct.eq_inducedLift` and
`TauCeti.BalancedProduct.inducedLift_mk_one`. Mathlib's
`CategoryTheory.Adjunction.leftAdjointOfEquiv` and `CategoryTheory.Adjunction.adjunctionOfEquivLeft`
assemble the functor and the adjunction from it.

That restriction has some left adjoint is already Mathlib's, by left Kan extension; the content
here is that the balanced product is that left adjoint, with the explicit unit `z ↦ ⟦1, z⟧`.

## Main definitions

* `TauCeti.BalancedProduct.inducedMulAction`: the action of `G` on the balanced product.
* `TauCeti.BalancedProduct.induced`: the induced `G`-set of a `K`-set.
* `TauCeti.BalancedProduct.inductionHomEquiv`: the hom-equivalence of the adjunction.
* `TauCeti.BalancedProduct.inductionFunctor`: induction, as a functor.
* `TauCeti.BalancedProduct.inductionAdjunction`: **induction is left adjoint to restriction.**

## References

Induced `G`-sets are standard; compare G. E. Bredon, *Introduction to Compact Transformation
Groups*, Academic Press, 1972, Section II.2, for the twisted products `G ×_K A`.
-/

public section

universe u

open CategoryTheory

namespace TauCeti

namespace BalancedProduct

variable {G : Type u} [Group G] (K : Subgroup G)

/-! ### The induced `G`-set -/

section MulAction

variable (Z : Type u) [MulAction K Z]

/-- The action of `G` on the balanced product `TauCeti.BalancedProduct K G Z` by
`a • ⟦g, z⟧ = ⟦g a⁻¹, z⟧`. It is not an instance, since `G` can act on balanced products in other
ways. -/
@[expose, instance_reducible]
def inducedMulAction : MulAction G (BalancedProduct K G Z) where
  smul a := Quotient.map (fun p : G × Z ↦ (p.1 * a⁻¹, p.2)) fun _ _ ⟨h, hh⟩ ↦ ⟨h, by
    rw [← hh]
    simp [Subgroup.smul_def, mul_assoc]⟩
  one_smul x := by
    induction x using BalancedProduct.ind with
    | h g z => exact congrArg (mk K · z) (by simp)
  mul_smul a b x := by
    induction x using BalancedProduct.ind with
    | h g z => exact congrArg (mk K · z) (by simp [mul_assoc])

variable {K Z}

/-- `a` acts on the class of `(g, z)` by right multiplication of `g` by `a⁻¹`. -/
theorem inducedMulAction_smul_mk (a g : G) (z : Z) :
    (inducedMulAction K Z).smul a (mk K g z) = mk K (g * a⁻¹) z :=
  (rfl)

end MulAction

variable (Z : Action (Type u) K)

/-- The **induced `G`-set** of a `K`-set `Z`: the balanced product `TauCeti.BalancedProduct K G Z`
with `G` acting by `a • ⟦g, z⟧ = ⟦g a⁻¹, z⟧`. -/
-- Exposed so that the points of `induced K Z` are the classes `mk K g z` by definition: the
-- statements of `induced_ρ_mk` and of the apply lemmas of `inductionHomEquiv` need it.
@[expose]
def induced : Action (Type u) G :=
  letI := inducedMulAction K Z.V
  Action.ofMulAction G (BalancedProduct K G Z.V)

/-- `a` acts on the class of `(g, z)` in the induced `G`-set as `⟦g a⁻¹, z⟧`. -/
@[simp]
theorem induced_ρ_mk (a g : G) (z : Z.V) : (induced K Z).ρ a (mk K g z) = mk K (g * a⁻¹) z :=
  (rfl)

/-! ### The hom-equivalence -/

variable {K Z} {Y : Action (Type u) G}

/-- A map of `G`-sets out of the induced `G`-set satisfies the `G`-map condition of
`TauCeti.bijOn_balancedProduct_lift`. -/
theorem induced_hom_mul_inv (f : induced K Z ⟶ Y) (a g : G) (z : Z.V) :
    f.hom (mk K (g * a⁻¹) z) = a • f.hom (mk K g z) :=
  Action.hom_comm_apply f a (mk K g z)

/-- The restriction `z ↦ f ⟦1, z⟧` of a map of `G`-sets out of the induced `G`-set, as a map of
`K`-sets into the restriction of `Y`. -/
def restrictHom (f : induced K Z ⟶ Y) : Z ⟶ (Action.res (Type u) K.subtype).obj Y where
  hom := TypeCat.ofHom fun z ↦ f.hom (mk K 1 z)
  comm k := ConcreteCategory.hom_ext _ _ fun z ↦
    apply_mk_one_smul (f := fun x ↦ f.hom x) (induced_hom_mul_inv f) k z

@[simp]
theorem restrictHom_hom_apply (f : induced K Z ⟶ Y) (z : Z.V) :
    (restrictHom f).hom z = f.hom (mk K 1 z) :=
  (rfl)

/-- A map of `K`-sets into the restriction of `Y`, as a function into the points of `Y`. -/
-- The points of the restriction of `Y` are those of `Y` only up to unfolding `Action.res`, so this
-- names the function with its codomain `Y.V`, where the action of `G` is found.
@[expose] def resFun (ι : Z ⟶ (Action.res (Type u) K.subtype).obj Y) : Z.V → Y.V :=
  fun z ↦ ι.hom z

/-- A map of `K`-sets `ι` into the restriction of `Y` satisfies the `K`-map condition of
`TauCeti.bijOn_balancedProduct_lift`. -/
theorem resFun_smul (ι : Z ⟶ (Action.res (Type u) K.subtype).obj Y) (h : K) (z : Z.V) :
    resFun ι (h • z) = (h : G) • resFun ι z :=
  Action.hom_comm_apply ι h z

/-- The map of `G`-sets `⟦g, z⟧ ↦ g⁻¹ • ι z` out of the induced `G`-set induced by a map of
`K`-sets `ι` into the restriction of `Y`. -/
def liftHom (ι : Z ⟶ (Action.res (Type u) K.subtype).obj Y) : induced K Z ⟶ Y where
  hom := TypeCat.ofHom (inducedLift K Z.V Y.V (resFun_smul ι))
  comm a := ConcreteCategory.hom_ext _ _ fun x ↦ by
    induction x using BalancedProduct.ind with
    | h g z => exact inducedLift_mul_inv K Z.V Y.V (resFun_smul ι) a g z

@[simp]
theorem liftHom_hom_mk (ι : Z ⟶ (Action.res (Type u) K.subtype).obj Y) (g : G) (z : Z.V) :
    (liftHom ι).hom (mk K g z) = g⁻¹ • resFun ι z :=
  inducedLift_mk K Z.V Y.V (resFun_smul ι) g z

variable (Z Y) in
/-- **The hom-equivalence of induction and restriction**: maps of `G`-sets out of the induced
`G`-set are maps of `K`-sets into the restriction, by restriction along `z ↦ ⟦1, z⟧`, with
inverse `ι ↦ (⟦g, z⟧ ↦ g⁻¹ • ι z)`. -/
def inductionHomEquiv :
    (induced K Z ⟶ Y) ≃ (Z ⟶ (Action.res (Type u) K.subtype).obj Y) where
  toFun := restrictHom
  invFun := liftHom
  left_inv f := Action.hom_ext _ _ (ConcreteCategory.hom_ext _ _ fun x ↦ congrFun
    (eq_inducedLift (f := fun x ↦ f.hom x) (induced_hom_mul_inv f) _ fun _ ↦ rfl).symm x)
  right_inv ι := Action.hom_ext _ _ (ConcreteCategory.hom_ext _ _ fun z ↦
    inducedLift_mk_one K Z.V Y.V (resFun_smul ι) z)

@[simp]
theorem inductionHomEquiv_apply (f : induced K Z ⟶ Y) : inductionHomEquiv Z Y f = restrictHom f :=
  (rfl)

@[simp]
theorem inductionHomEquiv_symm_apply (ι : Z ⟶ (Action.res (Type u) K.subtype).obj Y) :
    (inductionHomEquiv Z Y).symm ι = liftHom ι :=
  (rfl)

/-- The hom-equivalence is natural in the `G`-set. -/
theorem inductionHomEquiv_naturality {Y' : Action (Type u) G} (g : Y ⟶ Y')
    (h : induced K Z ⟶ Y) :
    inductionHomEquiv Z Y' (h ≫ g) =
      inductionHomEquiv Z Y h ≫ (Action.res (Type u) K.subtype).map g :=
  Action.hom_ext _ _ (ConcreteCategory.hom_ext _ _ fun _ ↦ rfl)

/-! ### The functor and the adjunction -/

variable (K) in
/-- **Induction of group actions**, as a functor from `K`-sets to `G`-sets: a `K`-set goes to its
induced `G`-set, and a map of `K`-sets to the map of `G`-sets induced by it. -/
-- Exposed so that the values of the functor are the induced `G`-sets by definition: the
-- statements of `inductionFunctor_obj` and `inductionAdjunction_homEquiv` need it.
@[expose] def inductionFunctor : Action (Type u) K ⥤ Action (Type u) G :=
  Adjunction.leftAdjointOfEquiv (fun Z Y ↦ inductionHomEquiv Z Y)
    fun _ _ _ g h ↦ inductionHomEquiv_naturality g h

@[simp]
theorem inductionFunctor_obj (Z : Action (Type u) K) :
    (inductionFunctor K).obj Z = induced K Z :=
  (rfl)

variable (K) in
/-- **Induction is left adjoint to restriction**: the balanced product functor is left adjoint to
Mathlib's restriction `Action.res (Type u) K.subtype`, with hom-equivalence
`TauCeti.BalancedProduct.inductionHomEquiv`. -/
def inductionAdjunction : inductionFunctor K ⊣ Action.res (Type u) K.subtype :=
  Adjunction.adjunctionOfEquivLeft _ _

@[simp]
theorem inductionAdjunction_homEquiv (Z : Action (Type u) K) (Y : Action (Type u) G) :
    (inductionAdjunction K).homEquiv Z Y = inductionHomEquiv Z Y :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

end BalancedProduct

end TauCeti
