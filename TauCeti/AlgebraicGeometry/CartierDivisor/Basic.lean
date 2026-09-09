/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.CategoryTheory.Sites.Units
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Cartier divisors on an integral scheme

Let `X` be an integral scheme and let `𝒦_X` be its sheaf of rational functions. The Cartier
divisor sheaf is the quotient

`𝒦_X^× / 𝒪_X^×`,

and a Cartier divisor is a global section of this quotient sheaf. The quotient is a sheaf
quotient, not the pointwise quotient of groups of sections: its sections are represented locally
by nonzero rational functions, with two representatives identified when their ratio is a regular
unit.

## Main declarations

* `Scheme.regularUnitSheaf` and `Scheme.rationalUnitSheaf` are the sheaves of units of `𝒪_X` and
  `𝒦_X`, written additively;
* `Scheme.toRationalUnitSheaf` is the monomorphism `𝒪_X^× ⟶ 𝒦_X^×`;
* `Scheme.cartierDivisorSheaf` is its cokernel in sheaves of abelian groups;
* `Scheme.CartierDivisor` is the additive group of global sections of that cokernel;
* `Scheme.rationalUnitClass` sends a nonzero rational function to its class in the
  Cartier-divisor sheaf over a nonempty open subset, its *local equation* there;
* `Scheme.principalCartierDivisor` sends a nonzero rational function to its principal Cartier
  divisor, the case of the whole space.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Cartier divisors; the
dictionaries `Cartier ≃ line bundles` and (smooth curve) `Weil ≃ Cartier`". The rational-function
sheaf was constructed in `TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean`; the next step
is to construct `𝒪_X(D)` from a Cartier divisor and prove the Cartier--line-bundle dictionary.

The definition follows the Stacks Project, *Divisors* (Tag 02AR). No formalization is vendored.
The sheaf quotient is Mathlib's categorical cokernel in the abelian category of sheaves of
abelian groups.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The sheaf `𝒪_X^×` of regular units, regarded as a sheaf of additive commutative groups. -/
noncomputable abbrev regularUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj X.sheaf

/-- The sheaf `𝒦_X^×` of nonzero rational functions, regarded as a sheaf of additive
commutative groups. -/
noncomputable abbrev rationalUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj
    (rationalFunctionsRing X)

/-- The inclusion `𝒪_X^× ⟶ 𝒦_X^×` of regular units into nonzero rational functions. -/
def toRationalUnitSheaf : regularUnitSheaf X ⟶ rationalUnitSheaf X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).map
    (toRationalFunctionsRing X)

/-- The inclusion of regular units into rational units is injective on sections over every open
subset of an integral scheme. -/
theorem toRationalUnitSheaf_app_injective (U : X.Opens) :
    Function.Injective ((toRationalUnitSheaf X).hom.app (op U)) := by
  intro f g h
  apply Additive.toMul.injective
  apply Units.map_injective (toRationalFunctionsRing_app_injective U)
  exact congrArg Additive.toMul h

/-- The inclusion `𝒪_X^× ⟶ 𝒦_X^×` of regular units into rational units is a
monomorphism. -/
instance : Mono (toRationalUnitSheaf X) := by
  have hU : ∀ U : (Opens X)ᵒᵖ, Mono ((toRationalUnitSheaf X).hom.app U) := fun U ↦
    ConcreteCategory.mono_of_injective _ (toRationalUnitSheaf_app_injective X U.unop)
  have : Mono (toRationalUnitSheaf X).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ (toRationalUnitSheaf X)

/-- The Cartier-divisor sheaf `𝒦_X^× / 𝒪_X^×`. This is the cokernel in the category of sheaves
of abelian groups, and hence is the sheafification of the pointwise quotient presheaf.

Use Mathlib's generic `cokernel.desc`, `cokernel.π_desc`, and cancellation through
`cokernel.π` for its universal property. -/
def cartierDivisorSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  cokernel (toRationalUnitSheaf X)

/-- The quotient projection `𝒦_X^× ⟶ 𝒦_X^× / 𝒪_X^×`. -/
def toCartierDivisorSheaf : rationalUnitSheaf X ⟶ cartierDivisorSheaf X :=
  cokernel.π (toRationalUnitSheaf X)

/-- The quotient projection to the Cartier-divisor sheaf is an epimorphism. -/
instance : Epi (toCartierDivisorSheaf X) := by
  dsimp only [toCartierDivisorSheaf]
  exact Cofork.IsColimit.epi (colimit.isColimit _)

/-- A regular unit has zero class in the Cartier-divisor sheaf. -/
@[reassoc (attr := simp)]
lemma toRationalUnitSheaf_comp_toCartierDivisorSheaf :
    toRationalUnitSheaf X ≫ toCartierDivisorSheaf X = 0 :=
  cokernel.condition (toRationalUnitSheaf X)

/-- The sequence from regular units to rational units and then to Cartier divisors is exact. -/
theorem exact_toRationalUnitSheaf_toCartierDivisorSheaf :
    (ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
      (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)).Exact :=
  ShortComplex.exact_cokernel (toRationalUnitSheaf X)

/-- The group of Cartier divisors on `X`, defined as the global sections of
`𝒦_X^× / 𝒪_X^×`. -/
abbrev CartierDivisor : Type u :=
  ((cartierDivisorSheaf X).obj.obj (op (⊤ : X.Opens)) : Type u)

/-- The map on global sections induced by the quotient projection from `𝒦_X^×` to the
Cartier-divisor sheaf. Its source is the group of units of `Γ(X, 𝒦_X)`, written additively. -/
def toCartierDivisor :
    Additive (((rationalFunctionsRing X).presheaf.obj (op (⊤ : X.Opens)))ˣ) →+
      CartierDivisor X :=
  ((toCartierDivisorSheaf X).hom.app (op (⊤ : X.Opens))).hom

/-- A global regular unit maps to zero under the quotient map to Cartier divisors. -/
@[simp]
lemma toRationalUnitSheaf_app_comp_toCartierDivisor :
    (toCartierDivisor X).comp
        ((toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens))).hom = 0 := by
  have h :
      (toRationalUnitSheaf X).hom ≫ (toCartierDivisorSheaf X).hom = 0 :=
    congrArg (fun f => f.hom) (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
  have h :
      (toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens)) ≫
          (toCartierDivisorSheaf X).hom.app (op (⊤ : X.Opens)) = 0 :=
    congrArg (fun f => f.app (op (⊤ : X.Opens))) h
  have h := congrArg (fun f => f.hom) h
  exact h

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstanceAs (Nonempty X)), by simp⟩⟩

/-- Over a nonempty open subset, the units of the rational-function sheaf are the units of the
function field. -/
def rationalUnitSectionsEquiv (U : X.Opens) [Nonempty U] :
    Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ) ≃+
      Additive X.functionFieldˣ := by
  exact (Units.mapEquiv (rationalFunctionsRingEquiv U).toMulEquiv).toAdditive

/-- The rational-unit equivalence applies the rational-functions equivalence to a unit. -/
@[simp]
lemma rationalUnitSectionsEquiv_apply (U : X.Opens) [Nonempty U]
    (f : ((rationalFunctionsRing X).presheaf.obj (op U))ˣ) :
    rationalUnitSectionsEquiv X U (Additive.ofMul f) =
      Additive.ofMul (Units.map
        (rationalFunctionsRingEquiv U).toMonoidHom f) := by
  rfl

/-- The homomorphism from regular units on `U` to units of the function field induced by the
germ map at the generic point. -/
noncomputable def regularUnitToFunctionField (U : X.Opens) [Nonempty U] :
    ((X.presheaf.obj (op U)) : Type u)ˣ →* X.functionFieldˣ := by
  exact Units.map (X.germToFunctionField U).hom.toMonoidHom

/-- The map on regular units applies the germ map to the underlying section. -/
@[simp]
lemma regularUnitToFunctionField_apply (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    regularUnitToFunctionField X U f =
      Units.map (X.germToFunctionField U).hom.toMonoidHom f := by
  rfl

/-- The equivalence from rational units to function-field units carries the image of a regular
unit to the unit induced by its germ in the function field. -/
lemma rationalUnitSectionsEquiv_toRationalUnitSheaf_app (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    rationalUnitSectionsEquiv X U
        (((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f)) =
      Additive.ofMul (regularUnitToFunctionField X U f) := by
  have hunit :
      ((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f) =
        Additive.ofMul (Units.map
          ((toRationalFunctionsRing X).hom.app
            (op U)).hom.toMonoidHom f) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_map_app_apply
      (Opens.grothendieckTopology X) (toRationalFunctionsRing X)
        (op U) (Additive.ofMul f)
  rw [hunit, rationalUnitSectionsEquiv_apply, regularUnitToFunctionField_apply]
  apply congrArg Additive.ofMul
  apply Units.ext
  simp only [Units.coe_map]
  -- The units API exposes underlying values, while the rational-functions comparison
  -- theorems use the definitionally equal module-sheaf section type.
  change rationalFunctionsRingEquiv U
      ((toRationalFunctionsRing X).hom.app (op U) (f : Γ(X, U))) =
    X.germToFunctionField U f
  rw [← toRationalFunctionsRing_app, ← rationalFunctionsEquiv_apply,
    rationalFunctionsEquiv_toRationalFunctions_app]

/-- The class in the Cartier-divisor sheaf over a nonempty open subset `U` of a nonzero rational
function, regarded as a local equation there. The multiplicative group of the function field is
written additively in the domain. -/
def rationalUnitClass (U : X.Opens) [Nonempty U] :
    Additive X.functionFieldˣ →+ ((cartierDivisorSheaf X).obj.obj (op U) : Type u) :=
  (((toCartierDivisorSheaf X).hom.app (op U)).hom).comp
    (rationalUnitSectionsEquiv X U).symm.toAddMonoidHom

/-- Evaluating the rational-unit class applies the quotient map to the corresponding rational
unit section. -/
lemma rationalUnitClass_apply (U : X.Opens) [Nonempty U] (g : Additive X.functionFieldˣ) :
    rationalUnitClass X U g = ((toCartierDivisorSheaf X).hom.app (op U)).hom
      ((rationalUnitSectionsEquiv X U).symm g) :=
  AddMonoidHom.comp_apply _ _ _

/-- Restricting a rational unit to a smaller nonempty open subset does not change the underlying
nonzero rational function. -/
@[simp]
lemma rationalUnitSectionsEquiv_symm_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (g : Additive X.functionFieldˣ) :
    TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj)
        ((rationalUnitSectionsEquiv X U).symm g) V h =
      (rationalUnitSectionsEquiv X V).symm g := by
  apply (rationalUnitSectionsEquiv X V).injective
  rw [AddEquiv.apply_symm_apply]
  set t := (rationalUnitSectionsEquiv X U).symm g with ht
  have hgt : rationalUnitSectionsEquiv X U t = g := by
    rw [ht, AddEquiv.apply_symm_apply]
  have hgt' : g = Additive.ofMul (Units.map
      (rationalFunctionsRingEquiv U).toMonoidHom (Additive.toMul t)) := by
    rw [← hgt]
    exact rationalUnitSectionsEquiv_apply X U (Additive.toMul t)
  -- Restricting a unit of the rational-function sheaf restricts its underlying section.
  have hrestrict :
      TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj) t V h =
        Additive.ofMul (Units.map
          ((rationalFunctionsRing X).presheaf.map (homOfLE h).op).hom.toMonoidHom
            (Additive.toMul t)) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_obj_map_apply
      (Opens.grothendieckTopology X) (rationalFunctionsRing X) (homOfLE h).op t
  rw [hrestrict, hgt', rationalUnitSectionsEquiv_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  simp

/-- The class of a nonzero rational function commutes with restriction to a smaller nonempty
open subset: a local equation stays a local equation. -/
@[simp]
lemma rationalUnitClass_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (g : Additive X.functionFieldˣ) :
    rationalUnitClass X U g |_ V = rationalUnitClass X V g := by
  rw [rationalUnitClass_apply]
  calc
    _ = ((toCartierDivisorSheaf X).hom.app (op V)).hom
          (TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj)
            ((rationalUnitSectionsEquiv X U).symm g) V h) :=
      (TopCat.Presheaf.map_restrict (toCartierDivisorSheaf X).hom h _).symm
    _ = _ := by rw [rationalUnitSectionsEquiv_symm_restrict, ← rationalUnitClass_apply]

/-- A regular unit on `U` has zero Cartier-divisor class over `U`. -/
@[simp]
lemma rationalUnitClass_germToFunctionField_eq_zero (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    rationalUnitClass X U
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom f)) = 0 := by
  have hsymm :
      (rationalUnitSectionsEquiv X U).symm
          (Additive.ofMul (regularUnitToFunctionField X U f)) =
        ((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f) := by
    apply (rationalUnitSectionsEquiv X U).injective
    rw [AddEquiv.apply_symm_apply]
    exact (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U f).symm
  have hzero :
      ((toCartierDivisorSheaf X).hom.app (op U)).hom
        (((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f)) = 0 := by
    have hcomp := toRationalUnitSheaf_comp_toCartierDivisorSheaf X
    have happ := congrArg (fun k ↦ k.hom.app (op U)) hcomp
    exact ConcreteCategory.congr_hom happ (Additive.ofMul f)
  refine (congrArg (rationalUnitClass X U)
    (congrArg Additive.ofMul (regularUnitToFunctionField_apply X U f).symm)).trans ?_
  rw [rationalUnitClass_apply, hsymm]
  exact hzero

/-- A nonzero rational function determines its principal Cartier divisor. The multiplicative
group of the function field is written additively in the domain. -/
def principalCartierDivisorAddHom : Additive X.functionFieldˣ →+ CartierDivisor X :=
  rationalUnitClass X ⊤

/-- The principal Cartier divisor of a nonzero rational function. -/
def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  principalCartierDivisorAddHom X (Additive.ofMul f)

/-- The principal Cartier divisor of one is zero. -/
@[simp]
lemma principalCartierDivisor_one : principalCartierDivisor X 1 = 0 :=
  map_zero (principalCartierDivisorAddHom X)

/-- The principal Cartier divisor of a product is the sum of the principal Cartier divisors. -/
@[simp]
lemma principalCartierDivisor_mul (f g : X.functionFieldˣ) :
    principalCartierDivisor X (f * g) =
      principalCartierDivisor X f + principalCartierDivisor X g :=
  map_add (principalCartierDivisorAddHom X) (Additive.ofMul f) (Additive.ofMul g)

/-- The principal Cartier divisor of an inverse is the negation of the principal Cartier
divisor. -/
@[simp]
lemma principalCartierDivisor_inv (f : X.functionFieldˣ) :
    principalCartierDivisor X f⁻¹ = -principalCartierDivisor X f :=
  map_neg (principalCartierDivisorAddHom X) (Additive.ofMul f)

/-- A global regular unit has zero principal Cartier divisor. -/
@[simp]
lemma principalCartierDivisor_regularUnitToFunctionField
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    principalCartierDivisor X
      (Units.map (X.germToFunctionField (⊤ : X.Opens)).hom f) = 0 :=
  rationalUnitClass_germToFunctionField_eq_zero X ⊤ f

/-- Restricting a principal Cartier divisor to a nonempty open subset gives the class of the same
rational function there: a principal divisor has a global equation. -/
@[simp]
lemma principalCartierDivisorAddHom_restrict (g : Additive X.functionFieldˣ) (U : X.Opens)
    [Nonempty U] :
    (principalCartierDivisorAddHom X g) |_ U = rationalUnitClass X U g :=
  rationalUnitClass_restrict X le_top g

/-- Restricting a principal Cartier divisor to a nonempty open subset gives the class of the same
rational function there. -/
@[simp]
lemma principalCartierDivisor_restrict (f : X.functionFieldˣ) (U : X.Opens) [Nonempty U] :
    (principalCartierDivisor X f) |_ U = rationalUnitClass X U (Additive.ofMul f) :=
  principalCartierDivisorAddHom_restrict X (Additive.ofMul f) U

end Scheme

end

end AlgebraicGeometry

end TauCeti
