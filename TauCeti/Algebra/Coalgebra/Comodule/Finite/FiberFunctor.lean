/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Preadditive
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Symmetric

/-!
# The fibre functor on finitely generated comodules

This file constructs the forgetful functor from finitely generated right comodules over a
coalgebra `C` over a commutative ring `R` to Mathlib's category `FGModuleCat R` of finitely
generated `R`-modules, and records the properties that make it a fibre functor:

* it is faithful, additive and `R`-linear;
* it preserves finite limits and finite colimits when `R` is Noetherian and `C` is flat over `R`,
  so in particular over a field;
* it is monoidal when `C` is a bialgebra, and braided when `C` is moreover commutative, for the
  full monoidal and braided subcategory structures of `FGModuleCat R` inside `ModuleCat R`.

Pulling back along this faithful monoidal functor makes the monoidal category of finite comodules
over a bialgebra monoidal preadditive and monoidal `R`-linear.

Together with the abelian, symmetric and rigid structures, essential smallness
(`TauCeti.FGComoduleCat.essentiallySmall`) and the identification of the endomorphisms of the
tensor unit with the scalars (`TauCeti.FGComoduleCat.smul_id_tensorUnit_bijective`), this exhibits
finite-dimensional comodules over a commutative Hopf algebra over a field, with their underlying
vector spaces, as a neutral Tannakian category with a fibre functor.

## Main declarations

* `TauCeti.FGComoduleCat.hasForgetToFGModuleCat`: the forgetful functor to `FGModuleCat R`.
* `TauCeti.FGComoduleCat.forget₂_fgModuleCat_obj` and `forget₂_fgModuleCat_map`: its values on
  objects and morphisms.
* `TauCeti.FGComoduleCat.instMonoidalForget₂FGModuleCat` and
  `TauCeti.FGComoduleCat.instBraidedForget₂FGModuleCat`: the monoidal and braided structures of
  the forgetful functor.
* `TauCeti.FGComoduleCat.forget₂_fgModuleCat_μ_apply` and its companions for `ε`, `δ` and `η`:
  the comparison maps of the monoidal structure are identities on underlying elements.
* `TauCeti.FGComoduleCat.instMonoidalPreadditive` and `TauCeti.FGComoduleCat.instMonoidalLinear`:
  tensor products of morphisms are additive and `R`-linear in each variable.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900 (1982), §2, Definition 2.19.
-/

public section

open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v w

section Coalgebra

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Forget a finitely generated comodule to its underlying finitely generated module. -/
noncomputable instance hasForgetToFGModuleCat :
    HasForget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R) where
  forget₂ := (ModuleCat.isFG R).lift (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R))
    fun M => (ModuleCat.isFG_iff _).2 (inferInstanceAs (Module.Finite R M))
  forget_comp := rfl

/-- The underlying module of a finite comodule is its image under the forgetful functor to
`FGModuleCat R`, followed by the inclusion into `ModuleCat R`. -/
@[simp]
theorem forget₂_fgModuleCat_obj (M : FGComoduleCat.{u, v, w} R C) :
    ((forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)).obj M).obj =
      (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).obj M :=
  (rfl)

/-- The forgetful functor to `FGModuleCat R` sends a comodule morphism to its underlying linear
map. -/
@[simp]
theorem forget₂_fgModuleCat_map {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    ((forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)).map f).hom =
      (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).map f :=
  (rfl)

instance : (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)).Faithful :=
  inferInstanceAs ((ModuleCat.isFG R).lift _ _).Faithful

instance : (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)).Additive where
  map_add := rfl

instance : (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)).Linear R where
  map_smul _ _ := rfl

/-- The forgetful functor from finite comodules to finite modules preserves finite colimits. -/
instance : PreservesFiniteColimits (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)) :=
  -- The inclusion `FGModuleCat R ⥤ ModuleCat R` is fully faithful, hence reflects colimits.
  have : PreservesFiniteColimits
      (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R) ⋙ (ModuleCat.isFG R).ι) :=
    inferInstanceAs
      (PreservesFiniteColimits (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)))
  preservesFiniteColimits_of_reflects_of_preserves _ (ModuleCat.isFG R).ι

variable [IsNoetherianRing R] [Module.Flat R C]

/-- Over a Noetherian base and a flat coalgebra, the forgetful functor from finite comodules to
finite modules preserves finite limits. -/
instance : PreservesFiniteLimits (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R)) :=
  -- The inclusion `FGModuleCat R ⥤ ModuleCat R` is fully faithful, hence reflects limits.
  have : PreservesFiniteLimits
      (forget₂ (FGComoduleCat.{u, v, w} R C) (FGModuleCat.{w} R) ⋙ (ModuleCat.isFG R).ι) :=
    inferInstanceAs
      (PreservesFiniteLimits (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)))
  preservesFiniteLimits_of_reflects_of_preserves _ (ModuleCat.isFG R).ι

end Coalgebra

section Bialgebra

variable {R : Type u} [CommRing R]
variable {C : Type v} [Semiring C] [Bialgebra R C]

/-- The forgetful functor from finite comodules over a bialgebra to finite modules is monoidal.
The comparison maps are identities on underlying modules: the unit comparison is the identity
of `R` and the tensor comparison is the identity of `M ⊗[R] N`. -/
noncomputable instance instMonoidalForget₂FGModuleCat :
    (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R)).Monoidal :=
  -- The comparison maps are identity linear equivalences, but not identity isomorphisms: the
  -- additive group on a forgotten comodule is `Module.addCommMonoidToAddCommGroup`, whose
  -- negation is not definitionally that of the module category's tensor unit and products.
  Functor.CoreMonoidal.toMonoidal
    { εIso := ObjectProperty.isoMk _
        (LinearEquiv.toModuleIso (g₂ := Module.addCommMonoidToAddCommGroup R)
          (LinearEquiv.refl R R))
      μIso M N := ObjectProperty.isoMk _ (LinearEquiv.refl R (M ⊗[R] N)).toModuleIso
      μIso_hom_natural_left _ _ := by
        ext1
        exact TensorProduct.ext' fun _ _ => rfl
      μIso_hom_natural_right _ _ := by
        ext1
        exact TensorProduct.ext' fun _ _ => rfl
      associativity _ _ _ := by
        ext1
        exact TensorProduct.ext_threefold fun x y z => associator_hom_apply x y z
      left_unitality _ := by
        ext1
        exact TensorProduct.ext' fun r x => (leftUnitor_hom_apply r x).symm
      right_unitality _ := by
        ext1
        exact TensorProduct.ext' fun x r => (rightUnitor_hom_apply x r).symm }

/-- The unit comparison of the forgetful functor to `FGModuleCat R` is the identity of `R`. -/
@[simp]
theorem forget₂_fgModuleCat_ε_apply (r : R) :
    Functor.LaxMonoidal.ε (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R)) r = r :=
  (rfl)

/-- The inverse unit comparison of the forgetful functor to `FGModuleCat R` is the identity
of `R`. -/
@[simp]
theorem forget₂_fgModuleCat_η_apply (r : R) :
    Functor.OplaxMonoidal.η (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R)) r = r :=
  (rfl)

/-- The tensor comparison of the forgetful functor to `FGModuleCat R` is the identity on pure
tensors. -/
@[simp]
theorem forget₂_fgModuleCat_μ_apply (M N : FGComoduleCat.{u, v, u} R C) (m : M) (n : N) :
    Functor.LaxMonoidal.μ (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R)) M N
      (m ⊗ₜ[R] n) = m ⊗ₜ[R] n :=
  (rfl)

/-- The inverse tensor comparison of the forgetful functor to `FGModuleCat R` is the identity on
pure tensors. -/
@[simp]
theorem forget₂_fgModuleCat_δ_apply (M N : FGComoduleCat.{u, v, u} R C) (m : M) (n : N) :
    Functor.OplaxMonoidal.δ (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R)) M N
      (m ⊗ₜ[R] n) = m ⊗ₜ[R] n :=
  (rfl)

/-- The tensor product of morphisms of finite comodules over a bialgebra is additive in each
variable. -/
instance instMonoidalPreadditive : MonoidalPreadditive (FGComoduleCat.{u, v, u} R C) :=
  monoidalPreadditive_of_faithful (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R))

/-- The tensor product of morphisms of finite comodules over a bialgebra is `R`-linear in each
variable. -/
instance instMonoidalLinear : MonoidalLinear R (FGComoduleCat.{u, v, u} R C) :=
  MonoidalLinear.ofFaithful R (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R))

end Bialgebra

section CommBialgebra

variable {R : Type u} [CommRing R]
variable {C : Type v} [CommSemiring C] [Bialgebra R C]

/-- The forgetful functor from finite comodules over a commutative bialgebra to finite modules
is braided: it sends the tensor-product swap of comodules to the tensor-product swap of
modules. -/
noncomputable instance instBraidedForget₂FGModuleCat :
    (forget₂ (FGComoduleCat.{u, v, u} R C) (FGModuleCat.{u} R)).Braided where
  braided _ _ := by
    ext1
    exact TensorProduct.ext' fun x y => braiding_hom_apply x y

end CommBialgebra

end TauCeti.FGComoduleCat
