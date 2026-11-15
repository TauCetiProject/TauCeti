/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Numerical

/-!
# The Euler form between projective and finitely generated modules

Let `A` be a finite-dimensional algebra over a field `k`. A finitely generated projective
`A`-module `P` has no higher `Ext`, and its Hom space into a finitely generated module `M` is
finite-dimensional. Hence every such pair is Euler-admissible, with
`χ(P, M) = dim_k Hom_A(P, M)`, and the Ext-Euler characteristic descends to a bilinear form

```text
χ : K₀(proj A) × G₀(mod A) ⟶ ℤ
```

on the two Grothendieck groups between which the Cartan map `TauCeti.cartanMap` runs. No
finiteness of the global dimension is needed: only projectives occur in the first argument. This
is the ungraded counterpart of `TauCeti.gradedProjectiveExtEuler`.

## Main definitions

* `TauCeti.projectiveExtEuler`: the Euler form `K₀(proj A) × G₀(mod A) → ℤ`.

## Main results

* `TauCeti.isEulerAdmissibleOn_finiteProjectiveModules_isFG`: finitely generated projectives and
  finitely generated modules form Euler-admissible pairs.
* `TauCeti.projectiveExtEuler_of_of`: on classes, the form is the Hom dimension
  `dim_k Hom_A(P, M)`.
* `TauCeti.extEulerPairing_cartanMap`: when every pair of finitely generated modules is
  Euler-admissible, the Ext-Euler pairing of `G₀(mod A)` with itself, evaluated on the Cartan image
  of a projective class `x`, is `χ(x, -)`.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the Euler form of a finite-dimensional
  algebra and its evaluation on projectives.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

variable (k : Type*) [Field k] (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]

/-- Over a finite-dimensional algebra, a finitely generated projective module and a finitely
generated module form an Euler-admissible pair: the projective has no higher `Ext`, and the Hom
space between two finitely generated modules is finite-dimensional. -/
theorem isEulerAdmissibleOn_finiteProjectiveModules_isFG :
    IsEulerAdmissibleOn.{u} k (finiteProjectiveModules A) (ModuleCat.isFG A) :=
  isEulerAdmissibleOn_of_projective k (finiteProjectiveModules_le_categoryTheory_isProjective A)
    fun X Y hX hY ↦
      have : Module.Finite A X := (finiteProjectiveModules_iff.mp hX).1
      have : Module.Finite A Y := (ModuleCat.isFG_iff Y).mp hY
      inferInstance

/-- **The Euler form between projective and finitely generated modules**,
`K₀(proj A) × G₀(mod A) → ℤ`. Its value on two classes is the Ext-Euler characteristic, which is
the Hom dimension `dim_k Hom_A(P, M)` by `TauCeti.projectiveExtEuler_of_of`. -/
noncomputable def projectiveExtEuler :
    ExactK0.{u} (finiteProjectiveModulesExactStructure A) →ₗ[ℤ]
      ExactK0.{u} (finiteModulesExactStructure A) →ₗ[ℤ] ℤ :=
  (extEulerBilinear _ (isExtensionClosed_finiteModules A)
      (isEulerAdmissibleOn_finiteProjectiveModules_isFG k A)).compl₁₂
    (finiteProjectiveModulesExactK0Equiv A).toIntLinearEquiv.toLinearMap
    (finiteModulesExactK0Equiv A).toIntLinearEquiv.toLinearMap

/-- The Euler form is the Ext-Euler pairing of the two extension-closed subcategories of
`ModuleCat A`, read through `TauCeti.finiteProjectiveModulesExactK0Equiv` and
`TauCeti.finiteModulesExactK0Equiv`. -/
theorem projectiveExtEuler_apply (x : ExactK0.{u} (finiteProjectiveModulesExactStructure A))
    (y : ExactK0.{u} (finiteModulesExactStructure A)) :
    projectiveExtEuler k A x y =
      extEulerPairing _ (isExtensionClosed_finiteModules A)
        (isEulerAdmissibleOn_finiteProjectiveModules_isFG k A)
        (finiteProjectiveModulesExactK0Equiv A x) (finiteModulesExactK0Equiv A y) := by
  simp only [projectiveExtEuler, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    AddEquiv.coe_toIntLinearEquiv, extEulerBilinear_apply]

/-- **The Euler form on classes is the Hom dimension**: `χ([P], [M]) = dim_k Hom_A(P, M)` for a
finitely generated projective `P` and a finitely generated module `M`. -/
@[simp]
theorem projectiveExtEuler_of_of (P : (finiteProjectiveModules A).FullSubcategory)
    (M : FGModuleCat.{u} A) :
    projectiveExtEuler k A (ExactK0.of P) (ExactK0.of M) =
      Module.finrank k (P.obj →ₗ[A] M.obj) := by
  have : Projective P.obj := finiteProjectiveModules_le_categoryTheory_isProjective A _ P.property
  rw [projectiveExtEuler_apply, finiteProjectiveModulesExactK0Equiv_of,
    finiteModulesExactK0Equiv_of, extEulerPairing_of_of, extEuler_projective,
    (ModuleCat.homLinearEquiv (S := k)).finrank_eq]

/-- **The Euler form is compatible with the Cartan map**: if every pair of finitely generated
modules is Euler-admissible, then the Ext-Euler pairing of `G₀(mod A)` with itself, evaluated on
the Cartan image of a projective class `x` and on a module class `y`, is `χ(x, y)`. -/
@[simp]
theorem extEulerPairing_cartanMap
    (h : IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A))
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure A))
    (y : ExactK0.{u} (finiteModulesExactStructure A)) :
    extEulerPairing (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A) h
        (finiteModulesExactK0Equiv A (cartanMap A x)) (finiteModulesExactK0Equiv A y) =
      projectiveExtEuler k A x y := by
  induction x using ExactK0.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, LinearMap.neg_apply, hx]
  | of P =>
    induction y using ExactK0.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
    | of M =>
      rw [cartanMap_of, finiteModulesExactK0Equiv_of, finiteModulesExactK0Equiv_of,
        extEulerPairing_of_of, projectiveExtEuler_apply, finiteProjectiveModulesExactK0Equiv_of,
        finiteModulesExactK0Equiv_of, extEulerPairing_of_of]

end TauCeti
