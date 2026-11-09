/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Module.Injective.DivisionRing
public import TauCeti.LinearAlgebra.Dual.RightAction

/-!
# The dual regular module is injective

For an algebra `A` over a commutative ring `k` and an injective `k`-module `E`, the module
`Hom_k(A, E)` is an injective left `A`-module, with action through right multiplication on `A`. For
a field and `E = k` this is the dual of the right regular module. Together with its cogenerator
property, this provides injective modules containing finite-dimensional modules, without a
self-injectivity assumption on the algebra.

The action on the dual is specified through an equivariant linear equivalence, rather than
installed as a global instance on all duals. This follows the convention of
`TauCeti.LinearAlgebra.Dual.RightAction`.

## Main results

* `LinearEquiv.moduleInjective_of_dual_regular`: `Hom_k(A, E)` is injective.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Section I.5.
-/

public section

namespace LinearEquiv

universe v

variable {k A Q : Type*} {E : Type v}

variable [CommRing k] [Small.{v} k] [Ring A] [Algebra k A] [AddCommGroup Q] [Module A Q]
  [Module k Q] [AddCommGroup E] [Module k E] [Module.Injective k E]

/-- For an injective `k`-module `E`, the module `Hom_k(A, E)`, with action
`(a • φ) x = φ (x * a)`, is an injective left module over any `k`-algebra `A`. -/
theorem moduleInjective_of_dual_regular (e : Q ≃ₗ[k] (A →ₗ[k] E))
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) :
    Module.Injective A Q := by
  have := e.isScalarTower_of_dual_regular he
  apply Module.Baer.injective
  intro I f
  -- Extend the map obtained by evaluation at the unit from the ideal to the algebra.
  let eI : I.restrictScalars k →ₗ[k] I :=
    { toFun := fun x => ⟨x, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l : I.restrictScalars k →ₗ[k] E :=
    (LinearMap.applyₗ (1 : A)).comp (e.toLinearMap.comp ((f.restrictScalars k).comp eI))
  obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property k E _ _
    (I.restrictScalars k).subtype (Submodule.injective_subtype _) l
  let g : A →ₗ[A] Q :=
    { toFun := fun a => e.symm (ψ.comp (LinearMap.mulRight k a))
      map_add' := fun a b => by apply e.injective; ext x; simp [mul_add]
      map_smul' := fun a b => by apply e.injective; ext x; simp [he, mul_assoc] }
  refine ⟨g, fun a ha => e.injective (LinearMap.ext fun x => ?_)⟩
  have hx : x * a ∈ I := I.mul_mem_left x ha
  have hf : f ⟨x * a, hx⟩ = x • f ⟨a, ha⟩ := f.map_smul x ⟨a, ha⟩
  simpa [g, l, eI, hf, he] using LinearMap.congr_fun hψ ⟨x * a, hx⟩

end LinearEquiv
