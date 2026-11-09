/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Coinduced modules over an algebra over a field are injective

For an algebra `A` over a field `k` and a `k`-vector space `V`, the coinduced module
`Hom_k(A, V)`, with `A` acting by `(a • f) x = f (x * a)`, is an injective left `A`-module: it is
the image of the injective `k`-module `V` under the right adjoint of restriction of scalars. Taking
`V = k` recovers the injectivity of the dual of the right regular module.

As in `TauCeti.LinearAlgebra.Dual.RightAction`, the action is not installed as an instance on the
type of linear maps, which already carries the codomain-scaling module structures. The statement
takes an arbitrary left `A`-module `Q` together with a `k`-linear identification
`e : Q ≃ₗ[k] (A →ₗ[k] V)` carrying the action of `a` to precomposition with right multiplication
by `a`.

## Main results

* `LinearEquiv.moduleBaer_of_coinduced`, `LinearEquiv.moduleInjective_of_coinduced`: the coinduced
  module `Hom_k(A, V)` satisfies Baer's criterion, hence is injective.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Section 3 (injectivity of coinduced modules).
-/

public section

namespace LinearEquiv

variable {k A V Q : Type*}

variable [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [AddCommGroup Q] [Module A Q] [Module k Q]

/-- The coinduced module `Hom_k(A, V)`, with action `(a • f) x = f (x * a)`, satisfies Baer's
criterion over any algebra over a field. -/
theorem moduleBaer_of_coinduced (e : Q ≃ₗ[k] (A →ₗ[k] V))
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) :
    Module.Baer A Q := by
  have : IsScalarTower k A Q :=
    IsScalarTower.of_algebraMap_smul fun c q => e.injective <| LinearMap.ext fun x => by
      simp [he, ← Algebra.commutes, ← Algebra.smul_def]
  intro I f
  -- Extend the `k`-linear map obtained by evaluation at the unit from the ideal to the algebra.
  let eI : I.restrictScalars k →ₗ[k] I :=
    { toFun := fun x => ⟨x, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l : I.restrictScalars k →ₗ[k] V :=
    (LinearMap.applyₗ (R := k) 1).comp (e.toLinearMap.comp ((f.restrictScalars k).comp eI))
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend l
  let g : A →ₗ[A] Q :=
    { toFun := fun a => e.symm (ψ.comp (LinearMap.mulRight k a))
      map_add' := fun a b => by apply e.injective; ext x; simp [mul_add]
      map_smul' := fun a b => by apply e.injective; ext x; simp [he, mul_assoc] }
  refine ⟨g, fun a ha => e.injective (LinearMap.ext fun x => ?_)⟩
  have hx : x * a ∈ I := I.mul_mem_left x ha
  have hf : f ⟨x * a, hx⟩ = x • f ⟨a, ha⟩ := f.map_smul x ⟨a, ha⟩
  simpa [g, l, eI, hf, he] using LinearMap.congr_fun hψ ⟨x * a, hx⟩

/-- **Coinduced modules are injective.** The coinduced module `Hom_k(A, V)`, with action
`(a • f) x = f (x * a)`, is an injective left module over any algebra `A` over a field `k`. -/
theorem moduleInjective_of_coinduced (e : Q ≃ₗ[k] (A →ₗ[k] V))
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) :
    Module.Injective A Q :=
  (e.moduleBaer_of_coinduced he).injective

end LinearEquiv
