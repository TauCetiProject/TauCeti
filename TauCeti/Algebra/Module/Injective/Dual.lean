/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dual regular module is injective

For an algebra `A` over a field `k`, the dual of the right regular module is an injective
left `A`-module. Together with its cogenerator property, this provides injective modules
containing finite-dimensional modules, without a self-injectivity assumption on the algebra.

The action on the dual is specified through an equivariant linear equivalence, rather than
installed as a global instance on all duals. This follows the convention of
`TauCeti.LinearAlgebra.Dual.RightAction`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Section I.5.
-/

public section

namespace TauCeti

variable {k A Q : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup Q] [Module A Q] [Module k Q]

variable (k) in
/-- The dual of the right regular module, with action `(a • φ) x = φ (x * a)`, is an
injective left module over any algebra over a field. -/
theorem moduleInjective_of_equiv_dual_regular
    (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) :
    Module.Injective A Q := by
  let : IsScalarTower k A Q := IsScalarTower.of_algebraMap_smul fun c q => by
    apply e.injective
    ext x
    rw [he, ← Algebra.commutes, ← Algebra.smul_def]
    simp
  apply Module.Baer.injective
  intro I f
  -- Extend the functional obtained by evaluation at the unit from the ideal to the algebra.
  let eI : I.restrictScalars k →ₗ[k] I :=
    { toFun := fun x => ⟨x, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l : I.restrictScalars k →ₗ[k] k :=
    (Module.Dual.eval k A 1).comp (e.toLinearMap.comp ((f.restrictScalars k).comp eI))
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend l
  let g : A →ₗ[A] Q :=
    { toFun := fun a => e.symm (ψ.comp (LinearMap.mulRight k a))
      map_add' := fun a b => by apply e.injective; ext x; simp [mul_add]
      map_smul' := fun a b => by apply e.injective; ext x; simp [he, mul_assoc] }
  refine ⟨g, fun a ha => e.injective (LinearMap.ext fun x => ?_)⟩
  have hx : x * a ∈ I := I.mul_mem_left x ha
  have hf : f ⟨x * a, hx⟩ = x • f ⟨a, ha⟩ :=
    f.map_smul x ⟨a, ha⟩
  have hψx := LinearMap.congr_fun hψ (⟨x * a, hx⟩ : I.restrictScalars k)
  simpa [g, l, eI, hf, he] using hψx

end TauCeti
