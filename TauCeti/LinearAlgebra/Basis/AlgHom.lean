/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Extending characters along basis-preserving maps

Let `f : k →+* k'` be a ring homomorphism of commutative semirings and `F : A →+* A'` a ring
homomorphism from a `k`-algebra to a `k'`-algebra that is compatible with `f` on scalars and carries
a `k`-basis of `A` to a `k'`-basis of `A'`. Every `k`-algebra homomorphism `A → k` then extends
uniquely to a `k'`-algebra homomorphism `A' → k'`: it is the `k'`-linear map with the transported
values on the basis, and it is multiplicative because the two bilinear maps `(x, y) ↦ ψ (x * y)` and
`(x, y) ↦ ψ x * ψ y` agree on pairs of basis vectors.

## Main results

* `TauCeti.existsUnique_algHom_comp_eq_of_basis`: the unique extension `φ'` with
  `φ' (F x) = f (φ x)`.
-/

public section

namespace TauCeti

variable {k k' A A' ι : Type*} [CommSemiring k] [CommSemiring k'] [Semiring A] [Algebra k A]
  [Semiring A'] [Algebra k' A']

/-- **Extending a character along a basis-preserving map.** Let `f : k →+* k'` be a ring
homomorphism, `F : A →+* A'` a ring homomorphism with `F(algebraMap r) = algebraMap (f r)`,
carrying a `k`-basis `v` of `A` to a `k'`-basis `v'` of `A'`. Every `k`-algebra homomorphism
`φ : A → k` extends to a unique `k'`-algebra homomorphism `φ' : A' → k'` with
`φ'(F x) = f(φ(x))`: `φ'` takes the value `f(φ(v i))` at `v' i`. -/
theorem existsUnique_algHom_comp_eq_of_basis (f : k →+* k') (F : A →+* A')
    (hF : ∀ r, F (algebraMap k A r) = algebraMap k' A' (f r)) (v : Module.Basis ι k A)
    (v' : Module.Basis ι k' A') (hv : ∀ i, F (v i) = v' i) (φ : A →ₐ[k] k) :
    ∃! φ' : A' →ₐ[k'] k', ∀ x, φ' (F x) = f (φ x) := by
  classical
  let ψ : A' →ₗ[k'] k' := v'.constr k' fun i => f (φ (v i))
  have hψv (i : ι) : ψ (v' i) = f (φ (v i)) := v'.constr_basis k' _ i
  -- `ψ ∘ F = f ∘ φ`, checked on `x = ∑ᵢ xᵢ v i`, the sum being finite.
  have hψF (x : A) : ψ (F x) = f (φ x) := by
    have hFs (c : k) (a : A) : F (c • a) = f c • F a := by
      rw [Algebra.smul_def, map_mul, hF, Algebra.smul_def]
    rw [← v.linearCombination_repr x]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, hFs, hv, hψv]
  have hmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    -- Both sides are `k'`-bilinear in `(x, y)`; compare them on the basis `v'`.
    have h := v'.ext fun i => v'.ext fun j => (show
      ((LinearMap.mul k' A').compr₂ ψ) (v' i) (v' j) =
        ((LinearMap.mul k' k').compl₁₂ ψ ψ) (v' i) (v' j) by
      simp [← hv, ← map_mul, hψF])
    exact fun x y => LinearMap.congr_fun₂ h x y
  have hone : ψ 1 = 1 := by
    rw [← map_one F, hψF, map_one, map_one]
  -- Any other extension agrees with `ψ` on the basis `v' i = F (v i)`.
  refine ⟨AlgHom.ofLinearMap ψ hone hmul, hψF, fun φ'' hφ'' => ?_⟩
  exact AlgHom.toLinearMap_injective (v'.ext fun i => by simp [← hv, hφ'', hψF])

end TauCeti
