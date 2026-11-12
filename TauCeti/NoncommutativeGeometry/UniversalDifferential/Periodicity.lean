/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.ExteriorProduct
public import TauCeti.RingTheory.CyclicCohomology.GroundRing

/-!
# Normalization of Connes' periodicity operator via the exterior product

On a commutative ground ring `k`, the calibrated scalar cyclic `2m`-cocycle
`σₘ(a₀, …, a₂ₘ) = m! a₀ ⋯ a₂ₘ` (`TauCeti.scalarCocycle`) satisfies `σ₀(a₀) = a₀`,
`σ₁(a₀, a₁, a₂) = a₀ a₁ a₂`, and `S(σₘ) = σₘ₊₁` (`TauCeti.cyclicCocyclesPeriodicity_scalarCocycle`).

For any (possibly nonunital) `k`-algebra `A` and any cyclic `p`-cocycle `φ` on `A` with values in a
`k`-module `M`, taking the exterior product `φ # σ₁` (`TauCeti.exteriorProductCocycle`) and
restricting along `a ↦ a ⊗ 1 : A → A ⊗[k] k` recovers `TauCeti.cyclicCocyclesPeriodicity` on the
nose:

`(φ # σ₁)(a₀ ⊗ 1, …, aₚ₊₂ ⊗ 1) = (S φ)(a₀, …, aₚ₊₂) ⊗ 1`.

Likewise `(φ # σ₀)(a₀ ⊗ 1, …, aₚ ⊗ 1) = φ(a₀, …, aₚ) ⊗ 1`. Together with `S(σₘ) = σₘ₊₁`, this pins
down the normalization of Connes' periodicity operator `S` by `φ ↦ φ # σ₁` with
`σ₁(1, 1, 1) = 1`.

## Main results

* `TauCeti.exteriorProductCocycle_scalarCocycle_zero_apply_tmul_one`:
  `(φ # σ₀)(a₀ ⊗ 1, …, aₚ ⊗ 1) = φ(a₀, …, aₚ) ⊗ 1`.
* `TauCeti.exteriorProductCocycle_scalarCocycle_one_apply_tmul_one` and
  `TauCeti.rid_comp_exteriorProductCocycle_scalarCocycle_one`: `φ # σ₁` restricted along
  `a ↦ a ⊗ 1` equals `S φ`.

## References

* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II, §1,
  Corollary 15.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.γ.
* J.-L. Loday, *Cyclic Homology*, §2.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

section ExteriorProduct

variable {k A M : Type*} [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
  [SMulCommClass k A A] [AddCommGroup M] [Module k M] {p : ℕ}

/-- **Exterior product with `σ₀`**: evaluating `φ # σ₀` on `(a₀ ⊗ 1, …, aₚ ⊗ 1)` recovers `φ`. -/
theorem exteriorProductCocycle_scalarCocycle_zero_apply_tmul_one
    (φ : cyclicCocycles k A M p) (a : Fin (p + 1) → A) :
    ((exteriorProductCocycle φ (scalarCocycle k 0) :
        cyclicCochains k (A ⊗[k] k) (M ⊗[k] k) (p + 0)) :
        MultilinearMap k (fun _ : Fin (p + 0 + 1) ↦ A ⊗[k] k) (M ⊗[k] k))
        (fun i ↦ a i ⊗ₜ[k] (1 : k)) =
      ((φ : cyclicCochains k A M p) : MultilinearMap k (fun _ : Fin (p + 1) ↦ A) M) a ⊗ₜ[k]
        (1 : k) := by
  rw [exteriorProductCocycle_apply_tmul_of_zero, scalarCocycle_zero_apply, List.ofFn_const,
    List.prod_replicate, one_pow]

/-- **Normalization of Connes' periodicity operator via the exterior product**: for any cyclic
`p`-cocycle `φ` on a (possibly nonunital) `k`-algebra `A`, evaluating the exterior product
`φ # σ₁` on `(a₀ ⊗ 1, …, aₚ₊₂ ⊗ 1)` yields `(S φ)(a₀, …, aₚ₊₂) ⊗ 1`. -/
theorem exteriorProductCocycle_scalarCocycle_one_apply_tmul_one
    (φ : cyclicCocycles k A M p) (a : Fin (p + 3) → A) :
    ((exteriorProductCocycle φ (scalarCocycle k 1) :
        cyclicCochains k (A ⊗[k] k) (M ⊗[k] k) (p + 2)) :
        MultilinearMap k (fun _ : Fin (p + 3) ↦ A ⊗[k] k) (M ⊗[k] k))
        (fun i ↦ a i ⊗ₜ[k] (1 : k)) =
      ((cyclicCocyclesPeriodicity k A M p φ : cyclicCochains k A M (p + 2)) :
        MultilinearMap k (fun _ : Fin (p + 3) ↦ A) M) a ⊗ₜ[k] (1 : k) := by
  rw [exteriorProductCocycle_apply]
  refine (cycleCharacter_gradedTensorHomOfMemZero_tmul_of_two (UniversalForms.isDGAlgebra k A)
    (UniversalForms.isDGAlgebra k k) IsIdempotentElem.one a).trans ?_
  rw [UniversalForms.cycleCharacter_trace, UniversalForms.cycleCharacter_trace,
    scalarCocycle_one_apply, mul_one, mul_one, coe_cyclicCocyclesPeriodicity_apply]

/-- Composing `φ # σ₁` with `(TensorProduct.rid k A).symm` (`a ↦ a ⊗ 1`) on inputs and
`TensorProduct.rid k M` on outputs recovers `TauCeti.cyclicCocyclesPeriodicity` on the nose. -/
theorem rid_comp_exteriorProductCocycle_scalarCocycle_one (φ : cyclicCocycles k A M p) :
    (TensorProduct.rid k M).toLinearMap.compMultilinearMap
        ((((exteriorProductCocycle φ (scalarCocycle k 1) :
          cyclicCochains k (A ⊗[k] k) (M ⊗[k] k) (p + 2)) :
          MultilinearMap k (fun _ : Fin (p + 3) ↦ A ⊗[k] k) (M ⊗[k] k))).compLinearMap
          fun _ ↦ (TensorProduct.rid k A).symm.toLinearMap) =
      ((cyclicCocyclesPeriodicity k A M p φ : cyclicCochains k A M (p + 2)) :
        MultilinearMap k (fun _ : Fin (p + 3) ↦ A) M) := by
  ext a
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_symm_apply,
    exteriorProductCocycle_scalarCocycle_one_apply_tmul_one, TensorProduct.rid_tmul, one_smul]

end ExteriorProduct

end TauCeti
