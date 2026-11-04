/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.ExteriorProduct
public import TauCeti.RingTheory.CyclicCohomology.GroundRing
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Normalization of Connes' periodicity operator via the exterior product

On a commutative ground ring `k`, the calibrated scalar cyclic `2m`-cocycle `σₘ` is given by

`σₘ(a₀, …, a₂ₘ) = m! a₀ ⋯ a₂ₘ`

(`TauCeti.scalarCocycle`). In degree zero `σ₀(a₀) = a₀` is the identity trace on `k`, in degree two
`σ₁(a₀, a₁, a₂) = a₀ a₁ a₂` is Connes' fundamental `2`-cocycle on `k`, and Connes' periodicity
operator steps through the calibrated sequence: `S(σₘ) = σₘ₊₁`.

For any (possibly nonunital) `k`-algebra `A` and any cyclic `p`-cocycle `φ` on `A` with values in a
`k`-module `M`, taking the exterior product `φ # σ₁` (`TauCeti.exteriorProductCocycle`) and
restricting along `a ↦ a ⊗ 1 : A → A ⊗[k] k` recovers `TauCeti.cyclicCocyclesPeriodicity` on the
nose:

`(φ # σ₁)(a₀ ⊗ 1, …, aₚ₊₂ ⊗ 1) = (S φ)(a₀, …, aₚ₊₂) ⊗ 1`.

Likewise `(φ # σ₀)(a₀ ⊗ 1, …, aₚ ⊗ 1) = φ(a₀, …, aₚ) ⊗ 1`. Together with `S(σₘ) = σₘ₊₁`, this pins
down the normalization of Connes' periodicity operator `S` by `φ ↦ φ # σ₁` with
`σ₁(1, 1, 1) = 1`.

## Main definitions

* `TauCeti.scalarCocycle`: the calibrated scalar cyclic `2m`-cocycle
  `σₘ(a₀, …, a₂ₘ) = m! a₀ ⋯ a₂ₘ` on a commutative ring `k`.

## Main results

* `TauCeti.scalarCocycle_zero_apply`, `TauCeti.scalarCocycle_one_apply`: explicit formulas
  `σ₀(a₀) = a₀` and `σ₁(a₀, a₁, a₂) = a₀ a₁ a₂`.
* `TauCeti.cyclicCocyclesPeriodicity_scalarCocycle`: `S(σₘ) = σₘ₊₁`.
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

section ScalarCocycle

open scoped Nat

variable (k : Type*) [CommRing k]

/-- The **calibrated scalar cyclic `2m`-cocycle** `σₘ` on a commutative ring `k`, defined by
`σₘ(a₀, …, a₂ₘ) = m! a₀ ⋯ a₂ₘ`. -/
def scalarCocycle (m : ℕ) : cyclicCocycles k k k (2 * m) :=
  ⟨⟨MultilinearMap.mkPiRing k (Fin (2 * m + 1)) (m ! : k),
    by simp [cyclicCochains_self_of_even k k (even_two_mul m)]⟩,
    by simp [cyclicCocycles_self_of_even k k (even_two_mul m)]⟩

/-- Underlying multilinear map of `scalarCocycle`. -/
@[simp]
theorem coe_scalarCocycle (m : ℕ) :
    ((scalarCocycle k m : cyclicCochains k k k (2 * m)) :
      MultilinearMap k (fun _ : Fin (2 * m + 1) ↦ k) k) =
      MultilinearMap.mkPiRing k (Fin (2 * m + 1)) (m ! : k) :=
  (rfl)

/-- Pointwise formula `σₘ(a₀, …, a₂ₘ) = m! ∏ᵢ aᵢ`. -/
theorem scalarCocycle_apply (m : ℕ) (a : Fin (2 * m + 1) → k) :
    ((scalarCocycle k m : cyclicCochains k k k (2 * m)) :
      MultilinearMap k (fun _ : Fin (2 * m + 1) ↦ k) k) a = (m ! : k) * ∏ i, a i := by
  rw [coe_scalarCocycle, MultilinearMap.mkPiRing_apply, smul_eq_mul, mul_comm]

/-- In degree zero, `σ₀(a₀) = a₀` is the identity trace on `k`. -/
theorem scalarCocycle_zero_apply (a : Fin 1 → k) :
    ((scalarCocycle k 0 : cyclicCochains k k k 0) :
      MultilinearMap k (fun _ : Fin 1 ↦ k) k) a = a 0 := by
  simp

/-- In degree two, `σ₁(a₀, a₁, a₂) = a₀ a₁ a₂` is Connes' fundamental `2`-cocycle on `k`. -/
theorem scalarCocycle_one_apply (a : Fin 3 → k) :
    ((scalarCocycle k 1 : cyclicCochains k k k 2) :
      MultilinearMap k (fun _ : Fin 3 ↦ k) k) a = a 0 * a 1 * a 2 := by
  rw [scalarCocycle_apply k 1 a, Nat.factorial_one, Nat.cast_one, one_mul, Fin.prod_univ_three]

/-- Connes' cocycle periodicity operator maps `σₘ` to `σₘ₊₁`. -/
@[simp]
theorem cyclicCocyclesPeriodicity_scalarCocycle (m : ℕ) :
    cyclicCocyclesPeriodicity k k k (2 * m) (scalarCocycle k m) = scalarCocycle k (m + 1) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_cyclicCocyclesPeriodicity_apply, coe_scalarCocycle, cochainPeriodicity_mkPiRing]
  have hdiv : 2 * m / 2 + 1 = m + 1 := by omega
  have hfac : ((m + 1 : ℕ) • (m ! : k)) = ((m + 1)! : k) := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.factorial_succ]
  rw [hdiv, hfac]
  rfl

/-- The cyclic cohomology class of `scalarCocycle k m` is `mkPiRing` of `m!`. -/
@[simp]
theorem cyclicCohomology.mk_scalarCocycle (m : ℕ) :
    cyclicCohomology.mk k k k (2 * m) (scalarCocycle k m) =
      cyclicCohomology.mkPiRing k k (2 * m) (even_two_mul m) (m ! : k) := by
  rw [cyclicCohomology.mkPiRing_apply]
  rfl

end ScalarCocycle

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
