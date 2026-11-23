/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Exp
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
import TauCeti.RingTheory.Derivation.Basic

/-!
# The differential of a symmetric power

A linear endomorphism `X` of a module `M` over a commutative ring `R` acts on each symmetric power
`Sym[R]^n M` by the Leibniz rule,

`d Symⁿ(X) (v₁ ⋯ vₙ) = ∑ⱼ v₁ ⋯ (X vⱼ) ⋯ vₙ`.

This is the differential of the representation `Symⁿ : GL(M) → GL(Symⁿ M)`, `g (v₁ ⋯ vₙ) =
g v₁ ⋯ g vₙ`. It is obtained by transporting the derivation `SymmetricAlgebra.derivationOfEnd`
of the symmetric algebra, which preserves the homogeneous components, along the identification
`SymmetricPower.equivHomogeneous` of `Sym[R]^n M` with the degree-`n` component. The assignment
`X ↦ d Symⁿ(X)` is a homomorphism of Lie algebras.

If `X ^ k = 0` then `d Symⁿ(X) ^ (n * (k - 1) + 1) = 0`, so `d Symⁿ(X)` is nilpotent when `X` is.
For nilpotent `N` over `ℚ`, the symmetric power of the unipotent endomorphism `exp N` is the
exponential of the differential:

`Symⁿ(exp N) = exp (d Symⁿ(N))`.

The nilpotency order of `d Symⁿ(N)` is in general larger than that of `N`; see the checks in
`TauCeti.Examples.LinearAlgebra.SymmetricPower.Derivation`.

## Main declarations

* `SymmetricPower.derivationMap`: the Lie algebra homomorphism `X ↦ d Symⁿ(X)` from
  `Module.End R M` to `Module.End R (Sym[R]^n M)`.
* `SymmetricPower.derivationMap_tprod`: the Leibniz formula on pure symmetric tensors.
* `SymmetricPower.toSymmetricAlgebra_derivationMap`: compatibility with
  `SymmetricAlgebra.derivationOfEnd`.
* `SymmetricPower.derivationMap_pow_eq_zero`: the nilpotency bound.
* `SymmetricPower.map_exp`: `Symⁿ(exp N) = exp (d Symⁿ(N))`.
-/

public section

open scoped TensorProduct

namespace SymmetricPower

open Finset

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Multiplication of generators is natural in the module. -/
theorem toSymmetricAlgebra_map {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)
    (f : M →ₗ[R] N) (x : Sym[R]^n M) :
    toSymmetricAlgebra R N n (map f x) = SymmetricAlgebra.map R f (toSymmetricAlgebra R M n x) :=
  LinearMap.congr_fun (SymmetricPower.ext (g := toSymmetricAlgebra R N n ∘ₗ map f)
    (h := (SymmetricAlgebra.map R f).toLinearMap ∘ₗ toSymmetricAlgebra R M n)
    fun m ↦ by simp [toSymmetricAlgebra_tprod]) x

/-- The endomorphism `d Symⁿ(X)` of `Sym[R]^n M`, transported from the derivation of the
symmetric algebra extending `X`. -/
private noncomputable def derivationMapAux (n : ℕ) (X : Module.End R M) :
    Module.End R (Sym[R]^n M) :=
  (equivHomogeneous n).symm.toLinearMap ∘ₗ
    ((SymmetricAlgebra.derivationOfEnd R M X).toLinearMap.restrict
      fun _ hp ↦ SymmetricAlgebra.derivationOfEnd_mem_homogeneousSubmodule R M X hp) ∘ₗ
    (equivHomogeneous n).toLinearMap

private theorem toSymmetricAlgebra_derivationMapAux (n : ℕ) (X : Module.End R M)
    (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n (derivationMapAux n X x) =
      SymmetricAlgebra.derivationOfEnd R M X (toSymmetricAlgebra R M n x) := by
  rw [← coe_equivHomogeneous_apply, derivationMapAux]
  simp

variable (R M) in
/-- **The differential of the `n`-th symmetric power**: the Lie algebra homomorphism sending a
linear endomorphism `X` of `M` to the endomorphism `v₁ ⋯ vₙ ↦ ∑ⱼ v₁ ⋯ (X vⱼ) ⋯ vₙ` of
`Sym[R]^n M` (`SymmetricPower.derivationMap_tprod`). -/
noncomputable def derivationMap (n : ℕ) : Module.End R M →ₗ⁅R⁆ Module.End R (Sym[R]^n M) where
  toFun := derivationMapAux n
  map_add' X Y := LinearMap.ext fun x ↦ toSymmetricAlgebra_injective n <| by
    simp [toSymmetricAlgebra_derivationMapAux]
  map_smul' c X := LinearMap.ext fun x ↦ toSymmetricAlgebra_injective n <| by
    simp [toSymmetricAlgebra_derivationMapAux]
  map_lie' {X Y} := LinearMap.ext fun x ↦ toSymmetricAlgebra_injective n <| by
    rw [toSymmetricAlgebra_derivationMapAux, LieHom.map_lie, Derivation.commutator_apply,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, map_sub, mul_apply_eq_comp,
      mul_apply_eq_comp, toSymmetricAlgebra_derivationMapAux, toSymmetricAlgebra_derivationMapAux,
      toSymmetricAlgebra_derivationMapAux, toSymmetricAlgebra_derivationMapAux]

/-- `d Symⁿ(X)` corresponds to the derivation of the symmetric algebra extending `X`. -/
@[simp]
theorem toSymmetricAlgebra_derivationMap (n : ℕ) (X : Module.End R M) (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n (derivationMap R M n X x) =
      SymmetricAlgebra.derivationOfEnd R M X (toSymmetricAlgebra R M n x) :=
  toSymmetricAlgebra_derivationMapAux n X x

/-- Iterates of `d Symⁿ(X)` correspond to iterates of the derivation extending `X`. -/
theorem toSymmetricAlgebra_derivationMap_pow (n : ℕ) (X : Module.End R M) (k : ℕ)
    (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n ((derivationMap R M n X ^ k) x) =
      (SymmetricAlgebra.derivationOfEnd R M X)^[k] (toSymmetricAlgebra R M n x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, toSymmetricAlgebra_derivationMap, ih,
      Function.iterate_succ_apply']

/-- **The Leibniz formula**: `d Symⁿ(X)` sends `v₁ ⋯ vₙ` to `∑ⱼ v₁ ⋯ (X vⱼ) ⋯ vₙ`. -/
theorem derivationMap_tprod (n : ℕ) (X : Module.End R M) (v : Fin n → M) :
    derivationMap R M n X (⨂ₛ[R] i, v i) =
      ∑ j, ⨂ₛ[R] i, Function.update v j (X (v j)) i := by
  apply toSymmetricAlgebra_injective n
  rw [toSymmetricAlgebra_derivationMap, toSymmetricAlgebra_tprod, map_sum,
    Derivation.leibniz_prod]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [toSymmetricAlgebra_tprod, SymmetricAlgebra.derivationOfEnd_ι, smul_eq_mul, mul_comm]
  have h : (fun i ↦ SymmetricAlgebra.ι R M (Function.update v j (X (v j)) i)) =
      Function.update (fun i ↦ SymmetricAlgebra.ι R M (v i)) j
        (SymmetricAlgebra.ι R M (X (v j))) := by
    funext i
    rcases eq_or_ne i j with rfl | hij <;> simp [*]
  rw [h, prod_update_of_mem (mem_univ j), sdiff_singleton_eq_erase]

/-- If `X ^ k` kills `M`, then the derivation extending `X` kills, after `n * (k - 1) + 1`
iterations, every product of `n` generators. -/
private theorem iterate_derivationOfEnd_prod_ι {X : Module.End R M} {k : ℕ} (hX : X ^ k = 0) :
    ∀ (n : ℕ) (v : Fin n → M) (j : ℕ), n * (k - 1) < j →
      (SymmetricAlgebra.derivationOfEnd R M X)^[j] (∏ i, SymmetricAlgebra.ι R M (v i)) = 0
  | 0, v, j, hj => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hj
    simp [Function.iterate_succ_apply]
  | n + 1, v, j, hj => by
    rw [Fin.prod_univ_succ, Derivation.iterate_apply_mul]
    refine sum_eq_zero fun ab hab ↦ ?_
    rw [mem_antidiagonal] at hab
    by_cases ha : k ≤ ab.1
    · have h : (X ^ ab.1) (v 0) = 0 := by
        rw [← Nat.sub_add_cancel ha, pow_add, hX, mul_zero, LinearMap.zero_apply]
      rw [SymmetricAlgebra.iterate_derivationOfEnd_ι, h, map_zero, zero_mul, smul_zero]
    · rw [iterate_derivationOfEnd_prod_ι hX n _ ab.2 (by rw [Nat.succ_mul] at hj; omega),
        mul_zero, smul_zero]

/-- **Nilpotency of the differential**: if `X ^ k = 0`, then
`d Symⁿ(X) ^ (n * (k - 1) + 1) = 0`. -/
theorem derivationMap_pow_eq_zero (n : ℕ) {X : Module.End R M} {k : ℕ} (hX : X ^ k = 0) :
    derivationMap R M n X ^ (n * (k - 1) + 1) = 0 := by
  refine SymmetricPower.ext fun v ↦ toSymmetricAlgebra_injective n ?_
  rw [toSymmetricAlgebra_derivationMap_pow,
    toSymmetricAlgebra_tprod, iterate_derivationOfEnd_prod_ι hX n v _ (Nat.lt_succ_self _)]
  simp

/-- The differential of a nilpotent endomorphism is nilpotent. -/
theorem isNilpotent_derivationMap (n : ℕ) {X : Module.End R M} (hX : IsNilpotent X) :
    IsNilpotent (derivationMap R M n X) :=
  let ⟨_, hk⟩ := hX
  ⟨_, derivationMap_pow_eq_zero n hk⟩

/-- **The symmetric power of a unipotent exponential**: for a nilpotent endomorphism `N` of a
module over a `ℚ`-algebra, `Symⁿ(exp N) = exp (d Symⁿ(N))`. The `ℚ`-module structures on `M` and
on `Sym[R]^n M` are arguments; each is unique, and one is given by restriction of scalars along
`ℚ → R`. -/
theorem map_exp [Algebra ℚ R] [Module ℚ M] [Module ℚ (Sym[R]^n M)]
    {N : Module.End R M} (hN : IsNilpotent N) :
    map (ι := Fin n) (IsNilpotent.exp N) = IsNilpotent.exp (derivationMap R M n N) := by
  obtain ⟨k, hk⟩ := hN
  -- The symmetric algebra of a module over a `ℚ`-algebra is a `ℚ`-algebra through its scalars.
  let : Algebra ℚ (SymmetricAlgebra R M) :=
    ((algebraMap R (SymmetricAlgebra R M)).comp (algebraMap ℚ R)).toAlgebra
  refine SymmetricPower.ext fun v ↦ toSymmetricAlgebra_injective n ?_
  have hv := iterate_derivationOfEnd_prod_ι hk n v _ (Nat.lt_succ_self _)
  rw [IsNilpotent.exp_eq_sum (derivationMap_pow_eq_zero n hk), LinearMap.sum_apply, map_sum,
    toSymmetricAlgebra_map, ← SymmetricAlgebra.taylorExp_derivationOfEnd ⟨k, hk⟩,
    toSymmetricAlgebra_tprod, Derivation.taylorExp_apply_eq_sum _ _ hv]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, map_rat_smul, toSymmetricAlgebra_derivationMap_pow,
    toSymmetricAlgebra_tprod]

end SymmetricPower
