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

* `SymmetricPower.differential`: the Lie algebra homomorphism `X ↦ d Symⁿ(X)` from
  `Module.End R M` to `Module.End R (Sym[R]^n M)`.
* `SymmetricPower.differential_tprod`: the Leibniz formula on pure symmetric tensors.
* `SymmetricPower.toSymmetricAlgebra_differential`: compatibility with
  `SymmetricAlgebra.derivationOfEnd`.
* `SymmetricPower.map_comp_differential`: naturality of the differential along linear maps.
* `SymmetricPower.differential_pow_eq_zero`: the nilpotency bound.
* `SymmetricPower.map_exp`: `Symⁿ(exp N) = exp (d Symⁿ(N))`.
-/

public section

open scoped TensorProduct

namespace SymmetricPower

open Finset

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The endomorphism `d Symⁿ(X)` of `Sym[R]^n M`, transported from the derivation of the
symmetric algebra extending `X`. -/
private noncomputable def differentialAux (n : ℕ) (X : Module.End R M) :
    Module.End R (Sym[R]^n M) :=
  (equivHomogeneous n).symm.toLinearMap ∘ₗ
    ((SymmetricAlgebra.derivationOfEnd R M X).toLinearMap.restrict
      fun _ hp ↦ SymmetricAlgebra.derivationOfEnd_mem_homogeneousSubmodule R M X hp) ∘ₗ
    (equivHomogeneous n).toLinearMap

private theorem toSymmetricAlgebra_differentialAux (n : ℕ) (X : Module.End R M)
    (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n (differentialAux n X x) =
      SymmetricAlgebra.derivationOfEnd R M X (toSymmetricAlgebra R M n x) := by
  rw [← coe_equivHomogeneous_apply, differentialAux]
  simp

variable (R M) in
/-- **The differential of the `n`-th symmetric power**: the Lie algebra homomorphism sending a
linear endomorphism `X` of `M` to the endomorphism `v₁ ⋯ vₙ ↦ ∑ⱼ v₁ ⋯ (X vⱼ) ⋯ vₙ` of
`Sym[R]^n M` (`SymmetricPower.differential_tprod`). -/
noncomputable def differential (n : ℕ) : Module.End R M →ₗ⁅R⁆ Module.End R (Sym[R]^n M) where
  toFun := differentialAux n
  map_add' X Y := LinearMap.ext fun x ↦ toSymmetricAlgebra_injective n <| by
    simp [toSymmetricAlgebra_differentialAux]
  map_smul' c X := LinearMap.ext fun x ↦ toSymmetricAlgebra_injective n <| by
    simp [toSymmetricAlgebra_differentialAux]
  map_lie' {X Y} := LinearMap.ext fun x ↦ toSymmetricAlgebra_injective n <| by
    rw [toSymmetricAlgebra_differentialAux, LieHom.map_lie, Derivation.commutator_apply]
    simp [toSymmetricAlgebra_differentialAux, LieRing.of_associative_ring_bracket]

/-- `d Symⁿ(X)` corresponds to the derivation of the symmetric algebra extending `X`. -/
@[simp]
theorem toSymmetricAlgebra_differential (n : ℕ) (X : Module.End R M) (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n (differential R M n X x) =
      SymmetricAlgebra.derivationOfEnd R M X (toSymmetricAlgebra R M n x) :=
  toSymmetricAlgebra_differentialAux n X x

/-- Iterates of `d Symⁿ(X)` correspond to iterates of the derivation extending `X`. -/
theorem toSymmetricAlgebra_differential_pow (n : ℕ) (X : Module.End R M) (k : ℕ)
    (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n ((differential R M n X ^ k) x) =
      (SymmetricAlgebra.derivationOfEnd R M X)^[k] (toSymmetricAlgebra R M n x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, toSymmetricAlgebra_differential, ih,
      Function.iterate_succ_apply']

/-- **The Leibniz formula**: `d Symⁿ(X)` sends `v₁ ⋯ vₙ` to `∑ⱼ v₁ ⋯ (X vⱼ) ⋯ vₙ`. -/
@[simp]
theorem differential_tprod (n : ℕ) (X : Module.End R M) (v : Fin n → M) :
    differential R M n X (⨂ₛ[R] i, v i) =
      ∑ j, ⨂ₛ[R] i, Function.update v j (X (v j)) i := by
  apply toSymmetricAlgebra_injective n
  rw [toSymmetricAlgebra_differential, toSymmetricAlgebra_tprod, map_sum,
    Derivation.leibniz_prod]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [toSymmetricAlgebra_tprod, SymmetricAlgebra.derivationOfEnd_ι, smul_eq_mul, mul_comm]
  simp_rw [Function.apply_update (fun _ ↦ SymmetricAlgebra.ι R M)]
  rw [prod_update_of_mem (mem_univ j), sdiff_singleton_eq_erase]

/-- In degree zero the differential vanishes. -/
@[simp]
theorem differential_zero : differential R M 0 = 0 := by
  ext X v
  simp

/-- **Naturality of the differential**: a linear map `f` intertwining `X` with `Y` makes
`Symⁿ(f)` intertwine `d Symⁿ(X)` with `d Symⁿ(Y)`. -/
theorem map_comp_differential {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)
    {f : M →ₗ[R] N} {X : Module.End R M} {Y : Module.End R N} (hf : f ∘ₗ X = Y ∘ₗ f) :
    map (ι := Fin n) f ∘ₗ differential R M n X = differential R N n Y ∘ₗ map f := by
  refine SymmetricPower.ext fun v ↦ ?_
  simp only [LinearMap.comp_apply, differential_tprod, map_tprod, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  simp_rw [Function.apply_update (fun _ ↦ f), ← LinearMap.comp_apply, hf]

/-- **Nilpotency of the differential**: if `X ^ k = 0`, then
`d Symⁿ(X) ^ (n * (k - 1) + 1) = 0`. -/
theorem differential_pow_eq_zero (n : ℕ) {X : Module.End R M} {k : ℕ} (hX : X ^ k = 0) :
    differential R M n X ^ (n * (k - 1) + 1) = 0 := by
  refine SymmetricPower.ext fun v ↦ toSymmetricAlgebra_injective n ?_
  rw [toSymmetricAlgebra_differential_pow, toSymmetricAlgebra_tprod,
    SymmetricAlgebra.iterate_derivationOfEnd_prod_ι_eq_zero hX v (Nat.lt_succ_self _)]
  simp

/-- The differential of a nilpotent endomorphism is nilpotent. -/
theorem isNilpotent_differential (n : ℕ) {X : Module.End R M} (hX : IsNilpotent X) :
    IsNilpotent (differential R M n X) :=
  let ⟨_, hk⟩ := hX
  ⟨_, differential_pow_eq_zero n hk⟩

/-- **The symmetric power of a unipotent exponential**: for a nilpotent endomorphism `N` of a
module over a `ℚ`-algebra, `Symⁿ(exp N) = exp (d Symⁿ(N))`. The `ℚ`-module structures on `M` and
on `Sym[R]^n M` are arguments; each is unique, and one is given by restriction of scalars along
`ℚ → R`. -/
theorem map_exp [Algebra ℚ R] [Module ℚ M] [Module ℚ (Sym[R]^n M)]
    {N : Module.End R M} (hN : IsNilpotent N) :
    map (ι := Fin n) (IsNilpotent.exp N) = IsNilpotent.exp (differential R M n N) := by
  obtain ⟨k, hk⟩ := hN
  -- The symmetric algebra of a module over a `ℚ`-algebra is a `ℚ`-algebra through its scalars.
  let : Algebra ℚ (SymmetricAlgebra R M) :=
    ((algebraMap R (SymmetricAlgebra R M)).comp (algebraMap ℚ R)).toAlgebra
  refine SymmetricPower.ext fun v ↦ toSymmetricAlgebra_injective n ?_
  have hv :=
    SymmetricAlgebra.iterate_derivationOfEnd_prod_ι_eq_zero hk v (Nat.lt_succ_self _)
  rw [IsNilpotent.exp_eq_sum (differential_pow_eq_zero n hk), LinearMap.sum_apply, map_sum,
    toSymmetricAlgebra_map, ← SymmetricAlgebra.taylorExp_derivationOfEnd ⟨k, hk⟩,
    toSymmetricAlgebra_tprod, Derivation.taylorExp_apply_eq_sum _ _ hv]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, map_rat_smul, toSymmetricAlgebra_differential_pow,
    toSymmetricAlgebra_tprod]

end SymmetricPower
