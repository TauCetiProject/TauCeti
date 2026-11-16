/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Projection from the tensor algebra to a tensor power

`TensorAlgebra.tensorPowerProjection d` reads the degree-`d` component of the tensor algebra.
It is a retraction of `TensorPower.toTensorAlgebra` in degree `d` and kills the other degrees.
In particular, it takes `(ι m)^d` to the pure tensor `m ⊗ ⋯ ⊗ m`. This permits constructions
using powers in the tensor algebra to take values in an individual tensor power.

The construction uses Eric Wieser's `TensorAlgebra.equivDirectSum` and its computation on
pure tensors.
-/

public noncomputable section

open scoped TensorProduct

namespace TensorAlgebra

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Projection from the tensor algebra to its degree-`d` tensor power. -/
def tensorPowerProjection (d : ℕ) : TensorAlgebra R M →ₗ[R] TensorPower R d M :=
  (DirectSum.component R ℕ (fun n ↦ TensorPower R n M) d).comp toDirectSum.toLinearMap

/-- The degree-`d` projection reads a tensor of length `n`, and vanishes unless `n = d`. -/
theorem tensorPowerProjection_tprod (d n : ℕ) (m : Fin n → M) :
    tensorPowerProjection (R := R) d (tprod R M n m) =
      if h : n = d then TensorPower.cast R M h (PiTensorProduct.tprod R m) else 0 := by
  classical
  simp only [tensorPowerProjection, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.component.of]
  split_ifs with h
  · subst n
    simp
  · rfl

/-- A tensor of length `d` is unchanged by the degree-`d` projection. -/
@[simp↓]
theorem tensorPowerProjection_tprod_self (d : ℕ) (m : Fin d → M) :
    tensorPowerProjection (R := R) d (tprod R M d m) = PiTensorProduct.tprod R m := by
  simp only [tensorPowerProjection_tprod, dite_eq_left rfl, TensorPower.cast_refl,
    LinearEquiv.refl_apply]

/-- The degree projection is a left inverse to the inclusion of that tensor power. -/
@[simp]
theorem tensorPowerProjection_comp_toTensorAlgebra (d : ℕ) :
    tensorPowerProjection (R := R) (M := M) d ∘ₗ TensorPower.toTensorAlgebra = LinearMap.id := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    TensorPower.toTensorAlgebra_tprod, tensorPowerProjection_tprod_self, LinearMap.id_apply]

/-- A power of a single generator projects to the pure tensor, with no factorial factor. -/
@[simp]
theorem tensorPowerProjection_ι_pow (d : ℕ) (m : M) :
    tensorPowerProjection d ((ι R m) ^ d) = PiTensorProduct.tprod R (fun _ : Fin d ↦ m) := by
  have hp : tprod R M d (fun _ ↦ m) = (ι R m) ^ d := by
    simp [tprod_apply, List.ofFn_const]
  rw [← hp, tensorPowerProjection_tprod_self]

/-- The degree projection commutes with the tensor algebra homomorphism induced by a linear
map, and the corresponding tensor-power map. -/
theorem tensorPowerProjection_comp_lift (d : ℕ) (f : M →ₗ[R] N) :
    tensorPowerProjection (R := R) d ∘ₗ (lift R ((ι R).comp f)).toLinearMap =
      (PiTensorProduct.map fun _ : Fin d ↦ f) ∘ₗ tensorPowerProjection d := by
  apply LinearMap.ext
  intro x
  rw [← ofDirectSum_toDirectSum x]
  generalize toDirectSum x = y
  induction y using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp_all
  | of n x =>
    induction x using PiTensorProduct.induction_on with
    | add x y hx hy => simp_all
    | smul_tprod r m =>
      have hl : lift R ((ι R).comp f) (tprod R M n m) = tprod R N n (fun i ↦ f (m i)) := by
        simp [tprod_apply, map_list_prod, List.map_ofFn, Function.comp_def]
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_smul, DirectSum.of_smul,
        ofDirectSum_of_tprod, hl, tensorPowerProjection_tprod]
      split_ifs with h
      · subst n
        simp
      · simp

/-- Two linear maps out of the tensor algebra agree if they agree on all pure tensor products. -/
theorem linearMap_ext_tprod {f g : TensorAlgebra R M →ₗ[R] N}
    (h : ∀ (n : ℕ) (x : Fin n → M), f (tprod R M n x) = g (tprod R M n x)) : f = g :=
  LinearMap.ext fun z ↦ by
    rw [← ofDirectSum_toDirectSum z]
    induction toDirectSum z using DirectSum.induction_on with
    | zero => simp
    | add _ _ hu hv => simp only [map_add, hu, hv]
    | of n t => induction t using PiTensorProduct.induction_on with
      | add _ _ hu hv => simp only [map_add, hu, hv]
      | smul_tprod _ x => simp only [DirectSum.of_smul, map_smul, ofDirectSum_of_tprod, h n x]

/-- Splitting off the first factor of a pure tensor product of length `n + 1`. -/
theorem tprod_succ (n : ℕ) (x : Fin (n + 1) → M) :
    tprod R M (n + 1) x = ι R (x 0) * tprod R M n (fun i ↦ x i.succ) := by
  simp [tprod_apply, List.ofFn_succ]

/-- Prepending a generator to a pure tensor product multiplies on the left by `ι R c`. -/
theorem tprod_cons {n : ℕ} (c : M) (x : Fin n → M) :
    tprod R M (n + 1) (Fin.cons c x) = ι R c * tprod R M n x := by simp

/-- Left multiplication by a generator raises tensor length by one. -/
theorem ι_mul_mem_range_toTensorAlgebra (c : M) {n : ℕ} {y : TensorAlgebra R M}
    (hy : y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))) :
    ι R c * y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hy; induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simpa only [map_add, mul_add] using Submodule.add_mem _ hu hv
  | smul_tprod r x =>
    rw [map_smul, mul_smul_comm, TensorPower.toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r ⟨PiTensorProduct.tprod R (Fin.cons c x), by
      rw [TensorPower.toTensorAlgebra_tprod, tprod_cons]⟩

end TensorAlgebra
