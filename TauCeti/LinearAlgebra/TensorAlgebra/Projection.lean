/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Projection from the tensor algebra to a tensor power

`TensorAlgebra.tensorPowerProjection d` reads the degree-`d` component of the tensor algebra.
It is a retraction of `TensorPower.toTensorAlgebra` in degree `d` and kills the other degrees.
In particular, it takes `(ι m)^d` to the pure tensor `m ⊗ ⋯ ⊗ m`, and its restriction to the
degree-`d` submodule `(LinearMap.range (ι R)) ^ d` gives a canonical linear equivalence
`TensorAlgebra.tensorPowerEquivRangePow d : TensorPower R d M ≃ₗ[R] (LinearMap.range (ι R)) ^ d`
inverse to `TensorPower.toTensorAlgebra`.

The construction uses Eric Wieser's `TensorAlgebra.equivDirectSum` and its computation on
pure tensors.
-/

public noncomputable section

open scoped TensorProduct

namespace TensorPower

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Casting the degree of a tensor power does not change its image in the tensor algebra. -/
@[simp]
theorem toTensorAlgebra_cast {n m : ℕ} (h : n = m) (x : TensorPower R n M) :
    toTensorAlgebra (cast R M h x) = toTensorAlgebra x := by
  subst h
  simp

end TensorPower

namespace TensorAlgebra

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Projection from the tensor algebra to its degree-`d` tensor power. -/
def tensorPowerProjection (d : ℕ) : TensorAlgebra R M →ₗ[R] TensorPower R d M :=
  (DirectSum.component R ℕ (fun n ↦ TensorPower R n M) d).comp toDirectSum.toLinearMap

/-- Multiplying two pure tensors in the tensor algebra concatenates their families of factors. -/
theorem tprod_mul_tprod {i j : ℕ} (u : Fin i → M) (v : Fin j → M) :
    tprod R M i u * tprod R M j v = tprod R M (i + j) (Fin.append u v) := by
  rw [← TensorPower.toTensorAlgebra_tprod, ← TensorPower.toTensorAlgebra_tprod,
    ← TensorPower.toTensorAlgebra_gMul, TensorPower.tprod_mul_tprod,
    TensorPower.toTensorAlgebra_tprod]

/-- A pure tensor of length `d` lies in the `d`-th power of the range of `TensorAlgebra.ι R`. -/
theorem tprod_mem_range_pow (d : ℕ) (m : Fin d → M) :
    tprod R M d m ∈ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ d := by
  induction d with
  | zero =>
    rw [tprod_apply, List.ofFn_zero, List.prod_nil, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | succ d ih =>
    rw [tprod_apply, List.ofFn_succ, List.prod_cons, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (m 0)) (ih (m ∘ Fin.succ))

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

/-- Applying the degree-`d` projection after `TensorPower.toTensorAlgebra` returns the input. -/
@[simp]
theorem tensorPowerProjection_toTensorAlgebra (d : ℕ) (x : TensorPower R d M) :
    tensorPowerProjection d (TensorPower.toTensorAlgebra x) = x :=
  LinearMap.congr_fun (tensorPowerProjection_comp_toTensorAlgebra d) x

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

end TensorAlgebra

namespace TensorPower

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Every element of the `d`-th tensor power embeds into the `d`-th graded piece of the tensor
algebra. -/
theorem toTensorAlgebra_mem_range_pow (d : ℕ) (x : TensorPower R d M) :
    toTensorAlgebra x ∈ LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ d := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r (TensorAlgebra.tprod_mem_range_pow d m)
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- The image of the `d`-th tensor power inside the tensor algebra is the `d`-th graded piece
`(LinearMap.range (TensorAlgebra.ι R)) ^ d`. -/
theorem range_toTensorAlgebra (d : ℕ) :
    LinearMap.range (toTensorAlgebra (R := R) (M := M) (n := d)) =
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ d := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact toTensorAlgebra_mem_range_pow d x
  · induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      exact ⟨DirectSum.GAlgebra.toFun (A := fun n ↦ TensorPower R n M) r,
        toTensorAlgebra_galgebra_toFun (M := M) r⟩
    | add x y _ _ _ hx hy => exact add_mem hx hy
    | mem_mul m hm i x _ ih =>
      rcases hm with ⟨v, rfl⟩
      rcases ih with ⟨y, rfl⟩
      refine ⟨TensorPower.cast R M (add_comm 1 i)
        (GradedMonoid.GMul.mul (A := fun n ↦ TensorPower R n M)
          (PiTensorProduct.tprod R (fun _ : Fin 1 ↦ v)) y), ?_⟩
      rw [toTensorAlgebra_cast, toTensorAlgebra_gMul, toTensorAlgebra_tprod]
      simp [TensorAlgebra.tprod_apply]

end TensorPower

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- On the `d`-th graded piece of the tensor algebra, `TensorPower.toTensorAlgebra` recovers an
element from its degree-`d` projection. -/
theorem toTensorAlgebra_tensorPowerProjection_of_mem_range_pow {d : ℕ} {x : TensorAlgebra R M}
    (hx : x ∈ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ d) :
    TensorPower.toTensorAlgebra (tensorPowerProjection d x) = x := by
  rw [← TensorPower.range_toTensorAlgebra] at hx
  rcases hx with ⟨y, rfl⟩
  rw [tensorPowerProjection_toTensorAlgebra]

/-- The degree-`d` projection vanishes on any graded piece of degree `n ≠ d`. -/
theorem tensorPowerProjection_of_mem_range_pow_ne {d n : ℕ} (h : n ≠ d) {x : TensorAlgebra R M}
    (hx : x ∈ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ n) :
    tensorPowerProjection d x = 0 := by
  rw [← TensorPower.range_toTensorAlgebra] at hx
  rcases hx with ⟨y, rfl⟩
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, TensorPower.toTensorAlgebra_tprod, map_smul, tensorPowerProjection_tprod,
      dite_eq_right fun h' ↦ (h h').elim, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- The canonical linear equivalence identifying the `d`-th tensor power with the `d`-th graded
piece `(LinearMap.range (TensorAlgebra.ι R)) ^ d` of the tensor algebra. -/
def tensorPowerEquivRangePow (d : ℕ) :
    TensorPower R d M ≃ₗ[R] ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ d) :=
  LinearEquiv.ofLinearMap
    (TensorPower.toTensorAlgebra.codRestrict _ (TensorPower.toTensorAlgebra_mem_range_pow d))
    ((tensorPowerProjection d).comp (Submodule.subtype _))
    (LinearMap.ext fun x ↦
      Subtype.ext (toTensorAlgebra_tensorPowerProjection_of_mem_range_pow x.property))
    (LinearMap.ext fun x ↦ tensorPowerProjection_toTensorAlgebra d x)

/-- The equivalence `tensorPowerEquivRangePow` acts as `TensorPower.toTensorAlgebra`. -/
@[simp]
theorem coe_tensorPowerEquivRangePow_apply (d : ℕ) (x : TensorPower R d M) :
    (tensorPowerEquivRangePow d x : TensorAlgebra R M) = TensorPower.toTensorAlgebra x := by
  rfl

/-- The inverse of `tensorPowerEquivRangePow` is the degree-`d` projection. -/
@[simp]
theorem tensorPowerEquivRangePow_symm_apply (d : ℕ)
    (x : ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ d)) :
    (tensorPowerEquivRangePow d).symm x = tensorPowerProjection d x := by
  rfl

end TensorAlgebra
