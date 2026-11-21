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
In particular, it takes `(ι m)^d` to the pure tensor `m ⊗ ⋯ ⊗ m`. This permits constructions
using powers in the tensor algebra to take values in an individual tensor power.

It also identifies the `d`-th homogeneous piece `(TensorAlgebra.ι R).range ^ d` of
`TensorAlgebra.gradedAlgebra` with `TensorPower R d M`
(`TensorAlgebra.rangePowEquivTensorPower`), vanishing on all pieces of degree different from `d`.

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

/-- A pure tensor of length `d` lies in the degree-`d` submodule `(ι R).range ^ d`. -/
theorem tprod_mem_range_ι_pow (d : ℕ) (m : Fin d → M) :
    tprod R M d m ∈ (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ d := by
  simpa [tprod_apply] using
    SetLike.list_prod_ofFn_mem_graded (A := (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ ·))
      (fun _ : Fin d => (1 : ℕ)) (fun i => ι R (m i)) fun i => by
        rw [pow_one]; exact LinearMap.mem_range_self _ _

/-- The image of `TensorPower.toTensorAlgebra` lies in `(ι R).range ^ d`. -/
theorem toTensorAlgebra_mem_range_ι_pow {d : ℕ} (x : TensorPower R d M) :
    TensorPower.toTensorAlgebra x ∈ (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ d := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, TensorPower.toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r (tprod_mem_range_ι_pow d m)
  | add _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Every homogeneous element of degree `d` maps under `toDirectSum` into the degree-`d` summand
given by `tensorPowerProjection d`. -/
theorem toDirectSum_of_mem_range_ι_pow {d : ℕ} {x : TensorAlgebra R M}
    (hx : x ∈ (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ d) :
    toDirectSum x = DirectSum.of (fun n => TensorPower R n M) d (tensorPowerProjection d x) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap _ =>
    simp [AlgHom.commutes, tensorPowerProjection, DirectSum.algebraMap_apply,
      ← DirectSum.lof_eq_of R]
  | add _ _ _ _ _ ihx ihy => rw [map_add, map_add, map_add, ihx, ihy]
  | mem_mul _ hm i x _ ih =>
    obtain ⟨v, rfl⟩ := hm
    have hmul : toDirectSum (ι R v * x) = DirectSum.of (fun n => TensorPower R n M) (i + 1)
        (TensorPower.cast R M (add_comm 1 i) (GradedMonoid.GMul.mul
          (A := fun n => TensorPower R n M) (PiTensorProduct.tprod R fun _ : Fin 1 => v)
          (tensorPowerProjection i x))) := by
      rw [map_mul, toDirectSum_ι, ih, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq
        (TensorPower.gradedMonoid_eq_of_cast (add_comm 1 i) rfl)
    rw [hmul]; congr 1; simp [tensorPowerProjection, hmul, ← DirectSum.lof_eq_of R]

/-- `toTensorAlgebra ∘ tensorPowerProjection d` recovers every degree-`d` element. -/
theorem toTensorAlgebra_tensorPowerProjection_of_mem {d : ℕ} {x : TensorAlgebra R M}
    (hx : x ∈ (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ d) :
    TensorPower.toTensorAlgebra (tensorPowerProjection d x) = x := by
  have h := congrArg ofDirectSum (toDirectSum_of_mem_range_ι_pow hx)
  rw [ofDirectSum_toDirectSum] at h
  exact (DirectSum.toAddMonoid_of (fun n =>
    (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)).toAddMonoidHom) d _).symm.trans h.symm

/-- `tensorPowerProjection d` vanishes on homogeneous elements of degree `n ≠ d`. -/
theorem tensorPowerProjection_of_mem_range_ι_pow_ne {d n : ℕ} (hnd : n ≠ d)
    {x : TensorAlgebra R M} (hx : x ∈ (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ n) :
    tensorPowerProjection d x = 0 := by
  rw [tensorPowerProjection, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    toDirectSum_of_mem_range_ι_pow hx, ← DirectSum.lof_eq_of R, DirectSum.component.of]
  simp [hnd]

/-- `tensorPowerProjection d` agrees with projecting onto the `d`-th homogeneous piece first. -/
theorem tensorPowerProjection_decompose (d : ℕ) (x : TensorAlgebra R M) :
    tensorPowerProjection d
        (DirectSum.decompose ((LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ ·) :
          ℕ → Submodule R _) x d : TensorAlgebra R M) =
      tensorPowerProjection d x := by
  classical
  let 𝒜 : ℕ → Submodule R (TensorAlgebra R M) :=
    (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ ·)
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 x]
  rw [map_sum, Finset.sum_eq_single d]
  · exact fun _ _ hid => tensorPowerProjection_of_mem_range_ι_pow_ne hid (SetLike.coe_mem _)
  · intro hd; rw [DFinsupp.notMem_support_iff.mp hd, ZeroMemClass.coe_zero, map_zero]

/-- Linear equivalence identifying `(ι R).range ^ d` with `TensorPower R d M`. -/
def rangePowEquivTensorPower (d : ℕ) :
    ↥((LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ d) ≃ₗ[R] TensorPower R d M :=
  LinearEquiv.ofLinearMap ((tensorPowerProjection d).comp (Submodule.subtype _))
    (TensorPower.toTensorAlgebra.codRestrict _ fun x => toTensorAlgebra_mem_range_ι_pow x)
    (tensorPowerProjection_comp_toTensorAlgebra d)
    (by ext ⟨x, hx⟩; exact toTensorAlgebra_tensorPowerProjection_of_mem hx)

@[simp] theorem rangePowEquivTensorPower_apply (d : ℕ)
    (x : ↥((LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ d)) :
    rangePowEquivTensorPower d x = tensorPowerProjection d x.val := by rfl
@[simp] theorem rangePowEquivTensorPower_symm_apply (d : ℕ) (x : TensorPower R d M) :
    ((rangePowEquivTensorPower d).symm x : TensorAlgebra R M) =
      TensorPower.toTensorAlgebra x := by rfl

end TensorAlgebra
