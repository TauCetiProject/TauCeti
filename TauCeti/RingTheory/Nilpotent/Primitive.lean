/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# Faithful divided-power exponentials from a primitive root step

If an integral divided-power action has a vector `v` with `x v = w`, `x w = 0`, and
`w` primitive, its exponential retains its parameter over every commutative value ring.
Indeed, its value at `v` is `v + t w`, and an integral functional taking `w` to one
recovers `t`. No basis, reducedness or characteristic hypothesis is required.

This criterion applies to the two-dimensional simple-root strings through the highest
vectors of fundamental representations. It uses the polynomial action
`TauCeti.baseChangeExp` and the basis-free notion `TauCeti.IsPrimitive`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
-/

public section

namespace TauCeti

open TensorProduct

-- Use the module structure stored by the value ring's integral algebra.
attribute [local instance high] Algebra.toModule

variable {B V S R : Type*} [Ring B] [Algebra ℚ B] [AddCommGroup V] [Module B V]
  [SetLike S V] [AddSubgroupClass S V] [CommRing R] [Algebra ℤ R]

/-- A primitive two-step string detects the parameter of a divided-power exponential
after arbitrary scalar extension. -/
theorem baseChangeExp_injective_of_isPrimitive (x : B) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hx : IsNilpotent x) (v w : M) (hvw : x • (v : V) = (w : V))
    (hw : x • (w : V) = 0) (hp : IsPrimitive w) :
    Function.Injective (baseChangeExp (R := R) x M hM) := by
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hp
  have h1 : integralDividedPower x M 1 (hM 1) v = w := by
    apply Subtype.ext
    rw [coe_integralDividedPower_one_apply]
    exact hvw
  have h2 : x ^ 2 • (v : V) = 0 := by rw [pow_two, mul_smul, hvw, hw]
  have heval (t : R) : baseChangeExp x M hM t (1 ⊗ₜ[ℤ] v) =
      (1 : R) ⊗ₜ[ℤ] v + t ⊗ₜ[ℤ] w := by
    rw [baseChangeExp_tmul_of_pow_smul_eq_zero x M hM hx t 1 v h2]
    simp [Finset.sum_range_succ, h1]
  intro t u htu
  have h := congrArg (fun g : Module.End R (R ⊗[ℤ] M) => g (1 ⊗ₜ[ℤ] v)) htu
  rw [heval, heval] at h
  have htw := add_left_cancel h
  have hcoord := congrArg
    (fun z : R ⊗[ℤ] M => (TensorProduct.rid ℤ R)
      (TensorProduct.map (LinearMap.id : R →ₗ[ℤ] R) f z)) htw
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, hf,
    TensorProduct.rid_tmul] at hcoord
  simpa only [Algebra.smul_def, map_one, one_mul] using hcoord

end TauCeti
