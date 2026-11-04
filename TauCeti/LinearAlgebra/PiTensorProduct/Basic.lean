/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Basic facts about indexed tensor products

If every element of one factor is its own additive inverse, then so is every element of an
indexed tensor product. This holds over a ring of characteristic two
and also, for instance, for a module of `𝔽₂`-valued cochains regarded over `ℤ`; it is how terms
appearing twice cancel in sign-free constructions on tensor powers. Over a single index, every
element of a tensor power is a pure tensor.

## Main results

* `PiTensorProduct.add_self_eq_zero`: if every element of one factor is its own additive inverse,
  so is every element of the indexed tensor product.
* `TauCeti.PiTensorProduct.exists_eq_tprod_of_subsingleton`: over a single index, every element
  of a tensor power is a pure tensor.
-/

public section

open Function
open scoped TensorProduct

universe uι uR uM

namespace PiTensorProduct

variable {ι : Type uι} {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- If every element of the factor at `i` is its own additive inverse, then so is every element
of the indexed tensor product. No hypothesis is needed on the other factors. -/
theorem add_self_eq_zero {M : ι → Type uM} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (x : ⨂[R] i, M i) (i : ι) (hM : ∀ m : M i, m + m = 0) : x + x = 0 := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    have h := (tprod R).map_update_add m i (m i) (m i)
    rw [update_eq_self, hM, MultilinearMap.map_update_zero] at h
    rw [← smul_add, ← h, smul_zero]
  | add x y hx hy => rw [add_add_add_comm, hx, hy, add_zero]

end PiTensorProduct

namespace TauCeti.PiTensorProduct

variable {ι : Type uι} {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Over a single index `i₀`, every element of a tensor power of `M` is a pure tensor
`tprod R fun _ ↦ y`. -/
theorem exists_eq_tprod_of_subsingleton [Subsingleton ι] (i₀ : ι) (x : ⨂[R] _ : ι, M) :
    ∃ y, x = PiTensorProduct.tprod R fun _ ↦ y :=
  ⟨_, ((PiTensorProduct.subsingletonEquiv i₀).symm_apply_apply x).symm.trans
    (PiTensorProduct.subsingletonEquiv_symm_apply' _ _)⟩

end TauCeti.PiTensorProduct
