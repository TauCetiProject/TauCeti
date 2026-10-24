/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Two-torsion in tensor powers

If every element of a module `M` is its own additive inverse, then so is every element of an
indexed tensor power of `M` with at least one factor. This holds over a ring of characteristic two
and also, for instance, for a module of `𝔽₂`-valued cochains regarded over `ℤ`; it is how terms
appearing twice cancel in sign-free constructions on tensor powers.

## Main results

* `TauCeti.PiTensorProduct.add_self_eq_zero`: if every element of `M` is its own additive inverse,
  so is every element of a tensor power of `M` with at least one factor.
-/

public section

open Function
open scoped TensorProduct

universe uι uR uM

namespace TauCeti.PiTensorProduct

variable {ι : Type uι} {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- If every element of `M` is its own additive inverse, then so is every element of a tensor
power of `M` with at least one factor. With no factors the tensor power is `R`, about which the
hypothesis on `M` says nothing. -/
theorem add_self_eq_zero [Nonempty ι] (hM : ∀ m : M, m + m = 0) (x : ⨂[R] _ : ι, M) :
    x + x = 0 := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h := (PiTensorProduct.tprod R).map_update_add m i (m i) (m i)
    rw [update_eq_self, hM, MultilinearMap.map_update_zero] at h
    rw [← smul_add, ← h, smul_zero]
  | add x y hx hy => rw [add_add_add_comm, hx, hy, add_zero]

end TauCeti.PiTensorProduct
