/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Tensoring an abelian group with `ℤ/n`

For an abelian group `G` and a natural number `n`, the tensor product `ℤ/n ⊗_ℤ G` is the
quotient `G / nG` (Mathlib's `TensorProduct.quotTensorEquivQuotSMul`, read through
`Int.quotientSpanNatEquivZMod`). So it vanishes exactly when `G` is `n`-divisible, that is, when
multiplication by `n` on `G` is surjective. Both tensor factor orders are recorded.

For `n = 2` this is the statement `G ⊗ ℤ/2 = 0` in which the vanishing of mod-two homology is
usually phrased: it says that `G` is two-divisible, and it holds in particular for every
uniquely two-divisible group.

## Main results

* `TauCeti.subsingleton_zmod_tensorProduct_iff`: `ℤ/n ⊗_ℤ G = 0` exactly when multiplication by
  `n` on `G` is surjective.
* `TauCeti.subsingleton_tensorProduct_zmod_iff`: the same with `G` as the left factor.
-/

public section

namespace TauCeti

variable {G : Type*} [AddCommGroup G]

/-- **`ℤ/n ⊗_ℤ G` vanishes exactly when `G` is `n`-divisible**: the tensor product is the
quotient `G / nG`. -/
theorem subsingleton_zmod_tensorProduct_iff (n : ℕ) :
    Subsingleton (TensorProduct ℤ (ZMod n) G) ↔ Function.Surjective fun x : G ↦ (n : ℤ) • x := by
  let e : TensorProduct ℤ (ZMod n) G ≃ₗ[ℤ] G ⧸ (Ideal.span {(n : ℤ)} • (⊤ : Submodule ℤ G)) :=
    (TensorProduct.congr (Int.quotientSpanNatEquivZMod n).toAddEquiv.toIntLinearEquiv.symm
      (LinearEquiv.refl ℤ G)).trans (TensorProduct.quotTensorEquivQuotSMul G _)
  rw [e.toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff,
    Submodule.ideal_span_singleton_smul, eq_top_iff]
  refine ⟨fun h x ↦ ?_, fun h x _ ↦ ?_⟩
  · obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h trivial)
    exact ⟨y, hy⟩
  · obtain ⟨y, rfl⟩ := h x
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

/-- **`G ⊗_ℤ ℤ/n` vanishes exactly when `G` is `n`-divisible**, with `G` as the left tensor
factor. -/
theorem subsingleton_tensorProduct_zmod_iff (n : ℕ) :
    Subsingleton (TensorProduct ℤ G (ZMod n)) ↔ Function.Surjective fun x : G ↦ (n : ℤ) • x := by
  rw [← subsingleton_zmod_tensorProduct_iff,
    (TensorProduct.comm ℤ G (ZMod n)).toEquiv.subsingleton_congr]

end TauCeti
