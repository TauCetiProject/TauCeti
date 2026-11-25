/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.LinearAlgebra.TensorPower.Basic
public import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Tensor powers of invertible modules

The tensor powers `⨂[R]^n M` of an invertible module `M` are invertible
(`Module.Invertible.tensorPower`), and their class in the Picard group is the `n`-th power of the
class of `M` (`CommRing.Pic.mk_tensorPower`). Pure tensors of an invertible module are controlled
by diagonal tensors: if `ξ y` is the value of a functional on a vector, then
`ξ y ^ n • (x₁ ⊗ ⋯ ⊗ xₙ) = (∏ ξ xᵢ) • (y ⊗ ⋯ ⊗ y)`
(`Module.Invertible.apply_pow_card_smul_tprod`).

## Main declarations

* `Module.Invertible.apply_pow_card_smul_tprod`: `ξ y ^ n • ⨂ xᵢ = (∏ ξ xᵢ) • ⨂ y` in an
  invertible module.
* `Module.Invertible.tensorPower`: tensor powers of an invertible module are invertible.
* `CommRing.Pic.mk_tensorPower`: the class of `⨂[R]^n L` is the `n`-th power of the class of `L`.
-/

public section

noncomputable section

open Module TensorProduct PiTensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace Module.Invertible

variable [Module.Invertible R M]

/-- In an invertible module, scaling a pure tensor `x₁ ⊗ ⋯ ⊗ xₙ` by `ξ y ^ n` gives a multiple of
the diagonal tensor `y ⊗ ⋯ ⊗ y`, with coefficient `∏ ξ xᵢ`. -/
theorem apply_pow_card_smul_tprod {ι : Type*} [Fintype ι] (ξ : Dual R M) (y : M) (x : ι → M) :
    ξ y ^ Fintype.card ι • tprod R x = (∏ i, ξ (x i)) • tprod R fun _ : ι ↦ y := by
  calc ξ y ^ Fintype.card ι • tprod R x = tprod R fun i ↦ ξ y • x i := by
        simp [MultilinearMap.map_smul_univ]
    _ = tprod R fun i ↦ ξ (x i) • y := by simp_rw [apply_smul_comm ξ y]
    _ = (∏ i, ξ (x i)) • tprod R fun _ : ι ↦ y := by simp [MultilinearMap.map_smul_univ]

/-- Tensor powers of an invertible module are invertible. -/
instance tensorPower (n : ℕ) : Module.Invertible R (⨂[R]^n M) := by
  induction n with
  | zero => exact .congr (isEmptyEquiv (Fin 0)).symm
  | succ n ih => exact .congr (TauCeti.TensorPower.succEquiv R M n)

end Module.Invertible

namespace CommRing.Pic

variable [Module.Invertible R M]

/-- The class of the `n`-th tensor power `⨂[R]^n M` in the Picard group is the `n`-th power of
the class of `M`. -/
theorem mk_tensorPower (n : ℕ) : Pic.mk R (⨂[R]^n M) = Pic.mk R M ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, mk_eq_one_iff]
    exact ⟨isEmptyEquiv (Fin 0)⟩
  | succ n ih =>
    rw [pow_succ, ← ih, ← mk_tensor, mk_eq_mk_iff]
    exact ⟨(TauCeti.TensorPower.succEquiv R M n).symm⟩

end CommRing.Pic
