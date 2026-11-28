/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Endomorphisms lowering a finite filtration

A linear map sending each filtration step into the preceding step has a vanishing power on
the whole module. In particular the idempotence error of an endomorphism that is idempotent
on each graded quotient is nilpotent, with exponent bounded by the length of the filtration.
-/

public section

namespace Module.End

open LinearMap

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- Applying a strictly filtration-lowering map `d` times kills the `d`-th step. -/
theorem pow_apply_eq_zero_of_filtration_lowering (f : End R V) {F : ℕ → Submodule R V}
    (hbot : F 0 = ⊥) {d : ℕ} (hf : ∀ i < d, (F (i + 1)).map f ≤ F i)
    {v : V} (hv : v ∈ F d) :
    (f ^ d) v = 0 := by
  induction d generalizing v with
  | zero =>
    rw [hbot, Submodule.mem_bot] at hv
    simp [hv]
  | succ d ih =>
    rw [pow_succ, _root_.mul_apply_eq_comp]
    exact ih (fun i hi ↦ hf i (Nat.lt_succ_of_lt hi)) (hf d (Nat.lt_succ_self d) ⟨v, hv, rfl⟩)

end Module.End

namespace Module.End

open LinearMap

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- If `T` acts idempotently on every successive quotient, its idempotence error has zero
`d`-th power. Here the quotient identity is expressed on representatives of each step. -/
theorem sub_sq_pow_eq_zero_of_graded_idempotent (T : End R V) {F : ℕ → Submodule R V}
    {d : ℕ} (hbot : F 0 = ⊥) (htop : F d = ⊤)
    (hgrade : ∀ i < d, ∀ v ∈ F (i + 1),
      (Submodule.Quotient.mk (T v) : V ⧸ F i) = Submodule.Quotient.mk (T (T v))) :
    (T - T ^ 2) ^ d = 0 := by
  ext v
  refine (T - T ^ 2).pow_apply_eq_zero_of_filtration_lowering hbot (fun i hi ↦ ?_)
    (htop ▸ Submodule.mem_top)
  rintro _ ⟨w, hw, rfl⟩
  simpa [pow_two, _root_.mul_apply_eq_comp] using
    (Submodule.Quotient.eq (F i)).mp (hgrade i hi w hw)

end Module.End
