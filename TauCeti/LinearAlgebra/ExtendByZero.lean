/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear extension of coordinate functions by zero

Mathlib's `Function.ExtendByZero.linearMap` along an injective index map is injective. Along
`Fin.castSucc` it views `R^N` as the coordinate hyperplane of `R^(N + 1)` with vanishing last
coordinate, and along `Fin.succ` it is the coordinate shift `e_i ↦ e_(i + 1)`, whose image is the
hyperplane with vanishing first coordinate.
This file records that `Fin.init` and `Fin.tail` invert these extensions, and that the shift
together with the first basis vector `e₀ = Pi.single 0 1` splits `R^(N + 1)`: every vector is
its first coordinate times `e₀` plus the shift of its tail. Consequently `R e₀ ⊕ shift X`
consists of the vectors whose tail lies in `X`, and over a division ring its dimension is one
more than that of `X`.
-/

public section

open Module

namespace Function.ExtendByZero

variable {R : Type*} [Semiring R]

/-- Extension by zero along an injective index map is injective. -/
theorem linearMap_injective {ι κ : Type*} {e : ι → κ} (he : Injective e) :
    Injective (linearMap R R e) :=
  extend_injective he (0 : κ → R)

variable {N : ℕ}

/-- Taking the tail undoes the coordinate shift along `Fin.succ`. -/
@[simp]
theorem tail_linearMap_succ (v : Fin N → R) : Fin.tail (linearMap R R Fin.succ v) = v := by
  funext i
  simp [Fin.tail, (Fin.succ_injective N).extend_apply]

/-- Taking the initial segment undoes the extension by zero along `Fin.castSucc`. -/
@[simp]
theorem init_linearMap_castSucc (v : Fin N → R) :
    Fin.init (linearMap R R Fin.castSucc v) = v := by
  funext i
  simp [Fin.init, (Fin.castSucc_injective N).extend_apply]

/-- The extension by zero along `Fin.castSucc` vanishes at the last coordinate. -/
theorem linearMap_castSucc_last (v : Fin N → R) :
    linearMap R R Fin.castSucc v (Fin.last N) = 0 := by
  simp

/-- Every vector of `R^(N + 1)` is its first coordinate times `e₀` plus the shift of its tail. -/
theorem eq_smul_single_zero_add_linearMap_succ_tail (w : Fin (N + 1) → R) :
    w = w 0 • Pi.single 0 1 + linearMap R R Fin.succ (Fin.tail w) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp [(Fin.succ_injective N).extend_apply, Fin.tail]

/-- The first basis vector `e₀` is not in the image of the coordinate shift. -/
theorem single_zero_notMem_range_linearMap_succ [Nontrivial R] :
    (Pi.single 0 1 : Fin (N + 1) → R) ∉
      LinearMap.range (linearMap R R (Fin.succ : Fin N → Fin (N + 1))) := by
  rintro ⟨v, hv⟩
  have h := congrFun hv 0
  simp at h

/-- A vector lies in `R e₀ ⊕ shift X` exactly when its tail lies in `X`. -/
theorem mem_span_single_zero_sup_map_linearMap_succ_iff (X : Submodule R (Fin N → R))
    (w : Fin (N + 1) → R) :
    w ∈ (R ∙ Pi.single 0 1) ⊔ X.map (linearMap R R Fin.succ) ↔ Fin.tail w ∈ X := by
  constructor
  · intro hw
    obtain ⟨a, ha, b, ⟨v, hv, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    have htail : Fin.tail (c • Pi.single 0 1 + linearMap R R Fin.succ v) =
        Fin.tail (linearMap R R Fin.succ v) := by
      funext i
      simp [Fin.tail, Fin.succ_ne_zero]
    rwa [htail, tail_linearMap_succ]
  · intro hw
    rw [eq_smul_single_zero_add_linearMap_succ_tail w]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      (Submodule.mem_map_of_mem hw)

/-- Adjoining `e₀` to the shift of `X` raises the dimension by one. -/
theorem finrank_span_single_zero_sup_map_linearMap_succ {K : Type*} [DivisionRing K]
    (X : Submodule K (Fin N → K)) :
    finrank K ↥((K ∙ Pi.single 0 1) ⊔ X.map (linearMap K K Fin.succ)) = finrank K X + 1 := by
  rw [sup_comm, Submodule.finrank_sup_span_singleton fun h ↦
    single_zero_notMem_range_linearMap_succ (LinearMap.map_le_range h),
    ← (Submodule.equivMapOfInjective _ (linearMap_injective (Fin.succ_injective N))
      X).finrank_eq]

end Function.ExtendByZero
