/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import TauCeti.Topology.Algebra.Module.ExtendByZero

/-!
# Interleaving finite coordinate spaces

Embed two finite coordinate spaces in one by placing the first in the even positions and the
second in the odd positions, filling unused positions with zero. The ambient dimension is
`2 * max a b`, so this convention is compatible with enlarging either input space. This is the
coordinate injection used for block sums of finite Grassmannians; see the references in
`TauCeti.Topology.Grassmannian.WhitneySum` for the classical disjoint-coordinate construction.

The linear construction uses Mathlib's `Function.ExtendByZero.linearMap` and
`LinearEquiv.sumArrowLequivProdArrow`.
-/

public section

namespace TauCeti

/-- The disjoint even/odd positions for two finite coordinate blocks. -/
def interleaveIndex (a b : ℕ) : Fin a ⊕ Fin b ↪ Fin (2 * max a b) where
  toFun := Sum.elim
    (fun i ↦ ⟨2 * i.val, by have := i.isLt; have := Nat.le_max_left a b; omega⟩)
    (fun i ↦ ⟨2 * i.val + 1, by have := i.isLt; have := Nat.le_max_right a b; omega⟩)
  inj' := by
    rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))

@[simp] theorem interleaveIndex_inl_val (a b : ℕ) (i : Fin a) :
    (interleaveIndex a b (.inl i)).val = 2 * i.val := (rfl)

@[simp] theorem interleaveIndex_inr_val (a b : ℕ) (i : Fin b) :
    (interleaveIndex a b (.inr i)).val = 2 * i.val + 1 := (rfl)

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] (a b : ℕ)

/-- Interleave two coordinate vectors, extending by zero outside their even/odd positions. -/
noncomputable def interleaveLinearMap : ((Fin a → M) × (Fin b → M)) →ₗ[R]
    (Fin (2 * max a b) → M) :=
  (Function.ExtendByZero.linearMap R M (interleaveIndex a b)).comp
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R M).symm.toLinearMap

variable {R M a b}

/-- The defining extension-by-zero formula for interleaving. -/
theorem interleaveLinearMap_apply (v : (Fin a → M) × (Fin b → M)) :
    interleaveLinearMap R M a b v = Function.extend (interleaveIndex a b)
      (Sum.elim v.1 v.2) 0 := (rfl)

@[simp] theorem interleaveLinearMap_apply_inl (v : (Fin a → M) × (Fin b → M)) (i : Fin a) :
    interleaveLinearMap R M a b v (interleaveIndex a b (.inl i)) = v.1 i :=
  (interleaveIndex a b).injective.extend_apply _ _ _

@[simp] theorem interleaveLinearMap_apply_inr (v : (Fin a → M) × (Fin b → M)) (i : Fin b) :
    interleaveLinearMap R M a b v (interleaveIndex a b (.inr i)) = v.2 i :=
  (interleaveIndex a b).injective.extend_apply _ _ _

/-- Unused coordinates of an interleaved vector vanish. -/
theorem interleaveLinearMap_apply_of_notMem_range (v : (Fin a → M) × (Fin b → M))
    {i : Fin (2 * max a b)} (hi : i ∉ Set.range (interleaveIndex a b)) :
    interleaveLinearMap R M a b v i = 0 :=
  Function.extend_apply' _ _ _ hi

/-- Both input vectors can be recovered from the interleaved vector. -/
theorem interleaveLinearMap_injective : Function.Injective (interleaveLinearMap R M a b) := by
  intro v w h
  apply Prod.ext
  · funext i
    simpa using congrFun h (interleaveIndex a b (.inl i))
  · funext i
    simpa using congrFun h (interleaveIndex a b (.inr i))

/-- Interleaving is continuous for the coordinate topologies, without assumptions on addition
or scalar multiplication. -/
@[fun_prop]
theorem continuous_interleaveLinearMap [TopologicalSpace R] :
    Continuous (interleaveLinearMap R R a b) := by
  have hc : Continuous (fun v : (Fin a → R) × (Fin b → R) ↦ Sum.elim v.1 v.2) :=
    continuous_pi fun i ↦ by
      cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  apply ((Function.ExtendByZero.continuousLinearMap R
    (interleaveIndex a b)).continuous.comp hc).congr
  intro v
  simp only [Function.comp_apply, Function.ExtendByZero.continuousLinearMap_apply,
    interleaveLinearMap_apply]

end TauCeti
