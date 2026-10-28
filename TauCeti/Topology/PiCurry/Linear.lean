/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.PiCurry

/-!
# Continuous linear regrouping of families

The regrouping homeomorphism `TauCeti.piSigmaConstHomeomorph` preserves pointwise addition and
scalar multiplication. This file gives it the continuous linear structure, for arbitrary index
families and topological modules over a semiring. The forward and inverse coercion lemmas identify
it with the existing homeomorphism, so coordinate and differential calculations can use both APIs.
-/

public section

namespace TauCeti

/-- Regrouping a family of tuples along a bijection of the sigma index, as a continuous linear
equivalence. The underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`. -/
def piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → E) ≃L[R] (ι' → E) where
  toLinearEquiv :=
    { toFun := piSigmaConstHomeomorph E e
      invFun := (piSigmaConstHomeomorph E e).symm
      left_inv := (piSigmaConstHomeomorph E e).left_inv
      right_inv := (piSigmaConstHomeomorph E e).right_inv
      map_add' := by
        intro x y
        ext j
        simp only [piSigmaConstHomeomorph_apply, Pi.add_apply]
      map_smul' := by
        intro a x
        ext j
        simp only [piSigmaConstHomeomorph_apply, Pi.smul_apply, RingHom.id_apply] }
  continuous_toFun := (piSigmaConstHomeomorph E e).continuous
  continuous_invFun := (piSigmaConstHomeomorph E e).symm.continuous

/-- The continuous linear regrouping has the existing regrouping homeomorphism as its function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (piSigmaConstContinuousLinearEquiv R E e : (∀ i, κ i → E) → (ι' → E)) =
      piSigmaConstHomeomorph E e := (rfl)

/-- The inverse continuous linear regrouping has the inverse regrouping homeomorphism as its
function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv_symm (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    ((piSigmaConstContinuousLinearEquiv R E e).symm : (ι' → E) → ∀ i, κ i → E) =
      (piSigmaConstHomeomorph E e).symm := (rfl)

end TauCeti
