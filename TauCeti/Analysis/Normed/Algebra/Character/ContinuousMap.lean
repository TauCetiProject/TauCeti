/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Ideals

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Algebra.GroupWithZero.Hom

/-!
# Multiplicative functionals on `C(X, ℂ)`

Mathlib identifies the characters of `C(X, ℂ)`, for a compact Hausdorff space `X`, with the
points of `X` (`WeakDual.CharacterSpace.continuousMapEval_bijective`); these characters are
unital algebra homomorphisms. A multiplicative linear functional that is not assumed unital is
also allowed to be `0`, and by `MulHomClass.forall_apply_eq_zero_or_map_one` it is otherwise
unital:

* `ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval`: a nonunital algebra homomorphism
  `C(X, ℂ) →ₙₐ[ℂ] ℂ` is either `0` or the evaluation at a point of `X`.
-/

public section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A multiplicative linear functional on `C(X, ℂ)` that need not preserve `1` is either `0` or
the evaluation at a point. -/
theorem nonUnitalAlgHom_eq_zero_or_exists_eval (ψ : C(X, ℂ) →ₙₐ[ℂ] ℂ) :
    ψ = 0 ∨ ∃ x : X, ∀ f, ψ f = f x := by
  refine (MulHomClass.forall_apply_eq_zero_or_map_one ψ).imp NonUnitalAlgHom.ext fun h1 ↦ ?_
  let φ : C(X, ℂ) →ₐ[ℂ] ℂ :=
    { ψ with
      map_one' := h1
      commutes' := fun c ↦ by simp [Algebra.algebraMap_eq_smul_one, h1] }
  have hφ : ∀ f, φ f = ψ f := fun _ ↦ rfl
  obtain ⟨x, hx⟩ :=
    (WeakDual.CharacterSpace.continuousMapEval_bijective X ℂ).2
      (WeakDual.CharacterSpace.equivAlgHom.symm φ)
  refine ⟨x, fun f ↦ ?_⟩
  rw [← hφ, ← WeakDual.CharacterSpace.equivAlgHom_symm_coe, ← hx,
    WeakDual.CharacterSpace.continuousMapEval_apply_apply]

end ContinuousMap
