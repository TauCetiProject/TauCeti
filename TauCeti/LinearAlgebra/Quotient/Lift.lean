/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Lifting maps of subspaces and quotients

Over a division ring, a map `B → A` between subspaces together with a map `W ⧸ B → V ⧸ A` between
the quotients is induced by a single linear map `W → V` taking `B` into `A`
(`Submodule.exists_restrict_eq_and_mapQ_eq`): extend the first map to `W`, lift the second
through `V → V ⧸ A`, and add.

## References

* Adapted from `New.Hall.exists_restrict_eq_and_mapQ_eq` of `src/Lib/LocalGL/Green/HallAlgebra.lean`
  in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- Any maps `B → A` and `W ⧸ B → V ⧸ A` are induced by one map `W → V` that takes `B` into
`A`. -/
theorem Submodule.exists_restrict_eq_and_mapQ_eq {A : Submodule K V} {B : Submodule K W}
    (α : B →ₗ[K] A) (β : W ⧸ B →ₗ[K] V ⧸ A) :
    ∃ (y : W →ₗ[K] V) (hy : B ≤ A.comap y), y.restrict hy = α ∧ B.mapQ A y hy = β := by
  -- Extend `α` to `c : W → A`, lift `β` to `r : W ⧸ B → V`, and add.
  obtain ⟨c, rfl⟩ : ∃ c : W →ₗ[K] A, c ∘ₗ B.subtype = α := α.exists_extend
  obtain ⟨r, rfl⟩ := Module.projective_lifting_property _ β A.mkQ_surjective
  refine ⟨A.subtype ∘ₗ c + r ∘ₗ B.mkQ, fun w hw ↦ ?_, ?_, ?_⟩
  · simp [(Submodule.Quotient.mk_eq_zero B).2 hw]
  · ext w
    simp [(Submodule.Quotient.mk_eq_zero B).2 w.prop]
  · ext w
    simp [(Submodule.Quotient.mk_eq_zero A).2 (c w).prop]
