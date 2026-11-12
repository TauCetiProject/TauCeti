/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv

/-!
# The postcomposition action of algebra equivalences on algebra maps

For algebras `L` and `M` over a commutative semiring `K`, the group `M ≃ₐ[K] M` acts on the set
of algebra maps `L →ₐ[K] M` by postcomposition, `σ • φ = σ ∘ φ`.

Only semiring structure is involved, so the action is defined here rather than alongside the
field-theoretic facts about it. The orbits and the kernel of this action are what turn a set of
embeddings into a group-theoretic object; those statements need fields and live in
`TauCeti/FieldTheory/Normal/Embeddings.lean`.

## Main results

* `AlgEquiv.smul_algHom_def`: the action is postcomposition, `σ • φ = σ.toAlgHom.comp φ`.
* `AlgEquiv.smul_algHom_apply`: it evaluates as `σ` after `φ`.
* `AlgEquiv.smul_algHom_eq_self_iff`: an equivalence fixes an algebra map exactly when it fixes
  its values.
-/

public section

namespace AlgEquiv

variable {K L M : Type*} [CommSemiring K] [Semiring L] [Semiring M] [Algebra K L] [Algebra K M]

/-- Postcomposition makes `L →ₐ[K] M` an `M ≃ₐ[K] M`-set: `σ • φ = σ ∘ φ`. -/
instance mulActionAlgHom : MulAction (M ≃ₐ[K] M) (L →ₐ[K] M) where
  smul σ φ := σ.toAlgHom.comp φ
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The action is postcomposition. -/
theorem smul_algHom_def (σ : M ≃ₐ[K] M) (φ : L →ₐ[K] M) : σ • φ = σ.toAlgHom.comp φ :=
  rfl

/-- **The action is evaluation of `σ` after `φ`.** -/
@[simp]
theorem smul_algHom_apply (σ : M ≃ₐ[K] M) (φ : L →ₐ[K] M) (x : L) : (σ • φ) x = σ (φ x) :=
  rfl

/-- **An algebra equivalence fixes an algebra map exactly when it fixes its values.** -/
theorem smul_algHom_eq_self_iff {σ : M ≃ₐ[K] M} {φ : L →ₐ[K] M} :
    σ • φ = φ ↔ ∀ x, σ (φ x) = φ x := by
  simp only [AlgHom.ext_iff, smul_algHom_apply]

end AlgEquiv

end
