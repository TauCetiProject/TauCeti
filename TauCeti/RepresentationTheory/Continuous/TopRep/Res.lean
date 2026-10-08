/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Iterated restriction of topological representations

This file supplements Mathlib's restriction `TopRep.res φ` of a topological representation along a
monoid homomorphism `φ` with its behaviour under composition: restricting along `φ` and then along
`ψ` is restricting along `φ.comp ψ`, restricting along the identity does nothing, and so restricting
along an isomorphism of topological groups and then along its inverse gives the representation
back.

## Main results

* `TopRep.res_res`: `Res_ψ (Res_φ X) = Res_{φ ∘ ψ} X`.
* `TopRep.res_id`: `Res_id X = X`.
* `TopRep.res_symm_res`: `Res_{e⁻¹} (Res_e X) = X` for `e : H ≃ₜ* G`.
-/

public section

namespace TopRep

variable {k G H K : Type*} [Ring k] [TopologicalSpace k] [Group G] [Group H] [Monoid K]

/-- Restricting along `φ` and then along `ψ` is restricting along the composite `φ.comp ψ`. -/
@[simp]
theorem res_res (φ : H →* G) (ψ : K →* H) (X : TopRep k G) :
    res ψ (res φ X) = res (φ.comp ψ) X :=
  rfl

/-- Restricting along the identity gives back the representation. -/
@[simp]
theorem res_id (X : TopRep k G) : res (MonoidHom.id G) X = X :=
  rfl

-- Not `@[simp]`: `res_res` already rewrites the left-hand side to a single restriction along
-- `(e : H →* G).comp e.symm`, so the simpNF linter rejects this lemma as a simp lemma.
/-- Restricting along `e : H ≃ₜ* G` and then along `e⁻¹` gives back the representation. -/
theorem res_symm_res [TopologicalSpace G] [TopologicalSpace H] (e : H ≃ₜ* G) (X : TopRep k G) :
    res ((e.symm : G →ₜ* H) : G →* H) (res ((e : H →ₜ* G) : H →* G) X) = X := by
  have hcomp : ((e : H →ₜ* G) : H →* G).comp ((e.symm : G →ₜ* H) : G →* H) = .id G :=
    MonoidHom.ext e.apply_symm_apply
  rw [res_res, hcomp, res_id]

end TopRep
