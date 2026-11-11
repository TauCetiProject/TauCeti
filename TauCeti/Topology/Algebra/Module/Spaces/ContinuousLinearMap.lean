/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Conjugation of continuous endomorphisms by a continuous linear equivalence

For a continuous linear equivalence `e : G ≃L[𝕜] H`, the conjugate `e ∘ f ∘ e⁻¹` of a continuous
endomorphism `f` of `G` is the continuous endomorphism `f'` of `H` exactly when `e` intertwines
`f` with `f'`, that is `e (f x) = f' (e x)` for all `x`.

## Main results

* `ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_eq_iff_semiconj`: conjugation by `e`
  carries `f` to `f'` if and only if `e` semiconjugates `f` to `f'`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 G H : Type*} [NormedField 𝕜] [AddCommGroup G] [AddCommGroup H] [Module 𝕜 G]
  [Module 𝕜 H] [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalAddGroup G]
  [IsTopologicalAddGroup H] [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- Conjugation by a continuous linear equivalence `e` carries `f` to `f'` exactly when `e`
intertwines them: `e (f x) = f' (e x)` for all `x`. -/
theorem conjContinuousAlgEquiv_apply_eq_iff_semiconj (e : G ≃L[𝕜] H) (f : G →L[𝕜] G)
    (f' : H →L[𝕜] H) : e.conjContinuousAlgEquiv f = f' ↔ Function.Semiconj e f f' := by
  constructor
  · rintro rfl x
    simp
  · intro h
    ext y
    simpa using h (e.symm y)

end ContinuousLinearEquiv
