/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic

/-!
# Wedge products and extension by zero

For open subsets `U ≤ W` of a manifold, wedging a form `φ` on `W` with the extension by zero of a
form `ψ` on `U` is the extension by zero of the wedge of the restriction of `φ` to `U` with `ψ`:
`φ ∧ ext ψ = ext (φ|_U ∧ ψ)`. This holds for every paired wedge `wedgeWith μ`
(`TauCeti.RoughForm.extendByZero_mpullback_inclusion_wedgeWith`), and in particular for the real
wedge (`TauCeti.RoughForm.extendByZero_mpullback_inclusion_wedge`).
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] {k l : ℕ}

/-- Pairing a form on `W` with the extension by zero of a form on an open subset `U ≤ W` is the
extension by zero of the pairing of its restriction to `U` with that form:
`φ ∧_μ ext ψ = ext (φ|_U ∧_μ ψ)`. -/
theorem RoughForm.extendByZero_mpullback_inclusion_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {U W : Opens M} (h : U ≤ W) (φ : RoughForm I W F₁ k) (ψ : RoughForm I U F₂ l) :
    RoughForm.extendByZero W ((mpullback I I (Opens.inclusion h) φ).wedgeWith μ ψ) =
      φ.wedgeWith μ (RoughForm.extendByZero W ψ) := by
  funext x
  rw [RoughForm.wedgeWith_apply']
  by_cases hx : (x : M) ∈ U
  · rw [RoughForm.extendByZero_apply_of_mem _ hx, RoughForm.extendByZero_apply_of_mem _ hx,
      RoughForm.wedgeWith_apply', mpullback_inclusion_apply]
    -- `Opens.inclusion h ⟨x, hx⟩` is `x` by structure eta for the subtype `W`. The point also
    -- appears in the types of the tangent-space arguments, so `rw` cannot replace it.
    rfl
  · rw [RoughForm.extendByZero_apply_of_notMem _ hx, RoughForm.extendByZero_apply_of_notMem _ hx]
    simp

/-- Wedging a form on `W` with the extension by zero of a form on an open subset `U ≤ W` is the
extension by zero of the wedge of its restriction to `U` with that form:
`φ ∧ ext ψ = ext (φ|_U ∧ ψ)`. -/
theorem RoughForm.extendByZero_mpullback_inclusion_wedge {U W : Opens M} (h : U ≤ W)
    (φ : RoughForm I W ℝ k) (ψ : RoughForm I U ℝ l) :
    RoughForm.extendByZero W ((mpullback I I (Opens.inclusion h) φ).wedge ψ) =
      φ.wedge (RoughForm.extendByZero W ψ) := by
  rw [RoughForm.wedge_def, RoughForm.wedge_def,
    RoughForm.extendByZero_mpullback_inclusion_wedgeWith]

end TauCeti
