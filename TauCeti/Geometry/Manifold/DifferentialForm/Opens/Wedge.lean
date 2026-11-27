/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic

/-!
# Wedge products on open subsets

For open subsets `U ≤ W` of a manifold, wedging a form `φ` on `W` with the extension by zero of a
form `ψ` on `U` is the extension by zero of the wedge of the restriction of `φ` to `U` with `ψ`:
`φ ∧ ext ψ = ext (φ|_U ∧ ψ)`. This holds for every paired wedge `wedgeWith μ`
(`TauCeti.RoughForm.extendByZero_mpullback_inclusion_wedgeWith`), and in particular for the real
wedge (`TauCeti.RoughForm.extendByZero_mpullback_inclusion_wedge`).

Conversely, pairing a `0`-form on an open subset `U` with the pullback of a form on the ambient
manifold evaluates the pairing pointwise along the canonical tangent-space identification
(`TauCeti.RoughForm.wedgeWith_ofFunction_mpullback_apply`), and in degree `1` on an open subset
of a normed space this reads directly through `TauCeti.RoughForm.flatOneFormEquiv`
(`TauCeti.RoughForm.flatOneFormEquiv_wedgeWith_ofFunction_mpullback`).
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

/-- Pairing a `0`-form on an open subset `U` with the pullback of a form `η` on the ambient
manifold evaluates `μ` on the function value and `η` at the tangent vectors transported via
`TauCeti.Manifold.tangentSpaceOpenEquiv`. -/
theorem RoughForm.wedgeWith_ofFunction_mpullback_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {U : Opens M} (f : U → F₁) (η : RoughForm I M F₂ k)
    (z : U) (v : Fin (0 + k) → TangentSpace I z) :
    RoughForm.wedgeWith μ (RoughForm.ofFunction I f)
        (mpullback I I (Subtype.val : U → M) η) z v =
      μ (f z) (η (z : M) fun i ↦
        Manifold.tangentSpaceOpenEquiv (I := I) z (v (Fin.cast (zero_add k).symm i))) := by
  rw [RoughForm.wedgeWith_apply_zero_left, RoughForm.ofFunction_apply,
    mpullback_subtype_val_apply, Function.comp_def]
  simp only [Manifold.tangentSpaceOpenEquiv_apply]
  -- `TangentSpace I z` and `TangentSpace I (z : M)` are both definitionally the model space `E`.
  rfl

/-- Evaluating the flat `1`-form of `f ∧_μ (ι^* η)` on an open subset `U` of a normed space `E`
pairs `f z` with `η (z : E)` on the tangent vector corresponding to `a : E`. -/
theorem RoughForm.flatOneFormEquiv_wedgeWith_ofFunction_mpullback (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {U : Opens E} (f : U → F₁) (η : RoughForm 𝓘(ℝ, E) E F₂ 1) (z : U) (a : E) :
    RoughForm.flatOneFormEquiv U
        (RoughForm.wedgeWith μ (RoughForm.ofFunction 𝓘(ℝ, E) f)
          (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) η)) z a =
      μ (f z) (η (z : E) ![(NormedSpace.fromTangentSpace (z : E)).symm a]) := by
  rw [RoughForm.flatOneFormEquiv_apply, RoughForm.wedgeWith_ofFunction_mpullback_apply]
  congr 2
  ext i
  fin_cases i
  simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cast_eq_self, Matrix.cons_val,
    Matrix.cons_val_fin_one]
  -- Both `TangentSpace 𝓘(ℝ, E) z` and `TangentSpace 𝓘(ℝ, E) (z : E)` are definitionally `E`.
  exact (Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, E)) z
    (a : TangentSpace 𝓘(ℝ, E) z)).trans (NormedSpace.fromTangentSpace_symm_apply (z : E) a).symm

end TauCeti
