/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.Flow.Diffeomorph
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Symplectomorphisms preserving a primitive commute with the Liouville flow

Let `σ` be a two-form on `M` with primitive `θ`, `σ = -dθ`. Its Liouville vector field `Z`,
with `L_Z σ = σ`, is determined by `ι_Z σ = -θ` when `σ` is nondegenerate. A symplectomorphism
which also preserves the primitive `θ` must therefore preserve `Z`, and so commute with its flow.

This file proves the statement for an arbitrary one-form `α` in place of `-θ`, for a vector field
`Z` with `ι_Z σ = α`: if a local diffeomorphism `f : M → M₂` satisfies `f^*σ₂ = σ` and
`f^*α₂ = α` with `σ₂` nondegenerate, then `df (Z x) = Z₂ (f x)` whenever `ι_{Z₂} σ₂ = α₂`
(`IsLocalDiffeomorph.mfderiv_apply_eq_of_interior_eq`). Indeed both vectors pair under `σ₂` with
`df v` to `α v`, and the differential of `f` is onto. Neither closedness of the forms nor finite
dimensionality is needed. For a diffeomorphism `ψ`, apply it to `ψ.isLocalDiffeomorph`. With
`α = -θ` this is the naturality of Liouville vector fields; with `α = df` it is the naturality of
Hamiltonian vector fields under symplectomorphisms preserving the Hamiltonian.

By naturality of flows, `ψ` then conjugates the maximal flows of `Z` and `Z₂`, which for
`M₂ = M` says that `ψ` commutes with the local flow of `Z`
(`Diffeomorph.apply_flowOf_of_interior_eq`).

## Main results

* `IsLocalDiffeomorph.mfderiv_apply_eq_of_interior_eq`: a local diffeomorphism preserving the
  two-forms and the one-forms carries the vector field dual to one to the vector field dual to the
  other.
* `Diffeomorph.apply_flowOf_of_interior_eq`: a diffeomorphism preserving the two-forms and the
  one-forms conjugates the maximal flows of the dual vector fields; in particular
  symplectomorphisms preserving a primitive commute with the local Liouville flow.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 3 (Liouville vector fields and exact symplectomorphisms).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3 (symplectomorphisms of cotangent bundles).
-/

public section

open scoped ContDiff Manifold

namespace Diffeomorph

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  {σ : SmoothTwoForm I M} {σ₂ : SmoothTwoForm I₂ M₂}
  {α : RoughForm I M ℝ 1} {α₂ : RoughForm I₂ M₂ ℝ 1}
  {Z : (x : M) → TangentSpace I x} {Z₂ : (y : M₂) → TangentSpace I₂ y}

/-- **Naturality of the vector field dual to a one-form, along a local diffeomorphism.** Let
`f : M → M₂` be a local diffeomorphism with `f^*σ₂ = σ` and `f^*α₂ = α`, where `σ₂` is
nondegenerate. If `ι_Z σ = α` and `ι_{Z₂} σ₂ = α₂`, then `df_x (Z x) = Z₂ (f x)` for every `x`.
Only the surjectivity of each differential of `f` is used. -/
theorem _root_.IsLocalDiffeomorph.mfderiv_apply_eq_of_interior_eq {f : M → M₂}
    (hf : IsLocalDiffeomorph I I₂ ∞ f) (hσ₂ : σ₂.IsNondegenerate)
    (hσ : SmoothForm.mpullback f hf.contMDiff σ₂ = σ) (hα : mpullback I I₂ f α₂ = α)
    (hZ : RoughForm.interior Z σ.val = α) (hZ₂ : RoughForm.interior Z₂ σ₂.val = α₂) (x : M) :
    mfderiv I I₂ f x (Z x) = Z₂ (f x) := by
  rw [← sub_eq_zero]
  refine SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ₂ (f x) _ fun w ↦ ?_
  obtain ⟨v, rfl⟩ := (hf.isInvertible_mfderiv (by simp) x).surjective w
  -- Both vectors pair with `df v` to `α v`: `σ₂(df Z, df v) = σ(Z, v) = α v`, and
  -- `α v = α₂(df v) = σ₂(Z₂, df v)`.
  have h₁ : SmoothBundleForm.eval₂ σ₂ (f x) (mfderiv I I₂ f x (Z x)) (mfderiv I I₂ f x v) =
      α x ![v] := by
    rw [← SmoothForm.eval₂_mpullback f hf.contMDiff, hσ, SmoothBundleForm.eval₂_apply, ← hZ,
      RoughForm.interior_apply]
  have hv : (fun i ↦ mfderiv I I₂ f x (![v] i)) = ![mfderiv I I₂ f x v] := by
    ext i
    fin_cases i
    rfl
  have h₂ : α x ![v] = SmoothBundleForm.eval₂ σ₂ (f x) (Z₂ (f x)) (mfderiv I I₂ f x v) := by
    rw [← hα, mpullback_apply, hv, ← hZ₂, RoughForm.interior_apply, SmoothBundleForm.eval₂_apply]
  rw [← SmoothForm.bilinFormAt_apply, map_sub, LinearMap.sub_apply, SmoothForm.bilinFormAt_apply,
    SmoothForm.bilinFormAt_apply, h₁, h₂, sub_self]

variable [T2Space M₂] [BoundarylessManifold I₂ M₂]

/-- **Symplectomorphisms preserving a primitive commute with the Liouville flow.** Let `ψ : M → M₂`
be a diffeomorphism with `ψ^*σ₂ = σ` and `ψ^*α₂ = α`, where `σ₂` is nondegenerate, and let
`ι_Z σ = α` and `ι_{Z₂} σ₂ = α₂` with `Z₂` of class `C^1`. Then `ψ` conjugates the maximal flows:
`ψ (flowOf Z t x) = flowOf Z₂ t (ψ x)`. For `M₂ = M` and `α = -θ` with `σ = -dθ`, a
symplectomorphism preserving `θ` commutes with the local flow of the Liouville field of `θ`. -/
theorem apply_flowOf_of_interior_eq (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hσ₂ : σ₂.IsNondegenerate)
    (hσ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) (hα : mpullback I I₂ ψ α₂ = α)
    (hZ : RoughForm.interior Z σ.val = α) (hZ₂ : RoughForm.interior Z₂ σ₂.val = α₂)
    (hZ₂' : CMDiff 1 (fun y ↦ (⟨y, Z₂ y⟩ : TangentBundle I₂ M₂))) (t : ℝ) (x : M) :
    ψ (flowOf Z t x) = flowOf Z₂ t (ψ x) :=
  ψ.apply_flowOf (by simp) hZ₂'
    (ψ.isLocalDiffeomorph.mfderiv_apply_eq_of_interior_eq hσ₂ hσ hα hZ hZ₂) t x

end Diffeomorph
