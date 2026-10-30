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
`Z` with `ι_Z σ = α`: if a diffeomorphism `ψ : M → M₂` satisfies `ψ^*σ₂ = σ` and `ψ^*α₂ = α` with
`σ₂` nondegenerate, then `dψ (Z x) = Z₂ (ψ x)` whenever `ι_{Z₂} σ₂ = α₂`
(`Diffeomorph.mfderiv_apply_eq_of_interior_eq`). Indeed both vectors pair under `σ₂` with
`dψ v` to `α v`, and the differential of `ψ` is onto. Neither closedness of the forms nor finite
dimensionality is needed. With `α = -θ` this is the naturality of Liouville vector fields; with
`α = df` it is the naturality of Hamiltonian vector fields under symplectomorphisms preserving the
Hamiltonian.

By naturality of flows, `ψ` then conjugates the maximal flows of `Z` and `Z₂`, which for
`M₂ = M` says that `ψ` commutes with the local flow of `Z`
(`Diffeomorph.apply_flowOf_of_interior_eq`).

## Main results

* `Diffeomorph.mfderiv_apply_eq_of_interior_eq`: a symplectomorphism preserving the one-forms
  carries the vector field dual to one to the vector field dual to the other.
* `Diffeomorph.apply_flowOf_of_interior_eq`: such a symplectomorphism conjugates their maximal
  flows; in particular symplectomorphisms preserving a primitive commute with the local Liouville
  flow.

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

/-- **Naturality of the vector field dual to a one-form.** Let `ψ : M → M₂` be a diffeomorphism
with `ψ^*σ₂ = σ` and `ψ^*α₂ = α`, where `σ₂` is nondegenerate. If `ι_Z σ = α` and
`ι_{Z₂} σ₂ = α₂`, then `dψ_x (Z x) = Z₂ (ψ x)` for every `x`. For `α = -θ` with `σ = -dθ`, this
says that a symplectomorphism preserving the primitives carries the Liouville field of `θ` to that
of `θ₂`. -/
theorem mfderiv_apply_eq_of_interior_eq (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hσ₂ : σ₂.IsNondegenerate)
    (hσ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) (hα : mpullback I I₂ ψ α₂ = α)
    (hZ : σ.1.interior Z = α) (hZ₂ : σ₂.1.interior Z₂ = α₂) (x : M) :
    mfderiv I I₂ ψ x (Z x) = Z₂ (ψ x) := by
  rw [← sub_eq_zero]
  refine SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ₂ (ψ x) _ fun w ↦ ?_
  obtain ⟨v, rfl⟩ := (ψ.isInvertible_mfderiv (by simp) (x := x)).surjective w
  -- Both vectors pair with `dψ v` to `α v`: `σ₂(dψ Z, dψ v) = σ(Z, v) = α v`, and
  -- `α v = α₂(dψ v) = σ₂(Z₂, dψ v)`.
  have h₁ : SmoothForm.eval₂ σ₂ (ψ x) (mfderiv I I₂ ψ x (Z x)) (mfderiv I I₂ ψ x v) =
      α x ![v] := by
    rw [← SmoothForm.eval₂_mpullback ψ ψ.contMDiff, hσ, SmoothForm.eval₂_apply, ← hZ,
      RoughForm.interior_apply]
  have hv : (fun i ↦ mfderiv I I₂ ψ x (![v] i)) = ![mfderiv I I₂ ψ x v] := by
    ext i
    fin_cases i
    rfl
  have h₂ : α x ![v] = SmoothForm.eval₂ σ₂ (ψ x) (Z₂ (ψ x)) (mfderiv I I₂ ψ x v) := by
    rw [← hα, mpullback_apply, hv, ← hZ₂, RoughForm.interior_apply, SmoothForm.eval₂_apply]
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
    (hZ : σ.1.interior Z = α) (hZ₂ : σ₂.1.interior Z₂ = α₂)
    (hZ₂' : CMDiff 1 (fun y ↦ (⟨y, Z₂ y⟩ : TangentBundle I₂ M₂))) (t : ℝ) (x : M) :
    ψ (flowOf Z t x) = flowOf Z₂ t (ψ x) :=
  ψ.apply_flowOf (by simp) hZ₂' (ψ.mfderiv_apply_eq_of_interior_eq hσ₂ hσ hα hZ hZ₂) t x

end Diffeomorph
