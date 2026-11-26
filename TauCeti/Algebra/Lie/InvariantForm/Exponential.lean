/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Analysis.SpecialFunctions.Exponential.BilinForm

/-!
# The inner automorphisms `exp (s ad X)` of a real Lie algebra

Let `L` be a finite-dimensional real Lie algebra with an invariant bilinear form `B`, and `X ∈ L`.
For every `s ∈ ℝ` there is a Lie algebra automorphism `θ` of `L` preserving `B` whose matrix in
every basis of `L` is the matrix exponential `exp (s M)` of the matrix `M` of `ad X`
(`LinearMap.BilinForm.exists_lieEquiv_apply_eq_cos_smul_add_sin_smul`): it is the automorphism
`exp (s ad X)`, identified without choosing a norm on `L`. It fixes every element commuting with
`X`, and it rotates every pair `p, q` with `⁅X, p⁆ = q` and `⁅X, q⁆ = -p` by the angle `s`:
`θ p = cos s • p + sin s • q`.

The proof computes `θ` as the operator exponential of `s ad X` for an auxiliary norm on `L`. That it
preserves the bracket comes from the Leibniz rule for the exponential of an operator
(`ContinuousLinearMap.exp_apply_apply_of_leibniz`), since `ad X` is a derivation of the bracket by
the Jacobi identity. That it preserves `B` comes from `LinearMap.IsSkewAdjoint.apply_exp_apply_exp`,
since `ad X` is skew for `B` by invariance.

For an element `X` of the rank-one subalgebra of a root of a compact Lie algebra, the angle `s = π`
gives the inner automorphisms realizing the root reflections, in
`TauCeti.Algebra.Lie.InvariantForm.Reflection`.

## Main results

* `LinearMap.BilinForm.exists_lieEquiv_apply_eq_cos_smul_add_sin_smul`: `exp (s ad X)`, identified
  through matrices in any basis, is a Lie algebra automorphism preserving `B`, fixing the
  centralizer of `X` and rotating the `ad X`-rotation pairs by the angle `s`.
-/

public section

open Module NormedSpace

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

/-- **The inner automorphism `exp (s ad X)`.** For an element `X` of a finite-dimensional real Lie
algebra `L`, an invariant bilinear form `B` and `s ∈ ℝ`, there is a Lie algebra automorphism `θ`
of `L` whose matrix in every basis `b`, indexed by a finite type in `Type`, is the matrix
exponential of `s` times the matrix of `ad X`. It preserves `B`, fixes every element commuting with
`X`, and sends `p` to `cos s • p + sin s • q` whenever `⁅X, p⁆ = q` and `⁅X, q⁆ = -p`. -/
theorem exists_lieEquiv_apply_eq_cos_smul_add_sin_smul (B : LinearMap.BilinForm ℝ L)
    (hB : B.lieInvariant L) (X : L) (s : ℝ) :
    ∃ θ : L ≃ₗ⁅ℝ⁆ L,
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ L),
        LinearMap.toMatrix b b θ.toLinearEquiv =
          exp (s • LinearMap.toMatrix b b (LieAlgebra.ad ℝ L X))) ∧
      (∀ v w, B (θ v) (θ w) = B v w) ∧ (∀ v, ⁅X, v⁆ = 0 → θ v = v) ∧
      ∀ p q : L, ⁅X, p⁆ = q → ⁅X, q⁆ = -p → θ p = Real.cos s • p + Real.sin s • q := by
  -- The exponential is computed for an auxiliary norm on `L`, transported from coordinates.
  let e := (Module.finBasis ℝ L).equivFun
  let _ : NormedAddCommGroup L := NormedAddCommGroup.induced L _ e e.injective
  let _ : NormedSpace ℝ L := NormedSpace.induced ℝ L _ e
  have : CompleteSpace L := FiniteDimensional.completeSpace ℝ L
  let D : L →L[ℝ] L := s • LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L X)
  have hD (v : L) : D v = s • ⁅X, v⁆ := by simp [D]
  -- The bracket, as a continuous bilinear map.
  let br : L →L[ℝ] L →L[ℝ] L := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : Module.End ℝ L ≃ₗ[ℝ] (L →L[ℝ] L)).toLinearMap ∘ₗ
      (LieAlgebra.ad ℝ L : L →ₗ[ℝ] Module.End ℝ L))
  have hbr (v w : L) : br v w = ⁅v, w⁆ := by simp [br]
  let θ₀ := ContinuousLinearMap.expEquiv D
  have hθ₀ (v : L) : θ₀ v = exp D v := D.expEquiv_apply v
  -- `ad X` is a derivation of the bracket, by the Jacobi identity, so `exp D` preserves it.
  have hlie (v w : L) : θ₀ ⁅v, w⁆ = ⁅θ₀ v, θ₀ w⁆ := by
    have h := ContinuousLinearMap.exp_apply_apply_of_leibniz br (D₁ := D) (D₂ := D) (D₃ := D)
      (fun a b ↦ by simp only [hbr, hD, smul_lie, lie_smul]; rw [leibniz_lie, smul_add]) v w
    rwa [hbr, hbr, ← hθ₀, ← hθ₀, ← hθ₀] at h
  let θ : L ≃ₗ⁅ℝ⁆ L := { θ₀.toLinearEquiv with map_lie' := fun {v w} ↦ hlie v w }
  -- By construction, the underlying map of `θ` is that of `θ₀`.
  have hθ (v : L) : θ v = exp D v := hθ₀ v
  refine ⟨θ, fun {ι} _ _ b ↦ ?_, fun v w ↦ ?_, fun v hv ↦ ?_, fun p q hp hq ↦ ?_⟩
  · -- Taking matrices commutes with the exponential.
    have h : (θ.toLinearEquiv : L →ₗ[ℝ] L) = ((exp D : L →L[ℝ] L) : L →ₗ[ℝ] L) :=
      LinearMap.ext hθ
    rw [h, ContinuousLinearMap.toMatrix_exp b D]
    simp [D]
  · -- `ad X` is skew for the invariant form, so `exp D` preserves it.
    rw [hθ, hθ]
    exact LinearMap.IsSkewAdjoint.apply_exp_apply_exp (fun a b ↦ by simp [hD, hB X a b]) v w
  · rw [hθ]
    exact ContinuousLinearMap.exp_apply_of_apply_eq_zero (by simp [hD, hv])
  · -- `D` rotates the pair `p, q` at the speed `s`.
    rw [hθ]
    exact D.exp_apply_eq_cos_smul_add_sin_smul (by rw [hD, hp]) (by rw [hD, hq, smul_neg])

end LinearMap.BilinForm
