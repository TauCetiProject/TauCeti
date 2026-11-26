/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# The inner automorphisms `exp (s ad X)` of a real Lie algebra

Let `L` be a finite-dimensional real Lie algebra with an invariant bilinear form `B`, and `X ∈ L`.
For every `s ∈ ℝ` the operator exponential `θ = exp (s ad X)`, computed for any norm on `L`, is a
Lie algebra automorphism of `L` preserving `B`
(`LinearMap.BilinForm.exists_lieEquiv_apply_eq_cos_smul_add_sin_smul`). It fixes every element
commuting with `X`, and it rotates every pair `p, q` with `⁅X, p⁆ = q` and `⁅X, q⁆ = -p` by the
angle `s`: `θ p = cos s • p + sin s • q`. The norm is an auxiliary choice inside the proof and does
not appear in the statement.

The automorphism property and the invariance of `B` both come from the Leibniz rule for the
exponential of an operator (`ContinuousLinearMap.exp_apply_apply_of_leibniz`): `ad X` is a
derivation of the bracket by the Jacobi identity, and it is skew for `B` by invariance.

For an element `X` of the rank-one subalgebra of a root of a compact Lie algebra, the angle `s = π`
gives the inner automorphisms realizing the root reflections, in
`TauCeti.Algebra.Lie.InvariantForm.Reflection`.

## Main results

* `LinearMap.BilinForm.exists_lieEquiv_apply_eq_cos_smul_add_sin_smul`: `exp (s ad X)` is a Lie
  algebra automorphism preserving `B`, fixing the centralizer of `X` and rotating the
  `ad X`-rotation pairs by the angle `s`.
-/

public section

open NormedSpace

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

/-- **The inner automorphism `exp (s ad X)`.** For an element `X` of a finite-dimensional real Lie
algebra `L`, an invariant bilinear form `B` and `s ∈ ℝ`, there is a Lie algebra automorphism `θ`
of `L`, namely `exp (s ad X)` for any norm on `L`, which preserves `B`, fixes every element
commuting with `X`, and sends `p` to `cos s • p + sin s • q` whenever `⁅X, p⁆ = q` and
`⁅X, q⁆ = -p`. -/
theorem exists_lieEquiv_apply_eq_cos_smul_add_sin_smul (B : LinearMap.BilinForm ℝ L)
    (hB : B.lieInvariant L) (X : L) (s : ℝ) :
    ∃ θ : L ≃ₗ⁅ℝ⁆ L, (∀ v w, B (θ v) (θ w) = B v w) ∧ (∀ v, ⁅X, v⁆ = 0 → θ v = v) ∧
      ∀ p q : L, ⁅X, p⁆ = q → ⁅X, q⁆ = -p → θ p = Real.cos s • p + Real.sin s • q := by
  -- The exponential is computed for an auxiliary norm on `L`, transported from coordinates.
  let e := (Module.finBasis ℝ L).equivFun
  let _ : NormedAddCommGroup L := NormedAddCommGroup.induced L _ e e.injective
  let _ : NormedSpace ℝ L := NormedSpace.induced ℝ L _ e
  have : CompleteSpace L := FiniteDimensional.completeSpace ℝ L
  let D : L →L[ℝ] L := s • LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L X)
  have hD (v : L) : D v = s • ⁅X, v⁆ := by simp [D]
  -- The bracket and the form, as continuous bilinear maps.
  let br : L →L[ℝ] L →L[ℝ] L := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : Module.End ℝ L ≃ₗ[ℝ] (L →L[ℝ] L)).toLinearMap ∘ₗ
      (LieAlgebra.ad ℝ L : L →ₗ[ℝ] Module.End ℝ L))
  have hbr (v w : L) : br v w = ⁅v, w⁆ := by simp [br]
  let bB : L →L[ℝ] L →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (L →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (L →L[ℝ] ℝ)).toLinearMap ∘ₗ B)
  have hbB (v w : L) : bB v w = B v w := by simp [bB]
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
  refine ⟨θ, fun v w ↦ ?_, fun v hv ↦ ?_, fun p q hp hq ↦ ?_⟩
  · -- `ad X` is skew for the invariant form, so `exp D` preserves it.
    have h := ContinuousLinearMap.exp_apply_apply_of_leibniz bB (D₁ := D) (D₂ := D) (D₃ := 0)
      (fun a b ↦ by simp [hD, hbB, hB X a b]) v w
    rw [hbB, hbB, NormedSpace.exp_zero, one_apply_eq_self] at h
    rw [hθ, hθ, h]
  · rw [hθ]
    exact ContinuousLinearMap.exp_apply_of_apply_eq_zero (by simp [hD, hv])
  · -- `D` rotates the pair `p, q` at the speed `s`.
    rw [hθ]
    exact D.exp_apply_eq_cos_smul_add_sin_smul (by rw [hD, hp]) (by rw [hD, hq, smul_neg])

end LinearMap.BilinForm
