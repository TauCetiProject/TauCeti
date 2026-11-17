/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# Noncompact idempotent operators on Hilbert spaces

On a separable Hilbert space `H` over `𝕜` (`ℝ` or `ℂ`), every noncompact continuous idempotent
operator `p : H →L[𝕜] H` (`p * p = p`) dominates the identity via a linear isometry
`v : H →ₗᵢ[𝕜] H` taking values in `p.range`, so that `p * v = v` and `star v * p * v = 1`.

In particular, any two-sided ideal of `H →L[𝕜] H` containing a noncompact idempotent operator
contains `1` and therefore equals `⊤`.

## Main results

* `IsIdempotentElem.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one`: on a separable Hilbert
  space, every noncompact idempotent operator `p` admits a linear isometry `v : H →ₗᵢ[𝕜] H`
  satisfying `p * v = v` and `star v * p * v = 1`.

## References

* J. W. Calkin, *Two-sided ideals and congruences in the ring of bounded operators in Hilbert
  space*, Annals of Mathematics 42 (1941), 839–873, §1.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Academic Press (1990), Theorem 2.4.9.
-/

public noncomputable section

open TopologicalSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- On a separable Hilbert space, every noncompact idempotent operator `p` admits a linear isometry
`v : H →ₗᵢ[𝕜] H` satisfying `p * v = v` and `star v * p * v = 1`. -/
theorem IsIdempotentElem.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one [SeparableSpace H]
    {p : H →L[𝕜] H} (hp : IsIdempotentElem p) (hnc : ¬ IsCompactOperator p) :
    ∃ v : H →ₗᵢ[𝕜] H,
      p * v.toContinuousLinearMap = v.toContinuousLinearMap ∧
        Star.star v.toContinuousLinearMap * p * v.toContinuousLinearMap = 1 := by
  have : CompleteSpace p.range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp).completeSpace_coe
  have hinf : ¬ FiniteDimensional 𝕜 p.range := fun _ ↦
    hnc (LinearMap.HasFiniteRange.isCompactOperator Submodule.FG.of_finite)
  obtain ⟨w₁, b₁, -⟩ := exists_hilbertBasis 𝕜 p.range
  have : Infinite w₁ := not_finite_iff_infinite.mp fun hfin ↦ by
    have := Fintype.ofFinite w₁
    exact hinf b₁.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  obtain ⟨w₂, b₂, -⟩ := exists_hilbertBasis 𝕜 H
  have : Countable w₂ := b₂.orthonormal.countable
  obtain ⟨f₂, hf₂⟩ := exists_injective_nat w₂
  -- Embed the countable Hilbert basis of `H` into the infinite Hilbert basis of `p.range`.
  let φ : w₂ → w₁ := Infinite.natEmbedding w₁ ∘ f₂
  have hφ : Function.Injective φ := (Infinite.natEmbedding w₁).injective.comp hf₂
  have hu : Orthonormal 𝕜 (b₁ ∘ φ) := b₁.orthonormal.comp φ hφ
  let v : H →ₗᵢ[𝕜] H :=
    p.range.subtypeₗᵢ.comp (hu.orthogonalFamily.linearIsometry.comp b₂.repr.toLinearIsometry)
  have hpv : p * v.toContinuousLinearMap = v.toContinuousLinearMap := by
    ext x
    simp [v, ContinuousLinearMap.IsIdempotentElem.apply_coe_range hp]
  refine ⟨v, hpv, ?_⟩
  rw [mul_assoc, hpv, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    v.adjoint_comp_self]

end
