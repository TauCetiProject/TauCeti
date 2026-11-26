/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.RingTheory.Derivation.DifferentialOperator

/-!
# Real and imaginary parts of complex differential operators on functions

Let `M` be a real manifold and let `Q` be a complex-linear operator on the complex-valued `C^n`
functions `C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯` which is a differential operator of order at most `m` in
Grothendieck's sense, for commutators with multiplication by complex-valued functions. Then
`u ↦ Re (Q u)` and `u ↦ Im (Q u)` are real differential operators of order at most `m` on the
real-valued `C^n` functions, for commutators with real-valued functions
(`TauCeti.re_comp_restrictScalars_comp_ofReal_mem_differentialOperators`,
`TauCeti.im_comp_restrictScalars_comp_ofReal_mem_differentialOperators`). Since `Q` is
determined by its values on real functions, this writes `Q = A + i B` with `A` and `B` real
differential operators.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {Q : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℕ}
  (hQ : Q ∈ differentialOperators ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
    C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
include hQ

/-- Reading a complex differential operator `Q` on real-valued functions and taking a real-linear
part `σ` that is linear over the real-valued functions gives a real differential operator of the
same order: the inclusion of real functions and `σ` intertwine multiplication by a real function
`b` with multiplication by `b` as a complex function. -/
private theorem comp_restrictScalars_comp_ofReal_mem_differentialOperators
    {σ : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℝ] C^n⟮I, M; ℝ⟯}
    (hσ : ∀ (b : C^n⟮I, M; ℝ⟯) y, σ (ContMDiffMap.ofReal b * y) = b * σ y) :
    σ ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ m :=
  comp_comp_mem_differentialOperators
    (fun b ↦ ⟨ContMDiffMap.ofReal b, fun x ↦ map_mul ContMDiffMap.ofReal b x, hσ b⟩)
    (restrictScalars_mem_differentialOperators hQ)

/-- **The real part of a complex differential operator.** If `Q` is a differential operator of
order at most `m` on the complex-valued smooth functions on `M`, for commutators with
complex-valued smooth functions, then `u ↦ Re (Q u)` is a differential operator of order at most
`m` on the real-valued smooth functions. -/
theorem re_comp_restrictScalars_comp_ofReal_mem_differentialOperators :
    ContMDiffMap.re ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ m :=
  comp_restrictScalars_comp_ofReal_mem_differentialOperators hQ ContMDiffMap.re_ofReal_mul

/-- **The imaginary part of a complex differential operator.** If `Q` is a differential operator
of order at most `m` on the complex-valued smooth functions on `M`, for commutators with
complex-valued smooth functions, then `u ↦ Im (Q u)` is a differential operator of order at most
`m` on the real-valued smooth functions. -/
theorem im_comp_restrictScalars_comp_ofReal_mem_differentialOperators :
    ContMDiffMap.im ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ m :=
  comp_restrictScalars_comp_ofReal_mem_differentialOperators hQ ContMDiffMap.im_ofReal_mul

end TauCeti
