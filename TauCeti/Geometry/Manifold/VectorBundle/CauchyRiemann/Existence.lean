/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence

/-!
# Existence of smooth real Cauchy–Riemann operators

Let `V` be a complex vector bundle of finite rank over a σ-compact Hausdorff manifold `M` with a
smooth almost complex structure `j`, modelled on a finite-dimensional space. If `V` is `C^k`, then
for `n + 1 ≤ k` it carries a `C^n` real Cauchy–Riemann operator: the `(0,1)`-part of a `C^n`
covariant derivative, which exists by a partition of unity
(`CovariantDerivative.exists_contMDiffCovariantDerivative`), is a real Cauchy–Riemann operator
(`IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart`) and is `C^n`
(`ContMDiffCovariantDerivativeOn.zeroOnePart`).

## Main results

* `TauCeti.exists_isRealCauchyRiemannOperator_contMDiffCovariantDerivativeOn`: existence of a
  `C^n` real Cauchy–Riemann operator on a `C^k` complex vector bundle, `n + 1 ≤ k`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℝ F V] [VectorBundle ℂ F V]

open SmoothAlmostComplexStructure

/-- **Existence of smooth real Cauchy–Riemann operators.** A `C^k` complex vector bundle of
finite rank over a σ-compact Hausdorff manifold with a smooth almost complex structure, modelled on
a finite-dimensional space, carries a `C^n` real Cauchy–Riemann operator whenever `n + 1 ≤ k`: the
`(0,1)`-part of a `C^n` covariant derivative
(`CovariantDerivative.exists_contMDiffCovariantDerivative`). -/
theorem exists_isRealCauchyRiemannOperator_contMDiffCovariantDerivativeOn [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ F] {n : ℕ∞} {k : ℕ∞ω}
    [ContMDiffVectorBundle k F V I] (hk : n + 1 ≤ k) :
    ∃ D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x,
      IsRealCauchyRiemannOperator F j D ∧ ContMDiffCovariantDerivativeOn F n D univ := by
  obtain ⟨cov, hcov⟩ := CovariantDerivative.exists_contMDiffCovariantDerivative (I := I) (F := F)
    (V := V) hk
  exact ⟨_, cov.isCovariantDerivativeOnUniv.isRealCauchyRiemannOperator_zeroOnePart j,
    hcov.contMDiff.zeroOnePart j (by exact_mod_cast le_top)⟩

end TauCeti
