/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Reflection
public import TauCeti.Analysis.Normed.Operator.Compact.StrongConvergence
import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Compact operators and finite reflections

For finite reflections `Wₙ` in a countable Hilbert basis, compact operators `K` and `L`
satisfy `K Wₙ L → 0` in operator norm. A single compact factor gives strong convergence
`K Wₙ x → 0`, and hence `Wₙ K Wₙ x → 0`. Since `Wₙ Pₙ = Pₙ Wₙ = Wₙ`, the latter
also gives strong convergence of the reflected finite compressions `Wₙ Pₙ K Pₙ Wₙ`.
These limits separate the two compact boundary remainders in finite-section algebras.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for compact remainders in the finite-section method.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace HilbertBasis

variable {𝕜 H E G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A compact operator takes every reflected vector to a norm-null sequence. -/
theorem tendsto_compact_comp_finiteReflection_apply (b : HilbertBasis ℕ 𝕜 H)
    (K : H →L[𝕜] G) (hK : IsCompactOperator K) (x : H) :
    Tendsto (fun n ↦ K (b.finiteReflection n x)) atTop (𝓝 0) := by
  have hw : Tendsto (fun n ↦ toWeakSpace 𝕜 H (b.finiteReflection n x)) atTop
      (𝓝 (toWeakSpace 𝕜 H 0)) := by
    apply TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.mpr
    intro f
    obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual 𝕜 H).surjective f
    simpa using b.tendsto_inner_finiteReflection x y
  simpa using (ContinuousLinearMap.isDunfordPettis_def.mp hK.isDunfordPettis) hw

/-- Compact factors on both sides turn weak decay of finite reflections into
operator-norm decay. The source and target need not be Hilbert spaces or complete. -/
theorem tendsto_compact_comp_finiteReflection_comp_compact (b : HilbertBasis ℕ 𝕜 H)
    (K : H →L[𝕜] G) (L : E →L[𝕜] H)
    (hK : IsCompactOperator K) (hL : IsCompactOperator L) :
    Tendsto (fun n ↦ K ∘L b.finiteReflection n ∘L L) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ‖K ∘L b.finiteReflection n‖ ≤ ‖K‖ :=
    (K.opNorm_comp_le _).trans_eq (by simp)
  simpa only [ContinuousLinearMap.comp_assoc] using
    ContinuousLinearMap.tendsto_comp_zero_of_isCompactOperator (norm_nonneg K) hbound
      (fun x ↦ b.tendsto_compact_comp_finiteReflection_apply K hK x) L hL

/-- Reflected compact compressions converge strongly to zero. The equalities
`Wₙ Pₙ = Pₙ Wₙ = Wₙ` identify this with the reflected finite-section remainder. -/
theorem tendsto_finiteReflection_comp_compact_comp_finiteReflection_apply
    (b : HilbertBasis ℕ 𝕜 H) (K : H →L[𝕜] H) (hK : IsCompactOperator K) (x : H) :
    Tendsto (fun n ↦ b.finiteReflection n (K (b.finiteReflection n x))) atTop (𝓝 0) := by
  exact ContinuousLinearMap.tendsto_apply_of_eventually_norm_le (w := 0)
    (Eventually.of_forall (b.norm_finiteReflection_le))
    (by simp)
    (b.tendsto_compact_comp_finiteReflection_apply K hK x)

end HilbertBasis
