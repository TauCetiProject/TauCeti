/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Bounded composition in the strong operator topology

Composition preserves pointwise convergence when the outer operators are uniformly bounded
in operator norm. Only that family needs a bound, and neither space needs completeness.
For sequences on a Banach space the bound follows automatically from Banach–Steinhaus.

On a complete real or complex Hilbert space, orthogonal projections form a strongly closed
set. Their uniform norm bound lets idempotence pass to the strong limit; self-adjointness
passes through inner products. The closedness statement uses Mathlib's
`PointwiseConvergenceCLM` copy, leaving the norm topology on continuous linear maps unchanged.

## References

* Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, §2.4.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A strongly convergent sequence of operators on a Banach space is uniformly norm bounded. -/
theorem exists_norm_le_of_tendsto_pointwise [CompleteSpace E]
    {T : ℕ → E →L[𝕜] F} {T₀ : E →L[𝕜] F}
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) :
    ∃ C : ℝ, ∀ n, ‖T n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hT x)).exists_norm_le
  exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩

/-- Strong convergence is preserved by composition when the outer operators are eventually
uniformly norm bounded. The inner operators need no norm bound. -/
theorem tendsto_comp_apply_of_eventually_norm_le {l : Filter ι}
    {S : ι → F →L[𝕜] G} {T : ι → E →L[𝕜] F}
    {S₀ : F →L[𝕜] G} {T₀ : E →L[𝕜] F} {C : ℝ}
    (hS : ∀ y, Tendsto (fun i => S i y) l (𝓝 (S₀ y)))
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (T₀ x)))
    (hC : ∀ᶠ i in l, ‖S i‖ ≤ C) (x : E) :
    Tendsto (fun i => (S i).comp (T i) x) l (𝓝 (S₀.comp T₀ x)) :=
  tendsto_apply_of_eventually_norm_le (T := S) (g := fun i => T i x)
    hC (hS (T₀ x)) (hT x)

/-- Composition of strongly continuous operator families is strongly continuous on any set
where the outer family has a common operator-norm bound. Taking the parameter space to be a
product of strong operator spaces gives joint continuity on norm-bounded sets. -/
theorem continuousOn_pointwise_comp_of_norm_le {X : Type*} [TopologicalSpace X]
    {S : X → F →L[𝕜] G} {T : X → E →L[𝕜] F} {s : Set X} {C : ℝ}
    (hS : ContinuousOn (fun x => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) F G (S x)) s)
    (hT : ContinuousOn (fun x => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F (T x)) s)
    (hC : ∀ x ∈ s, ‖S x‖ ≤ C) :
    ContinuousOn (fun x =>
      toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E G ((S x).comp (T x))) s := by
  intro x hx
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  exact tendsto_comp_apply_of_eventually_norm_le
    (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (hS x hx))
    (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (hT x hx))
    (eventually_mem_nhdsWithin.mono fun y hy => hC y hy)

/-- On a Banach intermediate space, composition preserves strong convergence of sequences
without an explicit uniform bound. This does not assert joint continuity on the whole space. -/
theorem tendsto_comp_apply_of_tendsto_pointwise [CompleteSpace F]
    {S : ℕ → F →L[𝕜] G} {T : ℕ → E →L[𝕜] F}
    {S₀ : F →L[𝕜] G} {T₀ : E →L[𝕜] F}
    (hS : ∀ y, Tendsto (fun n => S n y) atTop (𝓝 (S₀ y)))
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) (x : E) :
    Tendsto (fun n => (S n).comp (T n) x) atTop (𝓝 (S₀.comp T₀ x)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_pointwise hS
  exact tendsto_comp_apply_of_eventually_norm_le hS hT (Eventually.of_forall hC) x

end ContinuousLinearMap

namespace IsStarProjection

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A strong limit of orthogonal projections is an orthogonal projection, for arbitrary nets
and with no separability or dimension restriction. -/
theorem of_tendsto_pointwise {l : Filter ι} [l.NeBot]
    {P : ι → H →L[𝕜] H} {P₀ : H →L[𝕜] H}
    (hP : ∀ᶠ i in l, IsStarProjection (P i))
    (hlim : ∀ x, Tendsto (fun i => P i x) l (𝓝 (P₀ x))) : IsStarProjection P₀ := by
  have hsq := ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
    (hP.mono fun i hi => hi.norm_le _)
  have hidem : IsIdempotentElem P₀ := by
    apply ContinuousLinearMap.ext
    intro x
    exact tendsto_nhds_unique (hsq x)
      ((hlim x).congr' (hP.mono fun i hi => congrArg (fun T : H →L[𝕜] H => T x)
        hi.isIdempotentElem.eq.symm))
  refine ⟨hidem, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_⟩
  exact tendsto_nhds_unique
    (((hlim x).inner tendsto_const_nhds).congr' (hP.mono fun i hi =>
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hi.isSelfAdjoint x y)))
    (tendsto_const_nhds.inner (hlim y))

end IsStarProjection

namespace PointwiseConvergenceCLM

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Orthogonal projections are closed in the strong operator topology. -/
theorem isClosed_setOf_isStarProjection :
    IsClosed {P : H →Lₚₜ[𝕜] H |
      IsStarProjection ((UniformConvergenceCLM.ofFun (RingHom.id 𝕜) H _).symm P)} := by
  refine isClosed_iff_forall_filter.mpr fun P l hl hmem hlim => ?_
  have := hl
  exact IsStarProjection.of_tendsto_pointwise (le_principal_iff.mp hmem)
    (tendsto_iff_forall_tendsto.mp hlim)

end PointwiseConvergenceCLM
