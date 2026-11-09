/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.Analytic.Submanifold.ZeroDimensional
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Compactness.Lindelof

/-!
# Proper embeddings of zero-dimensional manifolds

A second-countable manifold with zero-dimensional model is a countable discrete space.
Enumerating its points by distinct natural numbers gives a closed, proper embedding into
`ℝ`, and hence into `ℂ`. All maps out of such a manifold are smooth, and their differentials
are injective. Consequently the enumeration is a regular analytic embedding in the real
case and a regular holomorphic embedding in the complex case.

We also give a real-analytic embedding into `Fin 2 → ℝ`, with closed discrete image. When
the source is nonempty this image is a native zero-dimensional analytic submanifold;
the empty source instead has empty image. No compactness of the source is required.

## References

* H. Grauert, *On Levi's Problem and the Imbedding of Real-Analytic Manifolds*,
  Annals of Mathematics **68** (1958), 460–472 (the dimension-zero embedding case).
-/

public section

open Set Topology Manifold
open scoped ContDiff

section Immersion

variable {𝕜 E F M : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] {f : M → F}

/-- A topological embedding from a zero-dimensional manifold into a finite-dimensional
normed space is a smooth embedding, for every positive differentiability order. -/
theorem Topology.IsEmbedding.isSmoothEmbedding_of_subsingleton (hf : IsEmbedding f)
    (hn : 1 ≤ n) : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, F) n f := by
  let : DiscreteTopology M := ChartedSpace.discreteTopology E M
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.mpr (fun x ↦ ?_), hf⟩
  -- TangentSpace is a type synonym for the model; its subsingleton instance is not inferred.
  let : Subsingleton (TangentSpace 𝓘(𝕜, E) x) := inferInstanceAs (Subsingleton E)
  exact (contMDiff_of_discreteTopology (f := f)).contMDiffOn
    |>.isImmersionAt_iff_injective_mfderiv isOpen_univ (mem_univ x) hn
    |>.mpr (Function.injective_of_subsingleton _)

end Immersion

namespace TauCeti

variable {𝕜 E M : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E]
  [TopologicalSpace M] [ChartedSpace E M] [SecondCountableTopology M]
  {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M]

/-- A second-countable zero-dimensional real or complex manifold admits a proper smooth
embedding into its scalar field, at every positive differentiability order. In particular,
`𝕜 = ℂ` and `n = ∞` give a proper holomorphic embedding, while `𝕜 = ℝ` and `n = ω`
give a proper real-analytic embedding. The empty manifold is included. -/
theorem exists_isProperMap_isSmoothEmbedding_of_subsingleton (hn : 1 ≤ n) :
    ∃ f : M → 𝕜, IsProperMap f ∧ IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜) n f ∧
      IsClosed (range f) := by
  let : DiscreteTopology M := ChartedSpace.discreteTopology E M
  let : Countable M := countable_of_Lindelof_of_discrete
  obtain ⟨e, he⟩ := exists_injective_nat M
  have hec : IsClosedEmbedding e :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap
      continuous_of_discreteTopology he (fun _ _ ↦ isClosed_discrete _)
  have hc := (RCLike.isUniformEmbedding_ofReal (𝕜 := 𝕜)).isClosedEmbedding
  have hf := hc.comp (Nat.isClosedEmbedding_coe_real.comp hec)
  exact ⟨_, hf.isProperMap, hf.isEmbedding.isSmoothEmbedding_of_subsingleton hn,
    hf.isClosed_range⟩

/-- A second-countable zero-dimensional real-analytic manifold has a proper regular
real-analytic embedding into `ℝ²` with closed image. Its image is empty if the source is
empty, and is a zero-dimensional analytic submanifold otherwise. -/
theorem exists_isProperMap_isSmoothEmbedding_real_two_of_subsingleton
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace M] [ChartedSpace E M] [SecondCountableTopology M]
    [IsManifold 𝓘(ℝ, E) ω M] :
    ∃ f : M → (Fin 2 → ℝ), IsProperMap f ∧
      IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, Fin 2 → ℝ) ω f ∧ IsClosed (range f) ∧
        (Nonempty M → IsAnalyticSubmanifold 0 (range f)) := by
  let : DiscreteTopology M := ChartedSpace.discreteTopology E M
  obtain ⟨g, -, hgs, hgc⟩ :=
    exists_isProperMap_isSmoothEmbedding_of_subsingleton (𝕜 := ℝ) (E := E) (M := M)
      (n := ω) (by simp)
  have hi : Isometry (fun t : ℝ ↦ fun _ : Fin 2 ↦ t) :=
    Isometry.of_dist_eq fun _ _ ↦ dist_pi_const _ _
  have hf := hi.isClosedEmbedding.comp ⟨hgs.isEmbedding, hgc⟩
  refine ⟨_, hf.isProperMap, hf.isEmbedding.isSmoothEmbedding_of_subsingleton (by simp),
    hf.isClosed_range, fun hM ↦ ?_⟩
  exact hf.isEmbedding.isInducing.isDiscrete_range.isAnalyticSubmanifold_zero
    (range_nonempty_iff_nonempty.mpr hM)

end TauCeti
