/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuity and bounds for pushforward of abstract measures

Pushforward is continuous for the weak topology of test-function evaluations. On compact
spaces it also contracts the continuous-dual operator norm, and hence is continuous for the
strong topology. These facts allow restrictions and inclusions of measure spaces to be
compared in either topology. The weak statement allows module-valued measures and does not
require compactness; the norm and strong statements also allow module-valued measures.

We use Mathlib's `AbstractMeasure.map` and `AbstractMeasure.toCLMEquiv`, and select its
`WeakTopology` and `StrongTopology` explicitly without installing global instances.

## References

Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, Definition 3.5,
Definitions 3.7–3.8 and Remark 3.31.
-/

public section

open AbstractMeasure

variable {X Y R E : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace ContinuousMap

/-- Pushforward is continuous for the weak topologies of test-function evaluations. -/
theorem continuous_abstractMeasure_map_weak [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [NormedAddCommGroup E] [Module R E] [ContinuousSMul R E] (f : C(X, Y)) :
    @Continuous _ _ (WeakTopology (X := X) (R := R) (E := E))
      (WeakTopology (X := Y) (R := R) (E := E)) (map (R := R) (E := E) f) := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  let : TopologicalSpace (AbstractMeasure Y R E) := WeakTopology
  have heval : Continuous (fun μ : AbstractMeasure X R E ↦ fun h : C(X, R) ↦ μ h) :=
    continuous_induced_dom
  refine continuous_induced_rng.mpr <| continuous_pi fun g ↦ ?_
  exact ((continuous_apply (g.comp f)).comp heval).congr fun μ ↦ by
    simp only [Function.comp_apply, map_apply]

end ContinuousMap

variable [CompactSpace X] [CompactSpace Y] [NontriviallyNormedField R]
  [NormedAddCommGroup E] [NormedSpace R E]

namespace AbstractMeasure

/-- Pushforward between compact spaces does not increase the continuous-dual operator norm. -/
theorem norm_toCLMEquiv_map_le (μ : AbstractMeasure X R E) (f : C(X, Y)) :
    ‖toCLMEquiv (map f μ)‖ ≤ ‖toCLMEquiv μ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g ↦ ?_
  simp only [coe_toCLMEquiv, map_apply]
  simpa only [coe_toCLMEquiv] using (toCLMEquiv μ).le_opNorm (g.comp f) |>.trans <|
    mul_le_mul_of_nonneg_left
      ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x ↦
        ContinuousMap.norm_coe_le_norm g (f x)) (norm_nonneg _)

end AbstractMeasure

namespace ContinuousMap

omit [CompactSpace X] [CompactSpace Y] in
/-- Pushforward is continuous for Mathlib's strong measure topologies, which on compact
spaces are the continuous-dual operator-norm topologies. -/
theorem continuous_abstractMeasure_map_strong (f : C(X, Y)) :
    @Continuous _ _ (StrongTopology (X := X) (R := R) (E := E))
      (StrongTopology (X := Y) (R := R) (E := E)) (map (R := R) (E := E) f) := by
  let : TopologicalSpace (AbstractMeasure X R E) := StrongTopology
  let : TopologicalSpace (AbstractMeasure Y R E) := StrongTopology
  have h : Continuous (fun μ : C(X, R) →L[R] E ↦ μ.comp (f.compCLM R R)) :=
    (ContinuousLinearMap.precomp (τ := RingHom.id R) (ρ := RingHom.id R)
      E (f.compCLM R R)).continuous
  exact h.congr fun μ ↦ by
    ext g
    exact (map_apply (R := R) (E := E) f μ g).symm

end ContinuousMap
