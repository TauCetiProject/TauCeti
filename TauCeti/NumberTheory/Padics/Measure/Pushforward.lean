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

Pushforward is continuous for the weak topology of test-function evaluations and for the
strong topology on arbitrary source and target spaces. Strong continuity comes from
precomposition by `f.compCLM`. On compact spaces the strong topology is the continuous-dual
operator-norm topology, and pushforward contracts this norm. These facts allow restrictions
and inclusions of measure spaces to be compared in either topology. All statements allow
module-valued measures.

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

namespace AbstractMeasure

/-- Under the continuous-linear-map equivalence, pushforward is precomposition. -/
@[simp]
theorem toCLMEquiv_map [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module R E] [ContinuousSMul R E] (μ : AbstractMeasure X R E) (f : C(X, Y)) :
    toCLMEquiv (map f μ) = (toCLMEquiv μ).comp (f.compCLM R R) := by
  ext g
  simp

end AbstractMeasure

variable [CompactSpace X] [CompactSpace Y] [NontriviallyNormedField R]

namespace AbstractMeasure

/-- Pushforward between compact spaces does not increase the continuous-dual operator norm. -/
theorem norm_toCLMEquiv_map_le [SeminormedAddCommGroup E] [NormedSpace R E]
    (μ : AbstractMeasure X R E) (f : C(X, Y)) :
    ‖toCLMEquiv (map f μ)‖ ≤ ‖toCLMEquiv μ‖ := by
  have hcomp : ‖f.compCLM R R‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g ↦ ?_
    simpa only [one_mul, ContinuousMap.compCLM_apply] using
      (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x ↦
        ContinuousMap.norm_coe_le_norm g (f x)
  rw [toCLMEquiv_map]
  exact ((toCLMEquiv μ).opNorm_comp_le _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hcomp)

end AbstractMeasure

namespace ContinuousMap

omit [CompactSpace X] [CompactSpace Y] in
/-- Pushforward is continuous for Mathlib's strong measure topologies, which on compact
spaces are the continuous-dual operator-norm topologies. -/
theorem continuous_abstractMeasure_map_strong [NormedAddCommGroup E] [NormedSpace R E]
    (f : C(X, Y)) :
    @Continuous _ _ (StrongTopology (X := X) (R := R) (E := E))
      (StrongTopology (X := Y) (R := R) (E := E)) (map (R := R) (E := E) f) := by
  let : TopologicalSpace (AbstractMeasure X R E) := StrongTopology
  let : TopologicalSpace (AbstractMeasure Y R E) := StrongTopology
  -- StrongTopology is by definition the continuous-linear-map topology on the type synonym,
  -- so h also gives continuity between these measure spaces after identifying the functions.
  have h : Continuous (fun μ : C(X, R) →L[R] E ↦ μ.comp (f.compCLM R R)) :=
    (ContinuousLinearMap.precomp (τ := RingHom.id R) (ρ := RingHom.id R)
      E (f.compCLM R R)).continuous
  exact h.congr fun μ ↦ by
    ext g
    calc
      μ ((f.compCLM R R) g) = (toCLMEquiv μ) ((f.compCLM R R) g) :=
        (coe_toCLMEquiv μ _).symm
      _ = toCLMEquiv (map f μ) g :=
        DFunLike.congr_fun (toCLMEquiv_map μ f).symm g
      _ = map f μ g := coe_toCLMEquiv _ _

end ContinuousMap
