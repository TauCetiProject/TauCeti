/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Weak-star cluster points in duals and biduals

Evaluation of a weak-star cluster point of a family in a weak dual agrees with any limit
of the corresponding evaluations. Banach–Alaoglu gives a weak-star cluster point, with the
same norm bound, for any family of continuous functionals that is frequently bounded along
a filter. Specializing to the canonical inclusion into the bidual, these facts let one
transfer approximate identity laws to identities for the Arens products.
-/

public section

open Filter NormedSpace
open scoped Topology

section WeakDual

variable {𝕜 X ι : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [T2Space 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid X] [Module 𝕜 X] [TopologicalSpace X]
  {l : Filter ι}

/-- Evaluation of a weak-star cluster point agrees with any limit of the evaluations. -/
theorem MapClusterPt.apply_eq_of_tendsto {φ : WeakDual 𝕜 X} {u : ι → WeakDual 𝕜 X}
    (hφ : MapClusterPt φ l u) (x : X) {c : 𝕜} (hx : Tendsto (fun i ↦ u i x) l (𝓝 c)) :
    φ x = c :=
  eq_of_nhds_neBot
    ((hφ.continuousAt_comp (WeakDual.eval_continuous x).continuousAt).clusterPt.mono hx).neBot

end WeakDual

section Normed

variable {𝕜 X ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] {l : Filter ι}

/-- Evaluation of a weak-star bidual cluster point agrees with a functional's limit. -/
theorem MapClusterPt.apply_eq_of_inclusionInDoubleDual_of_tendsto
    {E : StrongDual 𝕜 (StrongDual 𝕜 X)} {u : ι → X}
    (hE : MapClusterPt (StrongDual.toWeakDual E) l
      (fun i ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X (u i))))
    (g : StrongDual 𝕜 X) {c : 𝕜} (hg : Tendsto (fun i ↦ g (u i)) l (𝓝 c)) : E g = c := by
  simpa only [StrongDual.toWeakDual_apply] using hE.apply_eq_of_tendsto g
    (by simpa only [StrongDual.toWeakDual_apply, dual_def] using hg)

/-- A family of continuous functionals that is frequently bounded along a filter has a
weak-star cluster point with the same norm bound. -/
theorem Filter.Frequently.exists_mapClusterPt_toWeakDual [ProperSpace 𝕜]
    {u : ι → StrongDual 𝕜 X} {C : ℝ} (hC : ∃ᶠ i in l, ‖u i‖ ≤ C) :
    ∃ φ : StrongDual 𝕜 X, ‖φ‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual φ) l (fun i ↦ StrongDual.toWeakDual (u i)) := by
  obtain ⟨φ, hφC, hφ⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 X) C).exists_mapClusterPt_of_frequently
      (f := fun i ↦ StrongDual.toWeakDual (u i)) <| hC.mono fun i hi ↦ by
        simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
          mem_closedBall_zero_iff] using hi
  refine ⟨φ.toStrongDual, mem_closedBall_zero_iff.mp hφC, ?_⟩
  simpa only [WeakDual.toWeakDual_toStrongDual] using hφ

/-- A family that is frequently bounded along a filter has a weak-star bidual cluster point
with the same norm bound. No completeness of the space is required. -/
theorem Filter.Frequently.exists_mapClusterPt_inclusionInDoubleDual [ProperSpace 𝕜]
    {u : ι → X} {C : ℝ} (hC : ∃ᶠ i in l, ‖u i‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 X), ‖E‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual E) l
        (fun i ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X (u i))) :=
  (hC.mono fun i hi ↦ (double_dual_bound 𝕜 X (u i)).trans hi).exists_mapClusterPt_toWeakDual

end Normed
