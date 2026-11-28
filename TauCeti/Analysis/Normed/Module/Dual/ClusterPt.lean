/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Weak-star cluster points and limits in dual spaces

Banach–Alaoglu gives a weak-star cluster point in the dual space (and in particular a weak-star
limit along any ultrafilter) for any eventually norm-bounded family of continuous linear
functionals, retaining the norm bound. Applied to `NormedSpace.inclusionInDoubleDual`, this yields
weak-star cluster points in the bidual for any eventually bounded proper filter on a seminormed
space. Evaluation of such a cluster point agrees with any limit of the corresponding continuous
linear functional. These facts let one transfer approximate identity laws to identities for the
Arens products and to innerness reductions for derivations.
-/

public section

open Filter NormedSpace
open scoped Topology

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] {l : Filter X}

/-- Evaluation of a weak-star bidual cluster point agrees with a functional's limit. -/
theorem MapClusterPt.apply_eq_of_tendsto_inclusionInDoubleDual
    {E : StrongDual 𝕜 (StrongDual 𝕜 X)}
    (hE : MapClusterPt (StrongDual.toWeakDual E) l
      (fun x ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)))
    (g : StrongDual 𝕜 X) {c : 𝕜} (hg : Tendsto (fun x ↦ g x) l (𝓝 c)) : E g = c := by
  have hc := hE.continuousAt_comp (WeakDual.eval_continuous g).continuousAt
  simp only [Function.comp_def, StrongDual.toWeakDual_apply, dual_def] at hc
  exact eq_of_nhds_neBot (hc.clusterPt.mono hg).neBot

/-- An eventually norm-bounded proper filter of continuous linear functionals has a weak-star
cluster point with the same norm bound. No completeness of the space is required. -/
theorem Filter.Eventually.exists_mapClusterPt_toWeakDual [ProperSpace 𝕜]
    {α : Type*} {l : Filter α} [l.NeBot] {u : α → StrongDual 𝕜 X} {C : ℝ}
    (hC : ∀ᶠ a in l, ‖u a‖ ≤ C) :
    ∃ φ : StrongDual 𝕜 X, ‖φ‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual φ) l (fun a ↦ StrongDual.toWeakDual (u a)) := by
  obtain ⟨φ, hφC, hφ⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 X) C).exists_mapClusterPt
      (u := fun a ↦ StrongDual.toWeakDual (u a))
      (Filter.tendsto_principal.mpr <| hC.mono fun a ha ↦ by
        simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
          mem_closedBall_zero_iff] using ha)
  refine ⟨φ.toStrongDual, mem_closedBall_zero_iff.mp hφC, ?_⟩
  simpa only [WeakDual.toWeakDual_toStrongDual] using hφ

/-- An eventually norm-bounded family of continuous linear functionals converges in the weak-star
topology along any ultrafilter, with the same norm bound. No completeness of the space is
required. -/
theorem Ultrafilter.exists_tendsto_toWeakDual [ProperSpace 𝕜]
    {α : Type*} (U : Ultrafilter α) (u : α → StrongDual 𝕜 X) {C : ℝ}
    (hC : ∀ᶠ a in U, ‖u a‖ ≤ C) :
    ∃ φ : StrongDual 𝕜 X, ‖φ‖ ≤ C ∧
      Tendsto (fun a ↦ StrongDual.toWeakDual (u a)) U (𝓝 (StrongDual.toWeakDual φ)) := by
  obtain ⟨φ, hφC, hφ⟩ := (hC : ∀ᶠ a in (U : Filter α), ‖u a‖ ≤ C).exists_mapClusterPt_toWeakDual
  rw [mapClusterPt_def, ← Ultrafilter.coe_map, Ultrafilter.clusterPt_iff] at hφ
  exact ⟨φ, hφC, hφ⟩

/-- An eventually bounded proper filter has a weak-star bidual cluster point with the
same norm bound. No completeness of the space is required. -/
theorem Filter.Eventually.exists_mapClusterPt_inclusionInDoubleDual [ProperSpace 𝕜] [l.NeBot]
    {C : ℝ} (hC : ∀ᶠ x in l, ‖x‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 X), ‖E‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual E) l
        (fun x ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)) :=
  (hC.mono fun x hx ↦ (double_dual_bound 𝕜 X x).trans hx).exists_mapClusterPt_toWeakDual
