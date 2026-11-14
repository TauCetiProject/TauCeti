/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Weak-star cluster points in the bidual

Banach–Alaoglu gives a weak-star cluster point in the bidual for any eventually bounded
proper filter on a seminormed space. Evaluation of such a cluster point agrees with any
limit of the corresponding continuous linear functional. These facts let one transfer
approximate identity laws to identities for the Arens products.
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

/-- An eventually bounded proper filter has a weak-star bidual cluster point with the
same norm bound. No completeness of the space is required. -/
theorem Filter.Eventually.exists_mapClusterPt_inclusionInDoubleDual [ProperSpace 𝕜] [l.NeBot]
    {C : ℝ} (hC : ∀ᶠ x in l, ‖x‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 X), ‖E‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual E) l
        (fun x ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)) := by
  obtain ⟨E, hEC, hE⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 X)) C).exists_mapClusterPt
      (u := fun x : X ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x))
      (Filter.tendsto_principal.mpr <| hC.mono fun x hx ↦ by
        simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
          mem_closedBall_zero_iff] using (double_dual_bound 𝕜 X x).trans hx)
  refine ⟨E.toStrongDual, mem_closedBall_zero_iff.mp hEC, ?_⟩
  simpa only [WeakDual.toWeakDual_toStrongDual] using hE
