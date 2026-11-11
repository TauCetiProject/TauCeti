/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Arens.Basic
public import Mathlib.Topology.ApproximateUnit

/-!
# Approximate identities and mixed identities in the bidual

A weak-star cluster point of a right approximate identity is a right identity for the
first Arens product. A weak-star cluster point of a left approximate identity is a left
identity for the second product. These assertions require neither completeness nor a
bound on the approximate identity, once the cluster point is given.

For a bounded two-sided approximate identity, Banach–Alaoglu supplies a common cluster
point, with the same norm bound, satisfying both identity laws. Such an element is called
a mixed identity. The sides and the products matter: this does not assert a two-sided
identity for either product separately.

All results allow a nonunital algebra and the zero algebra, without normalizing a unit
norm. The existence result works over any proper nontrivially normed field, in particular
over the real and complex numbers.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6.
-/

public section

open Filter NormedSpace ContinuousLinearMap
open scoped Topology

namespace TauCeti

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  {l : Filter A} {E : StrongDual 𝕜 (StrongDual 𝕜 A)}

-- Shorten instance search for the iterated duals, as in the basic Arens construction.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup ContinuousLinearMap.strongBidualNormedSpace

/-- A weak-star cluster point of a right approximate identity is a right identity for
the first Arens product. The approximate identity need not be bounded. -/
theorem arensMul_eq_left_of_mapClusterPt
    (hl : ∀ a : A, Tendsto (a * ·) l (𝓝 a))
    (hE : MapClusterPt (StrongDual.toWeakDual E) l
      (fun a ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a)))
    (F : StrongDual 𝕜 (StrongDual 𝕜 A)) : arensMul 𝕜 A F E = F := by
  ext f
  rw [arensMul_apply]
  congr 1
  ext a
  rw [bilinearTranspose_apply]
  have hc := hE.continuousAt_comp
    (WeakDual.eval_continuous ((mul 𝕜 A).bilinearTranspose f a)).continuousAt
  have ht := f.continuous.continuousAt.tendsto.comp (hl a)
  simp only [Function.comp_def, StrongDual.toWeakDual_apply, dual_def,
    bilinearTranspose_apply] at hc
  exact eq_of_nhds_neBot (hc.clusterPt.mono ht).neBot

/-- A weak-star cluster point of a left approximate identity is a left identity for
the second Arens product. The approximate identity need not be bounded. -/
theorem arensMulRev_eq_right_of_mapClusterPt
    (hl : ∀ a : A, Tendsto (· * a) l (𝓝 a))
    (hE : MapClusterPt (StrongDual.toWeakDual E) l
      (fun a ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a)))
    (F : StrongDual 𝕜 (StrongDual 𝕜 A)) : arensMulRev 𝕜 A E F = F := by
  ext f
  rw [arensMulRev_apply]
  congr 1
  ext a
  rw [bilinearTranspose_apply]
  have hc := hE.continuousAt_comp
    (WeakDual.eval_continuous ((mul 𝕜 A).flip.bilinearTranspose f a)).continuousAt
  have ht := f.continuous.continuousAt.tendsto.comp (hl a)
  simp only [Function.comp_def, StrongDual.toWeakDual_apply, dual_def,
    bilinearTranspose_apply] at hc
  exact eq_of_nhds_neBot (hc.clusterPt.mono ht).neBot

/-- A bounded two-sided approximate identity has a weak-star cluster point of no greater
norm which is a right identity for the first Arens product and a left identity for the
second. No completeness of the algebra is required. -/
theorem exists_mixedIdentity_of_isApproximateUnit [ProperSpace 𝕜]
    (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ a in l, ‖a‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 A), ‖E‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual E) l
        (fun a ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a)) ∧
      (∀ F, arensMul 𝕜 A F E = F) ∧ (∀ F, arensMulRev 𝕜 A E F = F) := by
  have := hl.neBot
  obtain ⟨E, hEC, hE⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 A)) C).exists_mapClusterPt
      (u := fun a : A ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a))
      (Filter.tendsto_principal.mpr <| hC.mono fun a ha ↦ by
        simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
          mem_closedBall_zero_iff] using (double_dual_bound 𝕜 A a).trans ha)
  refine ⟨E.toStrongDual, ?_, ?_, ?_, ?_⟩
  · exact mem_closedBall_zero_iff.mp hEC
  · simpa only [WeakDual.toWeakDual_toStrongDual] using hE
  · exact arensMul_eq_left_of_mapClusterPt hl.tendsto_mul_left hE
  · exact arensMulRev_eq_right_of_mapClusterPt hl.tendsto_mul_right hE

end TauCeti
