/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Arens.Basic
public import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
public import Mathlib.Topology.ApproximateUnit

/-!
# Approximate identities and mixed identities in the bidual

A weak-star cluster point of a right approximate identity is a right identity for the
first Arens product. A weak-star cluster point of a left approximate identity is a left
identity for the second product. These assertions require neither completeness nor a
bound on the approximate identity, once the cluster point is given.

For a one-sided approximate identity that is frequently bounded (in particular, a bounded
one), Banach–Alaoglu supplies an identity for the corresponding Arens product with the same
norm bound. For a two-sided approximate identity, it supplies a common cluster point
satisfying both identity laws. Such an element is called a mixed identity. The sides and
the products matter: this does not assert a two-sided identity for either product
separately.

All results allow a nonunital algebra and the zero algebra, without normalizing a unit
norm. The existence results work over any proper nontrivially normed field, in particular
over the real and complex numbers.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6 for the Arens products and
  §2.9 (Proposition 2.9.16) for approximate identities and mixed identities.
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
theorem arensMul_eq_left_of_tendsto_mul_left_of_mapClusterPt
    (hl : ∀ a : A, Tendsto (a * ·) l (𝓝 a))
    (hE : MapClusterPt (StrongDual.toWeakDual E) l
      (fun a ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a)))
    (F : StrongDual 𝕜 (StrongDual 𝕜 A)) : arensMul 𝕜 A F E = F := by
  ext f
  rw [arensMul_apply, ← arensExtension_apply,
    (ContinuousLinearMap.mul 𝕜 A).arensExtension_eq_left_of_tendsto_of_mapClusterPt
      (u := fun a ↦ a) (by simpa only [mul_apply'] using hl) hE F]

/-- A weak-star cluster point of a left approximate identity is a left identity for
the second Arens product. The approximate identity need not be bounded. -/
theorem arensMulRev_eq_right_of_tendsto_mul_right_of_mapClusterPt
    (hl : ∀ a : A, Tendsto (· * a) l (𝓝 a))
    (hE : MapClusterPt (StrongDual.toWeakDual E) l
      (fun a ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a)))
    (F : StrongDual 𝕜 (StrongDual 𝕜 A)) : arensMulRev 𝕜 A E F = F := by
  ext f
  rw [arensMulRev_apply, ← arensExtension_apply,
    (ContinuousLinearMap.mul 𝕜 A).flip.arensExtension_eq_left_of_tendsto_of_mapClusterPt
      (u := fun a ↦ a) (by simpa only [flip_apply, mul_apply'] using hl) hE F]

/-- A frequently bounded right approximate identity supplies a right identity for the first
Arens product, with the same norm bound. No completeness of the algebra is required. -/
theorem exists_arensMul_eq_left_of_tendsto_mul_left_of_frequently_norm_le [ProperSpace 𝕜]
    (hl : ∀ a : A, Tendsto (a * ·) l (𝓝 a)) {C : ℝ} (hC : ∃ᶠ a in l, ‖a‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 A), ‖E‖ ≤ C ∧ ∀ F, arensMul 𝕜 A F E = F := by
  obtain ⟨E, hEC, hE⟩ := hC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜) (u := fun a ↦ a)
  exact ⟨E, hEC, arensMul_eq_left_of_tendsto_mul_left_of_mapClusterPt hl hE⟩

/-- A frequently bounded left approximate identity supplies a left identity for the second
Arens product, with the same norm bound. No completeness of the algebra is required. -/
theorem exists_arensMulRev_eq_right_of_tendsto_mul_right_of_frequently_norm_le [ProperSpace 𝕜]
    (hl : ∀ a : A, Tendsto (· * a) l (𝓝 a)) {C : ℝ} (hC : ∃ᶠ a in l, ‖a‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 A), ‖E‖ ≤ C ∧ ∀ F, arensMulRev 𝕜 A E F = F := by
  obtain ⟨E, hEC, hE⟩ := hC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜) (u := fun a ↦ a)
  exact ⟨E, hEC, arensMulRev_eq_right_of_tendsto_mul_right_of_mapClusterPt hl hE⟩

end TauCeti

open TauCeti

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {l : Filter A}

/-- A frequently bounded two-sided approximate identity has a weak-star cluster point of no
greater norm which is a right identity for the first Arens product and a left identity for
the second. No completeness of the algebra is required. -/
theorem Filter.IsApproximateUnit.exists_mapClusterPt_and_arensMul_eq_left_and_arensMulRev_eq_right
    [ProperSpace 𝕜] (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∃ᶠ a in l, ‖a‖ ≤ C) :
    ∃ E : StrongDual 𝕜 (StrongDual 𝕜 A), ‖E‖ ≤ C ∧
      MapClusterPt (StrongDual.toWeakDual E) l
        (fun a ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 A a)) ∧
      (∀ F, arensMul 𝕜 A F E = F) ∧ (∀ F, arensMulRev 𝕜 A E F = F) := by
  obtain ⟨E, hEC, hE⟩ := hC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜) (u := fun a ↦ a)
  exact ⟨E, hEC, hE, arensMul_eq_left_of_tendsto_mul_left_of_mapClusterPt hl.tendsto_mul_left hE,
    arensMulRev_eq_right_of_tendsto_mul_right_of_mapClusterPt hl.tendsto_mul_right hE⟩
