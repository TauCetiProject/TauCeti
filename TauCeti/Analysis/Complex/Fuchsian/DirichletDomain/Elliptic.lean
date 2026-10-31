/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# The elliptic part of a Dirichlet domain

Let `Γ ≤ PSL(2, ℝ)` be discrete with finitely many elliptic orbits. A nonidentity element fixing a
point `w` moves only a bounded set of points a bounded distance
(`Matrix.ProjectiveSpecialLinearGroup.isBounded_setOf_dist_smul_le_of_smul_eq_self`). As there are
finitely many elliptic orbits and each stabilizer is finite, the points moved a bounded distance by
a nonidentity element of `Γ` fixing a point lie in the `Γ`-orbit of a bounded set. Their
intersection with a Dirichlet domain is therefore bounded, because a point of the domain is the
point of its orbit closest to the centre.

## Main results

* `Subgroup.isBounded_dirichletDomain_inter_setOf_dist_smul_le`: for a discrete group with finitely
  many elliptic orbits, the points of a Dirichlet domain moved a bounded distance by a nonidentity
  element fixing a point form a bounded set.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§9.4 and 10.1.
-/

public section

open MulAction Set UpperHalfPlane TauCeti
open Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- **The elliptic part of a Dirichlet domain is bounded.** Let `Γ ≤ PSL(2, ℝ)` be discrete with
finitely many elliptic orbits. For every centre `p` and every `ε`, the points of the Dirichlet
domain of `Γ` centred at `p` moved a distance at most `ε` by some nonidentity element of `Γ`
fixing a point of `ℍ` form a bounded set. -/
theorem isBounded_dirichletDomain_inter_setOf_dist_smul_le [DiscreteTopology Γ]
    (hΓ : Γ.ellipticOrbits.Finite) (p : ℍ) (ε : ℝ) :
    Bornology.IsBounded (dirichletDomain Γ p ∩
      {z | ∃ g : Γ, g ≠ 1 ∧ (∃ w : ℍ, g • w = w) ∧ dist (g • z) z ≤ ε}) := by
  -- the points moved at most `ε` by a nonidentity element fixing a chosen orbit representative
  let K : Set ℍ := ⋃ q ∈ Γ.ellipticOrbits, ⋃ g ∈ {g : Γ | g • q.out = q.out},
    {y | g ≠ 1 ∧ dist (g • y) y ≤ ε}
  have hK : Bornology.IsBounded K := by
    refine (Bornology.isBounded_biUnion hΓ).2 fun q _ ↦
      (Bornology.isBounded_biUnion (ProperlyDiscontinuousSMul.finite_stabilizer' Γ q.out)).2
        fun g hg ↦ ?_
    by_cases hg₁ : g = 1
    · simp [hg₁]
    · exact (isBounded_setOf_dist_smul_le_of_smul_eq_self
        (fun h ↦ hg₁ (Subtype.ext h)) hg ε).subset fun y hy ↦ hy.2
  refine (isBounded_dirichletDomain_inter_iUnion_smul (G := Γ) p hK).subset ?_
  rintro z ⟨hz, g, hg₁, ⟨w, hgw⟩, hgz⟩
  refine ⟨hz, ?_⟩
  -- move `w` to the chosen representative of its orbit, which is elliptic
  set q := Quotient.mk (orbitRel Γ ℍ) w
  have hq : q ∈ Γ.ellipticOrbits := by
    rw [quotientMk_mem_ellipticOrbits_iff, mem_freeLocus]
    exact fun h ↦ hg₁ ((Subgroup.eq_bot_iff_forall _).1 h g (mem_stabilizer_iff.2 hgw))
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, γ • w = q.out :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  refine mem_iUnion.2 ⟨γ⁻¹, γ • z, mem_iUnion₂.2 ⟨q, hq, mem_iUnion₂.2
    ⟨γ * g * γ⁻¹, ?_, ?_, ?_⟩⟩, inv_smul_smul γ z⟩
  · rw [mem_ofPred_eq, ← hγ, mul_smul, mul_smul, inv_smul_smul, hgw]
  · rwa [Ne, mul_inv_eq_one, mul_eq_left]
  · rwa [mul_smul, mul_smul, inv_smul_smul, dist_smul]

end Subgroup
