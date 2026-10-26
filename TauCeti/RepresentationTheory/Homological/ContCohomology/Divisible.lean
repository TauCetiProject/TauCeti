/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Torsion
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup
public import Mathlib.GroupTheory.Divisible

/-!
# Vanishing for divisible discrete coefficients

For a compact group, vanishing in a positive degree for every discrete torsion module implies
vanishing in that degree for every divisible discrete module. No triviality of the action is
required. This reduces divisible-coefficient calculations to torsion-coefficient calculations,
in particular for the profinite integers.

Degree zero is excluded: the invariants of a trivial divisible module need not vanish.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Proposition 2, for the divisible-coefficient
  calculation for the profinite integers.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.3.2) and (1.6.1), for the long exact sequence and torsion in positive degrees.
-/

public section

namespace TauCeti.ContinuousCohomology

open CategoryTheory ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- If continuous cohomology in a positive degree vanishes for all discrete torsion modules,
it also vanishes for all divisible discrete modules, with arbitrary continuous action. -/
theorem subsingleton_continuousCohomology_of_divisible_of_forall_isAddTorsion (n : ℕ)
    (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A], IsAddTorsion A →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [DivisibleBy M ℕ] :
    Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  suffices hz : ∀ x : continuousCohomology (n + 1) (ofDiscreteModule ℤ G M), x = 0 from
    ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  intro x
  -- Torsion of positive-degree cohomology: NSW (1.6.1).
  obtain ⟨k, hk, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
    (isAddTorsion_continuousCohomology n x)
  -- The kernel of multiplication by the annihilator is a discrete torsion module.
  let K := (nsmulAddMonoidHom k : M →+ M).ker
  have hK : ∀ g : G, ∀ m ∈ K, g • m ∈ K := fun g m hm ↦ by
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hm ⊢
    rw [smul_comm, hm, smul_zero]
  let := K.restrictDistribMulAction hK
  have : ContinuousSMul G K := K.restrictDistribMulAction_continuousSMul hK
  have hKt : IsAddTorsion K := fun m ↦ isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨k, hk, Subtype.ext (AddMonoidHom.mem_ker.mp m.property)⟩
  have := h K hKt
  -- Divisibility makes multiplication by k surjective, giving a short exact sequence.
  let S : DiscreteShortExact G K M M :=
    { incl := K.subtype
      proj := nsmulAddMonoidHom k
      incl_equivariant := K.restrictDistribMulAction_coe_smul hK
      proj_equivariant := fun g m ↦ smul_comm k g m
      incl_injective := K.subtype_injective
      proj_surjective := DivisibleBy.surjective_smul M ℕ (Nat.ne_of_gt hk)
      exact := fun m ↦ by
        simp only [← AddMonoidHom.mem_ker, Set.mem_range]
        exact ⟨fun hm ↦ ⟨⟨m, hm⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.property⟩ }
  have hmap : coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) (n + 1) =
      k • 𝟙 (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) :=
    coeffMap_nsmulAddMonoidHom (G := G) k (n + 1)
  apply S.coeffMap_proj_injective (n := n + 1)
  simpa only [hmap, TopModuleCat.hom_nsmul, smul_apply, TopModuleCat.hom_id,
    ContinuousLinearMap.id_apply, smul_zero] using hx

end TauCeti.ContinuousCohomology
