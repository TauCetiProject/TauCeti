/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Separation.Basic

/-!
# The zero locus of a continuous `1`-cocycle

For a `1`-cocycle `f : G → M` in the sense of Mathlib's unbundled `groupCohomology.IsCocycle₁`,
`groupCohomology.zeroLocus` is the subgroup `{g | f g = 0}` of `G`. This file records its
topological properties:

* `groupCohomology.isClosed_zeroLocus`: the zero locus of a continuous `1`-cocycle with values
  in a `T1` space is closed.
* `groupCohomology.eq_zero_of_eqOn_zero_of_topologicalClosure_closure_eq_top`: a continuous
  `1`-cocycle with values in a `T1` space that vanishes on a set whose generated subgroup is
  dense vanishes everywhere.
* `TauCeti.continuous_groupNormHom`: the norm of a finite normal subgroup is continuous when the
  ambient group acts by continuous maps.
-/

public section

namespace groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M] [TopologicalSpace G]
  [TopologicalSpace M] [T1Space M]

/-- The zero locus of a continuous `1`-cocycle with values in a `T1` space is closed. -/
theorem isClosed_zeroLocus {f : G → M} (hf : IsCocycle₁ f) (hc : Continuous f) :
    IsClosed (zeroLocus hf : Set G) := by
  rw [coe_zeroLocus]
  exact isClosed_singleton.preimage hc

/-- **A continuous `1`-cocycle vanishing on a topological generating set vanishes.** A continuous
`1`-cocycle with values in a `T1` space that vanishes on a set `s` whose generated subgroup is
dense vanishes everywhere. -/
theorem eq_zero_of_eqOn_zero_of_topologicalClosure_closure_eq_top [IsTopologicalGroup G]
    {f : G → M} (hf : IsCocycle₁ f) (hc : Continuous f) {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) (h : Set.EqOn f 0 s) : f = 0 := by
  have hle : (Subgroup.closure s).topologicalClosure ≤ zeroLocus hf :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).2 fun g hg ↦ (mem_zeroLocus hf).2 (h hg))
      (isClosed_zeroLocus hf hc)
  funext g
  exact (mem_zeroLocus hf).1 (hle (hs ▸ Subgroup.mem_top g))

end groupCohomology

namespace TauCeti

/-- The norm of a finite normal subgroup `N` of `G` is continuous on a module on which every
element of `G` acts continuously. -/
theorem continuous_groupNormHom {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Fintype N]
    (M : Type*) [AddCommMonoid M] [DistribMulAction G M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul G M] : Continuous (groupNormHom N M) :=
  (continuous_finsetSum Finset.univ fun n _ ↦ continuous_const_smul ((n : N) : G)).congr
    fun m ↦ by simp only [groupNormHom_apply, groupNorm_apply, Subgroup.smul_def]

end TauCeti
