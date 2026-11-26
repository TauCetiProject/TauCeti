/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import TauCeti.Algebra.Group.Pow

/-!
# Vanishing of continuous 1-cocycles on pro-`p` subgroups

If `P` is a pro-`p` subgroup of a topological group `G` acting trivially on a discrete
`p`-torsion-free `G`-module `M`, then every continuous 1-cocycle `c : ContCohomology.Z1 G M`
vanishes on `P` (`TauCeti.IsProP.apply_eq_zero_of_mem_Z1`).

## Main results

* `TauCeti.IsProP.apply_eq_zero_of_mem_Z1`: a continuous 1-cocycle with discrete `p`-torsion-free
  coefficients vanishes on every pro-`p` subgroup acting trivially on the coefficients.
-/

public section

open TauCeti.ContCohomology

namespace TauCeti

/-- **A continuous 1-cocycle with discrete `p`-torsion-free coefficients vanishes on any pro-`p`
subgroup acting trivially.** -/
theorem IsProP.apply_eq_zero_of_mem_Z1 {G M : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
    [DistribMulAction G M] {p : ℕ} {P : Subgroup G} (hP : IsProP p P)
    (htriv : ∀ g ∈ P, ∀ m : M, g • m = m) (hM : ∀ m : M, p • m = 0 → m = 0)
    (c : Z1 G M) {g : G} (hg : g ∈ P) :
    (c : G → M) g = 0 := by
  have hc := mem_Z1_iff.1 c.property
  set cRes : Z1 P M := ⟨fun x ↦ (c : G → M) x.val, mem_Z1_iff.2
    ⟨hc.1.comp continuous_subtypeVal, fun x y ↦ hc.2 x.val y.val⟩⟩ with hcRes
  have hcRes_apply (x : P) : (cRes : P → M) x = (c : G → M) x.val := by rw [hcRes]
  set f : ContinuousMonoidHom P (Multiplicative M) :=
    Additive.toMul (Z1EquivOfSmulEqSelf (fun x m ↦ htriv x.val x.property m) cRes) with hf
  have hf_apply (x : P) : f x = Multiplicative.ofAdd ((c : G → M) x.val) := by
    rw [hf, ← hcRes_apply x]
    exact Z1EquivOfSmulEqSelf_apply _ cRes x
  have hf_ker_open : IsOpen (f.toMonoidHom.ker : Set P) :=
    (isOpen_discrete ({1} : Set (Multiplicative M))).preimage f.continuous
  have hpg : IsPGroup p f.toMonoidHom.range := hP.isPGroup_range f.toMonoidHom hf_ker_open
  obtain ⟨k, hk⟩ := hpg ⟨f ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩
  have h1 : f ⟨g, hg⟩ ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [hf_apply, ← ofAdd_nsmul, ← ofAdd_zero] at h1
  exact eq_zero_of_pow_nsmul_eq_zero hM (Multiplicative.ofAdd.injective h1)

end TauCeti
