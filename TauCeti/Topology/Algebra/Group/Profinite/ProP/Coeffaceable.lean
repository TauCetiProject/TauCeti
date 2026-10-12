/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# `H⁰` is co-effaceable on the finite modules of an infinite pro-`p` group

Let `G` be an infinite pro-`p` group and `M` a finite discrete `p`-primary torsion `G`-module. Then
`M` is a quotient of a finite discrete `G`-module `M₁` in such a way that no nonzero invariant of
`M` lifts to an invariant of `M₁`: the map `H⁰(G, M₁) → H⁰(G, M)` induced by the surjection
`M₁ → M` is zero. The functor `H⁰` is *co-effaceable* on this category of coefficients.

The module `M₁` is the coinduced module `Coind_V^G M` of `TauCeti.DiscreteCoind` along an open
subgroup `V`, and the surjection is the trace `TauCeti.DiscreteCoind.trace`. The choice of `V` is
the whole content. Fix an open normal subgroup `U` acting trivially on `M`. Since `G` is infinite
and pro-`p`, `U` contains open normal subgroups `V` of arbitrarily large `p`-power relative index
`[U : V]` (`TauCeti.IsProP.exists_openNormalSubgroup_le_pow_dvd_relIndex`). A `G`-invariant element
of `Coind_V^G M` is a constant function with value `m ∈ M`, and its trace is the norm
`∑_{q ∈ G ⧸ V} q.out • m`, which groups into `[U : V]` copies of the norm along `G ⧸ U` because `U`
fixes `m` (`TauCeti.DiscreteCoind.trace_eq_relIndex_nsmul_of_forall_smul_eq`). Once `[U : V]` is
divisible by the exponent of `M`, this vanishes.

Co-effaceability of `H⁰` is the step of Tate's duality argument for the cohomological dimension of
a Demushkin group that upgrades the surjectivity of the duality map `H⁰(G, M) → H²(G, M^∨)^∨` to
injectivity: the connecting map of `0 → K → Coind_V^G M → M → 0` embeds `H⁰(G, M)` into `H¹(G, K)`,
where the duality map is already known to be bijective. The hypothesis that `G` is infinite is
used and cannot be dropped: for a finite group `G` the module `𝔽_p[G]` is projective, so every
`G`-equivariant surjection onto it splits and its invariants lift. In the proof, infinitude is what
supplies open normal subgroups of arbitrarily large `p`-power relative index.

## Main results

* `TauCeti.IsProP.exists_isOpen_trace_eq_zero_of_mem_H0`: **co-effaceability of `H⁰`**. For a finite
  discrete `p`-primary torsion module `M` over an infinite pro-`p` group there is an open subgroup
  `V` of finite index such that the trace `Coind_V^G M → M` vanishes on the `G`-invariants.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962–1964), exp. 252, §9.1.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.5.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G]

/-- **`H⁰` is co-effaceable on the finite modules of an infinite pro-`p` group.** For a finite
discrete `p`-primary torsion `G`-module `M` there is an open subgroup `V` of finite index such that
the trace `Coind_V^G M → M`, a `G`-equivariant surjection, vanishes on the `G`-invariants: the
induced map `H⁰(G, Coind_V^G M) → H⁰(G, M)` is zero. -/
theorem IsProP.exists_isOpen_trace_eq_zero_of_mem_H0 (hG : IsProP p G) (M : Type v)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
    [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    ∃ (V : Subgroup G) (_ : V.FiniteIndex), IsOpen (V : Set G) ∧
      ∀ f ∈ H0 G (DiscreteCoind G V M), DiscreteCoind.trace G V M f = 0 := by
  obtain ⟨k, hk⟩ := hM.exists_pow_smul_eq_zero
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq_self_range (G := G) (id : M → M)
  obtain ⟨V, hVU, hdvd⟩ := hG.exists_openNormalSubgroup_le_pow_dvd_relIndex U k
  have : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : V.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨V.toSubgroup, inferInstance, V.isOpen, fun f hf ↦ ?_⟩
  refine DiscreteCoind.trace_eq_zero_of_forall_smul_eq hVU (fun u hu m ↦ hU u hu m) (fun m ↦ ?_)
    ((FixedPoints.mem_addSubgroup _ _ f).1 hf)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, mul_nsmul, hk, nsmul_zero]

end TauCeti
