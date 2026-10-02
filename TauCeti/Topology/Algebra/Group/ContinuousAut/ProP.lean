/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Congruence
public import TauCeti.Topology.Algebra.Group.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic
import TauCeti.GroupTheory.Frattini
import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration
import TauCeti.Topology.Algebra.Group.Profinite.ProP.MaximalSubgroup

/-!
# Continuous automorphisms of pro-`p` groups

Let `G` be a compact pro-`p` group and write `Φ(G) = proPFrattini p G` for its Frattini subgroup.
The continuous automorphisms of `G` acting trivially on the Frattini quotient `G ⧸ Φ(G)` form the
kernel of `ContinuousAut.mapQuotient : ContinuousAut G →* MulAut (G ⧸ Φ(G))`. This file shows that
this kernel is a pro-`p` group for the congruence topology, and that when `G` is topologically
finitely generated it is moreover open and of finite index. So the continuous automorphism group
of a topologically finitely generated pro-`p` group is virtually pro-`p`.

The pro-`p` property is the finite theorem `IsPGroup.isPGroup_ker_mapQuotient_frattini`, passed to
the limit. A neighbourhood of the identity in the congruence topology contains the automorphisms
acting trivially on some finite quotient `P = G ⧸ N` by a topologically characteristic open normal
subgroup. An automorphism acting trivially on `G ⧸ Φ(G)` induces on the finite `p`-group `P` an
automorphism acting trivially on `P ⧸ frattini P`, because the image of `Φ(G)` in `P` lies in the
Frattini subgroup of `P`. Such automorphisms of `P` form a `p`-group, so some `p`-power of the
original automorphism acts trivially on `P`, and lies in the given neighbourhood.

Openness holds because `Φ(G)` is an open, topologically characteristic subgroup of a topologically
finitely generated compact group, so the kernel is that of a coordinate of the congruence topology;
the finite index holds because `G ⧸ Φ(G)` is then finite.

## Main results

* `TauCeti.IsProP.isProP_ker_mapQuotient_proPFrattini`: for a compact pro-`p` group, the
  continuous automorphisms acting trivially on the Frattini quotient form a pro-`p` group.
* `TauCeti.ContinuousAut.isOpen_ker_mapQuotient_proPFrattini`: for a topologically finitely
  generated compact group, this kernel is open in the congruence topology.
* `TauCeti.ContinuousAut.finiteIndex_ker_mapQuotient_proPFrattini`: for a topologically finitely
  generated compact group, this kernel has finite index.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4 and §4.5.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann, D. Segal, *Analytic pro-p groups*, 2nd ed., Chapter 5.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

namespace ContinuousAut

/-- For a topologically finitely generated compact group, the continuous automorphisms acting
trivially on the pro-`p` Frattini quotient form an open subgroup for the congruence topology: the
pro-`p` Frattini subgroup is open and topologically characteristic. -/
theorem isOpen_ker_mapQuotient_proPFrattini (hG : IsTopologicallyFinitelyGenerated G) (p : ℕ) :
    IsOpen ((mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker :
      Set (ContinuousAut G)) :=
  isOpen_ker_mapQuotient ⟨⟨proPFrattini p G, hG.isOpen_proPFrattini p⟩, inferInstance⟩
    (isTopCharacteristic_proPFrattini p)

/-- For a topologically finitely generated compact group, the continuous automorphisms acting
trivially on the pro-`p` Frattini quotient form a subgroup of finite index: the Frattini quotient
is finite, and so is its automorphism group. -/
theorem finiteIndex_ker_mapQuotient_proPFrattini (hG : IsTopologicallyFinitelyGenerated G)
    (p : ℕ) : (mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker.FiniteIndex :=
  have := hG.finite_quotient_proPFrattini p
  inferInstance

end ContinuousAut

open ContinuousAut in
/-- **The continuous automorphisms of a pro-`p` group acting trivially on its Frattini quotient
form a pro-`p` group.** For a compact pro-`p` group `G`, the kernel of
`ContinuousAut G →* MulAut (G ⧸ proPFrattini p G)` is pro-`p` for the congruence topology. -/
theorem IsProP.isProP_ker_mapQuotient_proPFrattini {p : ℕ} [Fact p.Prime] (hG : IsProP p G) :
    IsProP p (mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker := by
  refine isProP_iff.mpr fun V ↦ ?_
  -- `V` contains the automorphisms in the kernel that act trivially on some characteristic open
  -- quotient `G ⧸ N`.
  obtain ⟨u, hu, huV⟩ := (mem_nhds_subtype _ _ _).mp (V.isOpen.mem_nhds V.one_mem)
  obtain ⟨N, hN, hNu⟩ := (hasBasis_nhds (1 : ContinuousAut G)).mem_iff.mp hu
  have : Finite (G ⧸ (N : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ N.isOpen
  have := QuotientGroup.discreteTopology N.isOpen
  have hP : IsPGroup p (G ⧸ (N : Subgroup G)) := isProP_iff.mp hG N
  intro q
  induction q using QuotientGroup.induction_on with
  | H φ =>
  -- The automorphism induced by `φ` on the finite `p`-group `G ⧸ N` is trivial modulo the
  -- Frattini subgroup, which contains the image of `proPFrattini p G`.
  have hφ : mapQuotient hN φ.1 ∈ (MulAut.mapQuotient (frattini (G ⧸ (N : Subgroup G)))).ker := by
    refine (MulAut.mem_ker_mapQuotient_iff _).mpr fun x ↦ ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
    have hx : (φ.1 x)⁻¹ * x ∈ proPFrattini p G := by
      refine QuotientGroup.eq.mp ?_
      simpa using (mapQuotient_eq_iff _).mp ((MonoidHom.mem_ker.mp φ.2).trans (map_one _).symm) x
    rw [mapQuotient_mk, QuotientGroup.eq, ← hP.proPFrattini_eq_frattini]
    exact MonoidHom.map_proPFrattini_le (QuotientGroup.mk' _) QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective _) ⟨_, hx, by simp⟩
  -- So some `p`-power of `φ` acts trivially on `G ⧸ N`, and lies in `V`.
  obtain ⟨k, hk⟩ := hP.isPGroup_ker_mapQuotient_frattini ⟨_, hφ⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  refine huV (hNu fun x ↦ ?_)
  have h1 : mapQuotient hN (φ ^ p ^ k).1 = mapQuotient hN 1 := by
    simpa using congrArg Subtype.val hk
  exact (mapQuotient_eq_iff hN).mp h1 x

end TauCeti
