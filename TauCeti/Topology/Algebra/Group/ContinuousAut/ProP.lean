/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Congruence
public import Mathlib.GroupTheory.Frattini
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import TauCeti.Topology.Algebra.Group.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic
import TauCeti.GroupTheory.Frattini
import TauCeti.Topology.Algebra.Group.ContinuousAut.Profinite
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

For a topologically finitely generated pro-`p` group the kernel is moreover the inverse limit of
the finite kernels of the theorem above, taken over the topologically characteristic open normal
subgroups `N ≤ Φ(G)`. These are cofinal among the open subgroups because `Φ(G)` is open. For such
`N` the Frattini subgroup of `G ⧸ N` is exactly the image of `Φ(G)`, so an automorphism acts
trivially on `G ⧸ Φ(G)` exactly when its coordinate on `G ⧸ N` acts trivially on the Frattini
quotient of `G ⧸ N`. A compatible family of such coordinates is induced by a continuous
automorphism, by the limit description along a cofinal family
(`ContinuousAut.exists_mapQuotient_eq_of_forall_exists_le`).

## Main results

* `TauCeti.IsProP.isProP_ker_mapQuotient_proPFrattini`: for a compact pro-`p` group, the
  continuous automorphisms acting trivially on the Frattini quotient form a pro-`p` group.
* `TauCeti.ContinuousAut.isOpen_ker_mapQuotient_proPFrattini`: for a topologically finitely
  generated compact group, this kernel is open in the congruence topology.
* `TauCeti.ContinuousAut.finiteIndex_ker_mapQuotient_proPFrattini`: for a topologically finitely
  generated compact group, this kernel has finite index.
* `TauCeti.IsProP.mapQuotient_mem_ker_mapQuotient_frattini_iff`: for `N ≤ Φ(G)`, the kernel is
  detected on the Frattini quotient of the finite `p`-group `G ⧸ N`.
* `TauCeti.IsProP.range_pi_mapQuotient_ker_proPFrattini`,
  `TauCeti.ContinuousAut.isEmbedding_pi_mapQuotient_ker_proPFrattini`: for a topologically
  finitely generated pro-`p` group, the coordinates on the quotients `G ⧸ N`, `N ≤ Φ(G)`
  topologically characteristic and open, embed the kernel onto the compatible families of
  elements of the finite kernels.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4 and §4.5.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann, D. Segal, *Analytic pro-p groups*, 2nd ed., Chapter 5.
-/

public section

open Topology

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
/-- For a compact pro-`p` group `G`, a continuous automorphism acting trivially on the Frattini
quotient `G ⧸ proPFrattini p G` induces, on each finite quotient `G ⧸ N` by a topologically
characteristic open normal subgroup, an automorphism acting trivially on the Frattini quotient of
the finite `p`-group `G ⧸ N`: the image of `proPFrattini p G` lies in its Frattini subgroup. -/
theorem IsProP.mapQuotient_mem_ker_mapQuotient_frattini {p : ℕ} [Fact p.Prime] (hG : IsProP p G)
    {N : OpenNormalSubgroup G} (hN : IsTopCharacteristic G N) {φ : ContinuousAut G}
    (hφ : φ ∈ (mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker) :
    mapQuotient hN φ ∈ (MulAut.mapQuotient (frattini (G ⧸ (N : Subgroup G)))).ker := by
  have : Finite (G ⧸ (N : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ N.isOpen
  have := QuotientGroup.discreteTopology N.isOpen
  have hP : IsPGroup p (G ⧸ (N : Subgroup G)) := isProP_iff.mp hG N
  refine (MulAut.mem_ker_mapQuotient_iff _).mpr fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H x =>
  have hx : (φ x)⁻¹ * x ∈ proPFrattini p G := by
    refine QuotientGroup.eq.mp ?_
    simpa using (mapQuotient_eq_iff _).mp ((MonoidHom.mem_ker.mp hφ).trans (map_one _).symm) x
  rw [mapQuotient_mk, QuotientGroup.eq, ← hP.proPFrattini_eq_frattini]
  exact MonoidHom.map_proPFrattini_le (QuotientGroup.mk' _) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective _) ⟨_, hx, by simp⟩

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
  have hP : IsPGroup p (G ⧸ (N : Subgroup G)) := isProP_iff.mp hG N
  intro q
  induction q using QuotientGroup.induction_on with
  | H φ =>
  -- The automorphism induced by `φ` on the finite `p`-group `G ⧸ N` is trivial modulo the
  -- Frattini subgroup, so some `p`-power of `φ` acts trivially on `G ⧸ N`, and lies in `V`.
  obtain ⟨k, hk⟩ := hP.isPGroup_ker_mapQuotient_frattini
    ⟨_, hG.mapQuotient_mem_ker_mapQuotient_frattini hN φ.2⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  refine huV (hNu fun x ↦ ?_)
  have h1 : mapQuotient hN (φ ^ p ^ k).1 = mapQuotient hN 1 := by
    simpa using congrArg Subtype.val hk
  exact (mapQuotient_eq_iff hN).mp h1 x

section Limit

open ContinuousAut in
/-- For a compact pro-`p` group `G` and a topologically characteristic open normal subgroup
`N ≤ proPFrattini p G`, a continuous automorphism acts trivially on the Frattini quotient of `G`
exactly when it induces on the finite `p`-group `G ⧸ N` an automorphism acting trivially on the
Frattini quotient of `G ⧸ N`: the Frattini subgroup of `G ⧸ N` is the image of
`proPFrattini p G`. -/
theorem IsProP.mapQuotient_mem_ker_mapQuotient_frattini_iff {p : ℕ} [Fact p.Prime]
    (hG : IsProP p G) {N : OpenNormalSubgroup G} (hN : IsTopCharacteristic G N)
    (hle : (N : Subgroup G) ≤ proPFrattini p G) {φ : ContinuousAut G} :
    mapQuotient hN φ ∈ (MulAut.mapQuotient (frattini (G ⧸ (N : Subgroup G)))).ker ↔
      φ ∈ (mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker := by
  refine ⟨fun h ↦ ?_, hG.mapQuotient_mem_ker_mapQuotient_frattini hN⟩
  have : Finite (G ⧸ (N : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ N.isOpen
  have := QuotientGroup.discreteTopology N.isOpen
  have hP : IsPGroup p (G ⧸ (N : Subgroup G)) := isProP_iff.mp hG N
  refine MonoidHom.mem_ker.mpr (((mapQuotient_eq_iff _).mpr fun x ↦ ?_).trans (map_one _))
  have hx := (MulAut.mem_ker_mapQuotient_iff _).mp h (x : G ⧸ (N : Subgroup G))
  rw [mapQuotient_mk, QuotientGroup.eq, ← hP.proPFrattini_eq_frattini] at hx
  -- The preimage of the Frattini subgroup of `G ⧸ N` is `proPFrattini p G ⊔ N = proPFrattini p G`.
  have hx' : (φ x)⁻¹ * x ∈
      (proPFrattini p (G ⧸ (N : Subgroup G))).comap (QuotientGroup.mk' (N : Subgroup G)) := by
    simpa using hx
  rw [comap_proPFrattini_eq_of_surjective Fact.out _ QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective _), QuotientGroup.ker_mk', sup_eq_left.mpr hle] at hx'
  exact QuotientGroup.eq.mpr (by simpa using hx')

variable [TotallyDisconnectedSpace G]

/-- For a topologically finitely generated profinite group `G`, the coordinates on the quotients
`G ⧸ N` by the topologically characteristic open normal subgroups `N ≤ proPFrattini p G` embed
the kernel of `ContinuousAut G →* MulAut (G ⧸ proPFrattini p G)` into the product of the discrete
automorphism groups of these finite quotients. -/
theorem ContinuousAut.isEmbedding_pi_mapQuotient_ker_proPFrattini
    (hG : IsTopologicallyFinitelyGenerated G) (p : ℕ) :
    letI : ∀ N : {N : OpenNormalSubgroup G //
        IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G},
      TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
    IsEmbedding fun (φ : (mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker)
      (N : {N : OpenNormalSubgroup G //
        IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G}) ↦
      mapQuotient N.2.1 φ.1 := by
  let _ : ∀ N : {N : OpenNormalSubgroup G //
      IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G},
    TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
  exact (isEmbedding_pi_mapQuotient_of_forall_exists_le hG
    (N := fun N : {N : OpenNormalSubgroup G //
      IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G} ↦ N.1)
    (fun N ↦ N.2.1) fun M _ ↦
      let ⟨N, hN, hΦ, hle⟩ := hG.exists_isTopCharacteristic_le_proPFrattini p M.toOpenSubgroup
      ⟨⟨N, hN, hΦ⟩, fun _ hx ↦ hle hx⟩).comp IsEmbedding.subtypeVal

open ContinuousAut in
/-- **The kernel on the Frattini quotient is the inverse limit of the finite kernels.** For a
topologically finitely generated pro-`p` group `G`, the coordinates on the quotients `G ⧸ N` by the
topologically characteristic open normal subgroups `N ≤ proPFrattini p G` identify the kernel of
`ContinuousAut G →* MulAut (G ⧸ proPFrattini p G)` with the families of automorphisms `σ N` of
the finite `p`-groups `G ⧸ N` that act trivially on the Frattini quotients of `G ⧸ N` and are
compatible with the quotient maps `G ⧸ N → G ⧸ M` for `N ≤ M`. The coordinate map is injective
and a topological embedding by `ContinuousAut.isEmbedding_pi_mapQuotient_ker_proPFrattini`. -/
theorem IsProP.range_pi_mapQuotient_ker_proPFrattini {p : ℕ} [Fact p.Prime] (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    Set.range (fun (φ : (mapQuotient (isTopCharacteristic_proPFrattini (G := G) p)).ker)
        (N : {N : OpenNormalSubgroup G //
          IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G}) ↦
        mapQuotient N.2.1 φ.1) =
      {σ : ∀ N : {N : OpenNormalSubgroup G //
          IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G},
          MulAut (G ⧸ (N.1 : Subgroup G)) |
        (∀ N, σ N ∈ (MulAut.mapQuotient (frattini (G ⧸ (N.1 : Subgroup G)))).ker) ∧
        ∀ ⦃N M : {N : OpenNormalSubgroup G //
          IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G}⦄ (hle : N.1 ≤ M.1)
          (q : G ⧸ (N.1 : Subgroup G)),
          QuotientGroup.mapOfLE hle (σ N q) = σ M (QuotientGroup.mapOfLE hle q)} := by
  ext σ
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨fun N ↦ hG.mapQuotient_mem_ker_mapQuotient_frattini N.2.1 φ.2,
      fun N M hle q ↦ mapOfLE_mapQuotient N.2.1 M.2.1 hle φ.1 q⟩
  · rintro ⟨hker, hσ⟩
    -- The family is cofinal among the open normal subgroups, so it is induced by some `φ`.
    obtain ⟨φ, hφ⟩ := exists_mapQuotient_eq_of_forall_exists_le
      (N := fun N : {N : OpenNormalSubgroup G //
        IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ proPFrattini p G} ↦ N.1)
      (fun N ↦ N.2.1)
      (fun U ↦
        let ⟨N, hN, hΦ, hle⟩ := hfg.exists_isTopCharacteristic_le_proPFrattini p U.toOpenSubgroup
        ⟨⟨N, hN, hΦ⟩, fun _ hx ↦ hle hx⟩)
      σ hσ
    -- Any single member of the family detects the kernel on the Frattini quotient.
    obtain ⟨N, hN, hΦ, -⟩ := hfg.exists_isTopCharacteristic_le_proPFrattini p ⊤
    refine ⟨⟨φ, (hG.mapQuotient_mem_ker_mapQuotient_frattini_iff hN hΦ).mp ?_⟩, funext hφ⟩
    exact hφ ⟨N, hN, hΦ⟩ ▸ hker ⟨N, hN, hΦ⟩

end Limit

end TauCeti
