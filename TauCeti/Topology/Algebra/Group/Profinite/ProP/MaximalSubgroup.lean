/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Frattini
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Algebra.ClopenNhdofOne
import TauCeti.GroupTheory.Index.Basic
import TauCeti.GroupTheory.PGroup
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside

/-!
# Maximal open subgroups of pro-`p` groups

In a compact pro-`p` group every maximal subgroup that is open is normal of index `p`. Such a
subgroup `M` contains an open normal subgroup `U`, and it is the preimage of a maximal subgroup
of the finite `p`-group `G ⧸ U`; a maximal subgroup of a finite `p`-group is normal of index `p`
(it is nilpotent, so satisfies the normalizer condition). Conversely a subgroup of prime index
is maximal in any group. So for a pro-`p` group the open normal subgroups of index `p`, whose
intersection defines `TauCeti.proPFrattini`, are exactly the maximal open subgroups, and the
pro-`p` Frattini subgroup is the intersection of the maximal open subgroups: the Frattini
subgroup in the usual sense.

A subgroup containing an open subgroup is itself open, so a subgroup which is open and maximal
among all subgroups is the same thing as a maximal element of the lattice of open subgroups; the
statements below use the former reading.

Two consequences are recorded. For a nontrivial profinite pro-`p` group the pro-`p` Frattini
subgroup is proper, which is Burnside's non-generator property applied to the trivial subgroup.
For a finite `p`-group with the discrete topology, where every subgroup is open, the pro-`p`
Frattini subgroup agrees with Mathlib's abstract `frattini`.

## Main results

* `TauCeti.IsProP.normal_of_isCoatom`, `TauCeti.IsProP.index_eq_of_isCoatom`: a maximal open
  subgroup of a compact pro-`p` group is normal of index `p`.
* `TauCeti.IsProP.isCoatom_iff_index_eq`: an open subgroup of a compact pro-`p` group is maximal
  exactly when it has index `p`.
* `TauCeti.iInf_isCoatom_le_proPFrattini`: in any topological group, the intersection of the
  maximal open subgroups lies in the pro-`p` Frattini subgroup.
* `TauCeti.IsProP.proPFrattini_eq_iInf_isCoatom`: for a compact pro-`p` group the pro-`p`
  Frattini subgroup is the intersection of the maximal open subgroups.
* `TauCeti.IsProP.proPFrattini_ne_top`: the pro-`p` Frattini subgroup of a nontrivial profinite
  pro-`p` group is proper.
* `IsPGroup.proPFrattini_eq_frattini`: for a finite discrete `p`-group, the pro-`p` Frattini
  subgroup is Mathlib's `frattini`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-- In any topological group, the intersection of the maximal open subgroups lies in the pro-`p`
Frattini subgroup: an open normal subgroup of prime index `p` is a maximal open subgroup. -/
theorem iInf_isCoatom_le_proPFrattini :
    ⨅ (M : Subgroup G) (_ : IsOpen (M : Set G)) (_ : IsCoatom M), M ≤ proPFrattini p G := by
  rw [proPFrattini_def]
  refine le_iInf fun U ↦ ?_
  exact (iInf₂_le U.1.toSubgroup U.1.isOpen).trans
    (iInf_le _ (Subgroup.isCoatom_of_index_prime (by rw [U.2]; exact hp.out)))

namespace IsProP

variable [IsTopologicalGroup G] [CompactSpace G]

/-- A maximal open subgroup of a compact pro-`p` group is normal of index `p`. It is the
preimage of a maximal subgroup of a finite `p`-group quotient. -/
private theorem normal_and_index_eq_of_isCoatom (hG : IsProP p G) {M : Subgroup G}
    (hMo : IsOpen (M : Set G)) (hM : IsCoatom M) : M.Normal ∧ M.index = p := by
  obtain ⟨U, hU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ⟨M.isClosed_of_isOpen hMo, hMo⟩ M.one_mem
  let q : G →* G ⧸ U.toSubgroup := QuotientGroup.mk' U.toSubgroup
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U.toSubgroup
  have hMK : (M.map q).comap q = M :=
    Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hU)
  have hK : IsCoatom (M.map q) := by
    refine ⟨fun h ↦ hM.1 ?_, fun L hL ↦ ?_⟩
    · rw [← hMK, h, Subgroup.comap_top]
    · have hL' : L.comap q = ⊤ :=
        hM.2 _ (hMK ▸ (Subgroup.comap_lt_comap_of_surjective hq).mpr hL)
      rw [← Subgroup.map_comap_eq_self_of_surjective hq L, hL', Subgroup.map_top_of_surjective _ hq]
  have : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have hQ : IsPGroup p (G ⧸ U.toSubgroup) := isProP_iff.mp hG U
  have : Group.IsNilpotent (G ⧸ U.toSubgroup) := hQ.isNilpotent
  have hKn : (M.map q).Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom _ Group.normalizerCondition_of_isNilpotent hK
  refine ⟨hMK ▸ hKn.comap q, ?_⟩
  rw [← hMK, Subgroup.index_comap_of_surjective _ hq]
  exact hQ.index_eq_prime_of_isCoatom hK

/-- **A maximal open subgroup of a pro-`p` group is normal.** -/
theorem normal_of_isCoatom (hG : IsProP p G) {M : Subgroup G} (hMo : IsOpen (M : Set G))
    (hM : IsCoatom M) : M.Normal :=
  (hG.normal_and_index_eq_of_isCoatom hMo hM).1

/-- **A maximal open subgroup of a pro-`p` group has index `p`.** -/
theorem index_eq_of_isCoatom (hG : IsProP p G) {M : Subgroup G} (hMo : IsOpen (M : Set G))
    (hM : IsCoatom M) : M.index = p :=
  (hG.normal_and_index_eq_of_isCoatom hMo hM).2

/-- An open subgroup of a compact pro-`p` group is maximal exactly when it has index `p`. -/
theorem isCoatom_iff_index_eq (hG : IsProP p G) {M : Subgroup G} (hMo : IsOpen (M : Set G)) :
    IsCoatom M ↔ M.index = p :=
  ⟨hG.index_eq_of_isCoatom hMo, fun h ↦ Subgroup.isCoatom_of_index_prime (h ▸ hp.out)⟩

/-- **The pro-`p` Frattini subgroup is the intersection of the maximal open subgroups.** For a
compact pro-`p` group, the open normal subgroups of index `p` are exactly the maximal open
subgroups, so `proPFrattini p G` is the Frattini subgroup in the usual sense. -/
theorem proPFrattini_eq_iInf_isCoatom (hG : IsProP p G) :
    proPFrattini p G = ⨅ (M : Subgroup G) (_ : IsOpen (M : Set G)) (_ : IsCoatom M), M := by
  refine le_antisymm (le_iInf₂ fun M hMo ↦ le_iInf fun hM ↦ ?_) iInf_isCoatom_le_proPFrattini
  exact proPFrattini_le (U := ⟨⟨M, hMo⟩, hG.normal_of_isCoatom hMo hM⟩)
    (hG.index_eq_of_isCoatom hMo hM)

/-- **The Frattini subgroup of a nontrivial pro-`p` group is proper.** Otherwise the trivial
subgroup together with the Frattini subgroup would generate, and the Frattini subgroup consists
of non-generators. -/
theorem proPFrattini_ne_top [TotallyDisconnectedSpace G] [Nontrivial G] (hG : IsProP p G) :
    proPFrattini p G ≠ ⊤ := by
  intro h
  have hbot : IsClosed ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  exact bot_ne_top (hG.eq_top_of_sup_proPFrattini_eq_top hbot (by rw [h, sup_top_eq]))

end IsProP

/-- **The pro-`p` Frattini subgroup of a finite `p`-group is its Frattini subgroup.** With the
discrete topology every subgroup is open, so the maximal open subgroups are all the maximal
subgroups. -/
theorem _root_.IsPGroup.proPFrattini_eq_frattini [DiscreteTopology G] [Finite G]
    (hG : IsPGroup p G) : proPFrattini p G = frattini G := by
  rw [hG.isProP.proPFrattini_eq_iInf_isCoatom, frattini, Order.radical]
  simp only [isOpen_discrete, iInf_true, Set.mem_ofPred_eq]

end TauCeti
