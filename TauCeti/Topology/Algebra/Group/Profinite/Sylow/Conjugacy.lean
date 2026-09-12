/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.QuotientGroup.Map

/-!
# Conjugacy of Sylow subgroups in profinite groups

Any two Sylow pro-`p` subgroups of a profinite group are conjugate. At every finite continuous
quotient their images are ordinary Sylow subgroups, so finite Sylow theory supplies a nonempty
set of conjugators. The inverse images of these finite sets form a downward-directed family of
closed subsets of the ambient compact group. An element of their intersection conjugates the
two closed subgroups in every finite quotient, and hence conjugates the subgroups themselves.

## Main results

* `IsProPSylow.exists_map_conj_eq`: any two Sylow pro-`p` subgroups are conjugate.
* `IsProPSylow.eq_of_normal`: a normal Sylow pro-`p` subgroup is unique.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {P Q : Subgroup G}

namespace IsProPSylow

/-- Any two Sylow pro-`p` subgroups of a profinite group are conjugate. -/
theorem exists_map_conj_eq (hP : IsProPSylow p P) (hQ : IsProPSylow p Q) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom = Q := by
  let PSylow (U : OpenNormalSubgroup G) : Sylow p (G ⧸ U.toSubgroup) :=
    (hP.isProP.isPGroup_map_mk' U).toSylow (hP.not_dvd_index U)
  let QSylow (U : OpenNormalSubgroup G) : Sylow p (G ⧸ U.toSubgroup) :=
    (hQ.isProP.isPGroup_map_mk' U).toSylow (hQ.not_dvd_index U)
  let conjugators (U : OpenNormalSubgroup G) : Set (G ⧸ U.toSubgroup) :=
    {x | x • PSylow U = QSylow U}
  let t (U : OpenNormalSubgroup G) : Set G :=
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' conjugators U
  have mem_t {U : OpenNormalSubgroup G} {g : G} : g ∈ t U ↔
      (P.map (QuotientGroup.mk' U.toSubgroup)).map
          (MulAut.conj (g : G ⧸ U.toSubgroup)).toMonoidHom =
        Q.map (QuotientGroup.mk' U.toSubgroup) := by
    simp only [t, conjugators, PSylow, QSylow, Set.mem_preimage, Set.mem_ofPred_eq,
      Sylow.ext_iff, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
    -- Mathlib defines the pointwise `MulAut` action on subgroups as `Subgroup.map`
    -- (`Subgroup.pointwise_smul_def` is `rfl`) and provides no rewrite lemma to `toMonoidHom`.
    exact Iff.rfl
  have ht_nonempty (U : OpenNormalSubgroup G) : (t U).Nonempty := by
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (G ⧸ U.toSubgroup) (PSylow U) (QSylow U)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
    exact ⟨g, hx⟩
  have ht_closed (U : OpenNormalSubgroup G) : IsClosed (t U) :=
    (isClosed_discrete (conjugators U)).preimage QuotientGroup.continuous_mk
  have ht_mono {U V : OpenNormalSubgroup G} (hVU : V ≤ U) : t V ⊆ t U := by
    intro g hg
    have hVU' : V.toSubgroup ≤ U.toSubgroup := fun _ hx ↦ hVU hx
    have hmap (R : Subgroup G) :
        (R.map (QuotientGroup.mk' V.toSubgroup)).map (QuotientGroup.mapOfLE hVU') =
          R.map (QuotientGroup.mk' U.toSubgroup) := by
      rw [Subgroup.map_map, QuotientGroup.mapOfLE_comp_mk']
    rw [mem_t] at hg ⊢
    rw [← hmap Q, ← hg, Subgroup.map_conj_map, hmap P, QuotientGroup.mapOfLE_mk]
  have ht_directed : Directed (· ⊇ ·) t := by
    intro U V
    exact ⟨U ⊓ V, ht_mono inf_le_left, ht_mono inf_le_right⟩
  let _ : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    ht_directed ht_nonempty (fun U ↦ (ht_closed U).isCompact) ht_closed
  refine ⟨g, ?_⟩
  rw [Subgroup.eq_iInf_sup_openNormalSubgroup Q hQ.isClosed,
    Subgroup.eq_iInf_sup_openNormalSubgroup _ (hP.map_conj g).isClosed]
  congr 1
  funext U
  have himages : (P.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' U.toSubgroup) =
      Q.map (QuotientGroup.mk' U.toSubgroup) := by
    rw [Subgroup.map_conj_map, QuotientGroup.mk'_apply]
    exact mem_t.mp (Set.mem_iInter.mp hg U)
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' U.toSubgroup)) himages
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hcomap

/-- A normal Sylow pro-`p` subgroup is the unique Sylow pro-`p` subgroup. -/
theorem eq_of_normal (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (P Q : Subgroup G)
    (hP : IsProPSylow p P) (hQ : IsProPSylow p Q) (hn : P.Normal) : P = Q := by
  obtain ⟨g, rfl⟩ := hP.exists_map_conj_eq hQ
  exact (@Subgroup.Normal.map_conj_eq G _ P hn g).symm

end IsProPSylow

end TauCeti
