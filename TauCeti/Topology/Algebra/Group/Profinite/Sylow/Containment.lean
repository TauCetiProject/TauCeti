/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Existence
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.QuotientGroup.Map

/-!
# Sylow subgroups and the poset of pro-`p` subgroups

Every pro-`p` subgroup of a profinite group is contained in a Sylow pro-`p` subgroup, and the
Sylow pro-`p` subgroups are exactly the maximal ones. The containment statement is proved in the
sharper conjugacy form: given one Sylow pro-`p` subgroup `P`, every pro-`p` subgroup `Q` lies in
a conjugate of `P`. At each finite continuous quotient the image of `Q` is a `p`-group and the
image of `P` is a Sylow subgroup, so finite Sylow theory supplies a nonempty set of elements
conjugating `P` past `Q`; these sets are closed and downward directed, and a point of their
intersection conjugates `P` past `Q` in every finite quotient, hence past `Q` itself.

Maximality runs the same finite-level comparison without compactness: a pro-`p` subgroup
containing a Sylow pro-`p` subgroup has the same image in every finite quotient, and a Sylow
pro-`p` subgroup is closed, so the two subgroups agree. Together with containment this
identifies the Sylow pro-`p` subgroups with the maximal pro-`p` subgroups, and shows that a
pro-`p` group is its own unique Sylow pro-`p` subgroup.

## Main results

* `IsProP.exists_le_map_conj`: a pro-`p` subgroup lies in a conjugate of any given Sylow
  pro-`p` subgroup.
* `IsProP.exists_le_isProPSylow`: a pro-`p` subgroup lies in a Sylow pro-`p` subgroup.
* `IsProPSylow.eq_of_le`: a Sylow pro-`p` subgroup is maximal among the pro-`p`
  subgroups.
* `isProPSylow_iff_isProP_and_maximal`: the Sylow pro-`p` subgroups are exactly the
  maximal pro-`p` subgroups.
* `IsProPSylow.eq_top`: a Sylow pro-`p` subgroup of a pro-`p` profinite group is the whole
  group. Together with `IsProP.isProPSylow_top` this says that a pro-`p` profinite group is its
  own unique Sylow pro-`p` subgroup.

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

/-- **Containment in a conjugate.** A pro-`p` subgroup of a profinite group is contained in a
conjugate of any given Sylow pro-`p` subgroup. -/
theorem IsProP.exists_le_map_conj (hQ : IsProP p Q) (hP : IsProPSylow p P) :
    ∃ g : G, Q ≤ P.map (MulAut.conj g).toMonoidHom := by
  -- At each finite level the image of `P` is an ordinary Sylow subgroup.
  let PSylow (U : OpenNormalSubgroup G) : Sylow p (G ⧸ U.toSubgroup) :=
    (hP.isProP.isPGroup_map_mk' U).toSylow (hP.not_dvd_index U)
  have hPSylow (U : OpenNormalSubgroup G) :
      (PSylow U : Subgroup (G ⧸ U.toSubgroup)) = P.map (QuotientGroup.mk' U.toSubgroup) :=
    IsPGroup.toSylow_coe _ _
  -- The elements that conjugate `P` past `Q` in the quotient by `U`.
  let conjugators (U : OpenNormalSubgroup G) : Set (G ⧸ U.toSubgroup) :=
    {x | Q.map (QuotientGroup.mk' U.toSubgroup) ≤ (x • PSylow U : Sylow p (G ⧸ U.toSubgroup))}
  let t (U : OpenNormalSubgroup G) : Set G := QuotientGroup.mk' U.toSubgroup ⁻¹' conjugators U
  have mem_t {U : OpenNormalSubgroup G} {g : G} : g ∈ t U ↔
      Q.map (QuotientGroup.mk' U.toSubgroup) ≤
        (P.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' U.toSubgroup) := by
    simp only [t, conjugators, Set.mem_preimage, Set.mem_ofPred_eq, Sylow.coe_subgroup_smul,
      QuotientGroup.mk'_apply, Subgroup.map_conj_map, hPSylow]
    -- Mathlib defines the pointwise `MulAut` action on subgroups as `Subgroup.map`
    -- (`Subgroup.pointwise_smul_def` is `rfl`) and provides no rewrite lemma to `toMonoidHom`.
    exact Iff.rfl
  have ht_nonempty (U : OpenNormalSubgroup G) : (t U).Nonempty := by
    obtain ⟨S, hS⟩ := (hQ.isPGroup_map_mk' U).exists_le_sylow
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (G ⧸ U.toSubgroup) (PSylow U) S
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
    refine ⟨g, ?_⟩
    simp only [t, conjugators, Set.mem_preimage, Set.mem_ofPred_eq, hx]
    exact hS
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
    rw [← hmap Q, ← hmap (P.map (MulAut.conj g).toMonoidHom)]
    exact Subgroup.map_mono hg
  have ht_directed : Directed (· ⊇ ·) t := fun U V ↦
    ⟨U ⊓ V, ht_mono inf_le_left, ht_mono inf_le_right⟩
  let _ : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    ht_directed ht_nonempty (fun U ↦ (ht_closed U).isCompact) ht_closed
  -- A conjugate of a Sylow pro-`p` subgroup is closed, so it is the infimum of its joins with
  -- the open normal subgroups, and each join contains `Q` by the finite-level containment.
  refine ⟨g, ?_⟩
  rw [Subgroup.eq_iInf_sup_openNormalSubgroup _ (hP.map_conj g).isClosed]
  refine le_iInf fun U ↦ ?_
  calc Q ≤ (Q.map (QuotientGroup.mk' U.toSubgroup)).comap (QuotientGroup.mk' U.toSubgroup) :=
        Subgroup.le_comap_map _ _
    _ ≤ ((P.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' U.toSubgroup)).comap
          (QuotientGroup.mk' U.toSubgroup) :=
        Subgroup.comap_mono (mem_t.mp (Set.mem_iInter.mp hg U))
    _ = P.map (MulAut.conj g).toMonoidHom ⊔ U.toSubgroup := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-- **Containment.** Every pro-`p` subgroup of a profinite group is contained in a Sylow pro-`p`
subgroup. -/
theorem IsProP.exists_le_isProPSylow (hQ : IsProP p Q) :
    ∃ P : Subgroup G, IsProPSylow p P ∧ Q ≤ P := by
  obtain ⟨P, hP⟩ := exists_isProPSylow p G
  obtain ⟨g, hg⟩ := hQ.exists_le_map_conj hP
  exact ⟨_, hP.map_conj g, hg⟩

/-- **Maximality.** A pro-`p` subgroup of a profinite group that contains a Sylow pro-`p`
subgroup is equal to it. Equivalently, a closed pro-`p` subgroup of index prime to `p` is
maximal among the pro-`p` subgroups. -/
theorem IsProPSylow.eq_of_le (hP : IsProPSylow p P) (hQ : IsProP p Q) (hPQ : P ≤ Q) : P = Q := by
  refine le_antisymm hPQ ?_
  rw [Subgroup.eq_iInf_sup_openNormalSubgroup P hP.isClosed]
  refine le_iInf fun U ↦ ?_
  -- The image of `P` in `G ⧸ U` is a Sylow subgroup, so the `p`-group above it is no bigger.
  have hPU : ((hP.isProP.isPGroup_map_mk' U).toSylow (hP.not_dvd_index U) :
      Subgroup (G ⧸ U.toSubgroup)) = P.map (QuotientGroup.mk' U.toSubgroup) :=
    IsPGroup.toSylow_coe _ _
  have himage : Q.map (QuotientGroup.mk' U.toSubgroup) =
      P.map (QuotientGroup.mk' U.toSubgroup) := by
    have hle : ((hP.isProP.isPGroup_map_mk' U).toSylow (hP.not_dvd_index U) :
        Subgroup (G ⧸ U.toSubgroup)) ≤ Q.map (QuotientGroup.mk' U.toSubgroup) := by
      rw [hPU]
      exact Subgroup.map_mono hPQ
    have hmax := ((hP.isProP.isPGroup_map_mk' U).toSylow (hP.not_dvd_index U)).is_maximal'
      (hQ.isPGroup_map_mk' U) hle
    rwa [hPU] at hmax
  calc Q ≤ (Q.map (QuotientGroup.mk' U.toSubgroup)).comap (QuotientGroup.mk' U.toSubgroup) :=
        Subgroup.le_comap_map _ _
    _ = P ⊔ U.toSubgroup := by
        rw [himage, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-- A maximal pro-`p` subgroup of a profinite group is a Sylow pro-`p` subgroup. -/
theorem isProPSylow_of_maximal (hQ : IsProP p Q)
    (hmax : ∀ R : Subgroup G, IsProP p R → Q ≤ R → R ≤ Q) : IsProPSylow p Q := by
  obtain ⟨P, hP, hQP⟩ := hQ.exists_le_isProPSylow
  exact le_antisymm hQP (hmax P hP.isProP hQP) ▸ hP

/-- **The Sylow pro-`p` subgroups are the maximal pro-`p` subgroups.** Closedness is not part of
the right-hand side: a maximal pro-`p` subgroup is closed because it is Sylow. -/
theorem isProPSylow_iff_isProP_and_maximal :
    IsProPSylow p P ↔ IsProP p P ∧ ∀ R : Subgroup G, IsProP p R → P ≤ R → R ≤ P :=
  ⟨fun hP ↦ ⟨hP.isProP, fun _ hR hPR ↦ (hP.eq_of_le hR hPR).ge⟩,
    fun hP ↦ isProPSylow_of_maximal hP.1 hP.2⟩

/-- A Sylow pro-`p` subgroup of a pro-`p` group is the whole group. -/
theorem IsProPSylow.eq_top (hP : IsProPSylow p P) (hG : IsProP p G) : P = ⊤ :=
  hP.eq_of_le hG.top le_top

end TauCeti
