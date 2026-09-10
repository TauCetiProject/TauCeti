/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

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

omit [Fact p.Prime] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
private theorem map_mk'_map_quotient {U V : Subgroup G} [U.Normal] [V.Normal]
    (hVU : V ≤ U) (R : Subgroup G) :
    (R.map (QuotientGroup.mk' V)).map
        (QuotientGroup.map V U (.id G) (by simpa using hVU)) =
      R.map (QuotientGroup.mk' U) := by
  rw [Subgroup.map_map]
  congr 1

omit [Fact p.Prime] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
private theorem map_conj_mk'_map_quotient {U V : Subgroup G} [U.Normal] [V.Normal]
    (hVU : V ≤ U) (R : Subgroup G) (g : G) :
    ((R.map (QuotientGroup.mk' V)).map
        (MulAut.conj (g : G ⧸ V)).toMonoidHom).map
          (QuotientGroup.map V U (.id G) (by simpa using hVU)) =
      (R.map (QuotientGroup.mk' U)).map
        (MulAut.conj (g : G ⧸ U)).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1

omit [Fact p.Prime] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
private theorem map_conj_map_mk' (U : Subgroup G) [U.Normal]
    (R : Subgroup G) (g : G) :
    (R.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' U) =
      (R.map (QuotientGroup.mk' U)).map
        (MulAut.conj (g : G ⧸ U)).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1

namespace IsProPSylow

/-- Any two Sylow pro-`p` subgroups of a profinite group are conjugate. -/
theorem exists_map_conj_eq (hP : IsProPSylow p P) (hQ : IsProPSylow p Q) :
    ∃ g : G, Q = P.map (MulAut.conj g).toMonoidHom := by
  let PSylow (U : OpenNormalSubgroup G) : Sylow p (G ⧸ U.toSubgroup) :=
    (hP.isPGroup_map_mk' U).toSylow (hP.not_dvd_index U)
  let QSylow (U : OpenNormalSubgroup G) : Sylow p (G ⧸ U.toSubgroup) :=
    (hQ.isPGroup_map_mk' U).toSylow (hQ.not_dvd_index U)
  let conjugators (U : OpenNormalSubgroup G) : Set (G ⧸ U.toSubgroup) :=
    {x | x • PSylow U = QSylow U}
  let t (U : OpenNormalSubgroup G) : Set G :=
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' conjugators U
  have ht_nonempty (U : OpenNormalSubgroup G) : (t U).Nonempty := by
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (G ⧸ U.toSubgroup) (PSylow U) (QSylow U)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
    exact ⟨g, hx⟩
  have ht_closed (U : OpenNormalSubgroup G) : IsClosed (t U) :=
    (isClosed_discrete (conjugators U)).preimage QuotientGroup.continuous_mk
  have ht_mono {U V : OpenNormalSubgroup G} (hVU : V ≤ U) : t V ⊆ t U := by
    intro g hg
    -- Unfold the two local set abbreviations to expose the finite-level conjugacy equation.
    change (QuotientGroup.mk g : G ⧸ V.toSubgroup) • PSylow V = QSylow V at hg
    change (QuotientGroup.mk g : G ⧸ U.toSubgroup) • PSylow U = QSylow U
    apply Sylow.ext
    have hsub := congrArg (fun S : Sylow p (G ⧸ V.toSubgroup) ↦
      (S : Subgroup (G ⧸ V.toSubgroup))) hg
    -- Coercing the bundled Sylow equality exposes the subgroup images defining `PSylow`.
    change (((P.map (QuotientGroup.mk' V.toSubgroup)).map
        (MulAut.conj (g : G ⧸ V.toSubgroup)).toMonoidHom) =
      Q.map (QuotientGroup.mk' V.toSubgroup)) at hsub
    have hVU' : V.toSubgroup ≤ U.toSubgroup := fun _ hx ↦ hVU hx
    have hmap := congrArg (fun S : Subgroup (G ⧸ V.toSubgroup) ↦
      S.map (QuotientGroup.map V.toSubgroup U.toSubgroup (.id G) hVU')) hsub
    -- `Sylow.ext` leaves an equality of underlying subgroups at level `U`.
    change (P.map (QuotientGroup.mk' U.toSubgroup)).map
        (MulAut.conj (g : G ⧸ U.toSubgroup)).toMonoidHom =
      Q.map (QuotientGroup.mk' U.toSubgroup)
    rw [map_conj_mk'_map_quotient hVU', map_mk'_map_quotient hVU'] at hmap
    exact hmap
  have ht_directed : Directed (· ⊇ ·) t := by
    intro U V
    exact ⟨U ⊓ V, ht_mono inf_le_left, ht_mono inf_le_right⟩
  let _ : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    ht_directed ht_nonempty (fun U ↦ (ht_closed U).isCompact) ht_closed
  refine ⟨g, ?_⟩
  let R := P.map (MulAut.conj g).toMonoidHom
  -- Name the conjugate subgroup so the closed-subgroup reconstruction theorem applies directly.
  change Q = R
  have hconj_apply : (MulAut.conj g : G → G) = fun x ↦ g * x * g⁻¹ := by
    funext x
    exact MulAut.conj_apply g x
  have hconj : Continuous (MulAut.conj g : G → G) := by
    rw [hconj_apply]
    exact ((continuous_const : Continuous (fun _ : G ↦ g)).mul
        (continuous_id : Continuous (fun x : G ↦ x))).mul
      (continuous_const : Continuous (fun _ : G ↦ g⁻¹))
  have hRclosed : IsClosed (R : Set G) := by
    dsimp only [R]
    rw [Subgroup.coe_map]
    exact (hP.isClosed.isCompact.image hconj).isClosed
  rw [Subgroup.eq_iInf_sup_openNormalSubgroup Q hQ.isClosed,
    Subgroup.eq_iInf_sup_openNormalSubgroup R hRclosed]
  congr 1
  funext U
  have hgU := Set.mem_iInter.mp hg U
  -- Unfold the local conjugator sets at this quotient.
  change (QuotientGroup.mk g : G ⧸ U.toSubgroup) • PSylow U = QSylow U at hgU
  have hsub := congrArg (fun S : Sylow p (G ⧸ U.toSubgroup) ↦
    (S : Subgroup (G ⧸ U.toSubgroup))) hgU
  -- Coerce the bundled Sylow equality to its underlying subgroup equality.
  change ((P.map (QuotientGroup.mk' U.toSubgroup)).map
      (MulAut.conj (g : G ⧸ U.toSubgroup)).toMonoidHom) =
    Q.map (QuotientGroup.mk' U.toSubgroup) at hsub
  have himages : R.map (QuotientGroup.mk' U.toSubgroup) =
      Q.map (QuotientGroup.mk' U.toSubgroup) := by
    dsimp only [R]
    rw [map_conj_map_mk']
    exact hsub
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' U.toSubgroup)) himages
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hcomap.symm

/-- A normal Sylow pro-`p` subgroup is the unique Sylow pro-`p` subgroup. -/
theorem eq_of_normal (hP : IsProPSylow p P) (hQ : IsProPSylow p Q) (hn : P.Normal) :
    P = Q := by
  obtain ⟨g, rfl⟩ := hP.exists_map_conj_eq hQ
  exact (@Subgroup.Normal.map_conj_eq G _ P hn g).symm

end IsProPSylow

end TauCeti
