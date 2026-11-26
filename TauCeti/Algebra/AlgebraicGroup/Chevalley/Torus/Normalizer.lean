/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient

/-!
# Torus centralizer and normalizer in the extended elementary Chevalley group

Over any infinite field `K`, inside `D.extendedElementarySubgroup K`, the normalizer of the
actual character-lattice torus `T(K)` is precisely the Weyl subgroup `D.weylSubgroup K`, and
its centralizer is `T(K)` itself.

The normalizer proof combines the sharp Bruhat normal form (`u * n * b`) with torus invariance
of `U_w(K)` (`ChevalleyDatum.range_torusPoints_le_normalizer_subsystemPoints`) and
self-normalization of `T(K)` in `B(K)`
(`ChevalleyDatum.borelSubgroup_inf_normalizer_range_torusPoints`). The centralizer calculation
then reduces to `D.weylSubgroup K` and identifies trivial Weyl projection with torus membership
via `ChevalleyDatum.weylProjection_eq_one_iff_mem_range_torusPoints`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.extendedElementarySubgroup_inf_normalizer_range_torusPoints`:
  over an infinite field, `D.extendedElementarySubgroup K ∩ N(T(K)) = D.weylSubgroup K`.
* `TauCeti.DynkinType.ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_range_torusPoints`:
  over an infinite field, `D.extendedElementarySubgroup K ∩ C(T(K)) = T(K)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.1–7.2.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht) (K : Type v) [Field K]

private theorem mem_centralizer_range_torusPoints_of_mul_mul_eq_of_mem_normalizer
    (n : D.weylSubgroup K) (u : D.inversionPoints K (D.weylProjection K n))
    (b : D.borelSubgroup K) {g : D.points K}
    (hg : (u : D.points K) * (n : D.points K) * b = g)
    (hgN : g ∈ Subgroup.normalizer (Set.range (D.torusPoints K))) :
    (u : D.points K) ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨r, rfl⟩
  let tr := D.torusPoints K r
  have htr' : g⁻¹ * tr * g ∈ (D.torusPoints K).range :=
    (Subgroup.mem_normalizer_iff''.mp hgN tr).mp ⟨r, rfl⟩
  have hu' : tr * (u : D.points K) * tr⁻¹ ∈
      D.inversionPoints K (D.weylProjection K n) :=
    (Subgroup.mem_normalizer_iff.mp
      (D.range_torusPoints_le_normalizer_inversionPoints K _ ⟨r, rfl⟩) u).mp u.property
  have hnt : (n : D.points K)⁻¹ * tr * (n : D.points K) ∈ (D.torusPoints K).range :=
    (Subgroup.mem_normalizer_iff''.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints K n.property) tr).mp ⟨r, rfl⟩
  have hb' : (n : D.points K)⁻¹ * tr * (n : D.points K) * (b : D.points K) *
      (g⁻¹ * tr * g)⁻¹ ∈ D.borelSubgroup K :=
    (D.borelSubgroup K).mul_mem
      ((D.borelSubgroup K).mul_mem (D.range_torusPoints_le_borelSubgroup K hnt) b.property)
      ((D.borelSubgroup K).inv_mem (D.range_torusPoints_le_borelSubgroup K htr'))
  have hprod : (tr * (u : D.points K) * tr⁻¹) * (n : D.points K) *
      ((n : D.points K)⁻¹ * tr * (n : D.points K) * (b : D.points K) *
        (g⁻¹ * tr * g)⁻¹) = (u : D.points K) * (n : D.points K) * b := by
    calc
      (tr * (u : D.points K) * tr⁻¹) * (n : D.points K) *
          ((n : D.points K)⁻¹ * tr * (n : D.points K) * (b : D.points K) *
            (g⁻¹ * tr * g)⁻¹)
        = tr * ((u : D.points K) * (n : D.points K) * b) * (g⁻¹ * tr * g)⁻¹ := by group
      _ = tr * g * (g⁻¹ * tr * g)⁻¹ := by rw [hg]
      _ = g := by group
      _ = (u : D.points K) * (n : D.points K) * b := hg.symm
  have heq := (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq K
    (D.inversionPoints_le_map_negativePoints_conj K n hu')
    (D.inversionPoints_le_map_negativePoints_conj K n u.property)
    hb' b.property hprod).1
  exact mul_inv_eq_iff_eq_mul.mp heq

variable [Infinite K]

private theorem torus_conj_bruhat_eq_of_mem_normalizer (n : D.weylSubgroup K)
    (u : D.inversionPoints K (D.weylProjection K n)) (b : D.borelSubgroup K)
    {g : D.points K} (hg : (u : D.points K) * (n : D.points K) * b = g)
    (hgN : g ∈ Subgroup.normalizer (Set.range (D.torusPoints K))) :
    (u : D.points K) = 1 := by
  rw [← Subgroup.mem_bot, ← D.positivePoints_inf_centralizer_range_torusPoints K]
  exact ⟨D.inversionPoints_le_positivePoints K _ u.property,
    D.mem_centralizer_range_torusPoints_of_mul_mul_eq_of_mem_normalizer K n u b hg hgN⟩

/-- **Torus normalizer in the extended elementary Chevalley group.** Over an infinite field,
the normalizer of the actual character-lattice torus inside `D.extendedElementarySubgroup K`
is precisely the Weyl subgroup `D.weylSubgroup K`. -/
@[simp]
theorem extendedElementarySubgroup_inf_normalizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.normalizer (Set.range (D.torusPoints K)) =
      D.weylSubgroup K := by
  have hW : D.weylSubgroup K ≤ Subgroup.normalizer (Set.range (D.torusPoints K)) := by
    simpa only [MonoidHom.coe_range] using D.weylSubgroup_le_normalizer_range_torusPoints K
  apply le_antisymm
  · rintro g ⟨hgE, hgN⟩
    obtain ⟨w, hw, _⟩ := D.existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup K hgE
    obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
    obtain ⟨⟨u, b⟩, hub, _⟩ := D.existsUnique_mul_mul_eq_of_mem_bruhatCell K n hw
    have hu1 : (u : D.points K) = 1 :=
      D.torus_conj_bruhat_eq_of_mem_normalizer K n u b hub hgN
    have hnb : (n : D.points K) * b = g := by simpa [hu1] using hub
    have hbN : (b : D.points K) ∈ Subgroup.normalizer (Set.range (D.torusPoints K)) := by
      have heq : (b : D.points K) = (n : D.points K)⁻¹ * g := eq_inv_mul_of_mul_eq hnb
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hW n.property)) hgN
    have hbT : (b : D.points K) ∈ (D.torusPoints K).range := by
      rw [← D.borelSubgroup_inf_normalizer_range_torusPoints K]
      exact ⟨b.property, hbN⟩
    obtain ⟨s, hs⟩ := hbT
    rw [← hnb, ← hs]
    exact (D.weylSubgroup K).mul_mem n.property (D.torusPoints_mem_weylSubgroup K s)
  · exact le_inf (D.weylSubgroup_le_extendedElementarySubgroup K) hW

/-- **Torus centralizer in the extended elementary Chevalley group.** Over an infinite field,
the actual character-lattice torus is self-centralizing inside
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem extendedElementarySubgroup_inf_centralizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      (D.torusPoints K).range := by
  apply le_antisymm
  · rintro g ⟨hgE, hgC⟩
    have hgN : g ∈ Subgroup.normalizer (Set.range (D.torusPoints K)) :=
      Subgroup.centralizer_le_normalizer _ hgC
    have hgW : g ∈ D.weylSubgroup K := by
      rw [← D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]
      exact ⟨hgE, hgN⟩
    have hproj1 : D.weylProjection K ⟨g, hgW⟩ = 1 := by
      rw [D.weylProjection_eq_one_iff K]
      intro s
      have hc : Commute g (D.torusPoints K (D.fullWeightTorusRestriction K s)) :=
        (Subgroup.mem_centralizer_iff.mp hgC _ ⟨_, rfl⟩).symm
      simpa only [Subgroup.coe_subtype, D.coe_torusPoints, ← D.kostantTorusMatrix_weight,
        kostantTorusMatrix_apply] using hc.map (D.points K).subtype
    exact (D.weylProjection_eq_one_iff_mem_range_torusPoints K ⟨g, hgW⟩).mp hproj1
  · refine le_inf ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact D.torusPoints_mem_extendedElementarySubgroup K s
    · simpa only [MonoidHom.coe_range] using Subgroup.le_centralizer (D.torusPoints K).range

end

end TauCeti.DynkinType.ChevalleyDatum
