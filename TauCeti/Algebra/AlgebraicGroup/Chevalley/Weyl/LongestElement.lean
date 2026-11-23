/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
public import TauCeti.LinearAlgebra.RootSystem.LongestElement
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import Mathlib.Tactic.Group

/-!
# Longest Weyl-element conjugation of unipotent and Borel subgroups

For a Chevalley datum `D` over a field `K`, any Weyl lift `n₀` of the longest Weyl element
`w₀` swaps the positive and negative unipotent subgroups `D.positivePoints K` and
`D.negativePoints K` under conjugation. Consequently the Borel subgroup `D.borelSubgroup K` and
its conjugate `n₀ D.borelSubgroup K n₀⁻¹` meet precisely in the actual character-lattice torus
`(D.torusPoints K).range`.

## Main results

* `ChevalleyDatum.map_positivePoints_conj_longestElement`: `n₀ U⁺(K) n₀⁻¹ = U⁻(K)`.
* `ChevalleyDatum.map_negativePoints_conj_longestElement`: `n₀ U⁻(K) n₀⁻¹ = U⁺(K)`.
* `ChevalleyDatum.borelSubgroup_inf_map_borelSubgroup_conj_longestElement`:
  `B(K) ∩ n₀ B(K) n₀⁻¹ = T(K)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2 and §8.4.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-- Conjugation by a Weyl lift of the longest element sends the positive unipotent subgroup onto
the negative unipotent subgroup. -/
@[simp]
theorem map_positivePoints_conj_longestElement (n₀ : D.weylSubgroup K)
    (hn₀ : D.weylProjection K n₀ =
      let _ := t.isReduced_simplyConnectedRootDatum ht
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)) :
    (D.positivePoints K).map (MulAut.conj (n₀ : D.points K) : D.points K →* D.points K) =
      D.negativePoints K := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  rw [D.positivePoints_def, D.negativePoints_def, ← MulEquiv.toMonoidHom_eq_coe,
    D.map_subsystemPoints_conj K n₀, hn₀, t.posRoots_rationalRootSystem ht,
    t.negRoots_rationalRootSystem ht, image_weylGroupToPerm_longestElement_posRoots]

/-- Conjugation by a Weyl lift of the longest element sends the negative unipotent subgroup onto
the positive unipotent subgroup. -/
@[simp]
theorem map_negativePoints_conj_longestElement (n₀ : D.weylSubgroup K)
    (hn₀ : D.weylProjection K n₀ =
      let _ := t.isReduced_simplyConnectedRootDatum ht
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)) :
    (D.negativePoints K).map (MulAut.conj (n₀ : D.points K) : D.points K →* D.points K) =
      D.positivePoints K := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  rw [D.negativePoints_def, D.positivePoints_def, ← MulEquiv.toMonoidHom_eq_coe,
    D.map_subsystemPoints_conj K n₀, hn₀, t.posRoots_rationalRootSystem ht,
    t.negRoots_rationalRootSystem ht, image_weylGroupToPerm_longestElement_negRoots]

/-- For any Weyl lift `n₀` of the longest element over a field `K`, the Borel subgroup and its
conjugate `n₀ B(K) n₀⁻¹` meet in the actual character-lattice torus `(D.torusPoints K).range`. -/
theorem borelSubgroup_inf_map_borelSubgroup_conj_longestElement (n₀ : D.weylSubgroup K)
    (hn₀ : D.weylProjection K n₀ =
      let _ := t.isReduced_simplyConnectedRootDatum ht
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)) :
    D.borelSubgroup K ⊓
        (D.borelSubgroup K).map (MulAut.conj (n₀ : D.points K)).toMonoidHom =
      (D.torusPoints K).range := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  have hn₀_inv : D.weylProjection K n₀⁻¹ =
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) := by
    rw [map_inv, hn₀, longestElement_inv]
  apply le_antisymm
  · rintro g ⟨hgB, hgConj⟩
    obtain ⟨u, huU, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hgB
    have hconj_g : (n₀ : D.points K)⁻¹ * (u * D.torusPoints K s) * (n₀ : D.points K) ∈
        D.borelSubgroup K := by
      obtain ⟨b, hb, hbeq⟩ := hgConj
      have hsub : (n₀ : D.points K)⁻¹ * (u * D.torusPoints K s) * (n₀ : D.points K) = b := by
        rw [← hbeq]
        simp [MulAut.conj_apply, mul_assoc]
      rwa [hsub]
    have hconj_t : (n₀ : D.points K)⁻¹ * D.torusPoints K s * (n₀ : D.points K) ∈
        (D.torusPoints K).range :=
      (Subgroup.mem_normalizer_iff''.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K n₀.property)
        (D.torusPoints K s)).mp ⟨s, rfl⟩
    have hu'B : (n₀ : D.points K)⁻¹ * u * (n₀ : D.points K) ∈ D.borelSubgroup K := by
      have hu'_eq : (n₀ : D.points K)⁻¹ * u * (n₀ : D.points K) =
          ((n₀ : D.points K)⁻¹ * (u * D.torusPoints K s) * (n₀ : D.points K)) *
            ((n₀ : D.points K)⁻¹ * D.torusPoints K s * (n₀ : D.points K))⁻¹ := by
        group
      rw [hu'_eq]
      exact (D.borelSubgroup K).mul_mem hconj_g
        ((D.borelSubgroup K).inv_mem (D.range_torusPoints_le_borelSubgroup K hconj_t))
    have hu'N : (n₀ : D.points K)⁻¹ * u * (n₀ : D.points K) ∈ D.negativePoints K := by
      rw [← D.map_positivePoints_conj_longestElement K n₀⁻¹ hn₀_inv]
      exact ⟨u, huU, rfl⟩
    have hu'1 : (n₀ : D.points K)⁻¹ * u * (n₀ : D.points K) = 1 := by
      rw [← Subgroup.mem_bot, ← D.negativePoints_inf_borelSubgroup_eq_bot K]
      exact ⟨hu'N, hu'B⟩
    have hu1 : u = 1 := by
      simpa [mul_assoc] using congrArg (fun x => (n₀ : D.points K) * x * (n₀ : D.points K)⁻¹) hu'1
    simp [hu1]
  · refine le_inf (D.range_torusPoints_le_borelSubgroup K) ?_
    rintro _ ⟨s, rfl⟩
    refine ⟨(n₀ : D.points K)⁻¹ * D.torusPoints K s * (n₀ : D.points K), ?_, ?_⟩
    · exact D.range_torusPoints_le_borelSubgroup K
        ((Subgroup.mem_normalizer_iff''.mp
          (D.weylSubgroup_le_normalizer_range_torusPoints K n₀.property)
          (D.torusPoints K s)).mp ⟨s, rfl⟩)
    · simp [MulAut.conj_apply, mul_assoc]

end TauCeti.DynkinType.ChevalleyDatum
