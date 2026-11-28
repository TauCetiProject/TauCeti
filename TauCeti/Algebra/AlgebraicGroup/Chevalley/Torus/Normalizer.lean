/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Uniqueness
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Gauss
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.ClosedImmersion
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient

/-!
# Torus centralizer and normalizer in the extended elementary Chevalley group

Over any infinite field `K`, inside `D.extendedElementarySubgroup K`, the normalizer of the
actual character-lattice torus `T(K)` is precisely the Weyl subgroup `D.weylSubgroup K`, and
its centralizer is `T(K)` itself.

The `[Infinite K]` hypothesis ensures that torus characters separate distinct roots from `0` (in
contrast to the field-independent Borel normalizer and centre computations). These `@[simp]`
intersection theorems provide direct normalizer and centralizer reductions for `T(K)` in
subgroup, Weyl-quotient, and structure arguments over infinite fields.

In addition, over any infinite field `K`, uniqueness of opposite-root–torus–root factorizations
(`ChevalleyDatum.eq_and_eq_and_eq_of_opposite_mul_torus_mul_eq`) forces any element in
opposite-root–torus–root form normalizing the actual torus to have trivial outer factors
(`ChevalleyDatum.eq_zero_of_opposite_mul_torus_mul_mem_normalizer`). Combined with Gauss
factorization, this yields the rank-one normalizer criterion
(`ChevalleyDatum.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`): if
`x_β(c) * x_{-β}(-d) * x_β(c)` with `c ∈ K` and `d ∈ Kˣ` normalizes the actual torus, then
`c * d = 1`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.extendedElementarySubgroup_inf_normalizer_range_torusPoints`:
  over an infinite field, `D.extendedElementarySubgroup K ∩ N(T(K)) = D.weylSubgroup K`.
* `TauCeti.DynkinType.ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_range_torusPoints`:
  over an infinite field, `D.extendedElementarySubgroup K ∩ C(T(K)) = T(K)`.
* `TauCeti.DynkinType.ChevalleyDatum.eq_zero_of_opposite_mul_torus_mul_mem_normalizer`: a
  normalizer element in opposite-root–torus–root form over an infinite field has zero outer
  parameters.
* `ChevalleyDatum.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`:
  rank-one normalizer criterion over an infinite field.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemma 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.1–7.2.
-/

public section

open Multiplicative TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section BruhatNormalizer

variable (K : Type v) [Field K]

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

-- Combine the sharp Bruhat normal form (`u * n * b`) with torus invariance of `U_w(K)` and
-- self-normalization of `T(K)` in `B(K)` (`borelSubgroup_inf_normalizer_range_torusPoints`).
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

end BruhatNormalizer

/-! ## Rank-one normalizer criterion -/

/-- Over an infinite field, any element in opposite-root–torus–root form normalizing the actual
torus has trivial outer root parameters. -/
theorem eq_zero_of_opposite_mul_torus_mul_mem_normalizer
    {K : Type v} [Field K] [Infinite K] (β : Fin t.numRoots) (a b : K) (h : Fin t.rank → Kˣ)
    (hnorm : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) K (ofAdd a) *
        D.torusPoints K h * D.rootSubgroupPoints β K (ofAdd b) ∈
      Subgroup.normalizer (D.torusPoints K).range) :
    a = 0 ∧ b = 0 := by
  let β' := (t.simplyConnectedRootDatum ht).reflectionPerm β β
  let w := D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
    D.rootSubgroupPoints β K (ofAdd b)
  -- Pick a torus point `s` where `β(s) ≠ 1`.
  obtain ⟨s, hs⟩ := D.exists_torusCharacter_coordinateRoot_ne_one (K := K) β
  obtain ⟨s', hs'⟩ : w * D.torusPoints K s * w⁻¹ ∈ (D.torusPoints K).range :=
    ((Subgroup.mem_normalizer_iff.mp hnorm) (D.torusPoints K s)).mp ⟨s, rfl⟩
  -- Commute `T s` left past `x_β(b)` and `T s'` right past `x_{-β}(a)` to equate factorizations.
  have hR : D.rootSubgroupPoints β K (ofAdd b) * D.torusPoints K s =
      D.torusPoints K s * D.rootSubgroupPoints β K
        (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) := by
    have hc := D.torusPoints_conj_rootSubgroupPoints β K s⁻¹ b
    have hinv : torusCharacter s⁻¹ (D.coordinateRoot β) =
        (torusCharacter s (D.coordinateRoot β))⁻¹ := by
      rw [← weightChar_apply, map_inv, weightChar_apply]
    rw [map_inv, inv_inv, hinv] at hc
    rw [← hc]
    group
  have hL : D.torusPoints K s' * D.rootSubgroupPoints β' K (ofAdd a) =
      D.rootSubgroupPoints β' K (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) *
        D.torusPoints K s' := by
    have hc := D.torusPoints_conj_rootSubgroupPoints β' K s' a
    rw [D.coordinateRoot_reflectionPerm_self β, torusCharacter_neg] at hc
    rw [← hc]
    group
  have hfac :
      D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K (h * s) *
          D.rootSubgroupPoints β K
            (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) =
        D.rootSubgroupPoints β' K
            (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) *
          D.torusPoints K (s' * h) * D.rootSubgroupPoints β K (ofAdd b) := by
    have hcomm : w * D.torusPoints K s = D.torusPoints K s' * w := by rw [hs']; group
    have h1 : D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
        (D.rootSubgroupPoints β K (ofAdd b) * D.torusPoints K s) =
        D.torusPoints K s' * D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
          D.rootSubgroupPoints β K (ofAdd b) := by
      simpa only [w, mul_assoc] using hcomm
    rw [hR, hL] at h1
    simpa only [map_mul, mul_assoc] using h1
  -- Uniqueness of the opposite-root–torus–root factorization forces `s' = s` and kills `a, b`.
  obtain ⟨hx', ht, hy'⟩ := D.eq_and_eq_and_eq_of_opposite_mul_torus_mul_eq β hfac
  have hss' : s' = s := by
    have hm : h * s = s' * h := D.torusPoints_injective K ht
    exact mul_right_cancel (hm.symm.trans (mul_comm h s))
  rw [hss'] at hx'
  have cancel_of_ne {γ : Fin t.numRoots} {x : K}
      (heq : D.rootSubgroupPoints γ K (ofAdd x) =
        D.rootSubgroupPoints γ K (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * x))) :
      x = 0 := by
    by_contra hx0
    have hxe : x = ((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * x :=
      ofAdd.injective ((D.rootSubgroupPoints_inj γ K).mp heq)
    have h1 : ((1 : K) - ((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ)) * x = 0 := by
      rw [sub_mul, one_mul, ← hxe, sub_self]
    exact hs <| inv_eq_one.mp <| Units.ext
      (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hx0)).symm
  exact ⟨cancel_of_ne hx', cancel_of_ne hy'.symm⟩

/-- **Rank-one normalizer lemma.** If `x_β(c) * x_{-β}(-d) * x_β(c)` with `c : K` and `d : Kˣ`
over an infinite field normalizes the actual torus, then `c * (d : K) = 1`. -/
theorem mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer
    {K : Type v} [Field K] [Infinite K] (β : Fin t.numRoots) (c : K) (d : Kˣ)
    (hnorm : D.rootSubgroupPoints β K (ofAdd c) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) K
          (ofAdd (-(d : K))) *
        D.rootSubgroupPoints β K (ofAdd c) ∈
      Subgroup.normalizer (D.torusPoints K).range) :
    c * (d : K) = 1 := by
  by_contra hcd
  have h1cd : (1 : K) - c * (d : K) ≠ 0 := sub_ne_zero.mpr fun heq => hcd heq.symm
  let u : Kˣ := Units.mk0 (1 - c * (d : K)) h1cd
  have hg := D.rootSubgroupPoints_mul_opposite_eq_gauss β K c (-(d : K)) u
    (by simp only [u, Units.val_mk0]; ring)
  have hw : D.rootSubgroupPoints β K (ofAdd c) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) K
          (ofAdd (-(d : K))) *
        D.rootSubgroupPoints β K (ofAdd c) =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) K
          (ofAdd (-(d : K) * ((u⁻¹ : Kˣ) : K))) *
        D.torusPoints K (D.fullWeightTorusRestriction K
          (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot β i)) *
        D.rootSubgroupPoints β K (ofAdd (c * ((u⁻¹ : Kˣ) : K) + c)) := by
    rw [hg, mul_assoc, mul_assoc, ← map_mul, ← ofAdd_add, mul_assoc]
  have ha := (D.eq_zero_of_opposite_mul_torus_mul_mem_normalizer β _ _ _ (hw ▸ hnorm)).1
  exact mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero d)) (Units.ne_zero u⁻¹) ha

end

end TauCeti.DynkinType.ChevalleyDatum
