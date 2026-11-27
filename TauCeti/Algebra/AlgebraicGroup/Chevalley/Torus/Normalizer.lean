/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Gauss
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Uniqueness
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective

/-!
# The rank-one normalizer criterion

Over an infinite field `K`, uniqueness of opposite-root–torus–root factorizations
(`ChevalleyDatum.eq_and_eq_and_eq_of_opposite_mul_torus_mul_eq`) forces any element in
opposite-root–torus–root form normalizing the actual torus to have trivial outer factors
(`ChevalleyDatum.eq_zero_of_opposite_mul_torus_mul_mem_normalizer`). Combined with Gauss
factorization, this yields the rank-one normalizer criterion
(`ChevalleyDatum.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`): if
`x_β(c) * x_{-β}(-d) * x_β(c)` with `c ∈ K` and `d ∈ Kˣ` normalizes the actual torus, then
`c * d = 1`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.eq_zero_of_opposite_mul_torus_mul_mem_normalizer`: a
  normalizer element in opposite-root–torus–root form over an infinite field has zero outer
  parameters.
* `ChevalleyDatum.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`:
  rank-one normalizer criterion over an infinite field.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative

universe v

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

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
