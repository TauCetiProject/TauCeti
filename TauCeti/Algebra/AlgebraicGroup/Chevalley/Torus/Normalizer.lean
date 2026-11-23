/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Gauss
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective

/-!
# Opposite-root–torus–root uniqueness and the rank-one normalizer criterion

Over any commutative ring, the opposite-intersection identities for the positive and negative
unipotent subgroups imply uniqueness of opposite-root–torus–root factorizations
(`ChevalleyDatum.eq_of_opposite_mul_torus_mul_eq`).

Over an infinite field `K`, any element in opposite-root–torus–root form normalizing the actual
torus must have trivial outer factors
(`ChevalleyDatum.eq_zero_of_opposite_mul_torus_mul_mem_normalizer`). Combined with Gauss
factorization, this yields the rank-one normalizer criterion
(`ChevalleyDatum.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`): if
`x_β(c) * x_{-β}(-d) * x_β(c)` with `c ∈ K` and `d ∈ Kˣ` normalizes the actual torus, then
`c * d = 1`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.eq_of_opposite_mul_torus_mul_eq`: uniqueness of
  opposite-root–torus–root factorizations over any commutative ring.
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
open TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

private theorem opposite_eq_torus_mul_toLinearEquiv {β : Fin t.numRoots} {u v : Multiplicative A}
    {r₁ r₂ : Fin t.rank → Aˣ}
    (h : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u =
      D.torusPoints A r₁ * D.rootSubgroupPoints β A v * D.torusPoints A r₂) :
    chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator
        ((t.simplyConnectedRootDatum ht).reflectionPerm β β) (CommAlgCat.of ℤ A) u =
      kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A) r₁ *
        chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator β (CommAlgCat.of ℤ A) v *
        kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A) r₂ :=
  Units.map_injective (f := (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom)
    (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).injective <| by
    simpa only [MulEquiv.toMonoidHom_eq_coe, map_mul, D.coe_rootSubgroupPoints,
      D.coe_torusPoints, Subgroup.coe_mul, basisMatrix_kostantTorusPoints,
      kostantTorusMatrix_apply] using congrArg Subtype.val h

private theorem rootSubgroupPoints_eq_one_of_opposite_eq_torus_mul (β : Fin t.numRoots)
    (u v : Multiplicative A) (r₁ r₂ : Fin t.rank → Aˣ)
    (h : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u =
      D.torusPoints A r₁ * D.rootSubgroupPoints β A v * D.torusPoints A r₂) :
    D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u = 1 ∧
      D.rootSubgroupPoints β A v = 1 ∧
      D.torusPoints A (r₁ * r₂) = 1 := by
  let β' := (t.simplyConnectedRootDatum ht).reflectionPerm β β
  let m := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  let x := chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator β' (CommAlgCat.of ℤ A) u
  let y := chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator β (CommAlgCat.of ℤ A) v
  let t₁ := kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A) r₁
  let t₂ := kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A) r₂
  have hxy : x = t₁ * y * t₂ := D.opposite_eq_torus_mul_toLinearEquiv A h
  let T := (kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A)).range
  have hsolve {U V : Subgroup _} (hUV : U ⊓ (V ⊔ T) = ⊥) (hVU : V ⊓ (U ⊔ T) = ⊥)
      (hxU : x ∈ U) (hyV : y ∈ V) : x = 1 ∧ y = 1 := by
    have hx1 : x = 1 := Subgroup.mem_bot.mp <| hUV ▸ ⟨hxU, hxy ▸ Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨r₁, rfl⟩) (Subgroup.mem_sup_left hyV))
      (Subgroup.mem_sup_right ⟨r₂, rfl⟩)⟩
    have hy_eq : y = t₁⁻¹ * t₂⁻¹ := by
      rw [hx1] at hxy; calc
        y = t₁⁻¹ * (t₁ * y * t₂) * t₂⁻¹ := by group
        _ = t₁⁻¹ * 1 * t₂⁻¹ := by rw [← hxy]
        _ = _ := by group
    exact ⟨hx1, Subgroup.mem_bot.mp <| hVU ▸ ⟨hyV, hy_eq ▸ Subgroup.mul_mem _
      (Subgroup.mem_sup_right (T.inv_mem ⟨r₁, rfl⟩))
      (Subgroup.mem_sup_right (T.inv_mem ⟨r₂, rfl⟩))⟩⟩
  have hxy1 : x = 1 ∧ y = 1 := by
    rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) β
      with hβ | hβ
    · exact hsolve
        (D.negativeSubgroup_inf_positiveSubgroup_sup_range_kostantTorusPoints_eq_bot A)
        (D.positiveSubgroup_inf_negativeSubgroup_sup_range_kostantTorusPoints_eq_bot A)
        (D.chevalleyRootSubgroup_mem_negativeSubgroup (CommAlgCat.of ℤ A)
          (by dsimp only [β']; rw [← t.reflectionPerm_rationalRootSystem ht]
              exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hβ) u)
        (D.chevalleyRootSubgroup_mem_positiveSubgroup (CommAlgCat.of ℤ A) hβ v)
    · exact hsolve
        (D.positiveSubgroup_inf_negativeSubgroup_sup_range_kostantTorusPoints_eq_bot A)
        (D.negativeSubgroup_inf_positiveSubgroup_sup_range_kostantTorusPoints_eq_bot A)
        (D.chevalleyRootSubgroup_mem_positiveSubgroup (CommAlgCat.of ℤ A)
          (by dsimp only [β']; rw [← t.reflectionPerm_rationalRootSystem ht]
              exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hβ) u)
        (D.chevalleyRootSubgroup_mem_negativeSubgroup (CommAlgCat.of ℤ A) hβ v)
  have hux : D.rootSubgroupPoints β' A u = 1 :=
    Subtype.ext ((D.coe_rootSubgroupPoints β' A u).trans ((congrArg m hxy1.1).trans m.map_one))
  have hvy : D.rootSubgroupPoints β A v = 1 :=
    Subtype.ext ((D.coe_rootSubgroupPoints β A v).trans ((congrArg m hxy1.2).trans m.map_one))
  exact ⟨hux, hvy, by rw [map_mul]; simpa only [β', hux, hvy, mul_one] using h.symm⟩

/-- **Uniqueness of opposite-root–torus–root factorizations** over any commutative ring. -/
theorem eq_of_opposite_mul_torus_mul_eq (β : Fin t.numRoots)
    {u₁ u₂ v₁ v₂ : Multiplicative A} {r₁ r₂ : Fin t.rank → Aˣ}
    (h : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u₁ *
        D.torusPoints A r₁ * D.rootSubgroupPoints β A v₁ =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u₂ *
        D.torusPoints A r₂ * D.rootSubgroupPoints β A v₂) :
    D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u₁ =
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u₂ ∧
      D.torusPoints A r₁ = D.torusPoints A r₂ ∧
      D.rootSubgroupPoints β A v₁ = D.rootSubgroupPoints β A v₂ := by
  let β' := (t.simplyConnectedRootDatum ht).reflectionPerm β β
  have hsep : D.rootSubgroupPoints β' A (u₂⁻¹ * u₁) =
      D.torusPoints A r₂ * D.rootSubgroupPoints β A (v₂ * v₁⁻¹) * D.torusPoints A r₁⁻¹ := by
    calc
      D.rootSubgroupPoints β' A (u₂⁻¹ * u₁)
          = (D.rootSubgroupPoints β' A u₂)⁻¹ *
              (D.rootSubgroupPoints β' A u₁ * D.torusPoints A r₁ * D.rootSubgroupPoints β A v₁) *
              ((D.rootSubgroupPoints β A v₁)⁻¹ * (D.torusPoints A r₁)⁻¹) := by
            rw [map_mul, map_inv]; group
      _ = _ := by dsimp only [β']; rw [h, map_mul, map_inv, map_inv]; group
  obtain ⟨hu, hv, ht⟩ := D.rootSubgroupPoints_eq_one_of_opposite_eq_torus_mul A β _ _ _ _ hsep
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, map_inv] at hu; exact (inv_mul_eq_one.mp hu).symm
  · rw [map_mul, map_inv] at ht; exact (mul_inv_eq_one.mp ht).symm
  · rw [map_mul, map_inv] at hv; exact (mul_inv_eq_one.mp hv).symm

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
  obtain ⟨s, hs⟩ : ∃ s : Fin t.rank → Kˣ, torusCharacter s (D.coordinateRoot β) ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_torusCharacter_ne (K := K) (D.coordinateRoot_ne_zero β)
    exact ⟨s, by simpa only [torusCharacter_zero] using hs⟩
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
  obtain ⟨hx', ht, hy'⟩ := D.eq_of_opposite_mul_torus_mul_eq K β hfac
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
      ofAdd.injective (D.rootSubgroupPoints_injective γ K heq)
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
