/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Coroot
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Gauss

/-!
# Gauss factorization at every Chevalley root

For a Chevalley datum, opposite root elements can be collected in either order whenever
`u = 1 + r * s` is a unit. The resulting three factors are an opposite root element, the
coroot value at `u` or `u⁻¹`, and a root element. These are the rank-one coordinate changes used in
big-cell calculations. The formulas hold over every commutative ring, including nonreduced
rings; neither root parameter needs to be a unit.

The middle factor is evaluated in the datum's actual character-lattice torus, by restricting
the full-weight coroot parameter. No surjectivity of this restriction, generation of all
scheme points, or simply connectedness of the datum is assumed.

Over an infinite field `K`, Gauss factorization together with opposite-root separation implies the
rank-one normalizer criterion (`mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`):
if `x_β(c) * x_{-β}(-d) * x_β(c)` with `c ∈ K` and `d ∈ Kˣ` normalizes the actual torus, then
`c * d = 1`.

The proof applies the integral Kostant Gauss identity
`kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f` to the named Chevalley root vectors
and the chosen root's Killing coroot. Admissibility and the integral coroot coordinates come
from `kostantForm_chevalleySystem_coroot_apply_mem` and
`apply_ι_coroot_rootEquiv_of_isCartanWeightVector`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20, and Chapter 5.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct Multiplicative
open LieAlgebra LieAlgebra.IsKilling
open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (α : Fin t.numRoots) (A : Type v) [CommRing A]

/-- Opposite root elements admit a Gauss factorization if `1 + r * s` is a unit.
The coroot is evaluated in the actual torus of the datum, even for a proper weight lattice. -/
theorem rootSubgroupPoints_mul_opposite_eq_gauss (r s : A) (u : Aˣ)
    (hu : (u : A) = 1 + r * s) :
    D.rootSubgroupPoints α A (ofAdd r) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A (ofAdd s) =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A
          (ofAdd (s * ↑u⁻¹)) *
        D.torusPoints A (D.fullWeightTorusRestriction A
          (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot α i)) *
        D.rootSubgroupPoints α A (ofAdd (r * ↑u⁻¹)) := by
  -- Use a single Cartan generator, the chosen coroot, in the integral Gauss identity.
  let H : Unit → t.lieAlgebra ht := fun _ =>
    ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
      (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)
  let W : Fin D.dim → Unit → ℤ := fun j _ =>
    ∑ i, (t.simplyConnectedRootDatum ht).coroot α i * D.weight j i
  let hM := fun z hz w hw => kostantForm_chevalleySystem_coroot_apply_mem
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator α (u := z) hz (v := w) hw
  have hw j : IsCartanWeightVector H D.representation (W j) (D.basis j : D) := by
    rw [isCartanWeightVector_iff]
    exact fun _ => apply_ι_coroot_rootEquiv_of_isCartanWeightVector D.representation
      (D.isCartanWeightVector_basis j) α
  have hT := (t.isSl2Triple_chevalleySystem ht α).map
    (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))
    (fun hz => (t.isSl2Triple_chevalleySystem ht α).h_ne_zero
      (D.injective_representation_ι (by simpa using hz)))
  have hpos : ∀ j, ⁅H j, t.chevalleySystem ht α⁆ = ((fun _ : Unit => 2) j : ℚ) •
      t.chevalleySystem ht α := fun _ => (t.isSl2Triple_chevalleySystem ht α).lie_h_e_smul ℚ
  have hneg : ∀ j, ⁅H j, t.chevalleySystem ht
      ((t.simplyConnectedRootDatum ht).reflectionPerm α α)⁆ =
      -(((fun _ : Unit => 2) j : ℚ) • t.chevalleySystem ht
        ((t.simplyConnectedRootDatum ht).reflectionPerm α α)) := fun _ =>
    (t.isSl2Triple_chevalleySystem ht α).lie_lie_smul_f ℚ
  have hg := kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f
    (t.chevalleySystem ht) H D.representation D.lattice hM
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator α)
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator _)
    D.basis W hw (c := ()) hT hpos hneg (CommAlgCat.of ℤ A) r s u hu
  -- Identify the re-presented root maps and coroot action before taking matrices.
  have hx (γ : Fin t.numRoots) (a : Multiplicative A) :
      kostantRootSubgroupParam (t.chevalleySystem ht) H D.representation D.lattice hM γ
        (isNilpotent_apply_ι_chevalleySystem D.representation
          D.isNilpotent_representation_rootGenerator γ) (CommAlgCat.of ℤ A) a =
      chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A) a := by
    refine Units.ext (LinearMap.ext fun z => ?_)
    rw [kostantRootSubgroupParam_val_apply, chevalleyRootSubgroup_val]
  have htorus : kostantCoordinateCocharacter D.lattice D.basis W (CommAlgCat.of ℤ A) () u =
      kostantTorusPoints D.lattice D.basis D.weight (CommAlgCat.of ℤ A)
        (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot α i) := by
    refine Units.ext (Module.Basis.ext (D.basis.baseChange A) fun j => ?_)
    simp only [Module.Basis.baseChange_apply, kostantCoordinateCocharacter_tmul_basis,
      kostantTorusPoints_tmul_basis, W, torusCharacter_def, ← zpow_mul,
      Finset.prod_zpow_eq_zpow_sum]
  rw [hx, hx, hx, hx, htorus] at hg
  have hm := congrArg (fun g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice) =>
    Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom g) hg
  apply Subtype.ext
  simpa only [map_mul, Subgroup.coe_mul, coe_rootSubgroupPoints, coe_torusPoints,
    MulEquiv.toMonoidHom_eq_coe, ← kostantTorusMatrix_weight,
    basisMatrix_kostantTorusPoints] using hm

/-- The reverse-order Gauss factorization has the inverse coroot in the middle.
Only `1 + r * s`, rather than either additive root parameter, must be invertible. -/
theorem opposite_mul_rootSubgroupPoints_eq_gauss (r s : A) (u : Aˣ)
    (hu : (u : A) = 1 + r * s) :
    D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A (ofAdd s) *
        D.rootSubgroupPoints α A (ofAdd r) =
      D.rootSubgroupPoints α A (ofAdd (r * ↑u⁻¹)) *
        D.torusPoints A (D.fullWeightTorusRestriction A
          (fun i => u⁻¹ ^ (t.simplyConnectedRootDatum ht).coroot α i)) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A
          (ofAdd (s * ↑u⁻¹)) := by
  have h := congrArg Inv.inv (D.rootSubgroupPoints_mul_opposite_eq_gauss α A (-r) (-s) u
    (by simpa only [neg_mul_neg] using hu))
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, Pi.inv_def,
    ← zpow_neg, inv_zpow, mul_assoc] using h

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
  let β' := (t.simplyConnectedRootDatum ht).reflectionPerm β β
  let h : Fin t.rank → Kˣ :=
    D.fullWeightTorusRestriction K (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot β i)
  let a : K := -(d : K) * ((u⁻¹ : Kˣ) : K)
  let b : K := c * ((u⁻¹ : Kˣ) : K) + c
  let w := D.rootSubgroupPoints β K (ofAdd c) *
    D.rootSubgroupPoints β' K (ofAdd (-(d : K))) *
    D.rootSubgroupPoints β K (ofAdd c)
  have ha : a ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero d)) (Units.ne_zero u⁻¹)
  have hw : w = D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
      D.rootSubgroupPoints β K (ofAdd b) := by
    have hg := D.rootSubgroupPoints_mul_opposite_eq_gauss β K c (-(d : K)) u
      (by simp only [u, Units.val_mk0]; ring)
    dsimp only [w, a, b, h, β']
    rw [hg, mul_assoc, mul_assoc, ← map_mul, ← ofAdd_add, mul_assoc]
  obtain ⟨s, hs⟩ : ∃ s : Fin t.rank → Kˣ, torusCharacter s (D.coordinateRoot β) ≠ 1 := by
    by_contra hall; push Not at hall
    exact D.coordinateRoot_ne_zero β <| weightChar_injective (K := K) <|
      MonoidHom.ext fun s => by simpa only [weightChar_apply, torusCharacter_zero] using hall s
  obtain ⟨s', hs'⟩ : w * D.torusPoints K s * w⁻¹ ∈ (D.torusPoints K).range :=
    ((Subgroup.mem_normalizer_iff.mp hnorm) (D.torusPoints K s)).mp ⟨s, rfl⟩
  have hR : D.rootSubgroupPoints β K (ofAdd b) * D.torusPoints K s =
      D.torusPoints K s * D.rootSubgroupPoints β K
        (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) := by
    have hc := D.torusPoints_conj_rootSubgroupPoints β K s⁻¹ b
    have hinv : torusCharacter s⁻¹ (D.coordinateRoot β) =
        (torusCharacter s (D.coordinateRoot β))⁻¹ := by
      simp only [torusCharacter_def, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]
    rw [map_inv, inv_inv, hinv] at hc; rw [← hc]; group
  have hL : D.torusPoints K s' * D.rootSubgroupPoints β' K (ofAdd a) =
      D.rootSubgroupPoints β' K (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) *
        D.torusPoints K s' := by
    have hc := D.torusPoints_conj_rootSubgroupPoints β' K s' a
    rw [D.coordinateRoot_reflectionPerm_self β, torusCharacter_neg] at hc; rw [← hc]; group
  have hfac :
      D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K (h * s) *
          D.rootSubgroupPoints β K
            (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) =
        D.rootSubgroupPoints β' K
            (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) *
          D.torusPoints K (s' * h) * D.rootSubgroupPoints β K (ofAdd b) := by
    have hcomm : w * D.torusPoints K s = D.torusPoints K s' * w := by rw [hs']; group
    rw [hw] at hcomm
    have h1 : D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
        (D.rootSubgroupPoints β K (ofAdd b) * D.torusPoints K s) =
        D.torusPoints K s' * D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
          D.rootSubgroupPoints β K (ofAdd b) := by simpa only [mul_assoc] using hcomm
    rw [hR, hL] at h1; simpa only [map_mul, mul_assoc] using h1
  obtain ⟨hx', ht, _⟩ := D.eq_of_opposite_mul_torus_mul_eq K β hfac
  have hs'_char : torusCharacter s' (D.coordinateRoot β) = 1 := by
    have haeq : a = ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a :=
      ofAdd.injective (D.rootSubgroupPoints_injective β' K hx')
    have h1 : ((1 : K) - ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ)) * a = 0 := by
      rw [sub_mul, one_mul, ← haeq, sub_self]
    exact inv_eq_one.mp <| Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right ha)).symm
  have hss' : s' = s := by
    have hm : h * s = s' * h := D.torusPoints_injective K ht
    exact mul_right_cancel (hm.symm.trans (mul_comm h s))
  exact hs (hss' ▸ hs'_char)

end

end TauCeti.DynkinType.ChevalleyDatum
