/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Valuation.Extension
import TauCeti.RingTheory.Valuation.LinearIndependent

/-!
# The value-group ramification index of a valuation on an algebra

Let `w` be a valuation on an algebra `L` over a commutative ring `K`. Restricting `w` along
`algebraMap K L` produces a valuation on `K` whose value group
`(w.comap (algebraMap K L)).valueGroup` is a subgroup of `w.valueGroup`. This file defines the
value-group ramification index

`w.ramificationIdx K : ℕ`

as the relative index of `(w.comap (algebraMap K L)).valueGroup` in `w.valueGroup`. No valuation on
`K` and no discreteness hypothesis is needed in the definition: the index depends only on `K` and
on the equivalence class of `w`, and multiplies in towers.

When `K` is a field and `L` is a `K`-algebra, elements of `L` whose nonzero values represent
distinct cosets of `(w.comap (algebraMap K L)).valueGroup` in `w.valueGroup` are linearly
independent over `K`. Consequently, when `L` is a finite division-ring extension of `K`, the
value-group ramification index is finite, positive, and bounded above by `Module.finrank K L`.

## Main definitions

* `Valuation.ramificationIdx`: the relative index `[Γ_w : Γ_{w|_K}]` of the restricted value group
  in the value group of `w`.

## Main results

* `Valuation.valueGroup_comap_le`: restricting a valuation along a ring homomorphism shrinks its
  value group.
* `Valuation.ramificationIdx_eq_one_iff`, `Valuation.ramificationIdx_ne_zero_iff`, and
  `Valuation.ramificationIdx_pos`: characterizations of `w.ramificationIdx K = 1`, `≠ 0`, and
  positivity under finite relative index.
* `Valuation.IsEquiv.ramificationIdx_eq`: equivalent valuations on `L` have the same ramification
  index over `K`.
* `Valuation.ramificationIdx_comap_mul_ramificationIdx` and `Valuation.ramificationIdx_tower`:
  multiplicativity of the ramification index in an algebra tower.
* `Valuation.linearIndependent_of_quotient_valueGroup`: elements of `L` with valuations in distinct
  cosets of the base value group are linearly independent over `K`.
* `Valuation.isFiniteRelIndex_valueGroup_comap` and `Valuation.ramificationIdx_le_finrank`: for a
  finite division-ring extension, the value-group index is finite and at most `[L : K]`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II,
  Proposition 6.8.
* N. Bourbaki, *Commutative Algebra*, Chapter VI, §8.
-/

public section

open MonoidWithZeroHom

namespace Valuation

section MonoidWithZero

variable {R S K L M Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]

/-- Restricting a valuation along a ring homomorphism shrinks its value monoid. -/
theorem valueMonoid_comap_le [Ring R] [Ring S] (w : Valuation S Γ) (f : R →+* S) :
    (w.comap f).valueMonoid ≤ w.valueMonoid := by
  intro γ hγ
  rw [mem_valueMonoid_iff, Set.mem_preimage, Set.mem_range] at hγ ⊢
  obtain ⟨r, hr⟩ := hγ
  rw [coe_toMonoidWithZeroHom, comap_apply] at hr
  exact ⟨f r, by rw [coe_toMonoidWithZeroHom, hr]⟩

/-- Restricting a valuation along a ring homomorphism shrinks its value group. -/
theorem valueGroup_comap_le [Ring R] [Ring S] (w : Valuation S Γ) (f : R →+* S) :
    (w.comap f).valueGroup ≤ w.valueGroup :=
  Subgroup.closure_mono (w.valueMonoid_comap_le f)

/-- Restricting a valuation along a surjective ring homomorphism preserves its value group. -/
theorem valueGroup_comap_eq_of_surjective [Ring R] [Ring S] (w : Valuation S Γ) {f : R →+* S}
    (hf : Function.Surjective f) : (w.comap f).valueGroup = w.valueGroup := by
  refine le_antisymm (w.valueGroup_comap_le f) (Subgroup.closure_mono fun γ hγ ↦ ?_)
  rw [SetLike.mem_coe, mem_valueMonoid_iff, Set.mem_preimage, Set.mem_range] at hγ ⊢
  obtain ⟨s, hs⟩ := hγ
  obtain ⟨r, rfl⟩ := hf s
  rw [coe_toMonoidWithZeroHom] at hs
  exact ⟨r, by rw [coe_toMonoidWithZeroHom, comap_apply, hs]⟩

/-- The **value-group ramification index** `[Γ_w : Γ_{w|_K}]` of a valuation `w` on a `K`-algebra
`L`: the relative index of the value group of `w` restricted to `K` in the value group of `w`. It
equals `0` by convention when that index is infinite. -/
noncomputable def ramificationIdx {L : Type*} [Ring L]
    (w : Valuation L Γ) (K : Type*) [CommRing K] [Algebra K L] : ℕ :=
  ((w.comap (algebraMap K L)).valueGroup).relIndex w.valueGroup

/-- The defining formula of `Valuation.ramificationIdx`. -/
theorem ramificationIdx_def [CommRing K] [Ring L] [Algebra K L] (w : Valuation L Γ) :
    w.ramificationIdx K = ((w.comap (algebraMap K L)).valueGroup).relIndex w.valueGroup :=
  (rfl)

/-- The value-group ramification index equals `1` if and only if restricting `w` to `K` has the
same value group as `w`. -/
theorem ramificationIdx_eq_one_iff [CommRing K] [Ring L] [Algebra K L] (w : Valuation L Γ) :
    w.ramificationIdx K = 1 ↔ (w.comap (algebraMap K L)).valueGroup = w.valueGroup := by
  rw [ramificationIdx_def, Subgroup.relIndex_eq_one]
  exact ⟨fun h ↦ le_antisymm (w.valueGroup_comap_le (algebraMap K L)) h, fun h ↦ h.ge⟩

/-- The value-group ramification index is nonzero if and only if the restricted value group has
finite relative index in `w.valueGroup`. -/
theorem ramificationIdx_ne_zero_iff [CommRing K] [Ring L] [Algebra K L] (w : Valuation L Γ) :
    w.ramificationIdx K ≠ 0 ↔
      ((w.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w.valueGroup :=
  Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.symm

/-- Whenever the restricted value group has finite relative index in `w.valueGroup`, the
value-group ramification index is positive. -/
theorem ramificationIdx_pos [CommRing K] [Ring L] [Algebra K L] (w : Valuation L Γ)
    [((w.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w.valueGroup] :
    0 < w.ramificationIdx K :=
  Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero

/-- A valuation has ramification index `1` over its own ring. -/
@[simp]
theorem ramificationIdx_self [CommRing K] (w : Valuation K Γ) : w.ramificationIdx K = 1 := by
  simp [ramificationIdx_def]

/-- When `algebraMap K L` is surjective, every valuation on `L` has ramification index `1` over
`K`. -/
theorem ramificationIdx_eq_one_of_surjective [CommRing K] [Ring L] [Algebra K L]
    (w : Valuation L Γ) (h : Function.Surjective (algebraMap K L)) :
    w.ramificationIdx K = 1 := by
  rw [ramificationIdx_eq_one_iff, w.valueGroup_comap_eq_of_surjective h]

/-- Pulling back a valuation along a surjective `K`-algebra homomorphism preserves its ramification
index over `K`. -/
theorem ramificationIdx_comap_of_surjective [CommRing K] [Ring L] [Ring M] [Algebra K L]
    [Algebra K M] (w : Valuation M Γ) {f : L →+* M} (hf : Function.Surjective f)
    (hcomp : f.comp (algebraMap K L) = algebraMap K M) :
    (w.comap f).ramificationIdx K = w.ramificationIdx K := by
  rw [ramificationIdx_def, ramificationIdx_def, ← comap_comp, hcomp,
    w.valueGroup_comap_eq_of_surjective hf]

/-- Pulling back a valuation along a `K`-algebra equivalence preserves its ramification index over
`K`. -/
@[simp]
theorem ramificationIdx_comap_algEquiv [CommRing K] [Ring L] [Ring M] [Algebra K L] [Algebra K M]
    (w : Valuation M Γ) (e : L ≃ₐ[K] M) :
    (w.comap (e : L →+* M)).ramificationIdx K = w.ramificationIdx K :=
  w.ramificationIdx_comap_of_surjective e.surjective e.toAlgHom.comp_algebraMap

/-- **Multiplicativity of the value-group ramification index in a tower**, written via restriction
to the intermediate algebra. -/
theorem ramificationIdx_comap_mul_ramificationIdx [CommRing K] [CommRing L] [Ring M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] (w : Valuation M Γ) :
    (w.comap (algebraMap L M)).ramificationIdx K * w.ramificationIdx L = w.ramificationIdx K := by
  have hcomp : w.comap (algebraMap K M) = (w.comap (algebraMap L M)).comap (algebraMap K L) := by
    rw [IsScalarTower.algebraMap_eq K L M, comap_comp]
  rw [ramificationIdx_def, ramificationIdx_def, ramificationIdx_def, hcomp]
  exact Subgroup.relIndex_mul_relIndex _ _ _
    ((w.comap (algebraMap L M)).valueGroup_comap_le (algebraMap K L))
    (w.valueGroup_comap_le (algebraMap L M))

end MonoidWithZero

section GroupWithZero

variable {R K L M Γ₁ Γ₂ : Type*}
  [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]

private theorem val_valueGroup_mk_comap [Ring R] [Ring L] (w : Valuation L Γ₁) (f : R →+* L)
    {r s : R} (hr : (w.comap f : R →*₀ Γ₁) r ≠ 0) (hs : (w.comap f : R →*₀ Γ₁) s ≠ 0)
    (hr' : (w : L →*₀ Γ₁) (f r) ≠ 0) (hs' : (w : L →*₀ Γ₁) (f s) ≠ 0) :
    (valueGroup.mk (w.comap f : R →*₀ Γ₁) r s hr hs : Γ₁ˣ) =
      (valueGroup.mk (w : L →*₀ Γ₁) (f r) (f s) hr' hs' : Γ₁ˣ) := by
  apply Units.ext
  rw [valueGroup.mk_eq_div, valueGroup.mk_eq_div, coe_toMonoidWithZeroHom,
    coe_toMonoidWithZeroHom, comap_apply, comap_apply]

private theorem map_orderMonoidIso_subgroupOf_valueGroup_comap_le [Ring R] [Ring L]
    {w₁ : Valuation L Γ₁} {w₂ : Valuation L Γ₂} (h : w₁.IsEquiv w₂) (f : R →+* L) :
    Subgroup.map (h.orderMonoidIso.toMulEquiv : w₁.valueGroup →* w₂.valueGroup)
        (((w₁.comap f).valueGroup).subgroupOf w₁.valueGroup) ≤
      ((w₂.comap f).valueGroup).subgroupOf w₂.valueGroup := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hγ
  rw [Subgroup.mem_subgroupOf]
  obtain ⟨r, s, hr, hs, hmk⟩ := (mem_valueGroup_iff_exists_mk_of_comm (w₁.comap f : R →*₀ Γ₁)).mp hγ
  have hrL : w₁ (f r) ≠ 0 := by simpa only [coe_toMonoidWithZeroHom, comap_apply] using hr
  have hsL : w₁ (f s) ≠ 0 := by simpa only [coe_toMonoidWithZeroHom, comap_apply] using hs
  have hγ' : γ = valueGroup.mk (w₁ : L →*₀ Γ₁) (f r) (f s) hrL hsL :=
    Subtype.ext (hmk.trans (val_valueGroup_mk_comap w₁ f hr hs
      (by simpa only [coe_toMonoidWithZeroHom] using hrL)
      (by simpa only [coe_toMonoidWithZeroHom] using hsL)))
  have hmap : (h.orderMonoidIso.toMulEquiv : w₁.valueGroup →* w₂.valueGroup) γ =
      valueGroup.mk (w₂ : L →*₀ Γ₂) (f r) (f s) (h.eq_zero.ne.mp hrL) (h.eq_zero.ne.mp hsL) := by
    rw [hγ']
    exact h.orderMonoidIso_spec hrL hsL
  rw [hmap]
  have hr₂ : (w₂.comap f : R →*₀ Γ₂) r ≠ 0 := by
    simpa only [coe_toMonoidWithZeroHom, comap_apply] using h.eq_zero.ne.mp hrL
  have hs₂ : (w₂.comap f : R →*₀ Γ₂) s ≠ 0 := by
    simpa only [coe_toMonoidWithZeroHom, comap_apply] using h.eq_zero.ne.mp hsL
  exact (mem_valueGroup_iff_exists_mk_of_comm (w₂.comap f : R →*₀ Γ₂)).mpr
    ⟨r, s, hr₂, hs₂, (val_valueGroup_mk_comap w₂ f hr₂ hs₂
      (by simpa only [coe_toMonoidWithZeroHom] using h.eq_zero.ne.mp hrL)
      (by simpa only [coe_toMonoidWithZeroHom] using h.eq_zero.ne.mp hsL)).symm⟩

/-- The value-group isomorphism induced by an equivalence of valuations carries the restricted
value subgroup of a ring homomorphism to the corresponding restricted value subgroup. -/
theorem IsEquiv.map_orderMonoidIso_subgroupOf_valueGroup_comap [Ring R] [Ring L]
    {w₁ : Valuation L Γ₁} {w₂ : Valuation L Γ₂} (h : w₁.IsEquiv w₂) (f : R →+* L) :
    Subgroup.map (h.orderMonoidIso.toMulEquiv : w₁.valueGroup →* w₂.valueGroup)
        (((w₁.comap f).valueGroup).subgroupOf w₁.valueGroup) =
      ((w₂.comap f).valueGroup).subgroupOf w₂.valueGroup := by
  refine le_antisymm (map_orderMonoidIso_subgroupOf_valueGroup_comap_le h f) ?_
  rintro γ hγ
  refine ⟨h.orderMonoidIso.symm γ, ?_, h.orderMonoidIso.apply_symm_apply γ⟩
  exact map_orderMonoidIso_subgroupOf_valueGroup_comap_le h.symm f ⟨γ, hγ, rfl⟩

/-- **Equivalent valuations have the same value-group ramification index.** -/
theorem IsEquiv.ramificationIdx_eq [CommRing K] [Ring L] [Algebra K L]
    {w₁ : Valuation L Γ₁} {w₂ : Valuation L Γ₂} (h : w₁.IsEquiv w₂) :
    w₁.ramificationIdx K = w₂.ramificationIdx K := by
  rw [ramificationIdx_def, ramificationIdx_def, Subgroup.relIndex, Subgroup.relIndex,
    ← h.map_orderMonoidIso_subgroupOf_valueGroup_comap (algebraMap K L)]
  exact (Subgroup.index_map_equiv _ h.orderMonoidIso.toMulEquiv).symm

/-- Equivalent valuations agree on whether the restricted value group has finite relative index. -/
theorem IsEquiv.isFiniteRelIndex_valueGroup_comap_iff [CommRing K] [Ring L] [Algebra K L]
    {w₁ : Valuation L Γ₁} {w₂ : Valuation L Γ₂} (h : w₁.IsEquiv w₂) :
    ((w₁.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w₁.valueGroup ↔
      ((w₂.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w₂.valueGroup := by
  simp only [← ramificationIdx_ne_zero_iff, h.ramificationIdx_eq]

/-- **Multiplicativity of the value-group ramification index in a tower** `M/L/K`, when the
valuation `w` on `M` extends a valuation `v` on `L`. No valuation on `K` is needed. -/
theorem ramificationIdx_tower
    (K : Type*) {L M : Type*} [CommRing K] [CommRing L] [Ring M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (v : Valuation L Γ₁) (w : Valuation M Γ₂) [v.HasExtension w] :
    w.ramificationIdx K = v.ramificationIdx K * w.ramificationIdx L := by
  rw [← w.ramificationIdx_comap_mul_ramificationIdx (K := K) (L := L),
    (HasExtension.val_isEquiv_comap (vR := v) (vA := w)).ramificationIdx_eq]

end GroupWithZero

section FieldBase

variable {K L Γ : Type*} [Field K] [Ring L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

/-- **Elements with valuations in distinct cosets of the base value group are linearly
independent.** Let `w` be a valuation on an algebra `L` over a field `K`. If `e i ∈ L` has nonzero
valuation `g i` and the classes of `g i` modulo the value group of `w|_K` are pairwise distinct,
then `e` is linearly independent over `K`. -/
theorem linearIndependent_of_quotient_valueGroup {ι : Type*} {e : ι → L} {g : ι → w.valueGroup}
    (hg : ∀ i, w (e i) = ((g i : Γˣ) : Γ))
    (hinj : Function.Injective fun i ↦
      QuotientGroup.mk
        (s := ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup) (g i)) :
    LinearIndependent K e := by
  refine w.linearIndependent_of_map_smul_ne (fun i a ha ↦ ?_) fun i j hij a b ha hb heq ↦ ?_
  · rw [Algebra.smul_def, map_mul, hg]
    exact mul_ne_zero ((ha.isUnit.map (algebraMap K L)).map w).ne_zero (Units.ne_zero _)
  · have hwa : w (algebraMap K L a) ≠ 0 := ((ha.isUnit.map (algebraMap K L)).map w).ne_zero
    have hwb : w (algebraMap K L b) ≠ 0 := ((hb.isUnit.map (algebraMap K L)).map w).ne_zero
    let ua : Γˣ := Units.mk0 (w (algebraMap K L a)) hwa
    let ub : Γˣ := Units.mk0 (w (algebraMap K L b)) hwb
    have hua : ua ∈ (w.comap (algebraMap K L)).valueGroup :=
      mem_valueGroup _ ⟨a, by rw [coe_toMonoidWithZeroHom, comap_apply, Units.val_mk0]⟩
    have hub : ub ∈ (w.comap (algebraMap K L)).valueGroup :=
      mem_valueGroup _ ⟨b, by rw [coe_toMonoidWithZeroHom, comap_apply, Units.val_mk0]⟩
    have hu : ua * (g i : Γˣ) = ub * (g j : Γˣ) := by
      apply Units.ext
      simpa [ua, ub, Algebra.smul_def, map_mul, hg] using heq
    have hquot : ((g i)⁻¹ * g j : w.valueGroup) ∈
        ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup := by
      rw [Subgroup.mem_subgroupOf]
      have hrel : ((g i : Γˣ))⁻¹ * (g j : Γˣ) = ua * ub⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, mul_comm (g i : Γˣ) ua, hu, mul_right_comm,
          mul_inv_cancel, one_mul]
      simpa [hrel] using mul_mem hua (inv_mem hub)
    exact hij (hinj (QuotientGroup.eq.mpr hquot))

end FieldBase

section DivisionRing

variable {K L Γ : Type*} [Field K] [DivisionRing L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

/-- Choosing one element of `L` in each coset of the base value group produces a `K`-linearly
independent family indexed by the value-group quotient. -/
private theorem exists_linearIndependent_quotient_valueGroup :
    ∃ e : (w.valueGroup ⧸ ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup) → L,
      LinearIndependent K e := by
  classical
  set H := ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup
  let g : (w.valueGroup ⧸ H) → w.valueGroup := Quotient.out
  have hex (q : w.valueGroup ⧸ H) : ∃ y : L, w y = ((g q : Γˣ) : Γ) := by
    have hmem : (g q : Γˣ) ∈ w.valueMonoid := by
      rw [valueMonoid_eq_valueGroup]
      exact (g q).2
    rw [mem_valueMonoid_iff, Set.mem_preimage, Set.mem_range] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, by rwa [coe_toMonoidWithZeroHom] at hy⟩
  refine ⟨fun q ↦ (hex q).choose,
    w.linearIndependent_of_quotient_valueGroup (fun q ↦ (hex q).choose_spec) fun q₁ q₂ hq ↦ ?_⟩
  simpa [g] using hq

section Finite

variable [Module.Finite K L]

/-- **Finiteness of the value-group index in a finite extension.** For any valuation `w` on a
division ring `L` finite over a field `K`, the restricted value group has finite relative index in
`w.valueGroup`. -/
instance isFiniteRelIndex_valueGroup_comap :
    ((w.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w.valueGroup := by
  obtain ⟨e, he⟩ := w.exists_linearIndependent_quotient_valueGroup (K := K)
  have hfin : Finite
      (w.valueGroup ⧸ ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup) :=
    he.finite
  exact ⟨Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩⟩

/-- **The value-group ramification index is at most the degree**: `[Γ_w : Γ_{w|_K}] ≤ [L : K]`. -/
theorem ramificationIdx_le_finrank : w.ramificationIdx K ≤ Module.finrank K L := by
  obtain ⟨e, he⟩ := w.exists_linearIndependent_quotient_valueGroup (K := K)
  have hfin : Finite
      (w.valueGroup ⧸ ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup) :=
    he.finite
  let _ := Fintype.ofFinite
    (w.valueGroup ⧸ ((w.comap (algebraMap K L)).valueGroup).subgroupOf w.valueGroup)
  rw [ramificationIdx_def, Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact he.fintype_card_le_finrank

end Finite

end DivisionRing

end Valuation
