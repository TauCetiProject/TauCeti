/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Restricting an endomorphism to the fixed subgroup of a power

For a group endomorphism `F` and a positive integer `n`, `F` induces an automorphism
of the subgroup fixed by `F ^ n`. Its inverse is induced by `F ^ (n - 1)` and its
`n`th power is the identity. No invertibility of `F` on the ambient group is needed.

The fixed subgroup of this restricted automorphism is canonically the fixed subgroup of `F`.
In particular, a Steinberg map whose power is a Frobenius can be treated as an automorphism
of the Frobenius-fixed group, with the same fixed subgroup. The bijectivity argument reuses
Mathlib's `Function.bijOn_ptsOfPeriod`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

private theorem mem_fixedSubgroup_pow_iff (F : Monoid.End G) (n : ℕ) (x : G) :
    x ∈ fixedSubgroup (F ^ n) ↔ Function.IsPeriodicPt F n x := by
  rfl

private def fixedSubgroupPowEnd (F : Monoid.End G) (n : ℕ) :
    Monoid.End ↥(fixedSubgroup (F ^ n)) where
  toFun x := ⟨F x, (mem_fixedSubgroup_pow_iff F n _).mpr
    ((mem_fixedSubgroup_pow_iff F n _).mp x.property).apply⟩
  map_one' := Subtype.ext (map_one F)
  map_mul' x y := Subtype.ext (map_mul F (x : G) (y : G))

private theorem fixedSubgroupPowEnd_bijective (F : Monoid.End G) {n : ℕ} (hn : 0 < n) :
    Function.Bijective (fixedSubgroupPowEnd F n) := by
  have h := Function.bijOn_ptsOfPeriod (F : G → G) hn
  constructor
  · intro x y hxy
    exact Subtype.ext (h.injOn
      ((mem_fixedSubgroup_pow_iff F n _).mp x.property)
      ((mem_fixedSubgroup_pow_iff F n _).mp y.property) (congrArg Subtype.val hxy))
  · intro y
    obtain ⟨x, hx, hxy⟩ := h.surjOn ((mem_fixedSubgroup_pow_iff F n _).mp y.property)
    exact ⟨⟨x, (mem_fixedSubgroup_pow_iff F n _).mpr hx⟩, Subtype.ext hxy⟩

/-- An endomorphism is an automorphism on the fixed subgroup of each positive power. -/
noncomputable def fixedSubgroupPowAut (F : Monoid.End G) {n : ℕ} (hn : 0 < n) :
    MulAut ↥(fixedSubgroup (F ^ n)) :=
  MulEquiv.ofBijective (fixedSubgroupPowEnd F n) (fixedSubgroupPowEnd_bijective F hn)

@[simp]
theorem coe_fixedSubgroupPowAut_apply (F : Monoid.End G) {n : ℕ} (hn : 0 < n)
    (x : ↥(fixedSubgroup (F ^ n))) : (fixedSubgroupPowAut F hn x : G) = F x := by
  rfl

/-- Powers of the restricted automorphism are the corresponding iterates of the ambient map. -/
@[simp]
theorem coe_fixedSubgroupPowAut_pow_apply (F : Monoid.End G) {n : ℕ} (hn : 0 < n)
    (m : ℕ) (x : ↥(fixedSubgroup (F ^ n))) :
    ((fixedSubgroupPowAut F hn ^ m) x : G) = (F ^ m) (x : G) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, coe_fixedSubgroupPowAut_apply, ih,
      pow_succ', Monoid.End.coe_mul, Function.comp_apply]

/-- The restricted automorphism has period dividing the specified exponent. -/
@[simp]
theorem fixedSubgroupPowAut_pow (F : Monoid.End G) {n : ℕ} (hn : 0 < n) :
    fixedSubgroupPowAut F hn ^ n = 1 := by
  ext x
  exact (coe_fixedSubgroupPowAut_pow_apply F hn n x).trans x.property

/-- The inverse restriction is the preceding iterate; positivity is essential here. -/
@[simp]
theorem coe_fixedSubgroupPowAut_symm_apply (F : Monoid.End G) {n : ℕ} (hn : 0 < n)
    (x : ↥(fixedSubgroup (F ^ n))) :
    ((fixedSubgroupPowAut F hn).symm x : G) = (F ^ (n - 1)) (x : G) := by
  have h : (fixedSubgroupPowAut F hn)⁻¹ = fixedSubgroupPowAut F hn ^ (n - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, fixedSubgroupPowAut_pow]
  rw [← MulAut.inv_def, h, coe_fixedSubgroupPowAut_pow_apply]

/-- Forgetting the larger periodic subgroup sends the restricted fixed subgroup onto `G^F`. -/
@[simp]
theorem map_subtype_fixedSubgroupPowAut (F : Monoid.End G) {n : ℕ} (hn : 0 < n) :
    (fixedSubgroup ↑(fixedSubgroupPowAut F hn)).map
      (fixedSubgroup (F ^ n)).subtype = fixedSubgroup F := by
  rw [map_subtype_fixedSubgroup_of_coe_eq _ F (coe_fixedSubgroupPowAut_apply F hn)]
  exact inf_eq_right.mpr (fixedSubgroup_le_fixedSubgroup_pow F n)

/-- The fixed subgroup is unchanged when the endomorphism is restricted to the fixed subgroup
of a positive power. -/
noncomputable def fixedSubgroupPowFixedEquiv (F : Monoid.End G) {n : ℕ} (hn : 0 < n) :
    ↥(fixedSubgroup (G := ↥(fixedSubgroup (F ^ n))) ↑(fixedSubgroupPowAut F hn)) ≃*
      ↥(fixedSubgroup F) :=
  ((fixedSubgroup ↑(fixedSubgroupPowAut F hn)).equivMapOfInjective
    (fixedSubgroup (F ^ n)).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_fixedSubgroupPowAut F hn))

@[simp]
theorem coe_fixedSubgroupPowFixedEquiv_apply (F : Monoid.End G) {n : ℕ} (hn : 0 < n)
    (x : ↥(fixedSubgroup (G := ↥(fixedSubgroup (F ^ n))) ↑(fixedSubgroupPowAut F hn))) :
    (fixedSubgroupPowFixedEquiv F hn x : G) = (x : ↥(fixedSubgroup (F ^ n))) := by
  rfl

end TauCeti
