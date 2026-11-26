/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.HalfCharacteristic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij

/-!
# The discriminant group and overlattices of the norm-parity kernel

For an odd unimodular lattice `L` with characteristic vector `w`, `L.evenSublattice` has index two,
`(L_even)ᵛ = L + ℤ · (w / 2)`, `Nat.card A_(L_even) = 4`, and `A_(L_even)` is `ℤ/4` (odd rank) or
`ℤ/2 × ℤ/2` (even rank). For any nondegenerate integral lattice `L` with characteristic vector `w`
satisfying `8 ∣ w²`, gluing `L.evenSublattice` along `⟨[w / 2]⟩` or `⟨[e] + [w / 2]⟩` produces the
even overlattices `halfCharacteristicOverlattice` (`L_even + ℤ · (w / 2)`) and
`shiftedHalfCharacteristicOverlattice` (`L_even + ℤ · (e + w / 2)`). When `L` is odd, each is a
Kneser two-neighbor of `L`; when `L` is odd and unimodular, these two lattices exhaust all even
Kneser two-neighbors of `L`.

Basic definitions of `halfCharacteristicClass` and `latticeVectorClass` live in
`TauCeti.LinearAlgebra.IntegralLattice.Characteristic.HalfCharacteristic`, and the mod-2
characteristic-norm congruence derived from `vanDerBlij` lives in
`TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §1.4 and §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II and Appendix 4.
* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- For an odd unimodular lattice, `A_(L_even)` has order four. -/
theorem natCard_evenSublattice_discriminantGroup (hLu : L.IsUnimodular) (hL : ¬ L.IsEven) :
    Nat.card L.evenSublattice.DiscriminantGroup = 4 := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  rw [L.evenSublattice.natCard_discriminantGroup, L.discriminant_evenSublattice_of_not_isEven hL,
    L.isUnimodular_iff_discriminant_eq_one.mp hLu, mul_one]

private theorem dvd_integralNorm_add_two_smul_iff {d : ℤ} (hd : d ∣ 8) {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    d ∣ L.integralNorm (w + (2 : ℤ) • e) ↔ d ∣ L.integralNorm w :=
  ((hw.integralNorm_add_two_smul_modEq e).of_dvd hd).dvd_iff

private theorem sub_mem_evenSublattice_of_odd {u e : L} (hu : Odd (L.integralNorm u))
    (he : Odd (L.integralNorm e)) : ((u - e : L) : V) ∈ L.evenSublattice.carrier :=
  (L.mem_evenSublattice_carrier_iff (u - e)).mpr
    (by rw [L.integralNorm_sub]; exact (hu.add_odd he).sub (even_two_mul _))

/-- Half of a characteristic vector cannot lie in an odd lattice. -/
theorem half_characteristic_notMem_carrier_of_not_isEven {w : L}
    (hw : L.IsCharacteristicVector w) (hL : ¬ L.IsEven) : (1 / 2 : ℚ) • (w : V) ∉ L.carrier :=
  fun hm ↦ hL (L.isEven_iff_isCharacteristicVector_zero.mpr
    ((L.isCharacteristicVector_add_two_smul_iff 0 ⟨(1 / 2 : ℚ) • (w : V), hm⟩).mp
      ((Subtype.ext (by simp [← Int.cast_smul_eq_zsmul ℚ]) :
        w = 0 + (2 : ℤ) • ⟨(1 / 2 : ℚ) • (w : V), hm⟩) ▸ hw)))

/-- In a unimodular lattice, `(1 / 2) • w` lies in the carrier iff the lattice is even. -/
theorem half_characteristic_mem_carrier_iff (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) : (1 / 2 : ℚ) • (w : V) ∈ L.carrier ↔ L.IsEven := by
  refine ⟨fun hm ↦ by_contra fun hL ↦ L.half_characteristic_notMem_carrier_of_not_isEven hw hL hm,
    fun hLe ↦ ?_⟩
  obtain ⟨v, hv⟩ := hLu.exists_characteristicVector_sub_eq_two_smul hw
    (L.isEven_iff_isCharacteristicVector_zero.mp hLe)
  have hv' : (1 / 2 : ℚ) • (w : V) = (v : V) := by
    simpa [← Int.cast_smul_eq_zsmul ℚ] using congrArg (fun z : L ↦ (1 / 2 : ℚ) • (z : V)) hv
  exact hv' ▸ v.property

private theorem isCharacteristicVector_of_even_on_evenNorm {u y₀ : L}
    (hu_even : ∀ z : L, Even (L.integralNorm z) → Even (L.integralForm u z))
    (hy₀ : Odd (L.integralForm u y₀)) : L.IsCharacteristicVector u := by
  have hy₀p : L.normParity y₀ = 1 := by
    rw [normParity_apply, ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    exact fun h ↦ Int.not_even_iff_odd.mpr hy₀ (hu_even y₀ h)
  rw [L.isCharacteristicVector_iff_forall_integralForm_eq_normParity]; intro y
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (L.normParity y) with hy0 | hy1
  · exact (ZMod.intCast_eq_zero_iff_even.mpr
      (hu_even y (ZMod.intCast_eq_zero_iff_even.mp (L.normParity_apply y ▸ hy0)))).trans hy0.symm
  · have hsum : Even (L.integralNorm (y + y₀)) := by
      rw [← ZMod.intCast_eq_zero_iff_even, ← L.normParity_apply, map_add, hy1, hy₀p]; decide
    have hform := ZMod.intCast_eq_zero_iff_even.mpr (hu_even (y + y₀) hsum)
    rw [map_add, Int.cast_add, ZMod.intCast_eq_one_iff_odd.mpr hy₀] at hform
    exact hy1.symm ▸ CharTwo.add_eq_zero.mp hform

/-- **Coset description of `(L_even)ᵛ` for unimodular `L`.** -/
theorem mem_evenSublattice_dualCarrier_iff (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (x : V) :
    x ∈ L.evenSublattice.dualCarrier ↔
      x ∈ L.carrier ∨ x - (1 / 2 : ℚ) • (w : V) ∈ L.carrier := by
  refine ⟨fun hx ↦ ?_, fun h ↦ h.elim (fun hx ↦ L.coe_mem_evenSublattice_dualCarrier ⟨x, hx⟩)
    fun hx ↦ sub_add_cancel x ((1 / 2 : ℚ) • (w : V)) ▸ L.evenSublattice.dualCarrier.add_mem
      (L.coe_mem_evenSublattice_dualCarrier ⟨_, hx⟩)
      (L.half_characteristic_mem_evenSublattice_dualCarrier hw)⟩
  have h2x : (2 : ℚ) • x ∈ L.carrier := by
    rw [L.isUnimodular_def.mp hLu, LinearMap.BilinForm.mem_dualSubmodule]; intro y hy
    simpa only [L.evenSublattice_form, map_smul, LinearMap.smul_apply] using
      hx _ (L.two_smul_mem_evenSublattice_carrier ⟨y, hy⟩)
  let u : L := ⟨(2 : ℚ) • x, h2x⟩
  have hu_even (z : L) (hz : Even (L.integralNorm z)) : Even (L.integralForm u z) := by
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hx z ((L.mem_evenSublattice_carrier_iff z).mpr hz))
    refine ⟨k, Int.cast_injective (α := ℚ) ?_⟩
    rw [L.integralForm_cast]
    simp only [u, map_smul, LinearMap.smul_apply, smul_eq_mul, L.evenSublattice_form] at hk ⊢
    rw [← hk, eq_intCast]; push_cast; ring
  by_cases hall : ∀ y : L, Even (L.integralForm u y)
  · left; rw [L.isUnimodular_def.mp hLu, LinearMap.BilinForm.mem_dualSubmodule]; intro y hy
    obtain ⟨k, hk⟩ := hall ⟨y, hy⟩; have hcast := L.integralForm_cast u ⟨y, hy⟩
    simp only [u, map_smul, LinearMap.smul_apply, smul_eq_mul, hk] at hcast
    exact Submodule.mem_one.mpr ⟨k, by rw [eq_intCast]; push_cast at hcast; linarith⟩
  · right; push Not at hall; obtain ⟨y₀, hy₀⟩ := hall
    obtain ⟨v, hv⟩ := hLu.exists_characteristicVector_sub_eq_two_smul
      (L.isCharacteristicVector_of_even_on_evenNorm hu_even hy₀) hw
    have hxv : x - (1 / 2 : ℚ) • (w : V) = (v : V) := by
      simpa [u, smul_sub, ← Int.cast_smul_eq_zsmul ℚ] using
        congrArg (fun z : L ↦ (1 / 2 : ℚ) • (z : V)) hv
    exact hxv ▸ v.property

/-- **Span description of `(L_even)ᵛ` for unimodular `L`:** `(L_even)ᵛ = L + ℤ · (w / 2)`. -/
theorem evenSublattice_dualCarrier_eq_sup_span_half_characteristic (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier = L.carrier ⊔ (ℤ ∙ ((1 / 2 : ℚ) • (w : V))) := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le (fun x hx ↦ L.coe_mem_evenSublattice_dualCarrier
    ⟨x, hx⟩) ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (L.half_characteristic_mem_evenSublattice_dualCarrier hw)))
  rcases (L.mem_evenSublattice_dualCarrier_iff hLu hw x).mp hx with hxL | hxL
  · exact Submodule.mem_sup_left hxL
  · exact sub_add_cancel x ((1 / 2 : ℚ) • (w : V)) ▸
      Submodule.add_mem_sup hxL (Submodule.mem_span_singleton_self _)

/-- In a unimodular lattice, `2 • [w / 2] = 0` in `A_(L_even)` iff the rank is even. -/
theorem two_nsmul_halfCharacteristicClass_eq_zero_iff_even_finrank (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    2 • L.halfCharacteristicClass hw = 0 ↔ Even (Module.finrank ℤ L) := by
  rw [L.two_nsmul_halfCharacteristicClass_eq_zero_iff_even_integralNorm hw,
    ← ZMod.intCast_eq_zero_iff_even, (ZMod.intCast_eq_intCast_iff _ _ 2).mpr
      (hLu.integralNorm_characteristicVector_modEq_finrank hw),
    Int.cast_natCast, ZMod.natCast_eq_zero_iff_even]

private theorem odd_integralNorm_of_odd_finrank (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w) :
    Odd (L.integralNorm w) := by
  rwa [← ZMod.intCast_eq_one_iff_odd, (ZMod.intCast_eq_intCast_iff _ _ 2).mpr
    (hLu.integralNorm_characteristicVector_modEq_finrank hw), Int.cast_natCast,
    ZMod.natCast_eq_one_iff_odd]

/-- In odd rank, `(2 : ℤ) • [w / 2]` is the unique nonzero class `[e]` of `L / L_even`. -/
theorem two_zsmul_halfCharacteristicClass_eq_latticeVectorClass (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w)
    {e : L} (he : Odd (L.integralNorm e)) :
    (2 : ℤ) • L.halfCharacteristicClass hw = L.latticeVectorClass e := by
  simpa [halfCharacteristicClass_def, latticeVectorClass_def,
    L.evenSublattice.zsmul_discriminantGroup_mk_eq_mk_iff] using
    L.sub_mem_evenSublattice_of_odd (L.odd_integralNorm_of_odd_finrank hLu hodd hw) he

/-- **Four-element exhaustion of `A_(L_even)`** for unimodular `L` with odd-norm `e ∈ L`. -/
theorem eq_zero_or_eq_latticeVectorClass_or_eq_halfCharacteristicClass_or_eq_add
    (hLu : L.IsUnimodular) {w : L} (hw : L.IsCharacteristicVector w)
    {e : L} (he : Odd (L.integralNorm e)) (x : L.evenSublattice.DiscriminantGroup) :
    x = 0 ∨ x = L.latticeVectorClass e ∨ x = L.halfCharacteristicClass hw ∨
      x = L.latticeVectorClass e + L.halfCharacteristicClass hw := by
  induction x using Submodule.Quotient.induction_on with | _ y =>
  rcases (L.mem_evenSublattice_dualCarrier_iff hLu hw y).mp y.property with hyL | hyL
  · rcases Int.even_or_odd (L.integralNorm ⟨y, hyL⟩) with hu | hu
    · exact Or.inl ((L.evenSublattice.discriminantGroup_mk_eq_zero_iff _).mpr
        ((L.mem_evenSublattice_carrier_iff ⟨y, hyL⟩).mpr hu))
    · rw [latticeVectorClass_def]; refine Or.inr (Or.inl
        ((L.evenSublattice.discriminantGroup_mk_eq_iff _ _).mpr ?_))
      simpa only [Submodule.coe_sub, coe_latticeVectorDual] using
        L.sub_mem_evenSublattice_of_odd hu he
  · let u : L := ⟨(y : V) - (1 / 2 : ℚ) • (w : V), hyL⟩
    rcases Int.even_or_odd (L.integralNorm u) with hu | hu
    · rw [halfCharacteristicClass_def]; refine Or.inr (Or.inr (Or.inl
        ((L.evenSublattice.discriminantGroup_mk_eq_iff _ _).mpr ?_)))
      simpa only [Submodule.coe_sub, coe_halfCharacteristicDual] using
        (L.mem_evenSublattice_carrier_iff u).mpr hu
    · rw [latticeVectorClass_def, halfCharacteristicClass_def, ← Submodule.Quotient.mk_add]
      refine Or.inr (Or.inr (Or.inr ((L.evenSublattice.discriminantGroup_mk_eq_iff _ _).mpr ?_)))
      rw [Submodule.coe_sub, Submodule.coe_add, coe_latticeVectorDual, coe_halfCharacteristicDual,
        ← sub_sub, sub_right_comm]
      exact L.sub_mem_evenSublattice_of_odd hu he

/-- **In odd rank, `A_(L_even) ≃+ ℤ/4`**, generated by `[w / 2]`. -/
noncomputable def zmodFourAddEquivEvenSublatticeDiscriminantGroup (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w) :
    ZMod 4 ≃+ L.evenSublattice.DiscriminantGroup := by
  have hw_odd := L.odd_integralNorm_of_odd_finrank hLu hodd hw
  refine zmodAddEquivOfGenerator (g := L.halfCharacteristicClass hw) (fun x ↦ ?_)
    (L.natCard_evenSublattice_discriminantGroup hLu (hLu.not_isEven_of_odd_finrank hodd))
  have h2 := L.two_zsmul_halfCharacteristicClass_eq_latticeVectorClass hLu hodd hw hw_odd
  rcases L.eq_zero_or_eq_latticeVectorClass_or_eq_halfCharacteristicClass_or_eq_add
      hLu hw hw_odd x with rfl | rfl | rfl | rfl
  exacts [⟨0, zero_zsmul _⟩, ⟨2, h2⟩, ⟨1, one_zsmul _⟩,
    ⟨2 + 1, (add_zsmul _ 2 1).trans (by rw [h2, one_zsmul])⟩]

/-- `zmodFourAddEquivEvenSublatticeDiscriminantGroup` sends `1` to `[w / 2]`. -/
@[simp] theorem zmodFourAddEquivEvenSublatticeDiscriminantGroup_apply_one (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w) :
    L.zmodFourAddEquivEvenSublatticeDiscriminantGroup hLu hodd hw 1 =
      L.halfCharacteristicClass hw := by
  rw [zmodFourAddEquivEvenSublatticeDiscriminantGroup]; exact zmodAddEquivOfGenerator_apply_one _ _

private noncomputable def evenSublatticeZModTwoHom (x : L.evenSublattice.DiscriminantGroup)
    (hx : (2 : ℤ) • x = 0) : ZMod 2 →+ L.evenSublattice.DiscriminantGroup :=
  ZMod.lift 2 ⟨zmultiplesHom _ x, by simpa using hx⟩

private theorem evenSublatticeZModTwoHom_one (x : L.evenSublattice.DiscriminantGroup)
    (hx : (2 : ℤ) • x = 0) : L.evenSublatticeZModTwoHom x hx 1 = x := by
  rw [evenSublatticeZModTwoHom, ← Int.cast_one, ZMod.lift_coe]; exact one_zsmul x

/-- **In even rank, `A_(L_even) ≃+ ℤ/2 × ℤ/2`** for odd unimodular `L`. -/
noncomputable def zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup (hLu : L.IsUnimodular)
    (heven : Even (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w)
    {e : L} (he : Odd (L.integralNorm e)) :
    ZMod 2 × ZMod 2 ≃+ L.evenSublattice.DiscriminantGroup := by
  have hw2 : (2 : ℤ) • L.halfCharacteristicClass hw = 0 := by
    rw [two_zsmul, ← two_nsmul]
    exact (L.two_nsmul_halfCharacteristicClass_eq_zero_iff_even_finrank hLu hw).mpr heven
  refine AddEquiv.ofBijective
    ((L.evenSublatticeZModTwoHom _ (L.two_zsmul_latticeVectorClass e)).coprod
      (L.evenSublatticeZModTwoHom _ hw2)) ?_
  rw [Nat.bijective_iff_surjective_and_card]
  refine ⟨fun g ↦ ?_, by simp [L.natCard_evenSublattice_discriminantGroup hLu
    (L.not_isEven_of_odd_integralNorm he)]⟩
  rcases L.eq_zero_or_eq_latticeVectorClass_or_eq_halfCharacteristicClass_or_eq_add
      hLu hw he g with rfl | rfl | rfl | rfl
  exacts [⟨(0, 0), by simp⟩, ⟨(1, 0), by simp [evenSublatticeZModTwoHom_one]⟩,
    ⟨(0, 1), by simp [evenSublatticeZModTwoHom_one]⟩,
    ⟨(1, 1), by simp [evenSublatticeZModTwoHom_one]⟩]

/-- `zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup` sends `(1, 0)` to `[e]`. -/
@[simp] theorem zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup_apply_one_zero
    (hLu : L.IsUnimodular) (heven : Even (Module.finrank ℤ L)) {w : L}
    (hw : L.IsCharacteristicVector w) {e : L} (he : Odd (L.integralNorm e)) :
    L.zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup hLu heven hw he (1, 0) =
      L.latticeVectorClass e := by
  simp [zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup, evenSublatticeZModTwoHom_one]

/-- `zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup` sends `(0, 1)` to `[w / 2]`. -/
@[simp] theorem zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup_apply_zero_one
    (hLu : L.IsUnimodular) (heven : Even (Module.finrank ℤ L)) {w : L}
    (hw : L.IsCharacteristicVector w) {e : L} (he : Odd (L.integralNorm e)) :
    L.zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup hLu heven hw he (0, 1) =
      L.halfCharacteristicClass hw := by
  simp [zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup, evenSublatticeZModTwoHom_one]

/-- The cyclic subgroup of `A_(L_even)` generated by `[w / 2]`. -/
noncomputable def halfCharacteristicSubgroup {w : L} (hw : L.IsCharacteristicVector w) :
    AddSubgroup L.evenSublattice.DiscriminantGroup :=
  AddSubgroup.zmultiples (L.halfCharacteristicClass hw)

/-- The cyclic subgroup of `A_(L_even)` generated by `[e] + [w / 2]`. -/
noncomputable def shiftedHalfCharacteristicSubgroup {w : L} (hw : L.IsCharacteristicVector w)
    (e : L) : AddSubgroup L.evenSublattice.DiscriminantGroup :=
  AddSubgroup.zmultiples (L.latticeVectorClass e + L.halfCharacteristicClass hw)

/-- Shifting `w` by `2 • e` identifies `shiftedHalfCharacteristicSubgroup` with
`halfCharacteristicSubgroup` at `w + 2 • e`. -/
theorem shiftedHalfCharacteristicSubgroup_eq_halfCharacteristicSubgroup {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    L.shiftedHalfCharacteristicSubgroup hw e =
      L.halfCharacteristicSubgroup (hw.add_two_smul e) :=
  congrArg AddSubgroup.zmultiples (L.halfCharacteristicClass_add_two_smul hw e).symm

/-- The subgroup of `A_(L_even)` attached to `L` itself is generated by any odd-norm vector. -/
theorem discriminantSubgroup_toIntermediateCarrier_eq_zmultiples_latticeVectorClass
    {e : L} (he : Odd (L.integralNorm e)) :
    L.evenSublattice.discriminantSubgroup
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) =
      AddSubgroup.zmultiples (L.latticeVectorClass e) := by
  ext x; rw [AddSubgroup.mem_zmultiples_iff_of_two_nsmul_eq_zero (L.two_nsmul_latticeVectorClass e)]
  induction x using Submodule.Quotient.induction_on with | _ y =>
  rw [L.evenSublattice.mk_mem_discriminantSubgroup_iff, coe_toIntermediateCarrier,
    L.evenSublattice.discriminantGroup_mk_eq_zero_iff, latticeVectorClass_def,
    L.evenSublattice.discriminantGroup_mk_eq_iff]
  exact ⟨fun hy ↦ (Int.even_or_odd (L.integralNorm ⟨y, hy⟩)).imp
    (L.mem_evenSublattice_carrier_iff ⟨y, hy⟩).mpr (fun h ↦ by
      simpa only [Submodule.coe_sub, coe_latticeVectorDual] using
        L.sub_mem_evenSublattice_of_odd h he),
    fun h ↦ h.elim (fun hy0 ↦ L.evenSublattice_carrier_le hy0) fun hye ↦ by
      simpa only [Submodule.coe_sub, coe_latticeVectorDual, sub_add_cancel] using
        L.carrier.add_mem (L.evenSublattice_carrier_le hye) e.property⟩

/-- `[w / 2]` is nonzero in `A_(L_even)` when `L` is odd. -/
theorem halfCharacteristicClass_ne_zero_of_not_isEven {w : L} (hw : L.IsCharacteristicVector w)
    (hL : ¬ L.IsEven) : L.halfCharacteristicClass hw ≠ 0 := fun h ↦ by
  rw [halfCharacteristicClass_def, L.evenSublattice.discriminantGroup_mk_eq_zero_iff,
    coe_halfCharacteristicDual] at h
  exact L.half_characteristic_notMem_carrier_of_not_isEven hw hL (L.evenSublattice_carrier_le h)

/-- `[e] + [w / 2]` is nonzero in `A_(L_even)` when `L` is odd. -/
theorem latticeVectorClass_add_halfCharacteristicClass_ne_zero_of_not_isEven {w : L}
    (hw : L.IsCharacteristicVector w) (hL : ¬ L.IsEven) (e : L) :
    L.latticeVectorClass e + L.halfCharacteristicClass hw ≠ 0 :=
  L.halfCharacteristicClass_add_two_smul hw e ▸
    L.halfCharacteristicClass_ne_zero_of_not_isEven (hw.add_two_smul e) hL

/-- `halfCharacteristicSubgroup` has order two whenever `L` is odd and `w²` is even. -/
theorem natCard_halfCharacteristicSubgroup {w : L} (hw : L.IsCharacteristicVector w)
    (hwe : Even (L.integralNorm w)) (hL : ¬ L.IsEven) :
    Nat.card (L.halfCharacteristicSubgroup hw) = 2 :=
  (Nat.card_zmultiples _).trans (addOrderOf_eq_prime
    ((L.two_nsmul_halfCharacteristicClass_eq_zero_iff_even_integralNorm hw).mpr hwe)
    (L.halfCharacteristicClass_ne_zero_of_not_isEven hw hL))

/-- `shiftedHalfCharacteristicSubgroup` has order two whenever `L` is odd and `w²` is even. -/
theorem natCard_shiftedHalfCharacteristicSubgroup {w : L} (hw : L.IsCharacteristicVector w)
    (hwe : Even (L.integralNorm w)) (hL : ¬ L.IsEven) (e : L) :
    Nat.card (L.shiftedHalfCharacteristicSubgroup hw e) = 2 :=
  L.shiftedHalfCharacteristicSubgroup_eq_halfCharacteristicSubgroup hw e ▸
    L.natCard_halfCharacteristicSubgroup (hw.add_two_smul e)
      (even_iff_two_dvd.mpr ((L.dvd_integralNorm_add_two_smul_iff (by decide) hw e).mpr
        (even_iff_two_dvd.mp hwe))) hL

/-- The self-pairing of `[w / 2]` in `A_(L_even)` vanishes iff `4 ∣ L.integralNorm w`. -/
theorem discriminantPairing_halfCharacteristicClass_self_eq_zero_iff {w : L}
    (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantPairing (L.halfCharacteristicClass hw)
        (L.halfCharacteristicClass hw) = 0 ↔ 4 ∣ L.integralNorm w := by
  rw [halfCharacteristicClass_def, L.evenSublattice.discriminantPairing_mk_eq_zero_iff,
    Submodule.mem_one, L.evenSublattice_form, coe_halfCharacteristicDual]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← L.integralForm_cast w w,
    ← L.integralNorm_apply, algebraMap_int_eq, eq_intCast]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, Int.cast_injective (α := ℚ) (by push_cast; linarith)⟩,
    fun ⟨k, hk⟩ ↦ ⟨k, by rw [hk]; push_cast; ring⟩⟩

/-- The carrier glued along `⟨[w / 2]⟩` is integral iff `4 ∣ L.integralNorm w`. -/
theorem isIntegral_intermediateCarrier_halfCharacteristicSubgroup_iff {w : L}
    (hw : L.IsCharacteristicVector w) :
    IntermediateCarrier.IsIntegral (L.evenSublattice.intermediateCarrierOfDiscriminantSubgroup
      (L.halfCharacteristicSubgroup hw)) ↔ 4 ∣ L.integralNorm w := by
  rw [IntermediateCarrier.isIntegral_iff_forall_discriminantPairing_eq_zero,
    L.evenSublattice.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    halfCharacteristicSubgroup]
  refine ⟨fun h ↦ (L.discriminantPairing_halfCharacteristicClass_self_eq_zero_iff hw).mp
    (h _ (AddSubgroup.mem_zmultiples _) _ (AddSubgroup.mem_zmultiples _)), fun h4 a ha b hb ↦ ?_⟩
  rcases AddSubgroup.mem_zmultiples_iff.mp ha, AddSubgroup.mem_zmultiples_iff.mp hb with
    ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
  simp [(L.discriminantPairing_halfCharacteristicClass_self_eq_zero_iff hw).mpr h4]

/-- The carrier glued along `⟨[e] + [w / 2]⟩` is integral iff `4 ∣ L.integralNorm w`. -/
theorem isIntegral_intermediateCarrier_shiftedHalfCharacteristicSubgroup_iff {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    IntermediateCarrier.IsIntegral (L.evenSublattice.intermediateCarrierOfDiscriminantSubgroup
      (L.shiftedHalfCharacteristicSubgroup hw e)) ↔ 4 ∣ L.integralNorm w := by
  rw [L.shiftedHalfCharacteristicSubgroup_eq_halfCharacteristicSubgroup hw e,
    L.isIntegral_intermediateCarrier_halfCharacteristicSubgroup_iff,
    L.dvd_integralNorm_add_two_smul_iff (by decide) hw e]

/-- `[w / 2]` is quadratic-isotropic in `A_(L_even)` iff `8 ∣ L.integralNorm w`. -/
theorem discriminantQuadraticMap_halfCharacteristicClass_eq_zero_iff {w : L}
    (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw) = 0 ↔ 8 ∣ L.integralNorm w := by
  rw [L.discriminantQuadraticMap_halfCharacteristicClass hw, ZMod.toRatAddCircle_eq_zero 8,
    ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl

/-- `⟨[w / 2]⟩` is quadratic-isotropic iff `8 ∣ L.integralNorm w`. -/
@[simp] theorem isIsotropic_halfCharacteristicSubgroup_iff [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).IsIsotropic
        (L.halfCharacteristicSubgroup hw) ↔ 8 ∣ L.integralNorm w := by
  rw [← L.evenSublattice.isEven_intermediateCarrierOfDiscriminantSubgroup_iff
    L.isEven_evenSublattice, IntermediateCarrier.isEven_iff_forall_discriminantQuadraticMap_eq_zero
      L.isEven_evenSublattice,
    L.evenSublattice.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    halfCharacteristicSubgroup]
  refine ⟨fun h ↦ (L.discriminantQuadraticMap_halfCharacteristicClass_eq_zero_iff hw).mp
    (h _ (AddSubgroup.mem_zmultiples _)), fun h8 a ha ↦ ?_⟩
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
  simp [QuadraticMap.map_smul,
    (L.discriminantQuadraticMap_halfCharacteristicClass_eq_zero_iff hw).mpr h8]

/-- `⟨[e] + [w / 2]⟩` is quadratic-isotropic iff `8 ∣ L.integralNorm w`. -/
@[simp] theorem isIsotropic_shiftedHalfCharacteristicSubgroup_iff [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).IsIsotropic
        (L.shiftedHalfCharacteristicSubgroup hw e) ↔ 8 ∣ L.integralNorm w := by
  rw [L.shiftedHalfCharacteristicSubgroup_eq_halfCharacteristicSubgroup hw e,
    L.isIsotropic_halfCharacteristicSubgroup_iff,
    L.dvd_integralNorm_add_two_smul_iff dvd_rfl hw e]

/-- **The even overlattice `L_even + ℤ · (w / 2)` of `L.evenSublattice` when `8 ∣ w²`.**
This definition does not assume `L` is odd or unimodular: when `L` is odd it is a Kneser
two-neighbor of `L`, and when `L` is unimodular it is unimodular (in particular, it equals `L`
when `L` is both even and unimodular). -/
noncomputable def halfCharacteristicOverlattice [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) : IntegralLattice V :=
  L.evenSublattice.ofIsotropicSubgroup L.isEven_evenSublattice (L.halfCharacteristicSubgroup hw)
    ((L.isIsotropic_halfCharacteristicSubgroup_iff hw).mpr h8)

/-- **The even overlattice `L_even + ℤ · (e + w / 2)` of `L.evenSublattice` when `8 ∣ w²`.**
This definition does not assume `L` is odd or unimodular: when `L` is odd it is a Kneser
two-neighbor of `L`, and when `L` is unimodular it is unimodular. -/
noncomputable def shiftedHalfCharacteristicOverlattice [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) : IntegralLattice V :=
  L.evenSublattice.ofIsotropicSubgroup L.isEven_evenSublattice
    (L.shiftedHalfCharacteristicSubgroup hw e)
    ((L.isIsotropic_shiftedHalfCharacteristicSubgroup_iff hw e).mpr h8)

/-- Shifting `w` by `2 • e` identifies `shiftedHalfCharacteristicOverlattice` with
`halfCharacteristicOverlattice` at `w + 2 • e`. -/
theorem shiftedHalfCharacteristicOverlattice_eq_halfCharacteristicOverlattice [L.IsNondegenerate]
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    L.shiftedHalfCharacteristicOverlattice hw h8 e = L.halfCharacteristicOverlattice
      (hw.add_two_smul e) ((hw.integralNorm_add_two_smul_modEq e).dvd_iff.mpr h8) :=
  (L.evenSublattice.ofIsotropicSubgroup_inj ..).mpr
    (L.shiftedHalfCharacteristicSubgroup_eq_halfCharacteristicSubgroup ..)

/-- `halfCharacteristicOverlattice` shares the ambient rational bilinear form of `L`. -/
@[simp] theorem halfCharacteristicOverlattice_form [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hw h8).form = L.form :=
  (L.evenSublattice.ofIsotropicSubgroup_form ..).trans L.evenSublattice_form

/-- `shiftedHalfCharacteristicOverlattice` shares the ambient rational bilinear form of `L`. -/
@[simp] theorem shiftedHalfCharacteristicOverlattice_form [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hw h8 e).form = L.form := by
  rw [L.shiftedHalfCharacteristicOverlattice_eq_halfCharacteristicOverlattice,
    L.halfCharacteristicOverlattice_form]

/-- `halfCharacteristicOverlattice` has the same signature as `L`. -/
@[simp] theorem halfCharacteristicOverlattice_signature [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hw h8).signature = L.signature :=
  signature_eq_of_form_eq (L.halfCharacteristicOverlattice_form hw h8)

/-- `shiftedHalfCharacteristicOverlattice` has the same signature as `L`. -/
@[simp] theorem shiftedHalfCharacteristicOverlattice_signature [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hw h8 e).signature = L.signature :=
  signature_eq_of_form_eq (L.shiftedHalfCharacteristicOverlattice_form hw h8 e)

/-- `halfCharacteristicOverlattice` is an even integral lattice. -/
theorem isEven_halfCharacteristicOverlattice [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hw h8).IsEven :=
  L.evenSublattice.isEven_ofIsotropicSubgroup ..

/-- `shiftedHalfCharacteristicOverlattice` is an even integral lattice. -/
theorem isEven_shiftedHalfCharacteristicOverlattice [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hw h8 e).IsEven := by
  rw [L.shiftedHalfCharacteristicOverlattice_eq_halfCharacteristicOverlattice]
  exact L.isEven_halfCharacteristicOverlattice ..

/-- Explicit coset membership in `halfCharacteristicOverlattice`. -/
theorem mem_halfCharacteristicOverlattice_carrier_iff [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (x : V) :
    x ∈ (L.halfCharacteristicOverlattice hw h8).carrier ↔
      x ∈ L.evenSublattice.carrier ∨ x - (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.carrier := by
  have hq : L.halfCharacteristicDual hw =
      ⟨(1 / 2 : ℚ) • (w : V), L.half_characteristic_mem_evenSublattice_dualCarrier hw⟩ :=
    Subtype.ext (L.coe_halfCharacteristicDual hw)
  have h2 : 2 • (Submodule.Quotient.mk ⟨(1 / 2 : ℚ) • (w : V),
      L.half_characteristic_mem_evenSublattice_dualCarrier hw⟩ :
        L.evenSublattice.DiscriminantGroup) = 0 := by
    rw [← hq, ← halfCharacteristicClass_def]
    exact (L.two_nsmul_halfCharacteristicClass_eq_zero_iff_even_integralNorm hw).mpr
      (even_iff_two_dvd.mpr (dvd_trans (by decide) h8))
  rw [halfCharacteristicOverlattice, L.evenSublattice.ofIsotropicSubgroup_carrier,
    halfCharacteristicSubgroup, halfCharacteristicClass_def, hq]
  exact L.evenSublattice.mem_intermediateCarrierOfDiscriminantSubgroup_zmultiples_iff
    (L.half_characteristic_mem_evenSublattice_dualCarrier hw) h2 x

/-- Explicit coset membership in `shiftedHalfCharacteristicOverlattice`. -/
theorem mem_shiftedHalfCharacteristicOverlattice_carrier_iff [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) (x : V) :
    x ∈ (L.shiftedHalfCharacteristicOverlattice hw h8 e).carrier ↔
      x ∈ L.evenSublattice.carrier ∨
        x - ((e : V) + (1 / 2 : ℚ) • (w : V)) ∈ L.evenSublattice.carrier := by
  rw [L.shiftedHalfCharacteristicOverlattice_eq_halfCharacteristicOverlattice,
    L.mem_halfCharacteristicOverlattice_carrier_iff,
    ← L.coe_halfCharacteristicDual (hw.add_two_smul e),
    L.halfCharacteristicDual_add_two_smul hw e, Submodule.coe_add, L.coe_latticeVectorDual,
    L.coe_halfCharacteristicDual hw]

/-- `halfCharacteristicOverlattice` is a Kneser two-neighbor of `L` whenever `L` is odd. -/
theorem isNeighbor_halfCharacteristicOverlattice [L.IsNondegenerate] (hL : ¬ L.IsEven)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    L.IsNeighbor (L.halfCharacteristicOverlattice hw h8) 2 := by
  have hinf : L.carrier ⊓ (L.halfCharacteristicOverlattice hw h8).carrier =
      L.evenSublattice.carrier := le_antisymm (fun x ⟨hxL, hxM⟩ ↦
    ((L.mem_halfCharacteristicOverlattice_carrier_iff hw h8 x).mp hxM).elim id fun hx1 ↦
      (L.half_characteristic_notMem_carrier_of_not_isEven hw hL
        (by simpa only [sub_sub_cancel] using
          L.carrier.sub_mem hxL (L.evenSublattice_carrier_le hx1))).elim)
    (le_inf L.evenSublattice_carrier_le fun x hx ↦
      (L.mem_halfCharacteristicOverlattice_carrier_iff hw h8 x).mpr (Or.inl hx))
  refine ⟨(L.halfCharacteristicOverlattice_form hw h8).symm,
    hinf ▸ L.relIndex_evenSublattice_of_not_isEven hL, ?_⟩
  rw [hinf, halfCharacteristicOverlattice, L.evenSublattice.ofIsotropicSubgroup_carrier,
    ← IntermediateCarrier.index_def,
    IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup]
  exact L.natCard_halfCharacteristicSubgroup hw
    (even_iff_two_dvd.mpr (dvd_trans (by decide) h8)) hL

/-- `shiftedHalfCharacteristicOverlattice` is a Kneser two-neighbor of `L` whenever `L` is odd. -/
theorem isNeighbor_shiftedHalfCharacteristicOverlattice [L.IsNondegenerate] (hL : ¬ L.IsEven)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    L.IsNeighbor (L.shiftedHalfCharacteristicOverlattice hw h8 e) 2 :=
  L.shiftedHalfCharacteristicOverlattice_eq_halfCharacteristicOverlattice hw h8 e ▸
    L.isNeighbor_halfCharacteristicOverlattice hL _ _

/-- `halfCharacteristicOverlattice` is unimodular when `L` is unimodular and `8 ∣ w²`. -/
theorem isUnimodular_halfCharacteristicOverlattice [L.IsNondegenerate] (hLu : L.IsUnimodular)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hw h8).IsUnimodular := by
  by_cases hL : L.IsEven
  · have hEq : L.halfCharacteristicOverlattice hw h8 = L := IntegralLattice.ext
      (Submodule.ext fun x ↦ by
        rw [L.mem_halfCharacteristicOverlattice_carrier_iff, L.evenSublattice_eq_self_iff.mpr hL]
        exact ⟨fun h ↦ h.elim id fun hx ↦ by
          simpa using L.carrier.add_mem hx ((L.half_characteristic_mem_carrier_iff hLu hw).mpr hL),
          Or.inl⟩) (L.halfCharacteristicOverlattice_form hw h8)
    rwa [hEq]
  · exact (L.isNeighbor_halfCharacteristicOverlattice hL hw h8).isUnimodular hLu

/-- `shiftedHalfCharacteristicOverlattice` is unimodular when `L` is unimodular and `8 ∣ w²`. -/
theorem isUnimodular_shiftedHalfCharacteristicOverlattice [L.IsNondegenerate]
    (hLu : L.IsUnimodular) {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w)
    (e : L) : (L.shiftedHalfCharacteristicOverlattice hw h8 e).IsUnimodular :=
  L.shiftedHalfCharacteristicOverlattice_eq_halfCharacteristicOverlattice hw h8 e ▸
    L.isUnimodular_halfCharacteristicOverlattice hLu _ _

/-- **Every even Kneser two-neighbor of an odd lattice meets it in the even sublattice.** -/
theorem carrier_inf_eq_evenSublattice_carrier_of_isNeighbor {M : IntegralLattice V}
    (hL : ¬ L.IsEven) (hM : L.IsNeighbor M 2) (hMe : M.IsEven) :
    L.carrier ⊓ M.carrier = L.evenSublattice.carrier := by
  have hle : L.carrier ⊓ M.carrier ≤ L.evenSublattice.carrier := fun x ⟨hxL, hxM⟩ ↦ by
    rw [L.mem_evenSublattice_carrier_iff ⟨x, hxL⟩, L.even_integralNorm_iff]
    simpa only [norm_apply, hM.form_eq] using M.isEven_iff_forall_norm.mp hMe ⟨x, hxM⟩
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (L.carrier ⊓ M.carrier).toAddSubgroup L.evenSublattice.carrier.toAddSubgroup
    L.carrier.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).mpr hle)
    ((Submodule.toAddSubgroup_le _ _).mpr L.evenSublattice_carrier_le)
  rw [hM.relIndex_inf_left, L.relIndex_evenSublattice_of_not_isEven hL] at hmul
  exact le_antisymm hle ((Submodule.toAddSubgroup_le _ _).mp
    (AddSubgroup.relIndex_eq_one.mp (by omega)))

/-- **Classification of even Kneser two-neighbors of an odd unimodular lattice.** -/
theorem eq_halfCharacteristicOverlattice_or_eq_shiftedHalfCharacteristicOverlattice_of_isNeighbor
    [L.IsNondegenerate] {M : IntegralLattice V} (hLu : L.IsUnimodular) (hM : L.IsNeighbor M 2)
    (hMe : M.IsEven) {w : L} (hw : L.IsCharacteristicVector w) {e : L}
    (he : Odd (L.integralNorm e)) :
    ∃ h8 : 8 ∣ L.integralNorm w,
      M = L.halfCharacteristicOverlattice hw h8 ∨
        M = L.shiftedHalfCharacteristicOverlattice hw h8 e := by
  have hL := L.not_isEven_of_odd_integralNorm he
  have hinf := L.carrier_inf_eq_evenSublattice_carrier_of_isNeighbor hL hM hMe
  have hle : L.evenSublattice.carrier ≤ M.carrier := hinf ▸ inf_le_right
  have hform : M.form = L.evenSublattice.form := hM.form_eq.symm.trans L.evenSublattice_form.symm
  let P := M.toIntermediateCarrier hform hle
  let H := L.evenSublattice.discriminantSubgroup P
  have hHiso : (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).IsIsotropic
      H := (IntermediateCarrier.isEven_iff_isIsotropic_discriminantSubgroup
        L.isEven_evenSublattice P).mp (M.isEven_toIntermediateCarrier hform hle hMe)
  obtain ⟨g, hg_ne, hHz⟩ := AddSubgroup.exists_zmultiples_eq_of_prime_natCard (H := H) (by
    rw [← IntermediateCarrier.index_eq_natCard_discriminantSubgroup, IntermediateCarrier.index_def,
      M.coe_toIntermediateCarrier hform hle, ← hinf, hM.relIndex_inf_right]
    exact Nat.prime_two)
  have hM_eq : L.evenSublattice.ofIsotropicSubgroup L.isEven_evenSublattice H hHiso = M :=
    IntegralLattice.ext (by
      rw [L.evenSublattice.ofIsotropicSubgroup_carrier,
        L.evenSublattice.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup P]
      exact M.coe_toIntermediateCarrier hform hle)
      ((L.evenSublattice.ofIsotropicSubgroup_form _ _ _).trans hform.symm)
  rcases L.eq_zero_or_eq_latticeVectorClass_or_eq_halfCharacteristicClass_or_eq_add
      hLu hw he g with rfl | rfl | rfl | rfl
  · exact (hg_ne rfl).elim
  · have hHL : L.evenSublattice.discriminantSubgroup P = L.evenSublattice.discriminantSubgroup
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) :=
      hHz.symm.trans
        (L.discriminantSubgroup_toIntermediateCarrier_eq_zmultiples_latticeVectorClass he).symm
    rw [← L.evenSublattice.intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
      ← L.evenSublattice.intermediateCarrierOrderIsoDiscriminantSubgroup_apply] at hHL
    have hPL := congrArg Subtype.val
      (L.evenSublattice.intermediateCarrierOrderIsoDiscriminantSubgroup.injective hHL)
    rw [M.coe_toIntermediateCarrier hform hle, L.coe_toIntermediateCarrier] at hPL
    exact (hL (IntegralLattice.ext hPL hM.form_eq.symm ▸ hMe)).elim
  · rw [← halfCharacteristicSubgroup] at hHz
    refine ⟨(L.isIsotropic_halfCharacteristicSubgroup_iff hw).mp (hHz ▸ hHiso), Or.inl ?_⟩
    rw [← hM_eq, halfCharacteristicOverlattice, L.evenSublattice.ofIsotropicSubgroup_inj]
    exact hHz.symm
  · rw [← shiftedHalfCharacteristicSubgroup] at hHz
    refine ⟨(L.isIsotropic_shiftedHalfCharacteristicSubgroup_iff hw e).mp (hHz ▸ hHiso), Or.inr ?_⟩
    rw [← hM_eq, shiftedHalfCharacteristicOverlattice, L.evenSublattice.ofIsotropicSubgroup_inj]
    exact hHz.symm

end TauCeti.IntegralLattice
