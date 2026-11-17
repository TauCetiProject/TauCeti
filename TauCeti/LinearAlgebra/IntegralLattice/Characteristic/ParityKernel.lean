/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

/-!
# The discriminant group and overlattices of the norm-parity kernel

For an odd unimodular lattice `L` with characteristic vector `w`, `L.evenSublattice` has index two,
`(L_even)ᵛ = L + ℤ · (w / 2)`, `w² ≡ finrank ℤ L [ZMOD 2]`, and `A_(L_even)` is `ℤ/4` (odd rank) or
`ℤ/2 × ℤ/2` (even rank). When `8 ∣ w²`, gluing along `⟨[w / 2]⟩` and `⟨[e + w / 2]⟩` gives the two
even unimodular Kneser two-neighbors of `L`, exhausting all even two-neighbors of `L`. We also
record that `evenSublattice` commutes with transport and orthogonal sums with even lattices, and
that Kneser `p`-neighbors are preserved by orthogonal sums.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §1.4 and §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II and Appendix 4.
* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Integral lattices on the same ambient space with equal rational form share a signature. -/
theorem signature_eq_of_form_eq {L M : IntegralLattice V} (h : L.form = M.form) :
    L.signature = M.signature :=
  L.signature_eq_of_equivalent ⟨h ▸ LinearMap.BilinForm.IsometryEquiv.refl L.form⟩

/-- Kneser `p`-neighbors share the same ambient rational form and therefore the same signature. -/
theorem IsNeighbor.signature_eq {L M : IntegralLattice V} {p : ℕ} (h : L.IsNeighbor M p) :
    L.signature = M.signature := signature_eq_of_form_eq h.form_eq

private theorem orthogonalSum_transport_prodComm {W : Type v} [AddCommGroup W] [Module ℚ W]
    (A : IntegralLattice V) (B : IntegralLattice W) :
    (B.orthogonalSum A).transport (LinearEquiv.prodComm ℚ W V) = A.orthogonalSum B := by
  have heq : LinearEquiv.prodComm ℚ W V = (Isometry.orthogonalSumComm B A).toLinearEquiv :=
    LinearEquiv.ext fun p ↦ (Isometry.orthogonalSumComm_apply B A p).symm
  exact heq ▸ (Isometry.orthogonalSumComm B A).transport_eq

/-- **Kneser `p`-neighbors are preserved by left orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_left {W : Type v} [AddCommGroup W] [Module ℚ W]
    (Y : IntegralLattice V) {M N : IntegralLattice W} {p : ℕ}
    (h : M.IsNeighbor N p) : (Y.orthogonalSum M).IsNeighbor (Y.orthogonalSum N) p := by
  have hrel (B : Submodule ℤ W) : (Y.carrier.prod (M.carrier ⊓ N.carrier)).toAddSubgroup.relIndex
      (Y.carrier.prod B).toAddSubgroup =
      (M.carrier ⊓ N.carrier).toAddSubgroup.relIndex B.toAddSubgroup := by
    let proj : (Y.carrier.prod B).toAddSubgroup →+ B.toAddSubgroup :=
      ⟨⟨fun q ↦ ⟨q.1.2, q.2.2⟩, rfl⟩, fun _ _ ↦ rfl⟩
    have hcomap : ((M.carrier ⊓ N.carrier).toAddSubgroup.addSubgroupOf B.toAddSubgroup).comap proj =
        (Y.carrier.prod (M.carrier ⊓ N.carrier)).toAddSubgroup.addSubgroupOf
          (Y.carrier.prod B).toAddSubgroup :=
      AddSubgroup.ext fun q ↦ ⟨fun hq ↦ ⟨q.2.1, hq⟩, fun hq ↦ hq.2⟩
    rw [AddSubgroup.relIndex, ← hcomap, AddSubgroup.index_comap_of_surjective _
      (fun b ↦ ⟨⟨(0, b.1), ⟨Y.carrier.zero_mem, b.2⟩⟩, rfl⟩), ← AddSubgroup.relIndex]
  have hinf : (Y.orthogonalSum M).carrier ⊓ (Y.orthogonalSum N).carrier =
      Y.carrier.prod (M.carrier ⊓ N.carrier) := Submodule.ext fun x ↦ by
    simp only [Submodule.mem_inf, orthogonalSum_carrier, Submodule.mem_prod]; tauto
  exact ⟨by simp [h.form_eq], by rw [hinf, orthogonalSum_carrier, hrel]; exact h.relIndex_inf_left,
    by rw [hinf, orthogonalSum_carrier, hrel]; exact h.relIndex_inf_right⟩

/-- **Kneser `p`-neighbors are preserved by right orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_right {W : Type v} [AddCommGroup W] [Module ℚ W]
    {M N : IntegralLattice V} {p : ℕ} (h : M.IsNeighbor N p) (Y : IntegralLattice W) :
    (M.orthogonalSum Y).IsNeighbor (N.orthogonalSum Y) p := by
  have hswap := (h.orthogonalSum_left Y).transport (LinearEquiv.prodComm ℚ W V)
  rwa [orthogonalSum_transport_prodComm, orthogonalSum_transport_prodComm] at hswap

variable (L : IntegralLattice V)

/-- Membership in `L.evenSublattice` is membership in `L` with an even integer norm. -/
theorem mem_evenSublattice_carrier_iff_exists_norm (x : V) :
    x ∈ L.evenSublattice.carrier ↔ x ∈ L.carrier ∧ ∃ k : ℤ, L.norm x = 2 * k :=
  ⟨fun h ↦ ⟨L.evenSublattice_carrier_le h,
    (L.even_integralNorm_iff ⟨x, L.evenSublattice_carrier_le h⟩).mp
      ((L.mem_evenSublattice_carrier_iff ⟨x, L.evenSublattice_carrier_le h⟩).mp h)⟩,
   fun ⟨hx, hk⟩ ↦ (L.mem_evenSublattice_carrier_iff ⟨x, hx⟩).mpr
    ((L.even_integralNorm_iff ⟨x, hx⟩).mpr hk)⟩

/-- `evenSublattice` commutes with transporting an integral lattice along a linear equivalence. -/
@[simp] theorem evenSublattice_transport {W : Type v} [AddCommGroup W] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) : (L.transport e).evenSublattice = L.evenSublattice.transport e :=
  IntegralLattice.ext (Submodule.ext fun y ↦ by
    rw [mem_evenSublattice_carrier_iff_exists_norm, transport_carrier, Submodule.mem_map_equiv,
      transport_carrier, Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply,
      mem_evenSublattice_carrier_iff_exists_norm]
    simp [norm_apply, transport_form]) (by simp)

omit L in
/-- **Orthogonal sum with an even lattice commutes with `evenSublattice`.** -/
theorem evenSublattice_orthogonalSum_of_isEven_left {W : Type v} [AddCommGroup W] [Module ℚ W]
    {Y : IntegralLattice V} (hY : Y.IsEven) (M : IntegralLattice W) :
    (Y.orthogonalSum M).evenSublattice = Y.orthogonalSum M.evenSublattice := by
  refine IntegralLattice.ext (Submodule.ext fun p ↦ ?_) (by simp)
  rw [mem_evenSublattice_carrier_iff_exists_norm, orthogonalSum_carrier, Submodule.mem_prod,
    orthogonalSum_carrier, Submodule.mem_prod, mem_evenSublattice_carrier_iff_exists_norm,
    norm_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply, ← Y.norm_apply, ← M.norm_apply]
  refine ⟨fun ⟨⟨hp1, hp2⟩, k, hk⟩ ↦ ?_, fun ⟨hp1, hp2, k, hk⟩ ↦ ?_⟩ <;>
    obtain ⟨m, hm⟩ := Y.isEven_iff_forall_norm.mp hY ⟨p.1, hp1⟩
  · exact ⟨hp1, hp2, k - m, by push_cast; linarith⟩
  · exact ⟨⟨hp1, hp2⟩, m + k, by push_cast; linarith⟩

omit L in
/-- Right-hand companion to `evenSublattice_orthogonalSum_of_isEven_left`. -/
theorem evenSublattice_orthogonalSum_of_isEven_right {W : Type v} [AddCommGroup W] [Module ℚ W]
    (M : IntegralLattice V) {Y : IntegralLattice W} (hY : Y.IsEven) :
    (M.orthogonalSum Y).evenSublattice = M.evenSublattice.orthogonalSum Y := by
  rw [← orthogonalSum_transport_prodComm M Y, evenSublattice_transport,
    evenSublattice_orthogonalSum_of_isEven_left hY M, orthogonalSum_transport_prodComm]

/-- The even sublattice coincides with the lattice itself precisely when the lattice is even. -/
@[simp] theorem evenSublattice_eq_self_iff : L.evenSublattice = L ↔ L.IsEven :=
  ⟨fun h ↦ h ▸ L.isEven_evenSublattice, fun h ↦ IntegralLattice.ext
    (le_antisymm L.evenSublattice_carrier_le fun x hx ↦ (L.mem_evenSublattice_carrier_iff
      ⟨x, hx⟩).mpr ((L.even_integralNorm_iff _).mpr (L.isEven_iff_forall_norm.mp h _)))
    L.evenSublattice_form⟩

/-- The even sublattice has index one in the lattice precisely when the lattice is even. -/
theorem relIndex_evenSublattice_eq_one_iff :
    L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup = 1 ↔ L.IsEven := by
  rw [AddSubgroup.relIndex_eq_one, Submodule.toAddSubgroup_le]
  exact ⟨fun h ↦ L.evenSublattice_eq_self_iff.mp
    (IntegralLattice.ext (le_antisymm L.evenSublattice_carrier_le h) L.evenSublattice_form),
    fun h ↦ le_of_eq (congrArg IntegralLattice.carrier (L.evenSublattice_eq_self_iff.mpr h).symm)⟩

/-- **The even sublattice has index two in every odd integral lattice.** -/
theorem relIndex_evenSublattice_of_not_isEven (hL : ¬ L.IsEven) :
    L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup = 2 := by
  rw [L.relIndex_evenSublattice_eq_natCard_quotient, L.natCard_quotient_evenSubmodule hL]

/-- For an odd lattice, `det(L_even) = 4 * det(L)`. -/
theorem determinant_evenSublattice_of_not_isEven (hL : ¬ L.IsEven) :
    L.evenSublattice.determinant = 4 * L.determinant := by
  rw [L.evenSublattice.determinant_eq_mul_relIndex_sq L L.evenSublattice_form
    L.evenSublattice_carrier_le, L.relIndex_evenSublattice_of_not_isEven hL]; ring

/-- For an odd lattice, `discriminant(L_even) = 4 * discriminant(L)`. -/
theorem discriminant_evenSublattice_of_not_isEven (hL : ¬ L.IsEven) :
    L.evenSublattice.discriminant = 4 * L.discriminant := by
  rw [L.evenSublattice.discriminant_eq_mul_relIndex_sq L L.evenSublattice_form
    L.evenSublattice_carrier_le, L.relIndex_evenSublattice_of_not_isEven hL]; ring

/-- For an odd unimodular lattice, `A_(L_even)` has order four. -/
theorem natCard_evenSublattice_discriminantGroup (hLu : L.IsUnimodular) (hL : ¬ L.IsEven) :
    Nat.card L.evenSublattice.DiscriminantGroup = 4 := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  rw [L.evenSublattice.natCard_discriminantGroup, L.discriminant_evenSublattice_of_not_isEven hL,
    L.isUnimodular_iff_discriminant_eq_one.mp hLu, mul_one]

/-- Half of a characteristic vector lies in the dual carrier of the even sublattice. -/
theorem half_characteristic_mem_evenSublattice_dualCarrier {w : L}
    (hw : L.IsCharacteristicVector w) : (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]; intro y hy
  let yL : L := ⟨y, L.evenSublattice_carrier_le hy⟩
  have hy2 := even_iff_two_dvd.mp ((L.mem_evenSublattice_carrier_iff yL).mp hy)
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp (((L.isCharacteristicVector_iff w).mp hw yL).trans
    (Int.modEq_zero_iff_dvd.mpr hy2))
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← L.integralForm_cast w yL, hk]; push_cast; ring

/-- Half of a characteristic vector, packaged in the dual carrier of `L.evenSublattice`. -/
noncomputable def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), L.half_characteristic_mem_evenSublattice_dualCarrier hw⟩

/-- Ambient coercion of `halfCharacteristicDual`. -/
@[simp] theorem coe_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    (L.halfCharacteristicDual hw : V) = (1 / 2 : ℚ) • (w : V) := (rfl)

/-- The discriminant class of `(1 / 2) • w` in `A_(L_even)`. -/
noncomputable def halfCharacteristicClass {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.DiscriminantGroup := Submodule.Quotient.mk (L.halfCharacteristicDual hw)

/-- `halfCharacteristicClass` unfolded as the quotient class of `halfCharacteristicDual`. -/
theorem halfCharacteristicClass_def {w : L} (hw : L.IsCharacteristicVector w) :
    L.halfCharacteristicClass hw = Submodule.Quotient.mk (L.halfCharacteristicDual hw) := (rfl)

/-- Any vector of `L` lies in the dual carrier of `L.evenSublattice`. -/
theorem coe_mem_evenSublattice_dualCarrier (x : L) : (x : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule, L.evenSublattice_form]
  exact fun y hy ↦ L.form_mem_one x ⟨y, L.evenSublattice_carrier_le hy⟩

/-- A vector of `L`, packaged in the dual carrier of `L.evenSublattice`. -/
noncomputable def oddVectorDual (x : L) : L.evenSublattice.dualCarrier :=
  ⟨x, L.coe_mem_evenSublattice_dualCarrier x⟩

/-- Ambient coercion of `oddVectorDual`. -/
@[simp] theorem coe_oddVectorDual (x : L) : (L.oddVectorDual x : V) = (x : V) := (rfl)

/-- The discriminant class in `A_(L_even)` of a lattice vector `x ∈ L`. -/
noncomputable def oddVectorClass (x : L) : L.evenSublattice.DiscriminantGroup :=
  Submodule.Quotient.mk (L.oddVectorDual x)

/-- `oddVectorClass` unfolded as the quotient class of `oddVectorDual`. -/
theorem oddVectorClass_def (x : L) :
    L.oddVectorClass x = Submodule.Quotient.mk (L.oddVectorDual x) := (rfl)

private theorem halfCharacteristicClass_add_two_smul {w : L} (hw : L.IsCharacteristicVector w)
    (e : L) : L.halfCharacteristicClass (hw.add_two_smul e) =
      L.oddVectorClass e + L.halfCharacteristicClass hw := by
  simp only [halfCharacteristicClass_def, oddVectorClass_def, ← Submodule.Quotient.mk_add]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [Submodule.coe_add, coe_halfCharacteristicDual, coe_oddVectorDual,
    Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, smul_add, smul_smul]; norm_num; abel

private theorem dvd_integralNorm_add_two_smul_iff {d : ℤ} (hd : d ∣ 8) {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    d ∣ L.integralNorm (w + (2 : ℤ) • e) ↔ d ∣ L.integralNorm w :=
  ((hw.integralNorm_add_two_smul_modEq e).of_dvd hd).dvd_iff

private theorem sub_mem_evenSublattice_of_odd {u e : L} (hu : Odd (L.integralNorm u))
    (he : Odd (L.integralNorm e)) : ((u - e : L) : V) ∈ L.evenSublattice.carrier :=
  (L.mem_evenSublattice_carrier_iff (u - e)).mpr
    (by rw [L.integralNorm_sub]; exact (hu.add_odd he).sub (even_two_mul _))

/-- The class of a lattice vector in `A_(L_even)` vanishes precisely when its norm is even. -/
@[simp] theorem oddVectorClass_eq_zero_iff (x : L) :
    L.oddVectorClass x = 0 ↔ Even (L.integralNorm x) := by
  rw [oddVectorClass_def, L.evenSublattice.discriminantGroup_mk_eq_zero_iff, coe_oddVectorDual,
    L.mem_evenSublattice_carrier_iff]

/-- Every lattice vector defines a two-torsion class in `A_(L_even)`. -/
@[simp] theorem two_nsmul_oddVectorClass (x : L) : 2 • L.oddVectorClass x = 0 := by
  rw [oddVectorClass_def, ← Nat.cast_smul_eq_nsmul ℤ, ← Submodule.Quotient.mk_smul,
    Nat.cast_smul_eq_nsmul ℤ, L.evenSublattice.discriminantGroup_mk_eq_zero_iff,
    show ((2 • L.oddVectorDual x : L.evenSublattice.dualCarrier) : V) = (((2 : ℤ) • x : L) : V) by
      simp [two_smul], L.mem_evenSublattice_carrier_iff]
  exact (L.mem_evenSubmodule_iff _).mp (L.two_smul_mem_evenSubmodule x)

/-- Integer scalar multiplication by `2` annihilates every `oddVectorClass`. -/
theorem two_zsmul_oddVectorClass (x : L) : (2 : ℤ) • L.oddVectorClass x = 0 := by
  rw [two_zsmul, ← two_nsmul, L.two_nsmul_oddVectorClass]

/-- Half of a characteristic vector cannot lie in an odd lattice. -/
theorem half_characteristic_notMem_carrier_of_not_isEven {w : L}
    (hw : L.IsCharacteristicVector w) (hL : ¬ L.IsEven) : (1 / 2 : ℚ) • (w : V) ∉ L.carrier :=
  fun hm ↦ hL (L.isEven_iff_isCharacteristicVector_zero.mpr
    ((L.isCharacteristicVector_add_two_smul_iff 0 ⟨(1 / 2 : ℚ) • (w : V), hm⟩).mp
      ((Subtype.ext (by simp [← Int.cast_smul_eq_zsmul ℚ, smul_smul]) :
        w = 0 + (2 : ℤ) • ⟨(1 / 2 : ℚ) • (w : V), hm⟩) ▸ hw)))

/-- In a unimodular lattice, `(1 / 2) • w` lies in the carrier iff the lattice is even. -/
theorem half_characteristic_mem_carrier_iff (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) : (1 / 2 : ℚ) • (w : V) ∈ L.carrier ↔ L.IsEven := by
  refine ⟨fun hm ↦ by_contra fun hL ↦ L.half_characteristic_notMem_carrier_of_not_isEven hw hL hm,
    fun hLe ↦ ?_⟩
  obtain ⟨v, hv⟩ := hLu.exists_characteristicVector_sub_eq_two_smul hw
    (L.isEven_iff_isCharacteristicVector_zero.mp hLe)
  have hv' := congrArg (Subtype.val : L → V) hv
  simp only [sub_zero, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ] at hv'
  exact (show (1 / 2 : ℚ) • (w : V) = (v : V) by rw [hv', smul_smul]; norm_num) ▸ v.2

/-- The discriminant quadratic map evaluates `[w / 2]` to `w² / 8` modulo `1`. -/
theorem discriminantQuadraticMap_halfCharacteristicClass {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw) = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [halfCharacteristicClass_def, discriminantQuadraticMap_mk, L.evenSublattice_form,
    ZMod.toRatAddCircle_intCast, L.integralNorm_cast, L.norm_apply]
  simp only [coe_halfCharacteristicDual, map_smul, LinearMap.smul_apply, smul_eq_mul]; congr 1; ring

/-- For any `e ∈ L`, `[e] + [w / 2]` has discriminant quadratic value `w² / 8` modulo `1`. -/
theorem discriminantQuadraticMap_oddVectorClass_add_halfCharacteristicClass {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.oddVectorClass e + L.halfCharacteristicClass hw) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [← L.halfCharacteristicClass_add_two_smul hw e,
    L.discriminantQuadraticMap_halfCharacteristicClass,
    (ZMod.intCast_eq_intCast_iff _ _ 8).mpr (hw.integralNorm_add_two_smul_modEq e)]

/-- Translating `[w / 2]` by any class from `L / L_even` leaves its quadratic value unchanged. -/
theorem discriminantQuadraticMap_halfCharacteristicClass_add {w : L}
    (hw : L.IsCharacteristicVector w)
    (h : L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw + h) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw) := by
  obtain ⟨x, hx⟩ := h
  change L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
      (L.halfCharacteristicClass hw + x) = _
  induction x using Submodule.Quotient.induction_on with | _ y =>
  have hy : (y : V) ∈ L.carrier := by
    simpa [coe_toIntermediateCarrier] using
      (L.evenSublattice.mk_mem_discriminantSubgroup_iff _ y).mp hx
  rw [show (Submodule.Quotient.mk y : L.evenSublattice.DiscriminantGroup) =
      L.oddVectorClass ⟨y, hy⟩ from rfl, add_comm,
    L.discriminantQuadraticMap_oddVectorClass_add_halfCharacteristicClass hw,
    L.discriminantQuadraticMap_halfCharacteristicClass hw]

private theorem isCharacteristicVector_of_even_on_evenNorm {u y₀ : L}
    (hu_even : ∀ z : L, Even (L.integralNorm z) → Even (L.integralForm u z))
    (hy₀ : ¬ Even (L.integralForm u y₀)) : L.IsCharacteristicVector u := by
  have hy₀p : L.normParity y₀ = 1 := by
    rw [normParity_apply, ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    exact fun h ↦ hy₀ (hu_even y₀ h)
  rw [L.isCharacteristicVector_iff_forall_integralForm_eq_normParity]; intro y
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (L.normParity y) with hy0 | hy1
  · exact (ZMod.intCast_eq_zero_iff_even.mpr
      (hu_even y (ZMod.intCast_eq_zero_iff_even.mp (L.normParity_apply y ▸ hy0)))).trans hy0.symm
  · have hsum : Even (L.integralNorm (y + y₀)) := by
      rw [← ZMod.intCast_eq_zero_iff_even, ← L.normParity_apply, map_add, hy1, hy₀p]; decide
    have hform := ZMod.intCast_eq_zero_iff_even.mpr (hu_even (y + y₀) hsum)
    rw [map_add, Int.cast_add, ZMod.intCast_eq_one_iff_odd.mpr (Int.not_even_iff_odd.mp hy₀)]
      at hform
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
    simpa only [L.evenSublattice_form, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ,
      map_smul, LinearMap.smul_apply, Int.cast_ofNat] using hx _ ((L.mem_evenSublattice_carrier_iff
        _).mpr ((L.mem_evenSubmodule_iff _).mp (L.two_smul_mem_evenSubmodule ⟨y, hy⟩)))
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
    have hv' := congrArg (Subtype.val : L → V) hv
    simp only [u, Submodule.coe_sub, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ] at hv'
    exact (show x - (1 / 2 : ℚ) • (w : V) = (v : V) by
      rw [show x - (1 / 2 : ℚ) • (w : V) = (1 / 2 : ℚ) • ((2 : ℚ) • x - (w : V)) by
        rw [smul_sub, smul_smul]; norm_num, hv', smul_smul]; norm_num) ▸ v.2

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

omit L in
/-- **Characteristic-norm parity modulo two:** `w² ≡ rank(L) (mod 2)` over `𝔽₂`. -/
theorem IsUnimodular.integralNorm_characteristicVector_modEq_finrank {L : IntegralLattice V}
    (hLu : L.IsUnimodular) {w : L} (hw : L.IsCharacteristicVector w) :
    L.integralNorm w ≡ Module.finrank ℤ L [ZMOD 2] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let b : Basis (Fin (Module.finrank ℤ L)) ℤ L := Module.finBasis ℤ L
  let G₂ := (Int.castRingHom (ZMod 2)).mapMatrix (L.gramMatrix b)
  let B : LinearMap.BilinForm (ZMod 2) (Fin (Module.finrank ℤ L) → ZMod 2) := G₂.toBilin'
  have hG₂unit : IsUnit G₂.det := by
    rw [← RingHom.map_det, ← L.gramDet_def]
    exact ((L.isUnimodular_iff_isUnit_gramDet b).mp hLu).map _
  have hBnd := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' G₂ hG₂unit.ne_zero
  let f (x : L) (i : Fin (Module.finrank ℤ L)) : ZMod 2 := b.repr x i
  have hf_form (x y : L) : B (f x) (f y) = (L.integralForm x y : ZMod 2) := by
    have hxy := LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b L.integralForm x y
    rw [← L.gramMatrix_eq_toMatrix] at hxy
    simpa [B, Matrix.toBilin'_apply', f, G₂, RingHom.mapMatrix_apply, dotProduct, Matrix.mulVec,
      Finset.sum_mul, mul_assoc] using (congrArg (Int.castRingHom (ZMod 2)) hxy).symm
  have hwB (x : Fin (Module.finrank ℤ L) → ZMod 2) : B (f w) x = B x x := by
    let y : L := b.repr.symm (Finsupp.equivFunOnFinite.symm fun i ↦ (x i).val)
    rw [← show f y = x by ext i; simp [f, y], hf_form, hf_form, ← L.integralNorm_apply]
    exact (ZMod.intCast_eq_intCast_iff _ _ 2).mpr ((L.isCharacteristicVector_iff w).mp hw y)
  apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
  rw [L.integralNorm_apply, ← hf_form w w, Int.cast_natCast]
  rcases hBnd.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one (fun a ↦ isSquare_of_charTwo' a)
    (Or.inr (Matrix.isSymm_toBilin'_iff_isSymm.mpr ((L.isSymm_gramMatrix b).map _))) with
    ⟨halt, -⟩ | ⟨_, v, hv⟩
  · rw [halt (f w), ZMod.natCast_eq_zero_iff_even.mpr
      (by simpa [Module.finrank_fintype_fun_eq_card] using halt.even_finrank hBnd)]
  · set s := ∑ i, v i
    have hvB (i j) : B (v i) (v j) = if i = j then 1 else 0 := by
      simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.one_apply] using congrFun (congrFun hv i) j
    have hzero : B (f w - s) = 0 := v.ext fun j ↦ by
      rw [map_sub, LinearMap.sub_apply, hwB (v j), hvB j j]
      simp [s, map_sum, LinearMap.sum_apply, hvB]
    rw [sub_eq_zero.mp (hBnd.1 (f w - s) fun m ↦ by rw [hzero, LinearMap.zero_apply])]
    simp [s, map_sum, LinearMap.sum_apply, hvB, Module.finrank_fintype_fun_eq_card]

omit L in
/-- A unimodular lattice of odd rank cannot be even. -/
theorem IsUnimodular.not_isEven_of_odd_finrank {L : IntegralLattice V} (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) : ¬ L.IsEven := fun hLe ↦ by
  have hmod := hLu.integralNorm_characteristicVector_modEq_finrank
    (L.isEven_iff_isCharacteristicVector_zero.mp hLe)
  rw [L.integralNorm_zero] at hmod
  exact Int.not_even_iff_odd.mpr hodd.natCast
    (even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod.symm))

/-- `2 • [w / 2] = 0` in `A_(L_even)` iff `L.integralNorm w` is even. -/
theorem two_nsmul_halfCharacteristicClass_eq_zero_iff_even_integralNorm {w : L}
    (hw : L.IsCharacteristicVector w) :
    2 • L.halfCharacteristicClass hw = 0 ↔ Even (L.integralNorm w) := by
  rw [halfCharacteristicClass_def, ← Nat.cast_smul_eq_nsmul ℤ, ← Submodule.Quotient.mk_smul,
    Nat.cast_smul_eq_nsmul ℤ, L.evenSublattice.discriminantGroup_mk_eq_zero_iff,
    show ((2 • L.halfCharacteristicDual hw : L.evenSublattice.dualCarrier) : V) = (w : V) by
      simp [← Nat.cast_smul_eq_nsmul ℚ, smul_smul], L.mem_evenSublattice_carrier_iff]

/-- In a unimodular lattice, `2 • [w / 2] = 0` in `A_(L_even)` iff the rank is even. -/
theorem two_nsmul_halfCharacteristicClass_eq_zero_iff (hLu : L.IsUnimodular) {w : L}
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

private theorem not_isEven_of_odd {e : L} (he : Odd (L.integralNorm e)) : ¬ L.IsEven :=
  fun hLe ↦ Int.not_odd_iff_even.mpr
    ((L.even_integralNorm_iff e).mpr (L.isEven_iff_forall_norm.mp hLe e)) he

/-- In odd rank, `(2 : ℤ) • [w / 2]` is the unique nonzero class `[e]` of `L / L_even`. -/
theorem two_zsmul_halfCharacteristicClass_eq_oddVectorClass (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w)
    {e : L} (he : Odd (L.integralNorm e)) :
    (2 : ℤ) • L.halfCharacteristicClass hw = L.oddVectorClass e := by
  rw [halfCharacteristicClass_def, oddVectorClass_def, ← Submodule.Quotient.mk_smul,
    L.evenSublattice.discriminantGroup_mk_eq_iff,
    show (((2 : ℤ) • L.halfCharacteristicDual hw - L.oddVectorDual e :
      L.evenSublattice.dualCarrier) : V) = ((w - e : L) : V) by
        simp [← Int.cast_smul_eq_zsmul ℚ, smul_smul]]
  exact L.sub_mem_evenSublattice_of_odd (L.odd_integralNorm_of_odd_finrank hLu hodd hw) he

/-- **Four-element exhaustion of `A_(L_even)`** for unimodular `L` with odd-norm `e ∈ L`. -/
theorem evenSublatticeDiscriminantGroup_eq_four_classes (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) {e : L} (he : Odd (L.integralNorm e))
    (x : L.evenSublattice.DiscriminantGroup) :
    x = 0 ∨ x = L.oddVectorClass e ∨ x = L.halfCharacteristicClass hw ∨
      x = L.oddVectorClass e + L.halfCharacteristicClass hw := by
  induction x using Submodule.Quotient.induction_on with | _ y =>
  rcases (L.mem_evenSublattice_dualCarrier_iff hLu hw y).mp y.2 with hyL | hyL
  · rcases Int.even_or_odd (L.integralNorm ⟨y, hyL⟩) with hu | hu
    · exact Or.inl ((L.evenSublattice.discriminantGroup_mk_eq_zero_iff _).mpr
        ((L.mem_evenSublattice_carrier_iff ⟨y, hyL⟩).mpr hu))
    · rw [oddVectorClass_def]; exact Or.inr (Or.inl
        ((L.evenSublattice.discriminantGroup_mk_eq_iff _ _).mpr
          (L.sub_mem_evenSublattice_of_odd hu he)))
  · let u : L := ⟨(y : V) - (1 / 2 : ℚ) • (w : V), hyL⟩
    rcases Int.even_or_odd (L.integralNorm u) with hu | hu
    · rw [halfCharacteristicClass_def]; exact Or.inr (Or.inr (Or.inl
        ((L.evenSublattice.discriminantGroup_mk_eq_iff _ _).mpr
          ((L.mem_evenSublattice_carrier_iff u).mpr hu))))
    · rw [oddVectorClass_def, halfCharacteristicClass_def, ← Submodule.Quotient.mk_add]
      refine Or.inr (Or.inr (Or.inr ((L.evenSublattice.discriminantGroup_mk_eq_iff _ _).mpr ?_)))
      rw [show ((y - (L.oddVectorDual e + L.halfCharacteristicDual hw) :
          L.evenSublattice.dualCarrier) : V) = ((u - e : L) : V) by simp [u]; abel]
      exact L.sub_mem_evenSublattice_of_odd hu he

/-- **In odd rank, `A_(L_even) ≃+ ℤ/4`**, generated by `[w / 2]`. -/
noncomputable def zmodFourAddEquivEvenSublatticeDiscriminantGroup (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w) :
    ZMod 4 ≃+ L.evenSublattice.DiscriminantGroup := by
  have hw_odd := L.odd_integralNorm_of_odd_finrank hLu hodd hw
  refine zmodAddEquivOfGenerator (g := L.halfCharacteristicClass hw) (fun x ↦ ?_)
    (L.natCard_evenSublattice_discriminantGroup hLu (hLu.not_isEven_of_odd_finrank hodd))
  have h2 := L.two_zsmul_halfCharacteristicClass_eq_oddVectorClass hLu hodd hw hw_odd
  rcases L.evenSublatticeDiscriminantGroup_eq_four_classes hLu hw hw_odd x with
    rfl | rfl | rfl | rfl
  exacts [⟨0, by simp⟩, ⟨2, h2⟩, ⟨1, one_zsmul _⟩,
    ⟨3, by dsimp only; rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, h2, one_zsmul]⟩]

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
    exact (L.two_nsmul_halfCharacteristicClass_eq_zero_iff hLu hw).mpr heven
  refine AddEquiv.ofBijective ((L.evenSublatticeZModTwoHom _ (L.two_zsmul_oddVectorClass e)).coprod
    (L.evenSublatticeZModTwoHom _ hw2)) ?_
  rw [Nat.bijective_iff_surjective_and_card]
  refine ⟨fun g ↦ ?_, by simp [L.natCard_evenSublattice_discriminantGroup hLu
    (L.not_isEven_of_odd he)]⟩
  rcases L.evenSublatticeDiscriminantGroup_eq_four_classes hLu hw he g with rfl | rfl | rfl | rfl
  exacts [⟨(0, 0), by simp⟩, ⟨(1, 0), by simp [evenSublatticeZModTwoHom_one]⟩,
    ⟨(0, 1), by simp [evenSublatticeZModTwoHom_one]⟩,
    ⟨(1, 1), by simp [evenSublatticeZModTwoHom_one]⟩]

/-- `zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup` sends `(1, 0)` to `[e]`. -/
@[simp] theorem zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup_apply_one_zero
    (hLu : L.IsUnimodular) (heven : Even (Module.finrank ℤ L)) {w : L}
    (hw : L.IsCharacteristicVector w) {e : L} (he : Odd (L.integralNorm e)) :
    L.zmodTwoProdAddEquivEvenSublatticeDiscriminantGroup hLu heven hw he (1, 0) =
      L.oddVectorClass e := by
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
  AddSubgroup.zmultiples (L.oddVectorClass e + L.halfCharacteristicClass hw)

private theorem shiftedHalfCharacteristicSubgroup_eq {w : L} (hw : L.IsCharacteristicVector w)
    (e : L) : L.shiftedHalfCharacteristicSubgroup hw e =
      L.halfCharacteristicSubgroup (hw.add_two_smul e) :=
  congrArg AddSubgroup.zmultiples (L.halfCharacteristicClass_add_two_smul hw e).symm

/-- The subgroup of `A_(L_even)` attached to `L` itself is generated by any odd-norm vector. -/
theorem discriminantSubgroup_toIntermediateCarrier_eq_zmultiples_oddVectorClass
    {e : L} (he : Odd (L.integralNorm e)) :
    L.evenSublattice.discriminantSubgroup
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) =
      AddSubgroup.zmultiples (L.oddVectorClass e) := by
  ext x; rw [AddSubgroup.mem_zmultiples_iff_of_two_nsmul_eq_zero (L.two_nsmul_oddVectorClass e)]
  induction x using Submodule.Quotient.induction_on with | _ y =>
  rw [L.evenSublattice.mk_mem_discriminantSubgroup_iff, coe_toIntermediateCarrier,
    L.evenSublattice.discriminantGroup_mk_eq_zero_iff, oddVectorClass_def,
    L.evenSublattice.discriminantGroup_mk_eq_iff]
  exact ⟨fun hy ↦ (Int.even_or_odd (L.integralNorm ⟨y, hy⟩)).imp
    (L.mem_evenSublattice_carrier_iff ⟨y, hy⟩).mpr (fun h ↦ L.sub_mem_evenSublattice_of_odd h he),
    fun h ↦ h.elim (fun hy0 ↦ L.evenSublattice_carrier_le hy0) fun hye ↦ by
      simpa only [Submodule.coe_sub, coe_oddVectorDual, sub_add_cancel] using
        L.carrier.add_mem (L.evenSublattice_carrier_le hye) e.2⟩

/-- `[w / 2]` is nonzero in `A_(L_even)` when `L` is odd. -/
theorem halfCharacteristicClass_ne_zero_of_not_isEven {w : L} (hw : L.IsCharacteristicVector w)
    (hL : ¬ L.IsEven) : L.halfCharacteristicClass hw ≠ 0 := fun h ↦
  L.half_characteristic_notMem_carrier_of_not_isEven hw hL (L.evenSublattice_carrier_le
    ((L.evenSublattice.discriminantGroup_mk_eq_zero_iff _).mp h))

/-- `[e] + [w / 2]` is nonzero in `A_(L_even)` when `L` is odd. -/
theorem oddVectorClass_add_halfCharacteristicClass_ne_zero_of_not_isEven {w : L}
    (hw : L.IsCharacteristicVector w) (hL : ¬ L.IsEven) (e : L) :
    L.oddVectorClass e + L.halfCharacteristicClass hw ≠ 0 :=
  L.halfCharacteristicClass_add_two_smul hw e ▸
    L.halfCharacteristicClass_ne_zero_of_not_isEven (hw.add_two_smul e) hL

/-- In even rank, `halfCharacteristicSubgroup` has order two when `L` is odd and unimodular. -/
theorem natCard_halfCharacteristicSubgroup (hLu : L.IsUnimodular)
    (heven : Even (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w)
    (hL : ¬ L.IsEven) : Nat.card (L.halfCharacteristicSubgroup hw) = 2 :=
  (Nat.card_zmultiples _).trans (addOrderOf_eq_prime
    ((L.two_nsmul_halfCharacteristicClass_eq_zero_iff hLu hw).mpr heven)
    (L.halfCharacteristicClass_ne_zero_of_not_isEven hw hL))

/-- In even rank, `shiftedHalfCharacteristicSubgroup` has order two for odd unimodular `L`. -/
theorem natCard_shiftedHalfCharacteristicSubgroup (hLu : L.IsUnimodular)
    (heven : Even (Module.finrank ℤ L)) {w : L} (hw : L.IsCharacteristicVector w)
    (hL : ¬ L.IsEven) (e : L) : Nat.card (L.shiftedHalfCharacteristicSubgroup hw e) = 2 :=
  L.shiftedHalfCharacteristicSubgroup_eq hw e ▸ L.natCard_halfCharacteristicSubgroup hLu heven _ hL

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
  rw [L.shiftedHalfCharacteristicSubgroup_eq hw e,
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
  rw [L.shiftedHalfCharacteristicSubgroup_eq hw e, L.isIsotropic_halfCharacteristicSubgroup_iff,
    L.dvd_integralNorm_add_two_smul_iff dvd_rfl hw e]

/-- **The first even unimodular two-neighbor of `L` when `8 ∣ w²`.** -/
noncomputable def halfCharacteristicOverlattice (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) : IntegralLattice V :=
  letI : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  L.evenSublattice.ofIsotropicSubgroup L.isEven_evenSublattice (L.halfCharacteristicSubgroup hw)
    ((L.isIsotropic_halfCharacteristicSubgroup_iff hw).mpr h8)

/-- **The second even unimodular two-neighbor of `L` when `8 ∣ w²`.** -/
noncomputable def shiftedHalfCharacteristicOverlattice (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) : IntegralLattice V :=
  letI : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  L.evenSublattice.ofIsotropicSubgroup L.isEven_evenSublattice
    (L.shiftedHalfCharacteristicSubgroup hw e)
    ((L.isIsotropic_shiftedHalfCharacteristicSubgroup_iff hw e).mpr h8)

private theorem shiftedHalfCharacteristicOverlattice_eq (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    L.shiftedHalfCharacteristicOverlattice hLu hw h8 e = L.halfCharacteristicOverlattice hLu
      (hw.add_two_smul e) ((L.dvd_integralNorm_add_two_smul_iff dvd_rfl hw e).mpr h8) := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  exact (L.evenSublattice.ofIsotropicSubgroup_inj ..).mpr
    (L.shiftedHalfCharacteristicSubgroup_eq ..)

/-- `halfCharacteristicOverlattice` shares the ambient rational bilinear form of `L`. -/
@[simp] theorem halfCharacteristicOverlattice_form (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hLu hw h8).form = L.form := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  exact (L.evenSublattice.ofIsotropicSubgroup_form ..).trans L.evenSublattice_form

/-- `shiftedHalfCharacteristicOverlattice` shares the ambient rational bilinear form of `L`. -/
@[simp] theorem shiftedHalfCharacteristicOverlattice_form (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hLu hw h8 e).form = L.form := by
  rw [L.shiftedHalfCharacteristicOverlattice_eq, L.halfCharacteristicOverlattice_form]

/-- `halfCharacteristicOverlattice` has the same signature as `L`. -/
@[simp] theorem halfCharacteristicOverlattice_signature (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hLu hw h8).signature = L.signature :=
  signature_eq_of_form_eq (L.halfCharacteristicOverlattice_form hLu hw h8)

/-- `shiftedHalfCharacteristicOverlattice` has the same signature as `L`. -/
@[simp] theorem shiftedHalfCharacteristicOverlattice_signature (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hLu hw h8 e).signature = L.signature :=
  signature_eq_of_form_eq (L.shiftedHalfCharacteristicOverlattice_form hLu hw h8 e)

/-- `halfCharacteristicOverlattice` is an even integral lattice. -/
theorem isEven_halfCharacteristicOverlattice (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hLu hw h8).IsEven := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  exact L.evenSublattice.isEven_ofIsotropicSubgroup ..

/-- `shiftedHalfCharacteristicOverlattice` is an even integral lattice. -/
theorem isEven_shiftedHalfCharacteristicOverlattice (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hLu hw h8 e).IsEven := by
  rw [L.shiftedHalfCharacteristicOverlattice_eq]; exact L.isEven_halfCharacteristicOverlattice ..

private theorem even_finrank_of_eight_dvd_characteristicNorm (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) : Even (Module.finrank ℤ L) :=
  (L.two_nsmul_halfCharacteristicClass_eq_zero_iff hLu hw).mp
    ((L.two_nsmul_halfCharacteristicClass_eq_zero_iff_even_integralNorm hw).mpr
      (even_iff_two_dvd.mpr (dvd_trans (by decide) h8)))

/-- Explicit coset membership in `halfCharacteristicOverlattice`. -/
theorem mem_halfCharacteristicOverlattice_carrier_iff (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (x : V) :
    x ∈ (L.halfCharacteristicOverlattice hLu hw h8).carrier ↔
      x ∈ L.evenSublattice.carrier ∨ x - (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.carrier := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  rw [halfCharacteristicOverlattice, L.evenSublattice.ofIsotropicSubgroup_carrier]
  exact L.evenSublattice.mem_intermediateCarrierOfDiscriminantSubgroup_zmultiples_iff
    (L.half_characteristic_mem_evenSublattice_dualCarrier hw)
    ((L.two_nsmul_halfCharacteristicClass_eq_zero_iff hLu hw).mpr
      (L.even_finrank_of_eight_dvd_characteristicNorm hLu hw h8)) x

/-- Explicit coset membership in `shiftedHalfCharacteristicOverlattice`. -/
theorem mem_shiftedHalfCharacteristicOverlattice_carrier_iff (hLu : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) (x : V) :
    x ∈ (L.shiftedHalfCharacteristicOverlattice hLu hw h8 e).carrier ↔
      x ∈ L.evenSublattice.carrier ∨
        x - ((e : V) + (1 / 2 : ℚ) • (w : V)) ∈ L.evenSublattice.carrier := by
  rw [L.shiftedHalfCharacteristicOverlattice_eq, L.mem_halfCharacteristicOverlattice_carrier_iff,
    show (1 / 2 : ℚ) • ((w + (2 : ℤ) • e : L) : V) = (e : V) + (1 / 2 : ℚ) • (w : V) by
      simp [← Int.cast_smul_eq_zsmul ℚ, smul_add, smul_smul]; abel]

/-- `halfCharacteristicOverlattice` is a Kneser two-neighbor of `L`. -/
theorem isNeighbor_halfCharacteristicOverlattice (hLu : L.IsUnimodular) (hL : ¬ L.IsEven)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    L.IsNeighbor (L.halfCharacteristicOverlattice hLu hw h8) 2 := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  have hinf : L.carrier ⊓ (L.halfCharacteristicOverlattice hLu hw h8).carrier =
      L.evenSublattice.carrier := le_antisymm (fun x ⟨hxL, hxM⟩ ↦
    ((L.mem_halfCharacteristicOverlattice_carrier_iff hLu hw h8 x).mp hxM).elim id fun hx1 ↦
      (L.half_characteristic_notMem_carrier_of_not_isEven hw hL
        (by simpa only [sub_sub_cancel] using
          L.carrier.sub_mem hxL (L.evenSublattice_carrier_le hx1))).elim)
    (le_inf L.evenSublattice_carrier_le fun x hx ↦
      (L.mem_halfCharacteristicOverlattice_carrier_iff hLu hw h8 x).mpr (Or.inl hx))
  refine ⟨(L.halfCharacteristicOverlattice_form hLu hw h8).symm,
    hinf ▸ L.relIndex_evenSublattice_of_not_isEven hL, ?_⟩
  rw [hinf, halfCharacteristicOverlattice, L.evenSublattice.ofIsotropicSubgroup_carrier,
    ← IntermediateCarrier.index_def,
    IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup]
  exact L.natCard_halfCharacteristicSubgroup hLu
    (L.even_finrank_of_eight_dvd_characteristicNorm hLu hw h8) hw hL

/-- `shiftedHalfCharacteristicOverlattice` is a Kneser two-neighbor of `L`. -/
theorem isNeighbor_shiftedHalfCharacteristicOverlattice (hLu : L.IsUnimodular) (hL : ¬ L.IsEven)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    L.IsNeighbor (L.shiftedHalfCharacteristicOverlattice hLu hw h8 e) 2 :=
  L.shiftedHalfCharacteristicOverlattice_eq hLu hw h8 e ▸
    L.isNeighbor_halfCharacteristicOverlattice hLu hL _ _

/-- `halfCharacteristicOverlattice` is unimodular when `8 ∣ L.integralNorm w`. -/
theorem isUnimodular_halfCharacteristicOverlattice (hLu : L.IsUnimodular)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) :
    (L.halfCharacteristicOverlattice hLu hw h8).IsUnimodular := by
  by_cases hL : L.IsEven
  · have hEq : L.halfCharacteristicOverlattice hLu hw h8 = L := IntegralLattice.ext
      (Submodule.ext fun x ↦ by
        rw [L.mem_halfCharacteristicOverlattice_carrier_iff, L.evenSublattice_eq_self_iff.mpr hL]
        exact ⟨fun h ↦ h.elim id fun hx ↦ by
          simpa using L.carrier.add_mem hx ((L.half_characteristic_mem_carrier_iff hLu hw).mpr hL),
          Or.inl⟩) (L.halfCharacteristicOverlattice_form hLu hw h8)
    rwa [hEq]
  · exact (L.isNeighbor_halfCharacteristicOverlattice hLu hL hw h8).isUnimodular hLu

/-- `shiftedHalfCharacteristicOverlattice` is unimodular when `8 ∣ L.integralNorm w`. -/
theorem isUnimodular_shiftedHalfCharacteristicOverlattice (hLu : L.IsUnimodular)
    {w : L} (hw : L.IsCharacteristicVector w) (h8 : 8 ∣ L.integralNorm w) (e : L) :
    (L.shiftedHalfCharacteristicOverlattice hLu hw h8 e).IsUnimodular :=
  L.shiftedHalfCharacteristicOverlattice_eq hLu hw h8 e ▸
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

private theorem exists_zmultiples_eq_of_natCard_eq_two
    {H : AddSubgroup L.evenSublattice.DiscriminantGroup} (hcardH : Nat.card H = 2) :
    ∃ g : L.evenSublattice.DiscriminantGroup, g ≠ 0 ∧ AddSubgroup.zmultiples g = H := by
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨g, hgH⟩, hg0⟩ := exists_ne (0 : H)
  have hg_ne : g ≠ 0 := fun h ↦ hg0 (Subtype.ext h)
  have hcard_smul : 2 • (⟨g, hgH⟩ : H) = 0 := hcardH ▸
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard (⟨g, hgH⟩ : H))
  have hcz : Nat.card (AddSubgroup.zmultiples g) = 2 :=
    (Nat.card_zmultiples g).trans (addOrderOf_eq_prime (congrArg Subtype.val hcard_smul) hg_ne)
  exact ⟨g, hg_ne, AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hgH) (by omega)⟩

/-- **Classification of even Kneser two-neighbors of an odd unimodular lattice.** -/
theorem eq_halfCharacteristicOverlattice_or_shifted_of_isNeighbor {M : IntegralLattice V}
    (hLu : L.IsUnimodular) (hM : L.IsNeighbor M 2) (hMe : M.IsEven)
    {w : L} (hw : L.IsCharacteristicVector w) {e : L} (he : Odd (L.integralNorm e)) :
    ∃ h8 : 8 ∣ L.integralNorm w,
      M = L.halfCharacteristicOverlattice hLu hw h8 ∨
        M = L.shiftedHalfCharacteristicOverlattice hLu hw h8 e := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  have hL := L.not_isEven_of_odd he
  have hinf := L.carrier_inf_eq_evenSublattice_carrier_of_isNeighbor hL hM hMe
  have hle : L.evenSublattice.carrier ≤ M.carrier := hinf ▸ inf_le_right
  have hform : M.form = L.evenSublattice.form := hM.form_eq.symm.trans L.evenSublattice_form.symm
  let P := M.toIntermediateCarrier hform hle
  let H := L.evenSublattice.discriminantSubgroup P
  have hHiso : (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).IsIsotropic
      H := (IntermediateCarrier.isEven_iff_isIsotropic_discriminantSubgroup
        L.isEven_evenSublattice P).mp (M.isEven_toIntermediateCarrier hform hle hMe)
  obtain ⟨g, hg_ne, hHz⟩ := L.exists_zmultiples_eq_of_natCard_eq_two (H := H) (by
    rw [← IntermediateCarrier.index_eq_natCard_discriminantSubgroup, IntermediateCarrier.index_def,
      M.coe_toIntermediateCarrier hform hle, ← hinf, hM.relIndex_inf_right])
  have hM_eq : L.evenSublattice.ofIsotropicSubgroup L.isEven_evenSublattice H hHiso = M :=
    IntegralLattice.ext (by
      rw [L.evenSublattice.ofIsotropicSubgroup_carrier,
        L.evenSublattice.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup P]
      exact M.coe_toIntermediateCarrier hform hle)
      ((L.evenSublattice.ofIsotropicSubgroup_form _ _ _).trans hform.symm)
  rcases L.evenSublatticeDiscriminantGroup_eq_four_classes hLu hw he g with rfl | rfl | rfl | rfl
  · exact (hg_ne rfl).elim
  · have hHL : L.evenSublattice.discriminantSubgroup P = L.evenSublattice.discriminantSubgroup
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) :=
      hHz.symm.trans
        (L.discriminantSubgroup_toIntermediateCarrier_eq_zmultiples_oddVectorClass he).symm
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
