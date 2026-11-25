/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.FinCases

/-!
# The even sublattice of an integral lattice

The kernel of norm parity consists exactly of the vectors with even integral norm.
It contains twice the carrier, so its image in the original rational ambient space is full.
Restricting the form gives a canonical even sublattice with the same signature.
For an odd lattice the quotient by this submodule is canonically `ℤ/2` through norm parity,
so the even sublattice has index two, determinant `4 * det L`, and discriminant `4 * disc L`.
The construction also commutes with ambient transport and with orthogonal sums by an even lattice.

The even sublattice supplies the discriminant-form construction used to prove
van der Blij's characteristic-norm congruence for odd unimodular lattices and the parity-kernel
overlattice theory.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §1.4.
-/

public section

open scoped Pointwise

namespace TauCeti.IntegralLattice

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The submodule of lattice vectors with even integral norm, defined as the norm-parity kernel. -/
noncomputable def evenSubmodule : Submodule ℤ L := L.normParity.toIntLinearMap.ker

/-- Membership in the norm-parity kernel means that the integral norm is even. -/
@[simp]
theorem mem_evenSubmodule_iff (x : L) :
    x ∈ L.evenSubmodule ↔ Even (L.integralNorm x) := by
  simp only [evenSubmodule, LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap,
    normParity_apply, ZMod.intCast_eq_zero_iff_even]

/-- Twice every lattice vector lies in the even-norm submodule. -/
theorem two_smul_mem_evenSubmodule (x : L) : (2 : ℤ) • x ∈ L.evenSubmodule := by
  rw [evenSubmodule, LinearMap.mem_ker, map_smul]
  simp [show (2 : ZMod 2) = 0 by decide]

/-- The embedded even-norm submodule is full: it contains the full sublattice `2L`. -/
instance instIsFullLatticeEvenSubmodule :
    (L.evenSubmodule.map L.carrier.subtype).IsFullLattice ℚ := by
  refine Submodule.IsFullLattice.of_le_of_fg ℚ
    (M := Units.mk0 (2 : ℚ) (by norm_num) • L.carrier) ?_
    (Submodule.FG.of_le (Submodule.IsLattice.fg ℚ L.carrier) (L.carrier.map_subtype_le _))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have h := L.two_smul_mem_evenSubmodule ⟨y, hy⟩
  have hmap := Submodule.mem_map_of_mem (f := L.carrier.subtype) h
  rw [map_smul] at hmap
  -- The carrier inclusion sends the integral double to the ambient additive double.
  change (2 : ℤ) • y ∈ L.evenSubmodule.map L.carrier.subtype at hmap
  simpa only [Units.smul_mk0, two_smul, two_zsmul] using hmap

/-- The canonical even sublattice in the original rational ambient space. -/
noncomputable def evenSublattice : IntegralLattice V :=
  L.restrictFull (L.evenSubmodule.map L.carrier.subtype) (L.carrier.map_subtype_le _)

/-- The even sublattice's carrier is the embedded norm-parity kernel. -/
@[simp]
theorem evenSublattice_carrier :
    L.evenSublattice.carrier = L.evenSubmodule.map L.carrier.subtype := by
  unfold evenSublattice
  exact restrictFull_carrier ..

/-- The even sublattice is contained in the original lattice carrier. -/
theorem evenSublattice_carrier_le : L.evenSublattice.carrier ≤ L.carrier := by
  rw [evenSublattice_carrier]
  exact L.carrier.map_subtype_le _

/-- Viewed in the original carrier, the even sublattice is exactly the norm-parity kernel. -/
theorem evenSublattice_carrier_submoduleOf :
    L.evenSublattice.carrier.submoduleOf L.carrier = L.evenSubmodule := by
  rw [evenSublattice_carrier, Submodule.submoduleOf,
    Submodule.comap_map_eq_of_injective L.carrier.injective_subtype]

/-- A vector of the original lattice belongs to the even sublattice exactly when its norm
is even. -/
theorem mem_evenSublattice_carrier_iff (x : L) :
    (x : V) ∈ L.evenSublattice.carrier ↔ Even (L.integralNorm x) := by
  rw [evenSublattice_carrier, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := L.carrier.injective_subtype hyx
    exact (L.mem_evenSubmodule_iff x).mp (h ▸ hy)
  · intro hx
    exact ⟨x, (L.mem_evenSubmodule_iff x).mpr hx, rfl⟩

/-- The even sublattice retains the original rational bilinear form. -/
@[simp]
theorem evenSublattice_form : L.evenSublattice.form = L.form := by
  unfold evenSublattice
  exact restrictFull_form ..

/-- Every vector of the even sublattice has even integral norm. -/
theorem isEven_evenSublattice : L.evenSublattice.IsEven := by
  rw [L.evenSublattice.isEven_iff_forall_norm]
  intro x
  have hx : (x : V) ∈ L.evenSubmodule.map L.carrier.subtype := by
    simpa only [evenSublattice_carrier] using x.property
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  obtain ⟨z, hz⟩ := (L.even_integralNorm_iff y).mp ((L.mem_evenSubmodule_iff y).mp hy)
  refine ⟨z, ?_⟩
  rw [norm_apply, evenSublattice_form, ← hyx, ← norm_apply]
  exact hz

/-- The even sublattice is nondegenerate whenever the original lattice is nondegenerate. -/
instance instIsNondegenerateEvenSublattice [L.IsNondegenerate] :
    L.evenSublattice.IsNondegenerate := by
  unfold evenSublattice
  infer_instance

/-- Passing to the full even sublattice preserves all three signature indices. -/
@[simp]
theorem evenSublattice_signature : L.evenSublattice.signature = L.signature := by
  have hr : L.evenSublattice.radical = L.radical := by
    ext x
    simp only [mem_radical_iff, evenSublattice_form]
  simp only [signature, sigPos, sigNull, sigNeg, evenSublattice_form]
  rw [hr]

/-- The norm-parity kernel has finite quotient, through the finite range in `ℤ/2`. -/
instance instFiniteQuotientEvenSubmodule : Finite (L ⧸ L.evenSubmodule) :=
  Finite.of_equiv (LinearMap.range L.normParity.toIntLinearMap)
    L.normParity.toIntLinearMap.quotKerEquivRange.symm.toEquiv

/-- Norm parity is surjective when the lattice is not even. -/
theorem normParity_surjective_of_not_isEven (hL : ¬ L.IsEven) :
    Function.Surjective L.normParity := by
  have hn : ¬ ∀ x : L, Even (L.integralNorm x) := by
    intro h
    exact hL (L.isEven_iff_forall_norm.mpr fun x ↦ (L.even_integralNorm_iff x).mp (h x))
  push Not at hn
  obtain ⟨w, hw⟩ := hn
  have hw' : L.normParity w = 1 := by
    rw [normParity_apply, ZMod.intCast_eq_one_iff_odd]
    exact hw
  intro z
  fin_cases z
  · exact ⟨0, map_zero _⟩
  · exact ⟨w, hw'⟩

/-- For an odd lattice, norm parity identifies the quotient by the even submodule with `ℤ/2`. -/
noncomputable def evenSubmoduleQuotientEquiv (hL : ¬ L.IsEven) :
    (L ⧸ L.evenSubmodule) ≃ₗ[ℤ] ZMod 2 :=
  L.normParity.toIntLinearMap.quotKerEquivOfSurjective
    (L.normParity_surjective_of_not_isEven hL)

/-- The quotient equivalence evaluates a lattice-vector class by its norm parity. -/
@[simp]
theorem evenSubmoduleQuotientEquiv_apply_mk (hL : ¬ L.IsEven) (x : L) :
    L.evenSubmoduleQuotientEquiv hL (Submodule.Quotient.mk x) = L.normParity x :=
  LinearMap.quotKerEquivOfSurjective_apply_mk ..

/-- The even submodule has index two in every odd integral lattice. -/
theorem natCard_quotient_evenSubmodule (hL : ¬ L.IsEven) :
    Nat.card (L ⧸ L.evenSubmodule) = 2 := by
  rw [Nat.card_congr (L.evenSubmoduleQuotientEquiv hL).toEquiv]
  exact Nat.card_zmod 2

/-- The relative index of the even sublattice in the lattice equals the cardinality of the
quotient by the even-norm submodule. -/
theorem relIndex_evenSublattice_eq_natCard_quotient :
    L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup =
      Nat.card (L ⧸ L.evenSubmodule) := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, ← L.evenSublattice_carrier_submoduleOf]
  exact Nat.card_congr (AddSubgroup.quotientEquivOfEq
    (Submodule.toAddSubgroup_submoduleOf L.evenSublattice.carrier L.carrier).symm)

/-- The even sublattice has index at most two in the lattice: it is the kernel of norm parity. -/
theorem relIndex_evenSublattice_le_two :
    L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup ≤ 2 := by
  rw [L.relIndex_evenSublattice_eq_natCard_quotient, evenSubmodule,
    Nat.card_congr L.normParity.toIntLinearMap.quotKerEquivRange.toEquiv]
  exact (Nat.card_le_card_of_injective _ Subtype.coe_injective).trans (Nat.card_zmod 2).le

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

end TauCeti.IntegralLattice
