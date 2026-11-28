/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.Data.ZMod.Units
import TauCeti.FieldTheory.Galois.Restriction

/-!
# Real cyclotomic subfields and odd-order Frobenius

Inside a cyclotomic field of level `N`, the real subfield of level `m ∣ N` is fixed by the
units reducing to `±1` modulo `m`. At a dyadic level `m`, the corresponding quotient of units
is a `2`-group. Thus if an intermediate field contains this real subfield, an odd-order signed
Frobenius in the intermediate field forces the prime to be `±1` modulo `m`.

The construction uses Mathlib's `IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply`
and the description of the maximal real subfield by `ζ ↦ ζ⁻¹` in
`TauCeti.IsCyclotomicExtension.Rat.toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one`.
For the cyclotomic restriction description see Washington, *Introduction to Cyclotomic Fields*,
Chapter 3.
-/

public section

open IntermediateField NumberField _root_.IsCyclotomicExtension.Rat

namespace TauCeti.IsCyclotomicExtension.Rat

variable {N m : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L]
  [_root_.IsCyclotomicExtension {N} ℚ L]

/-- The real subfield of level `m ∣ N` inside the `N`-th cyclotomic field. Its fixing group is the
preimage of `{±1}` under reduction of cyclotomic exponents from `N` to `m`. -/
noncomputable def realCyclotomicSubfield (h : m ∣ N) : IntermediateField ℚ L :=
  fixedField ((Subgroup.zpowers (-1 : (ZMod m)ˣ)).comap
    ((ZMod.unitsMap h).comp (galEquivZMod N L).toMonoidHom))

/-- The fixing subgroup of the real subfield at level `m` is the preimage of `{±1}` under
reduction of cyclotomic exponents from `N` to `m`. -/
theorem fixingSubgroup_realCyclotomicSubfield (h : m ∣ N) :
    (realCyclotomicSubfield (L := L) h).fixingSubgroup =
      (Subgroup.zpowers (-1 : (ZMod m)ˣ)).comap
        ((ZMod.unitsMap h).comp (galEquivZMod N L).toMonoidHom) := by
  have := _root_.IsCyclotomicExtension.isGalois {N} ℚ L
  rw [realCyclotomicSubfield, fixingSubgroup_fixedField]

/-- An automorphism fixes the real subfield at level `m` exactly when its exponent reduces to a
sign modulo `m`. -/
theorem mem_fixingSubgroup_realCyclotomicSubfield_iff (h : m ∣ N) (σ : Gal(L/ℚ)) :
    σ ∈ (realCyclotomicSubfield h).fixingSubgroup ↔
      ZMod.unitsMap h (galEquivZMod N L σ) = 1 ∨
        ZMod.unitsMap h (galEquivZMod N L σ) = -1 := by
  rw [fixingSubgroup_realCyclotomicSubfield]
  simp

/-- The pointwise form of `mem_fixingSubgroup_realCyclotomicSubfield_iff`. This is the simp
normal form, since `IntermediateField.mem_fixingSubgroup_iff` is a simp lemma. -/
@[simp]
theorem forall_eq_self_on_realCyclotomicSubfield_iff (h : m ∣ N) (σ : Gal(L/ℚ)) :
    (∀ x ∈ realCyclotomicSubfield h, σ x = x) ↔
      ZMod.unitsMap h (galEquivZMod N L σ) = 1 ∨
        ZMod.unitsMap h (galEquivZMod N L σ) = -1 := by
  rw [← IntermediateField.mem_fixingSubgroup_iff, mem_fixingSubgroup_realCyclotomicSubfield_iff]

/-- An element lies in the real subfield at level `m` exactly when it is fixed by every
automorphism whose exponent reduces to a sign modulo `m`. -/
theorem mem_realCyclotomicSubfield_iff (h : m ∣ N) (x : L) :
    x ∈ realCyclotomicSubfield h ↔ ∀ σ : Gal(L/ℚ),
      (ZMod.unitsMap h (galEquivZMod N L σ) = 1 ∨
        ZMod.unitsMap h (galEquivZMod N L σ) = -1) → σ x = x := by
  rw [realCyclotomicSubfield, IntermediateField.mem_fixedField_iff]
  simp

/-- Containment of the real subfield at level `m` can be checked on the fixing subgroup of the
larger field. -/
theorem realCyclotomicSubfield_le_iff (h : m ∣ N) (E : IntermediateField ℚ L) :
    realCyclotomicSubfield h ≤ E ↔ ∀ σ ∈ E.fixingSubgroup,
      ZMod.unitsMap h (galEquivZMod N L σ) = 1 ∨
        ZMod.unitsMap h (galEquivZMod N L σ) = -1 := by
  have := _root_.IsCyclotomicExtension.isGalois {N} ℚ L
  rw [← IsGalois.fixedField_fixingSubgroup (realCyclotomicSubfield h),
    IsGalois.fixedField_le_iff_fixingSubgroup_le]
  simp only [IsConcreteLE.le_iff, mem_fixingSubgroup_realCyclotomicSubfield_iff]

/-- The real subfield of level `m` is the image of the maximal real subfield of an embedded
`m`-th cyclotomic field. -/
theorem realCyclotomicSubfield_eq_map_maximalRealSubfield (h : m ∣ N)
    (F : IntermediateField ℚ L) [_root_.IsCyclotomicExtension {m} ℚ F] :
    realCyclotomicSubfield h = ((maximalRealSubfield F).toIntermediateField
      (K := ℚ) fun x ↦ SubfieldClass.ratCast_mem _ x).map (IsScalarTower.toAlgHom ℚ F L) := by
  have := _root_.IsCyclotomicExtension.isGalois {N} ℚ L
  have := _root_.IsCyclotomicExtension.isGalois {m} ℚ F
  have : NeZero m := ⟨fun hm ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (hm ▸ h))⟩
  let H := Subgroup.zpowers ((galEquivZMod m F).symm (-1))
  have hH (σ : Gal(L/ℚ)) : σ.restrictNormal F ∈ H ↔
      ZMod.unitsMap h (galEquivZMod N L σ) = 1 ∨
        ZMod.unitsMap h (galEquivZMod N L σ) = -1 := by
    have hsq : ((galEquivZMod m F).symm (-1)) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    rw [Subgroup.mem_zpowers_iff_of_sq_eq_one hsq,
      ← galEquivZMod_restrictNormal_apply N L F h]
    simp only [← (galEquivZMod m F).apply_eq_iff_eq, map_one, MulEquiv.apply_symm_apply]
  have hreal : (maximalRealSubfield F).toIntermediateField
      (K := ℚ) (fun x ↦ SubfieldClass.ratCast_mem _ x) = fixedField H := by
    apply IntermediateField.toSubfield_injective
    simpa only [Subfield.toIntermediateField_toSubfield] using
      (toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one m F).symm
  rw [hreal, ← IsGalois.fixedField_fixingSubgroup (realCyclotomicSubfield h),
    fixingSubgroup_realCyclotomicSubfield, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
    IntermediateField.map_fixingSubgroup, fixingSubgroup_fixedField]
  exact Subgroup.ext fun σ ↦ by
    simpa only [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_zpowers_neg_one_iff,
      AlgEquiv.restrictNormalHom_apply_eq_restrictNormal] using hH σ

/-- An automorphism that has odd order on `E` has exponent `±1` modulo the dyadic level of
any real cyclotomic subfield contained in `E`. -/
theorem unitsMap_eq_one_or_neg_one_of_odd_orderOf_restrictNormal {n : ℕ} (h : 2 ^ (n + 1) ∣ N)
    (E : IntermediateField ℚ L) [Normal ℚ E] (hE : realCyclotomicSubfield h ≤ E)
    (σ : Gal(L/ℚ)) (hodd : Odd (orderOf (σ.restrictNormal E))) :
    ZMod.unitsMap h (galEquivZMod N L σ) = 1 ∨ ZMod.unitsMap h (galEquivZMod N L σ) = -1 := by
  let r := orderOf (σ.restrictNormal E)
  let u := ZMod.unitsMap h (galEquivZMod N L σ)
  have hfix : σ ^ r ∈ E.fixingSubgroup := by
    rw [← restrictNormalHom_ker, MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one (σ.restrictNormal E)
  have hu : u ^ r ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 1)))ˣ) := by
    have hs := (realCyclotomicSubfield_le_iff h E).mp hE _ hfix
    simpa only [Subgroup.mem_zpowers_neg_one_iff, u, map_pow] using hs
  have hord : orderOf u ∣ 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ
      Nat.prime_two, Nat.reduceSub, mul_one] using orderOf_dvd_natCard u
  -- Taking the odd power is invertible on the dyadic units.
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime
    ((hodd.coprime_two_right.pow_right n).coprime_dvd_right hord)
  have hus : u ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 1)))ˣ) := hk ▸ Subgroup.pow_mem _ hu k
  exact Subgroup.mem_zpowers_neg_one_iff.mp hus

/-- If the Artin image of `-p` in `E` has odd order and `E` contains the real subfield of level
`2 ^ (n + 2)`, then `p` is `±1` at that level. For a prime `p` coprime to `N`, this Artin image is
complex conjugation times arithmetic Frobenius. -/
theorem natCast_eq_one_or_neg_one_of_odd_orderOf_restrictNormal {n p : ℕ} (h : 2 ^ (n + 2) ∣ N)
    (hp : p.Coprime N) (E : IntermediateField ℚ L) [Normal ℚ E]
    (hE : realCyclotomicSubfield h ≤ E)
    (hodd : Odd (orderOf (((galEquivZMod N L).symm (-ZMod.unitOfCoprime p hp)).restrictNormal E))) :
    (p : ZMod (2 ^ (n + 2))) = 1 ∨ (p : ZMod (2 ^ (n + 2))) = -1 := by
  have hs := unitsMap_eq_one_or_neg_one_of_odd_orderOf_restrictNormal h E hE _ hodd
  rw [MulEquiv.apply_symm_apply, ZMod.unitsMap_neg, ZMod.unitsMap_unitOfCoprime, Units.ext_iff,
    Units.ext_iff] at hs
  simpa only [Units.val_neg, ZMod.coe_unitOfCoprime, Units.val_one, neg_eq_iff_eq_neg, neg_neg,
    or_comm] using hs

end TauCeti.IsCyclotomicExtension.Rat
