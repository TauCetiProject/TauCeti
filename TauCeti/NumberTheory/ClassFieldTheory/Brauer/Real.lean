/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.FieldTheory.GaloisCohomology.Cyclic
public import TauCeti.FieldTheory.Galois.Complex
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.RingTheory.Norm.Complex
public import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Order.Ring.Units
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The cohomological Brauer invariant of the reals

This file computes `Br ℝ`, the continuous-cohomology Brauer group used by class formations,
via `H²(Gal(ℂ/ℝ), ℂˣ)`. The cyclic norm quotient for `ℂ/ℝ` is the real sign quotient, so
`Br ℝ ≃+ ZMod 2`. The real invariant embeds it in `ℚ/ℤ`, sending its nonzero class to `1/2`.

`realClass` carries a real unit to its cyclic class at complex conjugation. Positive units
represent zero, and negative units represent the unique nonzero class. This characterizes the
normalization without any choice of a generator beyond complex conjugation.

The comparison with relative cohomology uses an identification of a separable closure of `ℝ`
with `ℂ`. The invariant itself is independent of that identification: `realInv_apply` describes
it solely by whether a Brauer class is zero. The complex Brauer group is trivial by the general
`subsingleton_Br_of_isSepClosed` instance and `Complex.isAlgClosed`.

## Main definitions and results

* `realBrEquivRelative`: comparison with the relative cohomology of `ℂ/ℝ`.
* `realInvEquiv`: the identification `Br ℝ ≃+ ZMod 2`.
* `realInv`: the injective real invariant with two-torsion image in `ℚ/ℤ`.
* `realInv_realClass`: the invariant of a real cyclic class, zero or `1/2` according to sign.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1.
-/

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

private def realNormQuotientEquiv : Additive (ℝˣ ⧸ normGroup ℝ ℂ) ≃+ ZMod 2 := by
  have hg : ∀ u : ℤˣ, u ∈ Subgroup.zpowers (-1 : ℤˣ) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hc : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let e : ℝˣ ⧸ normGroup ℝ ℂ ≃* ℤˣ := normGroup_real_complex ▸ Units.signEquiv ℝ
  exact (e.trans (zmodMulEquivOfGenerator hg hc).symm).toAdditiveLeft

/-- The continuous-cohomology Brauer group of `ℝ` agrees with the relative cohomology of
`ℂ/ℝ`, using an identification of the separable closure with `ℂ`.

The group is finite, so its Krull topology is discrete. The coefficient topology on `ℂˣ` used
in the comparison is discrete, as required for Galois cohomology. -/
def realBrEquivRelative :
    Br ℝ ≃+ groupCohomology.H2 (Rep.ofMulDistribMulAction (ℂ ≃ₐ[ℝ] ℂ) ℂˣ) := by
  letI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  let eC := IsSepClosure.equiv ℝ (SeparableClosure ℝ) ℂ
  letI : Finite (AbsoluteGaloisGroup ℝ) :=
    Finite.of_equiv (ℂ ≃ₐ[ℝ] ℂ) eC.autCongr.toEquiv.symm
  letI : TopologicalSpace (Additive ℂˣ) := ⊥
  letI : DiscreteTopology (Additive ℂˣ) := ⟨rfl⟩
  letI : ContinuousSMul (ℂ ≃ₐ[ℝ] ℂ) (Additive ℂˣ) := ⟨continuous_of_discreteTopology⟩
  let φ : (ℂ ≃ₐ[ℝ] ℂ) ≃ₜ* AbsoluteGaloisGroup ℝ :=
    { eC.autCongr.symm with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let e : UnitsCoeff ℝ ≃+ Additive ℂˣ :=
    (Units.mapEquiv eC.toRingEquiv.toMulEquiv).toAdditive
  have he : ∀ (h : ℂ ≃ₐ[ℝ] ℂ) (m : UnitsCoeff ℝ), e (φ h • m) = h • e m := by
    intro h m
    apply Additive.toMul.injective
    apply Units.ext
    -- The action on units is evaluation by the field automorphism. After taking values,
    -- `Units.mapEquiv` and the additive type tags reduce to the underlying field map.
    change eC ((eC.autCongr.symm h) (m.toMul : SeparableClosure ℝ)) =
      h (eC (m.toMul : SeparableClosure ℝ))
    simp [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]
  exact (unitsRepH2Equiv ℝ).symm.trans
    ((ContCohomology.explicitMap2Equiv (AbsoluteGaloisGroup ℝ) (UnitsCoeff ℝ)
      (ℂ ≃ₐ[ℝ] ℂ) (Additive ℂˣ) φ e continuous_of_discreteTopology
      continuous_of_discreteTopology he).trans
      (ContCohomology.explicitH2IsoGroupCohomology (ℂ ≃ₐ[ℝ] ℂ) (Additive ℂˣ)))

/-- The cyclic class of a real unit, at complex conjugation, in the cohomological Brauer group. -/
def realClass : Additive ℝˣ →+ Br ℝ :=
  realBrEquivRelative.symm.toAddMonoidHom.comp
    (cyclicClass ((Subgroup.eq_top_iff' _).mp zpowers_conjAe_eq_top))

/-- The relative comparison sends a real cyclic class to the class at complex conjugation. -/
@[simp] theorem realBrEquivRelative_realClass (a : Additive ℝˣ) :
    realBrEquivRelative (realClass a) =
      cyclicClass ((Subgroup.eq_top_iff' _).mp zpowers_conjAe_eq_top) a := by
  simp [realClass]

/-- Every real Brauer class is represented by a real unit. -/
theorem realClass_surjective : Function.Surjective realClass :=
  realBrEquivRelative.symm.surjective.comp
    (cyclicClass_surjective ((Subgroup.eq_top_iff' _).mp zpowers_conjAe_eq_top))

/-- A real cyclic class vanishes exactly when its representing unit is positive. -/
@[simp] theorem realClass_eq_zero_iff (a : ℝˣ) :
    realClass (Additive.ofMul a) = 0 ↔ 0 < (a : ℝ) := by
  -- Unbundle the additive homomorphism composition defining `realClass`.
  change realBrEquivRelative.symm
    (cyclicClass ((Subgroup.eq_top_iff' _).mp zpowers_conjAe_eq_top) (Additive.ofMul a)) = 0 ↔ _
  rw [map_eq_zero_iff _ realBrEquivRelative.symm.injective, cyclicClass_eq_zero_iff,
    normGroup_real_complex, Units.mem_posSubgroup]

/-- The real cohomological Brauer group is the two-element sign group. -/
def realInvEquiv : Br ℝ ≃+ ZMod 2 :=
  realBrEquivRelative.trans
    ((cyclicNormQuotientEquiv ((Subgroup.eq_top_iff' _).mp zpowers_conjAe_eq_top)).symm.trans
      realNormQuotientEquiv)

/-- The real Brauer invariant, normalized to send the nonzero class to `1/2`. -/
def realInv : Br ℝ →+ AddCircle (1 : ℚ) :=
  (ZMod.toRatAddCircle 2).comp realInvEquiv.toAddMonoidHom

/-- The real invariant detects every Brauer class. -/
theorem realInv_injective : Function.Injective realInv :=
  (ZMod.toRatAddCircle_injective 2).comp realInvEquiv.injective

/-- The image of the real invariant is exactly the two-torsion of `ℚ/ℤ`. -/
theorem range_realInv :
    Set.range realInv = (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) :
      Set (AddCircle (1 : ℚ))) := by
  rw [realInv, AddMonoidHom.coe_comp, Set.range_comp, AddEquiv.coe_toAddMonoidHom,
    realInvEquiv.surjective.range_eq, Set.image_univ, ← AddMonoidHom.coe_range,
    ZMod.toRatAddCircle_range]
  norm_num

open scoped Classical in
/-- The real invariant is intrinsically determined by whether the class vanishes. -/
theorem realInv_apply (x : Br ℝ) :
    realInv x = if x = 0 then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  -- Unbundle the composition defining the invariant before computing in `ZMod 2`.
  change ZMod.toRatAddCircle 2 (realInvEquiv x) = _
  split_ifs with hx
  · simp [hx]
  · have hne : realInvEquiv x ≠ 0 := by
      intro h
      exact hx (realInvEquiv.injective (h.trans (map_zero _).symm))
    have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rw [(h _).resolve_left hne]
    simpa using ZMod.toRatAddCircle_natCast 2 1

/-- Positive real cyclic classes have invariant zero, and negative ones have invariant `1/2`. -/
@[simp] theorem realInv_realClass (a : ℝˣ) :
    realInv (realClass (Additive.ofMul a)) =
      if 0 < (a : ℝ) then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  rw [realInv_apply, realClass_eq_zero_iff]

/-- The real invariant coordinates send a positive cyclic class to zero and a negative one
to one. -/
@[simp] theorem realInvEquiv_realClass (a : ℝˣ) :
    realInvEquiv (realClass (Additive.ofMul a)) = if 0 < (a : ℝ) then 0 else 1 := by
  classical
  apply ZMod.toRatAddCircle_injective 2
  -- Unbundle `realInv` to use its normalization after applying the injective embedding.
  change realInv (realClass (Additive.ofMul a)) = _
  rw [realInv_realClass]
  split_ifs
  · simp
  · simpa using (ZMod.toRatAddCircle_natCast 2 1).symm

end TauCeti.ClassFieldTheory
