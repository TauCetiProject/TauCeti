/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
public import TauCeti.RingTheory.ClassGroup.Basic
import TauCeti.RingTheory.DedekindDomain.Factorization
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# The rank of the S-unit group

For a Dedekind domain with finite class group, the valuations of the S-units form a
finite-index subgroup of the integer tuples indexed by a finite set S of primes. Consequently,
the rank of the S-unit group is the rank of the ordinary unit group plus the cardinality of S.
This supplies the rank calculation for the unit lattices used in norm-index computations.

We use Mathlib's `Set.unit` and the valuation map `Set.unitValuation`. The finite-index
assertion comes from raising a fractional ideal supported on S to the class number: it then
has a generator which is an S-unit.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4 (the S-unit lattices).
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace TauCeti

noncomputable section

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- If `n` annihilates the class group, every tuple of S-valuations raised to `n` is the
valuation of an S-unit. -/
theorem pow_mem_range_unitValuation (S : Set (HeightOneSpectrum R)) [Finite S]
    (n : ℕ) (hn : ∀ c : ClassGroup R, c ^ n = 1) (f : S → Multiplicative ℤ) :
    f ^ n ∈ (Set.unitValuation S K).range := by
  classical
  let := Fintype.ofFinite S
  let I : (FractionalIdeal R⁰ K)ˣ :=
    ∏ v : S, v.val.unitOfPrime K ^ (-Multiplicative.toAdd (f v))
  have hcount (w : HeightOneSpectrum R) :
      FractionalIdeal.count K w (I : FractionalIdeal R⁰ K) =
        if h : w ∈ S then -Multiplicative.toAdd (f ⟨w, h⟩) else 0 := by
    simp only [I, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      HeightOneSpectrum.coe_unitOfPrime]
    rw [FractionalIdeal.count_prod]
    · simp only [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal]
      by_cases hw : w ∈ S
      · rw [Finset.sum_eq_single (⟨w, hw⟩ : S)]
        · simp [hw]
        · intro v _ hv
          have hvw : v.val ≠ w := fun h => hv (Subtype.ext h)
          simp [hvw]
        · simp
      · have hne : ∀ v : S, v.val ≠ w := fun v h => hw (h ▸ v.property)
        simp [hw, hne]
    · intro v _
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)
  have hprincipal : ClassGroup.mk K (I ^ n) = 1 := by
    rw [map_pow]
    exact hn _
  obtain ⟨u, hu⟩ := ClassGroup.mk_eq_one_iff_exists.mp hprincipal
  have huval (w : HeightOneSpectrum R) :
      Multiplicative.toAdd (w.valuationOfNeZero u) =
        if h : w ∈ S then (n : ℤ) * Multiplicative.toAdd (f ⟨w, h⟩)
          else 0 := by
    have h := congrArg (fun J : (FractionalIdeal R⁰ K)ˣ =>
      FractionalIdeal.count K w (J : FractionalIdeal R⁰ K)) hu
    rw [FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation,
      ← HeightOneSpectrum.valuationOfNeZero_eq, Units.val_pow_eq_pow_val,
      FractionalIdeal.count_pow, hcount] at h
    -- `log` reads the integer in the nonzero valuation's `Multiplicative` tag.
    simp only [WithZero.log, WithZero.recZeroCoe_coe] at h
    split_ifs at h ⊢ <;> linarith
  have huS : u ∈ S.unit K := by
    apply (Set.mem_unit_iff S K).mpr
    intro w hw
    rw [← HeightOneSpectrum.valuationOfNeZero_eq_one_iff]
    apply Multiplicative.toAdd.injective
    simpa [hw] using huval w
  refine ⟨⟨u, huS⟩, ?_⟩
  apply funext
  intro v
  apply Multiplicative.toAdd.injective
  simpa [Set.unitValuation_apply, v.property, Int.toAdd_pow, mul_comm] using huval v.val

/-- For a finite set S and finite class group, the S-unit valuation lattice has finite index
in the integer tuples on S. -/
theorem finiteIndex_range_unitValuation [Finite (ClassGroup R)]
    (S : Set (HeightOneSpectrum R)) [Finite S] :
    (Set.unitValuation S K).range.FiniteIndex := by
  have hn : Nat.card (ClassGroup R) ≠ 0 := Nat.card_pos.ne'
  have : (powMonoidHom (Nat.card (ClassGroup R)) :
      (S → Multiplicative ℤ) →* (S → Multiplicative ℤ)).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ hn
  exact Subgroup.finiteIndex_of_le (H := (powMonoidHom (Nat.card (ClassGroup R)) :
    (S → Multiplicative ℤ) →* (S → Multiplicative ℤ)).range) (by
      rintro _ ⟨f, rfl⟩
      exact pow_mem_range_unitValuation R K S _ (fun _ => pow_card_eq_one') f)

/-- The S-unit rank is the ordinary unit rank plus the number of allowed primes, provided
the class group is finite and the ordinary units are finitely generated. -/
theorem finrank_sUnits [Finite (ClassGroup R)] [Monoid.FG Rˣ]
    (S : Set (HeightOneSpectrum R)) [Finite S] :
    Module.finrank ℤ (Additive (S.unit K)) =
      Module.finrank ℤ (Additive Rˣ) + Nat.card S := by
  classical
  let := Fintype.ofFinite S
  let f := (Set.unitValuation S K).toAdditive.toIntLinearMap
  let e : Additive (S → Multiplicative ℤ) ≃ₗ[ℤ] (S → ℤ) :=
    (MulEquiv.funMultiplicative S ℤ).symm.toAdditiveLeft.toIntLinearEquiv
  have : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) :=
    Module.Finite.equiv e.symm
  have : Module.IsTorsionFree ℤ (Additive (S → Multiplicative ℤ)) :=
    e.injective.moduleIsTorsionFree _ e.map_smul
  have : (Set.unitValuation S K).range.toAddSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_toAddSubgroup_iff.mpr (finiteIndex_range_unitValuation R K S)
  have hrange : Module.finrank ℤ f.range = Nat.card S := by
    have h := AddSubgroup.finrank_eq_of_finiteIndex
      (Set.unitValuation S K).range.toAddSubgroup
    exact h.trans (e.finrank_eq.trans (by simp [Nat.card_eq_fintype_card]))
  let eker : f.ker ≃+ Additive (Set.unitValuation S K).ker :=
    -- The subgroup wrappers put `Additive` on opposite sides of the subtype. Both maps
    -- preserve the underlying unit and use the defining kernel equation.
    { toFun := fun x => .ofMul ⟨x.val.toMul, x.property⟩
      invFun := fun x => ⟨.ofMul x.toMul.val, x.toMul.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let ek := (MulEquiv.subgroupCongr (Set.unitValuation_ker S K)).trans
    ((Subgroup.subgroupOfEquivOfLe (Set.unit_mono K S.empty_subset)).trans
      (Set.unitEmptyEquivUnits K))
  have hker : Module.finrank ℤ f.ker = Module.finrank ℤ (Additive Rˣ) :=
    (eker.trans ek.toAdditive).toIntLinearEquiv.finrank_eq
  have : Module.Finite ℤ (Additive (S.unit K)) := Module.Finite.iff_addGroup_fg.mpr
    (AddGroup.fg_iff_mul_fg.mpr inferInstance)
  have h := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq, hrange, hker] at h
  exact h.symm.trans (Nat.add_comm _ _)

end

end TauCeti
