/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.Regulator
public import TauCeti.NumberTheory.Height.SInteger
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
public import TauCeti.NumberTheory.NumberField.SUnits.Regulator
public import TauCeti.NumberTheory.NumberField.Units.SUnit.Basic
public import TauCeti.NumberTheory.NumberField.Units.SUnit.FundamentalSystem

/-!
# The `S`-units of `ℚ`

Let `S` be a finite set of finite places of `ℚ`, that is, of height-one primes of `𝓞 ℚ`, and for
`v ∈ S` let `p_v = Rat.HeightOneSpectrum.natGenerator v` be its rational prime. The `S`-units of
`ℚ` are the rationals `± ∏ p_v ^ n_v`. This file computes the general `S`-unit API of
`TauCeti.NumberField.SUnit` in this case:

* the torsion of the `S`-units is `{±1}`;
* the primes `p_v`, `v ∈ S`, form a fundamental system of `S`-units, of size
  `NumberField.Units.rank ℚ + #S = #S`;
* the `S`-regulator is `∏ v ∈ S, log p_v`. In the determinant formula the omitted infinite
  place is the only one, and the matrix of the logarithms `log |p_u|_v` is diagonal with entries
  `log |p_v|_v = -log p_v`.

For `S = {2}` this says that the `S`-units have rank `1`, the fundamental system `{2}` and the
`S`-regulator `log 2`. The `S`-unit `1 / p_v` has multiplicative height `p_v`, all of it carried
by the finite place `v`: its archimedean local factor is `1`.

## Main results

* `Rat.HeightOneSpectrum.finitePlace_mk_natGenerator`: `|p_v|_v = p_v⁻¹`.
* `Rat.HeightOneSpectrum.mulHeight₁_inv_natGenerator_eq_max_finitePlace` and
  `Rat.HeightOneSpectrum.mulHeight₁_inv_natGenerator`: the height of `1 / p_v` is its local factor
  at `v`, which is `p_v`.
* `TauCeti.NumberField.SUnit.mem_torsion_unit_rat_iff`: the torsion `S`-units of `ℚ` are `±1`.
* `TauCeti.NumberField.SUnit.finrank_unit_rat`: the `S`-units of `ℚ` have rank `#S`.
* `TauCeti.NumberField.SUnit.primeUnit`: the prime `p_v` as an `S`-unit, with
  `TauCeti.NumberField.SUnit.isFundSystem_primeUnit`: these primes form a fundamental system.
* `TauCeti.NumberField.SUnit.regulator_rat_eq_prod_log`: the `S`-regulator of `ℚ` is
  `∏ v ∈ S, log p_v`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5 (the `S`-units 1.5.10–1.5.13).
-/

public section

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace Rat.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The absolute value of the rational prime of `v` at the finite place `v` is its inverse. -/
theorem finitePlace_mk_natGenerator :
    FinitePlace.mk v (natGenerator v) = ((natGenerator v : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding', valuation_natGenerator,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  simp

/-- The absolute value of the inverse of the rational prime of `v` at the finite place `v` is
the prime. -/
theorem finitePlace_mk_inv_natGenerator :
    FinitePlace.mk v ((natGenerator v : ℚ)⁻¹) = natGenerator v := by
  rw [map_inv₀, finitePlace_mk_natGenerator, inv_inv]

/-- The height of the inverse of the rational prime `p` of `v` is carried by the finite place `v`:
`1 / p` is a `{v}`-integer whose archimedean local factor is `1`, so its height is its local factor
`max |1 / p|_v 1` at `v`. -/
theorem mulHeight₁_inv_natGenerator_eq_max_finitePlace :
    Height.mulHeight₁ ((natGenerator v : ℚ)⁻¹) =
      max (FinitePlace.mk v (natGenerator v : ℚ)⁻¹) 1 := by
  have hx : ((natGenerator v : ℚ)⁻¹) ∈
      (({v} : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ := by
    refine fun w hw ↦ ?_
    rw [map_inv₀, valuation_natGenerator_of_ne (by simpa using hw), inv_one]
  have hp : (1 : ℝ) ≤ natGenerator v := Nat.one_le_cast.mpr (prime_natGenerator v).one_le
  rw [mulHeight₁_eq_prod_of_mem_integer _ hx, Finset.prod_singleton,
    Fintype.prod_subsingleton _ Rat.infinitePlace, Rat.infinitePlace_apply, abs_inv,
    max_eq_right (by simpa using inv_le_one_of_one_le₀ hp), one_pow, one_mul]

/-- The inverse of the rational prime of `v` has multiplicative height equal to the prime. -/
theorem mulHeight₁_inv_natGenerator :
    Height.mulHeight₁ ((natGenerator v : ℚ)⁻¹) = natGenerator v := by
  rw [mulHeight₁_inv_natGenerator_eq_max_finitePlace, finitePlace_mk_inv_natGenerator,
    max_eq_left (Nat.one_le_cast.mpr (prime_natGenerator v).one_le)]

end Rat.HeightOneSpectrum

namespace TauCeti.NumberField.SUnit

noncomputable section

/-- The torsion `S`-units of `ℚ` are `1` and `-1`. -/
theorem mem_torsion_unit_rat_iff {S : Set (HeightOneSpectrum (𝓞 ℚ))} {x : S.unit ℚ} :
    x ∈ CommGroup.torsion (S.unit ℚ) ↔ ((x : ℚˣ) : ℚ) = 1 ∨ ((x : ℚˣ) : ℚ) = -1 := by
  rw [CommGroup.mem_torsion]
  refine Submonoid.isOfFinOrder_coe.symm.trans
    (Units.isOfFinOrder_val.symm.trans ⟨fun h ↦ ?_, ?_⟩)
  · rcases le_total 0 ((x : ℚˣ) : ℚ) with h0 | h0
    · exact Or.inl (h.eq_one h0)
    · exact Or.inr (h.eq_neg_one h0)
  · rintro (h | h) <;> rw [h]
    · exact IsOfFinOrder.one
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by norm_num⟩

/-- The `S`-units of `ℚ` have rank `#S`: the unit rank of `ℚ` is zero. -/
theorem finrank_unit_rat (S : Set (HeightOneSpectrum (𝓞 ℚ))) [Finite S] :
    Module.finrank ℤ (Additive (S.unit ℚ)) = Nat.card S := by
  rw [TauCeti.finrank_sUnits_numberField,
    NumberField.Units.rank_eq_zero_of_finrank_eq_one ℚ (Module.finrank_self ℚ), zero_add]

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- The rational prime of a place `v ∈ S`, as an `S`-unit of `ℚ`. -/
def primeUnit (v : S) : (S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ :=
  ⟨Units.mk0 (natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : ℚ)
      (Nat.cast_ne_zero.mpr (prime_natGenerator _).ne_zero),
    fun _ hw ↦ valuation_natGenerator_of_ne fun h ↦ hw (h ▸ v.2)⟩

@[simp]
theorem coe_primeUnit (v : S) :
    ((primeUnit S v : ℚˣ) : ℚ) = natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :=
  (rfl)

/-- The valuations at the places of `S` of the rational prime of `v ∈ S` are `-1` at `v` and `0`
elsewhere, written multiplicatively. -/
theorem unitValuation_primeUnit [DecidableEq (HeightOneSpectrum (𝓞 ℚ))] (v : S) :
    Set.unitValuation _ ℚ (primeUnit S v) = Pi.mulSingle v (Multiplicative.ofAdd (-1)) := by
  funext w
  rw [Set.unitValuation_apply, HeightOneSpectrum.valuationOfNeZero_eq_iff, coe_primeUnit]
  by_cases h : w = v
  · subst h
    simp [valuation_natGenerator, WithZero.exp]
  · rw [Pi.mulSingle_eq_of_ne h, valuation_natGenerator_of_ne (Subtype.coe_injective.ne h),
      WithZero.coe_one]

/-- The rational primes of the places of `S`, together with `±1`, generate the `S`-units of
`ℚ`. -/
theorem closure_range_primeUnit_sup_torsion_eq_top :
    Subgroup.closure (Set.range (primeUnit S)) ⊔
      CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ) = ⊤ := by
  classical
  refine eq_top_iff.mpr fun x _ ↦ ?_
  -- `z` is the product of prime powers with the valuations of `x` at the places of `S`.
  set f := Set.unitValuation _ ℚ x
  set z := ∏ v, primeUnit S v ^ (-Multiplicative.toAdd (f v))
  have hz : Set.unitValuation _ ℚ z = f := by
    simp only [z, map_prod, map_zpow, unitValuation_primeUnit, ← Pi.mulSingle_zpow]
    conv_rhs => rw [← Finset.univ_prod_mulSingle f]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [← ofAdd_zsmul]
    simp
  -- `x * z⁻¹` has valuation one at every place of `S`, so it is a unit of `𝓞 ℚ`, hence `±1`.
  have hker : x * z⁻¹ ∈ (Set.unitValuation _ ℚ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hz, mul_inv_cancel]
  rw [Set.unitValuation_ker, Subgroup.mem_subgroupOf] at hker
  obtain ⟨u, hu⟩ := Set.mem_unit_empty_iff ℚ |>.mp hker
  have ht : x * z⁻¹ ∈ CommGroup.torsion _ := by
    rw [mem_torsion_unit_rat_iff, ← hu, ← Rat.ringOfIntegersEquiv_apply_coe]
    rcases Int.isUnit_iff.mp (u.isUnit.map Rat.ringOfIntegersEquiv) with h | h <;> simp [h]
  have hzc : z ∈ Subgroup.closure (Set.range (primeUnit S)) :=
    Subgroup.prod_mem _ fun v _ ↦
      Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self v)) _
  have hx : z * (x * z⁻¹) = x := by rw [mul_comm x, mul_inv_cancel_left]
  exact hx ▸ Subgroup.mul_mem_sup hzc ht

/-- The rational primes of the places of `S` form a fundamental system of `S`-units of `ℚ`. -/
theorem isFundSystem_primeUnit :
    IsFundSystem (S : Set (HeightOneSpectrum (𝓞 ℚ))) (primeUnit S) where
  finite := inferInstance
  card_eq := by
    simp [NumberField.Units.rank_eq_zero_of_finrank_eq_one ℚ (Module.finrank_self ℚ)]
  closure_sup_torsion_eq_top := closure_range_primeUnit_sup_torsion_eq_top S

/-- **The `S`-regulator of `ℚ`** is the product of the logarithms of the rational primes of the
places of `S`. For `S = {2}` it is `log 2`. -/
theorem regulator_rat_eq_prod_log : regulator S = ∏ v ∈ S, Real.log (natGenerator v) := by
  classical
  let w' := Rat.infinitePlace
  have : IsEmpty {w : InfinitePlace ℚ // w ≠ w'} := ⟨fun w ↦ w.2 (Subsingleton.elim _ _)⟩
  rw [regulator_eq_abs_det (closure_range_primeUnit_sup_torsion_eq_top S) w'
    (Equiv.emptySum _ _).symm]
  -- The matrix of the determinant formula is diagonal, with entries `log |p_v|_v = -log p_v`.
  have hdiag : (Matrix.of fun i k ↦ Sum.elim (fun w : {w // w ≠ w'} ↦
      (w.1.mult : ℝ) * Real.log (w.1 ((primeUnit S i : ℚˣ) : ℚ)))
      (fun v : S ↦ Real.log (FinitePlace.mk v.1 ((primeUnit S i : ℚˣ) : ℚ)))
      ((Equiv.emptySum _ _).symm k)) =
      Matrix.diagonal fun v : S ↦ -Real.log (natGenerator (v : HeightOneSpectrum (𝓞 ℚ))) := by
    ext i k
    simp only [Matrix.of_apply, Equiv.emptySum_symm_apply, Sum.elim_inr, coe_primeUnit]
    by_cases h : i = k
    · subst h
      rw [Matrix.diagonal_apply_eq, finitePlace_mk_natGenerator, Real.log_inv]
    · rw [Matrix.diagonal_apply_ne _ h, (FinitePlace.mk_apply_eq_one_iff _ _).mpr
        (valuation_natGenerator_of_ne (Subtype.coe_injective.ne (Ne.symm h))), Real.log_one]
  rw [hdiag, Matrix.det_diagonal, Finset.abs_prod]
  simp only [abs_neg, abs_of_nonneg (Real.log_natCast_nonneg _)]
  exact Finset.prod_coe_sort S fun v ↦ Real.log (natGenerator v)

end

end TauCeti.NumberField.SUnit
