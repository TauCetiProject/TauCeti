/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.HahnSeries.PowerSeries
public import TauCeti.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic

/-!
# The algebra action, the product rule, and residues of `φⁿ dφ` for Laurent series

For an `R`-algebra `A`, the `R`-algebra structure on `A⸨X⸩` is the one inherited from `A⟦X⟧`
through `HahnSeries.ofPowerSeries`, so its scalar action is multiplication by the image of a
constant power series. This is propositionally, but not definitionally, equal to the coefficientwise
action `HahnSeries.instSMul` found by default.

The scalar tower `S → A⟦X⟧ → A⸨X⸩` for any commutative semiring `S` over which `A⟦X⟧` is an
algebra (in particular `S = R` and `S = A[X]`) is imported from
`TauCeti.RingTheory.HahnSeries.PowerSeries`; the tower over `R` is what
fraction-field constructions such as `IsFractionRing.algEquivOfAlgEquiv` require to extend an
`R`-algebra equivalence with `A⟦X⟧` to one with `A⸨X⸩`. This file shows that the algebra action
of `R` on `A⸨X⸩` agrees with the coefficientwise action, and records that, over a field `K`, a
nonzero Laurent series `f ∈ K⸨X⸩` has valuation `exp (-ord f)`, since its power series part is a
unit of `K⟦X⟧`. Consequently a field embedding `K → L`, applied to every coefficient, preserves
valuations.

The second part proves the product rule for the derivative of Laurent series,
`(f * g)' = f' * g + f * g'`. Mathlib defines `LaurentSeries.derivative` only as a linear map,
the first Hasse derivative; the product rule is what makes it a derivation, so that composing it
with a ring homomorphism into `R⸨X⸩` gives a derivation, as for Laurent expansions of functions.
It is reduced to the product rule for power series by writing a Laurent series as a monomial
times a power series.

The third part computes the residue of the formal one-form `φ ^ n * φ' dX`
for any power series `φ` over a field and every integer `n`:
it is `(φ.order.toNat : k)` for `n = -1` and `0` otherwise. For `n ≠ -1` in characteristic zero,
`φ ^ n * φ'` is the derivative of `φ ^ (n + 1) / (n + 1)`; in characteristic `p` this fails when
`p ∣ n + 1`, and the proof uses
`PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative` instead. By linearity
this extends to every Laurent series: a substitution `X ↦ φ` multiplies the residue of `f(X) dX`
by `φ.order.toNat`, and in particular preserves the residue when `φ.order = 1`.

## Main results

* `TauCeti.LaurentSeries.coeff_algebraMap_mul`: multiplication by a constant of the algebra
  structure acts coefficientwise.
* `TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff`: the Laurent series coming from power series
  are those with no negative exponents.
* `TauCeti.laurentSeries_algebraMap_mul_eq_smul`: the algebra action agrees with the
  coefficientwise scalar action, and `TauCeti.laurentSeries_isScalarTower_algebra` transfers
  scalar towers from the coefficientwise action to the algebra action.
* `TauCeti.LaurentSeries.valuation_eq_exp_neg_order`: a nonzero Laurent series `f` has valuation
  `exp (-ord f)`; `TauCeti.LaurentSeries.valuation_coe` gives the same for a nonzero power series.
* `TauCeti.LaurentSeries.valuation_mapRingHom`: applying a field embedding to the coefficients
  preserves the valuation.
* `PowerSeries.order_coe` and `PowerSeries.orderTop_coe_of_ne_zero`: the order of a power series in
  `R⸨X⸩` agrees with its power series order.
* `LaurentSeries.derivative_mul`: the product rule for the derivative of Laurent series.
* `PowerSeries.coe_derivative` and `PowerSeries.coe_hasseDeriv`: the derivative and the Hasse
  derivatives of Laurent series extend those of power series.
* `LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le`: if `f` vanishes to order at least
  `m`, so does `f' - m X⁻¹ f`.
* `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative_eq_ite` and
  `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative`: the residue of `φ ^ n * φ'` for a power
  series `φ` is `φ.order.toNat` if `n = -1` and `0` otherwise (in particular `1` vs `0` when
  `φ.order = 1`).
* `LaurentSeries.coeff_neg_one_map_mul_derivative_eq_nsmul` and
  `LaurentSeries.coeff_neg_one_map_mul_derivative`: for a substitution `X ↦ φ`, the residue of
  `f(φ) φ'` is `φ.order.toNat • f.coeff (-1)` (and `f.coeff (-1)` when `φ.order = 1`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9.
-/

public section

open scoped LaurentSeries PowerSeries

namespace PowerSeries

open HahnSeries LaurentSeries

/-- The `WithTop ℤ`-valued order of a nonzero power series coerced to `R⸨X⸩` is
`(f.order.toNat : ℤ)`. -/
theorem orderTop_coe_of_ne_zero {R : Type*} [Semiring R] {f : R⟦X⟧} (hf : f ≠ 0) :
    (f : R⸨X⸩).orderTop = (f.order.toNat : ℤ) := by
  have hord : f.order = (f.order.toNat : ℕ∞) :=
    (ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hf)).symm
  refine orderTop_eq_of_le ?_ fun g hg ↦ ?_
  · rw [mem_support, coeff_coe]
    simpa using coeff_order hf
  · rw [mem_support, coeff_coe] at hg
    split_ifs at hg with hg0
    · exact (hg rfl).elim
    · have hle : f.order.toNat ≤ g.natAbs := by
        rw [← Nat.cast_le (α := ℕ∞), ← hord]
        exact order_le g.natAbs hg
      omega

/-- The integer order of a power series coerced to `R⸨X⸩` is `(f.order.toNat : ℤ)`. -/
@[simp]
theorem order_coe {R : Type*} [Semiring R] (f : R⟦X⟧) :
    (f : R⸨X⸩).order = f.order.toNat := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hf' : (f : R⸨X⸩) ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr hf
    exact WithTop.coe_inj.mp
      ((order_eq_orderTop_of_ne_zero hf').trans (orderTop_coe_of_ne_zero hf))

end PowerSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommSemiring R]

/-- Multiplying a Laurent series by a constant of the `R`-algebra structure on `R⸨X⸩` multiplies
each coefficient by that constant. -/
@[simp]
theorem coeff_algebraMap_mul (c : R) (f : R⸨X⸩) (n : ℤ) :
    (algebraMap R R⸨X⸩ c * f).coeff n = c * f.coeff n := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- A Laurent series is the image of a power series exactly when its coefficients at negative
exponents vanish. -/
theorem mem_range_ofPowerSeries_iff {f : R⸨X⸩} :
    f ∈ Set.range (HahnSeries.ofPowerSeries ℤ R) ↔ ∀ n < 0, f.coeff n = 0 := by
  refine ⟨?_, fun hf ↦ ⟨PowerSeries.mk fun n ↦ f.coeff n, ?_⟩⟩
  · rintro ⟨g, rfl⟩ n hn
    simp [PowerSeries.coeff_coe, hn]
  ext n
  rw [PowerSeries.coeff_coe]
  split_ifs with hn
  · exact (hf n hn).symm
  · rw [PowerSeries.coeff_mk, Int.natCast_natAbs, abs_of_nonneg (not_lt.mp hn)]

section Valuation

open HahnSeries PowerSeries WithZero

variable {K : Type*} [Field K]

/-- A unit of `K⟦X⟧`, that is a power series of nonzero constant coefficient, has valuation one
in `K⸨X⸩`. -/
theorem valuation_coe_of_isUnit {h : K⟦X⟧} (hh : IsUnit h) : Valued.v (h : K⸨X⸩) = 1 :=
  Valuation.Integers.one_of_isUnit' hh fun g ↦ (_root_.LaurentSeries.val_le_one_iff_eq_coe K _).mpr
    ⟨g, rfl⟩

/-- The power series part of a nonzero Laurent series over a division ring is a unit: its constant
coefficient is the leading coefficient. -/
theorem isUnit_powerSeriesPart {D : Type*} [DivisionRing D] {f : D⸨X⸩} (hf : f ≠ 0) :
    IsUnit f.powerSeriesPart := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    _root_.LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero, isUnit_iff_ne_zero]
  exact coeff_order_eq_zero.not.mpr hf

/-- A nonzero Laurent series `f` has valuation `exp (-ord f)`. -/
theorem valuation_eq_exp_neg_order {f : K⸨X⸩} (hf : f ≠ 0) : Valued.v f = exp (-f.order) := by
  nth_rw 1 [← f.single_order_mul_powerSeriesPart]
  rw [map_mul, valuation_coe_of_isUnit (isUnit_powerSeriesPart hf), mul_one,
    _root_.LaurentSeries.valuation_single_zpow]

/-- A nonzero power series `g` has valuation `exp (-ord g)` in `K⸨X⸩`. -/
theorem valuation_coe {g : K⟦X⟧} (hg : g ≠ 0) :
    Valued.v (g : K⸨X⸩) = exp (-(g.order.toNat : ℤ)) := by
  rw [valuation_eq_exp_neg_order ((map_ne_zero_iff _ ofPowerSeries_injective).mpr hg), order_coe]

/-- Applying a field embedding `σ : K →+* L` to the coefficients preserves the valuation. -/
@[simp]
theorem valuation_mapRingHom {L : Type*} [Field L] (σ : K →+* L) (f : K⸨X⸩) :
    Valued.v (mapRingHom σ f) = Valued.v f := by
  obtain rfl | hf := eq_or_ne f 0
  · simp only [map_zero]
  rw [valuation_eq_exp_neg_order hf,
    valuation_eq_exp_neg_order ((map_ne_zero_iff _ (mapRingHom_injective σ.injective)).mpr hf),
    mapRingHom_apply, order_map_of_injective f σ.injective]

end Valuation

end TauCeti.LaurentSeries

namespace TauCeti

/-- Truncating a Laurent series below an integer cutoff gives finite support. -/
theorem finite_support_truncLT {A : Type*} [Zero A] (a : ℤ) (f : A⸨X⸩) :
    (HahnSeries.truncLT a f).support.Finite := by
  apply (Set.finite_Ico f.order a).subset
  intro n hn
  rw [HahnSeries.support_truncLT] at hn
  exact ⟨HahnSeries.order_le_of_coeff_ne_zero hn.1, hn.2⟩

/-- Multiplication by a constant of the Laurent-series algebra structure agrees with the
coefficientwise scalar action, for Laurent series with coefficients in any `R`-algebra. -/
theorem laurentSeries_algebraMap_mul_eq_smul {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (c : R) (f : LaurentSeries A) :
    algebraMap R (LaurentSeries A) c * f = c • f := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, algebraMap_smul]

/-- A scalar tower `R → R⸨X⸩ → M` for the coefficientwise action of `R` on `R⸨X⸩`, which is the
one found by instance search, is also a scalar tower for the algebra action, since the two actions
agree. Derivations out of `R⸨X⸩` and Kähler differentials of `R⸨X⸩` use the algebra action. -/
instance laurentSeries_isScalarTower_algebra {R M : Type*} [CommSemiring R] [SMul R⸨X⸩ M]
    [SMul R M] [IsScalarTower R R⸨X⸩ M] :
    @IsScalarTower R R⸨X⸩ M Algebra.toSMul _ _ := by
  -- Specify the algebra action rather than the default coefficientwise action in the constructor.
  refine @IsScalarTower.mk R R⸨X⸩ M Algebra.toSMul _ _ ?_
  intro c f m
  rw [Algebra.smul_def, laurentSeries_algebraMap_mul_eq_smul, smul_assoc]

end TauCeti

namespace PowerSeries

open HahnSeries LaurentSeries

/-- The Hasse derivatives of Laurent series extend the Hasse derivatives of power series. -/
@[simp]
theorem coe_hasseDeriv {R : Type*} [Ring R] (k : ℕ) (f : R⟦X⟧) :
    ((PowerSeries.hasseDeriv k f : R⟦X⟧) : R⸨X⸩) = LaurentSeries.hasseDeriv R k (f : R⸨X⸩) := by
  ext i
  rw [LaurentSeries.hasseDeriv_coeff, coeff_coe, coeff_coe]
  rcases i with m | m
  · rw [Int.ofNat_eq_natCast, ← Nat.cast_add, Ring.choose_natCast]
    simp [show ¬(m : ℤ) < 0 by omega, show ¬(m : ℤ) + k < 0 by omega,
      show ((m : ℤ) + k).natAbs = m + k by omega]
  · simp only [Int.negSucc_lt_zero, ite_true]
    split_ifs with h
    · rw [smul_zero]
    · -- Here `0 ≤ i + k < k`, so the binomial coefficient vanishes.
      obtain ⟨j, hj⟩ : ∃ j : ℕ, Int.negSucc m + k = j :=
        ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
      rw [hj, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

/-- The derivative of Laurent series extends the derivative of power series. -/
@[simp]
theorem coe_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) :
    ((d⁄dX f : R⟦X⟧) : R⸨X⸩) = LaurentSeries.derivative R (f : R⸨X⸩) := by
  simpa only [hasseDeriv_one_apply, derivative_apply] using coe_hasseDeriv 1 f

end PowerSeries

namespace LaurentSeries

open HahnSeries

section Ring

variable {R : Type*} [Ring R]

/-- The product rule for a monomial over any ring:
`(c X ^ m * f)' = m c X ^ (m - 1) * f + c X ^ m * f'`. -/
theorem derivative_single_mul (m : ℤ) (c : R) (f : R⸨X⸩) :
    derivative R (single m c * f) = single (m - 1) (m * c) * f + single m c * derivative R f := by
  ext n
  simp only [derivative_apply, hasseDeriv_coeff, coeff_add, coeff_single_mul,
    Ring.choose_one_right]
  have h₁ : n - (m - 1) = n + 1 - m := by omega
  have h₂ : n - m + (1 : ℕ) = n + 1 - m := by omega
  simp only [h₁, h₂, ← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, ← add_zsmul]
  congr 1
  omega

/-- The derivative of `f` agrees with `m X⁻¹ f` up to a correction whose coefficient of `Xⁿ` is
`(n + 1 - m)` times the coefficient of `Xⁿ⁺¹` in `f`. -/
theorem coeff_derivative_sub_zsmul_single_mul (m n : ℤ) (f : R⸨X⸩) :
    (derivative R f - m • (single (-1) 1 * f)).coeff n =
      ((n + 1 - m : ℤ) : R) * f.coeff (n + 1) := by
  rw [coeff_sub, coeff_smul, coeff_single_mul, derivative_apply, hasseDeriv_coeff,
    Ring.choose_one_right, sub_neg_eq_add, one_mul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  rw [sub_mul]

end Ring

variable {R : Type*} [CommRing R]

/-- The product rule for a monomial times a power series:
`(c X ^ m * φ)' = m c X ^ (m - 1) * φ + c X ^ m * φ'`. -/
theorem derivative_single_mul_coe (m : ℤ) (c : R) (φ : R⟦X⟧) :
    derivative R (single m c * (φ : R⸨X⸩)) =
      single (m - 1) (m * c) * φ + single m c * ((d⁄dX φ : R⟦X⟧) : R⸨X⸩) := by
  rw [derivative_single_mul, ← PowerSeries.coe_derivative]

/-- **The product rule** for the derivative of Laurent series: `(f * g)' = f' * g + f * g'`. -/
theorem derivative_mul (f g : R⸨X⸩) :
    derivative R (f * g) = derivative R f * g + f * derivative R g := by
  -- Write `f = X ^ a * φ` and `g = X ^ b * ψ` with power series `φ` and `ψ`, so that
  -- `f * g = X ^ (a + b) * (φ * ψ)`, and use the product rule for power series.
  rw [← single_order_mul_powerSeriesPart f, ← single_order_mul_powerSeriesPart g]
  set a := f.order
  set b := g.order
  set φ := f.powerSeriesPart
  set ψ := g.powerSeriesPart
  have hab : (single (a + b) (1 : R) : R⸨X⸩) = single a 1 * single b 1 := by
    rw [single_mul_single, one_mul]
  have hfg : (single a (1 : R) * (φ : R⸨X⸩)) * (single b 1 * (ψ : R⸨X⸩)) =
      single (a + b) 1 * ((φ * ψ : R⟦X⟧) : R⸨X⸩) := by
    rw [PowerSeries.coe_mul, hab]
    ring
  -- The derivative of the monomial `X ^ (a + b)` splits as `(X ^ a)' X ^ b + X ^ a (X ^ b)'`.
  have hd : (single (a + b - 1) (((a + b : ℤ) : R) * 1) : R⸨X⸩) =
      single (a - 1) ((a : R) * 1) * single b 1 + single a 1 * single (b - 1) ((b : R) * 1) := by
    rw [single_mul_single, single_mul_single, show a - 1 + b = a + b - 1 by ring,
      show a + (b - 1) = a + b - 1 by ring, ← single_add]
    push_cast
    ring_nf
  simp only [hfg, derivative_single_mul_coe]
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.coe_add, PowerSeries.coe_mul]
  rw [hd, hab]
  ring

/-- **Differentiation lowers the order by at most one, with leading term `m X⁻¹ f`.** If `f` has
valuation at most `exp (-m)`, that is, vanishes to order at least `m`, then `f' - m X⁻¹ f` again
vanishes to order at least `m`. -/
theorem valuation_derivative_sub_zsmul_single_mul_le {K : Type*} [Field K] {m : ℤ} {f : K⸨X⸩}
    (hf : Valued.v f ≤ WithZero.exp (-m)) :
    Valued.v (derivative K f - m • (single (-1) 1 * f)) ≤ WithZero.exp (-m) := by
  rw [valuation_le_iff_coeff_lt_eq_zero] at hf ⊢
  intro n hn
  rw [coeff_derivative_sub_zsmul_single_mul]
  -- Below `m - 1` the coefficient of `f` vanishes; at `m - 1` the integer factor does.
  rcases lt_or_eq_of_le (show n + 1 ≤ m by omega) with h | h
  · rw [hf _ h, mul_zero]
  · simp [h]

end LaurentSeries

namespace TauCeti

open HahnSeries _root_.LaurentSeries PowerSeries

private theorem inv_pow_coe_X_pow_mul {k : Type*} [Field k] (u : k⟦X⟧)
    (hu0 : constantCoeff u ≠ 0) (e m : ℕ) : (((X ^ e * u : k⟦X⟧) : k⸨X⸩) ^ (m + 1))⁻¹ =
    single (-((e * (m + 1) : ℕ) : ℤ)) (1 : k) * ((u⁻¹ ^ (m + 1) : k⟦X⟧) : k⸨X⸩) := by
  refine inv_eq_of_mul_eq_one_right ?_
  have hX : (X ^ e * u) ^ (m + 1) * u⁻¹ ^ (m + 1) = X ^ (e * (m + 1)) := by
    rw [mul_pow, ← pow_mul, mul_assoc, ← mul_pow, mul_comm u,
      PowerSeries.inv_mul_cancel u hu0, one_pow, mul_one]
  rw [← coe_pow, mul_left_comm, ← coe_mul, hX, ofPowerSeries_X_pow]
  simp

private theorem inv_pow_mul_X_derivative_X_pow_mul {k : Type*} [Field k]
    (u : k⟦X⟧) (hvu : u⁻¹ * u = 1) (e m : ℕ) : u⁻¹ ^ (m + 1) * (X * d⁄dX (X ^ e * u)) =
    X ^ e * (e • u⁻¹ ^ m + X * (u⁻¹ ^ (m + 1) * d⁄dX u)) := by
  have hXe : (X : k⟦X⟧) * d⁄dX (X ^ e) = e • X ^ e := by
    rcases e with _ | d
    · simp
    · rw [derivative_pow, derivative_X, mul_one, nsmul_eq_mul, Nat.add_sub_cancel]
      ring
  calc u⁻¹ ^ (m + 1) * (X * d⁄dX (X ^ e * u))
      = u⁻¹ ^ m * (u⁻¹ * u) * (X * d⁄dX (X ^ e)) +
          X ^ e * (X * (u⁻¹ ^ (m + 1) * d⁄dX u)) := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pow_succ]
        ring
    _ = X ^ e * (e • u⁻¹ ^ m + X * (u⁻¹ ^ (m + 1) * d⁄dX u)) := by
        rw [hvu, mul_one, hXe, nsmul_eq_mul, nsmul_eq_mul]
        ring

private theorem coeff_neg_one_eq_coeff_zero_X_mul {R : Type*} [CommRing R] (f : R⸨X⸩) :
    f.coeff (-1) = (((X : R⟦X⟧) : R⸨X⸩) * f).coeff 0 := by
  rw [ofPowerSeries_X, coeff_single_mul, zero_sub, one_mul]

private theorem coeff_zero_single_neg_mul_X_pow_mul_coe {k : Type*} [Field k]
    (e m : ℕ) (f : k⟦X⟧) :
    (single (-((e * (m + 1) : ℕ) : ℤ)) (1 : k) *
      ((X ^ e * f : k⟦X⟧) : k⸨X⸩)).coeff 0 = coeff (e * m) f := by
  have hexp : -((e * (m + 1) : ℕ) : ℤ) + (e : ℤ) = -((e * m : ℕ) : ℤ) := by
    push_cast
    ring
  rw [coe_mul, ofPowerSeries_X_pow, ← mul_assoc, single_mul_single, one_mul, hexp]
  rw [coeff_single_mul, one_mul, zero_sub, neg_neg, coeff_coe,
    ite_eq_right (show ¬((e * m : ℕ) : ℤ) < 0 by omega), Int.natAbs_natCast]

end TauCeti

namespace PowerSeries

open HahnSeries LaurentSeries

/-- **The residue of `φ ^ n dφ` for a power series `φ` of arbitrary order.** Over a field `k`, for
any power series `φ : k⟦X⟧` and integer `n : ℤ`, the coefficient of `X⁻¹` in `φ ^ n * φ'` is
`(φ.order.toNat : k)` if `n = -1` and `0` otherwise. -/
theorem coeff_neg_one_coe_zpow_mul_derivative_eq_ite {k : Type*} [Field k] (φ : k⟦X⟧) (n : ℤ) :
    ((φ : k⸨X⸩) ^ n * LaurentSeries.derivative k (φ : k⸨X⸩)).coeff (-1) =
      if n = -1 then (φ.order.toNat : k) else 0 := by
  rcases eq_or_ne φ 0 with rfl | hφ0
  · simp
  rw [← coe_derivative]
  rcases n with m | m
  · -- For `n ≥ 0` the product is a power series.
    rw [Int.ofNat_eq_natCast, zpow_natCast, ← coe_pow, ← coe_mul, coeff_coe]
    simp [show (m : ℤ) ≠ -1 by omega]
  · -- Write `φ = X ^ e * u` with `e = φ.order.toNat` and `u = φ.divXPowOrder` a unit power series.
    set e := φ.order.toNat
    set u := φ.divXPowOrder
    have hu0 : constantCoeff u ≠ 0 := constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hφ0
    have hvu : u⁻¹ * u = 1 := PowerSeries.inv_mul_cancel u hu0
    have hφ : φ = X ^ e * u := (X_pow_order_mul_divXPowOrder (f := φ)).symm
    rw [TauCeti.coeff_neg_one_eq_coeff_zero_X_mul, hφ, zpow_negSucc,
      TauCeti.inv_pow_coe_X_pow_mul u hu0]
    have hproduct : ((X : k⟦X⟧) : k⸨X⸩) *
        (single (-((e * (m + 1) : ℕ) : ℤ)) (1 : k) * ((u⁻¹ ^ (m + 1) : k⟦X⟧) : k⸨X⸩) *
          ((d⁄dX (X ^ e * u) : k⟦X⟧) : k⸨X⸩)) =
        single (-((e * (m + 1) : ℕ) : ℤ)) (1 : k) *
          ((u⁻¹ ^ (m + 1) * (X * d⁄dX (X ^ e * u)) : k⟦X⟧) : k⸨X⸩) := by
      rw [coe_mul, coe_mul]
      ring
    rw [hproduct, TauCeti.inv_pow_mul_X_derivative_X_pow_mul u hvu,
      TauCeti.coeff_zero_single_neg_mul_X_pow_mul_coe, map_add, map_nsmul]
    rcases m with _ | m
    · simp
    · rw [ite_eq_right (show Int.negSucc (m + 1) ≠ -1 by omega)]
      let U : k⟦X⟧ˣ := ⟨u, u⁻¹, by rwa [mul_comm], hvu⟩
      simpa only [U, Units.val_mk, Units.inv_mk] using
        nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
          U e m

/-- **The residue of `φ ^ n dφ`.** For a power series `φ` of order one over a field, the
coefficient of `X⁻¹` in the Laurent series `φ ^ n * φ'` is `1` if `n = -1` and `0` otherwise.
Equivalently, the residue of `X ^ n dX` is unchanged by the substitution `X ↦ φ`. -/
theorem coeff_neg_one_coe_zpow_mul_derivative {k : Type*} [Field k] {φ : k⟦X⟧} (hφ : φ.order = 1)
    (n : ℤ) :
    ((φ : k⸨X⸩) ^ n * LaurentSeries.derivative k (φ : k⸨X⸩)).coeff (-1) =
      if n = -1 then 1 else 0 := by
  rw [coeff_neg_one_coe_zpow_mul_derivative_eq_ite, hφ, ENat.toNat_one, Nat.cast_one]

end PowerSeries

namespace LaurentSeries

open HahnSeries

/-- **The residue under a general-order substitution.** Let `ψ` be a ring endomorphism of `K⸨X⸩`
fixing the constants, sending power series to power series, and sending `X` to a power series `φ`,
such as the substitution `X ↦ φ`. Then the coefficient of `X⁻¹` in `ψ f * φ'` is `φ.order.toNat`
times the coefficient of `X⁻¹` in `f`. -/
theorem coeff_neg_one_map_mul_derivative_eq_nsmul {K : Type*} [Field K] (ψ : K⸨X⸩ →+* K⸨X⸩)
    (hC : ∀ c : K, ψ (C c) = C c)
    (hψ : ∀ f : K⸨X⸩, Valued.v f ≤ 1 → Valued.v (ψ f) ≤ 1) {φ : K⟦X⟧}
    (hX : ψ (single 1 1) = φ) (f : K⸨X⸩) :
    (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = φ.order.toNat • f.coeff (-1) := by
  -- Both sides vanish on power series.
  have base (f : K⸨X⸩) (hf : Valued.v f ≤ 1) :
      (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = φ.order.toNat • f.coeff (-1) := by
    obtain ⟨F, rfl⟩ := (val_le_one_iff_eq_coe K f).mp hf
    obtain ⟨G, hG⟩ := (val_le_one_iff_eq_coe K (ψ F)).mp (hψ F hf)
    rw [← hG, ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, PowerSeries.coeff_coe,
      PowerSeries.coeff_coe]
    simp
  -- Both sides agree on monomials, by the residue of `φ ^ j * φ'`.
  have mono (j : ℤ) (c : K) :
      (ψ (single j c) * derivative K (φ : K⸨X⸩)).coeff (-1) =
        φ.order.toNat • (single j c : K⸨X⸩).coeff (-1) := by
    -- The substitution sends `c X ^ j` to `c φ ^ j`.
    have h : ψ (single j c) = C c * (φ : K⸨X⸩) ^ j := by
      rw [← hC, ← hX, ← map_zpow₀, ← map_mul]
      simp [← RatFunc.single_zpow]
    rw [h, mul_assoc, C_mul_eq_smul, coeff_smul,
      PowerSeries.coeff_neg_one_coe_zpow_mul_derivative_eq_ite φ j, coeff_single]
    rcases eq_or_ne j (-1) with rfl | hj
    · simp [nsmul_eq_mul, mul_comm]
    · simp [hj, hj.symm]
  -- Induction on the order of the pole.
  have key (d : ℕ) (f : K⸨X⸩) (hf : Valued.v f ≤ WithZero.exp (d : ℤ)) :
      (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = φ.order.toNat • f.coeff (-1) := by
    induction d generalizing f with
    | zero => exact base f (by simpa using hf)
    | succ d ih =>
      set s : K⸨X⸩ := single (-((d + 1 : ℕ) : ℤ)) (f.coeff (-((d + 1 : ℕ) : ℤ)))
      have hg : Valued.v (f - s) ≤ WithZero.exp (d : ℤ) := by
        rw [← neg_neg (d : ℤ), valuation_le_iff_coeff_lt_eq_zero]
        intro n hn
        rw [← neg_neg ((d + 1 : ℕ) : ℤ), valuation_le_iff_coeff_lt_eq_zero] at hf
        rw [coeff_sub]
        rcases lt_or_eq_of_le (show n ≤ -((d + 1 : ℕ) : ℤ) by omega) with h | rfl
        · rw [hf n h, coeff_single_of_ne h.ne, sub_zero]
        · rw [coeff_single_same, sub_self]
      calc (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1)
          = (ψ (f - s) * derivative K (φ : K⸨X⸩)).coeff (-1) +
              (ψ s * derivative K (φ : K⸨X⸩)).coeff (-1) := by
            rw [map_sub, sub_mul, coeff_sub, sub_add_cancel]
        _ = φ.order.toNat • f.coeff (-1) := by
            rw [ih _ hg, mono, ← smul_add, ← coeff_add, sub_add_cancel]
  refine key (-f.order).toNat f ?_
  rw [← neg_neg ((-f.order).toNat : ℤ), valuation_le_iff_coeff_lt_eq_zero]
  exact fun n hn ↦ coeff_eq_zero_of_lt_order (by omega)

/-- **Residues are invariant under a coordinate-change substitution (`ord φ = 1`).** Let `ψ` be a
ring endomorphism of `K⸨X⸩` fixing the constants, sending power series to power series, and sending
`X` to a power series `φ` of order one, such as the substitution `X ↦ φ`. Then the coefficient of
`X⁻¹` in `ψ f * φ'` is the coefficient of `X⁻¹` in `f`: the residue of `f(X) dX` equals that of
`f(φ) dφ`. -/
theorem coeff_neg_one_map_mul_derivative {K : Type*} [Field K] (ψ : K⸨X⸩ →+* K⸨X⸩)
    (hC : ∀ c : K, ψ (C c) = C c)
    (hψ : ∀ f : K⸨X⸩, Valued.v f ≤ 1 → Valued.v (ψ f) ≤ 1) {φ : K⟦X⟧} (hφ : φ.order = 1)
    (hX : ψ (single 1 1) = φ) (f : K⸨X⸩) :
    (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = f.coeff (-1) := by
  rw [coeff_neg_one_map_mul_derivative_eq_nsmul ψ hC hψ hX f, hφ, ENat.toNat_one, one_smul]

end LaurentSeries
