/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Basic
public import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Substitution into formal Laurent series

Let `K` be a field and `φ ∈ K⟦X⟧` a nonzero power series with zero constant coefficient. Mathlib's
`PowerSeries.subst` substitutes `φ` into power series, `f ↦ f (φ)`. Since `φ` is nonzero, this
is injective (`PowerSeries.subst_eq_zero_iff`), and so it extends uniquely to a `K`-algebra map
`f ↦ f (φ)` of the fraction field `K⸨X⸩`. This file constructs that extension and computes its
effect on orders, valuations and coefficients.

Writing a Laurent series as `f = X ^ N * f₊` with `N ∈ ℤ` and `f₊ ∈ K⟦X⟧`, the substitution is
`f (φ) = φ ^ N * f₊ (φ)`, for every such representation
(`TauCeti.LaurentSeries.substAlgHom_single_mul_coe`). If `φ` has order `e ≥ 1`, then
`ord (f (φ)) = e * ord f`, so the valuation is raised to the power `e`. In particular the
substitution is injective and continuous for the valuation topology. Substitutions compose as
power series do: substituting `φ` and then `ψ` is substituting `φ (ψ)`. The ramified substitution
`X ↦ X ^ e` is the exponent embedding `n ↦ e * n` of Hahn series.

## Main definitions

* `TauCeti.LaurentSeries.substAlgHom`: the substitution `f ↦ f (φ)` as a `K`-algebra map
  `K⸨X⸩ →ₐ[K] K⸨X⸩`.

## Main results

* `TauCeti.LaurentSeries.substAlgHom_coe`: on power series it is `PowerSeries.subst`.
* `TauCeti.LaurentSeries.substAlgHom_single_mul_coe`: `(X ^ N * f₊) (φ) = φ ^ N * f₊ (φ)`.
* `TauCeti.LaurentSeries.orderTop_substAlgHom`: `ord (f (φ)) = ord φ * ord f`.
* `TauCeti.LaurentSeries.valuation_substAlgHom`: `v (f (φ)) = v f ^ ord φ`.
* `TauCeti.LaurentSeries.continuous_substAlgHom`: the substitution is continuous.
* `TauCeti.LaurentSeries.substAlgHom_comp_substAlgHom`: `(f (φ)) (ψ) = f (φ (ψ))`.
* `TauCeti.LaurentSeries.substAlgHom_X_pow`: the substitution `X ↦ X ^ e` is
  `HahnSeries.embDomainRingHom` along `n ↦ e * n`, with coefficient formulas
  `TauCeti.LaurentSeries.coeff_substAlgHom_X_pow_mul` and
  `TauCeti.LaurentSeries.coeff_substAlgHom_X_pow_of_not_dvd`.

Along the way, `TauCeti.LaurentSeries.valuation_eq_exp_neg_order` records that a nonzero Laurent
series `f` has valuation `exp (-ord f)`.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries PowerSeries WithZero

namespace TauCeti.LaurentSeries

variable {K : Type*} [Field K]

/-- A unit of `K⟦X⟧`, that is a power series of nonzero constant coefficient, has valuation one
in `K⸨X⸩`. -/
theorem valuation_coe_of_isUnit {h : K⟦X⟧} (hh : IsUnit h) : Valued.v (h : K⸨X⸩) = 1 :=
  Valuation.Integers.one_of_isUnit' hh fun g ↦ (_root_.LaurentSeries.val_le_one_iff_eq_coe K _).mpr
    ⟨g, rfl⟩

/-- The power series part of a nonzero Laurent series is a unit: its constant coefficient is the
leading coefficient. -/
theorem isUnit_powerSeriesPart {f : K⸨X⸩} (hf : f ≠ 0) : IsUnit f.powerSeriesPart := by
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
  have hu : IsUnit g.divXPowOrder := by
    rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hg
  nth_rw 1 [← X_pow_order_mul_divXPowOrder (f := g)]
  rw [PowerSeries.coe_mul, map_mul, PowerSeries.coe_pow, _root_.LaurentSeries.valuation_X_pow,
    valuation_coe_of_isUnit hu, mul_one]

variable {φ : K⟦X⟧} (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

include hφ hφ₀ in
/-- Substituting a nonzero power series `φ` of zero constant coefficient into power series,
followed by the inclusion into Laurent series, is injective. -/
private theorem injective_substAlgHom_coe :
    Function.Injective ((IsScalarTower.toAlgHom K K⟦X⟧ K⸨X⸩).comp
      (PowerSeries.substAlgHom (R := K) (HasSubst.of_constantCoeff_zero' hφ))) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', _root_.LaurentSeries.coe_algebraMap,
    map_eq_zero_iff _ ofPowerSeries_injective, coe_substAlgHom] at hf
  exact (subst_eq_zero_iff hφ hφ₀).mp hf

/-- Substitution `f ↦ f (φ)` of a nonzero power series `φ` with zero constant coefficient into
Laurent series, as a `K`-algebra map. It is the unique extension of `PowerSeries.subst` to the
fraction field `K⸨X⸩` of `K⟦X⟧`. -/
noncomputable def substAlgHom : K⸨X⸩ →ₐ[K] K⸨X⸩ :=
  IsFractionRing.liftAlgHom (injective_substAlgHom_coe hφ hφ₀)

/-- On power series, substitution into Laurent series is `PowerSeries.subst`. -/
@[simp]
theorem substAlgHom_coe (f : K⟦X⟧) :
    substAlgHom hφ hφ₀ (f : K⸨X⸩) = ((f.subst φ : K⟦X⟧) : K⸨X⸩) := by
  rw [substAlgHom, IsFractionRing.coe_liftAlgHom, ← _root_.LaurentSeries.coe_algebraMap,
    IsFractionRing.lift_algebraMap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', coe_substAlgHom, _root_.LaurentSeries.coe_algebraMap]

/-- Substitution sends the variable `X = single 1 1` to `φ`. -/
theorem substAlgHom_single_one : substAlgHom hφ hφ₀ (single 1 1) = (φ : K⸨X⸩) := by
  rw [← PowerSeries.coe_X, substAlgHom_coe, subst_X (.of_constantCoeff_zero' hφ)]

/-- Substitution sends the monomial `a X ^ n`, for every integer `n`, to `a φ ^ n`. -/
@[simp]
theorem substAlgHom_single (n : ℤ) (a : K) :
    substAlgHom hφ hφ₀ (single n a) = HahnSeries.C a * (φ : K⸨X⸩) ^ n := by
  rw [← mul_one a, ← zero_add n, ← single_mul_single, mul_one, zero_add, map_mul,
    RatFunc.single_zpow, map_zpow₀, substAlgHom_single_one, ← HahnSeries.C_apply,
    ← _root_.LaurentSeries.algebraMap_apply, AlgHom.commutes]

/-- Writing a Laurent series as `X ^ N * f₊` with `f₊` a power series, its substitution is
`φ ^ N * f₊ (φ)`. Since `substAlgHom` does not depend on the representation, neither does this
expression. -/
theorem substAlgHom_single_mul_coe (N : ℤ) (f : K⟦X⟧) :
    substAlgHom hφ hφ₀ (single N 1 * (f : K⸨X⸩)) =
      (φ : K⸨X⸩) ^ N * ((f.subst φ : K⟦X⟧) : K⸨X⸩) := by
  rw [map_mul, substAlgHom_single, substAlgHom_coe, HahnSeries.C_one, one_mul]

/-- Substitution into Laurent series is injective. -/
theorem substAlgHom_injective : Function.Injective (substAlgHom hφ hφ₀) :=
  (substAlgHom hφ hφ₀).toRingHom.injective

/-- Substituting `φ` raises the valuation to the power `ord φ`. -/
theorem valuation_substAlgHom (f : K⸨X⸩) :
    Valued.v (substAlgHom hφ hφ₀ f) = Valued.v f ^ φ.order.toNat := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, map_zero, zero_pow (toNat_order_ne_zero hφ hφ₀)]
  -- `f = X ^ n * g` with `n = ord f` and `g` a unit, so `f (φ) = φ ^ n * g (φ)`
  have hg := (isUnit_powerSeriesPart hf).map (PowerSeries.substAlgHom (.of_constantCoeff_zero' hφ))
  rw [coe_substAlgHom] at hg
  nth_rw 1 [← f.single_order_mul_powerSeriesPart]
  rw [substAlgHom_single_mul_coe, map_mul, map_zpow₀, valuation_coe hφ₀,
    valuation_coe_of_isUnit hg, mul_one, valuation_eq_exp_neg_order hf, ← exp_zsmul,
    ← exp_nsmul, exp_inj, smul_neg, smul_neg, smul_eq_mul, nsmul_eq_mul, mul_comm]

/-- Substituting `φ` multiplies the order by `ord φ`. -/
theorem order_substAlgHom (f : K⸨X⸩) :
    (substAlgHom hφ hφ₀ f).order = φ.order.toNat * f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, HahnSeries.order_zero, mul_zero]
  have h := valuation_substAlgHom hφ hφ₀ f
  rwa [valuation_eq_exp_neg_order ((map_ne_zero _).mpr hf), valuation_eq_exp_neg_order hf,
    ← exp_nsmul, exp_inj, smul_neg, neg_inj, nsmul_eq_mul] at h

/-- Substituting `φ` multiplies the order by `ord φ`: `ord (f (φ)) = ord φ * ord f`, including
`ord 0 = ⊤`. -/
theorem orderTop_substAlgHom (f : K⸨X⸩) :
    (substAlgHom hφ hφ₀ f).orderTop = φ.order.toNat • f.orderTop := by
  rcases eq_or_ne f 0 with rfl | hf
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (toNat_order_ne_zero hφ hφ₀)
    rw [map_zero, orderTop_zero, hm, succ_nsmul, WithTop.add_top]
  rw [← order_eq_orderTop_of_ne_zero ((map_ne_zero _).mpr hf), ← order_eq_orderTop_of_ne_zero hf,
    order_substAlgHom, ← WithTop.coe_nsmul, nsmul_eq_mul]

/-- Substitution into Laurent series is continuous for the valuation topology. -/
theorem continuous_substAlgHom : Continuous (substAlgHom hφ hφ₀) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  -- the valuation ball of radius `min γ 1` is mapped into the ball of radius `γ`
  refine ((Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)).mpr
    fun γ _ ↦ ⟨min γ 1, trivial, fun f hf ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.min_val, Units.val_one, lt_min_iff] at hf ⊢
  have h : Valued.v.restrict (substAlgHom hφ hφ₀ f) = Valued.v.restrict f ^ φ.order.toNat := by
    rw [← map_pow, Valuation.restrict_inj, map_pow, valuation_substAlgHom]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (toNat_order_ne_zero hφ hφ₀)
  rw [h, hm, pow_succ]
  exact (mul_le_of_le_one_left' (pow_le_one' hf.2.le m)).trans_lt hf.1

/-- Substituting `φ` and then `ψ` is substituting `φ (ψ)`. The hypotheses on `φ (ψ)` follow from
those on `φ` and `ψ` (`PowerSeries.constantCoeff_subst_eq_zero`, `PowerSeries.subst_eq_zero_iff`),
and are taken as arguments so that any proofs of them can be used. -/
theorem substAlgHom_comp_substAlgHom {ψ : K⟦X⟧} (hψ : constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (hφψ : constantCoeff (φ.subst ψ : K⟦X⟧) = 0) (hφψ₀ : (φ.subst ψ : K⟦X⟧) ≠ 0) :
    (substAlgHom hψ hψ₀).comp (substAlgHom hφ hφ₀) = substAlgHom hφψ hφψ₀ := by
  refine AlgHom.toRingHom_injective (IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_)
  rw [RingHom.coe_coe, RingHom.coe_coe, AlgHom.comp_apply, _root_.LaurentSeries.coe_algebraMap,
    substAlgHom_coe, substAlgHom_coe, substAlgHom_coe,
    subst_comp_subst_apply (.of_constantCoeff_zero' hφ) (.of_constantCoeff_zero' hψ)]

/-- Substituting `φ` and then `ψ` is substituting `φ (ψ)`. -/
theorem substAlgHom_substAlgHom {ψ : K⟦X⟧} (hψ : constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (hφψ : constantCoeff (φ.subst ψ : K⟦X⟧) = 0) (hφψ₀ : (φ.subst ψ : K⟦X⟧) ≠ 0) (f : K⸨X⸩) :
    substAlgHom hψ hψ₀ (substAlgHom hφ hφ₀ f) = substAlgHom hφψ hφψ₀ f :=
  congr($(substAlgHom_comp_substAlgHom hφ hφ₀ hψ hψ₀ hφψ hφψ₀) f)

/-- The ramified substitution `X ↦ X ^ e`, for `e ≠ 0`, multiplies all exponents by `e`: it is the
exponent embedding `HahnSeries.embDomainRingHom` along `n ↦ e * n`. -/
theorem substAlgHom_X_pow {e : ℕ} (he : e ≠ 0) :
    (substAlgHom (K := K) (φ := X ^ e) (by simp [he]) (pow_ne_zero e X_ne_zero) :
        K⸨X⸩ →+* K⸨X⸩) =
      embDomainRingHom (AddMonoidHom.mulLeft (e : ℤ)) (mul_right_injective₀ (by exact_mod_cast he))
        (fun _ _ ↦ mul_le_mul_iff_right₀ (by omega)) := by
  refine IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_
  rw [RingHom.coe_coe, _root_.LaurentSeries.coe_algebraMap, substAlgHom_coe]
  ext n
  simp only [embDomainRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  by_cases hn : (e : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ : ∃ k, AddMonoidHom.mulLeft (e : ℤ) k = n := ⟨_, Int.mul_ediv_cancel' hn⟩
    refine Eq.trans ?_ (embDomain_coeff (a := k)).symm
    have he' : (0 : ℤ) < e := by omega
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe, AddMonoidHom.coe_mulLeft,
      coeff_subst_X_pow he, Int.natAbs_mul, Int.natAbs_natCast,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he), ite_eq_left (dvd_mul_right _ _),
      Algebra.algebraMap_self_apply]
    simp only [← not_le, mul_nonneg_iff_of_pos_left he']
  · -- off the multiples of `e`, both coefficients vanish
    refine Eq.trans ?_ (embDomain_of_notMem_range fun ⟨k, hk⟩ ↦ hn ⟨k, hk.symm⟩).symm
    rw [PowerSeries.coeff_coe, ite_eq_left_iff, not_lt, coeff_subst_X_pow he, ite_eq_right]
    · exact fun _ ↦ rfl
    · exact fun h ↦ hn (Int.natCast_dvd.mpr h)

/-- The ramified substitution `X ↦ X ^ e` moves the coefficient of `Xⁿ` to `X ^ (e * n)`. -/
@[simp]
theorem coeff_substAlgHom_X_pow_mul {e : ℕ} (he : e ≠ 0) (f : K⸨X⸩) (n : ℤ) :
    (substAlgHom (φ := X ^ e) (by simp [he]) (pow_ne_zero e X_ne_zero) f).coeff (e * n) =
      f.coeff n := by
  rw [← AlgHom.coe_toRingHom, substAlgHom_X_pow he]
  exact embDomain_coeff

/-- After the ramified substitution `X ↦ X ^ e`, only exponents divisible by `e` occur. -/
theorem coeff_substAlgHom_X_pow_of_not_dvd {e : ℕ} (he : e ≠ 0) (f : K⸨X⸩) {n : ℤ}
    (hn : ¬(e : ℤ) ∣ n) :
    (substAlgHom (φ := X ^ e) (by simp [he]) (pow_ne_zero e X_ne_zero) f).coeff n = 0 := by
  rw [← AlgHom.coe_toRingHom, substAlgHom_X_pow he]
  exact embDomain_of_notMem_range fun ⟨k, hk⟩ ↦ hn ⟨k, hk.symm⟩

end TauCeti.LaurentSeries
