/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
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
`X ↦ X ^ e` is the exponent embedding `n ↦ e * n` of Hahn series. Formal differentiation obeys
the chain rule `D(f (φ)) = (Df)(φ) Dφ`, and the residue obeys the finite-map formula
`Res(f (φ) Dφ dX) = ord φ • Res(f dX)` in all characteristics (in particular, coordinate changes of
order `1` preserve the residue). A formal coordinate `φ = u X + ⋯`, `u ≠ 0`, gives a substitution
automorphism of `K⸨X⸩`, inverse to that of `φ⁻¹`. Substitution is natural in the coefficient
field: a field embedding `K → L`, applied to every coefficient, carries `f (φ)` to the
substitution of the image of `φ` into the image of `f`.

## Main definitions

* `TauCeti.LaurentSeries.substAlgHom`: the substitution `f ↦ f (φ)` as a `K`-algebra map
  `K⸨X⸩ →ₐ[K] K⸨X⸩`.
* `TauCeti.LaurentSeries.substAlgEquiv`: the substitution automorphism `f ↦ f (φ)` of a formal
  coordinate `φ`.
* `TauCeti.LaurentSeries.rescale`: the linear substitutions `f (X) ↦ f (a X)`, for units `a` of
  `K`, as a homomorphism from `Kˣ` to the `K`-algebra automorphisms of `K⸨X⸩`.

## Main results

* `TauCeti.LaurentSeries.substAlgHom_coe`: on power series it is `PowerSeries.subst`.
* `TauCeti.LaurentSeries.substAlgHom_single_mul_coe`: `(X ^ N * f₊) (φ) = φ ^ N * f₊ (φ)`.
* `TauCeti.LaurentSeries.orderTop_substAlgHom`: `ord (f (φ)) = ord φ * ord f`.
* `TauCeti.LaurentSeries.valuation_substAlgHom`: `v (f (φ)) = v f ^ ord φ`.
* `TauCeti.LaurentSeries.continuous_substAlgHom`: the substitution is continuous.
* `TauCeti.LaurentSeries.derivative_substAlgHom`: the chain rule for Laurent substitution.
* `TauCeti.LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul`: the finite-map
  residue formula
  `Res(f(φ) Dφ dX) = φ.order.toNat • Res(f dX)`, with coordinate-change invariance
  `TauCeti.LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative` when
  `φ.order = 1`.
* `TauCeti.LaurentSeries.substAlgHom_comp_substAlgHom`: `(f (φ)) (ψ) = f (φ (ψ))`.
* `TauCeti.LaurentSeries.substAlgEquiv_mul`: for formal coordinates, `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`.
* `TauCeti.LaurentSeries.mapRingHom_substAlgHom`, `TauCeti.LaurentSeries.mapRingHom_substAlgEquiv`:
  naturality of substitution under coefficient-field embeddings.
* `TauCeti.LaurentSeries.substAlgHom_X_pow`: the substitution `X ↦ X ^ e` is
  `HahnSeries.embDomainRingHom` along `n ↦ e * n`, with coefficient formulas
  `TauCeti.LaurentSeries.coeff_substAlgHom_X_pow_mul` and
  `TauCeti.LaurentSeries.coeff_substAlgHom_X_pow_of_not_dvd`.
* `TauCeti.LaurentSeries.coeff_substAlgHom_C_mul_X`, `TauCeti.LaurentSeries.coeff_rescale`: the
  substitution `X ↦ a X` multiplies the coefficient of `Xⁿ` by `a ^ n`, for every integer `n`.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries PowerSeries WithZero

namespace TauCeti.LaurentSeries

variable {K : Type*} [Field K]

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

/-- **Chain rule for Laurent series substitution.** The derivative of `f (φ)` is
`(Df)(φ) * Dφ`. -/
theorem derivative_substAlgHom (f : K⸨X⸩) :
    _root_.LaurentSeries.derivative K (substAlgHom hφ hφ₀ f) =
      substAlgHom hφ hφ₀ (_root_.LaurentSeries.derivative K f) *
        _root_.LaurentSeries.derivative K (φ : K⸨X⸩) := by
  have hpow :
      _root_.LaurentSeries.derivative K ((φ : K⸨X⸩) ^ f.order) =
        f.order • (φ : K⸨X⸩) ^ (f.order - 1) •
          _root_.LaurentSeries.derivative K (φ : K⸨X⸩) := by
    rw [← TauCeti.laurentSeriesDerivation_apply,
      (TauCeti.laurentSeriesDerivation K).leibniz_zpow,
      TauCeti.laurentSeriesDerivation_apply]
  have hseries :
      _root_.LaurentSeries.derivative K
          ((f.powerSeriesPart.subst φ : K⟦X⟧) : K⸨X⸩) =
        (((d⁄dX f.powerSeriesPart).subst φ : K⟦X⟧) : K⸨X⸩) *
          _root_.LaurentSeries.derivative K (φ : K⸨X⸩) := by
    rw [← PowerSeries.coe_derivative, PowerSeries.derivative_subst (.of_constantCoeff_zero' hφ),
      PowerSeries.coe_mul, PowerSeries.coe_derivative]
  rw [← f.single_order_mul_powerSeriesPart, substAlgHom_single_mul_coe,
    _root_.LaurentSeries.derivative_mul, hpow, hseries,
    _root_.LaurentSeries.derivative_single_mul_coe]
  simp only [map_add, map_mul, substAlgHom_single, substAlgHom_coe]
  simp only [HahnSeries.C_one, mul_one, smul_eq_mul, zsmul_eq_mul, map_intCast]
  ring

/-- **Finite-map residue formula for Laurent series substitution.** Substituting a nonzero power
series `φ` of zero constant coefficient multiplies the residue of `f dX` by `φ.order.toNat`, in all
characteristics: `Res(f(φ) Dφ dX) = φ.order.toNat • Res(f dX)`. -/
theorem coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul (f : K⸨X⸩) :
    (substAlgHom hφ hφ₀ f * _root_.LaurentSeries.derivative K (φ : K⸨X⸩)).coeff (-1) =
      φ.order.toNat • f.coeff (-1) := by
  refine _root_.LaurentSeries.coeff_neg_one_map_mul_derivative_eq_nsmul
    (substAlgHom hφ hφ₀).toRingHom ?_ ?_ (substAlgHom_single_one hφ hφ₀) f
  · intro c
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ← _root_.LaurentSeries.algebraMap_apply, AlgHom.commutes]
  · intro g hg
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, valuation_substAlgHom]
    exact pow_le_one' hg _

/-- **Coordinate-change invariance of the residue (`ord φ = 1`).** If `φ` has order one, then
`Res(f(φ) Dφ dX) = Res(f dX)`. -/
theorem coeff_neg_one_substAlgHom_mul_derivative (hφ₁ : φ.order = 1) (f : K⸨X⸩) :
    (substAlgHom hφ hφ₀ f * _root_.LaurentSeries.derivative K (φ : K⸨X⸩)).coeff (-1) =
      f.coeff (-1) := by
  rw [coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul, hφ₁, ENat.toNat_one, one_smul]

/-- Substituting `φ` and then `ψ` is substituting `φ (ψ)`. The hypotheses on `φ (ψ)` follow from
those on `φ` and `ψ` (`PowerSeries.constantCoeff_subst_eq_zero`,
`PowerSeries.subst_eq_zero_iff`). -/
theorem substAlgHom_comp_substAlgHom {ψ : K⟦X⟧} (hψ : constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0) :
    (substAlgHom hψ hψ₀).comp (substAlgHom hφ hφ₀) =
      substAlgHom (constantCoeff_subst_eq_zero hψ φ hφ)
        ((subst_eq_zero_iff hψ hψ₀).not.mpr hφ₀) := by
  refine AlgHom.toRingHom_injective (IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_)
  rw [RingHom.coe_coe, RingHom.coe_coe, AlgHom.comp_apply, _root_.LaurentSeries.coe_algebraMap,
    substAlgHom_coe, substAlgHom_coe,
    subst_comp_subst_apply (.of_constantCoeff_zero' hφ) (.of_constantCoeff_zero' hψ)]
  exact (substAlgHom_coe _ _ f).symm

/-- Substituting `φ` and then `ψ` is substituting `φ (ψ)`. -/
theorem substAlgHom_comp_substAlgHom_apply {ψ : K⟦X⟧} (hψ : constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (f : K⸨X⸩) :
    substAlgHom hψ hψ₀ (substAlgHom hφ hφ₀ f) =
      substAlgHom (constantCoeff_subst_eq_zero hψ φ hφ)
        ((subst_eq_zero_iff hψ hψ₀).not.mpr hφ₀) f :=
  congr($(substAlgHom_comp_substAlgHom hφ hφ₀ hψ hψ₀) f)

/-- Substituting `X` is the identity. -/
@[simp]
theorem substAlgHom_X :
    substAlgHom (K := K) (φ := X) constantCoeff_X X_ne_zero = AlgHom.id K K⸨X⸩ := by
  refine AlgHom.toRingHom_injective (IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_)
  rw [RingHom.coe_coe, RingHom.coe_coe, _root_.LaurentSeries.coe_algebraMap, substAlgHom_coe,
    X_subst, AlgHom.id_apply]

/-- `substAlgHom_X`, for a series `φ` known to equal `X` and carrying its own hypotheses. -/
private theorem substAlgHom_eq_id_of_eq_X (h : φ = X) :
    substAlgHom hφ hφ₀ = AlgHom.id K K⸨X⸩ := by
  subst h
  exact substAlgHom_X

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

/-- Substituting `X ↦ a X` sends the monomial `c Xⁿ` to `a ^ n c Xⁿ`. -/
private theorem substAlgHom_C_mul_X_single {a : K} (ha : a ≠ 0) (n : ℤ) (c : K) :
    substAlgHom (φ := C a * X) (by simp) (by simp [ha]) (single n c) = single n (a ^ n * c) := by
  -- `(a X) ^ n = a ^ n X ^ n`
  rw [substAlgHom_single, PowerSeries.coe_mul, mul_zpow]
  simp [← map_zpow₀, ← RatFunc.single_zpow, ← single_zero_mul_eq_smul, -HahnSeries.C_apply,
    HahnSeries.C_mul_eq_smul, mul_comm]

/-- On power series, `PowerSeries.rescale a` multiplies the Laurent coefficient of `Xⁿ` by `a ^ n`,
for every integer `n`. -/
private theorem coeff_coe_rescale (a : K) (g : K⟦X⟧) (n : ℤ) :
    ((PowerSeries.rescale a g : K⟦X⟧) : K⸨X⸩).coeff n = a ^ n * (g : K⸨X⸩).coeff n := by
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [mul_zero]
  · rw [PowerSeries.coeff_rescale, ← zpow_natCast, Int.natAbs_of_nonneg (not_lt.mp h)]

/-- On power series, substituting `X ↦ a X` multiplies the coefficient of `Xⁿ` by `a ^ n`. -/
private theorem coeff_substAlgHom_C_mul_X_coe {a : K} (ha : a ≠ 0) (g : K⟦X⟧) (n : ℤ) :
    (substAlgHom (φ := C a * X) (by simp) (by simp [ha]) (g : K⸨X⸩)).coeff n =
      a ^ n * (g : K⸨X⸩).coeff n := by
  rw [substAlgHom_coe, ← smul_eq_C_mul, ← rescale_eq_subst, coeff_coe_rescale]

/-- Substituting `X ↦ a X`, for `a ≠ 0`, multiplies the coefficient of `Xⁿ` by `a ^ n`, for every
integer `n`. -/
@[simp]
theorem coeff_substAlgHom_C_mul_X {a : K} (ha : a ≠ 0) (f : K⸨X⸩) (n : ℤ) :
    (substAlgHom (φ := C a * X) (by simp) (by simp [ha]) f).coeff n = a ^ n * f.coeff n := by
  -- write `f = X ^ N * f₊` with `f₊` a power series
  rw [← f.single_order_mul_powerSeriesPart, map_mul, substAlgHom_C_mul_X_single ha,
    coeff_single_mul, coeff_single_mul, coeff_substAlgHom_C_mul_X_coe ha]
  simp [← mul_assoc, ← zpow_add₀ ha]

/-- The substitution `X ↦ a X` for a unit `a`. -/
private noncomputable abbrev rescaleAlgHom (a : Kˣ) : K⸨X⸩ →ₐ[K] K⸨X⸩ :=
  substAlgHom (φ := C (a : K) * X) (by simp) (by simp)

private theorem coeff_rescaleAlgHom (a : Kˣ) (f : K⸨X⸩) (n : ℤ) :
    (rescaleAlgHom a f).coeff n = (a : K) ^ n * f.coeff n :=
  coeff_substAlgHom_C_mul_X a.ne_zero f n

private theorem rescaleAlgHom_mul_apply (a b : Kˣ) (f : K⸨X⸩) :
    rescaleAlgHom (a * b) f = rescaleAlgHom a (rescaleAlgHom b f) := by
  ext n
  rw [coeff_rescaleAlgHom, coeff_rescaleAlgHom, coeff_rescaleAlgHom, Units.val_mul, mul_zpow,
    mul_assoc]

private theorem rescaleAlgHom_one_apply (f : K⸨X⸩) : rescaleAlgHom 1 f = f := by
  ext n
  rw [coeff_rescaleAlgHom, Units.val_one, one_zpow, one_mul]

/-- The rescaling `f (X) ↦ f (a X)` of Laurent series by a unit `a`, as a `K`-algebra
automorphism. It multiplies the coefficient of `Xⁿ` by `a ^ n`, and the automorphisms for `a` and
`b` compose to the one for `a * b`. -/
noncomputable def rescale : Kˣ →* (K⸨X⸩ ≃ₐ[K] K⸨X⸩) where
  toFun a := AlgEquiv.ofAlgHom (rescaleAlgHom a) (rescaleAlgHom a⁻¹)
    (AlgHom.ext fun f ↦ by
      rw [AlgHom.comp_apply, ← rescaleAlgHom_mul_apply, mul_inv_cancel, rescaleAlgHom_one_apply,
        AlgHom.id_apply])
    (AlgHom.ext fun f ↦ by
      rw [AlgHom.comp_apply, ← rescaleAlgHom_mul_apply, inv_mul_cancel, rescaleAlgHom_one_apply,
        AlgHom.id_apply])
  map_one' := AlgEquiv.ext rescaleAlgHom_one_apply
  map_mul' a b := AlgEquiv.ext (rescaleAlgHom_mul_apply a b)

/-- Rescaling by `a` multiplies the coefficient of `Xⁿ` by `a ^ n`. -/
@[simp]
theorem coeff_rescale (a : Kˣ) (f : K⸨X⸩) (n : ℤ) :
    (rescale a f).coeff n = (a : K) ^ n * f.coeff n :=
  coeff_rescaleAlgHom a f n

/-- Rescaling by `a` is the substitution `X ↦ a X`, so it inherits, for instance, continuity and
the chain rule from `substAlgHom`. -/
theorem rescale_toAlgHom (a : Kˣ) :
    (rescale a : K⸨X⸩ →ₐ[K] K⸨X⸩) = substAlgHom (φ := C (a : K) * X) (by simp) (by simp) := by
  ext f n
  rw [AlgEquiv.coe_toAlgHom, coeff_rescale, coeff_substAlgHom_C_mul_X a.ne_zero]

/-- Rescaling sends the monomial `c Xⁿ` to `a ^ n c Xⁿ`. -/
@[simp]
theorem rescale_single (a : Kˣ) (n : ℤ) (c : K) :
    rescale a (single n c) = single n ((a : K) ^ n * c) := by
  ext m
  rcases eq_or_ne m n with rfl | h
  · simp
  · simp [coeff_single_of_ne h]

/-- On power series, rescaling Laurent series is `PowerSeries.rescale`. -/
@[simp]
theorem rescale_coe (a : Kˣ) (f : K⟦X⟧) :
    rescale a (f : K⸨X⸩) = ((PowerSeries.rescale (a : K) f : K⟦X⟧) : K⸨X⸩) := by
  ext n
  rw [coeff_rescale, coeff_coe_rescale]

/-! ### Naturality in the coefficient field -/

section map

variable {L : Type*} [Field L] (σ : K →+* L)

/-- Substitution into Laurent series is natural in the coefficient field: applying a field
embedding `σ : K →+* L` to the coefficients of `f (φ)` gives the substitution of the image `ψ` of
`φ` into the image of `f`. The image `ψ` is passed explicitly, with its (automatic) side conditions,
so that it can be given in normal form, such as `X ^ e` for the ramified substitution. -/
theorem mapRingHom_substAlgHom {ψ : L⟦X⟧} (hψ : constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (h : PowerSeries.map σ φ = ψ) (f : K⸨X⸩) :
    mapRingHom σ (substAlgHom hφ hφ₀ f) = substAlgHom hψ hψ₀ (mapRingHom σ f) := by
  subst h
  -- both sides are ring homomorphisms out of the fraction field `K⸨X⸩` of `K⟦X⟧`
  refine congr($(IsLocalization.ringHom_ext (nonZeroDivisors K⟦X⟧)
    (j := (mapRingHom σ).comp (substAlgHom hφ hφ₀ : K⸨X⸩ →+* K⸨X⸩))
    (k := (substAlgHom hψ hψ₀ : L⸨X⸩ →+* L⸨X⸩).comp (mapRingHom σ))
    (RingHom.ext fun p ↦ ?_)) f)
  simp only [RingHom.comp_apply, RingHom.coe_coe, _root_.LaurentSeries.coe_algebraMap,
    substAlgHom_coe, mapRingHom_apply, map_ofPowerSeries]
  -- `PowerSeries.map` is by definition `MvPowerSeries.map` over `Unit`, the form in which
  -- Mathlib states `PowerSeries.map_subst`
  exact congrArg _ (map_subst (HasSubst.of_constantCoeff_zero' hφ) p)

end map

/-! ### Substitution of formal coordinates -/

/-- The substitution automorphism `f ↦ f (φ)` of `K⸨X⸩` attached to a formal coordinate `φ`, with
inverse the substitution of the compositional inverse `φ⁻¹`. It extends the substitution
automorphism `TauCeti.FormalCoordinate.substAlgEquiv` of `K⟦X⟧` to Laurent series. -/
noncomputable def substAlgEquiv (φ : FormalCoordinate K) : K⸨X⸩ ≃ₐ[K] K⸨X⸩ :=
  .ofAlgHom (substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero)
    (substAlgHom φ⁻¹.constantCoeff_toPowerSeries φ⁻¹.toPowerSeries_ne_zero)
    (by
      rw [substAlgHom_comp_substAlgHom]
      exact substAlgHom_eq_id_of_eq_X _ _ (FormalCoordinate.toPowerSeries_inv_mul φ))
    (by
      rw [substAlgHom_comp_substAlgHom]
      exact substAlgHom_eq_id_of_eq_X _ _ (FormalCoordinate.toPowerSeries_mul_inv φ))

/-- The substitution automorphism of a formal coordinate is the substitution `substAlgHom`. -/
@[simp]
theorem coe_substAlgEquiv (φ : FormalCoordinate K) :
    ⇑(substAlgEquiv φ) = substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero :=
  (rfl)

/-- On power series, the substitution automorphism of `K⸨X⸩` is that of `K⟦X⟧`. -/
theorem substAlgEquiv_coe (φ : FormalCoordinate K) (f : K⟦X⟧) :
    substAlgEquiv φ (f : K⸨X⸩) = ((φ.substAlgEquiv f : K⟦X⟧) : K⸨X⸩) := by
  rw [coe_substAlgEquiv, substAlgHom_coe, FormalCoordinate.substAlgEquiv_apply]

@[simp]
theorem substAlgEquiv_symm (φ : FormalCoordinate K) :
    (substAlgEquiv φ).symm = substAlgEquiv φ⁻¹ :=
  AlgEquiv.ext fun _ ↦ rfl

/-- Substitution automorphisms reverse composition: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`. -/
@[simp]
theorem substAlgEquiv_mul (φ ψ : FormalCoordinate K) :
    substAlgEquiv (φ * ψ) = substAlgEquiv ψ * substAlgEquiv φ :=
  AlgEquiv.ext fun f ↦ by
    rw [AlgEquiv.mul_apply, coe_substAlgEquiv, coe_substAlgEquiv, coe_substAlgEquiv,
      substAlgHom_comp_substAlgHom_apply]

@[simp]
theorem substAlgEquiv_one : substAlgEquiv (1 : FormalCoordinate K) = 1 :=
  AlgEquiv.ext fun f ↦ by
    rw [coe_substAlgEquiv, substAlgHom_eq_id_of_eq_X _ _ FormalCoordinate.toPowerSeries_one,
      AlgHom.id_apply, AlgEquiv.one_apply]

/-- Substitution automorphisms are natural in the coefficient field: applying a field embedding
`σ : K →+* L` to the coefficients intertwines `σ_φ` with the substitution automorphism of the
base-changed coordinate. -/
theorem mapRingHom_substAlgEquiv {L : Type*} [Field L] (σ : K →+* L) (φ : FormalCoordinate K)
    (f : K⸨X⸩) :
    mapRingHom σ (substAlgEquiv φ f) =
      substAlgEquiv (FormalCoordinate.map σ φ) (mapRingHom σ f) := by
  rw [coe_substAlgEquiv, coe_substAlgEquiv]
  exact mapRingHom_substAlgHom _ _ σ _ _ (FormalCoordinate.toPowerSeries_map σ φ).symm f

/-- The ring homomorphisms underlying `σ_φ` and its inverse are inverse to each other, so that
`σ_φ`-semilinear equivalences can be formed. -/
instance (φ : FormalCoordinate K) :
    RingHomInvPair ((substAlgEquiv φ).toRingEquiv : K⸨X⸩ →+* K⸨X⸩)
      ((substAlgEquiv φ).toRingEquiv.symm : K⸨X⸩ →+* K⸨X⸩) :=
  .of_ringEquiv _

/-- The ring homomorphisms underlying the inverse of `σ_φ` and `σ_φ` are inverse to each other. -/
instance (φ : FormalCoordinate K) :
    RingHomInvPair ((substAlgEquiv φ).toRingEquiv.symm : K⸨X⸩ →+* K⸨X⸩)
      ((substAlgEquiv φ).toRingEquiv : K⸨X⸩ →+* K⸨X⸩) :=
  .of_ringEquiv_symm _

end TauCeti.LaurentSeries
