/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.Valuation.Discrete.AddVal
public import TauCeti.RingTheory.Valuation.Discrete.Normalize
public import TauCeti.RingTheory.Valuation.Extension

import TauCeti.Algebra.GroupWithZero.Range
import TauCeti.Algebra.Order.Monoid.Unbundled.WithTop
import TauCeti.Data.Rat.NumDenDvd
import TauCeti.RingTheory.Valuation.Surjective

/-!
# Extensions of rank-one discrete valuations and ramification scaling

For a valuation `w` on a `K`-algebra `L` extending a rank-one discrete valuation `v` on `K`
(`v.HasExtension w`), we transfer discreteness along finite-index and finite extensions, prove
generator and additive ramification scaling
`w.intAddVal (algebraMap K L x) = w.ramificationIdx K • v.intAddVal x`, compare `w.ramificationIdx`
with `Valuation.ordIndex` (on a division ring `L` over a field `K`) and with
`Ideal.ramificationIdx` (on fields), and construct the base-normalized real additive valuation
`w.extRealAddVal K` together with its rational-value denominator bounds.

## Main definitions

* `Valuation.extRealAddVal`: the base-normalized real additive valuation
  `AddValuation L (WithTop ℝ)` dividing `w.intAddVal` by `w.ramificationIdx K`.

## Main results

* `Valuation.IsRankOneDiscrete.of_isFiniteRelIndex` and `Valuation.IsRankOneDiscrete.of_finite`:
  discreteness passes to finite-index and finite extensions.
* `Valuation.generator_comap_eq_pow_ramificationIdx`, `Valuation.intAddVal_algebraMap`, and
  `Valuation.ramificationIdx_eq_ideal_ramificationIdx`: generator scaling, additive scaling, and
  agreement with `Ideal.ramificationIdx`.
* `Valuation.normalization_comap_intValuation` and `Valuation.ramificationIdx_eq_ordIndex`:
  compatibility with `ordIndex` and `normalization` on a division ring over a field.
* `Valuation.extRealAddVal_algebraMap`,
  `Valuation.den_dvd_ramificationIdx_of_extRealAddVal_eq_ratCast`, and
  `Valuation.den_le_finrank_of_extRealAddVal_eq_ratCast`: restriction and denominator bounds for
  `w.extRealAddVal K`.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter I, §4 and Chapter II, §2.
* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
-/

public section

open scoped WithZero
open MonoidWithZeroHom

namespace Valuation

section Discreteness

variable {K L ΓK ΓL : Type*}
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]

/-- Restricting a valuation `w` extending a rank-one discrete valuation `v` along `algebraMap K L`
produces a rank-one discrete valuation. -/
theorem isRankOneDiscrete_comap_of_hasExtension [CommRing K] [Ring L] [Algebra K L]
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w] :
    (w.comap (algebraMap K L)).IsRankOneDiscrete :=
  .of_isEquiv (HasExtension.val_isEquiv_comap (vR := v) (vA := w))

/-- **Discreteness passes along finite-index valuation extensions.** If `w` extends a rank-one
discrete valuation `v` and `(w.comap (algebraMap K L)).valueGroup` has finite relative index in
`w.valueGroup`, then `w` is rank-one discrete. -/
theorem IsRankOneDiscrete.of_isFiniteRelIndex [CommRing K] [Ring L] [Algebra K L]
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w]
    [((w.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w.valueGroup] :
    w.IsRankOneDiscrete := by
  have := isRankOneDiscrete_comap_of_hasExtension v w
  obtain ⟨x, hx0, hx1⟩ :=
    (inferInstance : (w.comap (algebraMap K L)).IsNontrivial).exists_val_nontrivial
  have : w.IsNontrivial := ⟨algebraMap K L x, hx0, hx1⟩
  have : IsCyclic w.valueGroup :=
    Subgroup.isCyclic_of_isFiniteRelIndex (w.comap (algebraMap K L)).valueGroup w.valueGroup
  exact .mk' w

/-- **Discreteness passes to finite extensions.** Any valuation on a finite division-ring extension
`L / K` extending a rank-one discrete valuation on `K` is rank-one discrete. -/
theorem IsRankOneDiscrete.of_finite [Field K] [DivisionRing L] [Algebra K L] [Module.Finite K L]
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w] :
    w.IsRankOneDiscrete :=
  of_isFiniteRelIndex v w

/-- For a finite field extension `L / K`, the valuation subring of any valuation extending a
rank-one discrete valuation on `K` is a discrete valuation ring. -/
theorem valuationSubring_isDiscreteValuationRing_of_finite [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (v : Valuation K ΓK) [v.IsRankOneDiscrete]
    (w : Valuation L ΓL) [v.HasExtension w] :
    IsDiscreteValuationRing w.valuationSubring :=
  have := IsRankOneDiscrete.of_finite v w
  inferInstance

end Discreteness

section Scaling

variable {K L ΓK ΓL : Type*} [CommRing K] [Ring L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]

/-- Restricting `w.intValuation` along `algebraMap K L` produces a valuation equivalent to `v`. -/
theorem isEquiv_comap_intValuation (v : Valuation K ΓK)
    (w : Valuation L ΓL) [w.IsRankOneDiscrete] [v.HasExtension w] :
    (w.intValuation.comap (algebraMap K L)).IsEquiv v :=
  (w.isEquiv_intValuation.comap (algebraMap K L)).trans
    (HasExtension.val_isEquiv_comap (vR := v) (vA := w)).symm

/-- Restricting `w.intValuation` along `algebraMap K L` produces a rank-one discrete valuation. -/
theorem isRankOneDiscrete_comap_intValuation (v : Valuation K ΓK) [v.IsRankOneDiscrete]
    (w : Valuation L ΓL) [w.IsRankOneDiscrete] [v.HasExtension w] :
    (w.intValuation.comap (algebraMap K L)).IsRankOneDiscrete :=
  .of_isEquiv (isEquiv_comap_intValuation v w).symm

/-- When both `w` and `w.comap (algebraMap K L)` are rank-one discrete, the generator of
`(w.comap (algebraMap K L)).valueGroup` is `hw.generator ^ w.ramificationIdx K`. -/
theorem generator_comap_eq_pow_ramificationIdx (w : Valuation L ΓL) [hw : w.IsRankOneDiscrete]
    [hu : (w.comap (algebraMap K L)).IsRankOneDiscrete] :
    hu.generator = hw.generator ^ w.ramificationIdx K := by
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp <|
    hw.generator_zpowers_eq_valueGroup ▸ w.valueGroup_comap_le (algebraMap K L)
      hu.generator_mem_valueGroup
  have he_pos : 0 < e :=
    (zpow_lt_one_iff_right_of_lt_one₀ (Units.zero_lt hw.generator) hw.generator_lt_one).mp
      (by rw [← Units.val_zpow_eq_zpow_val, he]; exact hu.generator_lt_one)
  have hsub : (w.comap (algebraMap K L)).valueGroup.subgroupOf w.valueGroup =
      Subgroup.zpowers (hw.generator' ^ e) := by
    ext g
    rw [Subgroup.mem_subgroupOf, ← hu.generator_zpowers_eq_valueGroup,
      Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    refine exists_congr fun k ↦ ?_
    rw [Subtype.ext_iff, Subgroup.coe_zpow, Subgroup.coe_zpow, IsRankOneDiscrete.generator',
      ← zpow_mul, ← he, ← zpow_mul]
  have hram : (w.ramificationIdx K : ℤ) = e := by
    rw [ramificationIdx_def, Subgroup.relIndex, hsub,
      Subgroup.index_zpowers_zpow_of_isMulTorsionFree hw.generator'_zpowers_eq_top
        hw.generator'_lt_one.ne]
    exact Int.natAbs_of_nonneg he_pos.le
  rw [← zpow_natCast, hram, he]

/-- **Positivity of the ramification index** for any extension of rank-one discrete valuations on a
`K`-algebra `L`, with no finiteness hypothesis on `L / K`. -/
theorem HasExtension.ramificationIdx_pos (v : Valuation K ΓK) [v.IsRankOneDiscrete]
    (w : Valuation L ΓL) [w.IsRankOneDiscrete] [v.HasExtension w] :
    0 < w.ramificationIdx K := by
  have := isRankOneDiscrete_comap_of_hasExtension v w
  refine Nat.pos_of_ne_zero fun h0 ↦
    IsRankOneDiscrete.generator_ne_one (w.comap (algebraMap K L)) ?_
  rw [generator_comap_eq_pow_ramificationIdx w, h0, pow_zero]

variable (v : Valuation K ΓK) [hv : v.IsRankOneDiscrete]
  (w : Valuation L ΓL) [hw : w.IsRankOneDiscrete] [v.HasExtension w]

/-- On `algebraMap K L x`, `w.intValuation` raises `v.intValuation x` to the power
`w.ramificationIdx K`. -/
theorem intValuation_algebraMap (x : K) :
    w.intValuation (algebraMap K L x) = v.intValuation x ^ w.ramificationIdx K := by
  have hequiv := HasExtension.val_isEquiv_comap (vR := v) (vA := w)
  have hu := isRankOneDiscrete_comap_of_hasExtension v w
  rcases eq_or_ne (v x) 0 with hx | hx
  · have hwx : w (algebraMap K L x) = 0 := by
      simpa only [comap_apply] using hequiv.eq_zero.mp hx
    rw [w.intValuation_eq_zero_iff.mpr hwx, v.intValuation_eq_zero_iff.mpr hx,
      zero_pow (HasExtension.ramificationIdx_pos v w).ne']
  · set u := w.comap (algebraMap K L)
    set m := ord u.intValuation x
    have hux_val : u x = (hu.generator : ΓL) ^ m :=
      (u.ord_intValuation_eq_iff (hequiv.eq_zero.ne.mp hx)).mp rfl
    have hwx_val : w (algebraMap K L x) = (hw.generator : ΓL) ^ (w.ramificationIdx K * m) := by
      rw [← comap_apply (algebraMap K L) w x, hux_val, generator_comap_eq_pow_ramificationIdx w,
        Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    rw [w.intValuation_eq_exp_neg_iff.mpr hwx_val, hequiv.intValuation_eq,
      u.intValuation_eq_exp_neg_iff.mpr hux_val, ← WithZero.exp_nsmul, nsmul_eq_mul,
      neg_mul_eq_mul_neg]

/-- On `algebraMap K L x`, the order for `w.intValuation` is `w.ramificationIdx K` times the order
for `v.intValuation`. -/
theorem ord_intValuation_algebraMap (x : K) :
    ord w.intValuation (algebraMap K L x) = w.ramificationIdx K * ord v.intValuation x := by
  rw [ord_def, intValuation_algebraMap v w x, WithZero.log_pow, nsmul_eq_mul, ord_def, mul_neg]

/-- **Ramification scaling of `intAddVal`.** Restricting `w.intAddVal` along `algebraMap K L`
multiplies `v.intAddVal` by `w.ramificationIdx K`. -/
theorem intAddVal_algebraMap (x : K) :
    w.intAddVal (algebraMap K L x) = w.ramificationIdx K • v.intAddVal x := by
  rw [intAddVal_apply, intValuation_algebraMap v w x, ← map_pow, ← intAddVal_apply,
    AddValuation.map_pow]

/-- **Ramification scaling of `realAddVal`.** Restricting `w.realAddVal` along `algebraMap K L`
multiplies `v.realAddVal` by `w.ramificationIdx K`. -/
theorem realAddVal_algebraMap (x : K) :
    w.realAddVal (algebraMap K L x) = w.ramificationIdx K • v.realAddVal x := by
  rw [realAddVal_eq_map, intAddVal_algebraMap v w x, ← AddValuation.map_pow,
    ← realAddVal_eq_map, AddValuation.map_pow]

/-- A uniformizer of `v` in `K` has normalized integer additive valuation `w.ramificationIdx K` in
`L`. -/
theorem IsUniformizer.intAddVal_algebraMap {v : Valuation K ΓK} [v.IsRankOneDiscrete]
    {w : Valuation L ΓL} [w.IsRankOneDiscrete] [v.HasExtension w] {π : K}
    (hπ : v.IsUniformizer π) :
    w.intAddVal (algebraMap K L π) = w.ramificationIdx K := by
  simp [Valuation.intAddVal_algebraMap v w π, hπ.intAddVal_eq_one]

/-- `w.ramificationIdx K` is uniquely characterized as the natural number `e` for which
`w.intAddVal` restricts to `e • v.intAddVal` on `K`. -/
theorem ramificationIdx_eq_iff_forall_intAddVal {e : ℕ} :
    w.ramificationIdx K = e ↔ ∀ x : K, w.intAddVal (algebraMap K L x) = e • v.intAddVal x := by
  refine ⟨fun h x ↦ h ▸ intAddVal_algebraMap v w x, fun h ↦ ?_⟩
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    (mem_valueGroup_iff_of_comm' (v : K →*₀ ΓK)).mp (IsRankOneDiscrete.generator_mem_valueGroup v)
  rw [coe_toMonoidWithZeroHom] at hr hs hrs
  have hord : ord v.intValuation s = ord v.intValuation r + 1 := by
    rw [v.ord_intValuation_eq_iff hs, ← hrs, (v.ord_intValuation_eq_iff hr).mp rfl,
      zpow_add_one₀ (Units.ne_zero _)]
  have h1 := h r; have h2 := h s
  simp only [intAddVal_algebraMap v w, v.intAddVal_of_map_ne_zero hr, v.intAddVal_of_map_ne_zero hs,
    ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul, hord] at h1 h2
  exact_mod_cast (by linarith : (w.ramificationIdx K : ℤ) = e)

end Scaling

section OrdIndex

variable {K L ΓK ΓL : Type*} [Field K] [DivisionRing L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  (w : Valuation L ΓL) [w.IsRankOneDiscrete]

/-- **Comparison with `Valuation.ordIndex`.** For a rank-one discrete valuation `w` on a division
ring `L` over a field `K`, `w.ramificationIdx K = ordIndex (w.intValuation.comap (algebraMap K L))`.
-/
theorem ramificationIdx_eq_ordIndex :
    w.ramificationIdx K = ordIndex (w.intValuation.comap (algebraMap K L)) := by
  have htop := w.intValuation.valueGroup_eq_top_of_surjective w.intValuation_surjective
  have hg₀ := IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective w.intValuation_surjective
  have hzpow : Subgroup.zpowers (Units.mk0 (WithZero.exp (-1 : ℤ)) (by simp)) = ⊤ := by
    rw [← hg₀, IsRankOneDiscrete.generator_zpowers_eq_valueGroup, htop]
  rw [w.isEquiv_intValuation.symm.ramificationIdx_eq, ramificationIdx_def, htop,
    Subgroup.relIndex_top_right, valueGroup_eq_zpowers_ordIndex,
    Subgroup.index_zpowers_zpow_of_isMulTorsionFree hzpow
      (hg₀ ▸ IsRankOneDiscrete.generator_ne_one _),
    Int.natAbs_natCast]

/-- Normalizing the restriction of `w.intValuation` to `K` recovers `v.intValuation`. -/
theorem normalization_comap_intValuation (v : Valuation K ΓK) [v.IsRankOneDiscrete]
    [v.HasExtension w] :
    normalization (w.intValuation.comap (algebraMap K L)) = v.intValuation := by
  have := isRankOneDiscrete_comap_intValuation v w
  exact eq_of_isEquiv_of_surjective
    (normalization_surjective _ (ordIndex_ne_zero_of_isNontrivial _)) v.intValuation_surjective
    ((isEquiv_normalization _).trans ((isEquiv_comap_intValuation v w).trans
      v.isEquiv_intValuation.symm))

end OrdIndex

section ValuationSubring

variable {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  (v : Valuation K ΓK) [v.IsRankOneDiscrete]
  (w : Valuation L ΓL) [w.IsRankOneDiscrete] [v.HasExtension w]

/-- **Maximal-ideal ramification identity.** In the extension of valuation subrings induced by
`v.HasExtension w`, the maximal ideal of `v.valuationSubring` generates the `w.ramificationIdx K`-th
power of the maximal ideal of `w.valuationSubring`. -/
theorem map_maximalIdeal_valuationSubring :
    (IsLocalRing.maximalIdeal v.valuationSubring).map
      (algebraMap v.valuationSubring w.valuationSubring) =
      IsLocalRing.maximalIdeal w.valuationSubring ^ w.ramificationIdx K := by
  obtain ⟨πK, hπK⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨πL, hπL⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial w
  rw [hπK.is_generator, hπL.is_generator, Ideal.span_singleton_pow, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_span_singleton]
  have hval : w ((algebraMap v.valuationSubring w.valuationSubring πK : L)) =
      w (((πL ^ w.ramificationIdx K : w.valuationSubring) : L)) := by
    apply w.isEquiv_intValuation.eq_iff.mp
    rw [HasExtension.coe_algebraMap_valuationSubring_eq, intValuation_algebraMap v w,
      hπK.intValuation_eq_exp_neg_one, ← hπL.intValuation_eq_exp_neg_one, SubmonoidClass.coe_pow,
      map_pow]
  exact associated_of_dvd_dvd
    ((Valuation.valuationSubring.integers w).dvd_iff_le.mpr hval.ge)
    ((Valuation.valuationSubring.integers w).dvd_iff_le.mpr hval.le)

/-- **Agreement of value-group and ideal-theoretic ramification indices.** For rank-one discrete
valuations on a field extension `L / K` with `v.HasExtension w`, `w.ramificationIdx K` equals
`(maximalIdeal w.valuationSubring).ramificationIdx v.valuationSubring`. -/
theorem ramificationIdx_eq_ideal_ramificationIdx :
    w.ramificationIdx K =
      (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx v.valuationSubring :=
  (TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow
    (map_maximalIdeal_valuationSubring v w)).symm

/-- On `v.valuationSubring`, `IsDiscreteValuationRing.addVal` multiplies by `w.ramificationIdx K`
along the inclusion into `w.valuationSubring`. -/
theorem addVal_algebraMap_valuationSubring (x : v.valuationSubring) :
    IsDiscreteValuationRing.addVal w.valuationSubring
      (algebraMap v.valuationSubring w.valuationSubring x) =
      w.ramificationIdx K • IsDiscreteValuationRing.addVal v.valuationSubring x := by
  rw [← AddValuation.map_pow]
  have h : (IsDiscreteValuationRing.addVal w.valuationSubring
      (algebraMap v.valuationSubring w.valuationSubring x)).map ((↑) : ℕ → ℤ) =
      (IsDiscreteValuationRing.addVal v.valuationSubring
        (x ^ w.ramificationIdx K)).map ((↑) : ℕ → ℤ) := by
    rw [← w.intAddVal_coe_valuationSubring, ← v.intAddVal_coe_valuationSubring,
      HasExtension.coe_algebraMap_valuationSubring_eq, SubmonoidClass.coe_pow,
      AddValuation.map_pow, intAddVal_algebraMap v w]
  exact WithTop.map_injective Nat.cast_injective h

end ValuationSubring

section ExtRealAddVal

section Ring

variable {K L ΓK ΓL ΓL' : Type*} [CommRing K] [Ring L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  [LinearOrderedCommGroupWithZero ΓL']
  (w : Valuation L ΓL) [w.IsRankOneDiscrete]

/-- The **base-normalized real additive valuation** of `w` on a `K`-algebra `L`: it divides
`w.intAddVal` by `w.ramificationIdx K` (and restricts to `v.realAddVal` when `w` extends `v`). -/
noncomputable def extRealAddVal (K : Type*) [CommRing K] [Algebra K L] :
    AddValuation L (WithTop ℝ) :=
  w.intAddVal.map
    { ({ toFun := fun m : ℤ ↦ (m : ℝ) / (w.ramificationIdx K : ℝ)
         map_zero' := by simp
         map_add' := fun a b ↦ by push_cast; exact add_div _ _ _ } : ℤ →+ ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h ↦
        div_le_div_of_nonneg_right (Int.cast_le.mpr h) (Nat.cast_nonneg _) }
    rfl

/-- Pointwise evaluation of `Valuation.extRealAddVal`. -/
theorem extRealAddVal_apply (y : L) :
    w.extRealAddVal K y = (w.intAddVal y).map (fun m : ℤ ↦ (m : ℝ) / (w.ramificationIdx K : ℝ)) :=
  (rfl)

/-- `w.extRealAddVal K` is `w.realAddVal` divided pointwise by `w.ramificationIdx K`. -/
theorem extRealAddVal_eq_map_realAddVal (y : L) :
    w.extRealAddVal K y = (w.realAddVal y).map (fun t : ℝ ↦ t / (w.ramificationIdx K : ℝ)) := by
  cases h : w.intAddVal y <;> simp [extRealAddVal_apply, realAddVal_eq_map, h]

/-- Over its own base ring `K`, `v.extRealAddVal K` agrees with `v.realAddVal`. -/
@[simp]
theorem extRealAddVal_self (v : Valuation K ΓL) [v.IsRankOneDiscrete] :
    v.extRealAddVal K = v.realAddVal :=
  AddValuation.ext fun _ ↦ by simp [extRealAddVal_apply, realAddVal_eq_map]

/-- `w.extRealAddVal K` takes the value `⊤` exactly on the valuation support of `w`. -/
@[simp]
theorem extRealAddVal_eq_top_iff {y : L} : w.extRealAddVal K y = ⊤ ↔ w y = 0 := by
  rw [extRealAddVal_apply, WithTop.map_eq_top_iff, intAddVal_eq_top_iff]

/-- Outside the valuation support, `w.extRealAddVal K y` is
`(ord w.intValuation y : ℝ) / w.ramificationIdx K`. -/
theorem extRealAddVal_of_map_ne_zero {y : L} (hy : w y ≠ 0) :
    w.extRealAddVal K y =
      (((ord w.intValuation y : ℝ) / (w.ramificationIdx K : ℝ)) : WithTop ℝ) := by
  rw [extRealAddVal_apply, w.intAddVal_of_map_ne_zero hy, WithTop.map_coe]

/-- Multiplying `w.extRealAddVal K` by `w.ramificationIdx K` recovers `w.realAddVal` whenever the
ramification index is positive. -/
theorem ramificationIdx_nsmul_extRealAddVal_of_pos (he : 0 < w.ramificationIdx K) (y : L) :
    w.ramificationIdx K • w.extRealAddVal K y = w.realAddVal y := by
  rw [extRealAddVal_eq_map_realAddVal]
  cases w.realAddVal y with
  | top => rw [WithTop.map_top, WithTop.nsmul_top_of_ne_zero he.ne']
  | coe t =>
    rw [WithTop.map_coe, ← WithTop.coe_nsmul, nsmul_eq_mul,
      mul_div_cancel₀ t (Nat.cast_ne_zero.mpr he.ne')]

/-- When `0 < w.ramificationIdx K`, `w.extRealAddVal K` reverses the preorder of `w`. -/
theorem extRealAddVal_le_extRealAddVal_iff_of_pos (he : 0 < w.ramificationIdx K) {x y : L} :
    w.extRealAddVal K x ≤ w.extRealAddVal K y ↔ w y ≤ w x := by
  rw [extRealAddVal_eq_map_realAddVal, extRealAddVal_eq_map_realAddVal,
    (strictMono_div_right_of_pos (Nat.cast_pos.mpr he)).withTop_map.le_iff_le,
    realAddVal_le_realAddVal_iff]

/-- When `0 < w.ramificationIdx K`, `w.extRealAddVal K` reverses the strict order of `w`. -/
theorem extRealAddVal_lt_extRealAddVal_iff_of_pos (he : 0 < w.ramificationIdx K) {x y : L} :
    w.extRealAddVal K x < w.extRealAddVal K y ↔ w y < w x := by
  rw [← not_le, extRealAddVal_le_extRealAddVal_iff_of_pos w he, not_le]

/-- When `0 < w.ramificationIdx K`, `0 ≤ w.extRealAddVal K y` is equivalent to `w y ≤ 1`. -/
theorem extRealAddVal_nonneg_iff_of_pos (he : 0 < w.ramificationIdx K) {y : L} :
    0 ≤ w.extRealAddVal K y ↔ w y ≤ 1 := by
  rw [← AddValuation.map_one (w.extRealAddVal K),
    extRealAddVal_le_extRealAddVal_iff_of_pos w he, w.map_one]

/-- When `0 < w.ramificationIdx K`, `0 < w.extRealAddVal K y` is equivalent to `w y < 1`. -/
theorem extRealAddVal_pos_iff_of_pos (he : 0 < w.ramificationIdx K) {y : L} :
    0 < w.extRealAddVal K y ↔ w y < 1 := by
  rw [← AddValuation.map_one (w.extRealAddVal K),
    extRealAddVal_lt_extRealAddVal_iff_of_pos w he, w.map_one]

/-- When `0 < w.ramificationIdx K`, `w.extRealAddVal K y = 0` is equivalent to `w y = 1`. -/
theorem extRealAddVal_eq_zero_iff_of_pos (he : 0 < w.ramificationIdx K) {y : L} :
    w.extRealAddVal K y = 0 ↔ w y = 1 := by
  rw [extRealAddVal_eq_map_realAddVal, ← realAddVal_eq_zero_iff]
  cases w.realAddVal y <;> simp [← WithTop.coe_zero, he.ne']

/-- Every uniformizer of `w` has `w.extRealAddVal K` equal to `(w.ramificationIdx K)⁻¹`. -/
theorem IsUniformizer.extRealAddVal_eq_inv_ramificationIdx
    {w : Valuation L ΓL} [w.IsRankOneDiscrete] {π : L} (hπ : w.IsUniformizer π) :
    w.extRealAddVal K π = (((w.ramificationIdx K : ℝ)⁻¹ : ℝ) : WithTop ℝ) := by
  simp [extRealAddVal_apply, hπ.intAddVal_eq_one, one_div]

/-- **Equivalent discrete valuations on `L` have the same `extRealAddVal` over `K`.** -/
theorem IsEquiv.extRealAddVal_eq {w₁ : Valuation L ΓL} {w₂ : Valuation L ΓL'}
    [w₁.IsRankOneDiscrete] [w₂.IsRankOneDiscrete] (h : w₁.IsEquiv w₂) :
    w₁.extRealAddVal K = w₂.extRealAddVal K := by
  ext y
  rw [extRealAddVal_apply, extRealAddVal_apply, h.intAddVal_eq, h.ramificationIdx_eq]

/-- **Denominators of rational values divide the ramification index.** If `w.extRealAddVal K α = q`
for `q : ℚ`, then `q.den ∣ w.ramificationIdx K`. -/
theorem den_dvd_ramificationIdx_of_extRealAddVal_eq_ratCast {α : L} {q : ℚ}
    (hα : w.extRealAddVal K α = ((q : ℝ) : WithTop ℝ)) :
    q.den ∣ w.ramificationIdx K := by
  rcases eq_or_ne (w.ramificationIdx K) 0 with he | he
  · exact he ▸ dvd_zero _
  have hα₀ : w α ≠ 0 := fun h ↦
    WithTop.top_ne_coe (((w.extRealAddVal_eq_top_iff (K := K)).mpr h).symm.trans hα)
  have hval := WithTop.coe_inj.mp (hα.symm.trans (w.extRealAddVal_of_map_ne_zero (K := K) hα₀))
  exact (Rat.den_dvd_iff_exists_eq_intCast_div he).2
    ⟨ord w.intValuation α, by exact_mod_cast hval⟩

/-- **Restriction property of `extRealAddVal`.** When `w` extends `v`, `w.extRealAddVal K`
restricts on `K` to `v.realAddVal`. -/
theorem extRealAddVal_algebraMap (v : Valuation K ΓK) [v.IsRankOneDiscrete]
    (w : Valuation L ΓL) [w.IsRankOneDiscrete] [v.HasExtension w] (x : K) :
    w.extRealAddVal K (algebraMap K L x) = v.realAddVal x := by
  have he := HasExtension.ramificationIdx_pos v w
  exact nsmul_right_injective he.ne'
    ((w.ramificationIdx_nsmul_extRealAddVal_of_pos he _).trans (realAddVal_algebraMap v w x))

end Ring

section DivisionRing

variable {K L ΓL : Type*} [CommRing K] [DivisionRing L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓL]
  (w : Valuation L ΓL) [w.IsRankOneDiscrete]

/-- On a division ring `L`, `w.extRealAddVal K y` equals
`(ord w.intValuation y : ℝ) / w.ramificationIdx K` for every nonzero `y`. -/
theorem extRealAddVal_of_ne_zero {y : L} (hy : y ≠ 0) :
    w.extRealAddVal K y =
      (((ord w.intValuation y : ℝ) / (w.ramificationIdx K : ℝ)) : WithTop ℝ) :=
  w.extRealAddVal_of_map_ne_zero (w.ne_zero_iff.mpr hy)

/-- Every nonzero element of `L` has `w.extRealAddVal K` of the form `n / w.ramificationIdx K` for
an integer `n`. -/
theorem exists_div_ramificationIdx_extRealAddVal {y : L} (hy : y ≠ 0) :
    ∃ n : ℤ, w.extRealAddVal K y = ((n / (w.ramificationIdx K : ℝ) : ℝ) : WithTop ℝ) :=
  ⟨ord w.intValuation y, w.extRealAddVal_of_ne_zero hy⟩

end DivisionRing

section FieldBase

variable {K L ΓL : Type*} [Field K] [DivisionRing L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓL]

/-- For a finite division-ring extension `L / K` over a field `K` and a rank-one discrete
valuation `w` on `L`, if `w.extRealAddVal K α = q` for `q : ℚ`, then
`q.den ≤ Module.finrank K L`. -/
theorem den_le_finrank_of_extRealAddVal_eq_ratCast [Module.Finite K L]
    (w : Valuation L ΓL) [w.IsRankOneDiscrete] {α : L} {q : ℚ}
    (hα : w.extRealAddVal K α = ((q : ℝ) : WithTop ℝ)) :
    q.den ≤ Module.finrank K L :=
  w.le_finrank_of_dvd_ramificationIdx (w.den_dvd_ramificationIdx_of_extRealAddVal_eq_ratCast hα)

/-- **Criterion for total ramification from a rational value.** In a finite extension `L / K`, if an
element `α : L` has rational base-normalized valuation `q` with `Module.finrank K L ≤ q.den`, then
`w.ramificationIdx K = Module.finrank K L`. -/
theorem ramificationIdx_eq_finrank_of_extRealAddVal_eq_ratCast [Module.Finite K L]
    (w : Valuation L ΓL) [w.IsRankOneDiscrete] {α : L} {q : ℚ}
    (hα : w.extRealAddVal K α = ((q : ℝ) : WithTop ℝ)) (hdeg : Module.finrank K L ≤ q.den) :
    w.ramificationIdx K = Module.finrank K L :=
  w.ramificationIdx_eq_finrank_of_dvd
    (w.den_dvd_ramificationIdx_of_extRealAddVal_eq_ratCast hα) hdeg

end FieldBase

end ExtRealAddVal

end Valuation
