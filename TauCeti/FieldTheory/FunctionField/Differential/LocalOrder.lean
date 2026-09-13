/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.Differential.LocalComponent

/-!
# The order of a Weil differential is a local invariant

The divisor `(ω)` of a nonzero Weil differential of an algebraic function field `F / k` with exact
constant field is the greatest divisor `D` with `ω ∈ Ω_F(D)`, a condition on *all* the places at
once.  Its coefficient `v_P (ω)` at a single place is nevertheless determined by the local
component `ω_P` alone:

`v_P (ω) = max {m : ℤ | ω_P z = 0 whenever v_P z ≤ exp m}`.

That the maximum is attained by `v_P (ω)` is the bound `ω ∈ Ω_F ((ω))` read at `P`; that nothing
larger belongs to the set is the maximality of `(ω)`, applied to the divisor obtained from `(ω)`
by resetting its coefficient at `P` to `m` — the other coefficients are unchanged, so the
local-component criterion for membership in `Ω_F` needs only the hypothesis at `P`.

This is the half of Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Proposition 1.7.3(a) that mentions the divisor `(ω)`; the other half, that `ω_P` never vanishes
identically, is in `TauCeti.FieldTheory.FunctionField.Differential.LocalNonvanishing`.

At a **rational** place the characterization sharpens to a single value: writing `r = v_P (ω)`,
some function with a pole of order at most `r + 1` at `P` is not killed by `ω_P`, and subtracting
a constant multiple of `t ^ (-r - 1)` from it — possible because the residue field is `k` — lands
in the part `ω_P` does kill.  So `ω_P` is already nonzero on the single power `t ^ (-r - 1)` of
any uniformizer `t`.  This is what pins down the normalization of the canonical Weil differential
of the rational function field.

## Main results

* `TauCeti.isGreatest_weilDifferentialOrder` and `TauCeti.le_weilDifferentialOrder_iff`: the order
  `v_P (ω)` is the largest bound the local component `ω_P` respects (Stichtenoth,
  Proposition 1.7.3(a)).
* `TauCeti.repartitionDualComponent_uniformizer_zpow_ne_zero`: at a rational place, `ω_P` is
  nonzero on `t ^ (-v_P (ω) - 1)` for every uniformizer `t`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.3(a).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The order of a nonzero Weil differential at a place is determined by its local component
there** (Stichtenoth, Proposition 1.7.3(a)): `v_P (ω)` is the greatest `m` for which `ω_P` kills
every function whose pole at `P` is bounded by `m`. -/
theorem isGreatest_weilDifferentialOrder (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) (P : Place k F) :
    IsGreatest {m : ℤ | ∀ z : F, P.valuation z ≤ WithZero.exp m →
        repartitionDualComponent ω P z = 0} (weilDifferentialOrder hF hex hmem hω P) := by
  have hW := isGreatest_weilDifferentialDivisor hF hex hmem hω
  constructor
  · intro z hz
    exact repartitionDualComponent_apply_eq_zero_of_le hW.1 P
      (by rwa [coeff_weilDifferentialDivisor])
  · intro m hm
    -- Reset the coefficient of `(ω)` at `P` to `m`; the local-component criterion then shows that
    -- `ω` is still bounded by the modified divisor, which maximality of `(ω)` sends back to `P`.
    set W := weilDifferentialDivisor hF hex hmem hω with hWdef
    set D : Divisor k F := W + (m - W.coeff P) • WeilDivisor.ofPoint P with hDdef
    have hDP : D.coeff P = m := by
      rw [hDdef, WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul,
        WeilDivisor.coeff_ofPoint_self, mul_one]
      ring
    have hDQ : ∀ Q : Place k F, Q ≠ P → D.coeff Q = W.coeff Q := fun Q hQ ↦ by
      rw [hDdef, WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul,
        WeilDivisor.coeff_ofPoint_of_ne hQ, mul_zero, add_zero]
    have hmemD : ω ∈ weilDifferentialFiltration D := by
      rw [mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero hmem]
      intro Q z hz
      rcases eq_or_ne Q P with rfl | hQ
      · exact hm z (hDP ▸ hz)
      · exact repartitionDualComponent_apply_eq_zero_of_le hW.1 Q (by rwa [hDQ Q hQ] at hz)
    have hle := WeilDivisor.coeff_le_coeff (hW.2 hmemD) P
    rw [hDP] at hle
    rwa [← coeff_weilDifferentialDivisor hF hex hmem hω]

/-- **The order of a nonzero Weil differential, as a bound on its local component** (Stichtenoth,
Proposition 1.7.3(a)): `m ≤ v_P (ω)` exactly when `ω_P` kills every function whose pole at `P` is
bounded by `m`. -/
theorem le_weilDifferentialOrder_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) (P : Place k F) (m : ℤ) :
    m ≤ weilDifferentialOrder hF hex hmem hω P ↔
      ∀ z : F, P.valuation z ≤ WithZero.exp m → repartitionDualComponent ω P z = 0 := by
  refine ⟨fun hm z hz ↦ (isGreatest_weilDifferentialOrder hF hex hmem hω P).1 z
    (hz.trans (WithZero.exp_le_exp.mpr hm)),
    fun hm ↦ (isGreatest_weilDifferentialOrder hF hex hmem hω P).2 hm⟩

/-- **At a rational place the order of a nonzero Weil differential is attained on a power of any
uniformizer**: with `r = v_P (ω)` and `t` a uniformizer at `P`, the local component `ω_P` does not
kill `t ^ (-r - 1)`.

Some function `z` with `v_P z ≤ exp (r + 1)` escapes `ω_P`, since `r + 1` exceeds the order.  As
the residue field of `P` is `k`, the function `z` differs from a constant multiple of
`t ^ (-r - 1)` by a function `ω_P` does kill, so the multiple does not escape `ω_P` either. -/
theorem repartitionDualComponent_uniformizer_zpow_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) {P : Place k F} (hdeg : P.degree = 1)
    {t : F} (ht : P.valuation.IsUniformizer t) :
    repartitionDualComponent ω P (t ^ (-weilDifferentialOrder hF hex hmem hω P - 1)) ≠ 0 := by
  set r := weilDifferentialOrder hF hex hmem hω P with hr
  have hordt : P.ord t = 1 := (P.isUniformizer_iff_ord_eq_one).mp ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hordt
    exact absurd hordt (by norm_num)
  have htn0 : t ^ (-r - 1) ≠ 0 := zpow_ne_zero _ ht0
  have hordtn : P.ord (t ^ (-r - 1)) = -r - 1 := by rw [Place.ord_zpow, hordt, mul_one]
  -- Some function with a pole of order at most `r + 1` at `P` escapes `ω_P`.
  have hnot : ¬ ∀ z : F, P.valuation z ≤ WithZero.exp (r + 1) →
      repartitionDualComponent ω P z = 0 := fun h ↦ by
    have := (isGreatest_weilDifferentialOrder hF hex hmem hω P).2 h
    omega
  push Not at hnot
  obtain ⟨z, hz, hz0⟩ := hnot
  have hzne : z ≠ 0 := by
    rintro rfl
    exact hz0 (map_zero _)
  have hzord : -(r + 1) ≤ P.ord z := by
    rw [P.valuation_eq_exp_neg_ord hzne, WithZero.exp_le_exp] at hz
    omega
  -- Correct `z` by a constant multiple of `t ^ (-r - 1)`, using that `P` is rational.
  have hint : z * (t ^ (-r - 1))⁻¹ ∈ P.integers := by
    rw [Place.mem_integers_iff_ord_nonneg, P.ord_mul hzne (inv_ne_zero htn0), Place.ord_inv,
      hordtn]
    omega
  obtain ⟨c, hc⟩ := (Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one P).mp hdeg _ hint
  set u := z * (t ^ (-r - 1))⁻¹ - algebraMap k F c with hu
  have hfactor : z - algebraMap k F c * t ^ (-r - 1) = u * t ^ (-r - 1) := by
    rw [hu, sub_mul, mul_assoc, inv_mul_cancel₀ htn0, mul_one]
  have hkey : P.valuation (z - algebraMap k F c * t ^ (-r - 1)) ≤ WithZero.exp r := by
    rcases eq_or_ne u 0 with hu0 | hu0
    · rw [hfactor, hu0, zero_mul, map_zero]
      exact zero_le
    · have hw0 : z - algebraMap k F c * t ^ (-r - 1) ≠ 0 := by
        rw [hfactor]
        exact mul_ne_zero hu0 htn0
      have hordu : 0 < P.ord u := (P.valuation_lt_one_iff_ord_pos hu0).mp hc
      have hordw : P.ord (z - algebraMap k F c * t ^ (-r - 1)) = P.ord u + (-r - 1) := by
        rw [hfactor, P.ord_mul hu0 htn0, hordtn]
      rw [P.valuation_eq_exp_neg_ord hw0, WithZero.exp_le_exp, hordw]
      omega
  have hvanish := (isGreatest_weilDifferentialOrder hF hex hmem hω P).1 _ hkey
  -- Hence `ω_P z` is the constant `c` times `ω_P (t ^ (-r - 1))`.
  have hsmul : algebraMap k F c * t ^ (-r - 1) = c • t ^ (-r - 1) := (Algebra.smul_def c _).symm
  rw [map_sub, hsmul, map_smul, sub_eq_zero] at hvanish
  intro hzero
  rw [hzero, smul_zero] at hvanish
  exact hz0 hvanish

end TauCeti
