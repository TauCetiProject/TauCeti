/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Radius.Convergence

/-!
# Convergence of power series in valued extensions and Newton slopes

Fix a real additive valuation `v` on a normed division ring `K` and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. At the radius `b ^ σ`, restrictedness of a power
series `f = ∑ aₙ Xⁿ` is the valuation decay condition that for every intercept `c`, eventually
`c + σ n ≤ v(aₙ)` (`PowerSeries.isRestricted_rpow_iff`). In a complete ultrametric target `A` over
`K` with norm-preserving scalar multiplication and powers, summability of `∑ aₙ • xⁿ` at a point
`x : A` of norm `b ^ σ` is therefore equivalent to this same asymptotic valuation condition
(`PowerSeries.summable_smul_pow_iff_eventually_le_addValuation_coeff`).

Comparing the convergence-point radius `PowerSeries.convergenceRadius A f` with the Newton-polygon
formula for `PowerSeries.radius f` separates what depends on the coefficients from what depends on
the value group of `A`:

* in every such target `A`, `f.convergenceRadius A ≤ b ^ λ`, where
  `λ = liminf_{n → ∞} v(aₙ) / n` (`PowerSeries.convergenceRadius_le_exp_linearGrowthInf`);
* in a complete densely normed extension `L` (such as `ℂ_[p]`), `f.convergenceRadius L = b ^ λ`,
  and for admissible series with infinitely many nonzero coefficients it is `b` raised to the
  supremum of the finite slopes of the Newton polygon
  (`PowerSeries.convergenceRadius_eq_exp_linearGrowthInf`,
  `PowerSeries.convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon`);
* when the nonzero norms of `A` are restricted to integer powers `{b ^ m | m : ℤ}` (such as
  `ℚ_[p]` with `b = p`) and `f.radius = b ^ t` with `t : ℝ`, the convergence-point radius is at
  most `b ^ ⌊t⌋`; whenever `t` is not an integer and `A` is complete and attains `b ^ ⌊t⌋`,
  `f.convergenceRadius A = b ^ ⌊t⌋ < b ^ t = f.radius`
  (`PowerSeries.convergenceRadius_le_ofReal_zpow_floor`,
  `PowerSeries.convergenceRadius_eq_ofReal_zpow_floor`).

In particular, over `ℚ_[p]` the series `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` has intrinsic radius `√p`,
convergence-point radius `1` in `ℚ_[p]`, and convergence-point radius `√p` in `ℂ_[p]`
(`PowerSeries.radius_mk_pow_ceil_div_two_padic`,
`PowerSeries.convergenceRadius_padic_mk_pow_ceil_div_two`,
`PowerSeries.convergenceRadius_padicComplex_mk_pow_ceil_div_two`).

## Main results

* `PowerSeries.isRestricted_rpow_iff` and
  `PowerSeries.summable_smul_pow_iff_eventually_le_addValuation_coeff`: valuation criteria for
  restrictedness at `b ^ σ` and convergence at a point of norm `b ^ σ`.
* `PowerSeries.convergenceRadius_eq_exp_linearGrowthInf` and
  `PowerSeries.convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon`: Newton-polygon formulas for
  the convergence-point radius in a complete densely normed extension.
* `PowerSeries.convergenceRadius_le_ofReal_zpow_floor` and
  `PowerSeries.convergenceRadius_eq_ofReal_zpow_floor`: rounding down of the convergence-point
  radius in discretely normed targets, with strict inequality `f.convergenceRadius A < f.radius` at
  non-integral slopes.
* `PowerSeries.convergenceRadius_padic_eq_ofReal_zpow_floor`,
  `PowerSeries.radius_mk_pow_ceil_div_two_padic`,
  `PowerSeries.convergenceRadius_padic_mk_pow_ceil_div_two`, and
  `PowerSeries.convergenceRadius_padicComplex_mk_pow_ceil_div_two`: comparison between `ℚ_[p]` and
  `ℂ_[p]`, witnessed by `∑ₙ p ^ ⌈n / 2⌉ Xⁿ`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6 §§1–2.
-/

public section

open Filter LinearGrowth TauCeti
open scoped NNReal ENNReal Topology

namespace PowerSeries

section Valuation

variable {K : Type*} [NormedDivisionRing K] (f : K⟦X⟧)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Valuation criterion for restrictedness.** A series `f = ∑ aₙ Xⁿ` is restricted at the radius
`b ^ σ` if and only if for every real intercept `c`, eventually `c + σ * n ≤ v (aₙ)`. -/
theorem isRestricted_rpow_iff (σ : ℝ) :
    f.IsRestricted (b ^ σ) ↔
      ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, ((c + σ * n : ℝ) : WithTop ℝ) ≤ v (coeff n f) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [isRestricted_iff']
  refine ⟨fun hf c ↦ ?_, fun h ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_⟩
  · have hmem : Set.Iic (b ^ (-c)) ∈ 𝓝 (0 : ℝ) :=
      Iic_mem_nhds (Real.rpow_pos_of_pos hb0 (-c))
    filter_upwards [hf.eventually hmem] with n hn
    exact (norm_coeff_mul_rpow_pow_le_iff f v hb hv n σ c).mp hn
  · -- Choose `c` with `b ^ (-c) = ε / 2 < ε`.
    set c := -Real.logb b (ε / 2)
    have hpow : b ^ (-c) = ε / 2 := by
      rw [neg_neg, Real.rpow_logb hb0 hb.ne' (half_pos hε)]
    filter_upwards [h c] with n hn
    have hle : ‖coeff n f‖ * (b ^ σ) ^ n ≤ ε / 2 :=
      hpow ▸ (norm_coeff_mul_rpow_pow_le_iff f v hb hv n σ c).mpr hn
    have hnonneg : 0 ≤ ‖coeff n f‖ * (b ^ σ) ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (Real.rpow_nonneg hb0.le σ) n)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact hle.trans_lt (half_lt_self hε)

/-- **Valuation criterion for pointwise convergence.** In a complete ultrametric target `A` over
`K` with norm-preserving scalar multiplication and powers, `∑ aₙ • xⁿ` is summable at a point `x`
of norm `b ^ σ` if and only if for every `c : ℝ`, eventually `c + σ * n ≤ v (aₙ)`. -/
theorem summable_smul_pow_iff_eventually_le_addValuation_coeff {A : Type*} [SeminormedRing A]
    [Module K A] [NormSMulClass K A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {x : A} {σ : ℝ} (hx : ‖x‖ = b ^ σ) :
    (Summable fun n ↦ coeff n f • x ^ n) ↔
      ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, ((c + σ * n : ℝ) : WithTop ℝ) ≤ v (coeff n f) :=
  (summable_smul_pow_iff_isRestricted_of_norm_eq hx).trans (isRestricted_rpow_iff f v hb hv σ)

/-- In any target `A` with norm-preserving scalar multiplication and powers, the convergence-point
radius of `f` is bounded above by `b ^ λ`, where `λ = liminf v(aₙ) / n`. -/
theorem convergenceRadius_le_exp_linearGrowthInf (A : Type*) [SeminormedRing A]
    [SMulZeroClass K A] [NormSMulClass K A] [NormMulClass A] :
    f.convergenceRadius A ≤
      EReal.exp ((linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) * Real.log b) :=
  convergenceRadius_le_radius.trans_eq (radius_eq_exp_linearGrowthInf f v hb hv)

/-- **Convergence-point radius from coefficient growth.** In a complete densely normed field `L`
over `K`, the convergence-point radius of `f` is `b ^ λ`, where `λ = liminf v(aₙ) / n`. -/
theorem convergenceRadius_eq_exp_linearGrowthInf (L : Type*) [DenselyNormedField L] [Module K L]
    [NormSMulClass K L] [CompleteSpace L] :
    f.convergenceRadius L =
      EReal.exp ((linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) * Real.log b) := by
  rw [convergenceRadius_eq_radius, radius_eq_exp_linearGrowthInf f v hb hv]

/-- **Convergence-point radius from Newton slopes.** In a complete densely normed field `L` over
`K`, for admissible coefficient heights with infinitely many nonzero coefficients, the
convergence-point radius of `f` is `b` raised to the supremum of the finite Newton slopes. -/
theorem convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon (L : Type*) [DenselyNormedField L]
    [Module K L] [NormSMulClass K L] [CompleteSpace L]
    (hf : IsAdmissible fun n ↦ v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.convergenceRadius L = EReal.exp ((⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal)) * Real.log b) := by
  rw [convergenceRadius_eq_radius, radius_eq_exp_iSup_unitSlope_newtonPolygon f v hb hv hf hinf]

end Valuation

section DiscreteValueGroup

variable {R A : Type*} [NormedRing R] [SeminormedRing A] {f : R⟦X⟧} {b : ℝ}

/-- When every nonzero norm in `A` is an integer power of `b > 1`, no element of `A` has extended
norm strictly between `b ^ m` and `b ^ (m + 1)`. -/
private theorem ofReal_zpow_succ_le_eNorm_of_lt (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) (m : ℤ) {x : A}
    (hx : ENNReal.ofReal (b ^ m) < ‖x‖ₑ) :
    ENNReal.ofReal (b ^ (m + 1)) ≤ ‖x‖ₑ := by
  have hx0 : ‖x‖ ≠ 0 := by
    intro h0
    have h0' : ‖x‖₊ = 0 := NNReal.eq h0
    simp [eNorm_eq_nnNorm, h0'] at hx
  obtain ⟨k, hk⟩ := hdisc ⟨⟨x, rfl⟩, hx0⟩
  dsimp only at hk
  have heq : ‖x‖ₑ = ENNReal.ofReal (b ^ k) := by
    rw [hk, eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
    rfl
  rw [heq] at hx ⊢
  have hmk : m < k := (zpow_lt_zpow_iff_right₀ hb).mp
    ((ENNReal.ofReal_lt_ofReal_iff (zpow_pos (zero_lt_one.trans hb) k)).mp hx)
  exact ENNReal.ofReal_le_ofReal (zpow_le_zpow_right₀ hb.le (Int.add_one_le_iff.mpr hmk))

/-- **Discrete norm rounding.** If every nonzero norm in `A` is an integer power of `b > 1` and
`f.radius = ENNReal.ofReal (b ^ t)`, then `f.convergenceRadius A ≤ ENNReal.ofReal (b ^ ⌊t⌋)`. -/
theorem convergenceRadius_le_ofReal_zpow_floor [SMulZeroClass R A] [NormSMulClass R A]
    [NormMulClass A] (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) {t : ℝ}
    (hr : f.radius = ENNReal.ofReal (b ^ t)) :
    f.convergenceRadius A ≤ ENNReal.ofReal (b ^ ⌊t⌋) := by
  refine convergenceRadius_le_of_radius_lt
    (fun _ ↦ ofReal_zpow_succ_le_eNorm_of_lt hb hdisc ⌊t⌋) ?_
  rw [hr, ← Real.rpow_intCast b (⌊t⌋ + 1)]
  refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hb) _)).mpr ?_
  exact (Real.rpow_lt_rpow_left_iff hb).mpr (mod_cast Int.lt_floor_add_one t)

/-- **Exact convergence-point radius and strict inequality at non-integral slopes.** Suppose `A` is
complete, every nonzero norm in `A` is an integer power of `b > 1`, and `f.radius` is
`ENNReal.ofReal (b ^ t)` for a non-integer real `t`. If `b ^ ⌊t⌋` is attained by a norm in `A`,
then `f.convergenceRadius A = ENNReal.ofReal (b ^ ⌊t⌋)`. -/
theorem convergenceRadius_eq_ofReal_zpow_floor [Module R A] [NormSMulClass R A] [NormMulClass A]
    [CompleteSpace A] (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) {t : ℝ}
    (ht : ∀ m : ℤ, (m : ℝ) ≠ t) (hatt : b ^ ⌊t⌋ ∈ Set.range (norm : A → ℝ))
    (hr : f.radius = ENNReal.ofReal (b ^ t)) :
    f.convergenceRadius A = ENNReal.ofReal (b ^ ⌊t⌋) := by
  refine le_antisymm (convergenceRadius_le_ofReal_zpow_floor hb hdisc hr) ?_
  obtain ⟨x, hx⟩ := hatt
  have hxe : ‖x‖ₑ = ENNReal.ofReal (b ^ ⌊t⌋) := by
    rw [← hx, eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
    rfl
  have hlt : ‖x‖ₑ < f.radius := by
    rw [hxe, hr, ← Real.rpow_intCast b ⌊t⌋]
    refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hb) t)).mpr ?_
    exact (Real.rpow_lt_rpow_left_iff hb).mpr ((Int.floor_le t).lt_of_ne (ht ⌊t⌋))
  exact hxe ▸ le_convergenceRadius_of_summable (summable_smul_pow_of_lt_radius hlt)

/-- If every nonzero norm in `A` is an integer power of `b > 1` and `f.radius` is
`ENNReal.ofReal (b ^ t)` for a non-integer real `t`, the convergence-point radius in `A` is
strictly smaller than `f.radius`. -/
theorem convergenceRadius_lt_radius_of_not_int [SMulZeroClass R A] [NormSMulClass R A]
    [NormMulClass A] (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) {t : ℝ}
    (ht : ∀ m : ℤ, (m : ℝ) ≠ t) (hr : f.radius = ENNReal.ofReal (b ^ t)) :
    f.convergenceRadius A < f.radius := by
  refine (convergenceRadius_le_ofReal_zpow_floor hb hdisc hr).trans_lt ?_
  rw [hr, ← Real.rpow_intCast b ⌊t⌋]
  refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hb) t)).mpr ?_
  exact (Real.rpow_lt_rpow_left_iff hb).mpr ((Int.floor_le t).lt_of_ne (ht ⌊t⌋))

end DiscreteValueGroup

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- Over `ℚ_[p]`, a power series of radius `p ^ t` for a non-integer real `t` has convergence-point
radius `p ^ ⌊t⌋` in `ℚ_[p]`. -/
theorem convergenceRadius_padic_eq_ofReal_zpow_floor {f : ℚ_[p]⟦X⟧} {t : ℝ}
    (ht : ∀ m : ℤ, (m : ℝ) ≠ t) (hr : f.radius = ENNReal.ofReal ((p : ℝ) ^ t)) :
    f.convergenceRadius ℚ_[p] = ENNReal.ofReal ((p : ℝ) ^ ⌊t⌋) := by
  have hrange := Padic.range_norm_sdiff_singleton_zero p
  exact convergenceRadius_eq_ofReal_zpow_floor (mod_cast (Fact.out : p.Prime).one_lt)
    hrange.subset ht ((hrange.symm.subset ⟨⌊t⌋, rfl⟩).1) hr

/-- For `k ≠ 0`, the coefficient valuations of `∑ₙ p ^ ⌈n / k⌉ Xⁿ` over `ℚ_[p]` have lower linear
growth `1 / k`. -/
theorem linearGrowthInf_padicRealValuation_mk_pow_ceil_div {k : ℕ} (hk : k ≠ 0) :
    (linearGrowthInf fun n : ℕ ↦
      (padicRealValuation p (coeff n (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / k⌉₊))).toEReal) =
        ((1 / (k : ℝ) : ℝ) : EReal) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hval : ∀ m : ℕ, padicRealValuation p ((p : ℚ_[p]) ^ m) = ((m : ℝ) : WithTop ℝ) := fun m ↦ by
    simp [(padicRealValuation p).map_pow]
  apply le_antisymm
  · rw [← linearGrowthInf_const_mul_self (a := ((1 / (k : ℝ) : ℝ) : EReal))]
    refine linearGrowthInf_le_of_eventually_le (b := (1 : EReal)) (EReal.coe_ne_top 1)
      (Eventually.of_forall fun n ↦ ?_)
    rw [coeff_mk, hval, WithTop.toEReal_coe, ← EReal.coe_natCast,
      ← EReal.coe_mul, ← EReal.coe_one, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hlt := (Nat.ceil_lt_add_one (div_nonneg n.cast_nonneg hk_pos.le)).le
    linarith [one_div_mul_eq_div (k : ℝ) (n : ℝ)]
  · refine le_linearGrowthInf_of_affine_le (c := 0) fun n ↦ ?_
    rw [coeff_mk, hval, WithTop.coe_le_coe, zero_add, one_div_mul_eq_div]
    exact Nat.le_ceil _

/-- For `k ≠ 0`, the series `∑ₙ p ^ ⌈n / k⌉ Xⁿ` over `ℚ_[p]` has intrinsic radius
`ENNReal.ofReal (p ^ (1 / k))`. -/
theorem radius_mk_pow_ceil_div_padic {k : ℕ} (hk : k ≠ 0) :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / k⌉₊).radius =
      ENNReal.ofReal ((p : ℝ) ^ (1 / (k : ℝ))) :=
  radius_eq_ofReal_rpow _ (padicRealValuation p) (mod_cast (Fact.out : p.Prime).one_lt)
    (fun _ hx ↦ norm_eq_rpow_neg_padicRealValuation hx)
    (linearGrowthInf_padicRealValuation_mk_pow_ceil_div hk)

variable (p) in
/-- **Intrinsic radius of `∑ₙ p ^ ⌈n / 2⌉ Xⁿ`.** Over `ℚ_[p]`, the series `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` has
intrinsic radius `√p`. -/
theorem radius_mk_pow_ceil_div_two_padic :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius = ENNReal.ofReal √p := by
  simpa [Real.sqrt_eq_rpow] using radius_mk_pow_ceil_div_padic (p := p) (k := 2) two_ne_zero

variable (p) in
/-- **Convergence-point radius of `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` in `ℚ_[p]`.** Because `ℚ_[p]` contains no
element of norm strictly between `1` and `p`, the convergence-point radius in `ℚ_[p]` is `1`. -/
theorem convergenceRadius_padic_mk_pow_ceil_div_two :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergenceRadius ℚ_[p] = 1 := by
  have hnot_int : ∀ m : ℤ, (m : ℝ) ≠ (1 / 2 : ℝ) := by
    intro m hm
    have hmul : (2 * m : ℤ) = (1 : ℤ) := by
      exact_mod_cast (by linarith : (2 : ℝ) * m = 1)
    omega
  have hrad := radius_mk_pow_ceil_div_padic (p := p) (k := 2) two_ne_zero
  simp only [Nat.cast_ofNat] at hrad
  have hfloor : ⌊(1 / 2 : ℝ)⌋ = 0 :=
    Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [convergenceRadius_padic_eq_ofReal_zpow_floor hnot_int hrad, hfloor, zpow_zero,
    ENNReal.ofReal_one]

variable (p) in
/-- **Convergence-point radius of `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` in `ℂ_[p]`.** Passing to `ℂ_[p]` restores
the full intrinsic radius `√p`. -/
theorem convergenceRadius_padicComplex_mk_pow_ceil_div_two :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergenceRadius ℂ_[p] = ENNReal.ofReal √p := by
  rw [convergenceRadius_eq_radius, radius_mk_pow_ceil_div_two_padic]

variable (p) in
/-- For `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` over `ℚ_[p]`, the convergence-point radius in `ℚ_[p]` is strictly
smaller than the intrinsic radius. -/
theorem convergenceRadius_padic_lt_radius_mk_pow_ceil_div_two :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergenceRadius ℚ_[p] <
      (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius := by
  rw [convergenceRadius_padic_mk_pow_ceil_div_two, radius_mk_pow_ceil_div_two_padic,
    ← ENNReal.ofReal_one]
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hsqrt : 1 < √p := (Real.lt_sqrt zero_le_one).mpr (by simpa using hp1)
  exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hsqrt)).mpr hsqrt

end Padic

end PowerSeries
