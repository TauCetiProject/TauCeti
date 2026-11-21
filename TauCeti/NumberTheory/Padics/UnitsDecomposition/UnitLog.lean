/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm
import TauCeti.Analysis.Normed.Algebra.Logarithm.Basic
import TauCeti.NumberTheory.Padics.UnitsDecomposition.Quotient

/-!
# The logarithm of a `p`-adic unit

For a prime `p`, put `m = 2 (p - 1)`. The `p`-adic logarithm of a unit `x ∈ ℤ_pˣ` is

`TauCeti.padicUnitLog p x = m⁻¹ log (x ^ m) = m⁻¹ ∑_{n ≥ 1} (-1) ^ (n - 1) (x ^ m - 1) ^ n / n`,

with Mathlib's series `NormedSpace.log`. Since `x ^ (p - 1) ≡ 1 mod p`, and `x ^ 2 ≡ 1 mod 8`
for `p = 2`, the element `x ^ m - 1` lies in `qℤ_p`, where `q = p` for odd `p` and `q = 4` for
`p = 2`; one exponent serves every prime. Precomposing with a character with values in `ℤ_pˣ`,
such as the cyclotomic character `χ`, gives the homomorphism `log χ` that spans first continuous
Galois cohomology of the completed algebraic closure in Tate's calculation.

Write `x = ω(x) u` with `ω(x)` the root of unity `TauCeti.padicUnitsSection p (x mod q)` and
`u ∈ 1 + qℤ_p`. Since `ω(x) ^ m = 1`, the unit logarithm is `log u`, which is `q` times the
logarithmic coordinate of `x` in the decomposition
`TauCeti.padicIntUnitsEquivZModUnitsProd p : ℤ_pˣ ≃ₜ* (ℤ/qℤ)ˣ × ℤ_p`
(`TauCeti.padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd`).
The properties below follow from this decomposition.

## Main declarations

* `TauCeti.padicUnitLog p`: the logarithm `ℤ_pˣ → ℚ_p`, with its series form
  `TauCeti.padicUnitLog_eq_tsum`.
* `TauCeti.padicUnitLogHom p`: the same map as a continuous homomorphism
  `ℤ_pˣ →ₜ* Multiplicative ℚ_p`, from the multiplicative to the additive group.
* `TauCeti.padicUnitLog_eq_zero_iff`: the logarithm vanishes exactly on the roots of unity.
* `TauCeti.padicUnitLog_eq_log`: on `1 + qℤ_p` the unit logarithm is the logarithm series
  itself; for odd `p` this is every `x ≡ 1 mod p` (`TauCeti.padicUnitLog_eq_log_of_ne_two`).
* `TauCeti.range_padicUnitLog`: the image is the disc `qℤ_p = {y : ‖y‖ ≤ ‖q‖}`, that is `pℤ_p`
  for odd `p` (`TauCeti.range_padicUnitLog_of_ne_two`) and `4ℤ_2` for `p = 2`
  (`TauCeti.range_padicUnitLog_two`).

## References

* O. Brinon and B. Conrad, *CMI summer school notes on `p`-adic Hodge theory*, §9.2, p. 139
  (the logarithm on units that kills roots of unity and is the series on principal units), and
  §1.3, p. 9 (the images `pℤ_p` and `4ℤ_2`).
-/

public section

open NormedSpace

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The `p`-adic logarithm of a unit.** For `x ∈ ℤ_pˣ` and `m = 2 (p - 1)`, it is
`m⁻¹ log (x ^ m)`, with Mathlib's logarithm series `NormedSpace.log`; the series converges because
`x ^ m ≡ 1` modulo `p` for odd `p` and modulo `8` for `p = 2`. It is a continuous homomorphism
`ℤ_pˣ → ℚ_p` (`TauCeti.padicUnitLogHom`), vanishing exactly on the roots of unity, and equal to
`log x` on `1 + qℤ_p`, where `q = p` for odd `p` and `q = 4` for `p = 2`. -/
noncomputable def padicUnitLog (x : ℤ_[p]ˣ) : ℚ_[p] :=
  ((2 * (p - 1) : ℕ) : ℚ_[p])⁻¹ * log (((x : ℤ_[p]) : ℚ_[p]) ^ (2 * (p - 1)))

theorem padicUnitLog_def (x : ℤ_[p]ˣ) :
    padicUnitLog p x =
      ((2 * (p - 1) : ℕ) : ℚ_[p])⁻¹ * log (((x : ℤ_[p]) : ℚ_[p]) ^ (2 * (p - 1))) :=
  (rfl)

variable {p}

/-- The order `φ(q)` of `(ℤ/qℤ)ˣ` divides the exponent `m = 2 (p - 1)`. -/
private theorem totient_dvd : (p ^ padicUnitsDepth p).totient ∣ 2 * (p - 1) := by
  rw [Nat.totient_prime_pow hp.out (padicUnitsDepth_pos p)]
  by_cases h : p = 2
  · subst h
    simp
  · rw [padicUnitsDepth_of_ne_two h, Nat.sub_self, pow_zero, one_mul]
    exact Dvd.intro_left 2 rfl

/-- The `m`-th power of a unit is congruent to `1` modulo `q`. -/
private theorem unitsToZModPow_pow (x : ℤ_[p]ˣ) :
    PadicInt.unitsToZModPow (padicUnitsDepth p) (x ^ (2 * (p - 1))) = 1 := by
  obtain ⟨c, hc⟩ := totient_dvd (p := p)
  rw [map_pow, hc, pow_mul, ZMod.pow_totient, one_pow]

private theorem natCast_two_mul_ne_zero : ((2 * (p - 1) : ℕ) : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by have := hp.out.two_le; omega)

/-- **The unit logarithm is `q` times the logarithmic coordinate** of the decomposition
`ℤ_pˣ ≃ₜ* (ℤ/qℤ)ˣ × ℤ_p`, with `q = p ^ padicUnitsDepth p`. -/
theorem padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd (x : ℤ_[p]ˣ) :
    padicUnitLog p x = (p : ℚ_[p]) ^ padicUnitsDepth p *
      ((padicIntUnitsEquivZModUnitsProd p x).2.toAdd : ℚ_[p]) := by
  have h := coe_padicIntUnitsEquivZModUnitsProd_apply_snd (x ^ (2 * (p - 1)))
  rw [unitsToZModPow_pow, map_one, inv_one, one_mul, eq_div_iff pow_padicUnitsDepth_ne_zero] at h
  simp only [map_pow, Prod.pow_snd, toAdd_pow, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, Units.val_pow_eq_pow_val, PadicInt.coe_pow] at h
  rw [padicUnitLog_def, ← h, inv_mul_eq_iff_eq_mul₀ natCast_two_mul_ne_zero]
  ring

/-- The unit logarithm of `x` is the logarithm series at `x / ω(x mod q)`, the principal-unit
part of `x`. -/
theorem padicUnitLog_eq_log_inv_padicUnitsSection_mul (x : ℤ_[p]ˣ) :
    padicUnitLog p x = log ((((padicUnitsSection p
      (PadicInt.unitsToZModPow (padicUnitsDepth p) x))⁻¹ * x : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
  rw [padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd,
    coe_padicIntUnitsEquivZModUnitsProd_apply_snd, mul_div_cancel₀ _ pow_padicUnitsDepth_ne_zero]

/-- The element `x ^ m - 1`, `m = 2 (p - 1)`, lies in the disc of convergence of the logarithm
series. -/
private theorem norm_coe_pow_sub_one_lt_one (x : ℤ_[p]ˣ) :
    ‖((x : ℤ_[p]) : ℚ_[p]) ^ (2 * (p - 1)) - 1‖ < 1 := by
  have h := mem_unitsPrincipal_iff_norm.mp (unitsToZModPow_eq_one_iff.mp (unitsToZModPow_pow x))
  rw [PadicInt.norm_def] at h
  push_cast at h
  exact h.trans_lt (zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt)
    (by simpa using padicUnitsDepth_pos p))

/-- **The series form of the unit logarithm**:
`padicUnitLog p x = m⁻¹ ∑_{n ≥ 0} (-1) ^ n (x ^ m - 1) ^ (n + 1) / (n + 1)`, `m = 2 (p - 1)`. -/
theorem padicUnitLog_eq_tsum (x : ℤ_[p]ˣ) :
    padicUnitLog p x = ((2 * (p - 1) : ℕ) : ℚ_[p])⁻¹ * ∑' n : ℕ,
      (-1 : ℚ_[p]) ^ n * (((x : ℤ_[p]) : ℚ_[p]) ^ (2 * (p - 1)) - 1) ^ (n + 1) / (n + 1) := by
  rw [padicUnitLog_def, congrFun (log_eq_tsum ℚ_[p]), (logSeries_summable_of_norm_lt_one ℚ_[p]
    ℚ_[p] (norm_coe_pow_sub_one_lt_one x)).tsum_eq_zero_add]
  congr 1
  simp only [Nat.cast_zero, div_zero, zero_mul, zero_add, smul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  exact tsum_congr fun n ↦ by ring

variable (p) in
/-- The unit logarithm is additive: `log (x y) = log x + log y`. -/
@[simp]
theorem padicUnitLog_mul (x y : ℤ_[p]ˣ) :
    padicUnitLog p (x * y) = padicUnitLog p x + padicUnitLog p y := by
  simp only [padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd, map_mul, Prod.snd_mul,
    toAdd_mul, PadicInt.coe_add, mul_add]

variable (p) in
@[simp]
theorem padicUnitLog_one : padicUnitLog p 1 = 0 := by
  simp [padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd]

variable (p) in
/-- The unit logarithm is continuous. -/
theorem continuous_padicUnitLog : Continuous (padicUnitLog p) := by
  rw [funext (padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd (p := p))]
  exact continuous_const.mul ((continuous_subtypeVal : Continuous ((↑) : ℤ_[p] → ℚ_[p])).comp
    (continuous_toAdd.comp (padicIntUnitsEquivZModUnitsProd p).continuous.snd))

variable (p) in
/-- **The unit logarithm as a continuous homomorphism** `ℤ_pˣ → ℚ_p`, from the multiplicative
group of units to the additive group of `ℚ_p`. -/
noncomputable def padicUnitLogHom : ℤ_[p]ˣ →ₜ* Multiplicative ℚ_[p] where
  toFun x := .ofAdd (padicUnitLog p x)
  map_one' := by rw [padicUnitLog_one, ofAdd_zero]
  map_mul' x y := by rw [padicUnitLog_mul, ofAdd_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_padicUnitLog p)

@[simp]
theorem padicUnitLogHom_apply (x : ℤ_[p]ˣ) : padicUnitLogHom p x = .ofAdd (padicUnitLog p x) :=
  (rfl)

@[simp]
theorem padicUnitLog_inv (x : ℤ_[p]ˣ) : padicUnitLog p x⁻¹ = -padicUnitLog p x := by
  simpa using congrArg Multiplicative.toAdd (map_inv (padicUnitLogHom p) x)

@[simp]
theorem padicUnitLog_div (x y : ℤ_[p]ˣ) :
    padicUnitLog p (x / y) = padicUnitLog p x - padicUnitLog p y := by
  rw [div_eq_mul_inv, padicUnitLog_mul, padicUnitLog_inv, sub_eq_add_neg]

@[simp]
theorem padicUnitLog_zpow (x : ℤ_[p]ˣ) (n : ℤ) :
    padicUnitLog p (x ^ n) = n * padicUnitLog p x := by
  simpa [zsmul_eq_mul] using congrArg Multiplicative.toAdd (map_zpow (padicUnitLogHom p) x n)

@[simp]
theorem padicUnitLog_pow (x : ℤ_[p]ˣ) (n : ℕ) :
    padicUnitLog p (x ^ n) = n * padicUnitLog p x := by
  simpa using padicUnitLog_zpow x n

/-- **The unit logarithm vanishes exactly on the roots of unity** of `ℤ_p`: the `(p - 1)`-st
roots of unity for odd `p` and `±1` for `p = 2`. -/
theorem padicUnitLog_eq_zero_iff {x : ℤ_[p]ˣ} : padicUnitLog p x = 0 ↔ IsOfFinOrder x := by
  rw [padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd, mul_eq_zero,
    or_iff_right pow_padicUnitsDepth_ne_zero, PadicInt.coe_eq_zero, toAdd_eq_zero,
    ← mem_torsion_padicIntUnits_iff, CommGroup.mem_torsion]

variable (p) in
@[simp]
theorem padicUnitLog_neg_one : padicUnitLog p (-1) = 0 :=
  padicUnitLog_eq_zero_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by simp⟩)

/-- **The unit logarithm is the logarithm series on `1 + qℤ_p`**, where `q = p` for odd `p`
and `q = 4` for `p = 2`. -/
theorem padicUnitLog_eq_log {x : ℤ_[p]ˣ} (hx : x ∈ unitsPrincipal p (padicUnitsDepth p)) :
    padicUnitLog p x = log ((x : ℤ_[p]) : ℚ_[p]) := by
  rw [padicUnitLog_eq_log_inv_padicUnitsSection_mul, unitsToZModPow_eq_one_iff.mpr hx, map_one,
    inv_one, one_mul]

/-- For odd `p`, the unit logarithm of every `x ≡ 1 mod p` is the logarithm series at `x`. -/
theorem padicUnitLog_eq_log_of_ne_two (hp₂ : p ≠ 2) {x : ℤ_[p]ˣ}
    (hx : x ∈ unitsPrincipal p 1) : padicUnitLog p x = log ((x : ℤ_[p]) : ℚ_[p]) :=
  padicUnitLog_eq_log (by rwa [padicUnitsDepth_of_ne_two hp₂])

variable (p) in
/-- The generator `γ = exp q` of `1 + qℤ_p` has unit logarithm `q`. -/
@[simp]
theorem padicUnitLog_padicUnitsGenerator :
    padicUnitLog p (padicUnitsGenerator p) = (p : ℚ_[p]) ^ padicUnitsDepth p := by
  simp [padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd]

variable (p) in
/-- **The image of the unit logarithm is `qℤ_p`**, the closed disc of radius `‖q‖ = p ^ (-k)`,
where `q = p ^ k` with `k = padicUnitsDepth p`. -/
theorem range_padicUnitLog :
    Set.range (padicUnitLog p) = {y : ℚ_[p] | ‖y‖ ≤ (p : ℝ) ^ (-(padicUnitsDepth p : ℤ))} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_ofPred_eq, padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd]
    exact norm_pow_padicUnitsDepth_mul_le _
  · intro hy
    let s : ℤ_[p] := ⟨y / (p : ℚ_[p]) ^ padicUnitsDepth p, div_pow_padicUnitsDepth_mem_subring hy⟩
    obtain ⟨x, hx⟩ := (padicIntUnitsEquivZModUnitsProd p).surjective (1, .ofAdd s)
    refine ⟨x, ?_⟩
    rw [padicUnitLog_eq_mul_padicIntUnitsEquivZModUnitsProd_snd, hx, toAdd_ofAdd]
    exact mul_div_cancel₀ y pow_padicUnitsDepth_ne_zero

/-- The unit logarithm takes values in `qℤ_p`; in particular in `ℤ_p`. -/
theorem norm_padicUnitLog_le (x : ℤ_[p]ˣ) :
    ‖padicUnitLog p x‖ ≤ (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) := by
  have hx : padicUnitLog p x ∈ Set.range (padicUnitLog p) := ⟨x, rfl⟩
  rwa [range_padicUnitLog] at hx

/-- For odd `p` the image of the unit logarithm is `pℤ_p`. -/
theorem range_padicUnitLog_of_ne_two (hp₂ : p ≠ 2) :
    Set.range (padicUnitLog p) = {y : ℚ_[p] | ‖y‖ ≤ (p : ℝ)⁻¹} := by
  rw [range_padicUnitLog, padicUnitsDepth_of_ne_two hp₂, Nat.cast_one, zpow_neg_one]

/-- For `p = 2` the image of the unit logarithm is `4ℤ_2`. -/
theorem range_padicUnitLog_two :
    Set.range (padicUnitLog 2) = {y : ℚ_[2] | ‖y‖ ≤ (4 : ℝ)⁻¹} := by
  rw [range_padicUnitLog, padicUnitsDepth_two]
  norm_num

end TauCeti
