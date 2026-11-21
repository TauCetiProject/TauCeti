/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Congruence
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.PowerSeries.QPochhammer
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.Data.ZMod.Divisibility
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.QPochhammer
import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Laurent `q_N`-expansions and cusp orders of Siegel functions

For `0 < N` and `v ∈ (ℤ/Nℤ)²`, `g_{v/N}^{12 N}` expands in `q_N = e^{2π i τ / N}` as
`q_N^{m(v)} ψ(q_N)` with `m(v) = 6 N² B₂({v₀ / N}) = 6 r₀² - 6 N r₀ + N²` (`r₀ = (v 0).val`) and
a holomorphic factor `ψ` (a unit at `q_N = 0` when `v ≠ 0`, vanishing identically when `v = 0`).
Its Laurent coefficients lie in `ℤ[ζ_N]` (`ζ_N = e^{2π i / N}`) and transform under
`ζ_N ↦ ζ_N^d` via `(v₀, v₁) ↦ (v₀, d v₁)`. Consequently, every `Γ(N)`-invariant Kubert–Lang
product `∏ᵢ g_{aᵢ/N}^{mᵢ}` is meromorphic at every cusp `γ • ∞`, and for `0 < N` and
`aᵢ ∉ N ℤ²` (whenever `mᵢ ≠ 0`), any cusp-meromorphic product has `12 N` times its `q_N`-order at
`γ • ∞` equal to `∑ᵢ mᵢ · 6 N² B₂({(aᵢ γ)₀ / N})`.

## Main definitions and results

* `TauCeti.ModularForm.siegelPowerCuspExponent`, `siegelPowerCuspExponent_eq_bernoulliFun`,
  `sum_siegelPowerCuspExponent_erase_zero`: `6 r₀² - 6 N r₀ + N² = 6 N² B₂((v 0).val / N)`
  (for `0 < N`), the `q_N`-order of `g_{v/N}^{12 N}` at `i∞` when `v ≠ 0`; its sum over
  `(ℤ/Nℤ)² \ {0}` is `0`.
* `TauCeti.ModularForm.siegelPowerLaurentSeries`, `siegelPowerLaurentSeries_def`,
  `siegelPowerLaurentSeries_zero`, `coeff_siegelPowerLaurentSeries_eq_zero_of_lt`,
  `coeff_siegelPowerLaurentSeries_siegelPowerCuspExponent`, `orderTop_siegelPowerLaurentSeries`,
  `mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries`,
  `mapRingHom_aeval_exp_siegelPowerLaurentSeries`,
  `laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem_adjoin`,
  `laurentQExpansion_siegelFunction_zmod_pow_twelve_mul_coeff_siegelPowerCuspExponent`: universal
  `HahnSeries ℤ ℤ[X]` lift (for `0 < N`), its zero case, defining product formula, order and
  leading coefficient, diagonal `ζ_N ↦ ζ_N^d` action, `ℤ[ζ_N]`-integrality, and leading
  coefficient at `q_N^{siegelPowerCuspExponent N v}` (nonzero iff `v ≠ 0`).
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul`,
  `meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul`,
  `meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_mem_Gamma`,
  `meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow`,
  `natCast_twelve_mul_mul_meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow`: cusp
  meromorphy (from `Γ(N)`-invariance or the Kubert–Lang congruences) and exact `q_N`-orders at
  `γ • ∞` (for `0 < N` and `aᵢ ∉ N ℤ²` whenever `mᵢ ≠ 0`).

## References

* D. S. Kubert, S. Lang, *Modular Units*, GTM 244, Chapter 2, §§1–2, and Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open TauCeti.UpperHalfPlane
open scoped Real Matrix MatrixGroups Manifold Polynomial

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### Cusp exponent and `q_N`-factorization of `g_{v/N}^{12 N}` -/

/-- **The cusp-order exponent of a level-`N` Siegel `(12 N)`-th power**:
`6 r₀² - 6 N r₀ + N²` where `r₀ = (v 0).val`. For `0 < N`, this equals
`6 N² B₂((v 0).val / N)` (`siegelPowerCuspExponent_eq_bernoulliFun`), and when `v ≠ 0` it is the
`q_N`-order of `g_{v/N}^{12 N}` at `i∞`. -/
def siegelPowerCuspExponent (N : ℕ) (v : Fin 2 → ZMod N) : ℤ :=
  6 * ((v 0).val : ℤ) ^ 2 - 6 * (N : ℤ) * (v 0).val + (N : ℤ) ^ 2

/-- Defining formula for `siegelPowerCuspExponent`. -/
theorem siegelPowerCuspExponent_def (N : ℕ) (v : Fin 2 → ZMod N) :
    siegelPowerCuspExponent N v =
      6 * ((v 0).val : ℤ) ^ 2 - 6 * (N : ℤ) * (v 0).val + (N : ℤ) ^ 2 :=
  (rfl)

/-- `siegelPowerCuspExponent N v` depends only on the first coordinate `v 0`. -/
theorem siegelPowerCuspExponent_congr {N : ℕ} {v w : Fin 2 → ZMod N} (h : v 0 = w 0) :
    siegelPowerCuspExponent N v = siegelPowerCuspExponent N w := by
  simp only [siegelPowerCuspExponent, h]

/-- If `v 0 = 0`, then `siegelPowerCuspExponent N v = N ^ 2`. -/
theorem siegelPowerCuspExponent_of_apply_zero_eq_zero {N : ℕ} {v : Fin 2 → ZMod N}
    (hv : v 0 = 0) :
    siegelPowerCuspExponent N v = (N : ℤ) ^ 2 := by
  simp [siegelPowerCuspExponent, hv]

/-- At `v = 0`, `siegelPowerCuspExponent N 0 = N ^ 2`. -/
@[simp]
theorem siegelPowerCuspExponent_zero (N : ℕ) : siegelPowerCuspExponent N 0 = (N : ℤ) ^ 2 :=
  siegelPowerCuspExponent_of_apply_zero_eq_zero rfl

/-- At `v = ![0, y]`, `siegelPowerCuspExponent N ![0, y] = N ^ 2`. -/
@[simp]
theorem siegelPowerCuspExponent_cons_zero (N : ℕ) (y : ZMod N) :
    siegelPowerCuspExponent N ![0, y] = (N : ℤ) ^ 2 :=
  siegelPowerCuspExponent_of_apply_zero_eq_zero rfl

/-- `siegelPowerCuspExponent` is invariant under negation of the division vector. -/
@[simp]
theorem siegelPowerCuspExponent_neg {N : ℕ} (v : Fin 2 → ZMod N) :
    siegelPowerCuspExponent N (-v) = siegelPowerCuspExponent N v := by
  rcases eq_or_ne N 0 with rfl | hN; · simp [siegelPowerCuspExponent, ZMod.val_neg']
  have : NeZero N := ⟨hN⟩
  rcases eq_or_ne (v 0) 0 with hv0 | hv0; · simp [siegelPowerCuspExponent, hv0]
  have : NeZero (v 0) := ⟨hv0⟩
  simp only [siegelPowerCuspExponent, Pi.neg_apply, ZMod.val_neg_of_ne_zero (v 0),
    Nat.cast_sub (v 0).val_lt.le]
  ring

/-- For `[NeZero N]`, `siegelPowerCuspExponent N (a mod N)` equals `6 N² B₂({a₀ / N})`, where
`{x} = Int.fract x` is the fractional part and `B₂` is the second Bernoulli polynomial. -/
theorem siegelPowerCuspExponent_eq_bernoulliFun {N : ℕ} [NeZero N] (a : Fin 2 → ℤ) :
    (siegelPowerCuspExponent N (fun i ↦ (a i : ZMod N)) : ℝ) =
      6 * (N : ℝ) ^ 2 * bernoulliFun 2 (Int.fract ((a 0 : ℝ) / N)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [siegelPowerCuspExponent, Int.fract_div_intCast_eq_div_intCast_mod, bernoulliFun_two]
  push_cast
  rw [← Int.cast_natCast (a 0 : ZMod N).val, ZMod.val_intCast]
  field_simp

/-- The sum of `siegelPowerCuspExponent N v` over all nonzero `v ∈ (ℤ/Nℤ)²` vanishes. -/
theorem sum_siegelPowerCuspExponent_erase_zero (N : ℕ) [NeZero N] :
    ∑ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0, siegelPowerCuspExponent N v = 0 := by
  set f : ℕ → ℤ := fun k ↦ 6 * (k : ℤ) ^ 2 - 6 * (N : ℤ) * k + (N : ℤ) ^ 2
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 2 → ZMod N)),
    siegelPowerCuspExponent_zero, sub_eq_zero,
    Fintype.sum_equiv (piFinTwoEquiv fun _ ↦ ZMod N) (siegelPowerCuspExponent N)
      (fun p ↦ f p.1.val) (fun v ↦ siegelPowerCuspExponent_def N v),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Fintype.sum_equiv (ZMod.finEquiv N).toEquiv (fun k : Fin N ↦ f k) (fun r ↦ f r.val)
      (fun k ↦ by simp [ZMod.val_natCast_of_lt k.isLt]), Fin.sum_univ_eq_sum_range f N]
  have hterm (k : ℕ) : f k = (k : ℤ) ^ 2 * 6 - 3 * (N : ℤ) * ((k : ℤ) * 2) + (N : ℤ) ^ 2 := by
    dsimp [f]; ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_range_natCast_sq_mul_six, Finset.sum_range_natCast_mul_two,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The holomorphic factor `ψ_{N, v}(τ)` in `g_{v/N}(τ)^{12N} = q_N^{m(v)} ψ_{N, v}(τ)`; for
`0 < N`, it is a unit at `q_N = 0` when `v ≠ 0` and vanishes identically when `v = 0`. -/
private def siegelUnitFun (N : ℕ) (v : Fin 2 → ZMod N) : ℍ → ℂ :=
  let ω := cexp (2 * π * I / N) ^ (v 1).val
  (fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) *
    (fun τ : ℍ ↦ 1 - ω * 𝕢 N τ ^ (v 0).val) ^ (12 * N) *
    (fun τ : ℍ ↦ qPochhammerFun N (N + (v 0).val) ω (𝕢 N τ)) ^ (12 * N) *
    (fun τ : ℍ ↦ qPochhammerFun N (N - (v 0).val) (ω ^ (N - 1)) (𝕢 N τ)) ^ (12 * N)

/-- Exact factorization
`g_{v/N}(τ)^{12 N} = q_N^{siegelPowerCuspExponent N v} * siegelUnitFun N v τ`. -/
private theorem siegelFunction_zmod_pow_twelve_mul_eq {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N)
    (τ : ℍ) :
    siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) =
      𝕢 N τ ^ siegelPowerCuspExponent N v * siegelUnitFun N v τ := by
  have hN : 0 < N := NeZero.pos N
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let ω := cexp (2 * π * I / N) ^ (v 1).val
  have hωN : ω ^ N = 1 := by
    rw [← pow_mul, mul_comm (v 1).val N, pow_mul,
      (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one, one_pow]
  have hω_inv : ω⁻¹ = ω ^ (N - 1) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hN, hωN])
  have hq1 : cexp (2 * π * I * (τ : ℂ)) = 𝕢 N τ ^ N := by
    simpa [Function.Periodic.qParam] using
      (TauCeti.Periodic.qParam_nat_mul_pow (h := 1) hN.ne' (τ : ℂ)).symm
  have hw : cexp (2 * π * I * ((((v 0).val : ℝ) / N : ℝ) * (τ : ℂ) +
      (((v 1).val : ℝ) / N : ℝ))) = ω * 𝕢 N τ ^ (v 0).val := by
    simp only [ω, Function.Periodic.qParam, ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1; push_cast; field_simp; ring
  have hB : cexp (π * I * bernoulliFun 2 (((v 0).val : ℝ) / N) * (τ : ℂ)) ^ (12 * N) =
      𝕢 N τ ^ siegelPowerCuspExponent N v := by
    rw [Function.Periodic.qParam, ← Complex.exp_natCast_mul, ← Complex.exp_intCast_mul,
      bernoulliFun_two, siegelPowerCuspExponent]; congr 1; push_cast; field_simp; ring
  have hph : cexp (π * I * ((((v 1).val : ℝ) / N : ℝ) : ℂ) *
      ((((v 0).val : ℝ) / N : ℝ) - 1)) ^ (12 * N) = ω ^ (6 * (v 0).val) := by
    have hexp : ((12 * N : ℕ) : ℂ) * (π * I * ((((v 1).val : ℝ) / N : ℝ) : ℂ) *
        ((((v 0).val : ℝ) / N : ℝ) - 1)) =
        ((6 * (v 0).val * (v 1).val : ℕ) : ℂ) * (2 * π * I / N) +
          (-(6 * ((v 1).val : ℤ)) : ℤ) * (2 * π * I) := by push_cast; field_simp; ring
    rw [← Complex.exp_natCast_mul, hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one, Complex.exp_natCast_mul]
    simp only [ω, ← pow_mul, mul_comm (6 * (v 0).val) (v 1).val, mul_assoc]
  rw [siegelFunction_eq_mul_tprod_mul_tprod _ τ.im_pos, Complex.exp_neg, hq1, hw,
    tprod_one_sub_pow_succ_mul_eq_qPochhammerFun,
    tprod_one_sub_pow_succ_mul_inv_eq_qPochhammerFun (v 0).val_lt.le ω
      (Function.Periodic.qParam_ne_zero _), hω_inv]
  simp only [neg_mul, neg_pow, Even.neg_one_pow (⟨6 * N, by ring⟩ : Even (12 * N)), one_mul,
    mul_pow, hB, hph, siegelUnitFun, Pi.mul_apply, Pi.pow_apply, ω]; ring

/-- Function-level factorization
`g_{v/N}^{12 N} = q_N^{siegelPowerCuspExponent N v} * siegelUnitFun N v`. -/
private theorem siegelFunction_zmod_pow_twelve_mul_eq_fun {N : ℕ} [NeZero N]
    (v : Fin 2 → ZMod N) :
    (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelPowerCuspExponent N v * siegelUnitFun N v τ :=
  funext (siegelFunction_zmod_pow_twelve_mul_eq v)

/-! ### Universal polynomial Laurent series and diagonal cyclotomic action -/

/-- Universal power series over `ℤ[X]` whose evaluation at `X = e^{2π i / N}` (for `0 < N`) is the
`q_N`-expansion of `siegelUnitFun N v`. -/
private def siegelUnitPowerSeries (N : ℕ) (v : Fin 2 → ZMod N) : PowerSeries ℤ[X] :=
  PowerSeries.C (Polynomial.X ^ (6 * (v 0).val * (v 1).val)) *
    (1 - PowerSeries.C (Polynomial.X ^ (v 1).val) * PowerSeries.X ^ (v 0).val) ^ (12 * N) *
    qPochhammerSeries N (N + (v 0).val) (Polynomial.X ^ (v 1).val) ^ (12 * N) *
    qPochhammerSeries N (N - (v 0).val) (Polynomial.X ^ ((N - 1) * (v 1).val)) ^ (12 * N)

/-- **Universal polynomial Laurent series of `g_{v/N}^{12N}`**: a formal Laurent series in
`HahnSeries ℤ ℤ[X]` whose coefficientwise evaluation at `X = e^{2π i / N}` equals the Laurent
`q_N`-expansion of `g_{v/N}^{12 N}` for `0 < N`. -/
def siegelPowerLaurentSeries (N : ℕ) (v : Fin 2 → ZMod N) : HahnSeries ℤ ℤ[X] :=
  HahnSeries.single (siegelPowerCuspExponent N v) 1 *
    HahnSeries.ofPowerSeries ℤ ℤ[X] (siegelUnitPowerSeries N v)

/-- Defining product formula for `siegelPowerLaurentSeries` in terms of `qPochhammerSeries`. -/
theorem siegelPowerLaurentSeries_def (N : ℕ) (v : Fin 2 → ZMod N) :
    siegelPowerLaurentSeries N v =
      HahnSeries.single (siegelPowerCuspExponent N v) 1 *
        HahnSeries.ofPowerSeries ℤ ℤ[X]
          (PowerSeries.C (Polynomial.X ^ (6 * (v 0).val * (v 1).val)) *
            (1 - PowerSeries.C (Polynomial.X ^ (v 1).val) * PowerSeries.X ^ (v 0).val) ^ (12 * N) *
            qPochhammerSeries N (N + (v 0).val) (Polynomial.X ^ (v 1).val) ^ (12 * N) *
            qPochhammerSeries N (N - (v 0).val)
              (Polynomial.X ^ ((N - 1) * (v 1).val)) ^ (12 * N)) :=
  (rfl)

/-- Coefficients of `siegelPowerLaurentSeries N v` vanish strictly below
`siegelPowerCuspExponent N v`. -/
theorem coeff_siegelPowerLaurentSeries_eq_zero_of_lt (N : ℕ) (v : Fin 2 → ZMod N)
    {n : ℤ} (hn : n < siegelPowerCuspExponent N v) :
    (siegelPowerLaurentSeries N v).coeff n = 0 := by
  rw [siegelPowerLaurentSeries, HahnSeries.coeff_single_mul, one_mul,
    HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  rintro ⟨m, hm⟩
  simp only [Nat.castOrderEmbedding_apply] at hm
  omega

/-- For `0 < N`, the universal Laurent series at `v = 0` vanishes identically. -/
@[simp]
theorem siegelPowerLaurentSeries_zero (N : ℕ) [NeZero N] :
    siegelPowerLaurentSeries N 0 = 0 := by
  have hN : 0 < N := NeZero.pos N
  simp [siegelPowerLaurentSeries, siegelUnitPowerSeries, show (12 * N : ℕ) ≠ 0 by positivity]

private theorem constantCoeff_siegelUnitPowerSeries {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    (siegelUnitPowerSeries N v).constantCoeff =
      Polynomial.X ^ (6 * (v 0).val * (v 1).val) *
        (if v 0 = 0 then (1 - Polynomial.X ^ (v 1).val) ^ (12 * N) else 1) := by
  have hr₀ : (v 0).val < N := (v 0).val_lt
  simp only [siegelUnitPowerSeries, map_mul, map_pow, map_sub, map_one,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
    constantCoeff_qPochhammerSeries (by omega : 0 < N + (v 0).val),
    constantCoeff_qPochhammerSeries (by omega : 0 < N - (v 0).val),
    one_pow, mul_one]
  by_cases hv0 : v 0 = 0
  · simp [hv0]
  · simp [hv0, zero_pow (mt (ZMod.val_eq_zero _).mp hv0)]

/-- For `0 < N`, the coefficient of `siegelPowerLaurentSeries N v` at
`siegelPowerCuspExponent N v`. -/
theorem coeff_siegelPowerLaurentSeries_siegelPowerCuspExponent {N : ℕ} [NeZero N]
    (v : Fin 2 → ZMod N) :
    (siegelPowerLaurentSeries N v).coeff (siegelPowerCuspExponent N v) =
      Polynomial.X ^ (6 * (v 0).val * (v 1).val) *
        (if v 0 = 0 then (1 - Polynomial.X ^ (v 1).val) ^ (12 * N) else 1) := by
  have h0 : (HahnSeries.ofPowerSeries ℤ ℤ[X] (siegelUnitPowerSeries N v)).coeff 0 =
      (siegelUnitPowerSeries N v).constantCoeff := by
    simpa using HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (siegelUnitPowerSeries N v) 0
  rw [siegelPowerLaurentSeries, HahnSeries.coeff_single_mul, one_mul, sub_self, h0,
    constantCoeff_siegelUnitPowerSeries]

/-- For `0 < N` and `v ≠ 0`, `siegelPowerLaurentSeries N v` has order
`siegelPowerCuspExponent N v`. -/
theorem orderTop_siegelPowerLaurentSeries {N : ℕ} [NeZero N] {v : Fin 2 → ZMod N}
    (hv : v ≠ 0) :
    (siegelPowerLaurentSeries N v).orderTop = siegelPowerCuspExponent N v := by
  have hne : (siegelPowerLaurentSeries N v).coeff (siegelPowerCuspExponent N v) ≠ 0 := by
    rw [coeff_siegelPowerLaurentSeries_siegelPowerCuspExponent]
    refine mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) ?_
    split_ifs with hv0
    · refine pow_ne_zero _ (sub_ne_zero.mpr fun h1 ↦ hv ?_)
      have hv1 : (v 1).val = 0 := by
        simpa using (congrArg Polynomial.natDegree h1).symm
      ext i; fin_cases i
      · exact hv0
      · exact ZMod.val_injective N (by simpa using hv1)
    · exact one_ne_zero
  refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hne) ?_
  rw [HahnSeries.le_orderTop_iff_forall]
  intro n hn
  exact coeff_siegelPowerLaurentSeries_eq_zero_of_lt N v (WithTop.coe_lt_coe.mp hn)

private theorem analyticAt_cuspFunction_siegelUnitFun {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    AnalyticAt ℂ (cuspFunction N (siegelUnitFun N v)) 0 := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set ω := cexp (2 * π * I / N) ^ (v 1).val
  exact analyticAt_cuspFunction_mul
    (analyticAt_cuspFunction_mul
      (analyticAt_cuspFunction_mul (analyticAt_cuspFunction_const N _)
        (analyticAt_cuspFunction_pow (analyticAt_cuspFunction_one_sub_mul_qParam_pow N _ ω) _))
      (analyticAt_cuspFunction_pow (analyticAt_cuspFunction_qPochhammerFun hNR hN _ ω) _))
    (analyticAt_cuspFunction_pow (analyticAt_cuspFunction_qPochhammerFun hNR hN _ (ω ^ (N - 1))) _)

private theorem map_aeval_siegelUnitPowerSeries {N : ℕ} (v : Fin 2 → ZMod N) (z : ℂ) :
    (siegelUnitPowerSeries N v).map (Polynomial.aeval z).toRingHom =
      PowerSeries.C ((z ^ (v 1).val) ^ (6 * (v 0).val)) *
        (1 - PowerSeries.C (z ^ (v 1).val) * PowerSeries.X ^ (v 0).val) ^ (12 * N) *
        qPochhammerSeries N (N + (v 0).val) (z ^ (v 1).val) ^ (12 * N) *
        qPochhammerSeries N (N - (v 0).val) ((z ^ (v 1).val) ^ (N - 1)) ^ (12 * N) := by
  simp only [siegelUnitPowerSeries, map_mul, map_pow, map_sub, map_one, PowerSeries.map_C,
    PowerSeries.map_X, map_qPochhammerSeries, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.aeval_X]
  simp only [← map_pow, ← pow_mul, mul_comm (v 1).val]

private theorem qExpansion_siegelUnitFun {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    qExpansion N (siegelUnitFun N v) =
      (siegelUnitPowerSeries N v).map (Polynomial.aeval (cexp (2 * π * I / N))).toRingHom := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set ω := cexp (2 * π * I / N) ^ (v 1).val
  have h0 := analyticAt_cuspFunction_const N (ω ^ (6 * (v 0).val))
  have h1 := analyticAt_cuspFunction_one_sub_mul_qParam_pow N (v 0).val ω
  have h2 := analyticAt_cuspFunction_qPochhammerFun hNR hN (N + (v 0).val) ω
  have h3 := analyticAt_cuspFunction_qPochhammerFun hNR hN (N - (v 0).val) (ω ^ (N - 1))
  have hp1 := analyticAt_cuspFunction_pow h1 (12 * N)
  have hp2 := analyticAt_cuspFunction_pow h2 (12 * N)
  have hp3 := analyticAt_cuspFunction_pow h3 (12 * N)
  rw [siegelUnitFun, _root_.UpperHalfPlane.qExpansion_mul
      (analyticAt_cuspFunction_mul (analyticAt_cuspFunction_mul h0 hp1) hp2) hp3,
    _root_.UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_mul h0 hp1) hp2,
    _root_.UpperHalfPlane.qExpansion_mul h0 hp1, qExpansion_const, qExpansion_pow h1,
    qExpansion_pow h2, qExpansion_pow h3, qExpansion_one_sub_mul_qParam_pow hNR (v 0).val ω,
    qExpansion_qPochhammerFun hNR hN (N + (v 0).val) ω,
    qExpansion_qPochhammerFun hNR hN (N - (v 0).val) (ω ^ (N - 1)),
    map_aeval_siegelUnitPowerSeries]

/-- **Diagonal cyclotomic action on the Laurent `q_N`-expansion of `g_{v/N}^{12N}`.**
For `0 < N`, evaluating `siegelPowerLaurentSeries N v` at `X = e^{2π i / N}^d` yields the Laurent
`q_N`-expansion of `g_{(v₀, d v₁)/N}^{12 N}`. -/
theorem mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries {N : ℕ} [NeZero N]
    (v : Fin 2 → ZMod N) (d : ℕ) :
    HahnSeries.mapRingHom (Polynomial.aeval (cexp (2 * π * I / N) ^ d)).toRingHom
        (siegelPowerLaurentSeries N v) =
      laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((![v 0, (d : ZMod N) * v 1] i).val : ℝ) / N) τ ^ (12 * N)) := by
  set v' : Fin 2 → ZMod N := ![v 0, (d : ZMod N) * v 1]
  have hN : 0 < N := NeZero.pos N
  set ζ := cexp (2 * π * I / N)
  have hpow : (ζ ^ d) ^ (v 1).val = ζ ^ (v' 1).val := by
    have hv1 : (v' 1).val = (d * (v 1).val) % N := by simp [v', ZMod.val_mul]
    rw [← pow_mul, hv1, ← pow_eq_pow_mod _ (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one]
  have hunit : (siegelUnitPowerSeries N v).map (Polynomial.aeval (ζ ^ d)).toRingHom =
      (siegelUnitPowerSeries N v').map (Polynomial.aeval ζ).toRingHom := by
    have h0 : (v' 0).val = (v 0).val := rfl
    rw [map_aeval_siegelUnitPowerSeries, map_aeval_siegelUnitPowerSeries, hpow, h0]
  rw [siegelFunction_zmod_pow_twelve_mul_eq_fun v',
    laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr hN)
      (siegelPowerCuspExponent N v') (analyticAt_cuspFunction_siegelUnitFun v').meromorphicAt,
    laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelUnitFun v'),
    qExpansion_siegelUnitFun v', ← hunit, ← siegelPowerCuspExponent_congr (v := v) (w := v') rfl,
    siegelPowerLaurentSeries, map_mul, HahnSeries.mapRingHom_single, map_one,
    HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries]

/-- For `0 < N`, evaluating `siegelPowerLaurentSeries N v` at `ζ_N = e^{2π i / N}` gives the
Laurent `q_N`-expansion of `g_{v/N}^{12 N}`. -/
theorem mapRingHom_aeval_exp_siegelPowerLaurentSeries {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    HahnSeries.mapRingHom (Polynomial.aeval (cexp (2 * π * I / N))).toRingHom
        (siegelPowerLaurentSeries N v) =
      laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)) := by
  have hv : ![v 0, v 1] = v := FinVec.etaExpand_eq v
  simpa [hv] using mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries v 1

/-- **Every Laurent `q_N`-coefficient of `g_{a/N}^{12 N}` lies in `ℤ[ζ_N]`**, where
`ζ_N = e^{2π i / N}`. For `0 < N`, these are the coefficients of the `q_N`-expansion at `i∞`;
at `N = 0`, division by zero makes the function identically `1`. -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem_adjoin {N : ℕ}
    (a : Fin 2 → ℤ) (n : ℤ) :
    (laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N))).coeff n ∈
      Algebra.adjoin ℤ {cexp (2 * π * I / N)} := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hconst : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ ^ (12 * 0)) =
        1 := funext fun _ ↦ by simp
    rw [hconst, laurentQExpansion_one]
    by_cases hn : n = 0 <;> simp [hn, one_mem, zero_mem]
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) :=
    funext fun τ ↦ siegelFunction_div_pow_twelve_mul_eq_zmod (dvd_mul_left N 6) a τ.im_pos
  rw [hfun, ← mapRingHom_aeval_exp_siegelPowerLaurentSeries v, HahnSeries.coeff_mapRingHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨(siegelPowerLaurentSeries N v).coeff n, rfl⟩

/-! ### Cusp meromorphy, cusp orders, and leading coefficients -/

/-- The constant term of `siegelUnitFun N v` at `i∞` (`q_N = 0`). -/
private theorem qExpansion_siegelUnitFun_coeff_zero {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    (qExpansion N (siegelUnitFun N v)).coeff 0 =
      cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
        (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
  rw [qExpansion_siegelUnitFun, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_siegelUnitPowerSeries]
  simp only [map_mul, map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
  split_ifs <;> simp

/-- For `v ≠ 0` in `Fin 2 → ZMod N`, the leading unit term of `g_{v/N}^{12N}` at `i∞` is nonzero. -/
private theorem qExpansion_siegelUnitFun_coeff_zero_ne_zero {N : ℕ} [NeZero N]
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) : (qExpansion N (siegelUnitFun N v)).coeff 0 ≠ 0 := by
  rw [qExpansion_siegelUnitFun_coeff_zero]
  refine mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) ?_
  split_ifs with hv0
  · refine pow_ne_zero _ (sub_ne_zero.mpr fun h1 ↦ hv ?_)
    have hv1 : (v 1).val = 0 := Nat.eq_zero_of_dvd_of_lt
      ((Complex.isPrimitiveRoot_exp N (NeZero.ne N)).dvd_of_pow_eq_one _ h1.symm) (v 1).val_lt
    ext i; fin_cases i
    · exact hv0
    · exact ZMod.val_injective N (by simpa using hv1)
  · exact one_ne_zero

/-- **The Laurent `q_N`-coefficient of `g_{v/N}^{12 N}` at `q_N^{siegelPowerCuspExponent N v}`.**
For `0 < N` and `v ≠ 0`, this is the nonzero leading Laurent `q_N`-coefficient of `g_{v/N}^{12 N}`;
when `v = 0`, it equals `0` (since `g_0 = 0` has the zero Laurent series). -/
theorem laurentQExpansion_siegelFunction_zmod_pow_twelve_mul_coeff_siegelPowerCuspExponent
    {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    (laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))).coeff
          (siegelPowerCuspExponent N v) =
      cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
        (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
  rw [siegelFunction_zmod_pow_twelve_mul_eq_fun v,
    laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
      (siegelPowerCuspExponent N v) (analyticAt_cuspFunction_siegelUnitFun v).meromorphicAt,
    laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelUnitFun v),
    HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  simpa using qExpansion_siegelUnitFun_coeff_zero v

private theorem siegelFunction_div_pow_twelve_mul_smul_eq_qParam_mul {N : ℕ} [NeZero N]
    (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) =
      fun τ : ℍ ↦
        𝕢 N τ ^ siegelPowerCuspExponent N
            (fun i ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N)) *
          siegelUnitFun N (fun i ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N)) τ :=
  funext fun τ ↦ by
    rw [siegelFunction_div_pow_twelve_mul_smul_eq_zmod (dvd_mul_left N 6) a γ τ]
    exact congrFun (siegelFunction_zmod_pow_twelve_mul_eq_fun _) τ

/-- **Cusp meromorphy of `g_{a/N}(γ • τ)^{12 N}` at `q_N = 0`.** For `0 < N`, this is
meromorphy at every cusp `γ • ∞` in the cusp coordinate `q_N`; at `N = 0`, the exponent `12 * 0`
makes the function identically `1`. -/
theorem meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul (N : ℕ) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [mul_zero, pow_zero]; exact meromorphicAt_cuspFunction_const 1
  have : NeZero N := ⟨hN⟩
  rw [siegelFunction_div_pow_twelve_mul_smul_eq_qParam_mul a γ]
  exact meromorphicAt_cuspFunction_qParam_zpow_mul _
    (analyticAt_cuspFunction_siegelUnitFun _).meromorphicAt

/-- **Cusp order of `g_{a/N}^{12 N}` at `γ • ∞`.** For `0 < N` and `a ∉ N ℤ²`, the `q_N`-order of
`τ ↦ g_{a/N}(γ • τ)^{12 N}` at `i∞` is `siegelPowerCuspExponent N ((a γ) mod N)`. -/
theorem meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul {N : ℕ} [NeZero N]
    {a : Fin 2 → ℤ} (ha : (fun i ↦ (a i : ZMod N)) ≠ 0) (γ : SL(2, ℤ)) :
    meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) 0 =
      siegelPowerCuspExponent N (fun i ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N)) := by
  set b := a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  set v : Fin 2 → ZMod N := fun i ↦ (b i : ZMod N)
  set e := (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv
  have hv_eq : v = e (fun i ↦ (a i : ZMod N)) := by
    ext j
    simpa [v, b, e, Matrix.SpecialLinearGroup.vecMulEquiv_apply, Function.comp_def, eq_intCast]
      using ((Int.castRingHom (ZMod N)).map_vecMul (γ : Matrix (Fin 2) (Fin 2) ℤ) a j)
  have hv : v ≠ 0 := by
    rw [hv_eq, ← Matrix.SpecialLinearGroup.vecMulEquiv_zero
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ)]
    exact e.injective.ne ha
  rw [← orderTop_laurentQExpansion
      (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N a γ),
    siegelFunction_div_pow_twelve_mul_smul_eq_qParam_mul a γ,
    laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
      (siegelPowerCuspExponent N v) (analyticAt_cuspFunction_siegelUnitFun v).meromorphicAt,
    laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelUnitFun v),
    HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero, PowerSeries.orderTop_coe]
  have hord : (qExpansion N (siegelUnitFun N v)).order = 0 :=
    nonpos_iff_eq_zero.mp (PowerSeries.order_le 0 (qExpansion_siegelUnitFun_coeff_zero_ne_zero hv))
  simp [hord]

/-! ### Cusp meromorphy and cusp orders of `Γ(N)`-invariant Siegel products -/

private theorem prod_siegelFunction_div_zpow_eq_finset_prod {N : ℕ} {ι : Type*}
    (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ) (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
      ∏ i ∈ s, fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i :=
  funext fun _ ↦ by simp only [Finset.prod_apply]

private theorem prod_siegelFunction_div_zpow_filter_ne_zero {N : ℕ} {ι : Type*}
    (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ) (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
      fun τ : ℍ ↦
        ∏ i ∈ s.filter (m · ≠ 0), siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i :=
  funext fun _ ↦
    (Finset.prod_filter_of_ne (p := (m · ≠ 0)) fun _ _ h h0 ↦ h (by simp [h0])).symm

private theorem prod_siegelFunction_div_zpow_pow_twelve_mul (N : ℕ) {ι : Type*}
    (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ) (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦
        (∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) ^ (12 * N)) =
      ∏ i ∈ s,
        (fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m i :=
  funext fun τ ↦ by
    simpa only [Pi.pow_apply, Finset.prod_apply] using
      Finset.prod_zpow_pow s
        (fun i ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ)) m (12 * N)

private theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_ne_zero
    {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, (fun j ↦ (a i j : ZMod N)) ≠ 0)
    (hinv : ∀ {δ : SL(2, ℤ)}, δ ∈ CongruenceSubgroup.Gamma N → ∀ τ : ℍ,
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(δ • τ) ^ m i =
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i)
    (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 := by
  set F : ℍ → ℂ := fun τ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i
  have hF_mdiff : MDiff F := by
    have hF_eq : F = ∏ i ∈ s, fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i := by
      simpa only [one_smul] using prod_siegelFunction_div_zpow_eq_finset_prod (N := N) s a m 1
    rw [hF_eq]
    refine MDifferentiable.prod fun i hi τ ↦ ?_
    have hne : siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ≠ 0 :=
      mt (siegelFunction_div_eq_zero_iff (a i) τ.im_pos).mp (ha i hi)
    rcases Int.eq_nat_or_neg (m i) with ⟨k, hk | hk⟩
    · simpa only [hk, zpow_natCast, Pi.pow_def] using (mdifferentiable_siegelFunction _ τ).pow k
    · simpa only [hk, zpow_neg, zpow_natCast, Pi.inv_def, Pi.pow_def] using
        ((mdifferentiable_siegelFunction _ τ).pow k).inv (pow_ne_zero k hne)
  have hγ : MDiff (fun τ : ℍ ↦ γ • τ) := by
    convert mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) (by simp) using 1
    funext τ; exact (Matrix.SpecialLinearGroup.mapGL_smul γ τ).symm
  have hper : Function.Periodic ((fun τ : ℍ ↦ F (γ • τ)) ∘ ofComplex) N :=
    TauCeti.periodic_smul_comp_ofComplex_of_Gamma_invariant (fun _ hδ τ ↦ hinv hδ τ) γ
  refine meromorphicAt_cuspFunction_of_pow (Nat.cast_pos.mpr (NeZero.pos N))
    (hF_mdiff.comp hγ) hper (by have := NeZero.pos N; positivity : 0 < 12 * N) ?_
  rw [Pi.pow_def, prod_siegelFunction_div_zpow_pow_twelve_mul N s a m γ]
  exact meromorphicAt_cuspFunction_prod s fun i _ ↦
    meromorphicAt_cuspFunction_zpow
      (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ) (m i)

/-- **Cusp meromorphy of a `Γ(N)`-invariant Siegel product.** For `0 < N`, every product
`∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` invariant under the principal congruence subgroup `Γ(N)` is meromorphic
at `q_N = 0` at every cusp `γ • ∞`. At `N = 0`, division by zero reduces the product to the
constant `∏ i ∈ s, (0 : ℂ) ^ m i`. -/
theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_mem_Gamma {N : ℕ}
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (hinv : ∀ {δ : SL(2, ℤ)}, δ ∈ CongruenceSubgroup.Gamma N → ∀ τ : ℍ,
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(δ • τ) ^ m i =
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i)
    (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · convert meromorphicAt_cuspFunction_const (∏ i ∈ s, (0 : ℂ) ^ m i) using 2
    ext _; simp [div_zero, ← Pi.zero_def]
  have : NeZero N := ⟨hN⟩
  set s' := s.filter (m · ≠ 0)
  rw [prod_siegelFunction_div_zpow_filter_ne_zero s a m γ]
  by_cases ha : ∀ i ∈ s', (fun j ↦ (a i j : ZMod N)) ≠ 0
  · refine meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_ne_zero s' a m ha
      (fun {δ} hδ τ ↦ ?_) γ
    have h₁ := congrFun (prod_siegelFunction_div_zpow_filter_ne_zero (N := N) s a m δ) τ
    have h₂ := congrFun (prod_siegelFunction_div_zpow_filter_ne_zero (N := N) s a m 1) τ
    simp only [one_smul] at h₂
    rw [← h₁, ← h₂]
    exact hinv hδ τ
  · obtain ⟨i₀, hi₀, hz⟩ := by push Not at ha; exact ha
    obtain ⟨t, ht⟩ := (TauCeti.exists_div_eq_intCast_iff_zmod_eq_zero (K := ℝ) hN (a i₀)).mpr hz
    convert meromorphicAt_cuspFunction_const (h := N) 0 using 2
    exact funext fun _ ↦ Finset.prod_eq_zero hi₀
      (by rw [ht, siegelFunction_intCast, zero_zpow _ (Finset.mem_filter.mp hi₀).2])

/-- **Cusp meromorphy of `Γ(N)`-invariant Kubert–Lang products.** For `0 < N`, every product
`∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` satisfying the Kubert–Lang congruence relations is meromorphic at
`q_N = 0` at every cusp `γ • ∞`. At `N = 0`, division by zero reduces the product to the
constant `∏ i ∈ s, (0 : ℂ) ^ m i`. -/
theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow {N : ℕ}
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 :=
  meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_mem_Gamma s a m
    (fun hδ τ ↦ prod_siegelFunction_div_zpow_smul_of_mem_Gamma s a m h₀ h₁ h₀₁ h₁₂ hδ τ) γ

/-- **Cusp order of a cusp-meromorphic Siegel product at `γ • ∞`.** For `0 < N` and non-integral
parameters `aᵢ ∉ N ℤ²` whenever `mᵢ ≠ 0`, if `τ ↦ ∏ i ∈ s, g_{aᵢ/N}(γ • τ)^{mᵢ}` is meromorphic
at `q_N = 0`, then `12 N` times its `q_N`-order at `0` equals
`∑ i ∈ s, mᵢ * siegelPowerCuspExponent N ((aᵢ γ) mod N)`. -/
theorem natCast_twelve_mul_mul_meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow
    {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, m i ≠ 0 → (fun j ↦ (a i j : ZMod N)) ≠ 0) (γ : SL(2, ℤ))
    (hmer : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0) :
    ↑(12 * N) * meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 =
      ((∑ i ∈ s, m i * siegelPowerCuspExponent N
        (fun j ↦ ((a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) : ℤ) :
          WithTop ℤ) := by
  set s' := s.filter (m · ≠ 0)
  rw [prod_siegelFunction_div_zpow_filter_ne_zero s a m γ] at hmer ⊢
  rw [← Finset.sum_filter_of_ne (p := (m · ≠ 0)) fun _ _ h h0 ↦ h (by simp [h0])]
  rw [← meromorphicOrderAt_pow (n := 12 * N) hmer, Pi.pow_def,
    ← meromorphicOrderAt_congr (cuspFunction_map_eventuallyEq (· ^ (12 * N)) _),
    prod_siegelFunction_div_zpow_pow_twelve_mul N s' a m γ]
  let g (i : ι) : meromorphicAtCuspSubring N :=
    ⟨(fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m i,
      mem_meromorphicAtCuspSubring.mpr <| meromorphicAt_cuspFunction_zpow
        (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ) (m i)⟩
  have hcoe : ((∏ i ∈ s', g i : meromorphicAtCuspSubring N) : ℍ → ℂ) = ∏ i ∈ s', (g i : ℍ → ℂ) :=
    map_prod (meromorphicAtCuspSubring N).subtype g s'
  rw [← hcoe,
    ← orderTop_laurentQExpansion (mem_meromorphicAtCuspSubring.mp (∏ i ∈ s', g i).property),
    ← laurentQExpansionRingHom_apply, map_prod, HahnSeries.orderTop_prod, WithTop.coe_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_filter.mp hi
  rw [laurentQExpansionRingHom_apply,
    orderTop_laurentQExpansion (mem_meromorphicAtCuspSubring.mp (g i).property)]
  dsimp only [g]
  rw [Pi.pow_def, meromorphicOrderAt_congr (cuspFunction_map_eventuallyEq (· ^ m i) _),
    fun_meromorphicOrderAt_zpow
      (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ),
    meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul (ha i hi'.1 hi'.2) γ,
    ← WithTop.coe_mul]

end TauCeti.ModularForm
