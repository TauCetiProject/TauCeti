/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Congruence
public import TauCeti.RingTheory.HahnSeries.Map
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.LinearAlgebra.Matrix.RationalVector
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.QPochhammer

/-!
# Laurent `q_N`-expansions and cusp orders of Siegel functions

For a positive level `N` and an integral row vector `a = (a₀, a₁)`, whenever `N ∣ 6 * k` the
`(12 k)`-th power `g_{a/N}(τ)^{12 k}` of the Siegel function depends only on `a mod N`, and
`g_{a/N}(γ • τ)^{12 k}` agrees with `g_{((a γ) mod N)/N}(τ)^{12 k}`. For `k = N`, `g_{a/N}^{12 N}`
expands in the local cusp parameter `q_N = e^{2π i τ / N}` at `i∞` as `q_N^{m(a)} ψ(q_N)`, where
`m(a) = 6 N² B₂({a₀ / N}) = 6 r₀² - 6 N r₀ + N²` for the canonical residue `0 ≤ r₀ < N` of `a₀`
modulo `N`, and `ψ` is a holomorphic unit power series (with nonzero constant term whenever
`a ∉ N ℤ²`). Every coefficient of this Laurent `q_N`-expansion is a polynomial over `ℤ` in the
primitive `N`-th root of unity `ζ_N = e^{2π i / N}`, and substituting `ζ_N ↦ ζ_N^d` transforms the
expansion into that of `g_{(a₀, d a₁)/N}^{12 N}` — the diagonal right action of `diag(1, d)` on the
row index.

Reading `g_{a/N}(γ • τ)` in the coordinate of an arbitrary cusp `γ • ∞` (`γ ∈ SL₂(ℤ)`) replaces `a`
by `a γ`. Together with `Gamma(N)`-normality, this implies that every `Γ(N)`-invariant Kubert–Lang
product `∏ᵢ g_{aᵢ/N}^{mᵢ}` is meromorphic at every cusp, and for `N > 0` and non-integral
parameters `aᵢ ∉ N ℤ²` (whenever `mᵢ ≠ 0`) any cusp-meromorphic product `∏ᵢ g_{aᵢ/N}^{mᵢ}` has
`12 N` times its `q_N`-order at `γ • ∞` equal to `∑ᵢ mᵢ · 6 N² B₂({(aᵢ γ)₀ / N})`.

## Main definitions and results

* `TauCeti.ModularForm.siegelFunction_div_pow_twelve_mul_congr`,
  `TauCeti.ModularForm.siegelFunction_div_pow_twelve_mul_eq_zmod`,
  `TauCeti.ModularForm.siegelFunction_div_pow_twelve_mul_smul_eq_zmod`: for `N ∣ 6 * k`,
  `g_{a/N}^{12 k}` depends only on `a mod N` and transforms via `a ↦ (a γ) mod N` under `SL₂(ℤ)`.
* `TauCeti.ModularForm.siegelFunction_div_eq_zero_iff`: for `N > 0`, `g_{a/N}(τ) = 0` on `ℍ` iff
  `a ≡ 0 (mod N)`.
* `TauCeti.ModularForm.siegelCuspOrder`: the integer `6 r₀² - 6 N r₀ + N²` with `r₀ = (v 0).val`,
  equal to `6 N² B₂((v 0).val / N)` for `0 < N` (`siegelCuspOrder_eq_bernoulliFun`), and equal to
  the `q_N`-order of `g_{v/N}^{12 N}` at `i∞` when `0 < N` and `v ≠ 0`; its sum over all nonzero
  `v ∈ (ℤ/Nℤ)²` vanishes (`sum_siegelCuspOrder_erase_zero`).
* `TauCeti.ModularForm.siegelPowerLaurentSeries`,
  `TauCeti.ModularForm.mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries`,
  `TauCeti.ModularForm.mapRingHom_aeval_exp_siegelPowerLaurentSeries`,
  `TauCeti.ModularForm.laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem_adjoin`:
  the universal `HahnSeries ℤ ℤ[X]` lift of the Laurent `q_N`-expansion of `g_{v/N}^{12 N}` (for
  `0 < N`), its equivariance under `ζ_N ↦ ζ_N^d` via `(v₀, v₁) ↦ (v₀, d v₁)`, and
  `ℤ[ζ_N]`-integrality of all Laurent `q_N`-coefficients.
* `TauCeti.ModularForm.laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_siegelCuspOrder`:
  for `0 < N`, the coefficient of `g_{v/N}^{12 N}` at `q_N^{siegelCuspOrder N v}`, which is the
  nonzero leading coefficient when `v ≠ 0` (and `0` when `v = 0`).
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul`,
  `TauCeti.ModularForm.meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul`: cusp
  meromorphy and exact `q_N`-order at `γ • ∞` of `g_{a/N}^{12 N}` (for `0 < N` and `a ∉ N ℤ²`).
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow` and
  `natCast_twelve_mul_mul_meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow`:
  cusp meromorphy for `Γ(N)`-invariant Kubert–Lang products and exact `12 N`-scaled cusp order at
  `γ • ∞` for `0 < N`, cusp-meromorphic products, and non-integral parameters `aᵢ ∉ N ℤ²` (whenever
  `mᵢ ≠ 0`).

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 and §2, and Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Matrix MatrixGroups Manifold Polynomial

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### Congruence of `g_{a/N}^{12 k}` modulo `N` and `q_N`-factorization -/

/-- **Congruence modulo `N` of `(12 k)`-th powers.** If `N ∣ 6 * k` and `a ≡ b [ZMOD N]`
coordinatewise, then `g_{a/N}(τ)^{12 k} = g_{b/N}(τ)^{12 k}` on the upper half-plane. -/
theorem siegelFunction_div_pow_twelve_mul_congr {N k : ℕ} (hk : N ∣ 6 * k) {a b : Fin 2 → ℤ}
    (hab : ∀ i, a i ≡ b i [ZMOD N]) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k) =
      siegelFunction (fun i ↦ (b i : ℝ) / N) τ ^ (12 * k) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have hdvd (i : Fin 2) : (N : ℤ) ∣ a i - b i := Int.modEq_iff_dvd.mp (hab i).symm
  choose s hs using hdvd
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hadd : (fun i ↦ (a i : ℝ) / N) = (fun i ↦ (b i : ℝ) / N) + fun i ↦ (s i : ℝ) := by
    ext i
    have hi : (a i : ℝ) - b i = N * s i := by exact_mod_cast hs i
    simp only [Pi.add_apply]
    field_simp
    linarith
  rw [hadd]
  obtain ⟨m, hm⟩ := hk
  refine siegelFunction_add_intCast_pow_twelve_mul _ s k (fun i ↦ ⟨(m : ℤ) * b i, ?_⟩) hτ
  have hm' : (6 * k : ℝ) = N * m := by exact_mod_cast hm
  rw [hm']
  push_cast
  field_simp

/-- On the upper half-plane, if `N ∣ 6 * k`, then `g_{a/N}(τ)^{12 k}` agrees with
`g_{((a mod N)/N)}(τ)^{12 k}`. -/
theorem siegelFunction_div_pow_twelve_mul_eq_zmod {N k : ℕ} (hk : N ∣ 6 * k) (a : Fin 2 → ℤ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k) =
      siegelFunction (fun i ↦ ((a i : ZMod N).val : ℝ) / N) τ ^ (12 * k) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have : NeZero N := ⟨hN⟩
  refine siegelFunction_div_pow_twelve_mul_congr hk (b := fun i ↦ ((a i : ZMod N).val : ℤ))
    (fun i ↦ ?_) hτ
  rw [ZMod.val_intCast]
  exact (Int.mod_modEq (a i) N).symm

/-- On the upper half-plane, if `N ∣ 6 * k`, then `g_{a/N}(γ • τ)^{12 k}` agrees with
`g_{((a γ mod N)/N)}(τ)^{12 k}` for every `γ ∈ SL₂(ℤ)`. -/
theorem siegelFunction_div_pow_twelve_mul_smul_eq_zmod {N k : ℕ} (hk : N ∣ 6 * k)
    (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * k) =
      siegelFunction (fun i ↦
        (((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N).val : ℝ) / N) τ ^ (12 * k) := by
  rw [siegelFunction_pow_twelve_mul_smul, Matrix.vecMul_div_map_intCast,
    siegelFunction_div_pow_twelve_mul_eq_zmod hk _ τ.im_pos]

/-- For `[NeZero N]` and `τ` in the upper half-plane, `g_{a/N}(τ) = 0` if and only if
`a ≡ 0 (mod N)`. -/
theorem siegelFunction_div_eq_zero_iff {N : ℕ} [NeZero N] (a : Fin 2 → ℤ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ = 0 ↔ (fun i ↦ (a i : ZMod N)) = 0 := by
  rw [siegelFunction_eq_zero_iff hτ,
    TauCeti.exists_div_eq_intCast_iff_zmod_eq_zero (K := ℝ) (NeZero.ne N) a]

/-- **The cusp-order integer of a level-`N` Siegel `(12 N)`-th power**:
`6 r₀² - 6 N r₀ + N²` where `r₀ = (v 0).val`. For `0 < N`, this equals
`6 N² B₂((v 0).val / N)` (`siegelCuspOrder_eq_bernoulliFun`), and when `v ≠ 0` it is the
`q_N`-order of `g_{v/N}^{12 N}` at `i∞`. -/
def siegelCuspOrder (N : ℕ) (v : Fin 2 → ZMod N) : ℤ :=
  6 * ((v 0).val : ℤ) ^ 2 - 6 * (N : ℤ) * (v 0).val + (N : ℤ) ^ 2

/-- Defining formula for `siegelCuspOrder`. -/
theorem siegelCuspOrder_def (N : ℕ) (v : Fin 2 → ZMod N) :
    siegelCuspOrder N v = 6 * ((v 0).val : ℤ) ^ 2 - 6 * (N : ℤ) * (v 0).val + (N : ℤ) ^ 2 :=
  (rfl)

/-- `siegelCuspOrder N v` depends only on the first coordinate `v 0`. -/
theorem siegelCuspOrder_congr {N : ℕ} {v w : Fin 2 → ZMod N} (h : v 0 = w 0) :
    siegelCuspOrder N v = siegelCuspOrder N w := by
  simp only [siegelCuspOrder, h]

/-- If `v 0 = 0`, then `siegelCuspOrder N v = N ^ 2`. -/
theorem siegelCuspOrder_of_apply_zero_eq_zero {N : ℕ} {v : Fin 2 → ZMod N} (hv : v 0 = 0) :
    siegelCuspOrder N v = (N : ℤ) ^ 2 := by
  simp [siegelCuspOrder, hv]

/-- At `v = 0`, `siegelCuspOrder N 0 = N ^ 2`. -/
@[simp]
theorem siegelCuspOrder_zero (N : ℕ) : siegelCuspOrder N 0 = (N : ℤ) ^ 2 :=
  siegelCuspOrder_of_apply_zero_eq_zero rfl

/-- At `v = ![0, y]`, `siegelCuspOrder N ![0, y] = N ^ 2`. -/
@[simp]
theorem siegelCuspOrder_cons_zero (N : ℕ) (y : ZMod N) :
    siegelCuspOrder N ![0, y] = (N : ℤ) ^ 2 :=
  siegelCuspOrder_of_apply_zero_eq_zero rfl

/-- `siegelCuspOrder` is invariant under negation of the division vector. -/
@[simp]
theorem siegelCuspOrder_neg {N : ℕ} (v : Fin 2 → ZMod N) :
    siegelCuspOrder N (-v) = siegelCuspOrder N v := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelCuspOrder, ZMod.val_neg']
  have : NeZero N := ⟨hN⟩
  rcases eq_or_ne (v 0) 0 with hv0 | hv0
  · simp [siegelCuspOrder, hv0]
  have : NeZero (v 0) := ⟨hv0⟩
  have hle : (v 0).val ≤ N := (v 0).val_lt.le
  simp only [siegelCuspOrder, Pi.neg_apply, ZMod.val_neg_of_ne_zero (v 0), Nat.cast_sub hle]
  ring

/-- For `[NeZero N]`, `siegelCuspOrder N (a mod N)` equals `6 N² B₂({a₀ / N})`, where
`{x} = Int.fract x` is the fractional part and `B₂` is the second Bernoulli polynomial. -/
theorem siegelCuspOrder_eq_bernoulliFun {N : ℕ} [NeZero N] (a : Fin 2 → ℤ) :
    (siegelCuspOrder N (fun i ↦ (a i : ZMod N)) : ℝ) =
      6 * (N : ℝ) ^ 2 * bernoulliFun 2 (Int.fract ((a 0 : ℝ) / N)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval : (((a 0 : ZMod N).val : ℤ) : ℝ) = ((a 0 % (N : ℤ) : ℤ) : ℝ) := by
    rw [ZMod.val_intCast]
  rw [siegelCuspOrder, Int.fract_div_intCast_eq_div_intCast_mod, bernoulliFun_two]
  push_cast
  rw [← Int.cast_natCast (a 0 : ZMod N).val, hval]
  field_simp

/-- The sum of `siegelCuspOrder N v` over all nonzero `v ∈ (ℤ/Nℤ)²` vanishes. -/
theorem sum_siegelCuspOrder_erase_zero (N : ℕ) [NeZero N] :
    ∑ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0, siegelCuspOrder N v = 0 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 2 → ZMod N)), siegelCuspOrder_zero,
    sub_eq_zero]
  have hprod : ∑ v : Fin 2 → ZMod N, siegelCuspOrder N v =
      ∑ r₀ : ZMod N, (N : ℤ) * (6 * (r₀.val : ℤ) ^ 2 - 6 * N * r₀.val + N ^ 2) := by
    rw [Fintype.sum_equiv (piFinTwoEquiv fun _ ↦ ZMod N) _
      (fun p : ZMod N × ZMod N ↦ 6 * (p.1.val : ℤ) ^ 2 - 6 * N * p.1.val + N ^ 2)
      (fun v ↦ siegelCuspOrder_def N v), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hprod, ← Finset.mul_sum,
    ← Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      (fun k : Fin N ↦ 6 * ((k : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (k : ℕ) + (N : ℤ) ^ 2)
      (fun r₀ : ZMod N ↦ 6 * (r₀.val : ℤ) ^ 2 - 6 * (N : ℤ) * r₀.val + (N : ℤ) ^ 2)
      (fun k ↦ by simp [ZMod.val_natCast_of_lt k.isLt]),
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ 6 * (k : ℤ) ^ 2 - 6 * (N : ℤ) * k + (N : ℤ) ^ 2) N]
  have hterm (k : ℕ) :
      6 * (k : ℤ) ^ 2 - 6 * (N : ℤ) * k + (N : ℤ) ^ 2 =
        (k : ℤ) ^ 2 * 6 - 3 * (N : ℤ) * ((k : ℤ) * 2) + (N : ℤ) ^ 2 := by
    ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_range_natCast_sq_mul_six, Finset.sum_range_natCast_mul_two,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The holomorphic unit factor `ψ_{N, v}(τ)` in `g_{v/N}(τ)^{12N} = q_N^{m(v)} ψ_{N, v}(τ)`. -/
private def siegelUnitFun (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  let ω := cexp (2 * π * I / N) ^ (v 1).val
  ω ^ (6 * (v 0).val) *
    (1 - ω * 𝕢 N τ ^ (v 0).val) ^ (12 * N) *
    qPochhammerFun N (N + (v 0).val) ω (𝕢 N τ) ^ (12 * N) *
    qPochhammerFun N (N - (v 0).val) (ω ^ (N - 1)) (𝕢 N τ) ^ (12 * N)

private theorem siegelUnitFun_eq (N : ℕ) (v : Fin 2 → ZMod N) :
    siegelUnitFun N v =
      (fun _ : ℍ ↦ (cexp (2 * π * I / N) ^ (v 1).val) ^ (6 * (v 0).val)) *
        (fun τ : ℍ ↦ 1 - cexp (2 * π * I / N) ^ (v 1).val * 𝕢 N τ ^ (v 0).val) ^ (12 * N) *
        (fun τ : ℍ ↦
          qPochhammerFun N (N + (v 0).val) (cexp (2 * π * I / N) ^ (v 1).val) (𝕢 N τ)) ^
          (12 * N) *
        (fun τ : ℍ ↦
          qPochhammerFun N (N - (v 0).val)
            ((cexp (2 * π * I / N) ^ (v 1).val) ^ (N - 1)) (𝕢 N τ)) ^ (12 * N) :=
  rfl

private theorem tprod_siegel_eq_qPochhammer {N r₀ : ℕ} (hN : 0 < N) (hr₀ : r₀ ≤ N)
    {ω : ℂ} (hωN : ω ^ N = 1) (τ : ℍ) :
    (∏' n : ℕ, (1 - (𝕢 N τ ^ N) ^ (n + 1) * (ω * 𝕢 N τ ^ r₀))) =
        qPochhammerFun N (N + r₀) ω (𝕢 N τ) ∧
      (∏' n : ℕ, (1 - (𝕢 N τ ^ N) ^ (n + 1) * (ω * 𝕢 N τ ^ r₀)⁻¹)) =
        qPochhammerFun N (N - r₀) (ω ^ (N - 1)) (𝕢 N τ) := by
  have hω_inv : ω⁻¹ = ω ^ (N - 1) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hN, hωN])
  rw [qPochhammerFun_def, qPochhammerFun_def]
  refine ⟨tprod_congr fun n ↦ ?_, tprod_congr fun n ↦ ?_⟩
  · congr 1
    rw [← pow_mul, mul_left_comm, ← pow_add]
    exact congrArg (fun k ↦ ω * 𝕢 N (τ : ℂ) ^ k) (by ring)
  · have hq_ne : 𝕢 N (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have hexp_sub : (𝕢 N (τ : ℂ) ^ N) ^ (n + 1) * (𝕢 N (τ : ℂ) ^ r₀)⁻¹ =
        𝕢 N (τ : ℂ) ^ (N * n + (N - r₀)) := by
      refine (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero r₀ hq_ne)).mpr ?_
      rw [← pow_mul, ← pow_add, add_assoc, Nat.sub_add_cancel hr₀]
      exact congrArg (𝕢 N (τ : ℂ) ^ ·) (by ring)
    rw [mul_inv, hω_inv]
    congr 1
    calc (𝕢 N (τ : ℂ) ^ N) ^ (n + 1) * (ω ^ (N - 1) * (𝕢 N (τ : ℂ) ^ r₀)⁻¹)
        = ω ^ (N - 1) * ((𝕢 N (τ : ℂ) ^ N) ^ (n + 1) * (𝕢 N (τ : ℂ) ^ r₀)⁻¹) := by ring
      _ = ω ^ (N - 1) * 𝕢 N (τ : ℂ) ^ (N * n + (N - r₀)) := by rw [hexp_sub]

/-- Exact factorization `g_{v/N}(τ)^{12 N} = q_N^{siegelCuspOrder N v} * siegelUnitFun N v τ`. -/
private theorem siegelFunction_zmod_pow_twelve_mul_eq {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N)
    (τ : ℍ) :
    siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) =
      𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ := by
  have hN : 0 < N := NeZero.pos N
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let ω := cexp (2 * π * I / N) ^ (v 1).val
  have hωN : ω ^ N = 1 := by
    rw [← pow_mul, mul_comm (v 1).val N, pow_mul,
      (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one, one_pow]
  have hq1 : cexp (2 * π * I * (τ : ℂ)) = 𝕢 N τ ^ N := by
    simpa [Function.Periodic.qParam] using
      (TauCeti.Periodic.qParam_nat_mul_pow (h := 1) hN.ne' (τ : ℂ)).symm
  have hw : cexp (2 * π * I * ((((v 0).val : ℝ) / N : ℝ) * (τ : ℂ) +
      (((v 1).val : ℝ) / N : ℝ))) = ω * 𝕢 N τ ^ (v 0).val := by
    simp only [ω, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; field_simp; ring
  have hB : cexp (π * I * bernoulliFun 2 (((v 0).val : ℝ) / N) * (τ : ℂ)) ^ (12 * N) =
      𝕢 N τ ^ siegelCuspOrder N v := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, bernoulliFun_two,
      siegelCuspOrder]
    congr 1; push_cast; field_simp; ring
  have hph : cexp (π * I * ((((v 1).val : ℝ) / N : ℝ) : ℂ) *
      ((((v 0).val : ℝ) / N : ℝ) - 1)) ^ (12 * N) = ω ^ (6 * (v 0).val) := by
    have hexp : ((12 * N : ℕ) : ℂ) * (π * I * ((((v 1).val : ℝ) / N : ℝ) : ℂ) *
        ((((v 0).val : ℝ) / N : ℝ) - 1)) =
        ((6 * (v 0).val * (v 1).val : ℕ) : ℂ) * (2 * π * I / N) +
          (-(6 * ((v 1).val : ℤ)) : ℤ) * (2 * π * I) := by push_cast; field_simp; ring
    rw [← Complex.exp_nat_mul, hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one, Complex.exp_nat_mul]
    simp only [ω, ← pow_mul, mul_comm (6 * (v 0).val) (v 1).val, mul_assoc]
  obtain ⟨hp₁, hp₂⟩ := tprod_siegel_eq_qPochhammer hN (v 0).val_lt.le hωN τ
  have hsign : (-1 : ℂ) ^ (12 * N) = 1 := Even.neg_one_pow ⟨6 * N, by ring⟩
  rw [siegelFunction_eq_mul_tprod_mul_tprod _ τ.im_pos, Complex.exp_neg, hq1, hw, hp₁, hp₂]
  have hpow : ∀ a b c d e : ℂ, (-a * b * c * (d * e)) ^ (12 * N) =
      (-1 : ℂ) ^ (12 * N) * a ^ (12 * N) * b ^ (12 * N) *
        c ^ (12 * N) * d ^ (12 * N) * e ^ (12 * N) := fun _ _ _ _ _ ↦ by ring
  rw [hpow, hsign, one_mul, hB, hph, siegelUnitFun]
  dsimp only [ω]
  ring

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
  HahnSeries.single (siegelCuspOrder N v) 1 *
    HahnSeries.ofPowerSeries ℤ ℤ[X] (siegelUnitPowerSeries N v)

private theorem analyticAt_cuspFunction_siegelUnitFun {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    AnalyticAt ℂ (cuspFunction N (siegelUnitFun N v)) 0 := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set ω := cexp (2 * π * I / N) ^ (v 1).val
  rw [siegelUnitFun_eq]
  exact UpperHalfPlane.analyticAt_cuspFunction_mul
    (UpperHalfPlane.analyticAt_cuspFunction_mul
      (UpperHalfPlane.analyticAt_cuspFunction_mul
        (UpperHalfPlane.analyticAt_cuspFunction_const N _)
        (UpperHalfPlane.analyticAt_cuspFunction_pow
          (UpperHalfPlane.analyticAt_cuspFunction_one_sub_mul_qParam_pow N (v 0).val ω) _))
      (UpperHalfPlane.analyticAt_cuspFunction_pow
        (UpperHalfPlane.analyticAt_cuspFunction_qPochhammerFun hNR hN (N + (v 0).val) ω) _))
    (UpperHalfPlane.analyticAt_cuspFunction_pow
      (UpperHalfPlane.analyticAt_cuspFunction_qPochhammerFun hNR hN (N - (v 0).val)
        (ω ^ (N - 1))) _)

private theorem qExpansion_siegelUnitFun {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    qExpansion N (siegelUnitFun N v) =
      (siegelUnitPowerSeries N v).map (Polynomial.aeval (cexp (2 * π * I / N))).toRingHom := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set ζ := cexp (2 * π * I / N)
  set ω := ζ ^ (v 1).val
  have hr₀ : (v 0).val < N := (v 0).val_lt
  have han_c := UpperHalfPlane.analyticAt_cuspFunction_const N (ω ^ (6 * (v 0).val))
  have han_lin := UpperHalfPlane.analyticAt_cuspFunction_one_sub_mul_qParam_pow N (v 0).val ω
  have han₁ := UpperHalfPlane.analyticAt_cuspFunction_qPochhammerFun hNR hN (N + (v 0).val) ω
  have han₂ :=
    UpperHalfPlane.analyticAt_cuspFunction_qPochhammerFun hNR hN (N - (v 0).val) (ω ^ (N - 1))
  have hconst : qExpansion N (fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) =
      PowerSeries.C (ω ^ (6 * (v 0).val)) := by
    have han1 : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 := by
      rw [Pi.one_def]
      exact UpperHalfPlane.analyticAt_cuspFunction_const N 1
    have hc : (fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) = ω ^ (6 * (v 0).val) • (1 : ℍ → ℂ) := by
      funext; simp
    rw [hc, UpperHalfPlane.qExpansion_smul han1, UpperHalfPlane.qExpansion_one,
      Algebra.smul_def, mul_one, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [siegelUnitFun_eq,
    UpperHalfPlane.qExpansion_mul
      (UpperHalfPlane.analyticAt_cuspFunction_mul
        (UpperHalfPlane.analyticAt_cuspFunction_mul han_c
          (UpperHalfPlane.analyticAt_cuspFunction_pow han_lin _))
        (UpperHalfPlane.analyticAt_cuspFunction_pow han₁ _))
      (UpperHalfPlane.analyticAt_cuspFunction_pow han₂ _),
    UpperHalfPlane.qExpansion_mul
      (UpperHalfPlane.analyticAt_cuspFunction_mul han_c
        (UpperHalfPlane.analyticAt_cuspFunction_pow han_lin _))
      (UpperHalfPlane.analyticAt_cuspFunction_pow han₁ _),
    UpperHalfPlane.qExpansion_mul han_c (UpperHalfPlane.analyticAt_cuspFunction_pow han_lin _),
    hconst, UpperHalfPlane.qExpansion_pow han_lin, UpperHalfPlane.qExpansion_pow han₁,
    UpperHalfPlane.qExpansion_pow han₂,
    UpperHalfPlane.qExpansion_one_sub_mul_qParam_pow hNR (v 0).val ω,
    UpperHalfPlane.qExpansion_qPochhammerFun hNR hN (by omega) ω,
    UpperHalfPlane.qExpansion_qPochhammerFun hNR hN (by omega) (ω ^ (N - 1)),
    siegelUnitPowerSeries]
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_C, PowerSeries.map_X,
    map_qPochhammerSeries, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
  simp only [ω, map_pow, ← pow_mul, mul_comm (v 1).val]

/-- **Diagonal cyclotomic action on the Laurent `q_N`-expansion of `g_{v/N}^{12N}`.**
For `0 < N`, evaluating `siegelPowerLaurentSeries N v` at `X = e^{2π i / N}^d` yields the Laurent
`q_N`-expansion of `g_{(v₀, d v₁)/N}^{12 N}`. -/
theorem mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries {N : ℕ} [NeZero N]
    (v : Fin 2 → ZMod N) (d : ℕ) :
    HahnSeries.mapRingHom (Polynomial.aeval (cexp (2 * π * I / N) ^ d)).toRingHom
        (siegelPowerLaurentSeries N v) =
      UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((![v 0, (d : ZMod N) * v 1] i).val : ℝ) / N) τ ^ (12 * N)) := by
  set v' : Fin 2 → ZMod N := ![v 0, (d : ZMod N) * v 1]
  have hN : 0 < N := NeZero.pos N
  set ζ := cexp (2 * π * I / N)
  have hζN : ζ ^ N = 1 := (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
  have hpow : (ζ ^ d) ^ (v 1).val = ζ ^ (v' 1).val := by
    have hv1 : (v' 1).val = (d * (v 1).val) % N := by simp [v', ZMod.val_mul]
    rw [← pow_mul, hv1]
    conv_lhs => rw [← Nat.div_add_mod (d * (v 1).val) N]
    rw [pow_add, pow_mul, hζN, one_pow, one_mul]
  have hord : siegelCuspOrder N v = siegelCuspOrder N v' := siegelCuspOrder_congr rfl
  have hunit : (siegelUnitPowerSeries N v).map (Polynomial.aeval (ζ ^ d)).toRingHom =
      (siegelUnitPowerSeries N v').map (Polynomial.aeval ζ).toRingHom := by
    simp only [siegelUnitPowerSeries, map_mul, map_pow, map_sub, map_one, PowerSeries.map_C,
      PowerSeries.map_X, map_qPochhammerSeries, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X]
    have h0 : (v' 0).val = (v 0).val := rfl
    have h6 : (PowerSeries.C ζ ^ d) ^ (6 * (v 0).val * (v 1).val) =
        PowerSeries.C ζ ^ (6 * (v' 0).val * (v' 1).val) := by
      have hexp : d * (6 * (v 0).val * (v 1).val) = d * (v 1).val * (6 * (v 0).val) := by ring
      rw [← pow_mul, ← map_pow, ← map_pow, hexp, pow_mul, pow_mul ζ d, hpow,
        ← pow_mul, h0, mul_comm]
    have h1 : (PowerSeries.C ζ ^ d) ^ (v 1).val = PowerSeries.C ζ ^ (v' 1).val := by
      rw [← pow_mul, ← map_pow, ← map_pow, pow_mul, hpow]
    have hN1 : (ζ ^ d) ^ ((N - 1) * (v 1).val) = ζ ^ ((N - 1) * (v' 1).val) := by
      rw [mul_comm (N - 1), pow_mul, hpow, ← pow_mul, mul_comm]
    rw [h6, h1, hN1, hpow, h0]
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v' i).val : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v' * siegelUnitFun N v' τ :=
    funext (siegelFunction_zmod_pow_twelve_mul_eq v')
  have hsingle : HahnSeries.mapRingHom (Polynomial.aeval (R := ℤ) (ζ ^ d)).toRingHom
      (HahnSeries.single (siegelCuspOrder N v) 1) = HahnSeries.single (siegelCuspOrder N v) 1 := by
    rw [HahnSeries.mapRingHom_apply]
    exact (HahnSeries.map_single (a := siegelCuspOrder N v) (r := (1 : ℤ[X]))
      (Polynomial.aeval (ζ ^ d)).toRingHom.toZeroHom).trans (by simp)
  rw [hfun,
    UpperHalfPlane.laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr hN)
      (siegelCuspOrder N v') (analyticAt_cuspFunction_siegelUnitFun v').meromorphicAt,
    UpperHalfPlane.laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelUnitFun v'),
    qExpansion_siegelUnitFun v', ← hunit, ← hord, siegelPowerLaurentSeries, map_mul, hsingle,
    HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries]

/-- For `0 < N`, evaluating `siegelPowerLaurentSeries N v` at `ζ_N = e^{2π i / N}` gives the
Laurent `q_N`-expansion of `g_{v/N}^{12 N}`. -/
theorem mapRingHom_aeval_exp_siegelPowerLaurentSeries {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    HahnSeries.mapRingHom (Polynomial.aeval (cexp (2 * π * I / N))).toRingHom
        (siegelPowerLaurentSeries N v) =
      UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)) := by
  have hv : (fun i ↦ ((![v 0, ((1 : ℕ) : ZMod N) * v 1] i).val : ℝ) / N) =
      fun i ↦ ((v i).val : ℝ) / N := by
    ext i; fin_cases i <;> simp
  have h := mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries v 1
  rwa [pow_one, hv] at h

/-- **Every Laurent `q_N`-coefficient of `g_{a/N}^{12 N}` lies in `ℤ[ζ_N]`**, where
`ζ_N = e^{2π i / N}`. -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem_adjoin {N : ℕ}
    (a : Fin 2 → ℤ) (n : ℤ) :
    (UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N))).coeff n ∈
      Algebra.adjoin ℤ {cexp (2 * π * I / N)} := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h1 : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ ^ (12 * 0)) = 1 :=
      funext fun _ ↦ by simp
    rw [h1, UpperHalfPlane.laurentQExpansion_one]
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
    siegelUnitPowerSeries]
  simp only [map_mul, map_pow, map_sub, map_one, constantCoeff_qPochhammerSeries, one_pow,
    mul_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  by_cases hv0 : v 0 = 0
  · simp [hv0]
  · have hv0' : (v 0).val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
    simp [hv0, hv0', zero_pow]

/-- For `v ≠ 0` in `Fin 2 → ZMod N`, the leading unit term of `g_{v/N}^{12N}` at `i∞` is nonzero. -/
private theorem qExpansion_siegelUnitFun_coeff_zero_ne_zero {N : ℕ} [NeZero N]
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    (qExpansion N (siegelUnitFun N v)).coeff 0 ≠ 0 := by
  rw [qExpansion_siegelUnitFun_coeff_zero]
  refine mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) ?_
  split_ifs with hv0
  · refine pow_ne_zero _ (sub_ne_zero.mpr fun h1 ↦ hv ?_)
    have hprim := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
    have hdvd : N ∣ (v 1).val := hprim.dvd_of_pow_eq_one (v 1).val h1.symm
    have hv1 : (v 1).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (v 1).val_lt
    ext i
    fin_cases i
    · exact hv0
    · exact ZMod.val_injective N (by simpa using hv1)
  · exact one_ne_zero

/-- **The Laurent `q_N`-coefficient of `g_{v/N}^{12 N}` at `q_N^{siegelCuspOrder N v}`.**
For `0 < N` and `v ≠ 0`, this is the nonzero leading Laurent `q_N`-coefficient of `g_{v/N}^{12 N}`;
when `v = 0`, it equals `0` (since `g_0 = 0` has the zero Laurent series). -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_siegelCuspOrder
    {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    (UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))).coeff (siegelCuspOrder N v) =
      cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
        (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ :=
    funext (siegelFunction_zmod_pow_twelve_mul_eq v)
  rw [hfun,
    UpperHalfPlane.laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
      (siegelCuspOrder N v) (analyticAt_cuspFunction_siegelUnitFun v).meromorphicAt,
    UpperHalfPlane.laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelUnitFun v),
    HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  simpa using qExpansion_siegelUnitFun_coeff_zero v

/-- **`g_{a/N}(γ • τ)^{12 N}` is meromorphic at `q_N = 0` for every cusp `γ • ∞`.** -/
theorem meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul (N : ℕ) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [mul_zero, pow_zero]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_const 1
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N)
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ := by
    funext τ
    rw [siegelFunction_div_pow_twelve_mul_smul_eq_zmod (dvd_mul_left N 6) a γ τ,
      siegelFunction_zmod_pow_twelve_mul_eq v τ]
  rw [hfun]
  exact UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
    (siegelCuspOrder N v) (analyticAt_cuspFunction_siegelUnitFun v).meromorphicAt

/-- **Cusp order of `g_{a/N}^{12 N}` at `γ • ∞`.** For `0 < N` and `a ∉ N ℤ²`, the `q_N`-order of
`τ ↦ g_{a/N}(γ • τ)^{12 N}` at `i∞` is `siegelCuspOrder N ((a γ) mod N)`. -/
theorem meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul {N : ℕ} [NeZero N]
    {a : Fin 2 → ℤ} (ha : (fun i ↦ (a i : ZMod N)) ≠ 0) (γ : SL(2, ℤ)) :
    meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) 0 =
      siegelCuspOrder N (fun i ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N)) := by
  set b := a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  set v : Fin 2 → ZMod N := fun i ↦ (b i : ZMod N)
  have hv : v ≠ 0 := by
    intro hv0
    apply ha
    ext i
    have hb : b ᵥ* (↑γ⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) = a := by
      simp only [b, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    rw [← hb]
    have h0 : ∀ j, (b j : ZMod N) = 0 := congrFun hv0
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h0]
  have hmer := meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N a γ
  rw [← UpperHalfPlane.orderTop_laurentQExpansion hmer]
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ := by
    funext τ
    rw [siegelFunction_div_pow_twelve_mul_smul_eq_zmod (dvd_mul_left N 6) a γ τ,
      siegelFunction_zmod_pow_twelve_mul_eq v τ]
  rw [hfun,
    UpperHalfPlane.laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
      (siegelCuspOrder N v) (analyticAt_cuspFunction_siegelUnitFun v).meromorphicAt,
    UpperHalfPlane.laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelUnitFun v),
    HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero, PowerSeries.orderTop_coe]
  have hord : (qExpansion N (siegelUnitFun N v)).order = 0 :=
    nonpos_iff_eq_zero.mp (PowerSeries.order_le 0 (qExpansion_siegelUnitFun_coeff_zero_ne_zero hv))
  simp [hord]

/-! ### Cusp meromorphy and cusp orders of `Γ(N)`-invariant Siegel products -/

private theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_ne_zero
    {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, (fun j ↦ (a i j : ZMod N)) ≠ 0)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 := by
  set F : ℍ → ℂ := fun τ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i
  have hF_mdiff : MDiff F := by
    have hF_eq : F = ∏ i ∈ s, fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i :=
      funext fun τ ↦ by simp [F]
    rw [hF_eq]
    refine MDifferentiable.prod fun i hi τ ↦ ?_
    have hne : siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ≠ 0 :=
      mt (siegelFunction_div_eq_zero_iff (a i) τ.im_pos).mp (ha i hi)
    rcases Int.eq_nat_or_neg (m i) with ⟨k, hk | hk⟩
    · simp only [hk, zpow_natCast]
      exact (mdifferentiable_siegelFunction _ τ).pow k
    · simp only [hk, zpow_neg, zpow_natCast]
      exact ((mdifferentiable_siegelFunction _ τ).pow k).inv (pow_ne_zero k hne)
  have hγ : MDiff (fun τ : ℍ ↦ γ • τ) := by
    have hsmul : (fun τ : ℍ ↦ Matrix.SpecialLinearGroup.mapGL ℝ γ • τ) = fun τ : ℍ ↦ γ • τ :=
      funext fun τ ↦ Matrix.SpecialLinearGroup.mapGL_smul γ τ
    rw [← hsmul]
    exact mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) (by simp)
  have hper : Function.Periodic ((fun τ : ℍ ↦ F (γ • τ)) ∘ ofComplex) N :=
    TauCeti.periodic_smul_comp_ofComplex_of_Gamma_invariant
      (fun _ hδ τ ↦ prod_siegelFunction_div_zpow_smul_of_mem_Gamma s a m h₀ h₁ h₀₁ h₁₂ hδ τ) γ
  refine UpperHalfPlane.meromorphicAt_cuspFunction_of_pow (Nat.cast_pos.mpr (NeZero.pos N))
    (hF_mdiff.comp hγ) hper (by have := NeZero.pos N; positivity : 0 < 12 * N) ?_
  have hpow_eq : ((fun τ : ℍ ↦ F (γ • τ)) ^ (12 * N)) =
      ∏ i ∈ s, ((fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^
        m i) := by
    funext τ
    simp only [F, Pi.pow_apply, Finset.prod_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (m i), zpow_mul, zpow_natCast]
  rw [hpow_eq]
  exact UpperHalfPlane.meromorphicAt_cuspFunction_prod s fun i _ ↦
    UpperHalfPlane.meromorphicAt_cuspFunction_zpow
      (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ) (m i)

/-- **Cusp meromorphy of `Γ(N)`-invariant Kubert–Lang products.** Every product
`∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` satisfying the Kubert–Lang congruence relations is meromorphic at every
cusp `γ • ∞`. -/
theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow {N : ℕ}
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hconst : (fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / (0 : ℕ)) ↑(γ • τ) ^ m i) =
        Function.const ℍ (∏ i ∈ s, (0 : ℂ) ^ m i) := by
      funext τ
      simp [div_zero, ← Pi.zero_def]
    rw [hconst]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_const _
  have : NeZero N := ⟨hN⟩
  let s' := s.filter fun i ↦ m i ≠ 0
  have hprod : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
      fun τ : ℍ ↦ ∏ i ∈ s', siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i := by
    funext τ
    refine (Finset.prod_subset (Finset.filter_subset _ s) fun i hi hni ↦ ?_).symm
    have hm0 : m i = 0 := by simpa [s', hi] using hni
    simp [hm0]
  have hsum (w : ι → ℤ) : ∑ i ∈ s, m i * w i = ∑ i ∈ s', m i * w i := by
    refine (Finset.sum_subset (Finset.filter_subset _ s) fun i hi hni ↦ ?_).symm
    have hm0 : m i = 0 := by simpa [s', hi] using hni
    simp [hm0]
  have hsum1 : ∑ i ∈ s, m i = ∑ i ∈ s', m i := by simpa using hsum fun _ ↦ 1
  by_cases ha : ∀ i ∈ s', (fun j ↦ (a i j : ZMod N)) ≠ 0
  · rw [hprod]
    exact meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_ne_zero s' a m ha
      (hsum (fun i ↦ a i 0 ^ 2) ▸ h₀) (hsum (fun i ↦ a i 1 ^ 2) ▸ h₁)
      (hsum (fun i ↦ a i 0 * a i 1) ▸ h₀₁) (hsum1 ▸ h₁₂) γ
  · obtain ⟨i₀, hi₀, hz⟩ := by push Not at ha; exact ha
    obtain ⟨t, ht⟩ := (TauCeti.exists_div_eq_intCast_iff_zmod_eq_zero (K := ℝ) hN (a i₀)).mpr hz
    have h0 : (fun τ : ℍ ↦ ∏ i ∈ s', siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
        Function.const ℍ 0 :=
      funext fun τ ↦ Finset.prod_eq_zero hi₀
        (by rw [ht, siegelFunction_intCast, zero_zpow _ (Finset.mem_filter.mp hi₀).2])
    rw [hprod, h0]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_const 0

/-- **Cusp order of a cusp-meromorphic Siegel product at `γ • ∞`.** For `0 < N` and non-integral
parameters `aᵢ ∉ N ℤ²` whenever `mᵢ ≠ 0`, if `τ ↦ ∏ i ∈ s, g_{aᵢ/N}(γ • τ)^{mᵢ}` is meromorphic
at `q_N = 0`, then `12 N` times its `q_N`-order at `0` equals
`∑ i ∈ s, mᵢ * siegelCuspOrder N ((aᵢ γ) mod N)`. -/
theorem natCast_twelve_mul_mul_meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow
    {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, m i ≠ 0 → (fun j ↦ (a i j : ZMod N)) ≠ 0) (γ : SL(2, ℤ))
    (hmer : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0) :
    ↑(12 * N) * meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 =
      ((∑ i ∈ s, m i *
        siegelCuspOrder N (fun j ↦ ((a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) : ℤ) :
          WithTop ℤ) := by
  let s' := s.filter fun i ↦ m i ≠ 0
  have hprod : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
      fun τ : ℍ ↦ ∏ i ∈ s', siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i := by
    funext τ
    refine (Finset.prod_subset (Finset.filter_subset _ s) fun i hi hni ↦ ?_).symm
    have hm0 : m i = 0 := by simpa [s', hi] using hni
    simp [hm0]
  have hsum :
      ∑ i ∈ s, m i *
          siegelCuspOrder N (fun j ↦ ((a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) =
        ∑ i ∈ s', m i *
          siegelCuspOrder N (fun j ↦ ((a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) := by
    refine (Finset.sum_subset (Finset.filter_subset _ s) fun i hi hni ↦ ?_).symm
    have hm0 : m i = 0 := by simpa [s', hi] using hni
    simp [hm0]
  have ha' : ∀ i ∈ s', (fun j ↦ (a i j : ZMod N)) ≠ 0 := fun i hi ↦
    ha i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  rw [hprod] at hmer ⊢
  rw [hsum, ← meromorphicOrderAt_pow (n := 12 * N) hmer, Pi.pow_def,
    ← meromorphicOrderAt_congr (UpperHalfPlane.cuspFunction_map_eventuallyEq (· ^ (12 * N)) _)]
  have hpow_eq : (fun τ : ℍ ↦ (∏ i ∈ s',
      siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) ^ (12 * N)) =
      ∏ i ∈ s', ((fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^
        m i) := by
    funext τ
    simp only [Finset.prod_apply, Pi.pow_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (m i), zpow_mul, zpow_natCast]
  rw [hpow_eq]
  clear hmer hpow_eq hprod hsum ha
  have hfactor_mer (i : ι) : MeromorphicAt (cuspFunction N
      ((fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m i)) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_zpow
      (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ) (m i)
  revert ha'
  generalize s' = u
  intro ha'
  induction u using Finset.cons_induction with
  | empty => simp
  | cons x t hxt ih =>
    have hx_ne := ha' x (Finset.mem_cons_self x t)
    have ht_ne : ∀ i ∈ t, (fun j ↦ (a i j : ZMod N)) ≠ 0 :=
      fun i hi ↦ ha' i (Finset.mem_cons_of_mem hi)
    have hx_ord : meromorphicOrderAt (cuspFunction N
        ((fun τ : ℍ ↦ siegelFunction (fun j ↦ (a x j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m x)) 0 =
        ((m x * siegelCuspOrder N
          (fun j ↦ ((a x ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) : ℤ) : WithTop ℤ) := by
      have hm0 := meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a x) γ
      rw [Pi.pow_def,
        meromorphicOrderAt_congr (UpperHalfPlane.cuspFunction_map_eventuallyEq (· ^ m x) _),
        fun_meromorphicOrderAt_zpow hm0,
        meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul hx_ne γ,
        ← WithTop.coe_mul]
    simp only [Finset.prod_cons, Finset.sum_cons]
    rw [Pi.mul_def,
      meromorphicOrderAt_congr (UpperHalfPlane.cuspFunction_map₂_eventuallyEq (· * ·) _ _),
      ← Pi.mul_def, meromorphicOrderAt_mul (hfactor_mer x)
        (UpperHalfPlane.meromorphicAt_cuspFunction_prod t fun i _ ↦ hfactor_mer i),
      hx_ord, ih ht_ne, ← WithTop.coe_add]

end TauCeti.ModularForm
