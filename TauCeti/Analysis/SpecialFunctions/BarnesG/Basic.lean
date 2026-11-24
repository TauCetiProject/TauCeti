/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Data.Nat.Factorial.SuperFactorial
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic

/-!
# The Barnes `G`-function

The Barnes `G`-function is the entire function of order two defined by the canonical Weierstrass
product
`G(z + 1) = (2π) ^ (z / 2) exp(-z(z + 1) / 2 - γ z² / 2)`
`  * ∏' k, (1 + z / (k + 1)) ^ (k + 1) exp(-z + z² / (2(k + 1)))`,
where `γ` is the Euler–Mascheroni constant. Away from the poles of `Complex.Gamma`, it satisfies
the functional recurrence `G(z + 1) = Γ(z) G(z)` with `G(1) = 1`, interpolating the superfactorials
`G(n + 2) = sf n = ∏_{k = 1}^n k!`.

Each factor in the infinite product is the `(k + 1)`-th power of the genus-two Weierstrass
elementary factor evaluated at `-z / (k + 1)`. On compact sets its deviation from `1` is
`O(‖z‖³ / (k + 1)²)` for large `k`, making `barnesG` entire with zeros precisely at the
nonpositive integers `-n` (`n : ℕ`) of exact multiplicity `n + 1`. Its logarithmic derivative is
expressed in terms of `Complex.digamma`, and the cleared recurrence `(Γ z)⁻¹ * G(z + 1) = G(z)`
holds as an identity of entire functions on all of `ℂ`.

## Main definitions

* `TauCeti.barnesG`: the Barnes `G`-function on `ℂ`, defined by its canonical Weierstrass product.

## Main results

* `TauCeti.hasProdUniformlyOn_barnesG_factor`, `TauCeti.hasProdLocallyUniformlyOn_barnesG_factor`:
  uniform convergence of the canonical Weierstrass product on compact sets.
* `TauCeti.differentiable_barnesG`, `TauCeti.analyticAt_barnesG`: `barnesG` is entire.
* `TauCeti.barnesG_eq_zero_iff`, `TauCeti.analyticOrderAt_barnesG_neg_natCast`: `barnesG` vanishes
  precisely at `-n` (`n : ℕ`), with analytic order `n + 1` at `-n`.
* `TauCeti.logDeriv_barnesG_one`, `TauCeti.logDeriv_barnesG_add_one`: logarithmic derivative of
  `barnesG` at `1` and away from the nonpositive integers.
* `TauCeti.barnesG_one`, `TauCeti.barnesG_two`, `TauCeti.inv_Gamma_mul_barnesG_add_one`,
  `TauCeti.barnesG_add_one`: normalization and the Gamma recurrence, both in pole-cleared entire
  form on all of `ℂ` and in standard form for every nonzero `z : ℂ`.
* `TauCeti.barnesG_natCast_add_two`, `TauCeti.barnesG_natCast_add_one`,
  `TauCeti.barnesG_natCast_of_two_le`: superfactorial values at positive integers.
* `TauCeti.barnesG_conj`, `TauCeti.barnesG_ofReal_im`, `TauCeti.barnesG_ofReal_re_pos`: Schwarz
  reflection and strict positivity on `(0, ∞)`.

## References

* E. W. Barnes, *The theory of the G-function*, Quart. J. Pure Appl. Math. **31** (1900), 264–314.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., §12.14.
* [NIST DLMF, §5.17](https://dlmf.nist.gov/5.17).
-/

public section

open Complex Filter Metric Set Topology
open scoped BigOperators Nat

namespace TauCeti

/-! ### Definition and elementary factor estimates -/

/-- The Barnes `G`-function, defined on `ℂ` by its canonical Weierstrass product around `z = 1`. -/
noncomputable def barnesG (z : ℂ) : ℂ :=
  let w := z - 1
  (2 * Real.pi : ℂ) ^ (w / 2) *
    Complex.exp (-(w * (w + 1)) / 2 - Real.eulerMascheroniConstant * w ^ 2 / 2) *
    ∏' k : ℕ, (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1)))

/-- The defining canonical Weierstrass product for `barnesG`. -/
theorem barnesG_def (z : ℂ) :
    barnesG z =
      let w := z - 1
      (2 * Real.pi : ℂ) ^ (w / 2) *
        Complex.exp (-(w * (w + 1)) / 2 - Real.eulerMascheroniConstant * w ^ 2 / 2) *
        ∏' k : ℕ, (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1))) :=
  (rfl)

private noncomputable def barnesPrefactor (w : ℂ) : ℂ :=
  (2 * Real.pi : ℂ) ^ (w / 2) *
    Complex.exp (-(w * (w + 1)) / 2 - Real.eulerMascheroniConstant * w ^ 2 / 2)

private noncomputable def barnesFactor (w : ℂ) (k : ℕ) : ℂ :=
  (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1)))

private theorem barnesG_eq_prefactor_mul_tprod (z : ℂ) :
    barnesG z = barnesPrefactor (z - 1) * ∏' k : ℕ, barnesFactor (z - 1) k :=
  rfl

private theorem barnesG_add_one_eq_prefactor_mul_tprod (w : ℂ) :
    barnesG (w + 1) = barnesPrefactor w * ∏' k : ℕ, barnesFactor w k := by
  rw [barnesG_eq_prefactor_mul_tprod, add_sub_cancel_right]

private noncomputable def barnesPrefactorExp (w : ℂ) : ℂ :=
  (Real.log (2 * Real.pi) : ℂ) * (w / 2) +
    (-(w * (w + 1)) / 2 - Real.eulerMascheroniConstant * w ^ 2 / 2)

private theorem barnesPrefactor_eq_exp (w : ℂ) :
    barnesPrefactor w = Complex.exp (barnesPrefactorExp w) := by
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hlog : Complex.log (2 * Real.pi : ℂ) = (Real.log (2 * Real.pi) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, ← ofReal_log (by positivity)]
  rw [barnesPrefactor, barnesPrefactorExp, cpow_def_of_ne_zero h2pi, hlog, ← Complex.exp_add]

private theorem barnesPrefactor_ne_zero (w : ℂ) : barnesPrefactor w ≠ 0 := by
  rw [barnesPrefactor_eq_exp]
  exact Complex.exp_ne_zero _

private theorem differentiable_barnesPrefactor : Differentiable ℂ barnesPrefactor := by
  rw [funext barnesPrefactor_eq_exp]
  unfold barnesPrefactorExp
  fun_prop

private theorem barnesFactor_eq_exp_of_norm_div_le_half {w : ℂ} {k : ℕ}
    (hu : ‖w / (k + 1)‖ ≤ 1 / 2) :
    barnesFactor w k =
      Complex.exp (((k : ℂ) + 1) *
        (Complex.log (1 + w / (k + 1)) - Complex.logTaylor 3 (w / (k + 1)))) := by
  set u : ℂ := w / (k + 1)
  have hk0 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hne : 1 + u ≠ 0 := slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hu1)
  have h1u : (1 + u) ^ (k + 1) = Complex.exp (((k + 1 : ℕ) : ℂ) * Complex.log (1 + u)) := by
    rw [Complex.exp_natCast_mul, Complex.exp_log hne]
  have htaylor : Complex.logTaylor 3 u = u - u ^ 2 / 2 := by
    simp only [Complex.logTaylor_succ, Complex.logTaylor_zero, Pi.add_apply]
    norm_num
    ring
  rw [barnesFactor, h1u, ← Complex.exp_add, htaylor]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, u]
  field_simp [hk0]
  ring

private theorem norm_barnesFactor_sub_one_le {w : ℂ} {R : ℝ} {k : ℕ}
    (hR1 : 1 ≤ R) (hwR : ‖w‖ ≤ R) (hkR : 2 * R ^ 2 ≤ (k : ℝ) + 1) :
    ‖barnesFactor w k - 1‖ ≤ 4 * R ^ 3 / ((k : ℝ) + 1) ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hk1_pos : 0 < (k : ℝ) + 1 := Nat.cast_add_one_pos k
  have hk1_sq_pos : 0 < ((k : ℝ) + 1) ^ 2 := sq_pos_of_pos hk1_pos
  have hkC_norm : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)
  have hRR2 : R ≤ R ^ 2 := by
    simpa [sq] using mul_le_mul_of_nonneg_left hR1 hR0.le
  set u : ℂ := w / ((k : ℂ) + 1)
  have hu_half : ‖u‖ ≤ 1 / 2 := by
    rw [norm_div, hkC_norm, div_le_iff₀ hk1_pos]
    linarith
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu_half (by norm_num)
  rw [barnesFactor_eq_exp_of_norm_div_le_half hu_half]
  set z : ℂ := ((k : ℂ) + 1) * (Complex.log (1 + u) - Complex.logTaylor 3 u)
  have hlog_le : ‖Complex.log (1 + u) - Complex.logTaylor 3 u‖ ≤ 2 * ‖u‖ ^ 3 := by
    have hrem := Complex.norm_log_sub_logTaylor_le 2 hu1
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]
      linarith
    have h3 : ‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / ((2 : ℕ) + 1 : ℝ) ≤ ‖u‖ ^ 3 * 2 / 3 := by
      norm_num
      gcongr
    have hpos : 0 ≤ ‖u‖ ^ 3 := by positivity
    linarith [hrem, h3, hpos]
  have hz_bound : ‖z‖ ≤ 2 * R ^ 3 / ((k : ℝ) + 1) ^ 2 := by
    rw [norm_div, hkC_norm] at hlog_le
    calc ‖z‖ = ((k : ℝ) + 1) * ‖Complex.log (1 + u) - Complex.logTaylor 3 u‖ := by
          rw [norm_mul, hkC_norm]
      _ ≤ ((k : ℝ) + 1) * (2 * (‖w‖ / ((k : ℝ) + 1)) ^ 3) := by gcongr
      _ ≤ ((k : ℝ) + 1) * (2 * (R / ((k : ℝ) + 1)) ^ 3) := by gcongr
      _ = 2 * R ^ 3 / ((k : ℝ) + 1) ^ 2 := by field_simp [hk1_pos.ne']
  have hz1 : ‖z‖ ≤ 1 := by
    refine hz_bound.trans ((div_le_one hk1_sq_pos).mpr ?_)
    have hsq : (2 * R ^ 2) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hkR 2
    have hR3 : 0 < R ^ 3 := pow_pos hR0 3
    have hR34 : R ^ 3 ≤ R ^ 4 := by
      calc R ^ 3 = R ^ 3 * 1 := (mul_one _).symm
        _ ≤ R ^ 3 * R := mul_le_mul_of_nonneg_left hR1 hR3.le
        _ = R ^ 4 := by ring
    exact (by linarith [hR3, hR34] : 2 * R ^ 3 ≤ (2 * R ^ 2) ^ 2).trans hsq
  calc ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hz1
    _ ≤ 2 * (2 * R ^ 3 / ((k : ℝ) + 1) ^ 2) := by gcongr
    _ = 4 * R ^ 3 / ((k : ℝ) + 1) ^ 2 := by ring

private theorem exists_summable_norm_barnesFactor_sub_one_le {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∃ N₀ : ℕ, ∀ k ≥ N₀, ∀ w ∈ K,
      ‖barnesFactor w k - 1‖ ≤ u k := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 1
  have hR1 : 1 ≤ R := le_max_right _ _
  let N₀ : ℕ := ⌈2 * R ^ 2⌉₊
  have hs0 : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) := by simp
  have hs : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
    have h1 := (summable_nat_add_iff (f := fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) 1).mpr hs0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  have hu : Summable (fun k : ℕ ↦ 4 * R ^ 3 / ((k : ℝ) + 1) ^ 2) :=
    (hs.mul_left (4 * R ^ 3)).congr fun k ↦ by ring
  refine ⟨fun k ↦ 4 * R ^ 3 / ((k : ℝ) + 1) ^ 2, hu, N₀, fun k hk w hw ↦ ?_⟩
  have hkR : 2 * R ^ 2 ≤ (k : ℝ) + 1 := by
    have hceil : 2 * R ^ 2 ≤ (N₀ : ℝ) := Nat.le_ceil _
    have hN : (N₀ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact norm_barnesFactor_sub_one_le hR1 ((hM w hw).trans (le_max_left _ _)) hkR

/-! ### Uniform convergence of the canonical product and entireness -/

/-- The infinite product in the canonical Weierstrass representation of `barnesG (w + 1)` converges
uniformly on every compact subset of `ℂ`. -/
theorem hasProdUniformlyOn_barnesG_factor {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun (k : ℕ) (w : ℂ) ↦
        (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1))))
      (fun w ↦ ∏' k : ℕ, (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1))))
      K := by
  obtain ⟨u, hu, N₀, hN₀⟩ := exists_summable_norm_barnesFactor_sub_one_le hK
  have hbound : ∀ᶠ k : ℕ in cofinite, ∀ w ∈ K, ‖barnesFactor w k - 1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    exact (eventually_ge_atTop N₀).mono hN₀
  have hcts : ∀ k : ℕ, ContinuousOn (fun w ↦ barnesFactor w k - 1) K := fun k ↦ by
    unfold barnesFactor; fun_prop
  simpa only [barnesFactor, ← add_sub_assoc, add_sub_cancel_left] using
    Summable.hasProdUniformlyOn_one_add hK hu hbound hcts

/-- The infinite product in the canonical Weierstrass representation of `barnesG (w + 1)` converges
locally uniformly on the whole complex plane. -/
theorem hasProdLocallyUniformlyOn_barnesG_factor :
    HasProdLocallyUniformlyOn
      (fun (k : ℕ) (w : ℂ) ↦
        (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1))))
      (fun w ↦ ∏' k : ℕ, (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1))))
      Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_barnesG_factor hK

private theorem hasProdLocallyUniformlyOn_barnesFactor_subtype (s : Set ℕ) :
    HasProdLocallyUniformlyOn (fun (k : s) w ↦ barnesFactor w k)
      (fun w ↦ ∏' k : s, barnesFactor w k) Set.univ := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK ↦ ?_
  obtain ⟨u, hu, N₀, hN₀⟩ := exists_summable_norm_barnesFactor_sub_one_le hK
  have hfin : {k : s | (k : ℕ) < N₀}.Finite :=
    (Set.finite_lt_nat N₀).preimage Subtype.val_injective.injOn
  have hbound : ∀ᶠ k : s in cofinite, ∀ w ∈ K, ‖barnesFactor w k - 1‖ ≤ u k := by
    filter_upwards [hfin.compl_mem_cofinite] with k hk w hw
    exact hN₀ k (not_lt.mp hk) w hw
  have hcts : ∀ k : s, ContinuousOn (fun w ↦ barnesFactor w k - 1) K := fun k ↦ by
    unfold barnesFactor; fun_prop
  simpa only [← add_sub_assoc, add_sub_cancel_left] using
    Summable.hasProdUniformlyOn_one_add hK (hu.subtype _) hbound hcts

private theorem differentiable_tprod_barnesFactor :
    Differentiable ℂ (fun w ↦ ∏' k : ℕ, barnesFactor w k) := by
  rw [← differentiableOn_univ]
  have hlu : HasProdLocallyUniformlyOn (fun k w ↦ barnesFactor w k)
      (fun w ↦ ∏' k : ℕ, barnesFactor w k) Set.univ := hasProdLocallyUniformlyOn_barnesG_factor
  refine hlu.differentiableOn ?_ isOpen_univ
  refine Eventually.of_forall fun s ↦ Differentiable.differentiableOn ?_
  unfold barnesFactor
  fun_prop

/-- The Barnes `G`-function is complex differentiable on the whole plane (entire). -/
@[fun_prop]
theorem differentiable_barnesG : Differentiable ℂ barnesG := by
  rw [funext barnesG_eq_prefactor_mul_tprod]
  exact (differentiable_barnesPrefactor.comp (differentiable_id.sub_const 1)).mul
    (differentiable_tprod_barnesFactor.comp (differentiable_id.sub_const 1))

/-- The Barnes `G`-function is analytic at every complex point. -/
@[fun_prop]
theorem analyticAt_barnesG (z : ℂ) : AnalyticAt ℂ barnesG z :=
  differentiable_barnesG.analyticAt z

/-- The Barnes `G`-function is analytic on every open neighborhood in `ℂ`. -/
theorem analyticOnNhd_barnesG : AnalyticOnNhd ℂ barnesG Set.univ :=
  fun z _ ↦ analyticAt_barnesG z

/-- The Barnes `G`-function is continuous everywhere on `ℂ`. -/
@[fun_prop]
theorem continuous_barnesG : Continuous barnesG :=
  differentiable_barnesG.continuous

/-! ### Normalization at `1` and zero divisor -/

/-- The Barnes `G`-function is normalized to `1` at `z = 1`. -/
@[simp]
theorem barnesG_one : barnesG 1 = 1 := by
  simp [barnesG_def]

private theorem summable_norm_barnesFactor_sub_one (w : ℂ) :
    Summable (fun k : ℕ ↦ ‖barnesFactor w k - 1‖) := by
  obtain ⟨u, hu, N₀, hN₀⟩ :=
    exists_summable_norm_barnesFactor_sub_one_le (isCompact_singleton (x := w))
  refine hu.of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop N₀] with k hk
  simpa only [Real.norm_eq_abs, abs_norm] using hN₀ k hk w (mem_singleton w)

private theorem barnesFactor_eq_zero_iff {w : ℂ} {k : ℕ} :
    barnesFactor w k = 0 ↔ w = -((k : ℂ) + 1) := by
  rw [barnesFactor, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _),
    pow_eq_zero_iff (Nat.succ_ne_zero k)]
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  constructor
  · intro h
    have h' : w / ((k : ℂ) + 1) = -1 := eq_neg_of_add_eq_zero_right h
    rw [div_eq_iff hk] at h'
    linear_combination h'
  · rintro rfl
    field_simp [hk]
    ring

private theorem tprod_barnesFactor_eq_zero_iff (w : ℂ) :
    (∏' k : ℕ, barnesFactor w k) = 0 ↔ ∃ k : ℕ, w = -((k : ℂ) + 1) := by
  constructor
  · intro h
    by_contra! hne
    have h1 : ∀ k : ℕ, 1 + (barnesFactor w k - 1) ≠ 0 := by
      intro k
      rw [← add_sub_assoc, add_sub_cancel_left]
      exact mt barnesFactor_eq_zero_iff.mp (hne k)
    have hp := tprod_one_add_ne_zero_of_summable h1 (summable_norm_barnesFactor_sub_one w)
    simp only [← add_sub_assoc, add_sub_cancel_left] at hp
    exact hp h
  · rintro ⟨k, rfl⟩
    exact tprod_of_exists_eq_zero ⟨k, barnesFactor_eq_zero_iff.mpr rfl⟩

/-- The Barnes `G`-function vanishes precisely at the nonpositive integers. -/
theorem barnesG_eq_zero_iff {z : ℂ} :
    barnesG z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  rw [barnesG_eq_prefactor_mul_tprod, mul_eq_zero, or_iff_right (barnesPrefactor_ne_zero _),
    tprod_barnesFactor_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linear_combination hk⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-- The Barnes `G`-function vanishes at every nonpositive integer `-n`. -/
@[simp]
theorem barnesG_neg_natCast (n : ℕ) : barnesG (-(n : ℂ)) = 0 :=
  barnesG_eq_zero_iff.mpr ⟨n, rfl⟩

/-- The Barnes `G`-function vanishes at the origin. -/
@[simp]
theorem barnesG_zero : barnesG 0 = 0 := by
  simpa using barnesG_neg_natCast 0

/-- Away from the nonpositive integers, `barnesG` is nonzero. -/
theorem barnesG_ne_zero {z : ℂ} (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) : barnesG z ≠ 0 := by
  intro h
  rcases barnesG_eq_zero_iff.mp h with ⟨n, rfl⟩
  exact hz n rfl

/-- On the slit plane `ℂ \ (-∞, 0]`, `barnesG` is everywhere nonzero. -/
theorem barnesG_ne_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    barnesG z ≠ 0 :=
  barnesG_ne_zero (ne_neg_natCast_of_mem_slitPlane hz)

/-- On the open right half-plane `Re z > 0`, `barnesG` is everywhere nonzero. -/
theorem barnesG_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : barnesG z ≠ 0 :=
  barnesG_ne_zero_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hz))

/-! ### Multiplicities of the zeros -/

private theorem analyticOrderAt_barnesFactor_root (n : ℕ) :
    analyticOrderAt (fun z ↦ barnesFactor (z - 1) n) (-(n : ℂ)) = n + 1 := by
  have hn0 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hlin : (fun z : ℂ ↦ 1 + (z - 1) / ((n : ℂ) + 1)) =
      fun z : ℂ ↦ (((n : ℂ) + 1)⁻¹) * (z - (-(n : ℂ))) := by
    ext z
    field_simp [hn0]
    ring
  have hord_lin : analyticOrderAt (fun z : ℂ ↦ 1 + (z - 1) / ((n : ℂ) + 1)) (-(n : ℂ)) = 1 := by
    refine AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop) ?_ ?_
    · field_simp [hn0]; ring
    · have hd : HasDerivAt (fun z : ℂ ↦ (((n : ℂ) + 1)⁻¹) * (z - (-(n : ℂ))))
          (((n : ℂ) + 1)⁻¹) (-(n : ℂ)) := by
        simpa using ((hasDerivAt_id (-(n : ℂ))).sub_const (-(n : ℂ))).const_mul (((n : ℂ) + 1)⁻¹)
      rw [hlin, hd.deriv]
      exact inv_ne_zero hn0
  have hpow : analyticOrderAt ((fun z : ℂ ↦ 1 + (z - 1) / ((n : ℂ) + 1)) ^ (n + 1))
      (-(n : ℂ)) = n + 1 := by
    rw [analyticOrderAt_pow (by fun_prop), hord_lin, nsmul_one, Nat.cast_add, Nat.cast_one]
  have hexp_ord : analyticOrderAt
      (fun z : ℂ ↦ Complex.exp (-(z - 1) + (z - 1) ^ 2 / (2 * ((n : ℂ) + 1)))) (-(n : ℂ)) = 0 :=
    (AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)).mpr (Complex.exp_ne_zero _)
  have hmul := analyticOrderAt_mul
    (f := (fun z : ℂ ↦ 1 + (z - 1) / ((n : ℂ) + 1)) ^ (n + 1))
    (g := fun z : ℂ ↦ Complex.exp (-(z - 1) + (z - 1) ^ 2 / (2 * ((n : ℂ) + 1))))
    (z₀ := -(n : ℂ)) (by fun_prop) (by fun_prop)
  have hfac_eq : (fun z ↦ barnesFactor (z - 1) n) =
      ((fun z : ℂ ↦ 1 + (z - 1) / ((n : ℂ) + 1)) ^ (n + 1)) *
        fun z : ℂ ↦ Complex.exp (-(z - 1) + (z - 1) ^ 2 / (2 * ((n : ℂ) + 1))) := rfl
  rw [hfac_eq, hmul, hpow, hexp_ord, add_zero]

/-- At each nonpositive integer `-n` (`n : ℕ`), `barnesG` has a zero of exact order `n + 1`. -/
theorem analyticOrderAt_barnesG_neg_natCast (n : ℕ) :
    analyticOrderAt barnesG (-(n : ℂ)) = n + 1 := by
  let S : Set ℕ := ({n} : Finset ℕ)
  have htail_diff : Differentiable ℂ (fun w ↦ ∏' k : (Sᶜ : Set ℕ), barnesFactor w k) := by
    rw [← differentiableOn_univ]
    refine (hasProdLocallyUniformlyOn_barnesFactor_subtype Sᶜ).differentiableOn ?_ isOpen_univ
    refine Eventually.of_forall fun t ↦ Differentiable.differentiableOn ?_
    unfold barnesFactor; fun_prop
  have htail_an : AnalyticAt ℂ (fun z ↦ ∏' k : (Sᶜ : Set ℕ), barnesFactor (z - 1) k) (-(n : ℂ)) :=
    (htail_diff.comp (differentiable_id.sub_const 1)).analyticAt _
  have htail_ne : (∏' k : (Sᶜ : Set ℕ), barnesFactor (-(n : ℂ) - 1) k) ≠ 0 := by
    have hsum : Summable (fun k : (Sᶜ : Set ℕ) ↦ ‖barnesFactor (-(n : ℂ) - 1) k - 1‖) :=
      (summable_norm_barnesFactor_sub_one _).subtype _
    have h1 : ∀ k : (Sᶜ : Set ℕ), 1 + (barnesFactor (-(n : ℂ) - 1) k - 1) ≠ 0 := by
      intro k
      rw [← add_sub_assoc, add_sub_cancel_left]
      intro hz
      have hkne : (k : ℕ) ≠ n := by simpa [S] using k.property
      have hroot := barnesFactor_eq_zero_iff.mp hz
      have hcast : ((k : ℕ) : ℂ) = (n : ℂ) := by linear_combination hroot
      exact hkne (Nat.cast_injective hcast)
    have hp := tprod_one_add_ne_zero_of_summable h1 hsum
    simpa only [← add_sub_assoc, add_sub_cancel_left] using hp
  have hpre_an : AnalyticAt ℂ (fun z ↦ barnesPrefactor (z - 1)) (-(n : ℂ)) :=
    (differentiable_barnesPrefactor.comp (differentiable_id.sub_const 1)).analyticAt _
  have hfac_an : AnalyticAt ℂ (fun z ↦ barnesFactor (z - 1) n) (-(n : ℂ)) := by
    unfold barnesFactor; fun_prop
  have heq : barnesG =
      (fun z ↦ barnesPrefactor (z - 1)) *
        ((fun z ↦ barnesFactor (z - 1) n) *
          fun z ↦ ∏' k : (Sᶜ : Set ℕ), barnesFactor (z - 1) k) := by
    ext z
    simp only [Pi.mul_apply, barnesG_eq_prefactor_mul_tprod]
    congr 1
    have htail_mul : Multipliable (fun k : (Sᶜ : Set ℕ) ↦ barnesFactor (z - 1) k) :=
      ((hasProdLocallyUniformlyOn_barnesFactor_subtype Sᶜ).hasProd (mem_univ _)).multipliable
    have hsplit := Multipliable.tprod_mul_tprod_compl (s := S)
      (f := fun k ↦ barnesFactor (z - 1) k) Multipliable.of_finite htail_mul
    rw [Finset.tprod_subtype' ({n} : Finset ℕ) (fun k ↦ barnesFactor (z - 1) k),
      Finset.prod_singleton] at hsplit
    exact hsplit.symm
  rw [heq, analyticOrderAt_mul hpre_an (hfac_an.mul htail_an),
    analyticOrderAt_mul hfac_an htail_an,
    hpre_an.analyticOrderAt_eq_zero.mpr (barnesPrefactor_ne_zero _),
    htail_an.analyticOrderAt_eq_zero.mpr htail_ne,
    analyticOrderAt_barnesFactor_root n, zero_add, add_zero]

/-- The zero of `barnesG` at `0` is simple. -/
theorem analyticOrderAt_barnesG_zero : analyticOrderAt barnesG 0 = 1 := by
  simpa using analyticOrderAt_barnesG_neg_natCast 0

/-! ### Logarithmic derivative -/

private theorem hasDerivAt_barnesFactor (w : ℂ) (k : ℕ) :
    HasDerivAt (fun z ↦ barnesFactor z k)
      ((1 + w / (k + 1)) ^ k * (w / (k + 1)) ^ 2 *
        Complex.exp (-w + w ^ 2 / (2 * (k + 1)))) w := by
  have hk0 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have h1 : HasDerivAt (fun z : ℂ ↦ (1 + z / ((k : ℂ) + 1)) ^ (k + 1))
      (((k + 1 : ℕ) : ℂ) * (1 + w / ((k : ℂ) + 1)) ^ k * (1 / ((k : ℂ) + 1))) w := by
    have hlin : HasDerivAt (fun z : ℂ ↦ 1 + z / ((k : ℂ) + 1)) (1 / ((k : ℂ) + 1)) w := by
      simpa [one_div] using ((hasDerivAt_id w).div_const ((k : ℂ) + 1)).const_add (1 : ℂ)
    exact (HasDerivAt.pow hlin (k + 1)).congr_deriv (by simp)
  have h2 : HasDerivAt (fun z : ℂ ↦ Complex.exp (-z + z ^ 2 / (2 * ((k : ℂ) + 1))))
      ((-1 + w / ((k : ℂ) + 1)) * Complex.exp (-w + w ^ 2 / (2 * ((k : ℂ) + 1)))) w := by
    have hquad : HasDerivAt (fun z : ℂ ↦ -z + z ^ 2 / (2 * ((k : ℂ) + 1)))
        (-1 + w / ((k : ℂ) + 1)) w := by
      have hp := ((hasDerivAt_id w).neg).add
        (((hasDerivAt_id w).pow 2).div_const (2 * ((k : ℂ) + 1)))
      refine hp.congr_deriv ?_
      simp only [id_eq]
      field_simp [hk0]
      ring
    simpa [mul_comm] using hquad.cexp
  refine (h1.mul h2).congr_deriv ?_
  have hpow : (1 + w / ((k : ℂ) + 1)) ^ (k + 1) =
      (1 + w / ((k : ℂ) + 1)) ^ k * (1 + w / ((k : ℂ) + 1)) := pow_succ _ _
  rw [hpow]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hk0]
  ring

private theorem logDeriv_barnesFactor {w : ℂ} {k : ℕ} (hw : w ≠ -((k : ℂ) + 1)) :
    logDeriv (fun z ↦ barnesFactor z k) w =
      w * (1 / ((k : ℂ) + 1) - 1 / (w + ((k : ℂ) + 1))) := by
  have hk0 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hwk : w + ((k : ℂ) + 1) ≠ 0 := fun h ↦ hw (eq_neg_of_add_eq_zero_left h)
  have h1w : 1 + w / ((k : ℂ) + 1) ≠ 0 := fun h ↦
    hw (barnesFactor_eq_zero_iff.mp (by simp [barnesFactor, h]))
  have hexp : Complex.exp (-w + w ^ 2 / (2 * ((k : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have hpow_ne : (1 + w / ((k : ℂ) + 1)) ^ k ≠ 0 := pow_ne_zero k h1w
  rw [logDeriv_apply, (hasDerivAt_barnesFactor w k).deriv, barnesFactor,
    pow_succ (1 + w / ((k : ℂ) + 1)) k, mul_div_mul_right _ _ hexp,
    mul_div_mul_left _ _ hpow_ne]
  have hlin : 1 + w / ((k : ℂ) + 1) = (w + ((k : ℂ) + 1)) / ((k : ℂ) + 1) := by
    field_simp [hk0]; ring
  rw [hlin]
  field_simp [hk0, hwk]
  ring

private theorem logDeriv_barnesPrefactor (w : ℂ) :
    logDeriv barnesPrefactor w =
      (Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 - w - Real.eulerMascheroniConstant * w := by
  have hd : HasDerivAt barnesPrefactorExp
      ((Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 - w - Real.eulerMascheroniConstant * w) w := by
    unfold barnesPrefactorExp
    have h1 : HasDerivAt (fun z : ℂ ↦ (Real.log (2 * Real.pi) : ℂ) * (z / 2))
        ((Real.log (2 * Real.pi) : ℂ) * (1 / 2)) w :=
      ((hasDerivAt_id w).div_const 2).const_mul _
    have h2 : HasDerivAt (fun z : ℂ ↦ -(z * (z + 1)) / 2) (-(w + (w + 1)) / 2) w := by
      have hm := ((hasDerivAt_id w).mul ((hasDerivAt_id w).add_const 1)).neg.div_const 2
      refine hm.congr_deriv ?_
      simp only [id_eq]; ring
    have h3 : HasDerivAt (fun z : ℂ ↦ (Real.eulerMascheroniConstant : ℂ) * z ^ 2 / 2)
        ((Real.eulerMascheroniConstant : ℂ) * (2 * w) / 2) w := by
      have hm := (((hasDerivAt_id w).pow 2).const_mul
        (Real.eulerMascheroniConstant : ℂ)).div_const 2
      refine hm.congr_deriv ?_
      simp only [id_eq]; ring
    refine (h1.add (h2.sub h3)).congr_deriv ?_
    ring
  rw [funext barnesPrefactor_eq_exp, logDeriv_apply, hd.cexp.deriv]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

private theorem logDeriv_barnesG_comp_add_one (z : ℂ) :
    logDeriv (fun w ↦ barnesG (w + 1)) z = logDeriv barnesG (z + 1) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

/-- Logarithmic derivative of `barnesG` at `z + 1` away from the negative integers `-(n + 1)`;
this formula holds at `z = 0` as well as at every non-integer complex point. -/
theorem logDeriv_barnesG_add_one_of_ne_neg_succ {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -((n : ℂ) + 1)) :
    logDeriv barnesG (z + 1) =
      (Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 - z + z * Complex.digamma (z + 1) := by
  have hz1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := fun m hm ↦ hz m (by linear_combination hm)
  have hprod_ne : (∏' k : ℕ, barnesFactor z k) ≠ 0 := by
    rw [ne_eq, tprod_barnesFactor_eq_zero_iff]
    rintro ⟨k, hk⟩
    exact hz k hk
  have hsum_gauss : Summable (fun k : ℕ ↦ logDeriv (fun w ↦ barnesFactor w k) z) := by
    refine ((Complex.summable_gaussSeries (z + 1)).mul_left z).congr fun k ↦ ?_
    rw [logDeriv_barnesFactor (hz k)]
    congr 2; ring
  have hlu : HasProdLocallyUniformlyOn (fun k w ↦ barnesFactor w k)
      (fun w ↦ ∏' k : ℕ, barnesFactor w k) Set.univ := hasProdLocallyUniformlyOn_barnesG_factor
  have htprod_ld : logDeriv (fun w ↦ ∏' k : ℕ, barnesFactor w k) z =
      ∑' k : ℕ, logDeriv (fun w ↦ barnesFactor w k) z :=
    logDeriv_tprod_eq_tsum isOpen_univ (mem_univ z)
      (fun k ↦ mt barnesFactor_eq_zero_iff.mp (hz k))
      (fun k ↦ by unfold barnesFactor; fun_prop)
      hsum_gauss hlu.multipliableLocallyUniformlyOn hprod_ne
  have htsum_val : (∑' k : ℕ, logDeriv (fun w ↦ barnesFactor w k) z) =
      z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant) := by
    have hcongr : (fun k : ℕ ↦ logDeriv (fun w ↦ barnesFactor w k) z) =
        fun k : ℕ ↦ z * (1 / ((k : ℂ) + 1) - 1 / (z + 1 + k)) := by
      ext k
      rw [logDeriv_barnesFactor (hz k)]
      congr 2; ring
    rw [hcongr, tsum_mul_left, Complex.digamma_eq_gaussSeries hz1]
    ring
  rw [← logDeriv_barnesG_comp_add_one, funext barnesG_add_one_eq_prefactor_mul_tprod,
    logDeriv_fun_mul z (barnesPrefactor_ne_zero z) hprod_ne
      (differentiable_barnesPrefactor z) (differentiable_tprod_barnesFactor z),
    logDeriv_barnesPrefactor, htprod_ld, htsum_val]
  ring

/-- The logarithmic derivative of `barnesG` at `1` is `log(2π) / 2 - 1 / 2`. -/
theorem logDeriv_barnesG_one :
    logDeriv barnesG 1 = (Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 := by
  have hz0 : ∀ n : ℕ, (0 : ℂ) ≠ -((n : ℂ) + 1) := fun n h ↦
    Nat.cast_add_one_ne_zero n (by linear_combination h)
  simpa using logDeriv_barnesG_add_one_of_ne_neg_succ hz0

/-- The derivative of `barnesG` at `1` is `log(2π) / 2 - 1 / 2`. -/
theorem deriv_barnesG_one :
    deriv barnesG 1 = (Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 := by
  have h := logDeriv_barnesG_one
  rwa [logDeriv_apply, barnesG_one, div_one] at h

/-- Away from the nonpositive integers, `logDeriv barnesG (z + 1)` equals
`log(2π) / 2 + 1 / 2 - z + z * digamma z`. -/
theorem logDeriv_barnesG_add_one {z : ℂ} (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    logDeriv barnesG (z + 1) =
      (Real.log (2 * Real.pi) : ℂ) / 2 + 1 / 2 - z + z * Complex.digamma z := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hz_succ : ∀ n : ℕ, z ≠ -((n : ℂ) + 1) := fun n ↦ by
    simpa [Nat.cast_add, Nat.cast_one, neg_add] using hz (n + 1)
  rw [logDeriv_barnesG_add_one_of_ne_neg_succ hz_succ,
    Complex.digamma_apply_add_one z hz, mul_add, mul_inv_cancel₀ hz0]
  ring

/-! ### Evaluation at `2`, the Gamma recurrence, and superfactorial values -/

private theorem barnesPrefactor_one_mul_prod_barnesFactor (N : ℕ) :
    barnesPrefactor 1 * (∏ k ∈ Finset.range N, barnesFactor 1 k) =
      Complex.exp
        (((-(Real.log (N ! : ℝ) -
            (((N : ℝ) + 1 / 2) * Real.log ((N : ℝ) + 1) - ((N : ℝ) + 1) +
              Real.log (2 * Real.pi) / 2)) +
          (1 / 2) * ((harmonic N : ℝ) - Real.log ((N : ℝ) + 1) -
            Real.eulerMascheroniConstant)) : ℝ) : ℂ) := by
  have htel : (∏ k ∈ Finset.range N, (1 + 1 / ((k : ℝ) + 1)) ^ (k + 1)) =
      ((N : ℝ) + 1) ^ N / (N ! : ℝ) := by
    refine Finset.prod_range_induction
      (fun k : ℕ ↦ (1 + 1 / ((k : ℝ) + 1)) ^ (k + 1))
      (fun n : ℕ ↦ ((n : ℝ) + 1) ^ n / (n ! : ℝ)) (by simp) N fun k _ ↦ ?_
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hfac : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hlin : (1 : ℝ) + 1 / ((k : ℝ) + 1) = ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      field_simp [hk1]; ring
    rw [Nat.factorial_succ, hlin, div_pow, pow_succ ((k : ℝ) + 1) k]
    push_cast
    field_simp [hk1, hfac]
    ring
  have hprod_split : (∏ k ∈ Finset.range N, barnesFactor 1 k) =
      ((∏ k ∈ Finset.range N, (1 + 1 / ((k : ℝ) + 1)) ^ (k + 1) : ℝ) : ℂ) *
        Complex.exp (∑ k ∈ Finset.range N, (-1 + (1 : ℂ) ^ 2 / (2 * ((k : ℂ) + 1)))) := by
    simp only [barnesFactor, Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1; push_cast; rfl
  have hsum_exp : (∑ k ∈ Finset.range N, (-1 + (1 : ℂ) ^ 2 / (2 * ((k : ℂ) + 1)))) =
      ((-(N : ℝ) + (harmonic N : ℝ) / 2 : ℝ) : ℂ) := by
    rw [Finset.sum_add_distrib]
    have h1 : (∑ _k ∈ Finset.range N, (-1 : ℂ)) = -(N : ℂ) := by simp
    have h2 : (∑ k ∈ Finset.range N, (1 : ℂ) ^ 2 / (2 * ((k : ℂ) + 1))) =
        (((harmonic N : ℝ) / 2 : ℝ) : ℂ) := by
      rw [harmonic]; push_cast; rw [Finset.sum_div]
      refine (Finset.sum_congr rfl fun k _ ↦ ?_).symm
      have hk0 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
      field_simp [hk0]
    rw [h1, h2]; push_cast; ring
  have hN1_pos : 0 < (N : ℝ) + 1 := by positivity
  have hfac_pos : 0 < (N ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hpow_exp : (((N : ℝ) + 1) ^ N / (N ! : ℝ)) =
      Real.exp ((N : ℝ) * Real.log ((N : ℝ) + 1) - Real.log (N ! : ℝ)) := by
    rw [Real.exp_sub, Real.exp_log hfac_pos, Real.exp_natCast_mul, Real.exp_log hN1_pos]
  rw [barnesPrefactor_eq_exp, barnesPrefactorExp, hprod_split, htel, hpow_exp, hsum_exp,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Barnes `G`-function takes the value `1` at `z = 2`. -/
@[simp]
theorem barnesG_two : barnesG 2 = 1 := by
  have hlu : HasProdLocallyUniformlyOn (fun k w ↦ barnesFactor w k)
      (fun w ↦ ∏' k : ℕ, barnesFactor w k) Set.univ := hasProdLocallyUniformlyOn_barnesG_factor
  have h21 : (2 : ℂ) - 1 = 1 := by ring
  have hlim_prod : Tendsto (fun N : ℕ ↦ barnesPrefactor 1 * ∏ k ∈ Finset.range N, barnesFactor 1 k)
      atTop (𝓝 (barnesG 2)) := by
    have hp := (hlu.hasProd (mem_univ (1 : ℂ))).tendsto_prod_nat
    simpa only [barnesG_eq_prefactor_mul_tprod, h21] using hp.const_mul (barnesPrefactor 1)
  have hst := Stirling.tendsto_log_factorial_sub_stirling.neg
  have hhm : Tendsto (fun N : ℕ ↦ (harmonic N : ℝ) - Real.log ((N : ℝ) + 1) -
      Real.eulerMascheroniConstant) atTop (𝓝 0) := by
    simpa using Real.tendsto_harmonic_sub_log_add_one.sub_const Real.eulerMascheroniConstant
  have hL_tendsto := hst.add (hhm.const_mul (1 / 2 : ℝ))
  have hc : Continuous (fun x : ℝ ↦ Complex.exp (x : ℂ)) :=
    Complex.continuous_exp.comp continuous_ofReal
  have hexp_tendsto : Tendsto
      (fun N : ℕ ↦ barnesPrefactor 1 * ∏ k ∈ Finset.range N, barnesFactor 1 k) atTop (𝓝 1) := by
    simp_rw [barnesPrefactor_one_mul_prod_barnesFactor]
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hL_tendsto
  exact tendsto_nhds_unique hlim_prod hexp_tendsto

private theorem inv_Gamma_mul_barnesG_add_one_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    (Complex.Gamma z)⁻¹ * barnesG (z + 1) = barnesG z := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  let Q : ℂ → ℂ := fun w ↦ barnesG (w + 1) / (Complex.Gamma w * barnesG w)
  have hU_open : IsOpen U := isOpen_re_gt 0
  have hno_pole : ∀ {w : ℂ}, w ∈ U → ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro w hw n h
    have hw_re : 0 < w.re := hw
    rw [h] at hw_re
    simp only [neg_re, natCast_re] at hw_re
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hQ_diff : DifferentiableOn ℂ Q U := fun w hw ↦ by
    have hG1 : DifferentiableAt ℂ (fun u ↦ barnesG (u + 1)) w :=
      (differentiable_barnesG.comp (differentiable_id.add_const 1)) w
    have hden : DifferentiableAt ℂ (fun u ↦ Complex.Gamma u * barnesG u) w :=
      (Complex.differentiableAt_Gamma w (hno_pole hw)).mul (differentiable_barnesG w)
    exact (hG1.div hden (mul_ne_zero (Complex.Gamma_ne_zero (hno_pole hw))
      (barnesG_ne_zero_of_re_pos hw))).differentiableWithinAt
  have hQ_deriv_zero : ∀ w ∈ U, deriv Q w = 0 := by
    intro w hw
    have hp := hno_pole hw
    have hw_re : 0 < w.re := hw
    have hw_sub_succ : ∀ n : ℕ, w - 1 ≠ -((n : ℂ) + 1) := fun n h ↦ hp n (by linear_combination h)
    have hΓ_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hp
    have hGw_ne : barnesG w ≠ 0 := barnesG_ne_zero_of_re_pos hw
    have hGw1_ne : barnesG (w + 1) ≠ 0 :=
      barnesG_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
    have hGw_ld : logDeriv barnesG w =
        (Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 - (w - 1) + (w - 1) * Complex.digamma w := by
      simpa [sub_add_cancel] using logDeriv_barnesG_add_one_of_ne_neg_succ hw_sub_succ
    have hQ_ld : logDeriv Q w = 0 := by
      have hd1 : DifferentiableAt ℂ (fun u ↦ barnesG (u + 1)) w :=
        (differentiable_barnesG.comp (differentiable_id.add_const 1)) w
      have hdΓ : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma w hp
      have hdG : DifferentiableAt ℂ barnesG w := differentiable_barnesG w
      have hdiv := logDeriv_fun_div (f := fun u ↦ barnesG (u + 1))
        (g := fun u ↦ Complex.Gamma u * barnesG u) w hGw1_ne (mul_ne_zero hΓ_ne hGw_ne) hd1
        (hdΓ.mul hdG)
      have hmul := logDeriv_fun_mul (f := Complex.Gamma) (g := barnesG) w hΓ_ne hGw_ne hdΓ hdG
      dsimp only [Q]
      rw [hdiv, hmul, logDeriv_barnesG_comp_add_one, logDeriv_barnesG_add_one hp, hGw_ld,
        ← Complex.digamma_def]
      ring
    rw [logDeriv_apply] at hQ_ld
    exact (div_eq_zero_iff.mp hQ_ld).resolve_right
      (div_ne_zero hGw1_ne (mul_ne_zero hΓ_ne hGw_ne))
  have hQ_const : Q z = Q 1 :=
    (convex_halfSpace_re_gt 0).is_const_of_fderivWithin_eq_zero hQ_diff
      (fun u hu ↦ by
        rw [fderivWithin_eq_fderiv (hU_open.uniqueDiffWithinAt hu)
          (hQ_diff.differentiableAt (hU_open.mem_nhds hu))]
        ext1; simp [hQ_deriv_zero u hu]) hz (by simp)
  have h11 : (1 : ℂ) + 1 = 2 := by ring
  have hQ1 : Q 1 = 1 := by simp [Q, h11, barnesG_two, barnesG_one, Complex.Gamma_one]
  have hp := hno_pole hz
  have hΓ_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hp
  have hGz_ne : barnesG z ≠ 0 := barnesG_ne_zero_of_re_pos hz
  have hQz : barnesG (z + 1) / (Complex.Gamma z * barnesG z) = 1 := hQ_const.trans hQ1
  rw [div_eq_one_iff_eq (mul_ne_zero hΓ_ne hGz_ne)] at hQz
  rw [hQz, inv_mul_cancel_left₀ hΓ_ne]

/-- Pole-cleared entire form of the Gamma recurrence, valid for every complex number `z`:
`(Γ z)⁻¹ * G(z + 1) = G(z)`. -/
theorem inv_Gamma_mul_barnesG_add_one (z : ℂ) :
    (Complex.Gamma z)⁻¹ * barnesG (z + 1) = barnesG z := by
  let F : ℂ → ℂ := fun w ↦ (Complex.Gamma w)⁻¹ * barnesG (w + 1)
  have hF_an : AnalyticOnNhd ℂ F Set.univ := fun w _ ↦
    (Complex.differentiable_one_div_Gamma.mul
      (differentiable_barnesG.comp (differentiable_id.add_const 1))).analyticAt w
  have hev : F =ᶠ[𝓝 (1 : ℂ)] barnesG := by
    filter_upwards [(isOpen_re_gt 0).mem_nhds (by simp : 0 < (1 : ℂ).re)] with w hw
    exact inv_Gamma_mul_barnesG_add_one_of_re_pos hw
  exact hF_an.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_barnesG
    isPreconnected_univ (mem_univ (1 : ℂ)) hev (mem_univ z)

/-- **Gamma recurrence for the Barnes `G`-function**: for every nonzero complex number `z`,
`barnesG (z + 1) = Complex.Gamma z * barnesG z`. At negative integers both sides vanish. -/
theorem barnesG_add_one {z : ℂ} (hz : z ≠ 0) :
    barnesG (z + 1) = Complex.Gamma z * barnesG z := by
  by_cases hneg : ∃ n : ℕ, z = -(n : ℂ)
  · rcases hneg with ⟨_ | m, rfl⟩
    · exact absurd (by simp) hz
    · have hm : -(((m + 1 : ℕ) : ℂ)) + 1 = -(m : ℂ) := by push_cast; ring
      rw [hm, barnesG_neg_natCast, barnesG_neg_natCast, mul_zero]
  · have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (not_exists.mp hneg)
    rw [← inv_Gamma_mul_barnesG_add_one z, mul_inv_cancel_left₀ hΓ]

/-- Iterated Gamma recurrence for `barnesG` along natural shifts `n` avoiding `0` at every
intermediate argument `z + j` (`j < n`). -/
theorem barnesG_add_natCast {z : ℂ} {n : ℕ} (hz : ∀ j ∈ Finset.range n, z + j ≠ 0) :
    barnesG (z + n) = (∏ j ∈ Finset.range n, Complex.Gamma (z + j)) * barnesG z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev : ∀ j ∈ Finset.range n, z + j ≠ 0 := fun j hj ↦
      hz j (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))
    have hzn : z + n ≠ 0 := hz n (Finset.self_mem_range_succ n)
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, barnesG_add_one hzn, ih hprev,
      Finset.prod_range_succ]
    ring

/-- **Superfactorial values**: for every `n : ℕ`, `barnesG (n + 1) = ∏ k ∈ range n, k!`. -/
theorem barnesG_natCast_add_one (n : ℕ) :
    barnesG (n + 1) = ∏ k ∈ Finset.range n, (k ! : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, barnesG_add_one (Nat.cast_add_one_ne_zero n), ih, Finset.prod_range_succ,
      Complex.Gamma_nat_eq_factorial]
    ring

/-- For every `n : ℕ`, `barnesG (n + 2)` equals the superfactorial `Nat.superFactorial n`. -/
theorem barnesG_natCast_add_two (n : ℕ) :
    barnesG (n + 2) = (Nat.superFactorial n : ℂ) := by
  have hcast : (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [hcast, barnesG_natCast_add_one (n + 1), ← Nat.cast_prod, Nat.prod_range_succ_factorial]

/-- For every integer `n ≥ 2`, `barnesG n = ∏_{k = 1}^{n - 2} k!`. -/
theorem barnesG_natCast_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    barnesG n = ∏ k ∈ Finset.Icc 1 (n - 2), (k ! : ℂ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hcast : ((2 + m : ℕ) : ℂ) = (m : ℂ) + 2 := by push_cast; ring
  rw [hcast, barnesG_natCast_add_two, Nat.add_sub_cancel_left, ← Nat.cast_prod,
    Nat.prod_Icc_factorial]

/-- At `z = 3`, `barnesG 3 = 1`. -/
@[simp]
theorem barnesG_three : barnesG 3 = 1 := by
  have h := barnesG_natCast_add_two 1
  norm_num at h ⊢
  exact h

/-- At `z = 4`, `barnesG 4 = 2`. -/
@[simp]
theorem barnesG_four : barnesG 4 = 2 := by
  have h := barnesG_natCast_add_two 2
  norm_num at h ⊢
  exact h

/-! ### Conjugation symmetry and positive real values -/

private theorem barnesPrefactor_conj (w : ℂ) :
    barnesPrefactor (starRingEnd ℂ w) = starRingEnd ℂ (barnesPrefactor w) := by
  rw [barnesPrefactor_eq_exp, barnesPrefactor_eq_exp, ← Complex.exp_conj]
  congr 1
  simp [barnesPrefactorExp, _root_.map_ofNat]

private theorem barnesFactor_conj (w : ℂ) (k : ℕ) :
    barnesFactor (starRingEnd ℂ w) k = starRingEnd ℂ (barnesFactor w k) := by
  simp only [barnesFactor, map_mul, map_pow, ← Complex.exp_conj]
  congr 2
  · simp
  · simp [_root_.map_ofNat]

/-- Schwarz reflection for the Barnes `G`-function: `G(conj z) = conj (G z)`. -/
theorem barnesG_conj (z : ℂ) :
    barnesG (starRingEnd ℂ z) = starRingEnd ℂ (barnesG z) := by
  rw [barnesG_eq_prefactor_mul_tprod, barnesG_eq_prefactor_mul_tprod]
  have hsub : starRingEnd ℂ z - 1 = starRingEnd ℂ (z - 1) := by simp
  rw [hsub, barnesPrefactor_conj, map_mul]
  congr 1
  have hlu : HasProdLocallyUniformlyOn (fun k w ↦ barnesFactor w k)
      (fun w ↦ ∏' k : ℕ, barnesFactor w k) Set.univ := hasProdLocallyUniformlyOn_barnesG_factor
  have hp : HasProd (fun k : ℕ ↦ barnesFactor (z - 1) k)
      (∏' k : ℕ, barnesFactor (z - 1) k) := hlu.hasProd (mem_univ (z - 1))
  have hp_conj : HasProd (fun k : ℕ ↦ starRingEnd ℂ (barnesFactor (z - 1) k))
      (starRingEnd ℂ (∏' k : ℕ, barnesFactor (z - 1) k)) :=
    hp.map (starRingEnd ℂ) Complex.continuous_conj
  simp_rw [← barnesFactor_conj] at hp_conj
  exact hp_conj.tprod_eq

/-- On the real axis, `barnesG` has zero imaginary part. -/
@[simp]
theorem barnesG_ofReal_im (x : ℝ) : (barnesG (x : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using (barnesG_conj (x : ℂ)).symm)

/-- At every real argument `x`, `barnesG x` equals the coercion of its real part. -/
theorem barnesG_ofReal_eq_re (x : ℝ) : barnesG (x : ℂ) = ((barnesG (x : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [barnesG_ofReal_im]

/-- On the positive real axis `x > 0`, `barnesG x` has strictly positive real part. -/
theorem barnesG_ofReal_re_pos {x : ℝ} (hx : 0 < x) : 0 < (barnesG (x : ℂ)).re := by
  by_contra! hle
  have hcont : ContinuousOn (fun t : ℝ ↦ (barnesG (t : ℂ)).re) (Ioi 0) :=
    (Complex.continuous_re.comp (continuous_barnesG.comp continuous_ofReal)).continuousOn
  have h1 : (0 : ℝ) < (barnesG ((1 : ℝ) : ℂ)).re := by simp
  have h0_mem : (0 : ℝ) ∈ (fun t : ℝ ↦ (barnesG (t : ℂ)).re) '' Ioi 0 := by
    have hconn := isPreconnected_Ioi.image _ hcont
    exact hconn.Icc_subset ⟨x, hx, rfl⟩ ⟨1, zero_lt_one, rfl⟩ ⟨hle, h1.le⟩
  rcases h0_mem with ⟨t, ht, ht0⟩
  dsimp only at ht0
  have hne : barnesG (t : ℂ) ≠ 0 := barnesG_ne_zero_of_re_pos (by simpa using ht)
  apply hne
  rw [barnesG_ofReal_eq_re t, ht0, Complex.ofReal_zero]

end TauCeti
