/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Bounds
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# The Lerch transcendent: power series, compact convergence, and periodic zeta comparison

The Lerch transcendent is defined on `‖z‖ < 1` by the principal-logarithm power series
`lerchSeries z s c = ∑' n : ℕ, z ^ n * Complex.exp (-s * Complex.log (n + c))`, with additive-phase
companion `lerchZeta s a c = lerchSeries (exp (2πia)) s c`. Using `exp (-s * log (n + c))` agrees
with `(n + c) ^ (-s)` whenever every `n + c ≠ 0`, while keeping each term entire in `s` and monomial
in `z`. On compact subsets with `‖z‖ < 1` and `c ∈ Complex.slitPlane`, all mixed partial derivatives
in `(z, s, c)` admit uniform summable bounds, giving joint analyticity, the lowering relation
`(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)`, and the raising relation
`∂_c Φ(z, s, c) = -s * Φ(z, s + 1, c)`.

## Main definitions and results

* `TauCeti.lerchSeries`, `TauCeti.lerchZeta`: power-series and additive-phase Lerch series.
* `TauCeti.summable_norm_lerchSeries_term`, `TauCeti.hasSum_lerchSeries`,
  `IsCompact.exists_summable_norm_lerchSeries_term_le`,
  `IsCompact.exists_summable_norm_iteratedDeriv_lerchSeries_term_le`,
  `IsCompact.tendstoUniformlyOn_iteratedDeriv_lerchSeries`: absolute convergence and compact uniform
  convergence of all mixed partial derivatives.
* `TauCeti.lerchSeries_zero_left`, `TauCeti.lerchSeries_zero_middle`,
  `TauCeti.lerchSeries_eq_sum_range_add_pow_mul_add_natCast_right`,
  `TauCeti.lerchSeries_eq_exp_add_mul_add_one_right`, `TauCeti.mul_lerchSeries_add_one_right`:
  initial values and `c`-shift identities.
* `TauCeti.lerchZeta_add_intCast_middle`, `TauCeti.lerchZeta_add_one_middle`,
  `TauCeti.hasSum_lerchZeta`, `TauCeti.lerchZeta_zero_left`,
  `TauCeti.lerchZeta_eq_exp_add_mul_add_one_right`, `TauCeti.analyticOnNhd_lerchZeta`,
  `TauCeti.differentiableOn_lerchZeta`, `TauCeti.hasSum_lerchZeta_of_im_nonneg`: characteristic API
  for `lerchZeta`.
* `TauCeti.hasDerivAt_lerchSeries_left`, `TauCeti.mul_deriv_lerchSeries_left_add_mul`,
  `TauCeti.hasDerivAt_lerchSeries_middle`, `TauCeti.hasDerivAt_lerchSeries_right`,
  `TauCeti.analyticOnNhd_lerchSeries`, `TauCeti.differentiableOn_lerchSeries`: termwise derivatives,
  lowering relation, and joint analyticity in `(s, z, c)`.
* `TauCeti.summable_norm_lerchSeries_term_of_norm_le_one`, `TauCeti.expZeta_eq_mul_lerchSeries`,
  `TauCeti.lerchSeries_one_one_eq_riemannZeta`,
  `TauCeti.lerchSeries_neg_one_one_eq_mul_riemannZeta`: boundary convergence on
  `‖z‖ ≤ 1, 1 < s.re` and comparison with `HurwitzZeta.expZeta` and `riemannZeta`.

## References

* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I–II*, Forum Math. 24 (2012), 1–84.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, (1.1), Theorem 2.3 (2.4), §4 Theorem 4.1, §5 Theorem 5.1 (5.3), §6 Theorem 6.1.
* NIST Digital Library of Mathematical Functions, Chapter 25.14 (*Lerch's Transcendent*).
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology Real

namespace TauCeti

/-- The Lerch transcendent on the open unit disc `‖z‖ < 1`, defined with Mathlib's principal
complex logarithm by `∑' n : ℕ, z ^ n * exp (-s * log (n + c))`. Outside the convergence domain the
value is totalized by `tsum` and carries no regularity assertion. -/
noncomputable def lerchSeries (z s c : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * Complex.exp (-s * Complex.log (n + c))

/-- Defining series expansion of `lerchSeries`. -/
theorem lerchSeries_def (z s c : ℂ) :
    lerchSeries z s c = ∑' n : ℕ, z ^ n * Complex.exp (-s * Complex.log (n + c)) := by rfl

/-- Additive-phase Lerch series `L(s, a, c) = Φ(exp(2πia), s, c)`. -/
noncomputable def lerchZeta (s a c : ℂ) : ℂ :=
  lerchSeries (Complex.exp (2 * Real.pi * I * a)) s c

/-- Defining identity of `lerchZeta` in terms of `lerchSeries`. -/
theorem lerchZeta_def (s a c : ℂ) :
    lerchZeta s a c = lerchSeries (Complex.exp (2 * Real.pi * I * a)) s c := by rfl

/-- When no shift `n + c` vanishes, each `exp (-s * log (n + c))` coincides with the principal
complex power `(n + c) ^ (-s)`. -/
theorem lerchSeries_eq_tsum_cpow (z s : ℂ) {c : ℂ} (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z s c = ∑' n : ℕ, z ^ n * ((n : ℂ) + c) ^ (-s) :=
  tsum_congr fun n => by rw [cpow_def_of_ne_zero (hc n), mul_comm (Complex.log _)]

/-! ### Uniform norm bounds and compact convergence -/

private theorem norm_log_pow_lerchTerm_le_aux {s z c : ℂ} {r S C δ : ℝ} {k n : ℕ}
    (hz : ‖z‖ ≤ r) (hs : ‖s‖ ≤ S) (hc : ‖c‖ ≤ C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hw_lo : δ ≤ ‖(n : ℂ) + c‖) :
    ‖z ^ n * ((-Complex.log (n + c)) ^ k * Complex.exp (-s * Complex.log (n + c)))‖ ≤
      (|Real.log δ| + Real.pi + C + 1) ^ k * Real.exp (S * Real.pi) *
        (Real.exp (-S * Real.log δ) * ((n : ℝ) + 1) ^ k * r ^ n +
          (C + 1) ^ Nat.ceil S * ((n : ℝ) + 1) ^ (k + Nat.ceil S) * r ^ n) := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hC0 : 0 ≤ C := (norm_nonneg c).trans hc
  have hw_hi : ‖(n : ℂ) + c‖ ≤ (n : ℝ) + C + 1 := by
    have := norm_add_le (n : ℂ) c; rw [Complex.norm_natCast] at this; linarith
  have hbase := Complex.norm_log_pow_mul_exp_le hs hδ0 hδ1 hw_lo
    (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + C + 1) hw_hi k
  set L : ℝ := |Real.log δ| + Real.pi + C + 1
  set M : ℕ := Nat.ceil S
  have hL_bound : |Real.log δ| + Real.pi + ((n : ℝ) + C + 1) ≤ L * ((n : ℝ) + 1) := by
    dsimp [L]; nlinarith [Nat.cast_nonneg (α := ℝ) n, abs_nonneg (Real.log δ), Real.pi_pos]
  have hB_bound : ((n : ℝ) + C + 1) ^ S ≤ (C + 1) ^ M * ((n : ℝ) + 1) ^ M := by
    calc ((n : ℝ) + C + 1) ^ S
        ≤ ((n : ℝ) + C + 1) ^ (M : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
            (Nat.le_ceil S)
      _ = ((n : ℝ) + C + 1) ^ M := Real.rpow_natCast _ M
      _ ≤ ((C + 1) * ((n : ℝ) + 1)) ^ M :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) M
      _ = (C + 1) ^ M * ((n : ℝ) + 1) ^ M := mul_pow _ _ M
  rw [norm_mul, norm_pow]
  calc ‖z‖ ^ n * ‖(-Complex.log ((n : ℂ) + c)) ^ k * Complex.exp (-s * Complex.log ((n : ℂ) + c))‖
      ≤ r ^ n * ((L * ((n : ℝ) + 1)) ^ k * Real.exp (S * Real.pi) *
          (Real.exp (-S * Real.log δ) + (C + 1) ^ M * ((n : ℝ) + 1) ^ M)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz n)
          (hbase.trans <| mul_le_mul
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hL_bound k)
              (Real.exp_pos _).le)
            (by linarith) (by positivity) (by positivity))
          (norm_nonneg _) (pow_nonneg hr0 n)
    _ = L ^ k * Real.exp (S * Real.pi) *
          (Real.exp (-S * Real.log δ) * ((n : ℝ) + 1) ^ k * r ^ n +
            (C + 1) ^ M * ((n : ℝ) + 1) ^ (k + M) * r ^ n) := by rw [mul_pow, pow_add]; ring

private theorem exists_summable_norm_log_pow_lerchSeries_term_le {K : Set (ℂ × ℂ × ℂ)}
    (hK : IsCompact K) (hKz : ∀ p ∈ K, ‖p.2.1‖ < 1)
    (hKc : ∀ p ∈ K, ∀ n : ℕ, (n : ℂ) + p.2.2 ≠ 0) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ p ∈ K,
      ‖p.2.1 ^ n * ((-Complex.log (n + p.2.2)) ^ k *
        Complex.exp (-p.1 * Complex.log (n + p.2.2)))‖ ≤ u n := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, summable_zero, by simp⟩
  obtain ⟨p₀, hp₀, hmax_z⟩ := hK.exists_isMaxOn hne
    (continuous_norm.comp (continuous_fst.comp continuous_snd)).continuousOn
  obtain ⟨S, hS⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := (hK.image (continuous_snd.comp continuous_snd)).isBounded.exists_norm_le
  obtain ⟨δ, hδ0, hδ1, hδK⟩ :=
    (hK.image (continuous_snd.comp continuous_snd)).exists_pos_le_norm_natCast_add
      (by rintro _ ⟨p, hp, rfl⟩ n; exact hKc p hp n)
  set r : ℝ := ‖p₀.2.1‖
  have hr : ‖r‖ < 1 := by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hKz p₀ hp₀
  have hsum1 : Summable (fun n : ℕ => Real.exp (-S * Real.log δ) * ((n : ℝ) + 1) ^ k * r ^ n) :=
    ((summable_add_pow_mul_geometric_of_norm_lt_one 1 k hr).mul_left
      (Real.exp (-S * Real.log δ))).congr fun _ => by ring
  have hsum2 : Summable (fun n : ℕ =>
      (C + 1) ^ Nat.ceil S * ((n : ℝ) + 1) ^ (k + Nat.ceil S) * r ^ n) :=
    ((summable_add_pow_mul_geometric_of_norm_lt_one 1 (k + Nat.ceil S) hr).mul_left
      ((C + 1) ^ Nat.ceil S)).congr fun _ => by ring
  exact ⟨_, (hsum1.add hsum2).mul_left
      ((|Real.log δ| + Real.pi + C + 1) ^ k * Real.exp (S * Real.pi)),
    fun n p hp => norm_log_pow_lerchTerm_le_aux (hmax_z hp) (hS p.1 ⟨p, hp, rfl⟩)
      (hC p.2.2 ⟨p, hp, rfl⟩) hδ0 hδ1 (hδK p.2.2 ⟨p, hp, rfl⟩ n)⟩

/-- On any compact subset `K ⊆ ℂ × ℂ × ℂ` (in coordinates `(s, z, c)`) with `‖z‖ < 1` and
`n + c ≠ 0` for all `n : ℕ`, the Lerch series terms are dominated by a single summable sequence. -/
theorem _root_.IsCompact.exists_summable_norm_lerchSeries_term_le {K : Set (ℂ × ℂ × ℂ)}
    (hK : IsCompact K) (hKz : ∀ p ∈ K, ‖p.2.1‖ < 1)
    (hKc : ∀ p ∈ K, ∀ n : ℕ, (n : ℂ) + p.2.2 ≠ 0) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ p ∈ K,
      ‖p.2.1 ^ n * Complex.exp (-p.1 * Complex.log (n + p.2.2))‖ ≤ u n := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le hK hKz hKc 0
  exact ⟨u, hu, fun n p hp => by simpa using hle n p hp⟩

private theorem continuous_log_pow_lerchSeries_term_prod (c : ℂ) (k : ℕ) :
    Continuous (fun x : ℕ × (ℂ × ℂ) =>
      x.2.2 ^ x.1 * ((-Complex.log (x.1 + c)) ^ k *
        Complex.exp (-x.2.1 * Complex.log (x.1 + c)))) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have heq : (fun y : ℕ × (ℂ × ℂ) => y.2.2 ^ y.1) =ᶠ[𝓝 x] fun y => y.2.2 ^ x.1 := by
    filter_upwards [(isOpen_discrete ({x.1} : Set ℕ)).preimage continuous_fst |>.mem_nhds rfl]
      with y hy
    exact congrArg _ (mem_singleton_iff.mp hy)
  have hcL : Continuous (fun y : ℕ × (ℂ × ℂ) => Complex.log ((y.1 : ℂ) + c)) :=
    (continuous_of_discreteTopology (f := fun m : ℕ => Complex.log ((m : ℂ) + c))).comp
      continuous_fst
  exact (ContinuousAt.congr
    ((continuous_snd.comp continuous_snd).pow x.1).continuousAt heq.symm).mul
    (((hcL.neg.pow k).mul (((continuous_fst.comp continuous_snd).neg.mul hcL).cexp)).continuousAt)

private theorem exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKz : ∀ q ∈ K, ‖q.2‖ < 1) (c : ℂ) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ q ∈ K,
      ‖q.2 ^ n * ((-Complex.log (n + c)) ^ k * Complex.exp (-q.1 * Complex.log (n + c)))‖ ≤
        u n := by
  set N : ℕ := Nat.ceil (‖c‖ + 1)
  have hshift_ne : ∀ n : ℕ, (n : ℂ) + (c + N) ≠ 0 := fun n h => by
    have hzero : ((n + N : ℕ) : ℂ) + c = 0 := by push_cast; linear_combination h
    have htri := Complex.sub_norm_le_norm_natCast_add (n + N) c
    rw [hzero, norm_zero] at htri
    linarith [Nat.le_ceil (‖c‖ + 1),
      (by exact_mod_cast Nat.le_add_left N n : (N : ℝ) ≤ ↑(n + N))]
  let emb : ℂ × ℂ → ℂ × ℂ × ℂ := fun q => (q.1, q.2, c + N)
  obtain ⟨u₁, hu₁, hle₁⟩ := exists_summable_norm_log_pow_lerchSeries_term_le
    (hK.image (by fun_prop : Continuous emb)) (by rintro _ ⟨q, hq, rfl⟩; exact hKz q hq)
    (by rintro _ ⟨_, _, rfl⟩ n; exact hshift_ne n) k
  obtain ⟨M₀, hM₀⟩ := (((Finset.finite_toSet (Finset.range N)).isCompact.prod hK).image
    (continuous_log_pow_lerchSeries_term_prod c k)).isBounded.exists_norm_le
  let u : ℕ → ℝ := fun n => if n < N then max M₀ 0 else u₁ (n - N)
  refine ⟨u, (summable_nat_add_iff N).mp (hu₁.congr fun n => by simp [u]), fun n q hq => ?_⟩
  by_cases hn : n < N
  · exact (hM₀ _ ⟨(n, q), ⟨Finset.mem_range.mpr hn, hq⟩, rfl⟩).trans (by simp [u, hn])
  · simp only [u, hn, ↓reduceIte]
    have hadd : (n : ℂ) + c = ((n - N : ℕ) : ℂ) + (c + N) :=
      calc (n : ℂ) + c = ((n - N + N : ℕ) : ℂ) + c := by
            rw [Nat.sub_add_cancel (Nat.le_of_not_lt hn)]
        _ = ((n - N : ℕ) : ℂ) + (c + N) := by push_cast; ring
    have hpow : ‖q.2 ^ n‖ ≤ ‖q.2 ^ (n - N)‖ := by
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hKz q hq).le (Nat.sub_le n N)
    rw [norm_mul, hadd]
    exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
      (by simpa [emb, norm_mul] using hle₁ (n - N) (emb q) ⟨q, hq, rfl⟩)

/-- On the open unit disc `‖z‖ < 1`, the Lerch series converges absolutely for all `s, c : ℂ`. -/
theorem summable_norm_lerchSeries_term {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n * Complex.exp (-s * Complex.log (n + c))‖) := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    (isCompact_singleton (x := (s, z))) (by simp [hz]) c 0
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa using hle n (s, z) rfl) hu

/-- On the open unit disc `‖z‖ < 1`, the Lerch series is summable for all `s, c : ℂ`. -/
theorem summable_lerchSeries_term {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_lerchSeries_term hz s c).of_norm

/-- `HasSum` form of `lerchSeries` on `‖z‖ < 1`. -/
theorem hasSum_lerchSeries {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasSum (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) (lerchSeries z s c) :=
  (summable_lerchSeries_term hz s c).hasSum

/-! ### Initial evaluations and parameter shifts -/

/-- At `z = 0`, only the `n = 0` term survives: `Φ(0, s, c) = exp (-s * log c)`. -/
@[simp]
theorem lerchSeries_zero_left (s c : ℂ) :
    lerchSeries 0 s c = Complex.exp (-s * Complex.log c) := by
  rw [lerchSeries_def, tsum_eq_single 0]
  · simp
  · intro n hn; simp [zero_pow hn]

-- Normalization check `Φ(0, 2, 1) = 1`, distinguishing `Φ(z, s, c)` from `z * Φ(z, s, c)`.
example : lerchSeries 0 2 1 = 1 := by simp

/-- At `s = 0` and `‖z‖ < 1`, the Lerch series reduces to the geometric sum `(1 - z)⁻¹`. -/
theorem lerchSeries_zero_middle {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    lerchSeries z 0 c = (1 - z)⁻¹ := by
  simpa [lerchSeries_def] using tsum_geometric_of_norm_lt_one hz

/-- `N`-step shift identity in `c`, peeling off the first `N` terms of any summable Lerch series. -/
theorem lerchSeries_eq_sum_range_add_pow_mul_add_natCast_right {z s c : ℂ}
    (hs : Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c)))) (N : ℕ) :
    lerchSeries z s c =
      (∑ n ∈ Finset.range N, z ^ n * Complex.exp (-s * Complex.log (n + c))) +
        z ^ N * lerchSeries z s (c + N) := by
  rw [lerchSeries_def, ← hs.sum_add_tsum_nat_add N, lerchSeries_def, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun n => ?_
  have hcast : ((n + N : ℕ) : ℂ) + c = (n : ℂ) + (c + N) := by push_cast; ring
  rw [pow_add, mul_comm (z ^ n) (z ^ N), mul_assoc, hcast]

/-- One-step shift identity in `c`: `Φ(z, s, c) = exp (-s * log c) + z * Φ(z, s, c + 1)`
whenever the Lerch series is summable. -/
theorem lerchSeries_eq_exp_add_mul_add_one_right {z s c : ℂ}
    (hs : Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c)))) :
    lerchSeries z s c = Complex.exp (-s * Complex.log c) + z * lerchSeries z s (c + 1) := by
  simpa using lerchSeries_eq_sum_range_add_pow_mul_add_natCast_right hs 1

/-- Rearranged shift identity `z * Φ(z, s, c + 1) = Φ(z, s, c) - exp (-s * log c)` whenever
the Lerch series is summable. -/
theorem mul_lerchSeries_add_one_right {z s c : ℂ}
    (hs : Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c)))) :
    z * lerchSeries z s (c + 1) = lerchSeries z s c - Complex.exp (-s * Complex.log c) := by
  rw [lerchSeries_eq_exp_add_mul_add_one_right hs, add_sub_cancel_left]

/-- Periodicity of `lerchZeta` in the phase `a`: adding an integer leaves `lerchZeta s a c`
unchanged. -/
@[simp]
theorem lerchZeta_add_intCast_middle (s a c : ℂ) (k : ℤ) :
    lerchZeta s (a + k) c = lerchZeta s a c := by
  have hexp : 2 * (Real.pi : ℂ) * I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * I) := by ring
  rw [lerchZeta_def, lerchZeta_def, mul_add, Complex.exp_add, hexp,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Unit periodicity of `lerchZeta` in the phase `a`: `L(s, a + 1, c) = L(s, a, c)`. -/
@[simp]
theorem lerchZeta_add_one_middle (s a c : ℂ) : lerchZeta s (a + 1) c = lerchZeta s a c := by
  simpa using lerchZeta_add_intCast_middle s a c 1

/-- On the upper half-plane `0 < a.im`, the `lerchZeta` series is summable for all `s, c : ℂ`. -/
theorem summable_lerchZeta_term (s : ℂ) {a : ℂ} (ha : 0 < a.im) (c : ℂ) :
    Summable (fun n : ℕ =>
      Complex.exp (2 * Real.pi * I * n * a) * Complex.exp (-s * Complex.log (n + c))) :=
  (summable_lerchSeries_term (UpperHalfPlane.norm_exp_two_pi_I_mul_lt_one_iff.mpr ha) s c).congr
    fun n => by rw [UpperHalfPlane.exp_two_pi_I_mul_pow]

/-- `HasSum` form of `lerchZeta` on the upper half-plane `0 < a.im`. -/
theorem hasSum_lerchZeta (s : ℂ) {a : ℂ} (ha : 0 < a.im) (c : ℂ) :
    HasSum (fun n : ℕ =>
      Complex.exp (2 * Real.pi * I * n * a) * Complex.exp (-s * Complex.log (n + c)))
      (lerchZeta s a c) := by
  simpa only [lerchZeta_def, UpperHalfPlane.exp_two_pi_I_mul_pow] using
    hasSum_lerchSeries (UpperHalfPlane.norm_exp_two_pi_I_mul_lt_one_iff.mpr ha) s c

/-- At `s = 0` on the upper half-plane `0 < a.im`, `L(0, a, c) = (1 - exp (2πia))⁻¹`. -/
theorem lerchZeta_zero_left {a : ℂ} (ha : 0 < a.im) (c : ℂ) :
    lerchZeta 0 a c = (1 - Complex.exp (2 * Real.pi * I * a))⁻¹ :=
  lerchSeries_zero_middle (UpperHalfPlane.norm_exp_two_pi_I_mul_lt_one_iff.mpr ha) c

/-- One-step shift identity in `c` for `lerchZeta`:
`L(s, a, c) = exp (-s * log c) + exp (2πia) * L(s, a, c + 1)` whenever the series is summable. -/
theorem lerchZeta_eq_exp_add_mul_add_one_right {s a c : ℂ}
    (hs : Summable (fun n : ℕ =>
      Complex.exp (2 * Real.pi * I * n * a) * Complex.exp (-s * Complex.log (n + c)))) :
    lerchZeta s a c =
      Complex.exp (-s * Complex.log c) +
        Complex.exp (2 * Real.pi * I * a) * lerchZeta s a (c + 1) :=
  lerchSeries_eq_exp_add_mul_add_one_right
    (hs.congr fun n => by rw [← UpperHalfPlane.exp_two_pi_I_mul_pow])

/-! ### Termwise derivatives, compact mixed-derivative bounds, and joint analyticity -/

private theorem isOpen_lerchSeriesDomain :
    IsOpen {p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} :=
  (isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
    (Complex.isOpen_slitPlane.preimage (continuous_snd.comp continuous_snd))

private theorem iteratedDeriv_exp_neg_mul (L : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun w : ℂ => Complex.exp (-w * L)) s =
      (-L) ^ k * Complex.exp (-s * L) := by
  have hfun : (fun w : ℂ => Complex.exp (-w * L)) = fun w => Complex.exp (-L * w) := by
    ext w; congr 1; ring
  rw [hfun, congrFun (iteratedDeriv_cexp_const_mul k (-L)) s]
  congr 2; ring

/-- On `‖z‖ < 1`, `w ↦ lerchSeries w s c` has term-by-term complex derivative at `z` for all
`s, c : ℂ`. -/
theorem hasDerivAt_lerchSeries_left {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun w => lerchSeries w s c)
      (∑' n : ℕ, (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) z := by
  set r : ℝ := (‖z‖ + 1) / 2
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hzr : ‖z‖ < r := by dsimp [r]; linarith
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    (isCompact_singleton.prod (isCompact_closedBall (0 : ℂ) r))
    (fun q hq => (mem_closedBall_zero_iff.mp hq.2).trans_lt hr_lt) c 0
  let F : ℕ → ℂ → ℂ := fun n w => w ^ n * Complex.exp (-s * Complex.log (n + c))
  have hd := Complex.hasDerivAt_tsum_of_summable_norm (F := F) hu (fun _ => by fun_prop) isOpen_ball
    (fun n w hw => by simpa [F] using hle n (s, w) ⟨rfl, ball_subset_closedBall hw⟩)
    (mem_ball_zero_iff.mpr hzr)
  simpa [F, lerchSeries_def] using hd

/-- Term-by-term formula for `deriv (fun w => lerchSeries w s c) z` on `‖z‖ < 1`. -/
theorem deriv_lerchSeries_left {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    deriv (fun w => lerchSeries w s c) z =
      ∑' n : ℕ, (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)) :=
  (hasDerivAt_lerchSeries_left hz s c).deriv

/-- For all `s, c : ℂ`, `w ↦ lerchSeries w s c` is holomorphic on the open unit disc. -/
theorem differentiableOn_lerchSeries_left (s c : ℂ) :
    DifferentiableOn ℂ (fun w => lerchSeries w s c) (ball 0 1) := fun _ hz =>
  (hasDerivAt_lerchSeries_left (mem_ball_zero_iff.mp hz) s c).differentiableAt
    |>.differentiableWithinAt

/-- Lowering differential relation `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)` on `‖z‖ < 1` whenever
`(n : ℂ) + c ≠ 0` for every `n : ℕ`. -/
theorem mul_deriv_lerchSeries_left_add_mul {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    z * deriv (fun w => lerchSeries w s c) z + c * lerchSeries z s c =
      lerchSeries z (s - 1) c := by
  have hterm (n : ℕ) :
      z * ((n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) =
        z ^ n * Complex.exp (-(s - 1) * Complex.log (n + c)) -
          c * (z ^ n * Complex.exp (-s * Complex.log (n + c))) := by
    have hzn : z * ((n : ℂ) * z ^ (n - 1)) = (n : ℂ) * z ^ n := by
      rcases n with _ | k <;> simp [pow_succ', mul_left_comm]
    have hexp : Complex.exp (-(s - 1) * Complex.log (n + c)) =
        ((n : ℂ) + c) * Complex.exp (-s * Complex.log (n + c)) := by
      have harg : -(s - 1) * Complex.log (n + c) =
          Complex.log (n + c) + (-s * Complex.log (n + c)) := by ring
      rw [harg, Complex.exp_add, Complex.exp_log (hc n)]
    rw [← mul_assoc, hzn, hexp]; ring
  have hs1 := summable_lerchSeries_term hz (s - 1) c
  have hs2 := (summable_lerchSeries_term hz s c).mul_left c
  have hfun : (fun n : ℕ => z * ((n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)))) =
      fun n : ℕ => z ^ n * Complex.exp (-(s - 1) * Complex.log (n + c)) -
        c * (z ^ n * Complex.exp (-s * Complex.log (n + c))) := funext hterm
  rw [deriv_lerchSeries_left hz s c, ← tsum_mul_left, lerchSeries_def z s c, ← tsum_mul_left, hfun,
    ← (hs1.sub hs2).tsum_add hs2]
  simp [lerchSeries_def]

/-- On `‖z‖ < 1`, `w ↦ lerchSeries z w c` is entire and may be differentiated term-by-term in `s`
for all `c : ℂ`. -/
theorem hasDerivAt_lerchSeries_middle {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun w => lerchSeries z w c)
      (∑' n : ℕ, -Complex.log (n + c) * z ^ n * Complex.exp (-s * Complex.log (n + c))) s := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    ((isCompact_closedBall s 1).prod isCompact_singleton)
    (fun q hq => by rw [hq.2]; exact hz) c 0
  let F : ℕ → ℂ → ℂ := fun n w => z ^ n * Complex.exp (-w * Complex.log (n + c))
  have hd := Complex.hasDerivAt_tsum_of_summable_norm (F := F) hu (fun _ => by fun_prop) isOpen_ball
    (fun n w hw => by simpa [F] using hle n (w, z) ⟨ball_subset_closedBall hw, rfl⟩)
    (mem_ball_self one_pos)
  have hterm : (fun n => deriv (F n) s) =
      fun n : ℕ => -Complex.log (n + c) * z ^ n * Complex.exp (-s * Complex.log (n + c)) := by
    ext n
    rw [((((hasDerivAt_neg s).mul_const (Complex.log (n + c))).cexp).const_mul (z ^ n)).deriv]
    ring
  rw [hterm] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun w => (lerchSeries_def z w c).symm)

/-- Termwise `s`-derivative of `lerchSeries` on `‖z‖ < 1`. -/
theorem deriv_lerchSeries_middle {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    deriv (fun w => lerchSeries z w c) s =
      ∑' n : ℕ, -Complex.log (n + c) * z ^ n * Complex.exp (-s * Complex.log (n + c)) :=
  (hasDerivAt_lerchSeries_middle hz s c).deriv

/-- For `‖z‖ < 1` and any `c : ℂ`, `s ↦ lerchSeries z s c` is entire on `ℂ`. -/
theorem differentiable_lerchSeries_middle {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    Differentiable ℂ (fun s => lerchSeries z s c) := fun s =>
  (hasDerivAt_lerchSeries_middle hz s c).differentiableAt

/-- Raising relation in `c`: for `‖z‖ < 1` and `c ∈ Complex.slitPlane`,
`∂_c Φ(z, s, c) = -s * Φ(z, s + 1, c)`. -/
theorem hasDerivAt_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    HasDerivAt (fun w => lerchSeries z s w) (-s * lerchSeries z (s + 1) c) c := by
  obtain ⟨δ, hδ, hcb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Complex.isOpen_slitPlane.mem_nhds hc)
  let K : Set (ℂ × ℂ × ℂ) :=
    ({s} : Set ℂ) ×ˢ (({z} : Set ℂ) ×ˢ closedBall c δ)
  have hK : IsCompact K :=
    isCompact_singleton.prod (isCompact_singleton.prod (isCompact_closedBall c δ))
  obtain ⟨u, hu, hle⟩ := hK.exists_summable_norm_lerchSeries_term_le
    (fun p hp => by rw [hp.2.1]; exact hz)
    (fun p hp n => slitPlane_ne_zero (natCast_add_mem_slitPlane_iff.mpr (hcb hp.2.2) n))
  let F : ℕ → ℂ → ℂ := fun n w => z ^ n * Complex.exp (-s * Complex.log (n + w))
  have hFo : ∀ n, DifferentiableOn ℂ (F n) (ball c δ) := fun n w hw =>
    (((((differentiableAt_id.const_add (n : ℂ)).clog
      (natCast_add_mem_slitPlane_iff.mpr (hcb (ball_subset_closedBall hw)) n)).const_mul (-s)).cexp)
      |>.const_mul (z ^ n)).differentiableWithinAt
  have hd := Complex.hasDerivAt_tsum_of_summable_norm hu hFo isOpen_ball
    (fun n w hw => hle n (s, z, w) ⟨rfl, rfl, ball_subset_closedBall hw⟩) (mem_ball_self hδ)
  have hterm : (fun n => deriv (F n) c) =
      fun n : ℕ => -s * (z ^ n * Complex.exp (-(s + 1) * Complex.log (n + c))) := by
    ext n
    have hslit : (n : ℂ) + c ∈ Complex.slitPlane := natCast_add_mem_slitPlane_iff.mpr hc n
    have hdF : HasDerivAt (F n)
        (z ^ n * (Complex.exp (-s * Complex.log (n + c)) * (-s * (1 / ((n : ℂ) + c))))) c :=
      (((((hasDerivAt_id c).const_add (n : ℂ)).clog hslit).const_mul (-s)).cexp).const_mul (z ^ n)
    have hexp : -(s + 1) * Complex.log (n + c) =
        -s * Complex.log (n + c) - Complex.log (n + c) := by ring
    rw [hdF.deriv, hexp, Complex.exp_sub, Complex.exp_log (slitPlane_ne_zero hslit)]
    simp only [div_eq_mul_inv]; ring
  rw [hterm, tsum_mul_left, ← lerchSeries_def] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun w => (lerchSeries_def z s w).symm)

/-- Derivative form of the raising relation `∂_c Φ(z, s, c) = -s * Φ(z, s + 1, c)`. -/
theorem deriv_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    deriv (fun w => lerchSeries z s w) c = -s * lerchSeries z (s + 1) c :=
  (hasDerivAt_lerchSeries_right hz s hc).deriv

/-- For `‖z‖ < 1` and any `s : ℂ`, `c ↦ lerchSeries z s c` is holomorphic on `Complex.slitPlane`. -/
theorem differentiableOn_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) :
    DifferentiableOn ℂ (fun w => lerchSeries z s w) Complex.slitPlane := fun _ hc =>
  (hasDerivAt_lerchSeries_right hz s hc).differentiableAt.differentiableWithinAt

/-- `lerchSeries` is jointly analytic in `(s, z, c)` on
`{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchSeries :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2)
      {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} := by
  intro p₀ hp₀
  obtain ⟨δ, hδ, hcb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_lerchSeriesDomain.mem_nhds hp₀)
  obtain ⟨u, hu, hle⟩ := (isCompact_closedBall p₀ δ).exists_summable_norm_lerchSeries_term_le
    (fun q hq => (hcb hq).1)
    (fun q hq n => slitPlane_ne_zero (natCast_add_mem_slitPlane_iff.mpr (hcb hq).2 n))
  have hunif : TendstoUniformlyOn
      (fun N (p : ℂ × ℂ × ℂ) =>
        ∑ n ∈ Finset.range N, p.2.1 ^ n * Complex.exp (-p.1 * Complex.log (n + p.2.2)))
      (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2) atTop (ball p₀ δ) :=
    (tendstoUniformlyOn_tsum_nat hu fun n q hq => hle n q (ball_subset_closedBall hq)).congr_right
      fun q _ => (lerchSeries_def q.2.1 q.1 q.2.2).symm
  have hdiff_sum : ∀ N : ℕ, DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ =>
        ∑ n ∈ Finset.range N, p.2.1 ^ n * Complex.exp (-p.1 * Complex.log (n + p.2.2)))
      (ball p₀ δ) := fun N q hq => by
    refine DifferentiableWithinAt.fun_sum fun n _ => ?_
    have hslit := natCast_add_mem_slitPlane_iff.mpr (hcb (ball_subset_closedBall hq)).2 n
    exact (((differentiableAt_fst.comp q differentiableAt_snd).pow n).mul
      ((differentiableAt_fst.neg.mul
        (((differentiableAt_const (n : ℂ)).add
          (differentiableAt_snd.comp q differentiableAt_snd)).clog hslit)).cexp)
      ).differentiableWithinAt
  have hdiff := hunif.differentiableOn (Eventually.of_forall hdiff_sum) isOpen_ball
  exact hdiff.analyticOnNhd_of_finiteDimensional isOpen_ball p₀ (mem_ball_self hδ)

/-- `lerchSeries` is jointly complex differentiable in `(s, z, c)` on
`{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem differentiableOn_lerchSeries :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2)
      {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} :=
  analyticOnNhd_lerchSeries.differentiableOn

/-- `lerchZeta` is jointly analytic in `(s, a, c)` on the upper half-plane in `a` and slit plane in
`c`: `{p : ℂ × ℂ × ℂ | 0 < p.2.1.im ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchZeta :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => lerchZeta p.1 p.2.1 p.2.2)
      {p | 0 < p.2.1.im ∧ p.2.2 ∈ Complex.slitPlane} := by
  intro p hp
  let φ : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun q => (q.1, Complex.exp (2 * Real.pi * I * q.2.1), q.2.2)
  have hφ : AnalyticAt ℂ φ p :=
    analyticAt_fst.prod (((analyticAt_const.mul (analyticAt_fst.comp analyticAt_snd)).cexp).prod
      (analyticAt_snd.comp analyticAt_snd))
  have hmem : φ p ∈ {q : ℂ × ℂ × ℂ | ‖q.2.1‖ < 1 ∧ q.2.2 ∈ Complex.slitPlane} :=
    ⟨UpperHalfPlane.norm_exp_two_pi_I_mul_lt_one_iff.mpr hp.1, hp.2⟩
  exact ((analyticOnNhd_lerchSeries (φ p) hmem).comp hφ).congr
    (Eventually.of_forall fun q => (lerchZeta_def q.1 q.2.1 q.2.2).symm)

/-- `lerchZeta` is jointly complex differentiable in `(s, a, c)` on
`{p : ℂ × ℂ × ℂ | 0 < p.2.1.im ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem differentiableOn_lerchZeta :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => lerchZeta p.1 p.2.1 p.2.2)
      {p | 0 < p.2.1.im ∧ p.2.2 ∈ Complex.slitPlane} :=
  analyticOnNhd_lerchZeta.differentiableOn

private theorem iteratedDeriv_lerchSeries_term_eq (n dz ds dc : ℕ) (p : ℂ × ℂ × ℂ) :
    iteratedDeriv dc (fun c =>
      iteratedDeriv dz (fun z =>
        iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
        p.2.1) p.2.2 =
      iteratedDeriv dz (fun z : ℂ =>
        z ^ n * iteratedDeriv dc (fun c : ℂ => (-Complex.log (n + c)) ^ ds *
          Complex.exp (-p.1 * Complex.log (n + c))) p.2.2) p.2.1 := by
  let g : ℂ → ℂ := fun c => (-Complex.log (n + c)) ^ ds * Complex.exp (-p.1 * Complex.log (n + c))
  have hs_eval (z c : ℂ) :
      iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1 =
        z ^ n * g c := by rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]
  have hz_pull (a : ℂ) : iteratedDeriv dz (fun z : ℂ => z ^ n * a) p.2.1 =
      iteratedDeriv dz (fun z : ℂ => z ^ n) p.2.1 * a := by
    rw [iteratedDeriv_mul_const_field]
  simp_rw [hs_eval, hz_pull (g _), iteratedDeriv_const_mul_field]
  exact (hz_pull (iteratedDeriv dc g p.2.2)).symm

private theorem norm_mul_iteratedDeriv_right_lerchSeries_term_le (n ds dc : ℕ) {s z' c₀ : ℂ}
    {R B : ℝ} (hR : 0 < R) (hcs : ∀ c' ∈ closedBall c₀ R, c' ∈ Complex.slitPlane)
    (hB : ∀ c' ∈ sphere c₀ R,
      ‖z' ^ n * ((-Complex.log (n + c')) ^ ds * Complex.exp (-s * Complex.log (n + c')))‖ ≤ B) :
    ‖z' ^ n * iteratedDeriv dc (fun c => (-Complex.log (n + c)) ^ ds *
      Complex.exp (-s * Complex.log (n + c))) c₀‖ ≤ dc.factorial * B / R ^ dc := by
  let g : ℂ → ℂ := fun c => (-Complex.log (n + c)) ^ ds * Complex.exp (-s * Complex.log (n + c))
  have hg_diff : DifferentiableOn ℂ (fun c' => z' ^ n * g c') (closedBall c₀ R) := fun c' hc' => by
    have hlog := (differentiableAt_id.const_add (n : ℂ)).clog
      (natCast_add_mem_slitPlane_iff.mpr (hcs c' hc') n)
    exact (((hlog.neg.pow ds).mul ((hlog.const_mul (-s)).cexp)).const_mul
      (z' ^ n)).differentiableWithinAt
  rw [← iteratedDeriv_const_mul_field (z' ^ n) g]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le dc hR
    ⟨hg_diff.mono ball_subset_closedBall, hg_diff.continuousOn.mono closure_ball_subset_closedBall⟩
    hB

/-- On any compact subset `K` of `{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`
(in coordinates `(s, z, c)`), every fixed mixed iterated partial derivative of order `(dz, ds, dc)`
of the Lerch series terms has a single summable norm bound uniformly on `K`. -/
theorem _root_.IsCompact.exists_summable_norm_iteratedDeriv_lerchSeries_term_le
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hKU : K ⊆ {p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane})
    (dz ds dc : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ p ∈ K,
      ‖iteratedDeriv dc (fun c =>
          iteratedDeriv dz (fun z =>
            iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
            p.2.1) p.2.2‖ ≤ u n := by
  obtain ⟨δ, hδ, hK'U⟩ := hK.exists_cthickening_subset_open isOpen_lerchSeriesDomain hKU
  set R : ℝ := δ / 2 with hR_def
  have hR : 0 < R := half_pos hδ
  have hmem_K' : ∀ p ∈ K, ∀ z' ∈ closedBall p.2.1 R, ∀ c' ∈ closedBall p.2.2 R,
      (p.1, z', c') ∈ cthickening δ K := fun p hp z' hz' c' hc' => by
    refine mem_cthickening_of_dist_le (p.1, z', c') p δ K hp ?_
    have hRδ : R ≤ δ := by linarith [hR_def, hδ]
    simp only [Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨hδ.le, (mem_closedBall.mp hz').trans hRδ, (mem_closedBall.mp hc').trans hRδ⟩
  obtain ⟨v, hv, hv_le⟩ := exists_summable_norm_log_pow_lerchSeries_term_le hK.cthickening
    (fun q hq => (hK'U hq).1)
    (fun q hq n => slitPlane_ne_zero (natCast_add_mem_slitPlane_iff.mpr (hK'U hq).2 n)) ds
  refine ⟨fun n => (dz.factorial / R ^ dz) * (dc.factorial / R ^ dc) * v n,
    hv.mul_left _, fun n p hp => ?_⟩
  rw [iteratedDeriv_lerchSeries_term_eq]
  let W : ℂ := iteratedDeriv dc (fun c => (-Complex.log (n + c)) ^ ds *
    Complex.exp (-p.1 * Complex.log (n + c))) p.2.2
  have hc_bound : ∀ z' ∈ sphere p.2.1 R, ‖z' ^ n * W‖ ≤ dc.factorial * v n / R ^ dc :=
    fun z' hz' => norm_mul_iteratedDeriv_right_lerchSeries_term_le n ds dc hR
      (fun c' hc' => (hK'U (hmem_K' p hp z' (sphere_subset_closedBall hz') c' hc')).2)
      (fun c' hc' => hv_le n (p.1, z', c')
        (hmem_K' p hp z' (sphere_subset_closedBall hz') c' (sphere_subset_closedBall hc')))
  calc ‖iteratedDeriv dz (fun z' : ℂ => z' ^ n * W) p.2.1‖
      ≤ dz.factorial * (dc.factorial * v n / R ^ dc) / R ^ dz :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le dz hR
          (by fun_prop : Differentiable ℂ (fun z' : ℂ => z' ^ n * W)).diffContOnCl hc_bound
    _ = (dz.factorial / R ^ dz) * (dc.factorial / R ^ dc) * v n := by ring

private theorem iteratedDeriv_lerchSeries_middle_left_eq_tsum {s₀ z₀ : ℂ} (hz : ‖z₀‖ < 1)
    (c : ℂ) (dz ds : ℕ) :
    iteratedDeriv dz (fun z => iteratedDeriv ds (fun s => lerchSeries z s c) s₀) z₀ =
      ∑' n : ℕ, iteratedDeriv dz (fun z =>
        iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) s₀) z₀ := by
  have hs_step : ∀ {z : ℂ}, ‖z‖ < 1 →
      iteratedDeriv ds (fun s => lerchSeries z s c) s₀ =
        ∑' n : ℕ, iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) s₀ :=
    fun {z} hz' => by
      obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
        ((isCompact_closedBall s₀ 1).prod isCompact_singleton)
        (fun q hq => by rw [hq.2]; exact hz') c 0
      simp_rw [lerchSeries_def]
      exact (Complex.hasSum_iteratedDeriv_of_summable_norm hu (fun _ => by fun_prop) isOpen_ball
        (fun n w hw => by simpa using hle n (w, z) ⟨ball_subset_closedBall hw, rfl⟩)
        ds (mem_ball_self one_pos)).tsum_eq.symm
  set r : ℝ := (‖z₀‖ + 1) / 2
  have hzr : ‖z₀‖ < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have heq : EqOn (fun z => iteratedDeriv ds (fun s => lerchSeries z s c) s₀)
      (fun z => ∑' n : ℕ,
        iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) s₀)
      (ball 0 r) := fun _ hz' => hs_step ((mem_ball_zero_iff.mp hz').trans hr1)
  rw [(heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzr))).iteratedDeriv_eq]
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    (isCompact_singleton.prod (isCompact_closedBall (0 : ℂ) r))
    (fun q hq => (mem_closedBall_zero_iff.mp hq.2).trans_lt hr1) c ds
  refine (Complex.hasSum_iteratedDeriv_of_summable_norm hu (fun n => ?_) isOpen_ball
    (fun n z' hz' => ?_) dz (mem_ball_zero_iff.mpr hzr)).tsum_eq.symm
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]; fun_prop
  · rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]
    exact hle n (s₀, z') ⟨rfl, ball_subset_closedBall hz'⟩

/-- At every `p` with `‖p.2.1‖ < 1` and `p.2.2 ∈ Complex.slitPlane`, the mixed `(dz, ds, dc)`
iterated derivative of `lerchSeries` equals the term-by-term sum of the mixed derivatives. -/
theorem iteratedDeriv_lerchSeries_eq_tsum {p : ℂ × ℂ × ℂ} (hz : ‖p.2.1‖ < 1)
    (hc : p.2.2 ∈ Complex.slitPlane) (dz ds dc : ℕ) :
    iteratedDeriv dc (fun c =>
      iteratedDeriv dz (fun z =>
        iteratedDeriv ds (fun s => lerchSeries z s c) p.1) p.2.1) p.2.2 =
      ∑' n : ℕ, iteratedDeriv dc (fun c =>
        iteratedDeriv dz (fun z =>
          iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
          p.2.1) p.2.2 := by
  obtain ⟨δ, hδ, hcb⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (Complex.isOpen_slitPlane.mem_nhds hc)
  simp_rw [iteratedDeriv_lerchSeries_middle_left_eq_tsum hz _ dz ds]
  obtain ⟨u, hu, hle⟩ :=
    (isCompact_singleton.prod
      (isCompact_singleton.prod
        (isCompact_closedBall p.2.2 δ))).exists_summable_norm_iteratedDeriv_lerchSeries_term_le
      (fun q hq => ⟨by rw [hq.2.1]; exact hz, hcb hq.2.2⟩) dz ds 0
  refine (Complex.hasSum_iteratedDeriv_of_summable_norm hu (fun n c' hc' => ?_) isOpen_ball
    (fun n c' hc' => ?_) dc (mem_ball_self hδ)).tsum_eq.symm
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul,
      iteratedDeriv_mul_const_field]
    have hlog := (differentiableAt_id.const_add (n : ℂ)).clog
      (natCast_add_mem_slitPlane_iff.mpr (hcb (ball_subset_closedBall hc')) n)
    exact (((hlog.neg.pow ds).mul ((hlog.const_mul (-p.1)).cexp)).const_mul
      _).differentiableWithinAt
  · simpa using hle n (p.1, p.2.1, c') ⟨rfl, rfl, ball_subset_closedBall hc'⟩

/-- Partial sums of every mixed `(dz, ds, dc)` partial derivative of `lerchSeries` converge
uniformly on every compact subset of `{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem _root_.IsCompact.tendstoUniformlyOn_iteratedDeriv_lerchSeries {K : Set (ℂ × ℂ × ℂ)}
    (hK : IsCompact K)
    (hKU : K ⊆ {p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}) (dz ds dc : ℕ) :
    TendstoUniformlyOn
      (fun N p => ∑ n ∈ Finset.range N,
        iteratedDeriv dc (fun c =>
          iteratedDeriv dz (fun z =>
            iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
            p.2.1) p.2.2)
      (fun p => iteratedDeriv dc (fun c =>
        iteratedDeriv dz (fun z =>
           iteratedDeriv ds (fun s => lerchSeries z s c) p.1) p.2.1) p.2.2)
      atTop K := by
  obtain ⟨u, hu, hle⟩ := hK.exists_summable_norm_iteratedDeriv_lerchSeries_term_le hKU dz ds dc
  exact (tendstoUniformlyOn_tsum_nat hu hle).congr_right fun p hp =>
    (iteratedDeriv_lerchSeries_eq_tsum (hKU hp).1 (hKU hp).2 dz ds dc).symm

/-! ### Boundary convergence on `‖z‖ ≤ 1, 1 < s.re` and comparison with `expZeta` -/

/-- On the closed unit disc `‖z‖ ≤ 1` with `1 < s.re`, the Lerch series converges absolutely for
every `c : ℂ`. -/
theorem summable_norm_lerchSeries_term_of_norm_le_one {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re)
    (c : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n * Complex.exp (-s * Complex.log (n + c))‖) := by
  set N : ℕ := Nat.ceil (2 * ‖c‖ + 1)
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (((summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))).mul_left
      (Real.exp (|s.im| * Real.pi) * (2 : ℝ) ^ s.re))
  set m : ℕ := n + N
  have hmN : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_add_left N n
  have hNc : 2 * ‖c‖ + 1 ≤ (N : ℝ) := Nat.le_ceil _
  have hm_pos : 0 < (m : ℝ) := by linarith [norm_nonneg c]
  have hw_lo : (m : ℝ) / 2 ≤ ‖(m : ℂ) + c‖ := by
    linarith [Complex.sub_norm_le_norm_natCast_add m c]
  have hre : (-s * Complex.log ((m : ℂ) + c)).re ≤
      |s.im| * Real.pi - s.re * Real.log ((m : ℝ) / 2) := by
    have him : s.im * ((m : ℂ) + c).arg ≤ |s.im| * Real.pi :=
      (le_abs_self _).trans <| by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_arg_le_pi _) (abs_nonneg _)
    simp only [mul_re, neg_re, neg_im, Complex.log_re, Complex.log_im]
    nlinarith [hs, Real.log_le_log (half_pos hm_pos) hw_lo]
  have hexp_eq : Real.exp (|s.im| * Real.pi - s.re * Real.log ((m : ℝ) / 2)) =
      Real.exp (|s.im| * Real.pi) * (2 : ℝ) ^ s.re * (m : ℝ) ^ (-s.re) := by
    have harg : -(s.re * (Real.log m - Real.log 2)) = Real.log 2 * s.re + Real.log m * (-s.re) :=
      by ring
    rw [sub_eq_add_neg, Real.exp_add, Real.log_div hm_pos.ne' two_ne_zero, harg,
      Real.exp_add, ← Real.rpow_def_of_pos two_pos, ← Real.rpow_def_of_pos hm_pos]
    ring
  rw [norm_mul, norm_pow, Complex.norm_exp]
  exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hz) (Real.exp_le_exp.mpr hre)
    (Real.exp_pos _).le zero_le_one).trans_eq (by rw [one_mul, hexp_eq])

/-- Summability of the Lerch series on `‖z‖ ≤ 1` when `1 < s.re`. -/
theorem summable_lerchSeries_term_of_norm_le_one {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re)
    (c : ℂ) :
    Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_lerchSeries_term_of_norm_le_one hz hs c).of_norm

/-- `HasSum` form of `lerchSeries` on the closed unit disc `‖z‖ ≤ 1` when `1 < s.re`. -/
theorem hasSum_lerchSeries_of_norm_le_one {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re) (c : ℂ) :
    HasSum (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) (lerchSeries z s c) :=
  (summable_lerchSeries_term_of_norm_le_one hz hs c).hasSum

/-- Summability of the `lerchZeta` series on `0 ≤ a.im` (including real `a`) when `1 < s.re`. -/
theorem summable_lerchZeta_term_of_im_nonneg {s a : ℂ} (hs : 1 < s.re) (ha : 0 ≤ a.im) (c : ℂ) :
    Summable (fun n : ℕ =>
      Complex.exp (2 * Real.pi * I * n * a) * Complex.exp (-s * Complex.log (n + c))) :=
  (summable_lerchSeries_term_of_norm_le_one
    ((UpperHalfPlane.norm_exp_two_pi_I_mul_le ha).trans_eq (by simp)) hs c).congr
    fun n => by rw [UpperHalfPlane.exp_two_pi_I_mul_pow]

/-- `HasSum` form of `lerchZeta` on `0 ≤ a.im` (including real `a`) when `1 < s.re`. -/
theorem hasSum_lerchZeta_of_im_nonneg {s a : ℂ} (hs : 1 < s.re) (ha : 0 ≤ a.im) (c : ℂ) :
    HasSum (fun n : ℕ =>
      Complex.exp (2 * Real.pi * I * n * a) * Complex.exp (-s * Complex.log (n + c)))
      (lerchZeta s a c) := by
  simpa only [lerchZeta_def, UpperHalfPlane.exp_two_pi_I_mul_pow] using
    hasSum_lerchSeries_of_norm_le_one
      ((UpperHalfPlane.norm_exp_two_pi_I_mul_le ha).trans_eq (by simp)) hs c

/-- On `1 < s.re`, Mathlib's periodic zeta `HurwitzZeta.expZeta a s` differs from the `c = 1`
boundary Lerch series at `z = exp (2πia)` by the prefactor `exp (2πia)`. -/
theorem expZeta_eq_mul_lerchSeries (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.expZeta a s =
      Complex.exp (2 * Real.pi * I * a) * lerchSeries (Complex.exp (2 * Real.pi * I * a)) s 1 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp only [zero_re] at hs; linarith
  have hsum := HurwitzZeta.hasSum_expZeta_of_one_lt_re a hs
  rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, Complex.zero_cpow hs0, div_zero, zero_add]
  rw [lerchSeries_def, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hden : (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ = Complex.exp (-s * Complex.log ((n : ℂ) + 1)) := by
    rw [cpow_def_of_ne_zero hn1, ← Complex.exp_neg]
    simp only [Nat.cast_add, Nat.cast_one, neg_mul, mul_comm (Complex.log _)]
  have hphase : Complex.exp (2 * Real.pi * I * a * ((n + 1 : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * I * a) * Complex.exp (2 * Real.pi * I * a) ^ n := by
    rw [mul_right_comm _ (a : ℂ), ← UpperHalfPlane.exp_two_pi_I_mul_pow, pow_succ']
  rw [div_eq_mul_inv, hden, hphase, mul_assoc]

/-- Equivalent form in terms of `lerchZeta`: `expZeta a s = exp (2πia) * lerchZeta s a 1` for
`a : ℝ` and `1 < s.re`. -/
theorem expZeta_eq_mul_lerchZeta (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.expZeta a s = Complex.exp (2 * Real.pi * I * a) * lerchZeta s a 1 :=
  expZeta_eq_mul_lerchSeries a hs

/-- At `z = 1` and `c = 1`, `lerchSeries 1 s 1 = riemannZeta s` for `1 < s.re`. -/
theorem lerchSeries_one_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries 1 s 1 = riemannZeta s := by
  simpa [HurwitzZeta.expZeta_zero] using (expZeta_eq_mul_lerchSeries 0 hs).symm

/-- At `z = -1` and `c = 1`, `lerchSeries (-1) s 1 = (1 - 2 ^ (1 - s)) * riemannZeta s` for
`1 < s.re`. -/
theorem lerchSeries_neg_one_one_eq_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries (-1) s 1 = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [← LSeries_neg_one_pow_add_one_eq_mul_riemannZeta hs, LSeries]
  have hterm (n : ℕ) :
      LSeries.term (fun k => (-1 : ℂ) ^ (k + 1)) s (n + 1) =
        (-1 : ℂ) ^ n * Complex.exp (-s * Complex.log (n + 1)) := by
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), div_eq_mul_inv, cpow_def_of_ne_zero hn1,
      ← Complex.exp_neg]
    congr 1
    · rw [pow_succ, pow_succ]; ring
    · congr 1; push_cast; ring
  have hsum : Summable (LSeries.term (fun k => (-1 : ℂ) ^ (k + 1)) s) :=
    (summable_nat_add_iff 1).mp <|
      (summable_lerchSeries_term_of_norm_le_one (z := -1) (by simp) hs 1).congr
        fun n => (hterm n).symm
  rw [hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add, lerchSeries_def]
  exact tsum_congr fun n => (hterm n).symm

-- Alternating Basel check `lerchSeries (-1) 2 1 = π ^ 2 / 12`.
example : lerchSeries (-1) 2 1 = (Real.pi : ℂ) ^ 2 / 12 := by
  have hsub : (1 : ℂ) - 2 = (-1 : ℤ) := by norm_num
  rw [lerchSeries_neg_one_one_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re), riemannZeta_two,
    hsub, cpow_intCast, zpow_neg_one]
  ring

-- Sign-distinguishing check against `HurwitzZeta.expZeta`: at `a = 1 / 2` and `s = 2`,
-- `expZeta (1 / 2) 2 = -π ^ 2 / 12`, opposite in sign to `lerchSeries (-1) 2 1 = π ^ 2 / 12` due to
-- the prefactor `exp (2πi · (1 / 2)) = -1`.
example : HurwitzZeta.expZeta ((1 / 2 : ℝ) : UnitAddCircle) 2 = -(Real.pi : ℂ) ^ 2 / 12 := by
  have harg : 2 * (Real.pi : ℂ) * I * ((1 / 2 : ℝ) : ℂ) = Real.pi * I := by push_cast; ring
  have hsub : (1 : ℂ) - 2 = (-1 : ℤ) := by norm_num
  rw [expZeta_eq_mul_lerchSeries (1 / 2 : ℝ) (by norm_num : 1 < (2 : ℂ).re), harg,
    Complex.exp_pi_mul_I, lerchSeries_neg_one_one_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re),
    riemannZeta_two, hsub, cpow_intCast, zpow_neg_one]
  ring

end TauCeti
