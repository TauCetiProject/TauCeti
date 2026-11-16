/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.Analysis.Normed.Module.Normalize.Lipschitz
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Norming mixed norms of `L²`-valued functions

Let `Φ : β → L²(X, μ)` be a family of square integrable functions, for instance the orbit
`t ↦ U(t) f` of a unitary group. Its mixed norm `L^q_b L^r_x` is

`‖Φ‖_{L^q L^r} = ‖b ↦ ‖Φ b‖_{L^r(μ)}‖_{L^q(ρ)}`,

which is meaningful because `b ↦ ‖Φ b‖_{L^r(μ)}` is measurable
(`MeasureTheory.AEStronglyMeasurable.aemeasurable_eLpNorm_Lp`). For Hölder conjugate pairs
`(q, q')` and `(r, r')`, Hölder's inequality in `x` and then in `b` bounds the pairings
`∫ ⟪Φ b, G b⟫ dρ` by `‖Φ‖_{L^q L^r} ‖G‖_{L^{q'} L^{r'}}`. This file proves the converse bound:
if `|∫ ⟪Φ b, G b⟫ dρ| ≤ M ‖G‖_{L^{q'} L^{r'}}` for every integrable `G : β → L²(X, μ)` for which
the pairing is integrable, then `‖Φ‖_{L^q L^r} ≤ M`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`), for
`1 ≤ q < ∞`, `2 ≤ r < ∞` and a σ-finite measure `ρ`. Membership of `Φ` in `L^q L^r` is not assumed;
it follows when `M < ∞`.

This turns estimates proved in weak form, by testing against `L²`-valued functions, into mixed-norm
estimates. The typical application is to Strichartz estimates, where the `TT*` argument bounds the
pairings `∫ ⟪U(t) f, G(t)⟫ dt` for `L²`-valued `G`.

## The argument

The test function is a truncated extremal function. In space, for `N > 0`, put
`u_N = (min ‖u‖ N / ‖u‖) u` and `g_N = (min ‖u‖ N ^ (r - 1) / ‖u‖) u`, so that
`‖g_N‖ = ‖u_N‖ ^ (r - 1)` and `⟪u, g_N⟫ = ‖u‖ min (‖u‖, N) ^ (r - 1) ≥ ‖u_N‖ ^ r` pointwise. These
are Lipschitz maps of `u` vanishing at `0`
(`TauCeti.lipschitzWith_ofReal_min_norm_rpow_div_norm_smul`), hence continuous maps of `L²` into
itself, which keeps `b ↦ g_N (Φ b)` measurable. With
`ψ b = ‖u_N (Φ b)‖_{L^r}`, finite because `u_N (Φ b)` is bounded and square integrable, the test
function in time is `G b = 1_A(b) ψ(b) ^ (q - r) g_N (Φ b)`, where `A` is a set of finite measure on
which `ψ` is bounded above and below and `‖Φ b‖₂` is bounded. Then

`∫_A ψ ^ q ≤ |∫ ⟪Φ b, G b⟫| ≤ M ‖G‖_{L^{q'} L^{r'}} ≤ M (∫_A ψ ^ q) ^ (1 - 1 / q)`,

so `‖1_A ψ‖_{L^q} ≤ M`. Exhausting `β` by such sets `A` and letting `N → ∞`, by monotone
convergence in `x` and in `b`, gives the bound for `Φ`.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.14 (norming `Lᵖ` by test functions).
* A. Benedek and R. Panzone, *The space `Lᴾ`, with mixed norm*, Duke Math. J. 28 (1961), 301–324.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MeasureTheory

variable {β X 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {mβ : MeasurableSpace β} {ρ : Measure β} {mX : MeasurableSpace X} {μ : Measure X}

/-! ### Truncated powers -/

/-- The truncated power `y ↦ (min ‖y‖ N ^ s / ‖y‖) y`, of length `min ‖y‖ N ^ s`. -/
private def truncPow (N : ℝ≥0) (s : ℝ) (y : E) : E :=
  ((min ‖y‖ N ^ s / ‖y‖ : ℝ) : 𝕜) • y

private theorem truncPow_zero (N : ℝ≥0) (s : ℝ) : truncPow (𝕜 := 𝕜) N s (0 : E) = 0 := by
  simp [truncPow]

private theorem norm_truncPow (N : ℝ≥0) {s : ℝ} (hs : 0 < s) (y : E) :
    ‖truncPow (𝕜 := 𝕜) N s y‖ = min ‖y‖ N ^ s := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [truncPow, Real.zero_rpow hs.ne']
  · have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have := le_min hy'.le N.2
    rw [truncPow, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hy'.ne']

private theorem inner_truncPow (N : ℝ≥0) (s : ℝ) (y : E) :
    ⟪y, truncPow (𝕜 := 𝕜) N s y⟫_𝕜 = ((‖y‖ * min ‖y‖ N ^ s : ℝ) : 𝕜) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [truncPow]
  · have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [truncPow, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul]
    congr 1
    field_simp

/-! ### Truncated powers of `L²` functions -/

/-- The truncated power of an `L²` function, composed pointwise. -/
private def truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) : Lp E 2 μ :=
  (TauCeti.lipschitzWith_ofReal_min_norm_rpow_div_norm_smul (𝕜 := 𝕜) (E := E) N hs).compLp
    (truncPow_zero N s) u

private theorem coeFn_truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    truncLp (𝕜 := 𝕜) N hs u =ᵐ[μ] fun x ↦ truncPow (𝕜 := 𝕜) N s (u x) :=
  LipschitzWith.coeFn_compLp _ _ _

private theorem continuous_truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) :
    Continuous (truncLp (𝕜 := 𝕜) (μ := μ) (E := E) N hs) :=
  (TauCeti.lipschitzWith_ofReal_min_norm_rpow_div_norm_smul (𝕜 := 𝕜) (E := E) N
    hs).continuous_compLp (truncPow_zero N s)

/-- The truncation at height `N` of an `L²` function lies in every `Lʳ` with `2 ≤ r`. -/
private theorem eLpNorm_truncLp_ne_top (N : ℝ≥0) {r : ℝ≥0∞} (hr2 : 2 ≤ r) (u : Lp E 2 μ) :
    eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ ≠ ∞ := by
  set U := truncLp (𝕜 := 𝕜) N le_rfl u
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eLpNorm_le_of_exponent_le
    (Lp.aestronglyMeasurable U) two_pos hr2 (M := N + ‖U‖ + 1) (by positivity) ?_ ?_)
  · rw [← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith [N.coe_nonneg])
  · filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx
    rw [hx, norm_truncPow N one_pos, Real.rpow_one]
    linarith [min_le_right ‖u x‖ (N : ℝ), norm_nonneg U]

/-- The extremal function `g_N` of the truncation `u_N` satisfies
`‖g_N‖_{r'} ≤ ‖u_N‖_r ^ (r - 1)`. -/
private theorem eLpNorm_truncLp_le (N : ℝ≥0) {r r' : ℝ≥0∞} [r.HolderConjugate r'] (hr : r ≠ ∞)
    (hs : 1 ≤ r.toReal - 1) (u : Lp E 2 μ) :
    eLpNorm (truncLp (𝕜 := 𝕜) N hs u) r' μ ≤
      eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ ^ (r.toReal - 1) := by
  refine TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one hr (Lp.aestronglyMeasurable _) ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N hs u, coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx hx'
  rw [hx, hx', norm_truncPow N (by linarith), norm_truncPow N one_pos, Real.rpow_one]

/-- The pairing of `u` with the extremal function `g_N` is `∫ ‖u‖ min (‖u‖, N) ^ (r - 1)`. -/
private theorem inner_truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    ⟪u, truncLp (𝕜 := 𝕜) N hs u⟫_𝕜 = ((∫ x, ‖u x‖ * min ‖u x‖ N ^ s ∂μ : ℝ) : 𝕜) := by
  rw [L2.inner_def, ← integral_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N hs u] with x hx
  rw [hx, inner_truncPow]

/-- The pairing of `u` with the extremal function `g_N` bounds `‖u_N‖_r ^ r`. -/
private theorem eLpNorm_truncLp_rpow_le (N : ℝ≥0) {r : ℝ≥0∞} (hr : r ≠ ∞) (hr2 : 2 ≤ r)
    (u : Lp E 2 μ) :
    eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ ^ r.toReal ≤
      ENNReal.ofReal (∫ x, ‖u x‖ * min ‖u x‖ N ^ (r.toReal - 1) ∂μ) := by
  have hr0 : r ≠ 0 := (two_pos.trans_le hr2).ne'
  have hs : 1 ≤ r.toReal - 1 := by
    have := ENNReal.toReal_mono hr hr2
    simp only [ENNReal.toReal_ofNat] at this
    linarith
  have hint : Integrable (fun x ↦ ‖u x‖ * min ‖u x‖ N ^ (r.toReal - 1)) μ := by
    refine (L2.integrable_inner (𝕜 := 𝕜) u (truncLp (𝕜 := 𝕜) N hs u)).norm.congr ?_
    filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N hs u] with x hx
    rw [hx, inner_truncPow, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
  rw [← lintegral_rpow_enorm_eq_eLpNorm_rpow hr0 hr (Lp.aestronglyMeasurable _),
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ by positivity)]
  refine lintegral_mono_ae ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx
  have hm : 0 ≤ min ‖u x‖ N := le_min (norm_nonneg _) N.2
  rw [hx, ← ofReal_norm, norm_truncPow N one_pos, Real.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hm (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc min ‖u x‖ N ^ r.toReal = min ‖u x‖ N * min ‖u x‖ N ^ (r.toReal - 1) := by
        rw [← Real.rpow_one_add' hm (by linarith)]
        ring_nf
    _ ≤ ‖u x‖ * min ‖u x‖ N ^ (r.toReal - 1) := by gcongr; exact min_le_left _ _

/-! ### The bound on a set of finite measure -/

section Core

variable {q q' r r' : ℝ≥0∞} [q.HolderConjugate q'] [r.HolderConjugate r']

/-- The `Lʳ` norm `ψ = ‖u_N‖_r` of the truncation of `u` at height `N`, as a real number. -/
private def truncNorm (N : ℝ≥0) (r : ℝ≥0∞) (u : Lp E 2 μ) : ℝ :=
  (eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ).toReal

/-- The test function `G b = 1_A(b) ψ(b) ^ e g_N (Φ b)`. -/
private def testFn (N : ℝ≥0) (r : ℝ≥0∞) {s : ℝ} (hs : 1 ≤ s) (Φ : β → Lp E 2 μ) (A : Set β)
    (e : ℝ) (b : β) : Lp E 2 μ :=
  ((A.indicator (fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b) ^ e) b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)

private theorem truncNorm_nonneg {N : ℝ≥0} {r : ℝ≥0∞} {u : Lp E 2 μ} :
    0 ≤ truncNorm (𝕜 := 𝕜) N r u :=
  ENNReal.toReal_nonneg

private theorem testFn_def (N : ℝ≥0) (r : ℝ≥0∞) {s : ℝ} (hs : 1 ≤ s) (Φ : β → Lp E 2 μ)
    (A : Set β) (e : ℝ) :
    testFn (𝕜 := 𝕜) N r hs Φ A e = fun b ↦
      ((A.indicator (fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b) ^ e) b : ℝ) : 𝕜) •
        truncLp (𝕜 := 𝕜) N hs (Φ b) :=
  rfl

private theorem measurable_truncNorm (N : ℝ≥0) (r : ℝ≥0∞) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) : Measurable fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b) := by
  borelize ↥(Lp E 2 μ)
  exact ((TauCeti.lowerSemicontinuous_eLpNorm_Lp (μ := μ) Measure.AbsolutelyContinuous.rfl
    r).measurable.comp ((continuous_truncLp (𝕜 := 𝕜) N le_rfl).comp_stronglyMeasurable
      hΦ).measurable).ennreal_toReal

/-- On `A`, where `ψ ∈ [a, K]` and `‖Φ b‖₂ ≤ K`, the test function and its pairing with `Φ` are
bounded, so both are integrable when `A` has finite measure. -/
private theorem integrable_testFn {N : ℝ≥0} {s : ℝ} (hs : 1 ≤ s) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) {A : Set β} (hA : MeasurableSet A) (hρA : ρ A ≠ ∞) (e : ℝ)
    {a K : ℝ} (ha : 0 < a)
    (hAψ : ∀ b ∈ A, a ≤ truncNorm (𝕜 := 𝕜) N r (Φ b) ∧ truncNorm (𝕜 := 𝕜) N r (Φ b) ≤ K ∧
      ‖Φ b‖ ≤ K) :
    Integrable (testFn (𝕜 := 𝕜) N r hs Φ A e) ρ ∧
      Integrable (fun b ↦ ⟪Φ b, testFn (𝕜 := 𝕜) N r hs Φ A e b⟫_𝕜) ρ := by
  set L := 2 * N ^ (s - 1) + s.toNNReal * N ^ (s - 1)
  set B := max (a ^ e) (K ^ e)
  have hw : Measurable (A.indicator fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b) ^ e) :=
    ((measurable_truncNorm (𝕜 := 𝕜) N r hΦ).pow_const e).indicator hA
  have hG : StronglyMeasurable (testFn (𝕜 := 𝕜) N r hs Φ A e) := by
    rw [testFn_def]
    exact ((RCLike.continuous_ofReal (K := 𝕜)).measurable.comp hw).stronglyMeasurable.smul
      ((continuous_truncLp (𝕜 := 𝕜) N hs).comp_stronglyMeasurable hΦ)
  -- The weight `ψ ^ e` is at most `B` on `A`, whatever the sign of `e`.
  have hB : ∀ b ∈ A, truncNorm (𝕜 := 𝕜) N r (Φ b) ^ e ≤ B := fun b hb ↦ by
    obtain ⟨h1, h2, -⟩ := hAψ b hb
    rcases le_total 0 e with he | he
    · exact (Real.rpow_le_rpow (ha.le.trans h1) h2 he).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos ha h1 he).trans (le_max_left _ _)
  have hGb : ∀ b, ‖testFn (𝕜 := 𝕜) N r hs Φ A e b‖ ≤ A.indicator (fun _ ↦ B * (L * K)) b :=
    fun b ↦ by
    by_cases hb : b ∈ A
    · obtain ⟨h1, -, h3⟩ := hAψ b hb
      have hψ : 0 ≤ truncNorm (𝕜 := 𝕜) N r (Φ b) := ha.le.trans h1
      rw [Set.indicator_of_mem hb, testFn_def, norm_smul, RCLike.norm_ofReal,
        Set.indicator_of_mem hb, abs_of_nonneg (by positivity)]
      gcongr
      · exact hB b hb
      · exact ((TauCeti.lipschitzWith_ofReal_min_norm_rpow_div_norm_smul (𝕜 := 𝕜) (E := E) N
          hs).norm_compLp_le _ _).trans (by gcongr)
    · simp [testFn_def, Set.indicator_of_notMem hb]
  have hint : Integrable (A.indicator fun _ ↦ B * (L * K)) ρ :=
    (integrable_indicator_iff hA).2 (integrableOn_const hρA)
  refine ⟨hint.mono' hG.aestronglyMeasurable (ae_of_all _ hGb),
    (hint.const_mul K).mono' (continuous_inner.comp_stronglyMeasurable
      (hΦ.prodMk hG)).aestronglyMeasurable (ae_of_all _ fun b ↦ ?_)⟩
  by_cases hb : b ∈ A
  · have hK := (hAψ b hb).2.2
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul hK (hGb b) (norm_nonneg _) ((norm_nonneg _).trans hK))
  · simp [testFn_def, Set.indicator_of_notMem hb]

/-- The pairing of `Φ b` with the test function is `1_A(b) ψ(b) ^ e ∫ ‖Φ b‖ min (‖Φ b‖, N) ^ s`. -/
private theorem inner_testFn (N : ℝ≥0) (r : ℝ≥0∞) {s : ℝ} (hs : 1 ≤ s) (Φ : β → Lp E 2 μ)
    (A : Set β) (e : ℝ) (b : β) :
    ⟪Φ b, testFn (𝕜 := 𝕜) N r hs Φ A e b⟫_𝕜 =
      ((A.indicator (fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b) ^ e) b *
        ∫ x, ‖Φ b x‖ * min ‖Φ b x‖ N ^ s ∂μ : ℝ) : 𝕜) := by
  rw [testFn_def, inner_smul_right, inner_truncLp, ← RCLike.ofReal_mul]

/-- With the exponent `e = q - r`, the pairing bounds `‖1_A ψ‖ ^ q` pointwise. -/
private theorem enorm_indicator_rpow_le_re_inner_testFn (hq0 : 0 < q.toReal) (hr : r ≠ ∞)
    (hr2 : 2 ≤ r)
    (N : ℝ≥0) (hs : 1 ≤ r.toReal - 1) (Φ : β → Lp E 2 μ) {A : Set β}
    (hAψ : ∀ b ∈ A, 0 < truncNorm (𝕜 := 𝕜) N r (Φ b)) (b : β) :
    ‖A.indicator (fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b)) b‖ₑ ^ q.toReal ≤
      ENNReal.ofReal (RCLike.re ⟪Φ b, testFn (𝕜 := 𝕜) N r hs Φ A (q.toReal - r.toReal) b⟫_𝕜) := by
  rw [inner_testFn, RCLike.ofReal_re]
  by_cases hb : b ∈ A
  · set ψ := truncNorm (𝕜 := 𝕜) N r (Φ b)
    have hψ : 0 < ψ := hAψ b hb
    -- `ψ ^ r ≤ ∫ ‖Φ b‖ min (‖Φ b‖, N) ^ (r - 1)`, read off in `[0, ∞]`.
    have hJ := eLpNorm_truncLp_rpow_le (𝕜 := 𝕜) N hr hr2 (Φ b)
    rw [← ENNReal.ofReal_toReal (eLpNorm_truncLp_ne_top N hr2 (Φ b)),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ by positivity)] at hJ
    rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, Real.eNorm_of_nonneg hψ.le,
      ENNReal.ofReal_rpow_of_nonneg hψ.le hq0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ψ ^ q.toReal = ψ ^ (q.toReal - r.toReal) * ψ ^ r.toReal := by
          rw [← Real.rpow_add hψ, sub_add_cancel]
      _ ≤ _ := by gcongr; exact hJ
  · simp [Set.indicator_of_notMem hb, ENNReal.zero_rpow_of_pos hq0]

/-- With the exponent `e = q - r`, `‖G b‖_{r'} ≤ ‖1_A ψ‖ ^ (q - 1)` pointwise. -/
private theorem eLpNorm_testFn_le (hr : r ≠ ∞) (hr2 : 2 ≤ r) (N : ℝ≥0) (hs : 1 ≤ r.toReal - 1)
    (Φ : β → Lp E 2 μ) {A : Set β} (hAψ : ∀ b ∈ A, 0 < truncNorm (𝕜 := 𝕜) N r (Φ b)) (b : β) :
    eLpNorm (testFn (𝕜 := 𝕜) N r hs Φ A (q.toReal - r.toReal) b) r' μ ≤
      ‖‖A.indicator (fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b)) b‖ ^ (q.toReal - 1)‖ₑ := by
  rw [testFn_def, eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul]
  by_cases hb : b ∈ A
  · set ψ := truncNorm (𝕜 := 𝕜) N r (Φ b)
    have hψ : 0 < ψ := hAψ b hb
    have hU : eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl (Φ b)) r μ = ENNReal.ofReal ψ :=
      (ENNReal.ofReal_toReal (eLpNorm_truncLp_ne_top N hr2 (Φ b))).symm
    rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, Real.norm_of_nonneg hψ.le,
      ← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      Real.eNorm_of_nonneg (by positivity)]
    calc _ ≤ ENNReal.ofReal (ψ ^ (q.toReal - r.toReal)) * ENNReal.ofReal ψ ^ (r.toReal - 1) := by
          gcongr
          rw [← hU]
          exact eLpNorm_truncLp_le N hr hs (Φ b)
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg hψ.le (by linarith),
            ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hψ]
          ring_nf
  · simp [Set.indicator_of_notMem hb]

/-- **The bound on a set of finite measure.** If `ψ = ‖u_N (Φ b)‖_r` lies in `[a, K]` with
`a > 0` and `‖Φ b‖₂ ≤ K` on a measurable set `A` of finite measure, then testing against
`G b = 1_A(b) ψ(b) ^ (q - r) g_N (Φ b)` gives `‖1_A ψ‖_q ^ q ≤ M ‖1_A ψ‖_q ^ (q - 1)`, so
`‖1_A ψ‖_q ≤ M`. -/
private theorem eLpNorm_indicator_truncNorm_le (hq : q ≠ ∞) (hr : r ≠ ∞) (hr2 : 2 ≤ r)
    {Φ : β → Lp E 2 μ} (hΦ : StronglyMeasurable Φ) {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ)
    (N : ℝ≥0) {A : Set β} (hA : MeasurableSet A) (hρA : ρ A ≠ ∞) {a K : ℝ} (ha : 0 < a)
    (hAψ : ∀ b ∈ A, a ≤ truncNorm (𝕜 := 𝕜) N r (Φ b) ∧ truncNorm (𝕜 := 𝕜) N r (Φ b) ≤ K ∧
      ‖Φ b‖ ≤ K) :
    eLpNorm (A.indicator fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b)) q ρ ≤ M := by
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q q'
  have hs : 1 ≤ r.toReal - 1 := by
    have := ENNReal.toReal_mono hr hr2
    simp only [ENNReal.toReal_ofNat] at this
    linarith
  have hpos : ∀ b ∈ A, 0 < truncNorm (𝕜 := 𝕜) N r (Φ b) := fun b hb ↦ ha.trans_le (hAψ b hb).1
  set f := A.indicator fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b) with hf_def
  set G := testFn (𝕜 := 𝕜) N r hs Φ A (q.toReal - r.toReal)
  obtain ⟨hG, hpair⟩ :=
    integrable_testFn (𝕜 := 𝕜) (r := r) hs hΦ hA hρA (q.toReal - r.toReal) ha hAψ
  have hf : AEStronglyMeasurable f ρ :=
    ((measurable_truncNorm (𝕜 := 𝕜) N r hΦ).indicator hA).aestronglyMeasurable
  -- `f` is bounded by `K` and vanishes off `A`, which has finite measure.
  have hX : eLpNorm f q ρ ≠ ∞ := by
    refine ((memLp_top_of_bound hf (max K 0) (ae_of_all _ fun b ↦ ?_)
      ).mono_exponent_of_measure_support_ne_top (fun b hb ↦ Set.indicator_of_notMem hb _) hρA
      le_top).eLpNorm_ne_top
    by_cases hb : b ∈ A
    · rw [hf_def, Set.indicator_of_mem hb, Real.norm_of_nonneg (hpos b hb).le]
      exact (hAψ b hb).2.1.trans (le_max_left _ _)
    · rw [hf_def, Set.indicator_of_notMem hb, norm_zero]
      exact le_max_right _ _
  refine ENNReal.le_of_rpow_le_mul_rpow_sub_one (r := q.toReal) hX ?_
  calc eLpNorm f q ρ ^ q.toReal = ∫⁻ b, ‖f b‖ₑ ^ q.toReal ∂ρ :=
        (lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf).symm
    _ ≤ ∫⁻ b, ENNReal.ofReal (RCLike.re ⟪Φ b, G b⟫_𝕜) ∂ρ := lintegral_mono fun b ↦
        enorm_indicator_rpow_le_re_inner_testFn (ENNReal.toReal_pos hq0 hq) hr hr2 N hs Φ hpos b
    _ = ENNReal.ofReal (∫ b, RCLike.re ⟪Φ b, G b⟫_𝕜 ∂ρ) := by
        refine (ofReal_integral_eq_lintegral_ofReal hpair.re (Eventually.of_forall fun b ↦ ?_)).symm
        simp only [Pi.zero_apply, inner_testFn, RCLike.ofReal_re]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ Real.rpow_nonneg truncNorm_nonneg _) _)
          (integral_nonneg fun x ↦ by positivity)
    _ ≤ ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ := by
        rw [integral_re hpair, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
    _ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ := hM G hG hpair
    _ ≤ M * eLpNorm (fun b ↦ ‖f b‖ ^ (q.toReal - 1)) q' ρ := by
        gcongr
        exact eLpNorm_mono_eNorm
          (hG.aestronglyMeasurable.aemeasurable_eLpNorm_Lp .rfl r').aestronglyMeasurable
          fun b ↦ by rw [eNorm_eq_self]; exact eLpNorm_testFn_le hr hr2 N hs Φ hpos b
    _ ≤ M * eLpNorm f q ρ ^ (q.toReal - 1) := by
        gcongr
        exact TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq
          (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
          (ae_of_all _ fun b ↦ (Real.norm_of_nonneg (by positivity)).le)

/-- **Exhaustion.** Exhausting `β` by the sets of finite measure where `ψ ∈ [1 / (k + 1), k]` and
`‖Φ b‖₂ ≤ k` bounds `‖ψ‖_q` by `M`. -/
private theorem eLpNorm_truncNorm_le [SigmaFinite ρ] (hq : q ≠ ∞) (hr : r ≠ ∞) (hr2 : 2 ≤ r)
    {Φ : β → Lp E 2 μ} (hΦ : StronglyMeasurable Φ) {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ)
    (N : ℝ≥0) : eLpNorm (fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b)) q ρ ≤ M := by
  set ψ := fun b ↦ truncNorm (𝕜 := 𝕜) N r (Φ b)
  have hψ : Measurable ψ := measurable_truncNorm N r hΦ
  set A : ℕ → Set β := fun k ↦
    spanningSets ρ k ∩ ({b | 1 / ((k : ℝ) + 1) ≤ ψ b} ∩ ({b | ψ b ≤ k} ∩ {b | ‖Φ b‖ ≤ k}))
  have hA (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_spanningSets ρ k).inter ((measurableSet_le measurable_const hψ).inter
      ((measurableSet_le hψ measurable_const).inter
        (measurableSet_le hΦ.norm.measurable measurable_const)))
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun k ↦ (A k).indicator ψ)
    (Eventually.of_forall fun k ↦ eLpNorm_indicator_truncNorm_le hq hr hr2 hΦ hM N (hA k)
      ((measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top ρ k)).ne
      (by positivity) fun b hb ↦ hb.2)
    (fun k ↦ (hψ.indicator (hA k)).aestronglyMeasurable) hψ.aestronglyMeasurable
    (ae_of_all _ fun b ↦ ?_)
  -- Every `b` with `ψ b > 0` lies in `A k` for all large `k`; where `ψ b = 0` there is nothing
  -- to prove.
  refine tendsto_const_nhds.congr' ?_
  rcases (truncNorm_nonneg : 0 ≤ ψ b).eq_or_lt with h0 | hpos
  · exact Eventually.of_forall fun k ↦
      ((Set.indicator_apply_eq_self (s := A k) (f := ψ)).2 fun _ ↦ h0.symm).symm
  filter_upwards [eventually_mem_spanningSets ρ b,
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_le_nhds hpos),
    eventually_ge_atTop ⌈ψ b⌉₊, eventually_ge_atTop ⌈‖Φ b‖⌉₊] with k h1 h2 h3 h4
  have h3' : ψ b ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast h3)
  have h4' : ‖Φ b‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast h4)
  have hb : b ∈ A k := ⟨h1, h2, h3', h4'⟩
  rw [Set.indicator_of_mem hb]

end Core

/-! ### Monotone convergence in the truncation height -/

private theorem truncNorm_mono {r : ℝ≥0∞} (hr2 : 2 ≤ r) (u : Lp E 2 μ) :
    Monotone fun N : ℕ ↦ truncNorm (𝕜 := 𝕜) (N : ℝ≥0) r u := fun N N' hN ↦ by
  refine ENNReal.toReal_mono (eLpNorm_truncLp_ne_top _ hr2 u) (eLpNorm_mono_ae
    (Lp.aestronglyMeasurable _) ?_)
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u,
    coeFn_truncLp (𝕜 := 𝕜) (N' : ℝ≥0) le_rfl u] with x hx hx'
  rw [hx, hx', norm_truncPow _ one_pos, norm_truncPow _ one_pos, Real.rpow_one, Real.rpow_one]
  exact min_le_min_left _ (by exact_mod_cast hN)

/-- `‖u‖_r` is the supremum of the norms `‖u_N‖_r` of the truncations of `u`. -/
private theorem eLpNorm_eq_iSup_truncNorm {r : ℝ≥0∞} (hr2 : 2 ≤ r) (u : Lp E 2 μ) :
    eLpNorm u r μ = ⨆ N : ℕ, ENNReal.ofReal (truncNorm (𝕜 := 𝕜) (N : ℝ≥0) r u) := by
  have hae : ∀ᵐ x ∂μ, ∀ N : ℕ, ‖truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u x‖ₑ =
      ENNReal.ofReal (min ‖u x‖ N) := by
    filter_upwards [ae_all_iff.2 fun N : ℕ ↦ coeFn_truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u]
      with x hx N
    rw [hx N, ← ofReal_norm, norm_truncPow _ one_pos, Real.rpow_one, NNReal.coe_natCast]
  simp_rw [truncNorm, ENNReal.ofReal_toReal (eLpNorm_truncLp_ne_top _ hr2 u)]
  rw [← eLpNorm_eNorm _ (Lp.aestronglyMeasurable u)]
  simp_rw [← fun N : ℕ ↦ eLpNorm_eNorm (μ := μ) (p := r) _
    (Lp.aestronglyMeasurable (truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u))]
  rw [← eLpNorm_iSup_eq_iSup_eLpNorm (fun N ↦ (Lp.aestronglyMeasurable _).eNorm)]
  · refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hx, ← ofReal_norm]
    refine le_antisymm ?_ (iSup_le fun N ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))
    refine le_iSup_of_le ⌈‖u x‖⌉₊ (ENNReal.ofReal_le_ofReal (le_min le_rfl (Nat.le_ceil _)))
  · filter_upwards [hae] with x hx N N' hN
    simp only [hx]
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hN))

/-! ### The norming theorem -/

variable {q q' r r' : ℝ≥0∞} [q.HolderConjugate q'] [r.HolderConjugate r']

/-- **Norming mixed norms by `L²`-valued test functions.** Let `1 ≤ q < ∞` and `2 ≤ r < ∞`, with
Hölder conjugates `q'` and `r'`, and let `ρ` be σ-finite. If an almost everywhere strongly
measurable `Φ : β → L²(X, μ)` satisfies

`|∫ ⟪Φ b, G b⟫ dρ(b)| ≤ M ‖G‖_{L^{q'}_b L^{r'}_x}`

for every integrable `G : β → L²(X, μ)` for which `b ↦ ⟪Φ b, G b⟫` is integrable, then
`‖Φ‖_{L^q_b L^r_x} ≤ M`. -/
theorem AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le
    [SigmaFinite ρ] (hq : q ≠ ∞) (hr : r ≠ ∞) (hr2 : 2 ≤ r) {Φ : β → Lp E 2 μ}
    (hΦ : AEStronglyMeasurable Φ ρ) {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ) :
    eLpNorm (fun b ↦ eLpNorm (Φ b) r μ) q ρ ≤ M := by
  -- Pass to a strongly measurable representative `Φ'` of `Φ`.
  obtain ⟨Φ', hΦ', hae⟩ := hΦ
  have hM' : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ' b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ' b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ := by
    intro G hG hpair
    have hcongr : (fun b ↦ ⟪Φ' b, G b⟫_𝕜) =ᵐ[ρ] fun b ↦ ⟪Φ b, G b⟫_𝕜 :=
      hae.mono fun b hb ↦ by simp only [hb]
    rw [integral_congr_ae hcongr]
    exact hM G hG (hpair.congr hcongr)
  rw [eLpNorm_congr_ae (g := fun b ↦ eLpNorm (Φ' b) r μ)
    (hae.mono fun b hb ↦ by simp only [hb])]
  -- Monotone convergence in the truncation height, then the bound for each truncation.
  have hmeas (N : ℕ) : Measurable fun b ↦ truncNorm (𝕜 := 𝕜) (N : ℝ≥0) r (Φ' b) :=
    measurable_truncNorm _ r hΦ'
  simp_rw [eLpNorm_eq_iSup_truncNorm (𝕜 := 𝕜) hr2]
  rw [eLpNorm_iSup_eq_iSup_eLpNorm (fun N ↦ (hmeas N).ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun b N N' hN ↦ ENNReal.ofReal_le_ofReal (truncNorm_mono hr2 (Φ' b) hN))]
  refine iSup_le fun N ↦ ?_
  rw [eLpNorm_congr_eNorm_ae (hmeas N).ennreal_ofReal.aestronglyMeasurable
    (hmeas N).aestronglyMeasurable
    (ae_of_all _ fun b ↦ by rw [eNorm_eq_self, Real.eNorm_of_nonneg truncNorm_nonneg])]
  exact eLpNorm_truncNorm_le hq hr hr2 hΦ' hM' _

end MeasureTheory
