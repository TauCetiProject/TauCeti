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
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Indicator
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
`1 ≤ q < ∞`, `2 ≤ r ≤ ∞` and a σ-finite measure `ρ`. Membership of `Φ` in `L^q L^r` is not assumed;
it follows when `M < ∞`. The endpoint `r = ∞`, `r' = 1` is included, as needed for the Strichartz
pair `(4, ∞)` on the line.

This turns estimates proved in weak form, by testing against `L²`-valued functions, into mixed-norm
estimates. The typical application is to Strichartz estimates, where the `TT*` argument bounds the
pairings `∫ ⟪U(t) f, G(t)⟫ dt` for `L²`-valued `G`.

The file also records two elementary properties of mixed norms of families of `Lᵖ` functions:
Minkowski's inequality `‖Φ + Ψ‖_{L^q L^r} ≤ ‖Φ‖_{L^q L^r} + ‖Ψ‖_{L^q L^r}` for `1 ≤ q, r`
(`MeasureTheory.eLpNorm_eLpNorm_add_le`), and invariance under the reflection `b ↦ -b` of the
parameter when `ρ` is invariant under negation (`ρ.IsNegInvariant`), as Lebesgue measure on the
time line is (`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_comp_neg`); the latter reverses
time in such estimates.

## The argument

The test function is a truncated extremal function. In space, for `N > 0`, put
`u_N = (min ‖u‖ N / ‖u‖) u` and `g_N = (min ‖u‖ N ^ (r - 1) / ‖u‖) u`, so that
`‖g_N‖ = ‖u_N‖ ^ (r - 1)` and `⟪u, g_N⟫ = ‖u‖ min (‖u‖, N) ^ (r - 1) ≥ ‖u_N‖ ^ r` pointwise. These
are the truncated powers `TauCeti.truncPow` at `s = 1` and `s = r - 1`, Lipschitz maps of `u`
vanishing at `0` (`TauCeti.lipschitzWith_truncPow`), hence continuous maps of `L²` into itself,
which keeps `b ↦ g_N (Φ b)` measurable. With `ψ b = ‖u_N (Φ b)‖_{L^r}`, finite because
`u_N (Φ b)` is bounded and square integrable, the test function in time is
`G b = 1_A(b) ψ(b) ^ (q - r) g_N (Φ b)`, where `A` is a set of finite measure on which `ψ` is
bounded above and below and `‖Φ b‖₂` is bounded. Then

`∫_A ψ ^ q ≤ |∫ ⟪Φ b, G b⟫| ≤ M ‖G‖_{L^{q'} L^{r'}} ≤ M (∫_A ψ ^ q) ^ (1 - 1 / q)`,

so `‖1_A ψ‖_{L^q} ≤ M`. Exhausting `β` by such sets `A` and letting `N → ∞`, by monotone
convergence in `x` and in `b`, gives the bound for `Φ`.

At `r = ∞` there is no extremal function in `L¹` for the essential supremum, and the test
functions are the truncated powers `g = g_{N,s}`, of length `min (‖u‖, N) ^ s`, normalized in `L¹`.
The ratio `ψ_s = ⟪u, g⟫ / ‖g‖₁ = ∫ ‖u‖ min (‖u‖, N) ^ s / ∫ min (‖u‖, N) ^ s` is a weighted
average of `‖u‖`, and the same argument with `G b = 1_A(b) ψ_s(b) ^ (q - 1) ‖g‖₁⁻¹ g (Φ b)` bounds
`‖ψ_s‖_{L^q}` by `M`. As `s → ∞` the weight `min (‖u‖, N) ^ s` concentrates where `min (‖u‖, N)` is
close to its essential supremum `‖u_N‖_∞`: for `0 < t < t' < ‖u_N‖_∞`, the mass of the weight on
`{min (‖u‖, N) > t'}` is at least `t' ^ s` times a positive measure, while on
`{min (‖u‖, N) ≤ t}` it is at most `t ^ (s - 2) ‖u‖₂²`. So `ψ_s ≥ t` for all large `s`, and
`‖u_N‖_∞` is the limit of `min (ψ_s, ‖u_N‖_∞)`, whose `L^q` norms are at most `M`.

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

/-! ### Truncated powers of `L²` functions -/

/-- The truncated power of an `L²` function, composed pointwise. -/
private def truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) : Lp E 2 μ :=
  (TauCeti.lipschitzWith_truncPow (𝕜 := 𝕜) (E := E) N hs).compLp
    (TauCeti.truncPow_zero N s) u

private theorem coeFn_truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    truncLp (𝕜 := 𝕜) N hs u =ᵐ[μ] fun x ↦ TauCeti.truncPow 𝕜 N s (u x) :=
  LipschitzWith.coeFn_compLp _ _ _

private theorem continuous_truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) :
    Continuous (truncLp (𝕜 := 𝕜) (μ := μ) (E := E) N hs) :=
  (TauCeti.lipschitzWith_truncPow (𝕜 := 𝕜) (E := E) N
    hs).continuous_compLp (TauCeti.truncPow_zero N s)

/-- The truncation at height `N` of an `L²` function lies in every `Lʳ` with `2 ≤ r`. -/
private theorem eLpNorm_truncLp_ne_top (N : ℝ≥0) {r : ℝ≥0∞} (hr2 : 2 ≤ r) (u : Lp E 2 μ) :
    eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ ≠ ∞ := by
  set U := truncLp (𝕜 := 𝕜) N le_rfl u
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eLpNorm_le_of_exponent_le
    (Lp.aestronglyMeasurable U) two_pos hr2 (M := N + ‖U‖ + 1) (by positivity) ?_ ?_)
  · rw [← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith [N.coe_nonneg])
  · filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx
    rw [hx, TauCeti.norm_truncPow N one_pos, Real.rpow_one]
    linarith [min_le_right ‖u x‖ (N : ℝ), norm_nonneg U]

/-- The extremal function `g_N` of the truncation `u_N` satisfies
`‖g_N‖_{r'} ≤ ‖u_N‖_r ^ (r - 1)`. -/
private theorem eLpNorm_truncLp_le (N : ℝ≥0) {r r' : ℝ≥0∞} [r.HolderConjugate r'] (hr : r ≠ ∞)
    (hs : 1 ≤ r.toReal - 1) (u : Lp E 2 μ) :
    eLpNorm (truncLp (𝕜 := 𝕜) N hs u) r' μ ≤
      eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ ^ (r.toReal - 1) := by
  refine TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one hr (Lp.aestronglyMeasurable _) ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N hs u, coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx hx'
  rw [hx, hx', TauCeti.norm_truncPow N (by linarith), TauCeti.norm_truncPow N one_pos,
    Real.rpow_one]

/-- The pairing of `u` with the extremal function `g_N` is `∫ ‖u‖ min (‖u‖, N) ^ (r - 1)`. -/
private theorem inner_truncLp (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    ⟪u, truncLp (𝕜 := 𝕜) N hs u⟫_𝕜 = ((∫ x, ‖u x‖ * min ‖u x‖ N ^ s ∂μ : ℝ) : 𝕜) := by
  rw [L2.inner_def, ← integral_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N hs u] with x hx
  rw [hx, TauCeti.inner_truncPow]

/-- For `0 ≤ v ≤ c`, `v ≤ w` and `s ≥ 1`, `w v ^ s ≤ c ^ (s - 1) w²`. -/
private theorem mul_rpow_le_rpow_sub_one_mul_sq {v c w s : ℝ} (hv : 0 ≤ v) (hvc : v ≤ c)
    (hvw : v ≤ w) (hs : 1 ≤ s) : w * v ^ s ≤ c ^ (s - 1) * w ^ 2 := by
  calc w * v ^ s = v ^ (s - 1) * (v * w) := by
        rw [← mul_assoc, ← Real.rpow_add_one' hv (by linarith), sub_add_cancel]
        ring
    _ ≤ c ^ (s - 1) * w ^ 2 := by
        rw [sq]
        exact mul_le_mul (Real.rpow_le_rpow hv hvc (by linarith))
          (mul_le_mul_of_nonneg_right hvw (hv.trans hvw)) (mul_nonneg hv (hv.trans hvw))
          (Real.rpow_nonneg (hv.trans hvc) _)

/-- For `0 ≤ v ≤ c`, `v ≤ w` and `s ≥ 2`, `v ^ s ≤ c ^ (s - 2) w²`. -/
private theorem rpow_le_rpow_sub_two_mul_sq {v c w s : ℝ} (hv : 0 ≤ v) (hvc : v ≤ c)
    (hvw : v ≤ w) (hs : 2 ≤ s) : v ^ s ≤ c ^ (s - 2) * w ^ 2 := by
  calc v ^ s = v * v ^ (s - 1) := by
        rw [← Real.rpow_one_add' hv (by linarith)]
        ring_nf
    _ ≤ w * v ^ (s - 1) := mul_le_mul_of_nonneg_right hvw (Real.rpow_nonneg hv _)
    _ ≤ c ^ (s - 1 - 1) * w ^ 2 := mul_rpow_le_rpow_sub_one_mul_sq hv hvc hvw (by linarith)
    _ = c ^ (s - 2) * w ^ 2 := by ring_nf

/-- The integrand `‖u‖ min (‖u‖, N) ^ s ≤ N ^ (s - 1) ‖u‖²` of the pairing of `u` with `g_N` is
integrable. -/
private theorem integrable_norm_mul_min_rpow (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    Integrable (fun x ↦ ‖u x‖ * min ‖u x‖ N ^ s) μ := by
  have hu := Lp.stronglyMeasurable u
  refine ((Lp.integrable_sq_norm u).const_mul ((N : ℝ) ^ (s - 1))).mono' (hu.norm.measurable.mul
      ((hu.norm.measurable.min measurable_const).pow_const s)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_rpow_le_rpow_sub_one_mul_sq (le_min (norm_nonneg _) N.property) (min_le_right _ _)
    (min_le_left _ _) hs

/-- The pairing of `u` with the extremal function `g_N` bounds `‖u_N‖_r ^ r`. -/
private theorem eLpNorm_truncLp_rpow_le (N : ℝ≥0) {r : ℝ≥0∞} (hr : r ≠ ∞) (hr2 : 2 ≤ r)
    (u : Lp E 2 μ) :
    eLpNorm (truncLp (𝕜 := 𝕜) N le_rfl u) r μ ^ r.toReal ≤
      ENNReal.ofReal (∫ x, ‖u x‖ * min ‖u x‖ N ^ (r.toReal - 1) ∂μ) := by
  have hr0 : r ≠ 0 := (two_pos.trans_le hr2).ne'
  have hs := ENNReal.one_le_toReal_sub_one hr hr2
  rw [← lintegral_rpow_enorm_eq_eLpNorm_rpow hr0 hr (Lp.aestronglyMeasurable _),
    ofReal_integral_eq_lintegral_ofReal (integrable_norm_mul_min_rpow N hs u)
      (Eventually.of_forall fun x ↦ by positivity)]
  refine lintegral_mono_ae ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx
  have hm : 0 ≤ min ‖u x‖ N := le_min (norm_nonneg _) N.property
  rw [hx, ← ofReal_norm, TauCeti.norm_truncPow N one_pos, Real.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hm (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc min ‖u x‖ N ^ r.toReal = min ‖u x‖ N * min ‖u x‖ N ^ (r.toReal - 1) := by
        rw [← Real.rpow_one_add' hm (by linarith)]
        ring_nf
    _ ≤ ‖u x‖ * min ‖u x‖ N ^ (r.toReal - 1) := by gcongr; exact min_le_left _ _

/-- **The duality step.** Let `f ≥ 0` vanish off a set `A` of finite measure and be at most `K` on
it. If the weak bound `|∫ ⟪Φ b, G b⟫ dρ| ≤ M ‖G‖_{L^{q'} L^{r'}}` holds and a test function `G`
with integrable pairing satisfies `‖f b‖ ^ q ≤ re ⟪Φ b, G b⟫` and `‖G b‖_{r'} ≤ ‖f b‖ ^ (q - 1)`,
then `‖f‖_q ^ q ≤ M ‖f‖_q ^ (q - 1)`, so `‖f‖_q ≤ M`. -/
private theorem eLpNorm_le_of_enorm_rpow_le_re_inner {q q' r' : ℝ≥0∞} [q.HolderConjugate q']
    (hq : q ≠ ∞) {Φ : β → Lp E 2 μ} {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ)
    {f : β → ℝ} (hf : AEStronglyMeasurable f ρ) (hf0 : ∀ b, 0 ≤ f b) {A : Set β}
    (hρA : ρ A ≠ ∞) {K : ℝ} (hfA : ∀ b ∉ A, f b = 0) (hfK : ∀ b ∈ A, f b ≤ K)
    {G : β → Lp E 2 μ} (hG : Integrable G ρ) (hpair : Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ)
    (hre : ∀ b, 0 ≤ RCLike.re ⟪Φ b, G b⟫_𝕜)
    (hle : ∀ b, ‖f b‖ₑ ^ q.toReal ≤ ENNReal.ofReal (RCLike.re ⟪Φ b, G b⟫_𝕜))
    (hGf : ∀ b, eLpNorm (G b) r' μ ≤ ‖‖f b‖ ^ (q.toReal - 1)‖ₑ) :
    eLpNorm f q ρ ≤ M := by
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q q'
  -- `f` is bounded by `max K 0` and vanishes off `A`, which has finite measure.
  have hX : eLpNorm f q ρ ≠ ∞ := by
    refine (memLp_of_norm_le_of_measure_support_ne_top hf (c := max K 0) (ae_of_all _ fun b ↦ ?_)
      hρA hfA q).eLpNorm_ne_top
    rw [Real.norm_of_nonneg (hf0 b)]
    by_cases hb : b ∈ A
    · exact (hfK b hb).trans (le_max_left _ _)
    · exact (hfA b hb).trans_le (le_max_right _ _)
  refine ENNReal.le_of_rpow_le_mul_rpow_sub_one (r := q.toReal) hX ?_
  calc eLpNorm f q ρ ^ q.toReal = ∫⁻ b, ‖f b‖ₑ ^ q.toReal ∂ρ :=
        (lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf).symm
    _ ≤ ∫⁻ b, ENNReal.ofReal (RCLike.re ⟪Φ b, G b⟫_𝕜) ∂ρ := lintegral_mono hle
    _ = ENNReal.ofReal (∫ b, RCLike.re ⟪Φ b, G b⟫_𝕜 ∂ρ) :=
        (ofReal_integral_eq_lintegral_ofReal hpair.re (Eventually.of_forall hre)).symm
    _ ≤ ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ := by
        rw [integral_re hpair, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
    _ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ := hM G hG hpair
    _ ≤ M * eLpNorm (fun b ↦ ‖f b‖ ^ (q.toReal - 1)) q' ρ := by
        gcongr
        exact eLpNorm_mono_eNorm
          (hG.aestronglyMeasurable.aemeasurable_eLpNorm_Lp .rfl r').aestronglyMeasurable
          fun b ↦ by rw [eNorm_eq_self]; exact hGf b
    _ ≤ M * eLpNorm f q ρ ^ (q.toReal - 1) := by
        gcongr
        exact TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq
          (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
          (ae_of_all _ fun b ↦ (Real.norm_of_nonneg (by positivity)).le)

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

/-- A test function `b ↦ w b • g_N (Φ b)` whose weight `w` vanishes off a set `A` of finite
measure and is bounded on it, where moreover `‖Φ b‖₂ ≤ K`, is integrable, and so is its pairing
with `Φ`. -/
private theorem integrable_smul_truncLp {N : ℝ≥0} {s : ℝ} (hs : 1 ≤ s) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) {A : Set β} (hA : MeasurableSet A) (hρA : ρ A ≠ ∞) {w : β → ℝ}
    (hw : Measurable w) {B K : ℝ} (hwA : ∀ b ∉ A, w b = 0) (hwB : ∀ b ∈ A, |w b| ≤ B)
    (hΦK : ∀ b ∈ A, ‖Φ b‖ ≤ K) :
    Integrable (fun b ↦ ((w b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)) ρ ∧
      Integrable (fun b ↦ ⟪Φ b, ((w b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)⟫_𝕜) ρ := by
  set L := 2 * N ^ (s - 1) + s.toNNReal * N ^ (s - 1)
  set G := fun b ↦ ((w b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)
  have hG : StronglyMeasurable G :=
    ((RCLike.continuous_ofReal (K := 𝕜)).measurable.comp hw).stronglyMeasurable.smul
      ((continuous_truncLp (𝕜 := 𝕜) N hs).comp_stronglyMeasurable hΦ)
  have hGb : ∀ b, ‖G b‖ ≤ A.indicator (fun _ ↦ B * (L * K)) b := fun b ↦ by
    by_cases hb : b ∈ A
    · have h3 := hΦK b hb
      rw [Set.indicator_of_mem hb, norm_smul, RCLike.norm_ofReal]
      exact mul_le_mul (hwB b hb) (((TauCeti.lipschitzWith_truncPow (𝕜 := 𝕜) (E := E) N
        hs).norm_compLp_le _ _).trans (by gcongr)) (norm_nonneg _)
        ((abs_nonneg _).trans (hwB b hb))
    · simp [G, hwA b hb, Set.indicator_of_notMem hb]
  have hint : Integrable (A.indicator fun _ ↦ B * (L * K)) ρ :=
    (integrable_indicator_iff hA).2 (integrableOn_const hρA)
  refine ⟨hint.mono' hG.aestronglyMeasurable (ae_of_all _ hGb),
    (hint.const_mul K).mono' (continuous_inner.comp_stronglyMeasurable
      (hΦ.prodMk hG)).aestronglyMeasurable (ae_of_all _ fun b ↦ ?_)⟩
  by_cases hb : b ∈ A
  · have hK := hΦK b hb
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul hK (hGb b) (norm_nonneg _) ((norm_nonneg _).trans hK))
  · simp [hwA b hb, Set.indicator_of_notMem hb]

/-- On `A`, where `ψ ∈ [a, K]` and `‖Φ b‖₂ ≤ K`, the test function and its pairing with `Φ` are
bounded, so both are integrable when `A` has finite measure. -/
private theorem integrable_testFn {N : ℝ≥0} {s : ℝ} (hs : 1 ≤ s) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) {A : Set β} (hA : MeasurableSet A) (hρA : ρ A ≠ ∞) (e : ℝ)
    {a K : ℝ} (ha : 0 < a)
    (hAψ : ∀ b ∈ A, a ≤ truncNorm (𝕜 := 𝕜) N r (Φ b) ∧ truncNorm (𝕜 := 𝕜) N r (Φ b) ≤ K ∧
      ‖Φ b‖ ≤ K) :
    Integrable (testFn (𝕜 := 𝕜) N r hs Φ A e) ρ ∧
      Integrable (fun b ↦ ⟪Φ b, testFn (𝕜 := 𝕜) N r hs Φ A e b⟫_𝕜) ρ := by
  rw [testFn_def]
  refine integrable_smul_truncLp hs hΦ hA hρA
    (((measurable_truncNorm (𝕜 := 𝕜) N r hΦ).pow_const e).indicator hA) (B := max (a ^ e) (K ^ e))
    (fun b hb ↦ Set.indicator_of_notMem hb _) (fun b hb ↦ ?_) fun b hb ↦ (hAψ b hb).2.2
  -- The weight `ψ ^ e` is at most `max (a ^ e) (K ^ e)` on `A`, whatever the sign of `e`.
  obtain ⟨h1, h2, -⟩ := hAψ b hb
  rw [Set.indicator_of_mem hb, abs_of_nonneg (Real.rpow_nonneg (ha.le.trans h1) _)]
  rcases le_total 0 e with he | he
  · exact (Real.rpow_le_rpow (ha.le.trans h1) h2 he).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos ha h1 he).trans (le_max_left _ _)

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
  have hs := ENNReal.one_le_toReal_sub_one hr hr2
  have hpos : ∀ b ∈ A, 0 < truncNorm (𝕜 := 𝕜) N r (Φ b) := fun b hb ↦ ha.trans_le (hAψ b hb).1
  obtain ⟨hG, hpair⟩ :=
    integrable_testFn (𝕜 := 𝕜) (r := r) hs hΦ hA hρA (q.toReal - r.toReal) ha hAψ
  refine eLpNorm_le_of_enorm_rpow_le_re_inner hq hM
    ((measurable_truncNorm (𝕜 := 𝕜) N r hΦ).indicator hA).aestronglyMeasurable
    (fun b ↦ Set.indicator_nonneg (fun _ _ ↦ truncNorm_nonneg) b) hρA
    (fun b hb ↦ Set.indicator_of_notMem hb _)
    (fun b hb ↦ by rw [Set.indicator_of_mem hb]; exact (hAψ b hb).2.1) hG hpair (fun b ↦ ?_)
    (enorm_indicator_rpow_le_re_inner_testFn (ENNReal.toReal_pos
      (ENNReal.HolderConjugate.ne_zero q q') hq) hr hr2 N hs Φ hpos)
    (eLpNorm_testFn_le hr hr2 N hs Φ hpos)
  rw [inner_testFn, RCLike.ofReal_re]
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ Real.rpow_nonneg truncNorm_nonneg _) _)
    (integral_nonneg fun x ↦ by positivity)

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
  refine TauCeti.eLpNorm_le_of_forall_eLpNorm_indicator_le hψ.aestronglyMeasurable hA (fun k ↦
    eLpNorm_indicator_truncNorm_le hq hr hr2 hΦ hM N (hA k)
      ((measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top ρ k)).ne
      (by positivity) fun b hb ↦ hb.2) (ae_of_all _ fun b hb ↦ ?_)
  -- Every `b` with `ψ b > 0` lies in `A k` for all large `k`.
  have hpos : 0 < ψ b := truncNorm_nonneg.lt_of_ne' hb
  filter_upwards [eventually_mem_spanningSets ρ b,
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_le_nhds hpos),
    eventually_ge_atTop ⌈ψ b⌉₊, eventually_ge_atTop ⌈‖Φ b‖⌉₊] with k h1 h2 h3 h4
  have h3' : ψ b ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast h3)
  have h4' : ‖Φ b‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast h4)
  exact ⟨h1, h2, h3', h4'⟩

end Core

/-! ### Monotone convergence in the truncation height -/

private theorem truncNorm_mono {r : ℝ≥0∞} (hr2 : 2 ≤ r) (u : Lp E 2 μ) :
    Monotone fun N : ℕ ↦ truncNorm (𝕜 := 𝕜) (N : ℝ≥0) r u := fun N N' hN ↦ by
  refine ENNReal.toReal_mono (eLpNorm_truncLp_ne_top _ hr2 u) (eLpNorm_mono_ae
    (Lp.aestronglyMeasurable _) ?_)
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u,
    coeFn_truncLp (𝕜 := 𝕜) (N' : ℝ≥0) le_rfl u] with x hx hx'
  rw [hx, hx', TauCeti.norm_truncPow _ one_pos, TauCeti.norm_truncPow _ one_pos, Real.rpow_one,
    Real.rpow_one]
  exact min_le_min_left _ (by exact_mod_cast hN)

/-- `‖u‖_r` is the supremum of the norms `‖u_N‖_r` of the truncations of `u`. -/
private theorem eLpNorm_eq_iSup_truncNorm {r : ℝ≥0∞} (hr2 : 2 ≤ r) (u : Lp E 2 μ) :
    eLpNorm u r μ = ⨆ N : ℕ, ENNReal.ofReal (truncNorm (𝕜 := 𝕜) (N : ℝ≥0) r u) := by
  have hae : ∀ᵐ x ∂μ, ∀ N : ℕ, ‖truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u x‖ₑ =
      ENNReal.ofReal (min ‖u x‖ N) := by
    filter_upwards [ae_all_iff.2 fun N : ℕ ↦ coeFn_truncLp (𝕜 := 𝕜) (N : ℝ≥0) le_rfl u]
      with x hx N
    rw [hx N, ← ofReal_norm, TauCeti.norm_truncPow _ one_pos, Real.rpow_one, NNReal.coe_natCast]
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

/-! ### The exponent `r = ∞`

At `r = ∞` the dual exponent is `r' = 1`, and the truncated powers `g = g_{N,s}(u)`, of length
`min (‖u‖, N) ^ s`, are the test functions in space after normalization in `L¹`. The ratio
`⟪u, g⟫ / ‖g‖₁ = ∫ ‖u‖ min (‖u‖, N) ^ s / ∫ min (‖u‖, N) ^ s` is a weighted average of `‖u‖`
whose weight concentrates, as `s → ∞`, where `min (‖u‖, N)` is close to its essential supremum
`‖u_N‖_∞`. -/

/-- The exponents `s = m + 2` along which the truncated powers are taken at `r = ∞`. -/
private theorem one_le_natCast_add_two (m : ℕ) : (1 : ℝ) ≤ m + 2 := by
  linarith [m.cast_nonneg (α := ℝ)]

/-- The pairing `⟪u, g_{N,s}(u)⟫ = ∫ ‖u‖ min (‖u‖, N) ^ s`, as a real number. -/
private def truncPair (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) : ℝ :=
  RCLike.re ⟪u, truncLp (𝕜 := 𝕜) N hs u⟫_𝕜

/-- The mass `‖g_{N,s}(u)‖₁ = ∫ min (‖u‖, N) ^ s` of the truncated power, as a real number. -/
private def truncMass (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) : ℝ :=
  (eLpNorm (truncLp (𝕜 := 𝕜) N hs u) 1 μ).toReal

/-- The ratio `∫ ‖u‖ min (‖u‖, N) ^ s / ∫ min (‖u‖, N) ^ s`. -/
private def truncRatio (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) : ℝ :=
  truncPair (𝕜 := 𝕜) N hs u / truncMass (𝕜 := 𝕜) N hs u

private theorem inner_truncLp_eq_truncPair (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    ⟪u, truncLp (𝕜 := 𝕜) N hs u⟫_𝕜 = ((truncPair (𝕜 := 𝕜) N hs u : ℝ) : 𝕜) := by
  rw [truncPair, inner_truncLp, RCLike.ofReal_re]

private theorem truncPair_eq (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (u : Lp E 2 μ) :
    truncPair (𝕜 := 𝕜) N hs u = ∫ x, ‖u x‖ * min ‖u x‖ N ^ s ∂μ := by
  rw [truncPair, inner_truncLp, RCLike.ofReal_re]

private theorem truncMass_nonneg {N : ℝ≥0} {s : ℝ} {hs : 1 ≤ s} {u : Lp E 2 μ} :
    0 ≤ truncMass (𝕜 := 𝕜) N hs u :=
  ENNReal.toReal_nonneg

private theorem truncRatio_nonneg {N : ℝ≥0} {s : ℝ} {hs : 1 ≤ s} {u : Lp E 2 μ} :
    0 ≤ truncRatio (𝕜 := 𝕜) N hs u := by
  rw [truncRatio, truncPair_eq]
  exact div_nonneg (integral_nonneg fun x ↦ by positivity) truncMass_nonneg

/-- For `s ≥ 2` the function `min (‖u‖, N) ^ s ≤ N ^ (s - 2) ‖u‖²` is integrable. -/
private theorem integrable_min_rpow (N : ℝ≥0) {s : ℝ} (hs : 2 ≤ s) (u : Lp E 2 μ) :
    Integrable (fun x ↦ min ‖u x‖ N ^ s) μ := by
  refine ((Lp.integrable_sq_norm u).const_mul ((N : ℝ) ^ (s - 2))).mono'
    (((Lp.stronglyMeasurable u).norm.measurable.min measurable_const).pow_const s
      |>.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact rpow_le_rpow_sub_two_mul_sq (le_min (norm_nonneg _) N.property) (min_le_right _ _)
    (min_le_left _ _) hs

/-- For `s ≥ 2` the truncated power has finite mass `‖g_{N,s}(u)‖₁ = ∫ min (‖u‖, N) ^ s`. -/
private theorem truncMass_eq (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (hs2 : 2 ≤ s) (u : Lp E 2 μ) :
    truncMass (𝕜 := 𝕜) N hs u = ∫ x, min ‖u x‖ N ^ s ∂μ := by
  rw [truncMass, eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _),
    ← ENNReal.toReal_ofReal (integral_nonneg fun x ↦ by positivity),
    ofReal_integral_eq_lintegral_ofReal (integrable_min_rpow N hs2 u)
      (Eventually.of_forall fun x ↦ by positivity)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [coeFn_truncLp (𝕜 := 𝕜) N hs u] with x hx
  rw [hx, ← ofReal_norm, TauCeti.norm_truncPow N (by linarith)]

private theorem measurable_truncRatio (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) :
    Measurable (fun b ↦ truncMass (𝕜 := 𝕜) N hs (Φ b)) ∧
      Measurable (fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b)) := by
  borelize ↥(Lp E 2 μ)
  have hJ : Measurable fun b ↦ truncMass (𝕜 := 𝕜) N hs (Φ b) :=
    ((TauCeti.lowerSemicontinuous_eLpNorm_Lp (μ := μ) Measure.AbsolutelyContinuous.rfl
      1).measurable.comp ((continuous_truncLp (𝕜 := 𝕜) N hs).comp_stronglyMeasurable
        hΦ).measurable).ennreal_toReal
  have hI : Measurable fun b ↦ truncPair (𝕜 := 𝕜) N hs (Φ b) :=
    ((RCLike.continuous_re.comp (continuous_id.inner (continuous_truncLp (𝕜 := 𝕜) N
      hs))).comp_stronglyMeasurable hΦ).measurable
  exact ⟨hJ, hI.div hJ⟩

/-- A pointwise inequality behind the limit of the ratio: for `0 ≤ v ≤ w`, `0 < t < t'` and
`s ≥ 2`, `t v ^ s + (t' - t) t' ^ s 1_{t' < v} - t ^ (s - 1) w² ≤ w v ^ s`. -/
private theorem mul_rpow_add_ite_sub_le {v w t t' s : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w)
    (ht : 0 < t) (htt' : t < t') (hs : 2 ≤ s) :
    t * v ^ s + ((if t' < v then (t' - t) * t' ^ s else 0) - t ^ (s - 1) * w ^ 2) ≤
      w * v ^ s := by
  have hvs : 0 ≤ v ^ s := Real.rpow_nonneg hv s
  have hw2 : 0 ≤ t ^ (s - 1) * w ^ 2 := by positivity
  have hmono : v * v ^ s ≤ w * v ^ s := mul_le_mul_of_nonneg_right hvw hvs
  rcases le_or_gt v t with hvt | htv
  · -- Below the level `t`, `t v ^ s ≤ t t ^ (s - 2) v² ≤ t ^ (s - 1) w²`.
    have hle : t * v ^ s ≤ t ^ (s - 1) * w ^ 2 := by
      calc t * v ^ s ≤ t * (t ^ (s - 2) * w ^ 2) :=
            mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_two_mul_sq hv hvt hvw hs) ht.le
        _ = t ^ (s - 1) * w ^ 2 := by
            rw [← mul_assoc, ← Real.rpow_one_add' ht.le (by linarith)]
            ring_nf
    rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ t' < v by linarith))]
    nlinarith [mul_nonneg (hv.trans hvw) hvs]
  rcases le_or_gt v t' with hvt' | ht'v
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ t' < v by linarith))]
    nlinarith
  · -- Above the level `t'`, `(t' - t) t' ^ s ≤ (v - t) v ^ s`.
    have hle : (t' - t) * t' ^ s ≤ (v - t) * v ^ s :=
      mul_le_mul (by linarith) (Real.rpow_le_rpow (by linarith) ht'v.le (by linarith))
        (Real.rpow_nonneg (by linarith) s) (by linarith)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ht'v)]
    nlinarith

private theorem measurableSet_lt_min (N : ℝ≥0) (u : Lp E 2 μ) (t' : ℝ) :
    MeasurableSet {x | t' < min ‖u x‖ N} :=
  measurableSet_lt measurable_const ((Lp.stronglyMeasurable u).norm.measurable.min measurable_const)

/-- For `s ≥ 2` and `t' ≥ 0`, the mass `∫ min (‖u‖, N) ^ s` is at least `t' ^ s` times the measure
of the level set `{t' < min (‖u‖, N)}`, when the latter is finite. -/
private theorem measureReal_mul_rpow_le_integral_min_rpow (N : ℝ≥0) (u : Lp E 2 μ) {t' s : ℝ}
    (ht'0 : 0 ≤ t') (hs : 2 ≤ s) (hPtop : μ {x | t' < min ‖u x‖ N} ≠ ∞) :
    μ.real {x | t' < min ‖u x‖ N} * t' ^ s ≤ ∫ x, min ‖u x‖ N ^ s ∂μ := by
  have hP := measurableSet_lt_min N u t'
  rw [← smul_eq_mul, ← integral_indicator_const _ hP]
  refine integral_mono ((integrable_indicator_iff hP).2 (integrableOn_const hPtop))
    (integrable_min_rpow N hs u) fun x ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with hx
  · exact Real.rpow_le_rpow ht'0 hx.le (by linarith)
  · exact Real.rpow_nonneg (le_min (norm_nonneg _) N.property) _

/-- The level set `{t' < min (‖u‖, N)}` below the essential supremum `‖u_N‖_∞` has positive and,
by Chebyshev's inequality for `u ∈ L²`, finite measure. -/
private theorem measureReal_lt_min_pos (N : ℝ≥0) (u : Lp E 2 μ) {t' : ℝ} (ht'0 : 0 < t')
    (ht' : t' < truncNorm (𝕜 := 𝕜) N ∞ u) :
    μ {x | t' < min ‖u x‖ N} ≠ ∞ ∧ 0 < μ.real {x | t' < min ‖u x‖ N} := by
  -- If `min (‖u‖, N) ≤ t'` almost everywhere, then `‖u_N‖_∞ ≤ t'`.
  have hP0 : μ {x | t' < min ‖u x‖ N} ≠ 0 := fun h0 ↦ by
    refine ht'.not_ge (ENNReal.toReal_le_of_le_ofReal ht'0.le ?_)
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0,
      coeFn_truncLp (𝕜 := 𝕜) N le_rfl u] with x hx hx'
    rw [hx', TauCeti.norm_truncPow N one_pos, Real.rpow_one]
    exact not_lt.1 hx
  have hPtop : μ {x | t' < min ‖u x‖ N} ≠ ∞ := by
    refine ne_top_of_le_ne_top ((Lp.memLp u).meas_ge_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (ε := t'.toNNReal) (by simp [ht'0])).ne (measure_mono fun x hx ↦ ?_)
    rw [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq, ← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal _ ht'0.le]
    exact hx.le.trans (min_le_left _ _)
  exact ⟨hPtop, ENNReal.toReal_pos hP0 hPtop⟩

/-- For `0 < t < t'`, `c > 0` and `C ≥ 0`, eventually `t ^ (s - 1) C ≤ (t' - t) t' ^ s c` along
`s = m + 2`, since `(t / t') ^ (m + 1) → 0`. -/
private theorem eventually_rpow_sub_one_mul_le {t t' c C : ℝ} (ht0 : 0 < t) (htt' : t < t')
    (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ m : ℕ in atTop, t ^ ((m : ℝ) + 2 - 1) * C ≤ (t' - t) * t' ^ ((m : ℝ) + 2) * c := by
  have ht'0 : 0 < t' := ht0.trans htt'
  have hε : 0 < (t' - t) * t' * c / (C + 1) := by
    have := sub_pos.2 htt'
    positivity
  filter_upwards [((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ht0.le ht'0.le)
    ((div_lt_one ht'0).2 htt')).comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_le_nhds hε)] with m hm
  have hlim : (t / t') ^ (m + 1) * C ≤ (t' - t) * t' * c := by
    calc (t / t') ^ (m + 1) * C ≤ (t' - t) * t' * c / (C + 1) * C :=
          mul_le_mul_of_nonneg_right hm hC
      _ ≤ (t' - t) * t' * c := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (add_pos_of_nonneg_of_pos hC one_pos)]
          exact mul_le_mul_of_nonneg_left (by linarith) (by have := sub_pos.2 htt'; positivity)
  have hs1 : (m : ℝ) + 2 - 1 = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hs' : (m : ℝ) + 2 = ((m + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hs1, hs', Real.rpow_natCast, Real.rpow_natCast, pow_succ t' (m + 1)]
  have hpow : t ^ (m + 1) = (t / t') ^ (m + 1) * t' ^ (m + 1) := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ht'0.ne')]
  rw [hpow]
  nlinarith [pow_pos ht'0 (m + 1)]

/-- The integrated form of the pointwise inequality above: with `P = {t' < min (‖u‖, N)}`,

`t ∫ min (‖u‖, N) ^ s + (t' - t) t' ^ s μ(P) - t ^ (s - 1) ‖u‖₂² ≤ ∫ ‖u‖ min (‖u‖, N) ^ s`. -/
private theorem mul_integral_add_sub_le (N : ℝ≥0) (u : Lp E 2 μ) {t t' s : ℝ} (ht0 : 0 < t)
    (htt' : t < t') (hs : 2 ≤ s) (hPtop : μ {x | t' < min ‖u x‖ N} ≠ ∞) :
    t * ∫ x, min ‖u x‖ N ^ s ∂μ + ((t' - t) * t' ^ s * μ.real {x | t' < min ‖u x‖ N} -
        t ^ (s - 1) * ∫ x, ‖u x‖ ^ 2 ∂μ) ≤ ∫ x, ‖u x‖ * min ‖u x‖ N ^ s ∂μ := by
  have hP := measurableSet_lt_min N u t'
  have hJ := integrable_min_rpow N hs u
  have h2 := Lp.integrable_sq_norm u
  have hind : Integrable ({x | t' < min ‖u x‖ N}.indicator fun _ ↦ (t' - t) * t' ^ s) μ :=
    (integrable_indicator_iff hP).2 (integrableOn_const hPtop)
  have hg : Integrable (fun x ↦ {x | t' < min ‖u x‖ N}.indicator
      (fun _ ↦ (t' - t) * t' ^ s) x - t ^ (s - 1) * ‖u x‖ ^ 2) μ := hind.sub (h2.const_mul _)
  have hint : Integrable (fun x ↦ t * min ‖u x‖ N ^ s +
      ({x | t' < min ‖u x‖ N}.indicator (fun _ ↦ (t' - t) * t' ^ s) x -
        t ^ (s - 1) * ‖u x‖ ^ 2)) μ := (hJ.const_mul t).add hg
  refine le_of_eq_of_le ?_ (integral_mono hint
    (integrable_norm_mul_min_rpow N (by linarith) u) fun x ↦ ?_)
  · rw [integral_add (hJ.const_mul t) hg, integral_sub hind (h2.const_mul _),
      integral_const_mul, integral_const_mul, integral_indicator_const _ hP, smul_eq_mul]
    ring
  · have hx := mul_rpow_add_ite_sub_le (le_min (norm_nonneg (u x)) N.property) (min_le_left _ _) ht0
      htt' hs
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    exact hx

/-- **The ratio eventually exceeds every level below the essential supremum.** If `t` is below
the essential supremum `‖u_N‖_∞` of `min (‖u‖, N)`, then
`t ≤ ∫ ‖u‖ min (‖u‖, N) ^ s / ∫ min (‖u‖, N) ^ s` for all large `s = m + 2`. -/
private theorem eventually_le_truncRatio (N : ℝ≥0) (u : Lp E 2 μ) {t : ℝ}
    (ht : t < truncNorm (𝕜 := 𝕜) N ∞ u) :
    ∀ᶠ m : ℕ in atTop, t ≤ truncRatio (𝕜 := 𝕜) N (one_le_natCast_add_two m) u := by
  rcases le_or_gt t 0 with ht0 | ht0
  · exact Eventually.of_forall fun m ↦ ht0.trans truncRatio_nonneg
  obtain ⟨t', htt', ht'⟩ := exists_between ht
  have ht'0 : 0 < t' := ht0.trans htt'
  obtain ⟨hPtop, hc⟩ := measureReal_lt_min_pos N u ht'0 ht'
  filter_upwards [eventually_rpow_sub_one_mul_le ht0 htt' hc
    (integral_nonneg fun x ↦ by positivity : 0 ≤ ∫ x, ‖u x‖ ^ 2 ∂μ)] with m hm
  have hs2 : (2 : ℝ) ≤ m + 2 := by linarith [m.cast_nonneg (α := ℝ)]
  have hkey := mul_integral_add_sub_le N u ht0 htt' hs2 hPtop
  -- The mass `J = ∫ min (‖u‖, N) ^ s` is at least `t' ^ s μ(P) > 0`.
  have hJpos : 0 < ∫ x, min ‖u x‖ N ^ ((m : ℝ) + 2) ∂μ :=
    (by positivity : 0 < μ.real {x | t' < min ‖u x‖ N} * t' ^ ((m : ℝ) + 2)).trans_le
      (measureReal_mul_rpow_le_integral_min_rpow N u ht'0.le hs2 hPtop)
  rw [truncRatio, truncPair_eq, truncMass_eq N _ hs2, le_div_iff₀ hJpos]
  linarith

section TopCore

/-- The weight `w = 1_A ψ ^ e / J` of the test functions `w b • g_{N,s}(Φ b)` at `r = ∞`, where
`ψ` is the ratio and `J` the mass of the truncated power of `Φ b`. -/
private def ratioWeight (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (Φ : β → Lp E 2 μ) (A : Set β) (e : ℝ) :
    β → ℝ :=
  A.indicator fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b) ^ e / truncMass (𝕜 := 𝕜) N hs (Φ b)

/-- Where the ratio `ψ` and the mass `J` are positive on `A`, the pairing of `Φ b` with the test
function `w b • g_{N,s}(Φ b)` is `(1_A ψ)(b) ^ (e + 1)`, since `⟪Φ b, g_{N,s}(Φ b)⟫ = ψ(b) J(b)`. -/
private theorem inner_ratioWeight_smul (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (Φ : β → Lp E 2 μ)
    {A : Set β} {e : ℝ} (he : 0 ≤ e)
    (hA : ∀ b ∈ A, 0 < truncRatio (𝕜 := 𝕜) N hs (Φ b) ∧ 0 < truncMass (𝕜 := 𝕜) N hs (Φ b))
    (b : β) :
    ⟪Φ b, ((ratioWeight (𝕜 := 𝕜) N hs Φ A e b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)⟫_𝕜 =
      ((A.indicator (fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b)) b ^ (e + 1) : ℝ) : 𝕜) := by
  rw [inner_smul_right, inner_truncLp_eq_truncPair, ← RCLike.ofReal_mul]
  congr 1
  by_cases hb : b ∈ A
  · obtain ⟨hψ, hJ⟩ := hA b hb
    have hI : truncPair (𝕜 := 𝕜) N hs (Φ b) =
        truncRatio (𝕜 := 𝕜) N hs (Φ b) * truncMass (𝕜 := 𝕜) N hs (Φ b) :=
      (div_mul_cancel₀ _ hJ.ne').symm
    rw [ratioWeight, Set.indicator_of_mem hb, Set.indicator_of_mem hb, hI,
      Real.rpow_add_one' hψ.le (by linarith)]
    field_simp
  · rw [ratioWeight, Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, zero_mul,
      Real.zero_rpow (by linarith)]

/-- Where the mass `J` is positive on `A`, the test function `w b • g_{N,s}(Φ b)` has
`‖w b • g_{N,s}(Φ b)‖₁ ≤ ‖(1_A ψ)(b)‖ ^ e`. -/
private theorem eLpNorm_ratioWeight_smul_le (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) (Φ : β → Lp E 2 μ)
    {A : Set β} (e : ℝ) (hA : ∀ b ∈ A, 0 < truncMass (𝕜 := 𝕜) N hs (Φ b)) (b : β) :
    eLpNorm (((ratioWeight (𝕜 := 𝕜) N hs Φ A e b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)) 1 μ ≤
      ‖‖A.indicator (fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b)) b‖ ^ e‖ₑ := by
  rw [eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul]
  by_cases hb : b ∈ A
  · have hJ := hA b hb
    have hψ : 0 ≤ truncRatio (𝕜 := 𝕜) N hs (Φ b) := truncRatio_nonneg
    have hfin : eLpNorm (truncLp (𝕜 := 𝕜) N hs (Φ b)) 1 μ =
        ENNReal.ofReal (truncMass (𝕜 := 𝕜) N hs (Φ b)) :=
      (ENNReal.ofReal_toReal fun h ↦ by simp [truncMass, h] at hJ).symm
    -- The key step: the weight times the mass is `ψ ^ e`.
    have hwJ : |ratioWeight (𝕜 := 𝕜) N hs Φ A e b| * truncMass (𝕜 := 𝕜) N hs (Φ b) =
        truncRatio (𝕜 := 𝕜) N hs (Φ b) ^ e := by
      simp only [ratioWeight, Set.indicator_of_mem hb]
      rw [abs_of_nonneg (div_nonneg (Real.rpow_nonneg hψ _) hJ.le), div_mul_cancel₀ _ hJ.ne']
    refine le_of_eq ?_
    calc _ = ENNReal.ofReal (|ratioWeight (𝕜 := 𝕜) N hs Φ A e b| *
          truncMass (𝕜 := 𝕜) N hs (Φ b)) := by
          rw [hfin, ← ofReal_norm, RCLike.norm_ofReal, ENNReal.ofReal_mul (abs_nonneg _)]
      _ = _ := by
          rw [hwJ, Set.indicator_of_mem hb, Real.norm_of_nonneg hψ,
            Real.eNorm_of_nonneg (Real.rpow_nonneg hψ _)]
  · rw [ratioWeight, Set.indicator_of_notMem hb]
    simp

variable {q q' : ℝ≥0∞} [q.HolderConjugate q']

/-- **The bound on a set of finite measure, at `r = ∞`.** If the ratio `ψ` lies in `[a, K]` and
the mass `J = ‖g_{N,s}(Φ b)‖₁` is at least `a > 0`, with `‖Φ b‖₂ ≤ K`, on a measurable set `A` of
finite measure, then testing against `G b = 1_A(b) ψ(b) ^ (q - 1) J(b)⁻¹ g_{N,s}(Φ b)`, for
which `⟪Φ b, G b⟫ = 1_A(b) ψ(b) ^ q` and `‖G b‖₁ = 1_A(b) ψ(b) ^ (q - 1)`, gives
`‖1_A ψ‖_q ≤ M`. -/
private theorem eLpNorm_indicator_truncRatio_le (hq : q ≠ ∞) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) 1 μ) q' ρ)
    (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) {A : Set β} (hA : MeasurableSet A) (hρA : ρ A ≠ ∞)
    {a K : ℝ} (ha : 0 < a)
    (hAψ : ∀ b ∈ A, a ≤ truncRatio (𝕜 := 𝕜) N hs (Φ b) ∧ truncRatio (𝕜 := 𝕜) N hs (Φ b) ≤ K ∧
      a ≤ truncMass (𝕜 := 𝕜) N hs (Φ b) ∧ ‖Φ b‖ ≤ K) :
    eLpNorm (A.indicator fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b)) q ρ ≤ M := by
  have hq1 : 1 ≤ q.toReal := by
    simpa using ENNReal.toReal_mono hq (ENNReal.HolderConjugate.one_le q q')
  obtain ⟨hJ, hψ⟩ := measurable_truncRatio (𝕜 := 𝕜) N hs hΦ
  have hpos : ∀ b ∈ A, 0 < truncRatio (𝕜 := 𝕜) N hs (Φ b) ∧
      0 < truncMass (𝕜 := 𝕜) N hs (Φ b) := fun b hb ↦
    ⟨ha.trans_le (hAψ b hb).1, ha.trans_le (hAψ b hb).2.2.1⟩
  set f := A.indicator fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b) with hf_def
  set w := ratioWeight (𝕜 := 𝕜) N hs Φ A (q.toReal - 1)
  set G := fun b ↦ ((w b : ℝ) : 𝕜) • truncLp (𝕜 := 𝕜) N hs (Φ b)
  have hwB : ∀ b ∈ A, |w b| ≤ K ^ (q.toReal - 1) / a := fun b hb ↦ by
    obtain ⟨-, h2, h3, -⟩ := hAψ b hb
    obtain ⟨hψb, hJb⟩ := hpos b hb
    simp only [w]
    rw [ratioWeight, Set.indicator_of_mem hb,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg hψb.le _) hJb.le)]
    exact div_le_div₀ (Real.rpow_nonneg (hψb.le.trans h2) _)
      (Real.rpow_le_rpow hψb.le h2 (by linarith)) ha h3
  obtain ⟨hG, hpair⟩ := integrable_smul_truncLp (𝕜 := 𝕜) hs hΦ hA hρA (w := w)
    (((hψ.pow_const _).div hJ).indicator hA) (fun b hb ↦ Set.indicator_of_notMem hb _) hwB
    fun b hb ↦ (hAψ b hb).2.2.2
  -- The pairing is `f ^ q`, with `f = 1_A ψ`.
  have hinner (b : β) : ⟪Φ b, G b⟫_𝕜 = ((f b ^ q.toReal : ℝ) : 𝕜) := by
    have h := inner_ratioWeight_smul N hs Φ (e := q.toReal - 1) (by linarith) hpos b
    rw [sub_add_cancel] at h
    exact h
  have hf0 : ∀ b, 0 ≤ f b := fun b ↦ Set.indicator_nonneg (fun _ _ ↦ truncRatio_nonneg) b
  refine eLpNorm_le_of_enorm_rpow_le_re_inner hq hM (hψ.indicator hA).aestronglyMeasurable hf0
    hρA (fun b hb ↦ Set.indicator_of_notMem hb _)
    (fun b hb ↦ by rw [hf_def, Set.indicator_of_mem hb]; exact (hAψ b hb).2.1) hG hpair
    (fun b ↦ ?_) (fun b ↦ ?_)
    (eLpNorm_ratioWeight_smul_le N hs Φ _ fun b hb ↦ (hpos b hb).2)
  · rw [hinner, RCLike.ofReal_re]
    exact Real.rpow_nonneg (hf0 b) _
  · rw [hinner, RCLike.ofReal_re, Real.eNorm_of_nonneg (hf0 b),
      ENNReal.ofReal_rpow_of_nonneg (hf0 b) (by linarith)]

/-- **Exhaustion, at `r = ∞`.** Exhausting `β` by the sets of finite measure where `ψ` lies in
`[1 / (k + 1), k]`, the mass `J` is at least `1 / (k + 1)` and `‖Φ b‖₂ ≤ k` bounds `‖ψ‖_q` by
`M`. -/
private theorem eLpNorm_truncRatio_le [SigmaFinite ρ] (hq : q ≠ ∞) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) 1 μ) q' ρ)
    (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) :
    eLpNorm (fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b)) q ρ ≤ M := by
  set ψ := fun b ↦ truncRatio (𝕜 := 𝕜) N hs (Φ b)
  set J := fun b ↦ truncMass (𝕜 := 𝕜) N hs (Φ b)
  obtain ⟨hJ, hψ⟩ := measurable_truncRatio (𝕜 := 𝕜) N hs hΦ
  set A : ℕ → Set β := fun k ↦ spanningSets ρ k ∩ ({b | 1 / ((k : ℝ) + 1) ≤ ψ b} ∩
    ({b | ψ b ≤ k} ∩ ({b | 1 / ((k : ℝ) + 1) ≤ J b} ∩ {b | ‖Φ b‖ ≤ k})))
  have hA (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_spanningSets ρ k).inter ((measurableSet_le measurable_const hψ).inter
      ((measurableSet_le hψ measurable_const).inter ((measurableSet_le measurable_const hJ).inter
        (measurableSet_le hΦ.norm.measurable measurable_const))))
  refine TauCeti.eLpNorm_le_of_forall_eLpNorm_indicator_le hψ.aestronglyMeasurable hA (fun k ↦
    eLpNorm_indicator_truncRatio_le hq hΦ hM N hs (hA k)
      ((measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top ρ k)).ne
      (by positivity) fun b hb ↦ ⟨hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2⟩)
    (ae_of_all _ fun b hb ↦ ?_)
  -- Where `ψ b ≠ 0`, also `J b ≠ 0`, since `ψ = I / J`; then `b ∈ A k` for all large `k`.
  have hpos : 0 < ψ b := truncRatio_nonneg.lt_of_ne' hb
  have hJpos : 0 < J b := by
    simp only [J]
    refine truncMass_nonneg.lt_of_ne' fun h0 ↦ hb ?_
    simp only [truncRatio, h0, div_zero]
  filter_upwards [eventually_mem_spanningSets ρ b,
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_le_nhds hpos),
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_le_nhds hJpos),
    eventually_ge_atTop ⌈ψ b⌉₊, eventually_ge_atTop ⌈‖Φ b‖⌉₊] with k h1 h2 h3 h4 h5
  have h4' : ψ b ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast h4)
  have h5' : ‖Φ b‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast h5)
  exact ⟨h1, h2, h4', h3, h5'⟩

/-- **The bound at `r = ∞` for each truncation.** The essential suprema `‖u_N‖_∞` of the
truncations `u_N` of `Φ b` have `L^q` norm at most `M`: `‖u_N‖_∞` is the limit of
`min (ψ_m, ‖u_N‖_∞)`, where
`ψ_m = ∫ ‖Φ b‖ min (‖Φ b‖, N) ^ (m + 2) / ∫ min (‖Φ b‖, N) ^ (m + 2)`, and each of these minima
has `L^q` norm at most `‖ψ_m‖_q ≤ M`. -/
private theorem eLpNorm_truncNorm_top_le [SigmaFinite ρ] (hq : q ≠ ∞) {Φ : β → Lp E 2 μ}
    (hΦ : StronglyMeasurable Φ) {M : ℝ≥0∞}
    (hM : ∀ G : β → Lp E 2 μ, Integrable G ρ → Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ →
      ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) 1 μ) q' ρ)
    (N : ℝ≥0) : eLpNorm (fun b ↦ truncNorm (𝕜 := 𝕜) N ∞ (Φ b)) q ρ ≤ M := by
  have hS : Measurable fun b ↦ truncNorm (𝕜 := 𝕜) N ∞ (Φ b) := measurable_truncNorm N ∞ hΦ
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun m b ↦ min (truncRatio (𝕜 := 𝕜) N (one_le_natCast_add_two m) (Φ b))
      (truncNorm (𝕜 := 𝕜) N ∞ (Φ b)))
    (Eventually.of_forall fun m ↦ (eLpNorm_mono_real
      (((measurable_truncRatio N _ hΦ).2.min hS).aestronglyMeasurable) fun b ↦ ?_).trans
        (eLpNorm_truncRatio_le hq hΦ hM N (one_le_natCast_add_two m)))
    (fun m ↦ ((measurable_truncRatio N _ hΦ).2.min hS).aestronglyMeasurable)
    hS.aestronglyMeasurable (ae_of_all _ fun b ↦ ?_)
  · rw [Real.norm_of_nonneg (le_min truncRatio_nonneg truncNorm_nonneg)]
    exact min_le_left _ _
  · refine tendsto_order.2 ⟨fun t ht ↦ ?_, fun t ht ↦
      Eventually.of_forall fun m ↦ (min_le_right _ _).trans_lt ht⟩
    obtain ⟨t₁, htt₁, ht₁⟩ := exists_between ht
    filter_upwards [eventually_le_truncRatio N (Φ b) ht₁] with m hm
    exact lt_min (htt₁.trans_le hm) ht

end TopCore

/-! ### Minkowski's inequality -/

section Elementary

variable {F : Type*} [NormedAddCommGroup F] {p q r : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Minkowski's inequality for mixed norms.** For `1 ≤ q` and `1 ≤ r`, the `L^q_b L^r_x` mixed
norm of the sum of two almost everywhere strongly measurable families of `Lᵖ` functions is at most
the sum of their mixed norms. -/
theorem eLpNorm_eLpNorm_add_le {u v : β → Lp F p μ} (hu : AEStronglyMeasurable u ρ)
    (hv : AEStronglyMeasurable v ρ) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    eLpNorm (fun b ↦ eLpNorm (u b + v b) r μ) q ρ ≤
      eLpNorm (fun b ↦ eLpNorm (u b) r μ) q ρ + eLpNorm (fun b ↦ eLpNorm (v b) r μ) q ρ :=
  calc _ ≤ eLpNorm (fun b ↦ eLpNorm (u b) r μ + eLpNorm (v b) r μ) q ρ :=
        eLpNorm_mono_eNorm ((hu.add hv).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun b ↦ by
            simp only [eNorm_eq_self, Pi.add_apply]
            rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
            exact eLpNorm_add_le hr
    _ ≤ _ := eLpNorm_add_le hq

end Elementary

/-! ### The norming theorem -/

variable {q q' r r' : ℝ≥0∞} [q.HolderConjugate q'] [r.HolderConjugate r']

/-- **Norming mixed norms by `L²`-valued test functions.** Let `1 ≤ q < ∞` and `2 ≤ r ≤ ∞`, with
Hölder conjugates `q'` and `r'`, and let `ρ` be σ-finite. If an almost everywhere strongly
measurable `Φ : β → L²(X, μ)` satisfies

`|∫ ⟪Φ b, G b⟫ dρ(b)| ≤ M ‖G‖_{L^{q'}_b L^{r'}_x}`

for every integrable `G : β → L²(X, μ)` for which `b ↦ ⟪Φ b, G b⟫` is integrable, then
`‖Φ‖_{L^q_b L^r_x} ≤ M`. At `r = ∞` the test functions are measured in `L^{q'}_b L¹_x`. -/
theorem AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le
    [SigmaFinite ρ] (hq : q ≠ ∞) (hr2 : 2 ≤ r) {Φ : β → Lp E 2 μ}
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
  rcases eq_or_ne r ∞ with rfl | hr
  · obtain rfl : r' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ r').1 rfl
    exact eLpNorm_truncNorm_top_le hq hΦ' hM' _
  · exact eLpNorm_truncNorm_le hq hr hr2 hΦ' hM' _

/-! ### Reflection of the parameter -/

/-- Reflecting the parameter, `b ↦ -b`, preserves mixed norms when the measure `ρ` is invariant
under negation, as Lebesgue measure on the time line is. -/
theorem AEStronglyMeasurable.eLpNorm_eLpNorm_comp_neg [InvolutiveNeg β] [MeasurableNeg β]
    [ρ.IsNegInvariant] {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Φ : β → Lp F p μ} (hΦ : AEStronglyMeasurable Φ ρ) {q r : ℝ≥0∞} :
    eLpNorm (fun b ↦ eLpNorm (Φ (-b)) r μ) q ρ = eLpNorm (fun b ↦ eLpNorm (Φ b) r μ) q ρ :=
  eLpNorm_comp_measurePreserving (g := fun b ↦ eLpNorm (Φ b) r μ)
    (hΦ.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable (Measure.measurePreserving_neg ρ)

end MeasureTheory
