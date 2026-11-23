/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Upper Mellin tails

Integrating a kernel against `t ^ (-(s + 1))` over `(1, ∞)` gives a holomorphic function on
`r < re s` when the kernel is `O(t ^ r)` at infinity. This holds even without local
integrability: in that case all the totalized integrals vanish. Absolute convergence and
differentiation under the integral sign require local integrability on the closed ray, including
its boundary at one. On `0 < re s`, a measurable kernel bounded by `C` on `(a, ∞)`, `a > 0`, gives
an absolutely convergent integral over `(a, ∞)` of norm at most `C a ^ (-re s) / re s`.

The proofs cut off kernels below one and use `mellin_indicator_Ici` to express the resulting
integrals as Mellin transforms. These upper tails occur in partial summation and in the
fractional-part formula for the Riemann zeta function.

## Motivation and provenance

These upper tails control analytic Abel remainders in Dirichlet-series continuation. One
application motivating the general kernel interface is Matteo Cipollina's
[PNT+ Abel-kernel formalization](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/e316efa96ec1faa14c06dccf912b7f1bcefb4d2a/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelKernel.lean).
The bounded-kernel estimate is extracted from the native partial-sum norm estimate in
`TauCeti.NumberTheory.LSeries.SumCoeff`; the proofs use the existing Mellin suppliers.

## Main results

* `TauCeti.differentiableOn_integral_mul_cpow_of_isBigO`: holomorphy from an upper power bound.
* `TauCeti.integrableOn_mul_cpow_of_isBigO` and
  `TauCeti.integrableOn_mul_log_mul_cpow_of_isBigO`: absolute convergence of the upper tail and its
  `log t`-weighted companion with local integrability.
* `TauCeti.hasDerivAt_integral_mul_cpow_of_isBigO`: complex derivative of the upper tail on
  `r < Re s` with local integrability.
* `TauCeti.integrableOn_mul_cpow_of_bound`: absolute convergence for a bounded kernel.
* `TauCeti.norm_integral_mul_cpow_le_of_bound`: the explicit bound for a bounded kernel.
-/

public section

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace TauCeti

/-- The normalized cutoff gives Mellin convergence, log-weighted convergence, and the complex
derivative in its strip. -/
private theorem upperTail_mellin_regular {g : ℝ → ℂ} {r : ℝ} {s : ℂ}
    (hg : LocallyIntegrableOn g (Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r)
    (hs : r < s.re) :
    MellinConvergent ((Ici 1).indicator g) (-s) ∧
      MellinConvergent (fun t : ℝ ↦ Real.log t • (Ici 1).indicator g t) (-s) ∧
      HasDerivAt (mellin ((Ici 1).indicator g))
        (mellin (fun t : ℝ ↦ Real.log t • (Ici 1).indicator g t) (-s)) (-s) := by
  have hlocal : LocallyIntegrableOn ((Ici 1).indicator g) (Ioi 0) :=
    hg.indicator_of_isClosed measurableSet_Ici.nullMeasurableSet
      isOpen_Ioi.isLocallyClosed isClosed_Ici Set.inter_subset_right (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact fun hn ↦ (hn ht).elim)
  have htop : (Ici 1).indicator g =O[atTop] fun t ↦ t ^ (-(-r)) := by
    rw [neg_neg]
    refine hO.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact (Set.indicator_of_mem ht g).symm
  have hbot : (Ici 1).indicator g =O[𝓝[>] 0] fun t ↦ t ^ (-((-s).re - 1)) := by
    apply IsBigO.of_bound 0
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    simp only [Set.indicator_of_notMem (Set.notMem_Ici.mpr ht.2) g,
      norm_zero, zero_mul, le_refl]
  have hstrip : (-s).re < -r := by simpa using hs
  exact ⟨mellinConvergent_of_isBigO_rpow hlocal htop hstrip hbot (sub_one_lt (-s).re),
    mellin_hasDerivAt_of_isBigO_rpow hlocal htop hstrip hbot (sub_one_lt (-s).re)⟩

/-- **Holomorphy of an integral against `t ^ (-(s + 1))`.** If `g` is `O(t ^ r)` at infinity,
then `s ↦ ∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))` is complex-differentiable on `r < Re s`.
No local-integrability hypothesis is needed: if it fails, all these Bochner integrals are zero. -/
theorem differentiableOn_integral_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hO : g =O[atTop] fun t ↦ t ^ r) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} := by
  classical
  by_cases hg : LocallyIntegrableOn g (Set.Ici 1)
  · intro s hs
    have hmellin : DifferentiableAt ℂ (fun z : ℂ ↦ mellin ((Set.Ici 1).indicator g) (-z)) s :=
      (upperTail_mellin_regular hg hO hs).2.2.differentiableAt.comp s differentiableAt_id.neg
    simpa only [mellin_indicator_Ici _ zero_le_one, smul_eq_mul, neg_add', mul_comm] using
      hmellin.differentiableWithinAt
  · have hzero (s : ℂ) :
        (∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))) = 0 := by
      apply integral_undef
      intro hi
      apply hg
      have hi' : IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) :=
        (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
      have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s + 1)) (Set.Ici 1) :=
        Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦
          Or.inl (by simpa using (zero_lt_one.trans_le (Set.mem_Ici.mp ht)))
      refine (hi'.locallyIntegrableOn.mul_continuousOn hc isClosed_Ici.isLocallyClosed).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
        (zero_lt_one.trans_le (Set.mem_Ici.mp ht)).ne')]
      simp
    have heq : (fun s : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))) =
        fun _ ↦ (0 : ℂ) := funext hzero
    rw [heq]
    exact differentiableOn_const 0

/-- If `g` is locally integrable on `[1, ∞)` and `O(t ^ r)` at infinity, then
`t ↦ g t * t ^ (-(s + 1))` is integrable on `(1, ∞)` for `r < Re s`. -/
theorem integrableOn_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r) {s : ℂ}
    (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hconv := (upperTail_mellin_regular hg hO hs).1
  refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioi
  dsimp only
  rw [Set.indicator_of_mem (Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le), smul_eq_mul, mul_comm,
    neg_add']

/-- If `g` is locally integrable on `[1, ∞)` and `O(t ^ r)` at infinity, then
`t ↦ g t * log t * t ^ (-(s + 1))` is integrable on `(1, ∞)` for `r < Re s`. -/
theorem integrableOn_mul_log_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r) {s : ℂ}
    (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * (Real.log t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hconv := (upperTail_mellin_regular hg hO hs).2.1
  refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioi
  dsimp only
  rw [Set.indicator_of_mem (Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le), Complex.real_smul,
    smul_eq_mul, neg_add']
  ring

/-- **Derivative of an integral against `t ^ (-(s + 1))`.** If `g` is locally integrable on
`[1, ∞)` and `O(t ^ r)` at infinity, then on `r < Re s` the complex derivative of
`z ↦ ∫ t in Set.Ioi 1, g t * t ^ (-(z + 1))` at `s` is
`-∫ t in Set.Ioi 1, g t * log t * t ^ (-(s + 1))`. -/
theorem hasDerivAt_integral_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r) {s : ℂ}
    (hs : r < s.re) :
    HasDerivAt (fun z : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(z + 1)))
      (-(∫ t in Set.Ioi (1 : ℝ), g t * (Real.log t : ℂ) * (t : ℂ) ^ (-(s + 1)))) s := by
  have hd : HasDerivAt (fun z : ℂ ↦ mellin ((Set.Ici 1).indicator g) (-z))
      (mellin (fun t : ℝ ↦ Real.log t • (Set.Ici 1).indicator g t) (-s) * -1) s :=
    (upperTail_mellin_regular hg hO hs).2.2.comp s (hasDerivAt_id s).neg
  have hfun : (fun z : ℂ ↦ mellin ((Set.Ici 1).indicator g) (-z)) =
      fun z : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(z + 1)) := by
    ext z
    simp only [mellin_indicator_Ici _ zero_le_one, smul_eq_mul, neg_add', mul_comm]
  rw [hfun] at hd
  refine hd.congr_deriv ?_
  have hind : (fun t : ℝ ↦ Real.log t • (Set.Ici 1).indicator g t) =
      (Set.Ici 1).indicator fun t : ℝ ↦ Real.log t • g t := by
    ext t
    by_cases ht : t ∈ Set.Ici (1 : ℝ) <;> simp [ht]
  rw [hind, mellin_indicator_Ici _ zero_le_one, mul_neg, mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [Complex.real_smul, smul_eq_mul, neg_add']
  ring

/-- The pointwise domination of `g t * t ^ (-(s + 1))` by `C * t ^ (-(re s + 1))` on `(a, ∞)`. -/
private theorem ae_norm_mul_cpow_le_of_bound {g : ℝ → ℂ} {C a : ℝ} (ha : 0 < a)
    (hg : ∀ t ∈ Set.Ioi a, ‖g t‖ ≤ C) (s : ℂ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi a), ‖g t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * t ^ (-(s.re + 1)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans ht)]
  simp only [neg_re, add_re, one_re]
  exact mul_le_mul_of_nonneg_right (hg t ht) (Real.rpow_nonneg (ha.trans ht).le _)

/-- If `g` is measurable with `‖g t‖ ≤ C` on `(a, ∞)`, `a > 0`, then `t ↦ g t * t ^ (-(s + 1))` is
integrable on `(a, ∞)` for `0 < Re s`. -/
theorem integrableOn_mul_cpow_of_bound {g : ℝ → ℂ} {C a : ℝ} (ha : 0 < a)
    (hgm : AEStronglyMeasurable g (volume.restrict (Set.Ioi a)))
    (hg : ∀ t ∈ Set.Ioi a, ‖g t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi a) :=
  Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) ha).const_mul C)
    (hgm.mul (measurable_ofReal.pow_const _).aestronglyMeasurable)
    (ae_norm_mul_cpow_le_of_bound ha hg s)

/-- If `‖g t‖ ≤ C` on `(a, ∞)`, `a > 0`, then
`‖∫ t in Set.Ioi a, g t * t ^ (-(s + 1))‖ ≤ C * a ^ (-s.re) / s.re` on `Re(s) > 0`. -/
theorem norm_integral_mul_cpow_le_of_bound {g : ℝ → ℂ} {C a : ℝ} (ha : 0 < a)
    (hg : ∀ t ∈ Set.Ioi a, ‖g t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi a, g t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * a ^ (-s.re) / s.re := by
  calc
    _ ≤ ∫ t in Set.Ioi a, C * t ^ (-(s.re + 1)) :=
      norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt
        (by linarith : -(s.re + 1) < -1) ha).const_mul C) (ae_norm_mul_cpow_le_of_bound ha hg s)
    _ = C * a ^ (-s.re) / s.re := by
      have hexp : -(s.re + 1) + 1 = -s.re := by ring
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha, hexp, neg_div_neg_eq,
        mul_div_assoc]

end TauCeti
