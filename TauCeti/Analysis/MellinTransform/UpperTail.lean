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
integrability: in that case all the totalized integrals vanish. Absolute convergence requires
local integrability on the closed ray, including its boundary at one. Uniformly bounded kernels
have integral norm at most `C / re s` on `0 < re s`.

The indicator estimates also allow an arbitrary cutoff at infinity and a positive cutoff near
zero. Together with `mellin_indicator_Ici`, these are the Mellin side conditions used for upper
tails in partial summation and in the fractional-part formula for the Riemann zeta function.

## Main results

* `TauCeti.differentiableOn_integral_mul_cpow_of_isBigO`: holomorphy from an upper power bound.
* `TauCeti.integrableOn_mul_cpow_of_isBigO`: absolute convergence with local integrability.
* `TauCeti.norm_integral_mul_cpow_le_of_bound`: the explicit bound for a bounded kernel.
-/

public section

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace TauCeti

/-- Cutting a kernel off below any real threshold preserves its power bound at infinity. -/
theorem isBigO_indicator_Ici_atTop {F : Type*} [Norm F] [Zero F]
    {g : ℝ → F} {a r : ℝ}
    (hO : g =O[atTop] fun t ↦ t ^ r) :
    (Set.Ici a).indicator g =O[atTop] fun t ↦ t ^ r := by
  refine hO.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop a] with t ht
  exact (Set.indicator_of_mem (Set.mem_Ici.mpr ht) g).symm

/-- A kernel cut off below a positive threshold vanishes near zero, so has any power bound. -/
theorem isBigO_indicator_Ici_nhdsGT_zero {F : Type*} [SeminormedAddGroup F]
    (g : ℝ → F) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (Set.Ici a).indicator g =O[𝓝[>] 0] fun t : ℝ ↦ t ^ b := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT ha] with t ht
  simp only [Set.indicator_of_notMem (Set.notMem_Ici.mpr ht.2) g, norm_zero, zero_mul, le_refl]

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
      (mellin_differentiableAt_of_isBigO_rpow (a := -r)
        (hg.indicator_of_isClosed measurableSet_Ici.nullMeasurableSet
          isOpen_Ioi.isLocallyClosed isClosed_Ici Set.inter_subset_right
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
            exact fun hn ↦ (hn ht).elim))
        (by rw [neg_neg]; exact isBigO_indicator_Ici_atTop hO) (by simpa using hs)
        (isBigO_indicator_Ici_nhdsGT_zero g zero_lt_one _) (sub_one_lt (-s).re)).comp s
        differentiableAt_id.neg
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
  have hconv : MellinConvergent ((Set.Ici 1).indicator g) (-s) :=
    mellinConvergent_of_isBigO_rpow (a := -r)
      (hg.indicator_of_isClosed measurableSet_Ici.nullMeasurableSet
          isOpen_Ioi.isLocallyClosed isClosed_Ici Set.inter_subset_right
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
            exact fun hn ↦ (hn ht).elim))
      (by rw [neg_neg]; exact isBigO_indicator_Ici_atTop hO) (by simpa using hs)
      (isBigO_indicator_Ici_nhdsGT_zero g zero_lt_one _) (sub_one_lt (-s).re)
  refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioi
  dsimp only
  rw [Set.indicator_of_mem (Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le), smul_eq_mul, mul_comm,
    neg_add']

/-- If `‖g t‖ ≤ C` on `(1, ∞)`, then `‖∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))‖ ≤ C / s.re` on
`Re(s) > 0`. -/
theorem norm_integral_mul_cpow_le_of_bound {g : ℝ → ℂ} {C : ℝ}
    (hg : ∀ t ∈ Set.Ioi (1 : ℝ), ‖g t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))‖ ≤ C / s.re := by
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), C * t ^ (-(s.re + 1)) := by
      refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt
        (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
      simp only [neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (hg t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
    _ = C / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
        Real.one_rpow]
      ring

end TauCeti
