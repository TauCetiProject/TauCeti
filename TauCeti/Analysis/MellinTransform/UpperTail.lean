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

Integrating a kernel against `t ^ (-(s + 1))` over `(a, ∞)` with `0 < a` gives a holomorphic
function on `r < re s` when the kernel is `O(t ^ r)` at infinity. This holds even without local
integrability: in that case all the totalized integrals vanish. Absolute convergence requires
local integrability on the closed ray `[a, ∞)`, including its boundary at `a`. Uniformly bounded
kernels have integral norm at most `C * a ^ (-re s) / re s` on `0 < re s` (and `C / re s` when
`a = 1`).

The proofs cut off kernels below `a` and use `mellin_indicator_Ici` to express the resulting
integrals as Mellin transforms. These upper tails occur in partial summation, in the
fractional-part formula for the Riemann zeta function, and in first-order Euler–Maclaurin
remainders at arbitrary positive cutoffs.

## Motivation and provenance

These upper tails control analytic Abel remainders in Dirichlet-series continuation. One
application motivating the general kernel interface is Matteo Cipollina's
[PNT+ Abel-kernel formalization](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/e316efa96ec1faa14c06dccf912b7f1bcefb4d2a/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelKernel.lean).
The bounded-kernel estimate is extracted from the native partial-sum norm estimate in
`TauCeti.NumberTheory.LSeries.SumCoeff`; the proofs use the existing Mellin suppliers.

## Main results

* `TauCeti.differentiableOn_integral_Ioi_mul_cpow_of_isBigO`,
  `TauCeti.differentiableOn_integral_mul_cpow_of_isBigO`: holomorphy from an upper power bound on
  `(a, ∞)` (`0 < a`) and on `(1, ∞)`.
* `TauCeti.integrableOn_Ioi_mul_cpow_of_isBigO`, `TauCeti.integrableOn_mul_cpow_of_isBigO`:
  absolute convergence with local integrability on `[a, ∞)` and on `[1, ∞)`.
* `TauCeti.norm_integral_Ioi_mul_cpow_le_of_bound`, `TauCeti.norm_integral_mul_cpow_le_of_bound`:
  the explicit norm bound for a bounded kernel on `(a, ∞)` and on `(1, ∞)`.
-/

public section

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace TauCeti

/-- An upper-ray cutoff at `0 < a` gives both Mellin convergence and differentiability in its
strip. -/
private theorem upperTail_mellin_regular {a : ℝ} (ha : 0 < a) {g : ℝ → ℂ} {r : ℝ} {s : ℂ}
    (hg : LocallyIntegrableOn g (Ici a)) (hO : g =O[atTop] fun t ↦ t ^ r)
    (hs : r < s.re) :
    MellinConvergent ((Ici a).indicator g) (-s) ∧
      DifferentiableAt ℂ (mellin ((Ici a).indicator g)) (-s) := by
  have hlocal : LocallyIntegrableOn ((Ici a).indicator g) (Ioi 0) :=
    hg.indicator_of_isClosed measurableSet_Ici.nullMeasurableSet
      isOpen_Ioi.isLocallyClosed isClosed_Ici Set.inter_subset_right (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact fun hn ↦ (hn ht).elim)
  have htop : (Ici a).indicator g =O[atTop] fun t ↦ t ^ (-(-r)) := by
    rw [neg_neg]
    refine hO.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop a] with t ht
    exact (Set.indicator_of_mem ht g).symm
  have hbot : (Ici a).indicator g =O[𝓝[>] 0] fun t ↦ t ^ (-((-s).re - 1)) := by
    apply IsBigO.of_bound 0
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    simp only [Set.indicator_of_notMem (Set.notMem_Ici.mpr ht.2) g,
      norm_zero, zero_mul, le_refl]
  have hstrip : (-s).re < -r := by simpa using hs
  exact ⟨mellinConvergent_of_isBigO_rpow hlocal htop hstrip hbot (sub_one_lt (-s).re),
    mellin_differentiableAt_of_isBigO_rpow hlocal htop hstrip hbot (sub_one_lt (-s).re)⟩

/-- **Holomorphy of an upper-tail integral against `t ^ (-(s + 1))`.** If `0 < a` and `g` is
`O(t ^ r)` at infinity, then `s ↦ ∫ t in Set.Ioi a, g t * t ^ (-(s + 1))` is complex-differentiable
on `r < Re s`. No local-integrability hypothesis is needed: if it fails, all these Bochner
integrals are zero. -/
theorem differentiableOn_integral_Ioi_mul_cpow_of_isBigO {a : ℝ} (ha : 0 < a) {g : ℝ → ℂ} {r : ℝ}
    (hO : g =O[atTop] fun t ↦ t ^ r) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t in Set.Ioi a, g t * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} := by
  classical
  by_cases hg : LocallyIntegrableOn g (Set.Ici a)
  · intro s hs
    have hmellin : DifferentiableAt ℂ (fun z : ℂ ↦ mellin ((Set.Ici a).indicator g) (-z)) s :=
      (upperTail_mellin_regular ha hg hO hs).2.comp s differentiableAt_id.neg
    simpa only [mellin_indicator_Ici _ ha.le, smul_eq_mul, neg_add', mul_comm] using
      hmellin.differentiableWithinAt
  · have hzero (s : ℂ) :
        (∫ t in Set.Ioi a, g t * (t : ℂ) ^ (-(s + 1))) = 0 := by
      apply integral_undef
      intro hi
      apply hg
      have hi' : IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ici a) :=
        (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
      have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s + 1)) (Set.Ici a) :=
        Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦
          Or.inl (by simpa using (ha.trans_le (Set.mem_Ici.mp ht)))
      refine (hi'.locallyIntegrableOn.mul_continuousOn hc isClosed_Ici.isLocallyClosed).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
        (ha.trans_le (Set.mem_Ici.mp ht)).ne')]
      simp
    have heq : (fun s : ℂ ↦ ∫ t in Set.Ioi a, g t * (t : ℂ) ^ (-(s + 1))) =
        fun _ ↦ (0 : ℂ) := funext hzero
    rw [heq]
    exact differentiableOn_const 0

/-- **Holomorphy of an integral against `t ^ (-(s + 1))`.** If `g` is `O(t ^ r)` at infinity,
then `s ↦ ∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))` is complex-differentiable on `r < Re s`.
No local-integrability hypothesis is needed: if it fails, all these Bochner integrals are zero. -/
theorem differentiableOn_integral_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hO : g =O[atTop] fun t ↦ t ^ r) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} :=
  differentiableOn_integral_Ioi_mul_cpow_of_isBigO zero_lt_one hO

/-- If `0 < a` and `g` is locally integrable on `[a, ∞)` and `O(t ^ r)` at infinity, then
`t ↦ g t * t ^ (-(s + 1))` is integrable on `(a, ∞)` for `r < Re s`. -/
theorem integrableOn_Ioi_mul_cpow_of_isBigO {a : ℝ} (ha : 0 < a) {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici a)) (hO : g =O[atTop] fun t ↦ t ^ r) {s : ℂ}
    (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi a) := by
  have hconv := (upperTail_mellin_regular ha hg hO hs).1
  refine (hconv.mono_set (Set.Ioi_subset_Ioi ha.le)).congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioi
  dsimp only
  rw [Set.indicator_of_mem (Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le), smul_eq_mul, mul_comm,
    neg_add']

/-- If `g` is locally integrable on `[1, ∞)` and `O(t ^ r)` at infinity, then
`t ↦ g t * t ^ (-(s + 1))` is integrable on `(1, ∞)` for `r < Re s`. -/
theorem integrableOn_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r) {s : ℂ}
    (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
  integrableOn_Ioi_mul_cpow_of_isBigO zero_lt_one hg hO hs

/-- If `0 < a` and `‖g t‖ ≤ C` on `(a, ∞)`, then
`‖∫ t in Set.Ioi a, g t * t ^ (-(s + 1))‖ ≤ C * a ^ (-s.re) / s.re` on `Re(s) > 0`. -/
theorem norm_integral_Ioi_mul_cpow_le_of_bound {a : ℝ} (ha : 0 < a) {g : ℝ → ℂ} {C : ℝ}
    (hg : ∀ t ∈ Set.Ioi a, ‖g t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi a, g t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * a ^ (-s.re) / s.re := by
  calc
    _ ≤ ∫ t in Set.Ioi a, C * t ^ (-(s.re + 1)) := by
      refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt
        (by linarith : -(s.re + 1) < -1) ha).const_mul C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans ht)]
      simp only [neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (hg t ht) (Real.rpow_nonneg (ha.trans ht).le _)
    _ = C * a ^ (-s.re) / s.re := by
      have hexp : -(s.re + 1) + 1 = -s.re := by ring
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha, hexp]
      ring

/-- If `‖g t‖ ≤ C` on `(1, ∞)`, then `‖∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))‖ ≤ C / s.re` on
`Re(s) > 0`. -/
theorem norm_integral_mul_cpow_le_of_bound {g : ℝ → ℂ} {C : ℝ}
    (hg : ∀ t ∈ Set.Ioi (1 : ℝ), ‖g t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))‖ ≤ C / s.re := by
  simpa only [Real.one_rpow, mul_one] using
    norm_integral_Ioi_mul_cpow_le_of_bound zero_lt_one hg hs

end TauCeti
