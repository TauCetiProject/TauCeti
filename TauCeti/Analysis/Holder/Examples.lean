/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic
public import TauCeti.MeasureTheory.Function.Campanato
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Examples of Hölder and Campanato spaces

This file computes the basic examples that calibrate the Hölder spaces `C^{k,α}(Ω)` on an open
set (`TauCeti.CkHolderSpaceOn`) and the Campanato spaces `𝓛^{p,λ}(Ω)`
(`TauCeti.MeasureTheory.campanatoSeminormPow`). They show what the definitions see and which
hypotheses of the general theorems are needed.

* **The cusp.** On `(-1, 1)` and for `0 < α ≤ 1`, the function `|x|^α` has `α`-Hölder seminorm
  exactly `1` (`TauCeti.holderOnWith_abs_rpow_Ioo_iff`); for `α = 1` this is the Lipschitz
  constant `1` of `|x|` (`TauCeti.lipschitzOnWith_abs_Ioo_iff`). It is `β`-Hölder for no
  `β > α` (`TauCeti.not_holderOnWith_abs_rpow_Ioo`), so the exponent of a Hölder space measures
  the sharp order of vanishing.
* **The seminorm is global.** On `Ω = (-1, 0) ∪ (0, 1)` the sign function is smooth with
  vanishing derivatives, and it lies in `C^{k,α}(Ω)` for every `k ≥ 1`
  (`TauCeti.exists_ckHolderSpaceOn_eq_sign`), since only the `k`-th derivative carries a
  Hölder condition. It does not lie in `C^{0,α}(Ω)` for `α > 0`
  (`TauCeti.not_exists_ckHolderSpaceOn_zero_eq_sign`): its Hölder quotient across the gap is
  unbounded. So the inclusion `C^{1,α}(Ω) ⊆ C^{0,α}(Ω)`, which holds on convex open sets
  (`TauCeti.CkHolderSpaceOn.inclusionSuccL`), fails on this non-convex set.
* **Boundedness.** `1/x` is smooth on `(0, 1)` but lies in no `C^{k,α}((0, 1))`, being unbounded
  (`TauCeti.not_exists_ckHolderSpaceOn_eq_inv`).
* **The dimension in Campanato's exponent.** For `n = 1` and `p = 2`, Campanato's
  characterization `𝓛^{p,n + p α} = C^{0,α}` predicts that `|x|^α` lies in `𝓛^{2,1+2α}((-1, 1))`
  (`TauCeti.campanatoSeminormPow_abs_rpow_Ioo_ne_top`) and not in `𝓛^{2,2+2α}((-1, 1))`
  (`TauCeti.campanatoSeminormPow_abs_rpow_Ioo_eq_top`), the space the two-dimensional value
  `n = 2` of the dimension would give. The second fact is read off from the characterization
  itself: membership in `𝓛^{2,2+2α}` would make `|x|^α` Hölder of exponent `α + 1/2`.

The exponents above one are treated in general beside the definitions: on a preconnected open
set a Hölder bound of exponent `r > 1` forces constancy (`HolderOnWith.eq_of_one_lt`), so
`C^{0,α}(Ω)` for `α > 1` consists of constants
(`TauCeti.CkHolderSpaceOn.apply_eq_apply_of_one_lt`) and so does `𝓛^{p,λ}(Ω)` for `λ > n + p`
(`TauCeti.MeasureTheory.exists_ae_eq_const_iff_campanatoSeminormPow_ne_top`).

## References

* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Section 5.1 and Theorem 5.5.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

/-! ### The cusp `|x|^α` -/

/-- On `(-1, 1)`, for `0 < α ≤ 1`, the cusp `|x|^α` is `α`-Hölder with constant `C` exactly when
`C ≥ 1`: its `α`-Hölder seminorm on `(-1, 1)` is `1`, attained on the pair `0, 1/2`. -/
theorem holderOnWith_abs_rpow_Ioo_iff {α C : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    HolderOnWith C α (fun x : ℝ ↦ |x| ^ (α : ℝ)) (Ioo (-1) 1) ↔ 1 ≤ C := by
  constructor
  · intro h
    have h1 := h.dist_le (x := 1 / 2) (y := 0) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩
    have hα0' : (α : ℝ) ≠ 0 := by exact_mod_cast hα0.ne'
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (α : ℝ) := by positivity
    simp only [Real.dist_eq, sub_zero, abs_zero, Real.zero_rpow hα0',
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hpos] at h1
    exact_mod_cast le_of_mul_le_mul_right (by linarith : 1 * (1 / 2 : ℝ) ^ (α : ℝ) ≤
      C * (1 / 2 : ℝ) ^ (α : ℝ)) hpos
  · intro hC
    have h := (holderWith_norm_rpow (E := ℝ) hα1).holderOnWith (Ioo (-1) 1)
    simp only [Real.norm_eq_abs] at h
    exact h.mono_const hC

/-- On `(-1, 1)` the absolute value is `C`-Lipschitz exactly when `C ≥ 1`: its Lipschitz constant
there is `1`. -/
theorem lipschitzOnWith_abs_Ioo_iff {C : ℝ≥0} :
    LipschitzOnWith C (fun x : ℝ ↦ |x|) (Ioo (-1) 1) ↔ 1 ≤ C := by
  have h := holderOnWith_abs_rpow_Ioo_iff (C := C) one_pos le_rfl
  simpa only [NNReal.coe_one, Real.rpow_one, holderOnWith_one] using h

/-- On `(-1, 1)`, for `0 < α < β`, the cusp `|x|^α` is not `β`-Hölder: the quotient
`|x|^α / |x|^β` is unbounded near `0`. -/
theorem not_holderOnWith_abs_rpow_Ioo {α β C : ℝ≥0} (hα : 0 < α) (hαβ : α < β) :
    ¬ HolderOnWith C β (fun x : ℝ ↦ |x| ^ (α : ℝ)) (Ioo (-1) 1) := by
  intro h
  have hβα : (0 : ℝ) < β - α := sub_pos.2 (by exact_mod_cast hαβ)
  obtain ⟨t, ht, hCt⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
    (eventually_mul_rpow_lt_nhdsGT_zero hβα C one_pos)).exists
  have h1 := h.dist_le (x := t) (y := 0) ⟨by linarith [ht.1], ht.2⟩ ⟨by norm_num, by norm_num⟩
  have hα0 : (α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  have hpos : 0 < t ^ (α : ℝ) := Real.rpow_pos_of_pos ht.1 _
  simp only [Real.dist_eq, sub_zero, abs_zero, Real.zero_rpow hα0, abs_of_pos ht.1,
    abs_of_pos hpos] at h1
  have hsplit : t ^ (β : ℝ) = t ^ ((β : ℝ) - α) * t ^ (α : ℝ) := by
    rw [← Real.rpow_add ht.1, sub_add_cancel]
  rw [hsplit, ← mul_assoc] at h1
  linarith [mul_lt_mul_of_pos_right hCt hpos]

/-! ### The sign function on `(-1, 0) ∪ (0, 1)` -/

section Sign

variable {Ω : Opens ℝ}

/-- The sign function is not in `C^{0,α}(Ω)` on `Ω = (-1, 0) ∪ (0, 1)` for `α > 0`, although it is
smooth on `Ω`: the `C^{0,α}(Ω)` seminorm is global on `Ω` and sees across the gap, where the
Hölder quotient `2 / (2 t)^α` of the sign function at the points `±t` is unbounded. -/
theorem not_exists_ckHolderSpaceOn_zero_eq_sign {α : ℝ≥0} (hα : 0 < α)
    (hΩ : (Ω : Set ℝ) = Ioo (-1) 0 ∪ Ioo 0 1) :
    ¬ ∃ f : CkHolderSpaceOn 0 α Ω ℝ, ∀ x : Ω, f x = Real.sign x := by
  rintro ⟨f, hf⟩
  set K := nnHolderNorm α (f.iteratedFDeriv (Fin.last 0) : Ω → ℝ [×0]→L[ℝ] ℝ)
  obtain ⟨t, ht, hKt⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
    (eventually_mul_rpow_lt_nhdsGT_zero (by exact_mod_cast hα) ((K : ℝ) * 2 ^ (α : ℝ))
      two_pos)).exists
  have htΩ : t ∈ (Ω : Set ℝ) := by
    rw [hΩ]
    exact Or.inr ht
  have hntΩ : -t ∈ (Ω : Set ℝ) := by
    rw [hΩ]
    exact Or.inl ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h1 := f.holderOnWith_extend.dist_le htΩ hntΩ
  have hft : f.extend t = 1 := by
    rw [← Real.sign_of_pos ht.1, ← hf ⟨t, htΩ⟩]
    exact f.extend_apply ⟨t, htΩ⟩
  have hfnt : f.extend (-t) = -1 := by
    rw [← Real.sign_of_neg (by linarith [ht.1] : -t < 0), ← hf ⟨-t, hntΩ⟩]
    exact f.extend_apply ⟨-t, hntΩ⟩
  have hd1 : dist (1 : ℝ) (-1) = 2 := by norm_num [Real.dist_eq]
  have hdt : dist t (-t) = 2 * t := by
    rw [Real.dist_eq, sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith [ht.1])]
  rw [hft, hfnt, hd1, hdt, Real.mul_rpow zero_le_two ht.1.le, ← mul_assoc] at h1
  exact lt_irrefl _ (h1.trans_lt hKt)

/-- For `k ≥ 1` and every `α`, the sign function lies in `C^{k,α}(Ω)` on `Ω = (-1, 0) ∪ (0, 1)`:
it is bounded by `1` and its derivatives vanish on `Ω`, so the Hölder condition on the `k`-th
derivative holds trivially. Together with `TauCeti.not_exists_ckHolderSpaceOn_zero_eq_sign`, this
shows that the inclusion `C^{1,α}(Ω) ⊆ C^{0,α}(Ω)` fails on this non-convex open set. -/
theorem exists_ckHolderSpaceOn_eq_sign {k : ℕ} (hk : 1 ≤ k) (α : ℝ≥0)
    (hΩ : (Ω : Set ℝ) = Ioo (-1) 0 ∪ Ioo 0 1) :
    ∃ f : CkHolderSpaceOn k α Ω ℝ, ∀ x : Ω, f x = Real.sign x := by
  -- The sign function is locally constant on `Ω`.
  have hloc : ∀ x ∈ (Ω : Set ℝ), Real.sign =ᶠ[𝓝 x] fun _ ↦ Real.sign x := by
    intro x hx
    rw [hΩ] at hx
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx.2] with y hy
      rw [Real.sign_of_neg hy, Real.sign_of_neg hx.2]
    · filter_upwards [Ioi_mem_nhds hx.1] with y hy
      rw [Real.sign_of_pos hy, Real.sign_of_pos hx.1]
  have hcont : ContDiffOn ℝ k Real.sign Ω := fun x hx ↦
    (contDiffAt_const.congr_of_eventuallyEq (hloc x hx)).contDiffWithinAt
  have hderiv : ∀ i : ℕ, i ≠ 0 → ∀ x ∈ (Ω : Set ℝ), iteratedFDeriv ℝ i Real.sign x = 0 := by
    intro i hi x hx
    rw [((hloc x hx).iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_const_of_ne hi, Pi.zero_apply]
  have hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖iteratedFDeriv ℝ i Real.sign x‖ ≤ C := fun i _ ↦
    ⟨1, fun x ↦ by
      rcases eq_or_ne i 0 with rfl | hi
      · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
      · rw [hderiv i hi x x.property, norm_zero]
        exact zero_le_one⟩
  have hholder : MemHolder α fun x : Ω ↦ iteratedFDeriv ℝ k Real.sign x := by
    have hzero : (fun x : Ω ↦ iteratedFDeriv ℝ k Real.sign x) = fun _ ↦ 0 :=
      funext fun x ↦ hderiv k (by omega) x x.property
    rw [hzero]
    exact (HolderWith.const (C := 0)).memHolder
  exact ⟨CkHolderSpaceOn.ofContDiffOn Real.sign hcont hbdd hholder,
    CkHolderSpaceOn.ofContDiffOn_apply _ _ _ _⟩

end Sign

/-- The function `1/x` lies in no `C^{k,α}((0, 1))`: it is smooth on `(0, 1)` but unbounded, and
the values of an element are bounded by its norm. -/
theorem not_exists_ckHolderSpaceOn_eq_inv {k : ℕ} {α : ℝ≥0} {Ω : Opens ℝ}
    (hΩ : (Ω : Set ℝ) = Ioo 0 1) :
    ¬ ∃ f : CkHolderSpaceOn k α Ω ℝ, ∀ x : Ω, f x = (x : ℝ)⁻¹ := by
  rintro ⟨f, hf⟩
  have hN : (1 : ℝ) < ‖f‖ + 2 := by linarith [norm_nonneg f]
  have ht : (‖f‖ + 2)⁻¹ ∈ (Ω : Set ℝ) := by
    rw [hΩ]
    exact ⟨by positivity, inv_lt_one_of_one_lt₀ hN⟩
  have h := f.norm_apply_le ⟨_, ht⟩
  rw [hf, inv_inv, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  linarith

/-! ### The cusp in Campanato spaces -/

/-- The interval `(-1, 1)` has density at least `1/8` in every closed ball centred in it of radius
at most twice its diameter. -/
private theorem mul_volume_closedBall_le_volume_closedBall_inter_Ioo {x r : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hr : 0 < r) (hr4 : ENNReal.ofReal r ≤ 2 * ediam (Ioo (-1 : ℝ) 1)) :
    ((8⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall x r) ≤ volume (closedBall x r ∩ Ioo (-1) 1) := by
  have hr4' : r ≤ 4 := by
    rw [Real.ediam_Ioo, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hr4
    linarith
  set m := min r 1
  have hm : r / 4 ≤ m := le_min (by linarith) (by linarith)
  have hmr : m ≤ r := min_le_left r 1
  have hm1 : m ≤ 1 := min_le_right r 1
  -- An interval of length `m` next to `x`, on the side of `0`, lies in the ball and in `(-1, 1)`.
  obtain ⟨a, ha⟩ : ∃ a, Ioo a (a + m) ⊆ closedBall x r ∩ Ioo (-1) 1 := by
    rcases le_or_gt x 0 with h | h
    · refine ⟨x, fun y hy ↦ ⟨?_, ?_, ?_⟩⟩
      · rw [mem_closedBall, Real.dist_eq, abs_le]
        constructor <;> linarith [hy.1, hy.2]
      · linarith [hx.1, hy.1]
      · linarith [hy.2]
    · refine ⟨x - m, fun y hy ↦ ⟨?_, ?_, ?_⟩⟩
      · rw [mem_closedBall, Real.dist_eq, abs_le]
        constructor <;> linarith [hy.1, hy.2]
      · linarith [hy.1]
      · linarith [hx.2, hy.2]
  calc ((8⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall x r) = ENNReal.ofReal (r / 4) := by
        rw [Real.volume_closedBall, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal hm
    _ = volume (Ioo a (a + m)) := by rw [Real.volume_Ioo, add_sub_cancel_left]
    _ ≤ volume (closedBall x r ∩ Ioo (-1) 1) := measure_mono ha

/-- For `α ≤ 1` the cusp `|x|^α` lies in the Campanato space `𝓛^{2,1+2α}((-1, 1))`, as Campanato's
characterization `𝓛^{p,n + p α} = C^{0,α}` with `n = 1` and `p = 2` predicts. -/
theorem campanatoSeminormPow_abs_rpow_Ioo_ne_top {α : ℝ≥0} (hα : α ≤ 1) :
    campanatoSeminormPow volume (Ioo (-1 : ℝ) 1) 2 (1 + 2 * α) (fun x : ℝ ↦ |x| ^ (α : ℝ)) ≠
      ⊤ := by
  have hhol : HolderOnWith 1 α (fun x : ℝ ↦ |x| ^ (α : ℝ)) (Ioo (-1) 1) := by
    have h := (holderWith_norm_rpow (E := ℝ) hα).holderOnWith (Ioo (-1) 1)
    simpa only [Real.norm_eq_abs] using h
  have h := campanatoSeminormPow_le_of_holderOnWith (μ := volume) zero_le_two
    measurableSet_Ioo.nullMeasurableSet hhol
    (continuous_abs.rpow_const fun _ ↦ Or.inr α.property).aestronglyMeasurable
  rw [Module.finrank_self, Nat.cast_one] at h
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    measure_closedBall_lt_top.ne) h

/-- For `α > 0` the cusp `|x|^α` does not lie in the Campanato space `𝓛^{2,2+2α}((-1, 1))`, the
space that the two-dimensional value `n = 2` in `λ = n + p α` would assign to the exponent `α`.
In dimension one, `𝓛^{2,2+2α}` is the space of exponent `α + 1/2`, and `|x|^α` is Hölder of no
exponent above `α`. So the dimension in the exponent is load-bearing. -/
theorem campanatoSeminormPow_abs_rpow_Ioo_eq_top {α : ℝ≥0} (hα : 0 < α) :
    campanatoSeminormPow volume (Ioo (-1 : ℝ) 1) 2 (2 + 2 * α) (fun x : ℝ ↦ |x| ^ (α : ℝ)) =
      ⊤ := by
  by_contra hfin
  have hcont : Continuous fun x : ℝ ↦ |x| ^ (α : ℝ) :=
    continuous_abs.rpow_const fun _ ↦ Or.inr α.property
  have hexp : (2 : ℝ) + 2 * α = (Module.finrank ℝ ℝ : ℝ) + 2 * ((α + 2⁻¹ : ℝ≥0) : ℝ) := by
    rw [Module.finrank_self]
    push_cast
    ring
  rw [hexp] at hfin
  obtain ⟨K, g, hg, hfg⟩ := (exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top
    (α := α + 2⁻¹) (c := 8⁻¹) (by positivity) one_le_two (by norm_num)
    measurableSet_Ioo.nullMeasurableSet
    (hcont.locallyIntegrable (μ := volume.restrict (Ioo (-1) 1)))
    fun x hx r hr hr4 ↦ mul_volume_closedBall_le_volume_closedBall_inter_Ioo hx hr hr4).2 hfin
  have heq : EqOn (fun x : ℝ ↦ |x| ^ (α : ℝ)) g (Ioo (-1) 1) :=
    Measure.eqOn_open_of_ae_eq hfg isOpen_Ioo hcont.continuousOn
      (hg.continuousOn (by positivity))
  refine not_holderOnWith_abs_rpow_Ioo (β := α + 2⁻¹) (C := K) hα
    (lt_add_of_pos_right α (by norm_num)) fun x hx y hy ↦ ?_
  rw [heq hx, heq hy]
  exact hg x hx y hy

end TauCeti
