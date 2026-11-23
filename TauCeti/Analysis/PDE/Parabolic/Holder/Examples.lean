/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.One
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Topology.MetricSpace.Holder

/-!
# The maps `√t` and `t ^ ((1 + α) / 2)` in the parabolic Hölder spaces

On the slab `E × [0, T]`, `T > 0`, this file places two maps that depend on time alone in the
bounded parabolic Hölder spaces of orders zero, one and two. They show what the time regularity
built into these spaces measures.

* `u = √t` lies in `C_b^{α,α/2}` for `α ≤ 1`
  (`TauCeti.exists_holderSpace_eq_sqrt_time`): its increments are at most `√|t - s|`, which
  is at most the parabolic distance.
* `u = √t` does not lie in the order-two space `C_b^{2+α,1+α/2}`, for any `α`
  (`TauCeti.not_exists_parabolicC2HolderSpace_eq_sqrt_time`). Its time derivative
  `1 / (2 √t)` is unbounded near `t = 0`, while the time derivative of an element is bounded on the
  closed slab, its endpoint value being a one-sided derivative.
* `u = √t` does not lie in the order-one space `C_{par,b}^{1+α}` when `α > 0`
  (`TauCeti.not_exists_parabolicC1HolderSpace_eq_sqrt_time`): the quotient
  `|√t - √0| / |t - 0| ^ ((1 + α) / 2) = t ^ (-α / 2)` is unbounded, so the temporal
  `(1 + α) / 2`-seminorm that is part of the order-one norm is infinite. At `α = 0` the exponent is
  `1 / 2`, and this obstruction disappears.
* `u = t ^ ((1 + α) / 2)` lies in `C_{par,b}^{1+α}` for `α ≤ 1`, with temporal
  `(1 + α) / 2`-seminorm at most `1`
  (`TauCeti.exists_parabolicC1HolderSpace_eq_rpow_time_and_timeEHolderNorm_le_one`),
  although for `α < 1` its time derivative is unbounded near `t = 0`: the order-one space asks for
  fractional time regularity, not for a time derivative.

So the temporal seminorm of exponent `(1 + α) / 2` distinguishes `t ^ ((1 + α) / 2)` from `√t`; a
definition of the order-one space without it would admit `√t`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 3.
-/

public section
noncomputable section

namespace TauCeti

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}

omit [NormedSpace ℝ E] in
/-- **`√t` is parabolically Hölder.** For `α ≤ 1`, the map `(x, t) ↦ √t` lies in `C_b^{α,α/2}` on
the slab `E × [0, T]`. -/
theorem exists_holderSpace_eq_sqrt_time {α : ℝ≥0} (hα : α ≤ 1) (T : ℝ) :
    ∃ f : HolderSpace α (slab (E := E) 0 T) ℝ,
      ∀ p, f p = √(p : ParabolicSpaceTime E).time := by
  -- `√` is `1 / 2`-Hölder with constant one on `[0, T]`, and its oscillation there is at most `√T`.
  have hbound : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist (√s) (√t) ≤ √T := by
    intro s hs t ht
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [Real.sqrt_le_sqrt hs.2, Real.sqrt_le_sqrt ht.2,
      Real.sqrt_nonneg s, Real.sqrt_nonneg t]
  have hsqrt := HolderOnWith.of_le_of_dist_le (f := Real.sqrt) (s := Icc 0 T) (K := 1)
    (β := 1 / 2) (γ := α / 2) (δ := 1) (D := ⟨√T, Real.sqrt_nonneg T⟩)
    (fun s _ t _ _ ↦ by
      simpa [Real.dist_eq, Real.sqrt_eq_rpow] using Real.abs_sqrt_sub_sqrt_le s t)
    hbound (by gcongr) one_pos
  let g : slab (E := E) 0 T →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun p ↦ √(p : ParabolicSpaceTime E).time,
        Real.continuous_sqrt.comp (continuous_time.comp continuous_subtypeVal)⟩ √T
      fun p q ↦ hbound _ (mem_slab.1 p.property) _ (mem_slab.1 q.property)
  have hg : MemHolder α (g : slab (E := E) 0 T → ℝ) := ⟨_, hsqrt.comp_parabolicTime_slab⟩
  exact ⟨HolderSpace.ofBoundedContinuousFunction g hg,
    fun p ↦ HolderSpace.ofBoundedContinuousFunction_apply g hg p⟩

open ParabolicC2HolderSpace in
/-- **`√t` is not of order two.** For every `α`, no element of `C_b^{2+α,1+α/2}` on the slab
`E × [0, T]`, `T > 0`, is the map `(x, t) ↦ √t`: the time derivative of an element is bounded on
the closed slab, while `√t` is not Lipschitz in time at `t = 0`. -/
theorem not_exists_parabolicC2HolderSpace_eq_sqrt_time {α : ℝ≥0} (hT : 0 < T) :
    ¬ ∃ f : ParabolicC2HolderSpace α E ℝ hT, ∀ p, f p = √(p : ParabolicSpaceTime E).time := by
  rintro ⟨f, hf⟩
  refine absurd (le_of_forall_mem_Ioc_rpow_le_mul_rpow (a := 1 / 2) (b := 1)
    (C := ‖timeDerivL f‖) hT fun t ht ↦ ?_) (by norm_num)
  have h := f.norm_apply_slabMk_sub_le 0 ⟨t, Ioc_subset_Icc_self ht⟩ ⟨0, left_mem_Icc.2 hT.le⟩
  rw [← Real.sqrt_eq_rpow]
  simpa [hf, abs_of_pos ht.1, abs_of_nonneg (Real.sqrt_nonneg t)] using h

/-- **`√t` is not of order one.** For `α > 0`, no element of `C_{par,b}^{1+α}` on the slab
`E × [0, T]`, `T > 0`, is the map `(x, t) ↦ √t`: its time slices would be `(1 + α) / 2`-Hölder,
while `√t / t ^ ((1 + α) / 2) = t ^ (-α / 2)` is unbounded near `t = 0`. -/
theorem not_exists_parabolicC1HolderSpace_eq_sqrt_time {α : ℝ≥0} (hα : 0 < α) (hT : 0 < T) :
    ¬ ∃ f : ParabolicC1HolderSpace α E ℝ 0 T, ∀ p, f p = √(p : ParabolicSpaceTime E).time := by
  rintro ⟨f, hf⟩
  obtain ⟨C, hC⟩ := f.memHolder_timeSlice 0
  have hγ : (1 / 2 : ℝ) < (((1 + α) / 2 : ℝ≥0) : ℝ) := by
    have : (0 : ℝ) < α := hα
    push_cast
    linarith
  refine absurd (le_of_forall_mem_Ioc_rpow_le_mul_rpow (a := 1 / 2) (C := C) hT fun t ht ↦ ?_)
    hγ.not_ge
  have ht' : t ∈ Icc 0 T := Ioc_subset_Icc_self ht
  have h := hC.dist_le ⟨t, ht'⟩ ⟨0, left_mem_Icc.2 hT.le⟩
  rw [← Real.sqrt_eq_rpow]
  simpa [hf, Subtype.dist_eq, Real.dist_eq, abs_of_pos ht.1, abs_of_nonneg (Real.sqrt_nonneg t)]
    using h

/-- **`t ^ ((1 + α) / 2)` is of order one.** For `α ≤ 1`, the map `(x, t) ↦ t ^ ((1 + α) / 2)`
lies in `C_{par,b}^{1+α}` on the slab `E × [0, T]`, with temporal `(1 + α) / 2`-seminorm at most
`1`, although for `α < 1` its time derivative is unbounded near `t = 0`. -/
theorem exists_parabolicC1HolderSpace_eq_rpow_time_and_timeEHolderNorm_le_one {α : ℝ≥0}
    (hα : α ≤ 1) (T : ℝ) :
    ∃ f : ParabolicC1HolderSpace α E ℝ 0 T,
      (∀ p, f p = (p : ParabolicSpaceTime E).time ^ (((1 + α) / 2 : ℝ≥0) : ℝ)) ∧
        timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) 0 T → ℝ) ≤ 1 := by
  set γ : ℝ≥0 := (1 + α) / 2 with hγ
  have hγ1 : (γ : ℝ) ≤ 1 := by
    have : (α : ℝ) ≤ 1 := hα
    rw [hγ]
    push_cast
    linarith
  -- `s ↦ s ^ γ` is `γ`-Hölder with constant `1` on `[0, ∞)`.
  have hinc : ∀ p q : slab (E := E) 0 T,
      dist ((p : ParabolicSpaceTime E).time ^ (γ : ℝ)) ((q : ParabolicSpaceTime E).time ^ (γ : ℝ))
        ≤ |(p : ParabolicSpaceTime E).time - (q : ParabolicSpaceTime E).time| ^ (γ : ℝ) :=
    fun p q ↦ Real.abs_rpow_sub_rpow_le (mem_slab.1 p.property).1 (mem_slab.1 q.property).1
      γ.coe_nonneg hγ1
  let u : slab (E := E) 0 T →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun p ↦ (p : ParabolicSpaceTime E).time ^ (γ : ℝ),
        (Real.continuous_rpow_const γ.coe_nonneg).comp
          (continuous_time.comp continuous_subtypeVal)⟩ (T ^ (γ : ℝ))
      fun p q ↦ by
        have hp := mem_slab.1 p.property
        have hq := mem_slab.1 q.property
        refine (hinc p q).trans (Real.rpow_le_rpow (abs_nonneg _) ?_ γ.coe_nonneg)
        rw [abs_sub_le_iff]
        constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  have hu : timeEHolderNorm γ (u : slab (E := E) 0 T → ℝ) ≤ 1 := by
    refine timeEHolderNorm_le_iff.2 fun x t s ↦ ?_
    rw [one_mul, edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hinc (slabMk x t) (slabMk x s)
    rw [time_slabMk, time_slabMk] at h
    simpa [u, Subtype.dist_eq, Real.dist_eq] using h
  refine ⟨ParabolicC1HolderSpace.mk u 0 (fun t x ↦ ?_) (hu.trans_lt ENNReal.one_lt_top),
    fun p ↦ ?_, ?_⟩
  · have hc : (fun y ↦ u (slabMk y t)) = fun _ ↦ (t : ℝ) ^ (γ : ℝ) :=
      funext fun y ↦ by simp [u]
    rw [hc, HolderSpace.zero_apply]
    exact hasFDerivAt_const _ x
  · simp [u]
  · refine le_of_eq_of_le ?_ hu
    congr 1
    funext p
    rw [ParabolicC1HolderSpace.mk_apply]

end TauCeti
