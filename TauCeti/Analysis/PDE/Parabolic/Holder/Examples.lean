/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.One
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
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
  although its time derivative is unbounded near `t = 0`: the order-one space asks for fractional
  time regularity, not for a time derivative.

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

/-- For `γ > 1 / 2`, no bound `√t ≤ C t ^ γ` holds on all of `(0, T]`. -/
private theorem not_forall_sqrt_le_mul_rpow {γ C : ℝ} (hγ : 1 / 2 < γ) (hT : 0 < T) :
    ¬ ∀ t ∈ Ioc 0 T, √t ≤ C * t ^ γ := by
  intro h
  obtain ⟨t, hCt, ht⟩ := ((eventually_mul_rpow_lt_nhdsGT_zero (sub_pos.2 hγ) C one_pos).and
    (Ioo_mem_nhdsGT hT)).exists
  have hsqrt : 0 < √t := Real.sqrt_pos.2 ht.1
  have hsplit : C * t ^ γ = C * t ^ (γ - 1 / 2) * √t := by
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht.1, sub_add_cancel]
  have hle := h t ⟨ht.1, ht.2.le⟩
  rw [hsplit] at hle
  nlinarith

omit [NormedSpace ℝ E] in
/-- **`√t` is parabolically Hölder.** For `α ≤ 1`, the map `(x, t) ↦ √t` lies in `C_b^{α,α/2}` on
the slab `E × [0, T]`. -/
theorem exists_holderSpace_eq_sqrt_time {α : ℝ≥0} (hα : α ≤ 1) (T : ℝ) :
    ∃ f : HolderSpace α (slab (E := E) 0 T) ℝ,
      ∀ p, f p = √(p : ParabolicSpaceTime E).time := by
  -- The increments are at most `√T`, and at most `√|t - s| ≤ d`.
  have hbound : ∀ p q : slab (E := E) 0 T,
      dist (√(p : ParabolicSpaceTime E).time) (√(q : ParabolicSpaceTime E).time) ≤ √T := by
    intro p q
    have hp := mem_slab.1 p.property
    have hq := mem_slab.1 q.property
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [Real.sqrt_le_sqrt hp.2, Real.sqrt_le_sqrt hq.2,
      Real.sqrt_nonneg (p : ParabolicSpaceTime E).time,
      Real.sqrt_nonneg (q : ParabolicSpaceTime E).time]
  have h₁ : ∀ p q : slab (E := E) 0 T,
      dist (√(p : ParabolicSpaceTime E).time) (√(q : ParabolicSpaceTime E).time) ≤
        dist p q := by
    intro p q
    have hp := mem_slab.1 p.property
    have hq := mem_slab.1 q.property
    rw [Real.dist_eq, Subtype.dist_eq]
    refine le_trans ?_ (sqrt_abs_time_sub_le_dist _ _)
    have h := Real.abs_rpow_sub_rpow_le hp.1 hq.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa only [← Real.sqrt_eq_rpow] using h
  let g : slab (E := E) 0 T →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun p ↦ √(p : ParabolicSpaceTime E).time,
        Real.continuous_sqrt.comp (continuous_time.comp continuous_subtypeVal)⟩ √T
      hbound
  have hg : MemHolder α (g : slab (E := E) 0 T → ℝ) :=
    ⟨_, holderOnWith_univ.1 (HolderOnWith.of_le_of_dist_le (K := 1) (β := 1) (δ := 1)
      (D := ⟨√T, Real.sqrt_nonneg T⟩) (fun p _ q _ _ ↦ by simpa [g] using h₁ p q)
      (fun p _ q _ ↦ hbound p q) hα one_pos)⟩
  exact ⟨HolderSpace.ofBoundedContinuousFunction g hg,
    fun p ↦ HolderSpace.ofBoundedContinuousFunction_apply g hg p⟩

open ParabolicC2HolderSpace in
/-- **`√t` is not of order two.** For every `α`, no element of `C_b^{2+α,1+α/2}` on the slab
`E × [0, T]`, `T > 0`, is the map `(x, t) ↦ √t`: the time derivative of an element is bounded on
the closed slab, while `√t` is not Lipschitz in time at `t = 0`. -/
theorem not_exists_parabolicC2HolderSpace_eq_sqrt_time {α : ℝ≥0} (hT : 0 < T) :
    ¬ ∃ f : ParabolicC2HolderSpace α E ℝ hT, ∀ p, f p = √(p : ParabolicSpaceTime E).time := by
  rintro ⟨f, hf⟩
  -- The time slice through `x = 0` is `‖∂ₜ f‖`-Lipschitz on `[0, T]` by the mean value theorem.
  have hlip : ∀ t ∈ Icc 0 T, ‖timeExtension hT.le f 0 t - timeExtension hT.le f 0 0‖ ≤
      ‖timeDerivL f‖ * ‖t - 0‖ := fun t ht ↦
    (convex_Icc 0 T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs ↦ f.hasDerivWithinAt_timeExtension 0 hs)
      (fun s hs ↦ le_of_eq_of_le (congrArg norm (timeExtension_of_mem hT.le _ 0 ⟨s, hs⟩))
        (HolderSpace.norm_apply_le _ _))
      (left_mem_Icc.2 hT.le) ht
  refine not_forall_sqrt_le_mul_rpow (γ := 1) (C := ‖timeDerivL f‖) (by norm_num) hT
    fun t ht ↦ ?_
  have ht' : t ∈ Icc 0 T := Ioc_subset_Icc_self ht
  have h := hlip t ht'
  have et : timeExtension hT.le f 0 t = √t :=
    (timeExtension_of_mem hT.le _ 0 ⟨t, ht'⟩).trans (by rw [hf, time_slabMk])
  have e0 : timeExtension hT.le f 0 0 = 0 :=
    (timeExtension_of_mem hT.le _ 0 ⟨0, left_mem_Icc.2 hT.le⟩).trans
      (by rw [hf, time_slabMk, Real.sqrt_zero])
  rw [et, e0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), abs_of_pos ht.1] at h
  rwa [Real.rpow_one]



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
  refine not_forall_sqrt_le_mul_rpow (C := C) hγ hT fun t ht ↦ ?_
  have ht' : t ∈ Icc 0 T := Ioc_subset_Icc_self ht
  have h := hC.dist_le ⟨t, ht'⟩ ⟨0, left_mem_Icc.2 hT.le⟩
  simpa [hf, Subtype.dist_eq, Real.dist_eq, abs_of_pos ht.1, abs_of_nonneg (Real.sqrt_nonneg t)]
    using h

/-- **`t ^ ((1 + α) / 2)` is of order one.** For `α ≤ 1`, the map `(x, t) ↦ t ^ ((1 + α) / 2)`
lies in `C_{par,b}^{1+α}` on the slab `E × [0, T]`, with temporal `(1 + α) / 2`-seminorm at most
`1`, although its time derivative is unbounded near `t = 0`. -/
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
