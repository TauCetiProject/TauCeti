/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Holder.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Calculus.BumpFunction.HolderApproximation
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Topology.MetricSpace.Holder

/-!
# Little Hölder spaces

A function `f` is *little `α`-Hölder* (`TauCeti.MemLittleHolder α f`) when its `α`-Hölder
difference quotients tend to zero at small scales: for every `ε > 0` there is `δ > 0` with
`dist (f x) (f y) ≤ ε * dist x y ^ α` whenever `dist x y < δ`. The little Hölder space
`h^{0,α}` is the subspace `TauCeti.HolderSpace.littleHolder` of these functions in the Banach space
`TauCeti.HolderSpace α X Y` of bounded `α`-Hölder functions.

## Main results

* `HolderWith.memLittleHolder`: a function that is Hölder of a larger exponent `β > α` is little
  `α`-Hölder; in particular so is every Lipschitz function when `α < 1`
  (`LipschitzWith.memLittleHolder`).
* `TauCeti.HolderSpace.isClosed_littleHolder`: the little Hölder space is closed in the
  supremum-plus-Hölder norm.
* `TauCeti.HolderSpace.exists_contDiff_lipschitzWith_norm_sub_lt` and
  `TauCeti.HolderSpace.littleHolder_eq_closure`: on a finite-dimensional real normed space and
  for `α < 1`, the little Hölder space is the closure of the smooth Lipschitz functions. A little
  Hölder function is approximated by its convolutions with normalized bumps at small scales. So
  the Banach space `h^{0,α}` is the completion of the smooth Lipschitz functions in the
  `C^{0,α}` norm.
* `TauCeti.not_memLittleHolder_norm_rpow` and `TauCeti.HolderSpace.littleHolder_ne_top`: the cusp
  `x ↦ ‖x‖ ^ α`, `0 < α ≤ 1`, is `α`-Hölder (`TauCeti.holderWith_norm_rpow`) but has difference
  quotient `1` between `0` and every other point. Truncated at height `1`, it is a bounded Hölder
  function outside `h^{0,α}`, so in positive dimension the smooth Lipschitz functions are not dense
  in the full Hölder space.

## References

* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Birkhäuser
  (1995), Chapter 0, for little Hölder spaces as closures of smooth functions and their
  characterization by vanishing small-scale Hölder quotients.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set ContinuousLinearMap
open scoped NNReal Topology Convolution ContDiff BoundedContinuousFunction

namespace TauCeti

section Predicate

variable {X Y : Type*} [PseudoMetricSpace X]

/-- A function is **little `α`-Hölder** if its `α`-Hölder difference quotients tend to zero at
small scales: for every `ε > 0` there is `δ > 0` such that
`dist (f x) (f y) ≤ ε * dist x y ^ α` whenever `dist x y < δ`. -/
def MemLittleHolder [PseudoMetricSpace Y] (α : ℝ≥0) (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → dist (f x) (f y) ≤ ε * dist x y ^ (α : ℝ)

/-- A Hölder function of exponent `β` is little Hölder of every smaller exponent `α < β`. -/
theorem _root_.HolderWith.memLittleHolder [PseudoMetricSpace Y] {C α β : ℝ≥0} {f : X → Y}
    (hf : HolderWith C β f) (hαβ : α < β) : MemLittleHolder α f := by
  intro ε hε
  have hαβ' : (0 : ℝ) < β - α := sub_pos.2 hαβ
  -- `t ↦ C t ^ (β - α)` is continuous and vanishes at `0`, so it is below `ε` near `0`.
  have hcont : Tendsto (fun t : ℝ ↦ (C : ℝ) * t ^ ((β : ℝ) - α)) (𝓝 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hαβ'.le).const_mul (C : ℝ)).tendsto 0
    rwa [Real.zero_rpow hαβ'.ne', mul_zero] at h
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  have hd : dist (dist x y) 0 < δ := by rwa [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg]
  calc dist (f x) (f y) ≤ C * dist x y ^ (β : ℝ) := hf.dist_le x y
    _ = C * dist x y ^ ((β : ℝ) - α) * dist x y ^ (α : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add_of_nonneg dist_nonneg hαβ'.le α.coe_nonneg, sub_add_cancel]
    _ ≤ ε * dist x y ^ (α : ℝ) := by gcongr; exact (hδε hd).le

/-- For `α < 1`, a Lipschitz function is little `α`-Hölder. -/
theorem _root_.LipschitzWith.memLittleHolder [PseudoMetricSpace Y] {K α : ℝ≥0} {f : X → Y}
    (hf : LipschitzWith K f) (hα : α < 1) : MemLittleHolder α f :=
  hf.holderWith.memLittleHolder hα

/-- Constant functions are little Hölder. -/
theorem memLittleHolder_const [PseudoMetricSpace Y] {α : ℝ≥0} (c : Y) :
    MemLittleHolder α (fun _ : X ↦ c) :=
  fun ε _ ↦ ⟨1, one_pos, fun x y _ ↦ by rw [dist_self]; positivity⟩

variable [SeminormedAddCommGroup Y] {α : ℝ≥0} {f g : X → Y}

/-- The zero function is little Hölder. -/
theorem memLittleHolder_zero : MemLittleHolder α (0 : X → Y) :=
  memLittleHolder_const 0

/-- The sum of two little Hölder functions is little Hölder. -/
theorem MemLittleHolder.add (hf : MemLittleHolder α f) (hg : MemLittleHolder α g) :
    MemLittleHolder α (f + g) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x y hxy ↦ ?_⟩
  calc dist ((f + g) x) ((f + g) y) ≤ dist (f x) (f y) + dist (g x) (g y) :=
        dist_add_add_le _ _ _ _
    _ ≤ ε / 2 * dist x y ^ (α : ℝ) + ε / 2 * dist x y ^ (α : ℝ) :=
      add_le_add (h₁ x y (hxy.trans_le (min_le_left _ _)))
        (h₂ x y (hxy.trans_le (min_le_right _ _)))
    _ = ε * dist x y ^ (α : ℝ) := by ring

/-- A scalar multiple of a little Hölder function is little Hölder. -/
theorem MemLittleHolder.const_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 Y]
    (hf : MemLittleHolder α f) (c : 𝕜) : MemLittleHolder α (c • f) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (‖c‖ + 1)) (by positivity)
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  have hc : ‖c‖ / (‖c‖ + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  calc dist ((c • f) x) ((c • f) y) = ‖c‖ * dist (f x) (f y) := by
        rw [Pi.smul_apply, Pi.smul_apply, dist_smul₀]
    _ ≤ ‖c‖ * (ε / (‖c‖ + 1) * dist x y ^ (α : ℝ)) := by gcongr; exact h x y hxy
    _ = ‖c‖ / (‖c‖ + 1) * (ε * dist x y ^ (α : ℝ)) := by ring
    _ ≤ ε * dist x y ^ (α : ℝ) := mul_le_of_le_one_left (by positivity) hc

/-- The difference of two little Hölder functions is little Hölder. -/
theorem MemLittleHolder.sub (hf : MemLittleHolder α f) (hg : MemLittleHolder α g) :
    MemLittleHolder α (f - g) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x y hxy ↦ ?_⟩
  calc dist ((f - g) x) ((f - g) y) ≤ dist (f x) (f y) + dist (g x) (g y) :=
        dist_sub_sub_le _ _ _ _
    _ ≤ ε / 2 * dist x y ^ (α : ℝ) + ε / 2 * dist x y ^ (α : ℝ) :=
      add_le_add (h₁ x y (hxy.trans_le (min_le_left _ _)))
        (h₂ x y (hxy.trans_le (min_le_right _ _)))
    _ = ε * dist x y ^ (α : ℝ) := by ring

end Predicate

/-! ### The cusp -/

section Cusp

variable {E : Type*} {α : ℝ≥0}

/-- **The cusp is not little Hölder.** For `α > 0` the function `x ↦ ‖x‖ ^ α` has `α`-Hölder
difference quotient `1` between `0` and every other point, so its quotients do not tend to zero at
small scales. -/
theorem not_memLittleHolder_norm_rpow [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (hα : 0 < α) :
    ¬ MemLittleHolder α (fun x : E ↦ ‖x‖ ^ (α : ℝ)) := by
  intro h
  obtain ⟨δ, hδ, hδh⟩ := h (1 / 2) one_half_pos
  obtain ⟨x, hx⟩ := exists_norm_eq E (half_pos hδ).le
  have hx0 : dist x 0 < δ := by rw [dist_zero_right, hx]; exact half_lt_self hδ
  have hpos : 0 < (δ / 2) ^ (α : ℝ) := Real.rpow_pos_of_pos (half_pos hδ) _
  have key := hδh x 0 hx0
  dsimp only at key
  rw [dist_zero_right, hx, norm_zero, Real.zero_rpow (NNReal.coe_pos.2 hα).ne', Real.dist_eq,
    sub_zero, abs_of_pos hpos] at key
  linarith

/-- For `α ≤ 1`, the cusp `x ↦ ‖x‖ ^ α` is `α`-Hölder with constant `1`. -/
theorem holderWith_norm_rpow [SeminormedAddCommGroup E] (hα : α ≤ 1) :
    HolderWith 1 α (fun x : E ↦ ‖x‖ ^ (α : ℝ)) := by
  have hα' : (α : ℝ) ≤ 1 := hα
  -- Subadditivity of `t ↦ t ^ α` gives `b ^ α - a ^ α ≤ (b - a) ^ α` for `0 ≤ a ≤ b`.
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ^ (α : ℝ) - a ^ (α : ℝ) ≤ (b - a) ^ (α : ℝ) := by
    intro a b ha hab
    have h := Real.rpow_add_le_add_rpow ha (sub_nonneg.2 hab) α.coe_nonneg hα'
    rw [add_sub_cancel] at h
    linarith
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  have hxy : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y
  rcases le_total ‖y‖ ‖x‖ with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow (norm_nonneg y) h α.coe_nonneg))]
    refine (key _ _ (norm_nonneg y) h).trans (Real.rpow_le_rpow (sub_nonneg.2 h) ?_ α.coe_nonneg)
    exact (le_abs_self _).trans hxy
  · rw [abs_of_nonpos (sub_nonpos.2 (Real.rpow_le_rpow (norm_nonneg x) h α.coe_nonneg)), neg_sub]
    refine (key _ _ (norm_nonneg x) h).trans (Real.rpow_le_rpow (sub_nonneg.2 h) ?_ α.coe_nonneg)
    rw [abs_sub_comm] at hxy
    exact (le_abs_self _).trans hxy

end Cusp

/-! ### The little Hölder space -/

namespace HolderSpace

section MetricSpace

variable (α : ℝ≥0) (X Y : Type*) [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The **little Hölder space** `h^{0,α}`: the bounded `α`-Hölder functions whose `α`-Hölder
difference quotients tend to zero at small scales. -/
def littleHolder : Submodule ℝ (HolderSpace α X Y) where
  carrier := {f | MemLittleHolder α f}
  zero_mem' := memLittleHolder_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

variable {α X Y}

@[simp]
theorem mem_littleHolder_iff {f : HolderSpace α X Y} :
    f ∈ littleHolder α X Y ↔ MemLittleHolder α f := Iff.rfl

/-- **The little Hölder space is closed** in the supremum-plus-Hölder norm. -/
theorem isClosed_littleHolder : IsClosed (littleHolder α X Y : Set (HolderSpace α X Y)) := by
  refine isClosed_of_closure_subset fun f hf ε hε ↦ ?_
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, hδg⟩ := (mem_littleHolder_iff.1 hg) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  have hfg' : ‖f - g‖ ≤ ε / 2 := by rw [← dist_eq_norm]; exact hfg.le
  calc dist (f x) (f y) ≤ dist ((f - g) x) ((f - g) y) + dist (g x) (g y) := by
        simp only [sub_apply, dist_eq_norm]
        exact (norm_add_le _ _).trans_eq' (by abel_nf)
    _ ≤ ‖f - g‖ * dist x y ^ (α : ℝ) + ε / 2 * dist x y ^ (α : ℝ) :=
      add_le_add ((f - g).holderWith_nnnorm.dist_le x y) (hδg x y hxy)
    _ ≤ ε / 2 * dist x y ^ (α : ℝ) + ε / 2 * dist x y ^ (α : ℝ) := by gcongr
    _ = ε * dist x y ^ (α : ℝ) := by ring

/-- The little Hölder space of a complete space is a Banach space. -/
instance [CompleteSpace Y] : CompleteSpace (littleHolder α X Y) :=
  isClosed_littleHolder.completeSpace_coe

end MetricSpace

/-! ### Density of smooth functions -/

section Mollification

variable {α : ℝ≥0} {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **Mollification approximates little Hölder functions.** For `α < 1`, a little `α`-Hölder
function on a finite-dimensional space is approximated in the supremum-plus-Hölder norm by smooth
Lipschitz functions: its convolutions with normalized bumps at small enough scales. -/
theorem exists_contDiff_lipschitzWith_norm_sub_lt (hα : α < 1) (f : HolderSpace α E Y)
    (hf : f ∈ littleHolder α E Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : HolderSpace α E Y, ContDiff ℝ ∞ g ∧ (∃ K, LipschitzWith K g) ∧ ‖f - g‖ < ε := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hη : 0 < ε / 4 := by positivity
  obtain ⟨δ₀, hδ₀, hδ₀f⟩ := (mem_littleHolder_iff.1 hf) (ε / 4) hη
  -- Mollify at the scale `δ = min δ₀ 1`, below which the quotients of `f` are at most `ε / 4`.
  set δ := min δ₀ 1 with hδ_def
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hloc : ∀ x y, dist x y < ρ.rOut → dist (f x) (f y) ≤ ε / 4 * dist x y ^ (α : ℝ) :=
    fun x y hxy ↦ hδ₀f x y (hxy.trans_le (min_le_left _ _))
  set M := ‖f.toBoundedContinuousFunction‖
  have hM : ∀ x, ‖f x‖ ≤ M := fun x ↦ by
    simpa using f.toBoundedContinuousFunction.norm_coe_le_norm x
  let g₀ : E → Y := ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hg₀smooth : ContDiff ℝ ∞ g₀ := ρ.hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) ρ.contDiff_normed f.continuous.locallyIntegrable
  have hg₀lip : LipschitzWith _ g₀ :=
    (ρ.hasCompactSupport_normed (μ := μ)).lipschitzWith_convolution_left
      (ρ.contDiff_normed (n := 1)) f.continuous.locallyIntegrable hM
  have hg₀M : ∀ w, ‖g₀ w‖ ≤ M := fun w ↦ by
    have h := norm_integral_kernel_smul_sub_le (μ := μ) ρ.integrable_normed hM w
    simpa only [Real.norm_of_nonneg (ρ.nonneg_normed _), ρ.integral_normed, one_mul, g₀,
      convolution_def, lsmul_apply] using h
  -- `g₀` is bounded and Lipschitz, hence an element of the Hölder space.
  let g₁ : E →ᵇ Y := .ofNormedAddCommGroup g₀ hg₀smooth.continuous M hg₀M
  have hg₁ : MemHolder α (g₁ : E → Y) := by
    have hcoe : (g₁ : E → Y) = g₀ := by ext x; simp [g₁]
    rw [hcoe]
    exact (holderOnWith_univ.1 ((hg₀lip.lipschitzOnWith (s := univ)).holderOnWith_of_norm_le
      (M := ⟨M, norm_nonneg _⟩) (fun x _ ↦ hg₀M x) hα.le)).memHolder
  let g : HolderSpace α E Y := ofBoundedContinuousFunction g₁ hg₁
  have hg : (g : E → Y) = g₀ := funext fun x ↦ by simp [g, g₁]
  refine ⟨g, hg ▸ hg₀smooth, ⟨_, hg ▸ hg₀lip⟩, ?_⟩
  -- `f - g` is uniformly at most `ε / 4` and has Hölder seminorm at most `ε / 2`.
  have hfg : ((f - g).toBoundedContinuousFunction : E → Y) = f - g₀ := by
    rw [toBoundedContinuousFunction_sub, FunLike.coe_sub,
      coe_toBoundedContinuousFunction, coe_toBoundedContinuousFunction, hg]
  have hsup : ‖(f - g).toBoundedContinuousFunction‖ ≤ ε / 4 := by
    refine (BoundedContinuousFunction.norm_le hη.le).2 fun w ↦ ?_
    rw [hfg, Pi.sub_apply, ← dist_eq_norm, dist_comm]
    refine (ρ.dist_normed_convolution_le_mul_rpow f.continuous hloc hη.le w).trans ?_
    exact mul_le_of_le_one_right hη.le
      (Real.rpow_le_one hδ.le (min_le_right _ _) α.coe_nonneg)
  have hhol :
      (nnHolderNorm α ((f - g).toBoundedContinuousFunction : E → Y) : ℝ) ≤ 2 * (ε / 4) := by
    rw [hfg]
    exact (NNReal.coe_le_coe.2 (ρ.holderWith_sub_normed_convolution f.continuous hloc
      hη.le).nnholderNorm_le).trans_eq (Real.coe_toNNReal _ (by positivity))
  rw [norm_def]
  linarith

/-- **Smooth Lipschitz functions are dense in the little Hölder space.** For `α < 1` and a
finite-dimensional real normed space `E`, the little Hölder space `h^{0,α}(E)` is the closure, in
the supremum-plus-Hölder norm, of the smooth Lipschitz functions. -/
theorem littleHolder_eq_closure (hα : α < 1) :
    (littleHolder α E Y : Set (HolderSpace α E Y)) =
      closure {g : HolderSpace α E Y | ContDiff ℝ ∞ g ∧ ∃ K, LipschitzWith K g} := by
  refine Subset.antisymm (fun f hf ↦ Metric.mem_closure_iff.2 fun ε hε ↦ ?_) ?_
  · obtain ⟨g, hg, hgK, hfg⟩ := exists_contDiff_lipschitzWith_norm_sub_lt hα f hf hε
    exact ⟨g, ⟨hg, hgK⟩, by rwa [dist_eq_norm]⟩
  · exact closure_minimal (fun g ⟨_, K, hK⟩ ↦ hK.memLittleHolder hα) isClosed_littleHolder

end Mollification

/-- **The little Hölder space is a proper subspace** in positive dimension, for `0 < α ≤ 1`: the
cusp `x ↦ ‖x‖ ^ α`, truncated at height `1`, is a bounded `α`-Hölder function whose Hölder
quotients do not tend to zero at small scales. -/
theorem littleHolder_ne_top {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (hα0 : 0 < α) (hα1 : α ≤ 1) : littleHolder α E ℝ ≠ ⊤ := by
  let c : E → ℝ := fun x ↦ min (‖x‖ ^ (α : ℝ)) 1
  have hc : HolderWith 1 α c := by
    have h := (LipschitzWith.id.min_const 1).holderWith.comp (holderWith_norm_rpow (E := E) hα1)
    rw [NNReal.one_rpow, mul_one, one_mul] at h
    exact h
  have hcb : ∀ x, ‖c x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (le_min (by positivity) zero_le_one)]
    exact min_le_right _ _
  let f : HolderSpace α E ℝ :=
    ofBoundedContinuousFunction (.ofNormedAddCommGroup c (hc.continuous hα0) 1 hcb) hc.memHolder
  intro htop
  obtain ⟨δ, hδ, hδf⟩ := mem_littleHolder_iff.1 (htop ▸ Submodule.mem_top (x := f)) (1 / 2)
    one_half_pos
  -- Below height `1` the truncated cusp is the cusp, with quotient `1` between `0` and `x`.
  set r := min δ 1 / 2 with hr_def
  have hr : 0 < r := half_pos (lt_min hδ one_pos)
  obtain ⟨x, hx⟩ := exists_norm_eq E hr.le
  have hrα : 0 < r ^ (α : ℝ) := Real.rpow_pos_of_pos hr _
  have hfc : ∀ y, f y = c y := fun y ↦ (ofBoundedContinuousFunction_apply _ _ y).trans (by simp)
  have hfx : f x = r ^ (α : ℝ) := by
    rw [hfc]
    simp only [c]
    rw [hx, min_eq_left (Real.rpow_le_one hr.le (by linarith [min_le_right δ 1]) α.coe_nonneg)]
  have hf0 : f 0 = 0 := by
    rw [hfc]
    simp only [c]
    rw [norm_zero, Real.zero_rpow (NNReal.coe_pos.2 hα0).ne', min_eq_left zero_le_one]
  have hx0 : dist x 0 < δ := by
    rw [dist_zero_right, hx]; linarith [min_le_left δ 1]
  have key := hδf x 0 hx0
  rw [hfx, hf0, Real.dist_eq, sub_zero, abs_of_pos hrα, dist_zero_right, hx] at key
  linarith

end HolderSpace

end TauCeti
