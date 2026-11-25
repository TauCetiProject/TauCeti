/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Calculus.ContDiff.BoundedDerivatives
public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Holder.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.HolderApproximation
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# Little Hölder spaces

A function `f` is *little `α`-Hölder* (`TauCeti.MemLittleHolder α f`) when its `α`-Hölder
difference quotients tend to zero at small scales: for every `ε > 0` there is `δ > 0` with
`dist (f x) (f y) ≤ ε * dist x y ^ α` whenever `dist x y < δ`. The little Hölder space
`h^{0,α}` is the subspace `TauCeti.HolderSpace.littleHolder` of these functions in the Banach space
`TauCeti.HolderSpace α X Y` of bounded `α`-Hölder functions. For every order `k`, the little Hölder
space `h^{k,α}` is the subspace `TauCeti.CkHolderSpace.littleHolder` of the Banach space
`TauCeti.CkHolderSpace k α E F` of bounded `C^{k,α}` maps whose `k`-th derivative is little
`α`-Hölder. On a finite-dimensional real normed space, `h^{k,α}` lies in the closure of the
smooth maps with bounded derivatives, with equality when `α < 1`, so a bounded operator that sends
those smooth maps into a little Hölder space sends all of `h^{k,α}` there.

## Main results

* `HolderWith.memLittleHolder`: a function that is Hölder of a larger exponent `β > α` is little
  `α`-Hölder; in particular so is every Lipschitz function when `α < 1`
  (`LipschitzWith.memLittleHolder`).
* `TauCeti.HolderSpace.isClosed_littleHolder`: the little Hölder space is closed in the
  supremum-plus-Hölder norm.
* `TauCeti.HolderSpace.exists_contDiff_lipschitzWith_norm_sub_lt` and
  `TauCeti.HolderSpace.littleHolder_eq_closure`: on a finite-dimensional real normed space, a
  little Hölder function is approximated by its convolutions with normalized bumps at small
  scales, which are smooth and Lipschitz. For `α < 1` Lipschitz functions are conversely little
  Hölder, so the little Hölder space is the closure of the smooth Lipschitz functions, and the
  Banach space `h^{0,α}` is the completion of the smooth Lipschitz functions in the `C^{0,α}`
  norm.
* `TauCeti.not_memLittleHolder_of_eqOn_norm_rpow`, `TauCeti.not_memLittleHolder_norm_rpow` and
  `TauCeti.HolderSpace.littleHolder_ne_top`: the cusp `x ↦ ‖x‖ ^ α`, `0 < α ≤ 1`, is `α`-Hölder
  (`TauCeti.holderWith_norm_rpow`) but has difference quotient `1` between `0` and every other
  point, so no function agreeing with it near `0` is little Hölder. Truncated at height `1`, and
  taken along a unit vector of any nontrivial target, it is a bounded Hölder function outside
  `h^{0,α}`. So for `α < 1`, in positive dimension, the smooth Lipschitz functions are not dense in
  the full Hölder space.
* `TauCeti.CkHolderSpace.isClosed_littleHolder`: `h^{k,α}` is closed in the `C^{k,α}` norm, hence
  a Banach space when `F` is complete.
* `TauCeti.CkHolderSpace.exists_mem_smoothBoundedDerivatives_norm_sub_lt`,
  `TauCeti.CkHolderSpace.littleHolder_subset_closure` and
  `TauCeti.CkHolderSpace.littleHolder_eq_closure`: on a finite-dimensional real normed space, an
  element of `h^{k,α}` is approximated in the `C^{k,α}` norm by its convolutions with normalized
  bumps, which lie in the subspace `TauCeti.CkHolderSpace.smoothBoundedDerivatives` of smooth maps
  with bounded derivatives of every order. Convolution commutes with the derivatives through order
  `k`, so the lower derivatives converge uniformly, being Lipschitz, and the top one converges in
  the Hölder norm as in the case `k = 0`. For `α < 1` smooth maps with
  bounded derivatives have Lipschitz `k`-th derivative, so `h^{k,α}` is exactly their closure,
  and the Banach space `h^{k,α}` is their completion in the `C^{k,α}` norm.
* `TauCeti.CkHolderSpace.exists_mem_smoothBoundedDerivatives_tsupport_subset_norm_sub_lt` and
  `CkHolderSpace.exists_mem_smoothBoundedDerivatives_hasCompactSupport_tsupport_subset_norm_sub_lt`:
  the approximants can be supported within any distance `r > 0` of the support, so a compactly
  supported element of `h^{k,α}` inside an open set `U` is a limit of compactly supported smooth
  maps inside `U`.
* `TauCeti.CkHolderSpace.mapsTo_littleHolder`: on a finite-dimensional real normed space, a
  bounded operator of spaces of bounded `C^{k,α}` maps sending the smooth maps with bounded
  derivatives into `h^{k',α'}` sends all of `h^{k,α}` into `h^{k',α'}`.

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

/-- Characterization of `MemLittleHolder`: for every `ε > 0` there is `δ > 0` such that
`dist (f x) (f y) ≤ ε * dist x y ^ α` whenever `dist x y < δ`. -/
theorem memLittleHolder_iff [PseudoMetricSpace Y] {α : ℝ≥0} {f : X → Y} :
    MemLittleHolder α f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → dist (f x) (f y) ≤ ε * dist x y ^ (α : ℝ) :=
  Iff.rfl

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

/-- Postcomposition with a Lipschitz map preserves little Hölder continuity. -/
theorem _root_.LipschitzWith.comp_memLittleHolder [PseudoMetricSpace Y] {Z : Type*}
    [PseudoMetricSpace Z] {K α : ℝ≥0} {g : Y → Z} (hg : LipschitzWith K g) {f : X → Y}
    (hf : MemLittleHolder α f) : MemLittleHolder α (g ∘ f) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  have hK : (K : ℝ) / (K + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  calc dist (g (f x)) (g (f y)) ≤ K * dist (f x) (f y) := hg.dist_le_mul _ _
    _ ≤ K * (ε / (K + 1) * dist x y ^ (α : ℝ)) := by gcongr; exact h x y hxy
    _ = K / (K + 1) * (ε * dist x y ^ (α : ℝ)) := by ring
    _ ≤ ε * dist x y ^ (α : ℝ) := mul_le_of_le_one_left (by positivity) hK

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

/-- The negation of a little Hölder function is little Hölder. -/
theorem MemLittleHolder.neg (hf : MemLittleHolder α f) : MemLittleHolder α (-f) := by
  simpa only [MemLittleHolder, Pi.neg_apply, dist_neg_neg] using hf

/-- A scalar multiple of a little Hölder function is little Hölder. -/
theorem MemLittleHolder.const_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 Y]
    (hf : MemLittleHolder α f) (c : 𝕜) : MemLittleHolder α (c • f) :=
  (lipschitzWith_smul c).comp_memLittleHolder hf

/-- The difference of two little Hölder functions is little Hölder. -/
theorem MemLittleHolder.sub (hf : MemLittleHolder α f) (hg : MemLittleHolder α g) :
    MemLittleHolder α (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Predicate

/-! ### The cusp -/

section Cusp

variable {E : Type*} {α : ℝ≥0}

/-- A real function that agrees with the cusp `x ↦ ‖x‖ ^ α`, `α > 0`, on a ball about `0` is not
little Hölder: its `α`-Hölder difference quotient between `0` and every other point of the ball is
`1`, so its quotients do not tend to zero at small scales. -/
theorem not_memLittleHolder_of_eqOn_norm_rpow [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (hα : 0 < α) {f : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : EqOn f (fun x ↦ ‖x‖ ^ (α : ℝ)) (ball 0 r)) : ¬ MemLittleHolder α f := by
  intro h
  obtain ⟨δ, hδ, hδh⟩ := h (1 / 2) one_half_pos
  set s := min δ r / 2
  have hs : 0 < s := half_pos (lt_min hδ hr)
  have hsδr : s < min δ r := half_lt_self (lt_min hδ hr)
  obtain ⟨x, hx⟩ := exists_norm_eq E hs.le
  have hfx : f x = s ^ (α : ℝ) :=
    (hf (mem_ball_zero_iff.2 (hx ▸ hsδr.trans_le (min_le_right _ _)))).trans (by simp only [hx])
  have hf0 : f 0 = 0 := (hf (mem_ball_self hr)).trans <| by
    simp only [norm_zero, Real.zero_rpow (NNReal.coe_pos.2 hα).ne']
  have hpos : 0 < s ^ (α : ℝ) := Real.rpow_pos_of_pos hs _
  have key := hδh x 0 (by rw [dist_zero_right, hx]; exact hsδr.trans_le (min_le_left _ _))
  rw [hfx, hf0, Real.dist_eq, sub_zero, abs_of_pos hpos, dist_zero_right, hx] at key
  linarith

/-- **The cusp is not little Hölder.** For `α > 0` the function `x ↦ ‖x‖ ^ α` has `α`-Hölder
difference quotient `1` between `0` and every other point, so its quotients do not tend to zero at
small scales. -/
theorem not_memLittleHolder_norm_rpow [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (hα : 0 < α) :
    ¬ MemLittleHolder α (fun x : E ↦ ‖x‖ ^ (α : ℝ)) :=
  not_memLittleHolder_of_eqOn_norm_rpow hα one_pos (eqOn_refl _ _)

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

/-- **Mollification approximates little Hölder functions.** A little `α`-Hölder
function on a finite-dimensional space is approximated in the supremum-plus-Hölder norm by smooth
Lipschitz functions: its convolutions with normalized bumps at small enough scales. -/
theorem exists_contDiff_lipschitzWith_norm_sub_lt (f : HolderSpace α E Y)
    (hf : f ∈ littleHolder α E Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : HolderSpace α E Y, ContDiff ℝ ∞ g ∧ (∃ K, LipschitzWith K g) ∧ ‖f - g‖ < ε := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hη : 0 < ε / 4 := by positivity
  obtain ⟨δ₀, hδ₀, hδ₀f⟩ := (mem_littleHolder_iff.1 hf) (ε / 4) hη
  -- Mollify at the scale `δ = min δ₀ 1`, below which the quotients of `f` are at most `ε / 4`.
  set δ := min δ₀ 1
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
  have hg₀M : ∀ w, ‖g₀ w‖ ≤ M := ρ.norm_normed_convolution_le (Eventually.of_forall hM)
  -- `g₀` is bounded and inherits the Hölder bound of `f`, so it lies in the Hölder space.
  let g₁ : E →ᵇ Y := .ofNormedAddCommGroup g₀ hg₀smooth.continuous M hg₀M
  have hg₁ : MemHolder α (g₁ : E → Y) := by
    have hcoe : (g₁ : E → Y) = g₀ := by ext x; simp [g₁]
    rw [hcoe]
    refine ⟨‖f‖₊, holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦
      ρ.dist_normed_convolution_le_of_dist_sub_le f.continuous fun t ↦ ?_⟩
    simpa only [dist_sub_right] using f.holderWith_nnnorm.dist_le (x - t) (y - t)
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
  · obtain ⟨g, hg, hgK, hfg⟩ := exists_contDiff_lipschitzWith_norm_sub_lt f hf hε
    exact ⟨g, ⟨hg, hgK⟩, by rwa [dist_eq_norm]⟩
  · exact closure_minimal (fun g ⟨_, K, hK⟩ ↦ hK.memLittleHolder hα) isClosed_littleHolder

end Mollification

/-- **The little Hölder space is a proper subspace** in positive dimension, for `0 < α ≤ 1` and
every nontrivial target: for a unit vector `v`, the function `x ↦ min (‖x‖ ^ α) 1 • v`, the cusp
truncated at height `1` along `v`, is a bounded `α`-Hölder function whose Hölder quotients do not
tend to zero at small scales. -/
theorem littleHolder_ne_top {α : ℝ≥0} {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Nontrivial Y] (hα0 : 0 < α)
    (hα1 : α ≤ 1) : littleHolder α E Y ≠ ⊤ := by
  obtain ⟨v, hv⟩ := exists_norm_eq Y zero_le_one
  let c : E → ℝ := fun x ↦ min (‖x‖ ^ (α : ℝ)) 1
  have hc0 : ∀ x, 0 ≤ c x := fun x ↦ le_min (by positivity) zero_le_one
  have hc : HolderWith 1 α c := by
    have h := (LipschitzWith.id.min_const 1).holderWith.comp (holderWith_norm_rpow (E := E) hα1)
    rw [NNReal.one_rpow, mul_one, one_mul] at h
    exact h
  -- Along the unit vector `v`, the truncated cusp keeps its Hölder bound and its norm.
  let g : E → Y := LinearIsometry.toSpanSingleton ℝ Y hv ∘ c
  have hg : HolderWith 1 α g := (LinearIsometry.toSpanSingleton ℝ Y hv).isometry.comp_holderWith hc
  have hgc : ∀ x, ‖g x‖ = c x := fun x ↦ by
    simp only [g, Function.comp_apply, LinearIsometry.norm_map, Real.norm_of_nonneg (hc0 x)]
  let f : HolderSpace α E Y :=
    ofBoundedContinuousFunction (.ofNormedAddCommGroup g (hg.continuous hα0) 1
      fun x ↦ (hgc x).trans_le (min_le_right _ _)) hg.memHolder
  have hfg : ∀ y, f y = g y := fun y ↦ (ofBoundedContinuousFunction_apply _ _ y).trans (by simp)
  -- Below height `1` the norm of the truncated cusp is the cusp.
  refine fun htop ↦ not_memLittleHolder_of_eqOn_norm_rpow hα0 one_pos (f := fun x ↦ ‖f x‖)
    (fun x hx ↦ ?_) (lipschitzWith_one_norm.comp_memLittleHolder
      (mem_littleHolder_iff.1 (htop ▸ Submodule.mem_top (x := f))))
  simp only [hfg, hgc, c]
  exact min_eq_left (Real.rpow_le_one (norm_nonneg x) (mem_ball_zero_iff.1 hx).le α.coe_nonneg)

end HolderSpace

/-! ### Little Hölder spaces of higher order -/

namespace CkHolderSpace

section Definition

variable (k : ℕ) (α : ℝ≥0) (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **little Hölder space** `h^{k,α}`: the bounded `C^{k,α}` maps whose `k`-th iterated
derivative has `α`-Hölder difference quotients tending to zero at small scales. It is the preimage
of the little Hölder space `HolderSpace.littleHolder` of derivative fields under the `k`-th
derivative map `CkHolderSpace.iteratedFDerivHolderL`. -/
def littleHolder : Submodule ℝ (CkHolderSpace k α E F) :=
  (HolderSpace.littleHolder α E (E [×k]→L[ℝ] F)).comap
    (iteratedFDerivHolderL : CkHolderSpace k α E F →L[ℝ] _).toLinearMap

variable {k α E F}

/-- A bounded `C^{k,α}` map lies in `h^{k,α}` exactly when its `k`-th derivative is little
`α`-Hölder. -/
@[simp]
theorem mem_littleHolder_iff {f : CkHolderSpace k α E F} :
    f ∈ littleHolder k α E F ↔ MemLittleHolder α (_root_.iteratedFDeriv ℝ k f) := by
  simp [littleHolder]

/-- **The little Hölder space `h^{k,α}` is closed** in the `C^{k,α}` norm. -/
theorem isClosed_littleHolder :
    IsClosed (littleHolder k α E F : Set (CkHolderSpace k α E F)) := by
  rw [littleHolder, Submodule.comap_coe, ContinuousLinearMap.coe_coe]
  exact HolderSpace.isClosed_littleHolder.preimage iteratedFDerivHolderL.continuous

/-- The little Hölder space `h^{k,α}` of a complete space is a Banach space. -/
instance [CompleteSpace F] : CompleteSpace (littleHolder k α E F) :=
  isClosed_littleHolder.completeSpace_coe

variable (k α E F) in
/-- The bounded `C^{k,α}` maps that are smooth with all derivatives bounded, as a subspace of
`CkHolderSpace k α E F`: the preimage of `TauCeti.smoothBoundedDerivatives` under the coercion to
functions. On a finite-dimensional space, `h^{k,α}` lies in their closure
(`CkHolderSpace.littleHolder_subset_closure`), with equality when `α < 1`
(`CkHolderSpace.littleHolder_eq_closure`). -/
def smoothBoundedDerivatives : Submodule ℝ (CkHolderSpace k α E F) :=
  (TauCeti.smoothBoundedDerivatives ℝ E F).comap
    ({ toFun := (⇑)
       map_add' := coe_add
       map_smul' := coe_smul } : CkHolderSpace k α E F →ₗ[ℝ] E → F)

/-- Membership in `smoothBoundedDerivatives` is smoothness together with a global bound on each
derivative. -/
@[simp]
theorem mem_smoothBoundedDerivatives_iff {g : CkHolderSpace k α E F} :
    g ∈ smoothBoundedDerivatives k α E F ↔
      ContDiff ℝ ∞ g ∧ ∀ i, ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C :=
  TauCeti.mem_smoothBoundedDerivatives ℝ E F

/-- For `α < 1`, a bounded `C^{k,α}` map that is `C^{k+1}` with bounded `(k+1)`-th derivative
lies in `h^{k,α}`, since its `k`-th derivative is Lipschitz. -/
theorem mem_littleHolder_of_contDiff_succ (hα : α < 1) {g : CkHolderSpace k α E F}
    (hg : ContDiff ℝ (k + 1) g) {C : ℝ}
    (hC : ∀ x, ‖_root_.iteratedFDeriv ℝ (k + 1) g x‖ ≤ C) : g ∈ littleHolder k α E F :=
  mem_littleHolder_iff.2 <| (hg.lipschitzWith_iteratedFDeriv (lt_add_one k)
    fun x ↦ (hC x).trans (Real.le_coe_toNNReal C)).memLittleHolder hα

end Definition

/-! ### Density of smooth maps -/

section Mollification

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The convolution of a bounded `C^{k,α}` map `f` with a normalized bump is a smooth bounded
`C^{k,α}` map `g` with bounded derivatives of every order, and the derivatives of `f - g` through
order `k` are those of `f` minus their convolutions with the bump. -/
private theorem exists_contDiff_iteratedFDeriv_sub_eq [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (f : CkHolderSpace k α E F) (ρ : ContDiffBump (0 : E)) :
    ∃ g ∈ smoothBoundedDerivatives k α E F, ⇑g = ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ⇑f ∧
      ∀ i ≤ k, _root_.iteratedFDeriv ℝ i ⇑(f - g) =
        _root_.iteratedFDeriv ℝ i f - ρ.normed μ ⋆[lsmul ℝ ℝ, μ] _root_.iteratedFDeriv ℝ i f := by
  set g₀ : E → F := ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hD (i : ℕ) (hi : i ≤ k) : _root_.iteratedFDeriv ℝ i g₀ =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] _root_.iteratedFDeriv ℝ i f :=
    ρ.iteratedFDeriv_normed_convolution (N := k) f.contDiff (by exact_mod_cast hi)
  have hg₀ : ContDiff ℝ ∞ g₀ := ρ.hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) ρ.contDiff_normed f.contDiff.continuous.locallyIntegrable
  have hg₀b (i : ℕ) : ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i g₀ x‖ ≤ C :=
    ⟨_, ρ.hasCompactSupport_normed.norm_iteratedFDeriv_convolution_left_le (N := i)
      ρ.contDiff_normed le_rfl f.contDiff.continuous.locallyIntegrable f.norm_apply_le⟩
  -- Convolution with the nonnegative normalized bump keeps the Hölder constant of `Dᵏ f`.
  obtain ⟨C, hC⟩ := f.memHolder_iteratedFDeriv
  have hg₀h : MemHolder α (_root_.iteratedFDeriv ℝ k g₀) := by
    rw [hD k le_rfl]
    refine ⟨C, holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦
      ρ.dist_normed_convolution_le_of_dist_sub_le
        (f.contDiff.continuous_iteratedFDeriv le_rfl) fun t ↦ ?_⟩
    simpa only [dist_sub_right] using hC.dist_le (x - t) (y - t)
  let g : CkHolderSpace k α E F :=
    ofContDiff g₀ (hg₀.of_le (by exact_mod_cast le_top)) (fun i _ ↦ hg₀b i) hg₀h
  have hg : ⇑g = g₀ := coe_ofContDiff _ _ _ _
  refine ⟨g, mem_smoothBoundedDerivatives_iff.2 ⟨hg ▸ hg₀, hg ▸ hg₀b⟩, hg, fun i hi ↦ ?_⟩
  have hfi : ContDiff ℝ i f := f.contDiff.of_le (by exact_mod_cast hi)
  have hgi : ContDiff ℝ i g₀ := hg₀.of_le (by exact_mod_cast le_top)
  rw [coe_sub, hg, iteratedFDeriv_sub hfi hgi, hD i hi]

/-- **Mollification approximates elements of `h^{k,α}` with support control.** An element `f` of
the little Hölder space `h^{k,α}` on a finite-dimensional space is approximated in the `C^{k,α}`
norm by smooth maps `g` all of whose derivatives are bounded, supported within any prescribed
distance `r > 0` of the support of `f`: its convolutions with normalized bumps at small enough
scales. In particular a compactly supported `f` is approximated by smooth maps supported in
any given neighbourhood of its support. -/
theorem exists_mem_smoothBoundedDerivatives_tsupport_subset_norm_sub_lt
    (f : CkHolderSpace k α E F) (hf : f ∈ littleHolder k α E F) {ε : ℝ} (hε : 0 < ε) {r : ℝ}
    (hr : 0 < r) :
    ∃ g ∈ smoothBoundedDerivatives k α E F,
      tsupport g ⊆ Metric.cthickening r (tsupport f) ∧ ‖f - g‖ < ε := by
  borelize E
  -- Each derivative of `f - ρ ⋆ f` will be at most `η`, and the Hölder constant of the top one
  -- at most `2 η`, so that `‖f - ρ ⋆ f‖ ≤ (k + 3) η < ε`.
  set η : ℝ := ε / (4 * (k + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ₀, hδ₀, hδ₀f⟩ := (mem_littleHolder_iff.1 hf) η hη
  -- Mollify at a scale `δ` below `δ₀`, below `1`, with `‖f‖ δ ≤ η`, and below `r`.
  set δ := min (min δ₀ (min 1 (η / (‖f‖ + 1)))) r
  have hδ : 0 < δ := lt_min (lt_min hδ₀ (lt_min one_pos (by positivity))) hr
  obtain ⟨hδδ₀, hδ1, hδη, hδr⟩ : δ ≤ δ₀ ∧ δ ≤ 1 ∧ δ ≤ η / (‖f‖ + 1) ∧ δ ≤ r := by simp [δ]
  have hfδ : ‖f‖ * δ ≤ η := by
    rw [le_div_iff₀ (by positivity)] at hδη
    nlinarith [norm_nonneg f]
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  obtain ⟨g, hg, hgf, hsub⟩ :=
    exists_contDiff_iteratedFDeriv_sub_eq (μ := Measure.addHaar) f ρ
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hgf]
    refine (ρ.tsupport_normed_convolution_subset (μ := Measure.addHaar)).trans ?_
    rintro _ ⟨y, hy, x, hx, rfl⟩
    exact mem_cthickening_of_dist_le _ x _ _ hx
      (by simpa [dist_eq_norm] using (mem_closedBall_zero_iff.1 hy).trans hδr)
  -- Below the scale `δ`, the top derivative of `f` has Hölder quotients at most `η`.
  have hloc : ∀ x y, dist x y < ρ.rOut → dist (_root_.iteratedFDeriv ℝ k f x)
      (_root_.iteratedFDeriv ℝ k f y) ≤ η * dist x y ^ (α : ℝ) :=
    fun x y hxy ↦ hδ₀f x y (hxy.trans_le hδδ₀)
  have hk : Continuous (_root_.iteratedFDeriv ℝ k f) := f.contDiff.continuous_iteratedFDeriv le_rfl
  have hbound (i : ℕ) (hi : i ≤ k) (x : E) : ‖_root_.iteratedFDeriv ℝ i ⇑(f - g) x‖ ≤ η := by
    rw [hsub i hi, Pi.sub_apply, ← dist_eq_norm, dist_comm]
    rcases hi.lt_or_eq with hi | rfl
    · -- Below the top order, the derivative of `f` is `‖f‖`-Lipschitz.
      have hlip : LipschitzWith ‖f‖₊ (_root_.iteratedFDeriv ℝ i f) :=
        f.contDiff.lipschitzWith_iteratedFDeriv hi fun x ↦ f.norm_iteratedFDeriv_apply_le hi x
      refine (ρ.dist_normed_convolution_le
        (hlip.continuous.aestronglyMeasurable) fun y hy ↦ ?_).trans hfδ
      exact (hlip.dist_le_mul y x).trans (by rw [coe_nnNorm]; gcongr; exact (mem_ball.1 hy).le)
    · refine (ρ.dist_normed_convolution_le_mul_rpow hk hloc hη.le x).trans ?_
      exact mul_le_of_le_one_right hη.le (Real.rpow_le_one hδ.le hδ1 α.coe_nonneg)
  have hhol : HolderWith (2 * η).toNNReal α (_root_.iteratedFDeriv ℝ k ⇑(f - g)) := by
    rw [hsub k le_rfl]
    exact ρ.holderWith_sub_normed_convolution hk hloc hη.le
  calc ‖f - g‖ ≤ (k + 1) * η + (2 * η).toNNReal :=
        norm_le_of_norm_iteratedFDeriv_le_of_holderWith hbound hhol
    _ = (k + 3) * ε / (4 * (k + 1)) := by
        rw [Real.coe_toNNReal _ (by positivity), hη_def]
        field_simp
        ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- **Mollification approximates elements of `h^{k,α}`.** An element of the little Hölder space
`h^{k,α}` on a finite-dimensional space is approximated in the `C^{k,α}` norm by smooth maps all
of whose derivatives are bounded: its convolutions with normalized bumps at small enough scales. -/
theorem exists_mem_smoothBoundedDerivatives_norm_sub_lt (f : CkHolderSpace k α E F)
    (hf : f ∈ littleHolder k α E F) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ smoothBoundedDerivatives k α E F, ‖f - g‖ < ε :=
  have ⟨g, hg, _, hfg⟩ :=
    exists_mem_smoothBoundedDerivatives_tsupport_subset_norm_sub_lt f hf hε one_pos
  ⟨g, hg, hfg⟩

/-- **Compactly supported elements of `h^{k,α}` are limits of compactly supported smooth maps.**
On a finite-dimensional space, an element `f` of the little Hölder space `h^{k,α}` whose support
is compact and lies in an open set `U` is approximated in the `C^{k,α}` norm by smooth maps with
bounded derivatives whose supports are compact and lie in `U`. This is the Euclidean step in
approximating sections of a vector bundle chart by chart after a cutoff. -/
theorem exists_mem_smoothBoundedDerivatives_hasCompactSupport_tsupport_subset_norm_sub_lt
    (f : CkHolderSpace k α E F) (hf : f ∈ littleHolder k α E F) (hfc : HasCompactSupport f)
    {U : Set E} (hU : IsOpen U) (hfU : tsupport f ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ smoothBoundedDerivatives k α E F,
      HasCompactSupport g ∧ tsupport g ⊆ U ∧ ‖f - g‖ < ε := by
  obtain ⟨r, hr, hrU⟩ := IsCompact.exists_cthickening_subset_open hfc hU hfU
  obtain ⟨g, hg, hgr, hfg⟩ :=
    exists_mem_smoothBoundedDerivatives_tsupport_subset_norm_sub_lt f hf hε hr
  exact ⟨g, hg, (IsCompact.cthickening hfc).of_isClosed_subset (isClosed_tsupport _) hgr,
    hgr.trans hrU, hfg⟩

/-- **Smooth maps are dense in the little Hölder space.** On a finite-dimensional real normed
space `E`, every element of the little Hölder space `h^{k,α}(E, F)` is a limit, in the `C^{k,α}`
norm, of smooth maps all of whose derivatives are bounded. -/
theorem littleHolder_subset_closure :
    (littleHolder k α E F : Set (CkHolderSpace k α E F)) ⊆
      closure (smoothBoundedDerivatives k α E F) := fun f hf ↦
  Metric.mem_closure_iff.2 fun ε hε ↦
    have ⟨g, hg, hfg⟩ := exists_mem_smoothBoundedDerivatives_norm_sub_lt f hf hε
    ⟨g, hg, by rwa [dist_eq_norm]⟩

/-- **The little Hölder space is the closure of the smooth maps.** For `α < 1` and a
finite-dimensional real normed space `E`, the little Hölder space `h^{k,α}(E, F)` is the closure,
in the `C^{k,α}` norm, of the smooth maps all of whose derivatives are bounded. So `h^{k,α}` is the
completion of these smooth maps in the `C^{k,α}` norm. -/
theorem littleHolder_eq_closure (hα : α < 1) :
    (littleHolder k α E F : Set (CkHolderSpace k α E F)) =
      closure (smoothBoundedDerivatives k α E F) := by
  refine littleHolder_subset_closure.antisymm
    (closure_minimal (fun g hg ↦ ?_) isClosed_littleHolder)
  obtain ⟨hg, hgb⟩ := mem_smoothBoundedDerivatives_iff.1 hg
  obtain ⟨C, hC⟩ := hgb (k + 1)
  exact mem_littleHolder_of_contDiff_succ hα (hg.of_le (by exact_mod_cast le_top)) hC

/-- **Bounded operators restrict to the little Hölder spaces.** On a finite-dimensional real
normed space `E`, a continuous linear map between spaces of bounded `C^{k,α}` maps that sends
every smooth map with bounded derivatives into the little Hölder space `h^{k',α'}` sends all of
`h^{k,α}` into `h^{k',α'}`. -/
theorem mapsTo_littleHolder {k' : ℕ} {α' : ℝ≥0} {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (T : CkHolderSpace k α E F →L[ℝ] CkHolderSpace k' α' E' F')
    (hT : ∀ g ∈ smoothBoundedDerivatives k α E F, T g ∈ littleHolder k' α' E' F') :
    MapsTo T (littleHolder k α E F) (littleHolder k' α' E' F') := by
  have h : MapsTo T (smoothBoundedDerivatives k α E F) (littleHolder k' α' E' F') := hT
  have h' := (h.closure T.continuous).mono_left littleHolder_subset_closure
  rwa [isClosed_littleHolder.closure_eq] at h'

end Mollification

end CkHolderSpace

end TauCeti
