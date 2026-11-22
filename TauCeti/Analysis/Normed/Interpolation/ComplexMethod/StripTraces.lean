/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Complex.VerticalStrip.Basic
public import TauCeti.Analysis.Complex.VerticalStrip.Gaussian
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Admissible strip functions and boundary traces for the complex method

For a compatible couple `(X₀, X₁)` of complex normed spaces, this file develops the Banach space
`CompatibleCouple.stripTraces` of boundary traces of admissible functions on the vertical strip
`0 ≤ re z ≤ 1`, together with evaluation `CompatibleCouple.stripEval z` and Gaussian damping
`CompatibleCouple.isStripFunction_stripGaussian_smul`.

## Main declarations

* `CompatibleCouple.IsBoundedStripFunction`, `CompatibleCouple.IsStripFunction`: holomorphic strip
  functions with bounded continuous (respectively, `C₀`) boundary traces.
* `CompatibleCouple.stripTraces`: the submodule of admissible boundary traces in
  `C₀(ℝ, X₀) × C₀(ℝ, X₁)`, complete when `X₀` and `X₁` are complete.
* `CompatibleCouple.stripFunction`, `CompatibleCouple.stripEval`: the canonical admissible function
  determined by a boundary trace pair and its contractive evaluation at `z : ℂ`.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines Filter Set Topology
open scoped BoundedContinuousFunction ZeroAtInfty

namespace TauCeti

open Complex.HadamardThreeLines

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Admissible functions on the strip -/

/-- `F` is a *bounded-boundary strip function* for `C`, with bounded continuous boundary traces
`g = (g₀, g₁) : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)` on `re z = 0` and `re z = 1`. -/
structure IsBoundedStripFunction (F : ℂ → C.SumSpace) (g : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)) : Prop where
  /-- `F` is holomorphic on the open strip and continuous on its closure. -/
  diffContOnCl : DiffContOnCl ℂ F (verticalStrip 0 1)
  /-- `F` is bounded on the closed strip. -/
  isBounded : Bornology.IsBounded (F '' verticalClosedStrip 0 1)
  /-- On `re z = 0`, `F` takes the values of `g₀` in `X₀`. -/
  apply_mul_I (t : ℝ) : F (t * I) = C.fstToSum (g.1 t)
  /-- On `re z = 1`, `F` takes the values of `g₁` in `X₁`. -/
  apply_one_add_mul_I (t : ℝ) : F (1 + t * I) = C.sndToSum (g.2 t)

namespace IsBoundedStripFunction
variable {C} {F G : ℂ → C.SumSpace} {g h : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)}

theorem exists_norm_le (hF : C.IsBoundedStripFunction F g) :
    ∃ M, ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ M :=
  let ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hF.isBounded
  ⟨M, fun _ hz => hM _ (mem_image_of_mem F hz)⟩

theorem zero : C.IsBoundedStripFunction 0 0 :=
  ⟨diffContOnCl_const (c := 0),
    (Bornology.isBounded_singleton (x := 0)).subset fun _ ⟨_, _, h⟩ => h.symm,
    fun _ => by simp, fun _ => by simp⟩

theorem const (x : C.inter) : C.IsBoundedStripFunction (fun _ => C.fstToSum (C.interFst x))
    (.const ℝ (C.interFst x), .const ℝ (C.interSnd x)) :=
  ⟨diffContOnCl_const, (Bornology.isBounded_singleton (x := _)).subset fun _ ⟨_, _, h⟩ => h.symm,
    fun _ => by simp, fun _ => by simpa using C.fstToSum_interFst x⟩

theorem add (hF : C.IsBoundedStripFunction F g) (hG : C.IsBoundedStripFunction G h) :
    C.IsBoundedStripFunction (F + G) (g + h) := by
  obtain ⟨M, hM⟩ := hF.exists_norm_le; obtain ⟨N, hN⟩ := hG.exists_norm_le
  exact ⟨hF.diffContOnCl.add hG.diffContOnCl, isBounded_iff_forall_norm_le.2 ⟨M + N,
    by rintro _ ⟨z, hz, rfl⟩; exact (norm_add_le _ _).trans (add_le_add (hM z hz) (hN z hz))⟩,
    fun _ => by simp [hF.apply_mul_I, hG.apply_mul_I],
    fun _ => by simp [hF.apply_one_add_mul_I, hG.apply_one_add_mul_I]⟩

theorem const_smul (hF : C.IsBoundedStripFunction F g) (c : ℂ) :
    C.IsBoundedStripFunction (c • F) (c • g) := by
  obtain ⟨M, hM⟩ := hF.exists_norm_le
  exact ⟨hF.diffContOnCl.const_smul c, isBounded_iff_forall_norm_le.2 ⟨‖c‖ * M, by
    rintro _ ⟨z, hz, rfl⟩
    exact (norm_smul c _).trans_le (mul_le_mul_of_nonneg_left (hM z hz) (norm_nonneg c))⟩,
    fun _ => by simp [hF.apply_mul_I], fun _ => by simp [hF.apply_one_add_mul_I]⟩

theorem smul (hF : C.IsBoundedStripFunction F g) {c : ℂ → ℂ}
    (hc : DiffContOnCl ℂ c (verticalStrip 0 1)) {K : ℝ}
    (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) {g' : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)}
    (hg'₀ : ∀ t, g'.1 t = c (t * I) • g.1 t) (hg'₁ : ∀ t, g'.2 t = c (1 + t * I) • g.2 t) :
    C.IsBoundedStripFunction (fun z => c z • F z) g' := by
  obtain ⟨M, hM⟩ := hF.exists_norm_le
  exact ⟨hc.smul hF.diffContOnCl, isBounded_iff_forall_norm_le.2 ⟨K * M, by
      rintro _ ⟨z, hz, rfl⟩; exact (norm_smul _ _).trans_le
        (mul_le_mul (hK z hz) (hM z hz) (norm_nonneg _) ((norm_nonneg _).trans (hK z hz)))⟩,
    fun _ => by simp [hF.apply_mul_I, hg'₀], fun _ => by simp [hF.apply_one_add_mul_I, hg'₁]⟩

theorem sub (hF : C.IsBoundedStripFunction F g) (hG : C.IsBoundedStripFunction G h) :
    C.IsBoundedStripFunction (F - G) (g - h) := by
  simpa [sub_eq_add_neg] using hF.add (hG.const_smul (-1))

/-- **Three-lines bound** for bounded-boundary strip functions. -/
theorem norm_le_rpow_mul_rpow (hF : C.IsBoundedStripFunction F g) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖F z‖ ≤ ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re := by
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) :=
    let ⟨M, hM⟩ := hF.exists_norm_le; ⟨M, by rintro _ ⟨w, hw, rfl⟩; exact hM w hw⟩
  refine norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hF.diffContOnCl hB
    (fun w hw => ?_) (fun w hw => ?_)
  · rw [← re_add_im w, hw, ofReal_zero, zero_add, hF.apply_mul_I]
    exact (C.norm_fstToSum_le _).trans (g.1.norm_coe_le_norm _)
  · rw [← re_add_im w, hw, ofReal_one, hF.apply_one_add_mul_I]
    exact (C.norm_sndToSum_le _).trans (g.2.norm_coe_le_norm _)

/-- **Maximum principle** for bounded-boundary strip functions. -/
theorem norm_le (hF : C.IsBoundedStripFunction F g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F z‖ ≤ ‖g‖ :=
  (hF.norm_le_rpow_mul_rpow hz).trans (g.norm_fst_rpow_mul_norm_snd_rpow_le hz)

/-- A bounded-boundary strip function is determined on the closed strip by its boundary traces. -/
theorem eqOn (hF : C.IsBoundedStripFunction F g) (hG : C.IsBoundedStripFunction G g) :
    EqOn F G (verticalClosedStrip 0 1) := fun _ hz => by
  simpa [sub_eq_zero] using (hF.sub hG).norm_le hz
end IsBoundedStripFunction

/-- `F` is an *admissible function* for the complex method, with boundary traces
`g = (g₀, g₁)`: it is bounded on the closed strip `0 ≤ re z ≤ 1`, holomorphic on the open strip
and continuous up to its boundary, and its values on the boundary lines are
`F (t * I) = g₀ t ∈ X₀` and `F (1 + t * I) = g₁ t ∈ X₁`. The traces are continuous and vanish at
infinity since `g₀ : C₀(ℝ, X₀)` and `g₁ : C₀(ℝ, X₁)`. -/
structure IsStripFunction (F : ℂ → C.SumSpace) (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) : Prop where
  /-- `F` is holomorphic on the open strip and continuous on the closed strip. -/
  diffContOnCl : DiffContOnCl ℂ F (verticalStrip 0 1)
  /-- `F` is bounded on the closed strip. -/
  isBounded : Bornology.IsBounded (F '' verticalClosedStrip 0 1)
  /-- On the line `re z = 0`, `F` takes the values of `g₀` in `X₀`. -/
  apply_mul_I (t : ℝ) : F (t * I) = C.fstToSum (g.1 t)
  /-- On the line `re z = 1`, `F` takes the values of `g₁` in `X₁`. -/
  apply_one_add_mul_I (t : ℝ) : F (1 + t * I) = C.sndToSum (g.2 t)

namespace IsStripFunction

variable {C} {F G : ℂ → C.SumSpace} {g h : C₀(ℝ, X₀) × C₀(ℝ, X₁)}

/-- `F` with boundary traces `g : C₀(ℝ, X₀) × C₀(ℝ, X₁)` is an admissible strip function if and
only if it is a bounded-boundary strip function for `(g.1.toBCF, g.2.toBCF)`. -/
theorem isBoundedStripFunction_iff :
    C.IsStripFunction F g ↔ C.IsBoundedStripFunction F (g.1.toBCF, g.2.toBCF) :=
  ⟨fun hF => ⟨hF.diffContOnCl, hF.isBounded, hF.apply_mul_I, hF.apply_one_add_mul_I⟩,
    fun hF => ⟨hF.diffContOnCl, hF.isBounded, hF.apply_mul_I, hF.apply_one_add_mul_I⟩⟩

/-- Every admissible strip function with traces in `C₀` is a bounded-boundary strip function. -/
theorem isBoundedStripFunction (hF : C.IsStripFunction F g) :
    C.IsBoundedStripFunction F (g.1.toBCF, g.2.toBCF) := isBoundedStripFunction_iff.1 hF

/-- An admissible function is bounded in norm on the closed strip. -/
theorem exists_norm_le (hF : C.IsStripFunction F g) :
    ∃ M, ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ M := hF.isBoundedStripFunction.exists_norm_le

theorem zero : C.IsStripFunction 0 0 :=
  isBoundedStripFunction_iff.2 (by convert IsBoundedStripFunction.zero (C := C) <;> ext <;> simp)

theorem add (hF : C.IsStripFunction F g) (hG : C.IsStripFunction G h) :
    C.IsStripFunction (F + G) (g + h) :=
  isBoundedStripFunction_iff.2
    (by convert hF.isBoundedStripFunction.add hG.isBoundedStripFunction <;> ext <;> simp)

theorem const_smul (hF : C.IsStripFunction F g) (c : ℂ) : C.IsStripFunction (c • F) (c • g) :=
  isBoundedStripFunction_iff.2 (by convert hF.isBoundedStripFunction.const_smul c <;> ext <;> simp)

/-- Multiplying an admissible function by a scalar function `c`, holomorphic on the open strip,
continuous up to its boundary and bounded on the closed strip, gives an admissible function. Its
boundary traces are any `g'` with `g'₀ t = c (t * I) • g₀ t` and `g'₁ t = c (1 + t * I) • g₁ t`;
they are supplied by the caller, since they vanish at infinity only as products. -/
theorem smul (hF : C.IsStripFunction F g) {c : ℂ → ℂ} (hc : DiffContOnCl ℂ c (verticalStrip 0 1))
    {K : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) {g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hg'₀ : ∀ t, g'.1 t = c (t * I) • g.1 t) (hg'₁ : ∀ t, g'.2 t = c (1 + t * I) • g.2 t) :
    C.IsStripFunction (fun z => c z • F z) g' :=
  isBoundedStripFunction_iff.2 (hF.isBoundedStripFunction.smul hc hK hg'₀ hg'₁)

theorem sub (hF : C.IsStripFunction F g) (hG : C.IsStripFunction G h) :
    C.IsStripFunction (F - G) (g - h) := by
  simpa [sub_eq_add_neg] using hF.add (hG.const_smul (-1))

/-- **Three-lines bound.** On the closed strip, an admissible function with boundary traces
`(g₀, g₁)` satisfies `‖F z‖ ≤ ‖g₀‖ ^ (1 - re z) * ‖g₁‖ ^ re z`. -/
theorem norm_le_rpow_mul_rpow (hF : C.IsStripFunction F g) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖F z‖ ≤ ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re := by
  simpa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
    hF.isBoundedStripFunction.norm_le_rpow_mul_rpow hz

/-- **Maximum principle.** On the closed strip, an admissible function is bounded in the sum norm
by the norm `max ‖g₀‖ ‖g₁‖` of its boundary traces. -/
theorem norm_le (hF : C.IsStripFunction F g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F z‖ ≤ ‖g‖ :=
  (hF.norm_le_rpow_mul_rpow hz).trans (g.norm_fst_rpow_mul_norm_snd_rpow_le hz)

/-- An admissible function is determined on the closed strip by its boundary traces. -/
theorem eqOn (hF : C.IsStripFunction F g) (hG : C.IsStripFunction G g) :
    EqOn F G (verticalClosedStrip 0 1) :=
  hF.isBoundedStripFunction.eqOn hG.isBoundedStripFunction

end IsStripFunction

variable {C} in
/-- **Gaussian damping of a bounded holomorphic function.** Let `Φ` be holomorphic on the strip,
continuous and bounded on its closure, with values `f₀ t ∈ X₀` on the line `re z = 0` and
`f₁ t ∈ X₁` on the line `re z = 1` for bounded continuous `f₀`, `f₁`. For `δ > 0` the function
`exp (δ (z - θ)²) Φ z` is admissible, with the damped boundary values as traces. -/
theorem isStripFunction_stripGaussian_smul {Φ : ℂ → C.SumSpace} {f₀ : ℝ →ᵇ X₀} {f₁ : ℝ →ᵇ X₁}
    {δ : ℝ} (hδ : 0 < δ) (θ : ℝ)
    (hΦ : DiffContOnCl ℂ Φ (verticalStrip 0 1))
    (hb : Bornology.IsBounded (Φ '' verticalClosedStrip 0 1))
    (h₀ : ∀ t : ℝ, Φ (t * I) = C.fstToSum (f₀ t))
    (h₁ : ∀ t : ℝ, Φ (1 + t * I) = C.sndToSum (f₁ t)) :
    C.IsStripFunction (fun z => stripGaussian δ θ z • Φ z)
      (stripGaussianSMul hδ θ 0 f₀, stripGaussianSMul hδ θ 1 f₁) where
  diffContOnCl := (differentiable_stripGaussian δ θ).diffContOnCl.smul hΦ
  isBounded := by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
    refine isBounded_iff_forall_norm_le.2 ⟨Real.exp (δ * (|θ| + 1) ^ 2) * M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_smul]
    exact mul_le_mul (norm_stripGaussian_le hδ.le θ hz) (hM _ (mem_image_of_mem Φ hz))
      (norm_nonneg _) (Real.exp_pos _).le
  apply_mul_I t := by simp [h₀]
  apply_one_add_mul_I t := by simp [h₁]

namespace IsBoundedStripFunction
variable {C} {F : ℂ → C.SumSpace} {g : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)}

/-- Damping a bounded-boundary strip function by `exp (δ (z - θ)²)` (`δ > 0`) yields an admissible
strip function with `C₀` boundary traces of norm at most `exp (δ (|θ| + 1)²) ‖g‖`. -/
theorem exists_isStripFunction_stripGaussian_smul_and_norm_le (hF : C.IsBoundedStripFunction F g)
    {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) : ∃ g' : C₀(ℝ, X₀) × C₀(ℝ, X₁),
      C.IsStripFunction (fun z => stripGaussian δ θ z • F z) g' ∧
        ‖g'‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖g‖ :=
  ⟨_, isStripFunction_stripGaussian_smul hδ θ hF.diffContOnCl hF.isBounded hF.apply_mul_I
      hF.apply_one_add_mul_I,
    norm_prod_le_iff.2 ⟨(norm_stripGaussianSMul_le hδ θ ⟨le_rfl, zero_le_one⟩ g.1).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le g) (by positivity)),
      (norm_stripGaussianSMul_le hδ θ ⟨zero_le_one, le_rfl⟩ g.2).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le g) (by positivity))⟩⟩
end IsBoundedStripFunction

/-! ### The space of boundary traces -/

/-- The boundary traces `(g₀, g₁)` of the admissible functions of the complex method, a submodule
of `C₀(ℝ, X₀) × C₀(ℝ, X₁)`. With the induced norm `max ‖g₀‖ ‖g₁‖` it is isometric to the space of
admissible functions with the norm `max_j sup_t ‖F (j + i t)‖_{X_j}`, since an admissible function
is determined by its traces (`CompatibleCouple.IsStripFunction.eqOn`). -/
def stripTraces : Submodule ℂ (C₀(ℝ, X₀) × C₀(ℝ, X₁)) where
  carrier := {g | ∃ F, C.IsStripFunction F g}
  add_mem' := fun ⟨F, hF⟩ ⟨G, hG⟩ => ⟨F + G, hF.add hG⟩
  zero_mem' := ⟨0, IsStripFunction.zero⟩
  smul_mem' c _ := fun ⟨F, hF⟩ => ⟨c • F, hF.const_smul c⟩

variable {C} in
theorem mem_stripTraces_iff {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} :
    g ∈ C.stripTraces ↔ ∃ F, C.IsStripFunction F g :=
  Iff.rfl

/-- The admissible function with boundary traces `g`, extended by zero off the closed strip. On
the closed strip it agrees with every admissible function with these traces
(`CompatibleCouple.stripFunction_eq`). -/
def stripFunction (g : C.stripTraces) : ℂ → C.SumSpace :=
  (verticalClosedStrip 0 1).indicator (mem_stripTraces_iff.1 g.property).choose

theorem isStripFunction_stripFunction (g : C.stripTraces) :
    C.IsStripFunction (C.stripFunction g) g := by
  have hF := (mem_stripTraces_iff.1 g.property).choose_spec
  have hEq : EqOn (C.stripFunction g) (mem_stripTraces_iff.1 g.property).choose
      (verticalClosedStrip 0 1) := fun z hz => indicator_of_mem hz _
  exact
    { diffContOnCl :=
        ⟨hF.diffContOnCl.differentiableOn.congr
            (hEq.mono (verticalStrip_subset_verticalClosedStrip 0 1)),
          hF.diffContOnCl.continuousOn.congr (hEq.mono (closure_verticalStrip_subset 0 1))⟩
      isBounded := by
        rw [hEq.image_eq]
        exact hF.isBounded
      apply_mul_I t :=
        (hEq (by simp)).trans (hF.apply_mul_I t)
      apply_one_add_mul_I t :=
        (hEq (by simp)).trans (hF.apply_one_add_mul_I t) }

variable {C} in
theorem stripFunction_eq {g : C.stripTraces} {F : ℂ → C.SumSpace} (hF : C.IsStripFunction F g)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : C.stripFunction g z = F z :=
  (C.isStripFunction_stripFunction g).eqOn hF hz

@[simp]
theorem stripFunction_mul_I (g : C.stripTraces) (t : ℝ) :
    C.stripFunction g (t * I) = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) :=
  (C.isStripFunction_stripFunction g).apply_mul_I t

@[simp]
theorem stripFunction_one_add_mul_I (g : C.stripTraces) (t : ℝ) :
    C.stripFunction g (1 + t * I) = C.sndToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t) :=
  (C.isStripFunction_stripFunction g).apply_one_add_mul_I t

@[simp] theorem stripFunction_apply_zero (g : C.stripTraces) :
    C.stripFunction g 0 = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) := by
  simpa using C.stripFunction_mul_I g 0

@[simp] theorem stripFunction_apply_one (g : C.stripTraces) :
    C.stripFunction g 1 = C.sndToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0) := by
  simpa using C.stripFunction_one_add_mul_I g 0

@[simp]
theorem stripFunction_eq_zero (g : C.stripTraces) {z : ℂ} (hz : z ∉ verticalClosedStrip 0 1) :
    C.stripFunction g z = 0 :=
  indicator_of_notMem hz _

@[simp]
theorem stripFunction_zero : C.stripFunction 0 = 0 := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact stripFunction_eq IsStripFunction.zero hz
  · exact C.stripFunction_eq_zero _ hz

@[simp]
theorem stripFunction_add (g h : C.stripTraces) :
    C.stripFunction (g + h) = C.stripFunction g + C.stripFunction h := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact stripFunction_eq
      ((C.isStripFunction_stripFunction g).add (C.isStripFunction_stripFunction h)) hz
  · simp [C.stripFunction_eq_zero _ hz]

@[simp]
theorem stripFunction_smul (c : ℂ) (g : C.stripTraces) :
    C.stripFunction (c • g) = c • C.stripFunction g := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact stripFunction_eq ((C.isStripFunction_stripFunction g).const_smul c) hz
  · simp [C.stripFunction_eq_zero _ hz]

/-- The admissible function with traces `g` is bounded by `‖g‖` everywhere. -/
theorem norm_stripFunction_le (g : C.stripTraces) (z : ℂ) : ‖C.stripFunction g z‖ ≤ ‖g‖ := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact (C.isStripFunction_stripFunction g).norm_le hz
  · simp [C.stripFunction_eq_zero _ hz]

/-- Evaluation `g ↦ F z` of the admissible function with traces `g` at a point `z`, a continuous
linear map of norm at most one. It vanishes for `z` off the closed strip
(`CompatibleCouple.stripEval_eq_zero`). -/
def stripEval (z : ℂ) : C.stripTraces →L[ℂ] C.SumSpace :=
  LinearMap.mkContinuous
    { toFun g := C.stripFunction g z
      map_add' g h := by rw [stripFunction_add, Pi.add_apply]
      map_smul' c g := by rw [stripFunction_smul, Pi.smul_apply, RingHom.id_apply] }
    1 fun g => by simpa using C.norm_stripFunction_le g z

@[simp]
theorem stripEval_apply (z : ℂ) (g : C.stripTraces) : C.stripEval z g = C.stripFunction g z :=
  (rfl)

/-- Evaluation off the closed strip vanishes. -/
@[simp]
theorem stripEval_eq_zero {z : ℂ} (hz : z ∉ verticalClosedStrip 0 1) : C.stripEval z = 0 :=
  ContinuousLinearMap.ext fun g => C.stripFunction_eq_zero g hz

theorem norm_stripEval_le (z : ℂ) : ‖C.stripEval z‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    simpa using C.norm_stripFunction_le g z

/-- The boundary traces of the admissible functions form a closed subspace when `X₀` and `X₁` are
complete: a uniform limit of admissible functions on the closed strip is admissible. -/
theorem isClosed_stripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    IsClosed (C.stripTraces : Set (C₀(ℝ, X₀) × C₀(ℝ, X₁))) := by
  refine IsSeqClosed.isClosed fun {u g} hu hlim => ?_
  set F : ℕ → ℂ → C.SumSpace := fun n => C.stripFunction ⟨u n, hu n⟩
  have hF (n : ℕ) : C.IsStripFunction (F n) (u n) := C.isStripFunction_stripFunction _
  have hdist (n m : ℕ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      ‖F n z - F m z‖ ≤ ‖u n - u m‖ :=
    ((hF n).sub (hF m)).norm_le hz
  -- on the closed strip, `F n` converges pointwise, since the traces form a Cauchy sequence
  have hcauchy {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : CauchySeq fun n => F n z := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
    exact ⟨N, fun n hn => by
      rw [dist_eq_norm]
      exact (hdist n N hz).trans_lt (by simpa [dist_eq_norm] using hN n hn)⟩
  set F' : ℂ → C.SumSpace := fun z => limUnder atTop fun n => F n z
  have hlimz {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      Tendsto (fun n => F n z) atTop (𝓝 (F' z)) :=
    (hcauchy hz).tendsto_limUnder
  -- the convergence is uniform on the closed strip, with rate `‖u n - g‖`
  have hunif : TendstoUniformlyOn F F' atTop (verticalClosedStrip 0 1) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    have hg : Tendsto (fun n => ‖u n - g‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hlim
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn z hz
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt ?_ hn
    exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub (hlimz hz)).norm
      (tendsto_const_nhds.sub hlim).norm fun m => hdist n m hz
  have hbound {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : ‖F' z‖ ≤ ‖g‖ :=
    le_of_tendsto_of_tendsto' (hlimz hz).norm hlim.norm fun n => (hF n).norm_le hz
  have hfst (t : ℝ) : Tendsto (fun n => (u n).1 t) atTop (𝓝 (g.1 t)) := by
    simpa [Function.comp_def] using
      ((ZeroAtInftyContinuousMap.evalCLM ℂ t).continuous.tendsto _).comp
        ((continuous_fst.tendsto g).comp hlim)
  have hsnd (t : ℝ) : Tendsto (fun n => (u n).2 t) atTop (𝓝 (g.2 t)) := by
    simpa [Function.comp_def] using
      ((ZeroAtInftyContinuousMap.evalCLM ℂ t).continuous.tendsto _).comp
        ((continuous_snd.tendsto g).comp hlim)
  -- the limit `F'` is admissible with traces `g`
  refine ⟨F', ⟨⟨?_, ?_⟩, ?_, fun t => ?_, fun t => ?_⟩⟩
  · exact (hunif.mono (verticalStrip_subset_verticalClosedStrip 0 1)).tendstoLocallyUniformlyOn
      |>.differentiableOn (.of_forall fun n => (hF n).diffContOnCl.differentiableOn)
        (isOpen_verticalStrip 0 1)
  · exact (hunif.mono (closure_verticalStrip_subset 0 1)).continuousOn
      (.of_forall fun n => (hF n).diffContOnCl.continuousOn)
  · refine isBounded_iff_forall_norm_le.2 ⟨‖g‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hbound hz
  · refine tendsto_nhds_unique (hlimz (by simp)) ?_
    simp_rw [(hF _).apply_mul_I]
    exact (C.fstToSum.continuous.tendsto _).comp (hfst t)
  · refine tendsto_nhds_unique (hlimz (by simp)) ?_
    simp_rw [(hF _).apply_one_add_mul_I]
    exact (C.sndToSum.continuous.tendsto _).comp (hsnd t)

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.stripTraces :=
  C.isClosed_stripTraces.completeSpace_coe

instance (z : ℂ) : IsClosed ((C.stripEval z).ker : Set C.stripTraces) :=
  (C.stripEval z).isClosed_ker

end CompatibleCouple

end TauCeti
