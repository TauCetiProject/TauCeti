/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.VerticalStrip
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The complex interpolation method

For a compatible couple `(X₀, X₁)` of complex normed spaces and `0 ≤ θ ≤ 1`, Calderón's complex
interpolation space `[X₀, X₁]_θ` consists of the values `f θ` of the bounded continuous functions
`f` from the closed strip `0 ≤ re z ≤ 1` to the sum space `X₀ + X₁` that are holomorphic in the
open strip and whose boundary functions `t ↦ f (j + t i)`, `j = 0, 1`, are continuous functions
into `X_j` vanishing at infinity. Its norm is the infimum of
`max (sup_t ‖f (t i)‖_{X₀}) (sup_t ‖f (1 + t i)‖_{X₁})` over all such `f` with value `u` at `θ`.
This is one of the two basic interpolation functors, besides the real `K`-method. It is the
functor behind the Riesz–Thorin theorem: for Lebesgue spaces `[L^{p₀}, L^{p₁}]_θ = L^{p_θ}` with
`1 / p_θ = (1 - θ) / p₀ + θ / p₁` (Bergh–Löfström, Theorem 5.1.1), and Bessel potential spaces
interpolate in the same way.

By the three lines theorem such a function is determined on the closed strip by its two boundary
functions, and its sup norm there is at most the norm above. We therefore realise Calderón's
space of functions as the space `CompatibleCouple.stripSpace` of pairs of boundary
functions `(g₀, g₁) : C₀(ℝ, X₀) × C₀(ℝ, X₁)` that extend to an admissible function (one satisfying
the strip conditions, `CompatibleCouple.HasStripBoundary`); the product
norm `max ‖g₀‖ ‖g₁‖` is exactly Calderón's norm. The interpolation space
`CompatibleCouple.ComplexMethodSpace θ` is the quotient of `stripSpace` by the kernel of the
evaluation at `θ`, with its quotient norm.

## Main declarations

* `CompatibleCouple.HasStripBoundary f g₀ g₁`: `f` is admissible: bounded and continuous on
  the closed strip, holomorphic inside, with boundary values `g₀`, `g₁`, on which no continuity or
  decay is imposed. `HasStripBoundary.norm_le_interp` is the three lines bound
  `‖f z‖ ≤ a ^ (1 - re z) * b ^ re z` and `HasStripBoundary.eqOn` the resulting uniqueness.
* `CompatibleCouple.stripSpace`: the space of admissible boundary pairs. It is closed in
  `C₀(ℝ, X₀) × C₀(ℝ, X₁)` (`isClosed_stripSpace`), so it is a Banach space when `X₀` and `X₁` are:
  a uniform limit of holomorphic functions is holomorphic.
* `CompatibleCouple.stripEval z`: the evaluation at a point `z` of the strip, of norm at most `1`.
* `CompatibleCouple.ComplexMethodSpace θ`: the complex interpolation space `[X₀, X₁]_θ`, a
  Banach space when `X₀` and `X₁` are. Its norm is described by `ComplexMethodSpace.norm_lt_iff`.
* `ComplexMethodSpace.toSum`: the injective inclusion `[X₀, X₁]_θ → X₀ + X₁`, of norm at most `1`
  (`norm_toSum_le`).
* `ComplexMethodSpace.ofInter`: the inclusion `X₀ ∩ X₁ → [X₀, X₁]_θ`, of norm at most `1`
  (`norm_ofInter_le`). It is built from the admissible functions `exp (δ (z - θ) ^ 2) • x`,
  `δ > 0`, whose norms tend to `‖x‖` as `δ → 0`.
* `ComplexMethodSpace.map`: **exactness of the complex method** (Bergh–Löfström, Theorem 4.1.2).
  A map of sum spaces restricting to `T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` induces
  `[X₀, X₁]_θ → [Y₀, Y₁]_θ`; if `T₀`, `T₁` have norms at most `M₀, M₁ ≥ 0`, it has norm at most
  `M₀ ^ (1 - θ) * M₁ ^ θ` (`norm_map_le`).
* `ComplexMethodSpace.reflEquiv`: for the couple `(X, X)`, `[X, X]_θ` is `X` with its own norm.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Lemma 4.1.1 and Theorem 4.1.2).
-/

public noncomputable section

open Set Filter Complex Topology Complex.HadamardThreeLines
open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap (evalCLM norm_coe_le_norm)

namespace TauCeti

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Admissible functions on the strip -/

/-- `f : ℂ → X₀ + X₁` is an admissible function of the complex method with boundary functions
`g₀ : ℝ → X₀` and `g₁ : ℝ → X₁`: it is bounded and continuous on the closed strip
`0 ≤ re z ≤ 1`, holomorphic in the open strip `0 < re z < 1`, and `f (t i) = g₀ t`,
`f (1 + t i) = g₁ t` for real `t`. Values of `f` off the closed strip play no role.

No continuity or decay is required of `g₀` and `g₁`. Calderón's space also asks the boundary
functions to be continuous and vanish at infinity; it is `CompatibleCouple.stripSpace`, the
pairs `(g₀, g₁)` in `C₀(ℝ, X₀) × C₀(ℝ, X₁)` with an admissible `f`. -/
structure HasStripBoundary (f : ℂ → C.SumSpace) (g₀ : ℝ → X₀) (g₁ : ℝ → X₁) : Prop where
  /-- `f` is holomorphic in the open strip and continuous on its closure. -/
  diffContOnCl : DiffContOnCl ℂ f (verticalStrip 0 1)
  /-- `f` is bounded on the closed strip. -/
  bddAbove : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)
  /-- On the line `re z = 0`, `f` takes the values of `g₀`. -/
  apply_mul_I : ∀ t : ℝ, f (t * I) = C.fstToSum (g₀ t)
  /-- On the line `re z = 1`, `f` takes the values of `g₁`. -/
  apply_one_add_mul_I : ∀ t : ℝ, f (1 + t * I) = C.sndToSum (g₁ t)

private theorem ofReal_mem_verticalClosedStrip {θ : ℝ} :
    (θ : ℂ) ∈ verticalClosedStrip 0 1 ↔ θ ∈ Icc 0 1 := by
  simp [verticalClosedStrip]

private theorem mul_I_mem_verticalClosedStrip (t : ℝ) : (t : ℂ) * I ∈ verticalClosedStrip 0 1 := by
  simp [verticalClosedStrip]

private theorem one_add_mul_I_mem_verticalClosedStrip (t : ℝ) :
    1 + (t : ℂ) * I ∈ verticalClosedStrip 0 1 := by
  simp [verticalClosedStrip]

namespace HasStripBoundary

variable {C} {f f' : ℂ → C.SumSpace} {g₀ g₀' : ℝ → X₀} {g₁ g₁' : ℝ → X₁}

theorem zero : C.HasStripBoundary 0 0 0 where
  diffContOnCl := diffContOnCl_const
  bddAbove := bddAbove_norm_comp_image_iff.2 ⟨0, by simp⟩
  apply_mul_I t := by simp
  apply_one_add_mul_I t := by simp

theorem add (h : C.HasStripBoundary f g₀ g₁) (h' : C.HasStripBoundary f' g₀' g₁') :
    C.HasStripBoundary (f + f') (g₀ + g₀') (g₁ + g₁') where
  diffContOnCl := h.diffContOnCl.add h'.diffContOnCl
  bddAbove := by
    obtain ⟨A, hA⟩ := bddAbove_norm_comp_image_iff.1 h.bddAbove
    obtain ⟨B, hB⟩ := bddAbove_norm_comp_image_iff.1 h'.bddAbove
    exact bddAbove_norm_comp_image_iff.2
      ⟨A + B, fun z hz => (norm_add_le _ _).trans (add_le_add (hA z hz) (hB z hz))⟩
  apply_mul_I t := by simp [h.apply_mul_I, h'.apply_mul_I]
  apply_one_add_mul_I t := by simp [h.apply_one_add_mul_I, h'.apply_one_add_mul_I]

/-- Multiplying an admissible function by a bounded scalar function, holomorphic in the open
strip and continuous on its closure, gives an admissible function. -/
theorem smul {φ : ℂ → ℂ} (hφ : DiffContOnCl ℂ φ (verticalStrip 0 1))
    (hφb : BddAbove ((norm ∘ φ) '' verticalClosedStrip 0 1)) (h : C.HasStripBoundary f g₀ g₁) :
    C.HasStripBoundary (fun z => φ z • f z) (fun t => φ (t * I) • g₀ t)
      (fun t => φ (1 + t * I) • g₁ t) where
  diffContOnCl := hφ.smul h.diffContOnCl
  bddAbove := by
    obtain ⟨A, hA⟩ := bddAbove_norm_comp_image_iff.1 hφb
    obtain ⟨B, hB⟩ := bddAbove_norm_comp_image_iff.1 h.bddAbove
    refine bddAbove_norm_comp_image_iff.2 ⟨A * B, fun z hz => ?_⟩
    rw [norm_smul]
    exact mul_le_mul (hA z hz) (hB z hz) (norm_nonneg _) ((norm_nonneg _).trans (hA z hz))
  apply_mul_I t := by simp [h.apply_mul_I]
  apply_one_add_mul_I t := by simp [h.apply_one_add_mul_I]

theorem const_smul (c : ℂ) (h : C.HasStripBoundary f g₀ g₁) :
    C.HasStripBoundary (c • f) (c • g₀) (c • g₁) :=
  h.smul (φ := fun _ => c) diffContOnCl_const
    (bddAbove_norm_comp_image_iff.2 ⟨‖c‖, fun _ _ => le_rfl⟩)

theorem neg (h : C.HasStripBoundary f g₀ g₁) : C.HasStripBoundary (-f) (-g₀) (-g₁) := by
  simpa using h.const_smul (-1)

theorem sub (h : C.HasStripBoundary f g₀ g₁) (h' : C.HasStripBoundary f' g₀' g₁') :
    C.HasStripBoundary (f - f') (g₀ - g₀') (g₁ - g₁') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

variable {Y₀ Y₁ W : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W}

/-- A map of sum spaces compatible with maps `T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` sends admissible
functions to admissible functions. -/
theorem map (h : C.HasStripBoundary f g₀ g₁) (T : C.SumSpace →L[ℂ] D.SumSpace) {T₀ : X₀ → Y₀}
    {T₁ : X₁ → Y₁} (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) :
    D.HasStripBoundary (T ∘ f) (T₀ ∘ g₀) (T₁ ∘ g₁) where
  diffContOnCl := T.differentiable.comp_diffContOnCl h.diffContOnCl
  bddAbove := by
    obtain ⟨A, hA⟩ := bddAbove_norm_comp_image_iff.1 h.bddAbove
    exact bddAbove_norm_comp_image_iff.2 ⟨‖T‖ * A, fun z hz =>
      (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hA z hz) (norm_nonneg _))⟩
  apply_mul_I t := by simp [h.apply_mul_I, hT₀]
  apply_one_add_mul_I t := by simp [h.apply_one_add_mul_I, hT₁]

/-- **Three lines bound** for admissible functions: if the boundary functions are bounded by
`a` and `b`, then `‖f z‖ ≤ a ^ (1 - re z) * b ^ re z` on the closed strip. -/
theorem norm_le_interp (h : C.HasStripBoundary f g₀ g₁) {a b : ℝ} (ha : ∀ t, ‖g₀ t‖ ≤ a)
    (hb : ∀ t, ‖g₁ t‖ ≤ b) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖f z‖ ≤ a ^ (1 - z.re) * b ^ z.re := by
  refine norm_le_interp_of_mem_verticalClosedStrip₀₁' f hz h.diffContOnCl h.bddAbove
    (fun w hw => ?_) (fun w hw => ?_)
  · have hw : w = (w.im : ℂ) * I := by
      apply Complex.ext <;> simp_all
    rw [hw, h.apply_mul_I]
    exact (C.norm_fstToSum_le _).trans (ha _)
  · have hw : w = 1 + (w.im : ℂ) * I := by
      apply Complex.ext <;> simp_all
    rw [hw, h.apply_one_add_mul_I]
    exact (C.norm_sndToSum_le _).trans (hb _)

/-- An admissible function is bounded on the closed strip by the larger of the bounds of its
boundary functions. -/
theorem norm_le_max (h : C.HasStripBoundary f g₀ g₁) {a b : ℝ} (ha : ∀ t, ‖g₀ t‖ ≤ a)
    (hb : ∀ t, ‖g₁ t‖ ≤ b) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : ‖f z‖ ≤ max a b := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have hx0 : 0 ≤ z.re := hz.1
  have hx1 : z.re ≤ 1 := hz.2
  calc ‖f z‖ ≤ a ^ (1 - z.re) * b ^ z.re := h.norm_le_interp ha hb hz
    _ ≤ max a b ^ (1 - z.re) * max a b ^ z.re :=
        mul_le_mul (Real.rpow_le_rpow ha0 (le_max_left a b) (sub_nonneg.2 hx1))
          (Real.rpow_le_rpow hb0 (le_max_right a b) hx0) (by positivity) (by positivity)
    _ = max a b := by
        rw [← Real.rpow_add' (le_max_of_le_left ha0) (by norm_num), sub_add_cancel,
          Real.rpow_one]

/-- An admissible function is determined on the closed strip by its boundary functions. -/
theorem eqOn (h : C.HasStripBoundary f g₀ g₁) (h' : C.HasStripBoundary f' g₀ g₁) :
    EqOn f f' (verticalClosedStrip 0 1) := fun z hz => by
  have := (h.sub h').norm_le_max (a := 0) (b := 0) (by simp) (by simp) hz
  rw [max_self, Pi.sub_apply] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end HasStripBoundary

/-- The constant function with value in the intersection is admissible, with constant boundary
functions. Unless the value is `0` these do not vanish at infinity, so they are not a boundary
pair of `stripSpace`; `ComplexMethodSpace.ofInter` corrects this with a Gaussian factor. -/
theorem hasStripBoundary_const (x : C.inter) :
    C.HasStripBoundary (fun _ => C.fstToSum (C.interFst x)) (fun _ => C.interFst x)
      (fun _ => C.interSnd x) where
  diffContOnCl := diffContOnCl_const
  bddAbove := bddAbove_norm_comp_image_iff.2 ⟨_, fun _ _ => le_rfl⟩
  apply_mul_I _ := rfl
  apply_one_add_mul_I _ := C.fstToSum_interFst x

/-! ### The space of admissible boundary pairs -/

/-- Calderón's space of functions of the complex method, realised by their boundary
functions: the pairs `(g₀, g₁) : C₀(ℝ, X₀) × C₀(ℝ, X₁)` that are the boundary functions of an
admissible function (`HasStripBoundary`). The admissible function is unique on the closed strip
(`HasStripBoundary.eqOn`), and the product norm `max ‖g₀‖ ‖g₁‖` is Calderón's norm. -/
def stripSpace : Submodule ℂ (C₀(ℝ, X₀) × C₀(ℝ, X₁)) where
  carrier := {g | ∃ f, C.HasStripBoundary f g.1 g.2}
  zero_mem' := ⟨0, by simpa using HasStripBoundary.zero⟩
  add_mem' := fun ⟨f, hf⟩ ⟨f', hf'⟩ => ⟨f + f', by simpa using hf.add hf'⟩
  smul_mem' c _ := fun ⟨f, hf⟩ => ⟨c • f, by simpa using hf.const_smul c⟩

theorem mem_stripSpace_iff {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} :
    g ∈ C.stripSpace ↔ ∃ f, C.HasStripBoundary f g.1 g.2 :=
  Iff.rfl

variable {C}

/-- The admissible function with boundary functions `g`, on the closed strip; it is set to zero
off the closed strip. -/
private def stripExtend (g : C.stripSpace) : ℂ → C.SumSpace :=
  (verticalClosedStrip 0 1).indicator (C.mem_stripSpace_iff.1 g.2).choose

private theorem hasStripBoundary_stripExtend (g : C.stripSpace) :
    C.HasStripBoundary (stripExtend g) (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
      (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 := by
  set F := (C.mem_stripSpace_iff.1 g.2).choose
  have hF : C.HasStripBoundary F _ _ := (C.mem_stripSpace_iff.1 g.2).choose_spec
  have heq : EqOn (stripExtend g) F (verticalClosedStrip 0 1) := fun z hz => indicator_of_mem hz F
  refine ⟨⟨hF.diffContOnCl.1.congr fun z hz =>
      heq (verticalStrip_subset_verticalClosedStrip 0 1 hz),
    hF.diffContOnCl.2.congr fun z hz => heq (closure_verticalStrip zero_ne_one ▸ hz)⟩, ?_,
    fun t => ?_, fun t => ?_⟩
  · obtain ⟨A, hA⟩ := bddAbove_norm_comp_image_iff.1 hF.bddAbove
    exact bddAbove_norm_comp_image_iff.2 ⟨A, fun z hz => heq hz ▸ hA z hz⟩
  · rw [heq (mul_I_mem_verticalClosedStrip t), hF.apply_mul_I]
  · rw [heq (one_add_mul_I_mem_verticalClosedStrip t), hF.apply_one_add_mul_I]

private theorem stripExtend_of_notMem (g : C.stripSpace) {z : ℂ}
    (hz : z ∉ verticalClosedStrip 0 1) : stripExtend g z = 0 :=
  indicator_of_notMem hz _

/-- `stripExtend g` is the admissible function with boundary functions `g` on the closed
strip. -/
private theorem eqOn_stripExtend {g : C.stripSpace} {f : ℂ → C.SumSpace}
    (h : C.HasStripBoundary f (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2) :
    EqOn (stripExtend g) f (verticalClosedStrip 0 1) :=
  (hasStripBoundary_stripExtend g).eqOn h

/-- The admissible function is bounded by the norm of its boundary functions. -/
private theorem norm_stripExtend_le (g : C.stripSpace) (z : ℂ) : ‖stripExtend g z‖ ≤ ‖g‖ := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · rw [← Submodule.norm_coe, Prod.norm_def]
    exact (hasStripBoundary_stripExtend g).norm_le_max (norm_coe_le_norm _) (norm_coe_le_norm _)
      hz
  · rw [stripExtend_of_notMem g hz, norm_zero]
    exact norm_nonneg _

private theorem stripExtend_add (g g' : C.stripSpace) {z : ℂ} :
    stripExtend (g + g') z = stripExtend g z + stripExtend g' z := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · have h := (hasStripBoundary_stripExtend g).add (hasStripBoundary_stripExtend g')
    exact eqOn_stripExtend (g := g + g') (by simpa using h) hz
  · simp [stripExtend_of_notMem _ hz]

private theorem stripExtend_smul (c : ℂ) (g : C.stripSpace) {z : ℂ} :
    stripExtend (c • g) z = c • stripExtend g z := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · have h := (hasStripBoundary_stripExtend g).const_smul c
    exact eqOn_stripExtend (g := c • g) (by simpa using h) hz
  · simp [stripExtend_of_notMem _ hz]

variable (C) in
/-- The evaluation at `z` of the admissible function with boundary functions `g`, a continuous
linear map of norm at most `1` (`norm_stripEval_apply_le`). It vanishes for `z` off the closed
strip. -/
def stripEval (z : ℂ) : C.stripSpace →L[ℂ] C.SumSpace :=
  LinearMap.mkContinuous
    { toFun g := stripExtend g z
      map_add' g g' := stripExtend_add g g'
      map_smul' c g := stripExtend_smul c g }
    1 fun g => by simpa using norm_stripExtend_le g z

/-- The evaluations `z ↦ stripEval z g` form an admissible function with boundary functions
`g`. -/
theorem hasStripBoundary_stripEval (g : C.stripSpace) :
    C.HasStripBoundary (fun z => C.stripEval z g) (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
      (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 :=
  hasStripBoundary_stripExtend g

/-- The evaluation of a boundary pair at a point of the closed strip is the value there of any
admissible function with these boundary functions. -/
theorem stripEval_eq {g : C.stripSpace} {f : ℂ → C.SumSpace}
    (h : C.HasStripBoundary f (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : C.stripEval z g = f z :=
  eqOn_stripExtend h hz

theorem stripEval_of_notMem {z : ℂ} (hz : z ∉ verticalClosedStrip 0 1) (g : C.stripSpace) :
    C.stripEval z g = 0 :=
  stripExtend_of_notMem g hz

theorem norm_stripEval_apply_le (z : ℂ) (g : C.stripSpace) : ‖C.stripEval z g‖ ≤ ‖g‖ :=
  norm_stripExtend_le g z

variable (C) in
/-- **Calderón's space is complete** (Bergh–Löfström, Lemma 4.1.1): the admissible boundary pairs
form a closed subspace of `C₀(ℝ, X₀) × C₀(ℝ, X₁)`. Along a convergent sequence of boundary pairs
the admissible functions converge uniformly on the closed strip, by the three lines bound, and
the limit is admissible since a uniform limit of holomorphic functions is holomorphic. -/
theorem isClosed_stripSpace [CompleteSpace X₀] [CompleteSpace X₁] :
    IsClosed (C.stripSpace : Set (C₀(ℝ, X₀) × C₀(ℝ, X₁))) := by
  refine IsSeqClosed.isClosed fun g gl hg hlim => ?_
  set G : ℕ → C.stripSpace := fun n => ⟨g n, hg n⟩
  have hF n := hasStripBoundary_stripExtend (G n)
  -- The admissible functions are uniformly Cauchy on the closed strip.
  have hdist n m : ∀ z ∈ verticalClosedStrip 0 1,
      dist (stripExtend (G n) z) (stripExtend (G m) z) ≤ dist (g n) (g m) := fun z hz => by
    rw [dist_eq_norm, dist_eq_norm, Prod.norm_def]
    refine ((hF n).sub (hF m)).norm_le_max (fun t => ?_) (fun t => ?_) hz
    · simpa using norm_coe_le_norm ((g n).1 - (g m).1) t
    · simpa using norm_coe_le_norm ((g n).2 - (g m).2) t
  have hcauchy : UniformCauchySeqOn (fun n => stripExtend (G n)) atTop
      (verticalClosedStrip 0 1) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
    exact ⟨N, fun m hm n hn z hz => (hdist m n z hz).trans_lt (hN m hm n hn)⟩
  set f : ℂ → C.SumSpace := fun z => limUnder atTop fun n => stripExtend (G n) z
  have hpt : ∀ z ∈ verticalClosedStrip 0 1,
      Tendsto (fun n => stripExtend (G n) z) atTop (𝓝 (f z)) := fun z hz =>
    (hcauchy.cauchySeq hz).tendsto_limUnder
  have hunif : TendstoUniformlyOn (fun n => stripExtend (G n)) f atTop
      (verticalClosedStrip 0 1) :=
    hcauchy.tendstoUniformlyOn_of_tendsto hpt
  -- Pointwise convergence of the boundary functions.
  have hfst (t : ℝ) : Tendsto (fun n => (g n).1 t) atTop (𝓝 (gl.1 t)) := by
    simpa [Function.comp_def] using
      ((evalCLM ℂ t).continuous.comp continuous_fst).tendsto gl |>.comp hlim
  have hsnd (t : ℝ) : Tendsto (fun n => (g n).2 t) atTop (𝓝 (gl.2 t)) := by
    simpa [Function.comp_def] using
      ((evalCLM ℂ t).continuous.comp continuous_snd).tendsto gl |>.comp hlim
  refine ⟨f, ⟨?_, ?_⟩, ?_, fun t => ?_, fun t => ?_⟩
  · exact (hunif.mono (verticalStrip_subset_verticalClosedStrip 0 1)).tendstoLocallyUniformlyOn
      |>.differentiableOn (Eventually.of_forall fun n => (hF n).diffContOnCl.differentiableOn)
        (isOpen_verticalStrip 0 1)
  · rw [closure_verticalStrip zero_ne_one]
    exact hunif.continuousOn (Frequently.of_forall fun n => by
      simpa [closure_verticalStrip zero_ne_one] using (hF n).diffContOnCl.continuousOn)
  · refine bddAbove_norm_comp_image_iff.2 ⟨‖gl‖, fun z hz => ?_⟩
    exact le_of_tendsto_of_tendsto' (hpt z hz).norm hlim.norm fun n =>
      norm_stripExtend_le (G n) z
  · exact tendsto_nhds_unique (hpt _ (mul_I_mem_verticalClosedStrip t))
      (((C.fstToSum.continuous.tendsto _).comp (hfst t)).congr fun n =>
        ((hF n).apply_mul_I t).symm)
  · exact tendsto_nhds_unique (hpt _ (one_add_mul_I_mem_verticalClosedStrip t))
      (((C.sndToSum.continuous.tendsto _).comp (hsnd t)).congr fun n =>
        ((hF n).apply_one_add_mul_I t).symm)

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.stripSpace :=
  (C.isClosed_stripSpace).completeSpace_coe

/-! ### The complex interpolation space -/

variable (C) in
/-- The boundary pairs whose admissible function vanishes at `θ`. -/
def complexKer (θ : ℝ) : Submodule ℂ C.stripSpace :=
  (C.stripEval θ).ker

@[simp]
theorem mem_complexKer_iff {θ : ℝ} {g : C.stripSpace} : g ∈ C.complexKer θ ↔ C.stripEval θ g = 0 :=
  Iff.rfl

instance (θ : ℝ) : IsClosed (C.complexKer θ : Set C.stripSpace) :=
  (C.stripEval θ).isClosed_ker

variable (C) in
/-- The complex interpolation space `[X₀, X₁]_θ` of a compatible couple: the values at `θ` of
the admissible functions, realised as the quotient of `stripSpace` by the boundary pairs whose
admissible function vanishes at `θ`, with the quotient norm
`‖u‖ = inf {max ‖g₀‖ ‖g₁‖ | (g₀, g₁) admissible with value u at θ}`
(`ComplexMethodSpace.norm_lt_iff`). It is meaningful for `0 ≤ θ ≤ 1`; for other `θ` it is the
zero space. It is a Banach space when `X₀` and `X₁` are. -/
abbrev ComplexMethodSpace (θ : ℝ) : Type _ :=
  C.stripSpace ⧸ C.complexKer θ

namespace ComplexMethodSpace

variable {θ : ℝ}

variable (θ) in
/-- The element of `[X₀, X₁]_θ` represented by an admissible boundary pair. -/
def mk : C.stripSpace →L[ℂ] C.ComplexMethodSpace θ :=
  (C.complexKer θ).mkQL

theorem mk_surjective : Function.Surjective (mk θ : C.stripSpace → C.ComplexMethodSpace θ) :=
  (C.complexKer θ).mkQ_surjective

/-- The inclusion `[X₀, X₁]_θ → X₀ + X₁`, sending the class of a boundary pair to the value at
`θ` of its admissible function. -/
def toSum : C.ComplexMethodSpace θ →L[ℂ] C.SumSpace :=
  (C.complexKer θ).liftQL (C.stripEval θ) le_rfl

@[simp]
theorem toSum_mk (g : C.stripSpace) : toSum (mk θ g) = C.stripEval θ g :=
  (rfl)

theorem toSum_injective : Function.Injective (toSum : C.ComplexMethodSpace θ → C.SumSpace) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- Elements of `[X₀, X₁]_θ` are determined by their images in the sum space. -/
@[ext]
theorem ext {u v : C.ComplexMethodSpace θ} (h : toSum u = toSum v) : u = v :=
  toSum_injective h

theorem mk_eq_iff {g : C.stripSpace} {u : C.ComplexMethodSpace θ} :
    mk θ g = u ↔ C.stripEval θ g = toSum u :=
  ⟨fun h => h ▸ (toSum_mk g).symm, fun h => ext (by rw [toSum_mk, h])⟩

theorem norm_mk_le (g : C.stripSpace) : ‖mk θ g‖ ≤ ‖g‖ :=
  Submodule.Quotient.norm_mk_le _ g

/-- The norm of `[X₀, X₁]_θ` is the infimum of the norms of the admissible boundary pairs
representing an element: strict upper bounds. -/
theorem norm_lt_iff {u : C.ComplexMethodSpace θ} {r : ℝ} :
    ‖u‖ < r ↔ ∃ g : C.stripSpace, mk θ g = u ∧ ‖g‖ < r :=
  QuotientAddGroup.norm_lt_iff

/-- The norm of `[X₀, X₁]_θ` is the infimum of the norms of the admissible boundary pairs
representing an element: lower bounds. -/
theorem le_norm_iff {u : C.ComplexMethodSpace θ} {r : ℝ} :
    r ≤ ‖u‖ ↔ ∀ g : C.stripSpace, mk θ g = u → r ≤ ‖g‖ := by
  simp only [← not_lt, norm_lt_iff, not_exists, not_and]

/-- A bound on representatives gives a bound on `[X₀, X₁]_θ`. -/
private theorem norm_le_of_forall_mk {E : Type*} [SeminormedAddCommGroup E]
    {F : C.ComplexMethodSpace θ → E} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ g : C.stripSpace, ‖F (mk θ g)‖ ≤ c * ‖g‖) (u : C.ComplexMethodSpace θ) :
    ‖F u‖ ≤ c * ‖u‖ := by
  rcases hc.eq_or_lt with rfl | hc
  · obtain ⟨g, rfl⟩ := mk_surjective u
    simpa using h g
  · rw [← div_le_iff₀' hc]
    exact le_norm_iff.2 fun g hg => by
      rw [div_le_iff₀' hc, ← hg]
      exact h g

/-- The inclusion `[X₀, X₁]_θ → X₀ + X₁` has norm at most `1`. -/
theorem norm_toSum_le (u : C.ComplexMethodSpace θ) : ‖toSum u‖ ≤ ‖u‖ := by
  simpa using norm_le_of_forall_mk (F := toSum) zero_le_one
    (fun g => by simpa using norm_stripEval_apply_le θ g) u

end ComplexMethodSpace

/-! ### The inclusion of the intersection -/

/-- The Gaussian factor `exp (δ (z - θ) ^ 2)`, used to make the boundary functions of constant
functions vanish at infinity. -/
private def gaussian (δ θ : ℝ) (z : ℂ) : ℂ :=
  cexp (δ * (z - θ) ^ 2)

private theorem norm_gaussian (δ θ : ℝ) (z : ℂ) :
    ‖gaussian δ θ z‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [gaussian, Complex.norm_exp]
  congr 1
  simp [sq]

private theorem gaussian_self (δ θ : ℝ) : gaussian δ θ θ = 1 := by
  simp [gaussian]

private theorem differentiable_gaussian (δ θ : ℝ) : Differentiable ℂ (gaussian δ θ) := by
  unfold gaussian
  fun_prop

private theorem norm_gaussian_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖gaussian δ θ z‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_gaussian]
  gcongr
  have h0 : 0 ≤ z.re := hz.1
  have h1 : z.re ≤ 1 := hz.2
  have : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [le_abs_self θ]) (by linarith [neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

private theorem tendsto_gaussian {δ : ℝ} (hδ : 0 < δ) (θ c : ℝ) :
    Tendsto (fun t : ℝ => gaussian δ θ (c + t * I)) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop := by
    simpa [Function.comp_def, Real.norm_eq_abs, sq_abs] using
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))
  have hexp : Tendsto (fun t : ℝ => δ * ((c - θ) ^ 2 - t ^ 2)) (cocompact ℝ) atBot :=
    Tendsto.const_mul_atBot hδ <| (tendsto_atBot_add_const_left _ ((c - θ) ^ 2)
      (tendsto_neg_atTop_atBot.comp hsq)).congr fun t => by simp [sub_eq_add_neg]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (Real.tendsto_exp_atBot.comp hexp).congr fun t => ?_
  simp [norm_gaussian]

/-- The boundary function `t ↦ exp (δ (c + t i - θ) ^ 2) • x`, which vanishes at infinity. -/
private def gaussianSMul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {δ : ℝ}
    (hδ : 0 < δ) (θ c : ℝ) (x : X) : C₀(ℝ, X) where
  toFun t := gaussian δ θ (c + t * I) • x
  continuous_toFun := by
    have := differentiable_gaussian δ θ
    unfold gaussian at this ⊢
    fun_prop
  zero_at_infty' := by simpa using (tendsto_gaussian hδ θ c).smul_const x

@[simp]
private theorem coe_gaussianSMul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {δ : ℝ}
    (hδ : 0 < δ) (θ c : ℝ) (x : X) :
    ⇑(gaussianSMul hδ θ c x) = fun t : ℝ => gaussian δ θ (c + t * I) • x :=
  (rfl)

variable (C) in
/-- The Gaussian `z ↦ exp (δ (z - θ) ^ 2) • x` is admissible for `x` in the intersection. -/
private theorem hasStripBoundary_gaussian_smul {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    C.HasStripBoundary (fun z => gaussian δ θ z • C.fstToSum (C.interFst x))
      (fun t => gaussian δ θ (t * I) • C.interFst x)
      (fun t => gaussian δ θ (1 + t * I) • C.interSnd x) :=
  (C.hasStripBoundary_const x).smul (differentiable_gaussian δ θ).diffContOnCl
    (bddAbove_norm_comp_image_iff.2 ⟨_, fun _ hz => norm_gaussian_le hδ.le θ hz⟩)

private theorem norm_gaussianSMul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (y : X) :
    ‖gaussianSMul hδ θ c y‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖y‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (by positivity)]
  intro t
  simp only [ZeroAtInftyContinuousMap.toBCF_apply, coe_gaussianSMul, norm_smul]
  gcongr
  exact norm_gaussian_le hδ.le θ (by simpa [verticalClosedStrip] using hc)

variable (C) in
/-- The admissible boundary pair of `z ↦ exp (δ (z - θ) ^ 2) • x` for `x` in the
intersection. -/
private def interStrip {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) : C.inter →ₗ[ℂ] C.stripSpace where
  toFun x := ⟨(gaussianSMul hδ θ 0 (C.interFst x), gaussianSMul hδ θ 1 (C.interSnd x)),
    ⟨_, by simpa using C.hasStripBoundary_gaussian_smul hδ θ x⟩⟩
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp [smul_comm c]

private theorem stripEval_interStrip {δ θ : ℝ} (hδ : 0 < δ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (x : C.inter) : C.stripEval θ (C.interStrip hδ θ x) = C.fstToSum (C.interFst x) := by
  have h := C.hasStripBoundary_gaussian_smul hδ θ x
  rw [stripEval_eq (g := C.interStrip hδ θ x) (by simpa [interStrip] using h)
    (ofReal_mem_verticalClosedStrip.2 hθ), gaussian_self, one_smul, interFst_apply]

private theorem norm_interStrip_le {δ θ : ℝ} (hδ : 0 < δ) (x : C.inter) :
    ‖C.interStrip hδ θ x‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖ := by
  rw [← Submodule.norm_coe, Prod.norm_def, CompatibleCouple.norm_inter, ← interFst_apply,
    ← interSnd_apply, mul_max_of_nonneg _ _ (Real.exp_pos _).le]
  exact max_le_max (norm_gaussianSMul_le hδ θ (c := 0) (by simp) _)
    (norm_gaussianSMul_le hδ θ (c := 1) (by simp) _)

namespace ComplexMethodSpace

variable {θ : ℝ}

variable (C θ) in
/-- The Gaussian boundary pairs of width `1`, as a continuous linear map. -/
private def interStripL : C.inter →L[ℂ] C.stripSpace :=
  (C.interStrip one_pos θ).mkContinuous (Real.exp ((|θ| + 1) ^ 2))
    fun x => (C.norm_interStrip_le one_pos x).trans_eq (by rw [one_mul])

variable (θ) in
/-- The inclusion of the intersection `X₀ ∩ X₁` into `[X₀, X₁]_θ`, of norm at most `1`
(`norm_ofInter_le`). -/
def ofInter : C.inter →L[ℂ] C.ComplexMethodSpace θ :=
  (mk (C := C) θ).comp (interStripL C θ)

private theorem ofInter_eq_mk (x : C.inter) : ofInter θ x = mk θ (C.interStrip one_pos θ x) :=
  (rfl)

/-- The class of the Gaussian boundary pair does not depend on the Gaussian's width. -/
private theorem mk_interStrip {δ : ℝ} (hδ : 0 < δ) (x : C.inter) :
    mk θ (C.interStrip hδ θ x) = ofInter θ x := by
  rw [ofInter_eq_mk, mk_eq_iff, toSum_mk]
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rw [C.stripEval_interStrip hδ hθ, C.stripEval_interStrip one_pos hθ]
  · rw [stripEval_of_notMem (by rwa [ofReal_mem_verticalClosedStrip]),
      stripEval_of_notMem (by rwa [ofReal_mem_verticalClosedStrip])]

/-- For `0 ≤ θ ≤ 1` an element `x` of the intersection is sent to `x` in the sum space. -/
@[simp]
theorem toSum_ofInter (hθ : θ ∈ Icc (0 : ℝ) 1) (x : C.inter) :
    toSum (ofInter θ x) = C.fstToSum (C.interFst x) := by
  rw [ofInter_eq_mk, toSum_mk, C.stripEval_interStrip one_pos hθ]

/-- The inclusion `X₀ ∩ X₁ → [X₀, X₁]_θ` has norm at most `1`. -/
theorem norm_ofInter_le (x : C.inter) : ‖ofInter θ x‖ ≤ ‖x‖ := by
  have hle : ∀ δ > 0, ‖ofInter θ x‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖ := fun δ hδ =>
    mk_interStrip hδ x ▸ (norm_mk_le _).trans (C.norm_interStrip_le hδ x)
  have hlim : Tendsto (fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖) (𝓝[>] 0) (𝓝 ‖x‖) := by
    have : Continuous fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖ := by fun_prop
    simpa using this.continuousWithinAt.tendsto (s := Ioi 0) (x := 0)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)

end ComplexMethodSpace

/-! ### Exactness of the complex method -/

/-- The scalar factor `M₀ ^ (z - 1) * M₁ ^ (-z)` that normalises the boundary norms of a couple
morphism with norms `M₀`, `M₁`. -/
private def weight (M₀ M₁ : ℝ) (z : ℂ) : ℂ :=
  cexp ((z - 1) * Real.log M₀ - z * Real.log M₁)

private theorem norm_weight (M₀ M₁ : ℝ) (z : ℂ) :
    ‖weight M₀ M₁ z‖ = Real.exp ((z.re - 1) * Real.log M₀ - z.re * Real.log M₁) := by
  rw [weight, Complex.norm_exp]
  congr 1
  simp

private theorem differentiable_weight (M₀ M₁ : ℝ) : Differentiable ℂ (weight M₀ M₁) := by
  unfold weight
  fun_prop

private theorem continuous_weight_mul_I (M₀ M₁ : ℝ) :
    Continuous fun t : ℝ => weight M₀ M₁ (t * I) := by
  unfold weight
  fun_prop

private theorem continuous_weight_one_add_mul_I (M₀ M₁ : ℝ) :
    Continuous fun t : ℝ => weight M₀ M₁ (1 + t * I) := by
  unfold weight
  fun_prop

private theorem norm_weight_mul_I {M₀ : ℝ} (hM₀ : 0 < M₀) (M₁ t : ℝ) :
    ‖weight M₀ M₁ (t * I)‖ = M₀⁻¹ := by
  simp [norm_weight, Real.exp_neg, Real.exp_log hM₀]

private theorem norm_weight_one_add_mul_I (M₀ : ℝ) {M₁ : ℝ} (hM₁ : 0 < M₁) (t : ℝ) :
    ‖weight M₀ M₁ (1 + t * I)‖ = M₁⁻¹ := by
  simp [norm_weight, Real.exp_neg, Real.exp_log hM₁]

private theorem bddAbove_weight (M₀ M₁ : ℝ) :
    BddAbove ((norm ∘ weight M₀ M₁) '' verticalClosedStrip 0 1) := by
  refine bddAbove_norm_comp_image_iff.2 ⟨Real.exp (|Real.log M₀| + |Real.log M₁|), fun z hz => ?_⟩
  rw [norm_weight]
  have h0 : 0 ≤ z.re := hz.1
  have h1 : z.re ≤ 1 := hz.2
  gcongr
  have e₀ : (z.re - 1) * Real.log M₀ ≤ |Real.log M₀| := by
    have := le_abs_self ((z.re - 1) * Real.log M₀)
    rw [abs_mul, abs_of_nonpos (by linarith : z.re - 1 ≤ 0)] at this
    nlinarith [abs_nonneg (Real.log M₀)]
  have e₁ : -(z.re * Real.log M₁) ≤ |Real.log M₁| := by
    have := neg_le_abs (z.re * Real.log M₁)
    rw [abs_mul, abs_of_nonneg h0] at this
    nlinarith [abs_nonneg (Real.log M₁)]
  linarith

private theorem norm_weight_ofReal_inv {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (θ : ℝ) :
    ‖weight M₀ M₁ θ‖⁻¹ = M₀ ^ (1 - θ) * M₁ ^ θ := by
  rw [norm_weight, ← Real.exp_neg, Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁,
    ← Real.exp_add]
  congr 1
  simp only [ofReal_re]
  ring

private theorem weight_ofReal_ne_zero (M₀ M₁ θ : ℝ) : weight M₀ M₁ θ ≠ 0 :=
  Complex.exp_ne_zero _

variable {Y₀ Y₁ W : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W}

/-- The boundary function `t ↦ ψ t • T (g t)` of a bounded continuous scalar function `ψ`, a
continuous linear map `T` and a function `g` vanishing at infinity. -/
private def smulMap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] (ψ : ℝ → ℂ) (hψ : Continuous ψ) {A : ℝ} (hA : ∀ t, ‖ψ t‖ ≤ A)
    (T : X →L[ℂ] Y) (g : C₀(ℝ, X)) : C₀(ℝ, Y) where
  toFun t := ψ t • T (g t)
  continuous_toFun := hψ.smul (T.continuous.comp g.continuous)
  zero_at_infty' := by
    refine squeeze_zero_norm (a := fun t => A * (‖T‖ * ‖g t‖)) (fun t => ?_) ?_
    · rw [norm_smul]
      exact mul_le_mul (hA t) (T.le_opNorm _) (norm_nonneg _) ((norm_nonneg _).trans (hA t))
    · simpa using ((g.zero_at_infty'.norm).const_mul ‖T‖).const_mul A

@[simp]
private theorem coe_smulMap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (ψ : ℝ → ℂ) (hψ : Continuous ψ) {A : ℝ}
    (hA : ∀ t, ‖ψ t‖ ≤ A) (T : X →L[ℂ] Y) (g : C₀(ℝ, X)) :
    ⇑(smulMap ψ hψ hA T g) = fun t => ψ t • T (g t) :=
  (rfl)

private theorem norm_smulMap_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M : ℝ} (hM : 0 < M) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hψM : ∀ t, ‖ψ t‖ = M⁻¹) (S : X →L[ℂ] Y) (hS : ∀ x, ‖S x‖ ≤ M * ‖x‖) (φ : C₀(ℝ, X)) :
    ‖smulMap ψ hψ (fun t => (hψM t).le) S φ‖ ≤ ‖φ‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (norm_nonneg _)]
  intro t
  rw [ZeroAtInftyContinuousMap.toBCF_apply, coe_smulMap, norm_smul, hψM, inv_mul_le_iff₀ hM]
  exact (hS _).trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm φ t) hM.le)

section Map

variable (T : C.SumSpace →L[ℂ] D.SumSpace) {T₀ : X₀ →L[ℂ] Y₀} {T₁ : X₁ →L[ℂ] Y₁}
  (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
  (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)

include hT₀ hT₁ in
/-- The admissible function `z ↦ M₀ ^ (z - 1) * M₁ ^ (-z) • T (f z)` for `f` admissible. -/
private theorem hasStripBoundary_weight_smul_map (g : C.stripSpace) :
    D.HasStripBoundary (fun z => weight M₀ M₁ z • T (stripExtend g z))
      (fun t => weight M₀ M₁ (t * I) • T₀ ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t))
      (fun t => weight M₀ M₁ (1 + t * I) • T₁ ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t)) :=
  ((hasStripBoundary_stripExtend g).map T hT₀ hT₁).smul (differentiable_weight M₀ M₁).diffContOnCl
    (bddAbove_weight M₀ M₁)

/-- The admissible boundary pairs of `z ↦ M₀ ^ (z - 1) * M₁ ^ (-z) • T (f z)`. -/
private def stripMap : C.stripSpace →ₗ[ℂ] D.stripSpace where
  toFun g := ⟨(smulMap (fun t : ℝ => weight M₀ M₁ (t * I))
      (continuous_weight_mul_I M₀ M₁) (fun t => (norm_weight_mul_I hM₀ M₁ t).le)
      T₀ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1,
    smulMap (fun t : ℝ => weight M₀ M₁ (1 + t * I))
      (continuous_weight_one_add_mul_I M₀ M₁) (fun t => (norm_weight_one_add_mul_I M₀ hM₁ t).le)
      T₁ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2),
    ⟨_, hasStripBoundary_weight_smul_map T hT₀ hT₁ g⟩⟩
  map_add' g g' := by ext <;> simp
  map_smul' c g := by ext <;> simp [smul_comm c]

private theorem stripEval_stripMap {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (g : C.stripSpace) :
    D.stripEval z (stripMap T hT₀ hT₁ hM₀ hM₁ g) = weight M₀ M₁ z • T (C.stripEval z g) := by
  have h := hasStripBoundary_weight_smul_map (M₀ := M₀) (M₁ := M₁) T hT₀ hT₁ g
  rw [stripEval_eq (g := stripMap T hT₀ hT₁ hM₀ hM₁ g) (by simpa [stripMap] using h) hz,
    stripEval_eq (hasStripBoundary_stripExtend g) hz]

private theorem norm_stripMap_le (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (g : C.stripSpace) : ‖stripMap T hT₀ hT₁ hM₀ hM₁ g‖ ≤ ‖g‖ := by
  rw [← Submodule.norm_coe, Prod.norm_def, ← Submodule.norm_coe, Prod.norm_def]
  exact max_le_max
    (norm_smulMap_le hM₀ _ (continuous_weight_mul_I M₀ M₁) (norm_weight_mul_I hM₀ M₁) _ h₀ _)
    (norm_smulMap_le hM₁ _ (continuous_weight_one_add_mul_I M₀ M₁)
      (norm_weight_one_add_mul_I M₀ hM₁) _ h₁ _)

namespace ComplexMethodSpace

variable (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) {θ : ℝ}

variable (θ) in
/-- The boundary pairs of `z ↦ (M₀ ^ (z - θ) * M₁ ^ (θ - z)) • T (f z)`, normalised so that the
value at `θ` is `T (f θ)`. -/
private def scaledStripMap : C.stripSpace →ₗ[ℂ] D.stripSpace :=
  (weight M₀ M₁ θ)⁻¹ • stripMap T hT₀ hT₁ hM₀ hM₁

private theorem stripEval_scaledStripMap (g : C.stripSpace) :
    D.stripEval θ (scaledStripMap T hT₀ hT₁ hM₀ hM₁ θ g) = T (C.stripEval θ g) := by
  rw [scaledStripMap, LinearMap.smul_apply, map_smul]
  by_cases hθ : (θ : ℂ) ∈ verticalClosedStrip 0 1
  · rw [stripEval_stripMap T hT₀ hT₁ hM₀ hM₁ hθ, smul_smul,
      inv_mul_cancel₀ (weight_ofReal_ne_zero M₀ M₁ θ), one_smul]
  · simp [stripEval_of_notMem hθ]

include h₀ h₁ in
private theorem norm_scaledStripMap_le (g : C.stripSpace) :
    ‖scaledStripMap T hT₀ hT₁ hM₀ hM₁ θ g‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖g‖ := by
  rw [scaledStripMap, LinearMap.smul_apply, norm_smul, norm_inv, norm_weight_ofReal_inv hM₀ hM₁]
  gcongr
  exact norm_stripMap_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ g

variable (θ) in
/-- `scaledStripMap` as a continuous linear map. -/
private def scaledStripMapL : C.stripSpace →L[ℂ] D.stripSpace :=
  (scaledStripMap T hT₀ hT₁ hM₀ hM₁ θ).mkContinuous (M₀ ^ (1 - θ) * M₁ ^ θ)
    (norm_scaledStripMap_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁)

/-- A continuous linear map `S` satisfies `‖S x‖ ≤ (‖S‖ + 1) * ‖x‖`, with a positive constant. -/
private theorem norm_apply_le_opNorm_add_one {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (S : X →L[ℂ] Y) (x : X) :
    ‖S x‖ ≤ (‖S‖ + 1) * ‖x‖ :=
  (S.le_opNorm x).trans (by gcongr; linarith)

/-- **Exactness of the complex method** (Bergh–Löfström, Theorem 4.1.2). A continuous linear map
`T : X₀ + X₁ → Y₀ + Y₁` restricting to `T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` induces a map
`[X₀, X₁]_θ → [Y₀, Y₁]_θ` (`toSum_map`). If `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖`, its norm is
at most `M₀ ^ (1 - θ) * M₁ ^ θ` (`norm_map_le`). The construction uses the bounds `‖T_j‖ + 1`,
but the map is determined by `T` (`toSum_map` and `ext`). -/
def map : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ :=
  (C.complexKer θ).liftQL ((mk (C := D) θ).comp (scaledStripMapL T hT₀ hT₁
      (by positivity : (0 : ℝ) < ‖T₀‖ + 1) (by positivity : (0 : ℝ) < ‖T₁‖ + 1)
      (norm_apply_le_opNorm_add_one T₀) (norm_apply_le_opNorm_add_one T₁) θ))
    fun g hg => by
      have hg' : C.stripEval θ g = 0 := mem_complexKer_iff.1 hg
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        mk_eq_iff, scaledStripMapL, LinearMap.mkContinuous_apply, stripEval_scaledStripMap, hg',
        map_zero, map_zero]

@[simp]
theorem toSum_map (u : C.ComplexMethodSpace θ) : toSum (map T hT₀ hT₁ u) = T (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  exact stripEval_scaledStripMap T hT₀ hT₁ _ _ g

/-- For any positive bounds `M₀`, `M₁`, the induced map sends the class of `g` to the class of
the weighted boundary pair `scaledStripMap`. -/
private theorem map_mk (g : C.stripSpace) :
    map T hT₀ hT₁ (mk θ g) = mk θ (scaledStripMap T hT₀ hT₁ hM₀ hM₁ θ g) :=
  ext (by rw [toSum_map, toSum_mk, toSum_mk, stripEval_scaledStripMap])

include hM₀ hM₁ h₀ h₁ in
private theorem norm_map_le_of_pos (u : C.ComplexMethodSpace θ) :
    ‖map T hT₀ hT₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ :=
  norm_le_of_forall_mk (by positivity) (fun g => by
    rw [map_mk T hT₀ hT₁ hM₀ hM₁]
    exact (norm_mk_le _).trans (norm_scaledStripMap_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ g)) u

/-- **Exactness of the complex method** (Bergh–Löfström, Theorem 4.1.2): if
`‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖`, the induced map has norm at most
`M₀ ^ (1 - θ) * M₁ ^ θ`. The case `M_j > 0` uses the weight `M₀ ^ (z - 1) * M₁ ^ (-z)`; the
general case follows by letting `M_j + ε` tend to `M_j`. -/
theorem norm_map_le {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.ComplexMethodSpace θ) :
    ‖map T hT₀ hT₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · have hle : ∀ ε > 0, ‖map T hT₀ hT₁ u‖ ≤ (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖ :=
      fun ε hε => norm_map_le_of_pos T hT₀ hT₁ (by positivity) (by positivity)
        (fun x => (h₀ x).trans (by gcongr; linarith))
        (fun x => (h₁ x).trans (by gcongr; linarith)) u
    have hcont : ContinuousAt (fun ε : ℝ => (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖) 0 :=
      (((Real.continuousAt_rpow_const _ _ (Or.inr (sub_nonneg.2 hθ.2))).comp
        (continuous_const.add continuous_id).continuousAt).mul
        ((Real.continuousAt_rpow_const _ _ (Or.inr hθ.1)).comp
          (continuous_const.add continuous_id).continuousAt)).mul continuousAt_const
    have hlim : Tendsto (fun ε : ℝ => (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖) (𝓝[>] 0)
        (𝓝 (M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖)) := by
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)
  · -- Off `[0, 1]` the space is zero: every element is the class of `0`.
    have hu : ‖u‖ = 0 := by
      have hθ' : (θ : ℂ) ∉ verticalClosedStrip 0 1 := by rwa [ofReal_mem_verticalClosedStrip]
      obtain ⟨g, rfl⟩ := mk_surjective u
      have h0 : mk θ (0 : C.stripSpace) = mk θ g := mk_eq_iff.2 <| by
        rw [toSum_mk, stripEval_of_notMem hθ', stripEval_of_notMem hθ']
      exact le_antisymm (h0 ▸ (norm_mk_le 0).trans_eq norm_zero) (norm_nonneg (mk θ g))
    have := norm_map_le_of_pos T hT₀ hT₁ (by positivity : (0 : ℝ) < ‖T₀‖ + 1)
      (by positivity : (0 : ℝ) < ‖T₁‖ + 1) (norm_apply_le_opNorm_add_one T₀)
      (norm_apply_le_opNorm_add_one T₁) u
    rw [hu, mul_zero] at this ⊢
    exact this

end ComplexMethodSpace

end Map

/-! ### The diagonal couple -/

namespace ComplexMethodSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}

/-- The diagonal element `(x, x)` of the intersection of the couple `(X, X)`. -/
private def reflDiag (x : X) : (refl ℂ X).inter :=
  ⟨(x, x), by simp only [mem_inter_iff, refl_embed₀, refl_embed₁]⟩

private theorem coe_reflDiag (x : X) : (reflDiag x : X × X) = (x, x) :=
  rfl

private theorem sumSpaceEmbed_toSum_ofInter_reflDiag (hθ : θ ∈ Icc (0 : ℝ) 1) (x : X) :
    (refl ℂ X).sumSpaceEmbed (toSum (ofInter θ (reflDiag x))) = x := by
  rw [toSum_ofInter hθ, sumSpaceEmbed_fstToSum, refl_embed₀, ContinuousLinearMap.id_apply,
    interFst_apply, coe_reflDiag]

/-- For the couple `(X, X)` and `0 ≤ θ ≤ 1`, the norm of `[X, X]_θ` is the norm of `X`. -/
theorem norm_refl_sumSpaceEmbed_toSum (hθ : θ ∈ Icc (0 : ℝ) 1)
    (u : (refl ℂ X).ComplexMethodSpace θ) : ‖(refl ℂ X).sumSpaceEmbed (toSum u)‖ = ‖u‖ := by
  refine le_antisymm ((norm_refl_sumSpaceEmbed _).trans_le (norm_toSum_le u)) ?_
  have hu : ofInter θ (reflDiag ((refl ℂ X).sumSpaceEmbed (toSum u))) = u :=
    toSum_injective <| (refl ℂ X).sumSpace_ext (sumSpaceEmbed_toSum_ofInter_reflDiag hθ _)
  calc ‖u‖ = ‖ofInter θ (reflDiag ((refl ℂ X).sumSpaceEmbed (toSum u)))‖ := by rw [hu]
    _ ≤ ‖reflDiag ((refl ℂ X).sumSpaceEmbed (toSum u))‖ := norm_ofInter_le _
    _ = ‖(refl ℂ X).sumSpaceEmbed (toSum u)‖ := by
        rw [norm_refl_inter, interFst_apply, coe_reflDiag]

/-- For the couple `(X, X)` and `0 ≤ θ ≤ 1`, the complex interpolation space is `X` with its own
norm: the value at `θ` is a linear isometric equivalence `[X, X]_θ ≃ X`. -/
def reflEquiv (hθ : θ ∈ Icc (0 : ℝ) 1) : (refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] X where
  toLinearEquiv := LinearEquiv.ofBijective
    ((refl ℂ X).sumSpaceEmbed.toLinearMap ∘ₗ toSum.toLinearMap)
    ⟨(refl ℂ X).sumSpaceEmbed_injective.comp toSum_injective,
      fun x => ⟨ofInter θ (reflDiag x), sumSpaceEmbed_toSum_ofInter_reflDiag hθ x⟩⟩
  norm_map' := norm_refl_sumSpaceEmbed_toSum hθ

@[simp]
theorem reflEquiv_apply (hθ : θ ∈ Icc (0 : ℝ) 1) (u : (refl ℂ X).ComplexMethodSpace θ) :
    reflEquiv hθ u = (refl ℂ X).sumSpaceEmbed (toSum u) :=
  (rfl)

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
