/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.Indicator
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Multiplication operators on `Lᵖ`

An essentially bounded scalar function `a : Lp 𝕜 ∞ μ` acts on `Lp E p μ` (`1 ≤ p ≤ ∞`) by
pointwise scalar multiplication. This file bundles that action as
`MeasureTheory.Lp.multiplicationOperator a` and records its algebraic, adjoint, and norm
properties. Because the operator is built directly from heterogeneous `Lp` scalar multiplication
via `LinearMap.mkContinuous`, the definition and algebraic identities require only `[NormedField 𝕜]`
(without `[NontriviallyNormedField 𝕜]`).

Over a nontrivially normed field `𝕜` on a sigma-finite measure space with nontrivial fiber `E`, the
operator norm on `Lp E p μ` equals the `L∞` norm `‖a‖` (`norm_multiplicationOperator`). On
`Lp E 2 μ` for a complete inner-product space `E` over `𝕜` (`[RCLike 𝕜]`), the Hilbert adjoint of
multiplication by `a` is multiplication by `star a` (`adjoint_multiplicationOperator`).

For a measurable set `s`, multiplication by the class `TauCeti.linftyIndicator μ s hs` of its
indicator cuts an `Lᵖ` class off to `s` (`multiplicationOperator_linftyIndicator_ae`). It does not
increase the norm (`norm_multiplicationOperator_linftyIndicator_apply_le`), and the cut-offs to `s`
and to its complement add up to the class (`multiplicationOperator_linftyIndicator_add_compl`).

A function `f` continuous and bounded on a measurable set `s` has a class
`TauCeti.linftyOfContinuousOn μ hf hs hC` in `L∞(μ.restrict s)`, and multiplication by it acts by
`x ↦ f x • g x` (`multiplicationOperator_linftyOfContinuousOn_ae`). For `|f| ≤ 1` on `s` it does
not increase the norm (`norm_multiplicationOperator_linftyOfContinuousOn_apply_le`), and
multiplications by two functions summing to one on `s` add up to the identity
(`multiplicationOperator_linftyOfContinuousOn_add_eq_one`). Multiplication by `a` commutes
with composition by a continuous linear map (`ContinuousLinearMap.compLpL_multiplicationOperator`).
-/

public section

noncomputable section

open scoped ENNReal InnerProductSpace

namespace TauCeti

open MeasureTheory

variable {α F : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [NormedAddCommGroup F] [SecondCountableTopologyEither α F] {f : α → F} {s : Set α}

variable (μ : Measure α) in
/-- The class in `L∞(μ.restrict s)` of a function continuous and bounded on a measurable set `s`. -/
def linftyOfContinuousOn (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hC : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C) : Lp F ∞ (μ.restrict s) :=
  (hf.memLp_top_restrict_of_bound hs _ hC.choose_spec).toLp f

/-- The class `TauCeti.linftyOfContinuousOn μ hf hs hC` is almost everywhere `f` on `s`. -/
theorem coeFn_linftyOfContinuousOn {μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hC : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C) : linftyOfContinuousOn μ hf hs hC =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp _

end TauCeti

namespace MeasureTheory.Lp

open ContinuousLinearMap

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise scalar multiplication by an essentially bounded symbol `a : Lp 𝕜 ∞ μ`, as a
continuous linear operator on `Lp E p μ` (`1 ≤ p ≤ ∞`). -/
def multiplicationOperator (a : Lp 𝕜 ∞ μ) : Lp E p μ →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun f := a • f
      map_add' := Lp.add_smul a
      map_smul' c f := (Lp.smul_comm c a f).symm }
    ‖a‖ (Lp.norm_smul_le a)

/-- Applying the multiplication operator is heterogeneous `Lp` scalar multiplication. -/
theorem multiplicationOperator_apply (a : Lp 𝕜 ∞ μ) (f : Lp E p μ) :
    multiplicationOperator a f = a • f :=
  (rfl)

/-- The multiplication operator acts by pointwise scalar multiplication almost everywhere. -/
theorem multiplicationOperator_ae (a : Lp 𝕜 ∞ μ) (f : Lp E p μ) :
    multiplicationOperator a f =ᵐ[μ] fun x ↦ a x • f x :=
  coeFn_lpSMul a f

/-- Multiplication by `a` changes the `Lᵖ` norm by at most `‖a‖ * ‖f‖`. -/
theorem norm_multiplicationOperator_apply_le (a : Lp 𝕜 ∞ μ) (f : Lp E p μ) :
    ‖multiplicationOperator a f‖ ≤ ‖a‖ * ‖f‖ :=
  Lp.norm_smul_le a f

@[simp]
theorem multiplicationOperator_zero :
    multiplicationOperator (E := E) (p := p) (0 : Lp 𝕜 ∞ μ) = 0 :=
  ContinuousLinearMap.ext fun f ↦ Lp.zero_smul 𝕜 ∞ f

/-- Multiplication operators depend additively on their symbols. -/
@[simp]
theorem multiplicationOperator_add (a b : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (a + b) =
      multiplicationOperator a + multiplicationOperator b :=
  ContinuousLinearMap.ext fun f ↦ Lp.smul_add a b f

/-- Multiplication operators depend linearly on their symbols. -/
@[simp]
theorem multiplicationOperator_smul (c : 𝕜) (a : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (c • a) = c • multiplicationOperator a :=
  ContinuousLinearMap.ext fun f ↦ Lp.smul_assoc c a f

/-- Composing multiplication operators multiplies their symbols in the same order. -/
theorem multiplicationOperator_comp_multiplicationOperator (a b : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) a ∘L multiplicationOperator b =
      multiplicationOperator (a * b) := by
  ext f
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f,
    multiplicationOperator_ae (a * b) f,
    coeFn_mul a b] with x ha hb hab hsmul
  simp only [comp_apply, ha, hb, hab, hsmul, Pi.mul_apply, smul_smul]

/-- Multiplication operators commute with each other. -/
theorem commute_multiplicationOperator (a b : Lp 𝕜 ∞ μ) :
    Commute (multiplicationOperator (E := E) (p := p) a) (multiplicationOperator b) := by
  refine (commute_iff_eq _ _).2 (ContinuousLinearMap.ext fun f ↦ Lp.ext ?_)
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f, multiplicationOperator_ae b (multiplicationOperator a f),
    multiplicationOperator_ae a f] with x hab hb hba ha
  simp only [mul_apply_eq_comp, hab, hb, hba, ha, smul_smul, mul_comm]

/-- Multiplication by a symbol of norm one almost everywhere preserves the `Lᵖ` norm. -/
theorem norm_multiplicationOperator_apply_of_ae_norm_eq_one {u : Lp 𝕜 ∞ μ}
    (hu : ∀ᵐ x ∂μ, ‖u x‖ = 1) (f : Lp E p μ) :
    ‖multiplicationOperator u f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂μ, ‖multiplicationOperator u f x‖ = ‖f x‖ := by
    filter_upwards [multiplicationOperator_ae u f, hu] with x hx hux
    rw [hx, norm_smul, hux, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.ge))

/-- A symbol equal almost everywhere to a constant acts by scalar multiplication. -/
theorem multiplicationOperator_of_ae_eq_const {a : Lp 𝕜 ∞ μ} {c : 𝕜}
    (ha : a =ᵐ[μ] fun _ ↦ c) :
    multiplicationOperator (E := E) (p := p) a = c • ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext f
  filter_upwards [multiplicationOperator_ae a f, Lp.coeFn_smul c f, ha] with x h hf ha'
  simp [h, hf, ha']

/-- The scalar embedding into `L∞` acts on `Lᵖ` by scalar multiplication. -/
@[simp]
theorem multiplicationOperator_algebraMap (c : 𝕜) :
    multiplicationOperator (E := E) (p := p) (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) =
      c • ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  apply multiplicationOperator_of_ae_eq_const
  simpa only [Algebra.algebraMap_self_apply] using coeFn_algebraMap (R := 𝕜) (μ := μ) c

@[simp]
theorem multiplicationOperator_const [IsFiniteMeasure μ] (c : 𝕜) :
    multiplicationOperator (E := E) (p := p) (Lp.const ∞ μ c) =
      c • ContinuousLinearMap.id 𝕜 (Lp E p μ) :=
  multiplicationOperator_of_ae_eq_const (Lp.coeFn_const (μ := μ) ∞ c)

end NormedSpace

section Indicator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {s : Set α}

/-- Multiplication by the `L∞` class `TauCeti.linftyIndicator μ s hs` cuts an `Lᵖ` class off to
`s`. -/
theorem multiplicationOperator_linftyIndicator_ae (hs : MeasurableSet s) (f : Lp E p μ) :
    multiplicationOperator (TauCeti.linftyIndicator μ s hs) f =ᵐ[μ] s.indicator f := by
  filter_upwards [multiplicationOperator_ae (TauCeti.linftyIndicator μ s hs) f,
    TauCeti.coeFn_linftyIndicator (μ := μ) hs] with x hx h₁
  rw [hx, h₁]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Cutting an `Lᵖ` class off to a measurable set does not increase its norm. -/
theorem norm_multiplicationOperator_linftyIndicator_apply_le (hs : MeasurableSet s)
    (f : Lp E p μ) : ‖multiplicationOperator (TauCeti.linftyIndicator μ s hs) f‖ ≤ ‖f‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [multiplicationOperator_linftyIndicator_ae hs f] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self f x

/-- The cut-offs of an `Lᵖ` class to a measurable set and to its complement add up to the class. -/
theorem multiplicationOperator_linftyIndicator_add_compl (hs : MeasurableSet s) (f : Lp E p μ) :
    multiplicationOperator (TauCeti.linftyIndicator μ s hs) f +
      multiplicationOperator (TauCeti.linftyIndicator μ sᶜ hs.compl) f = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (multiplicationOperator (TauCeti.linftyIndicator μ s hs) f)
      (multiplicationOperator (TauCeti.linftyIndicator μ sᶜ hs.compl) f),
    multiplicationOperator_linftyIndicator_ae hs f,
    multiplicationOperator_linftyIndicator_ae hs.compl f] with x hx h₁ h₂
  rw [hx, Pi.add_apply, h₁, h₂, Set.indicator_self_add_compl_apply]

end Indicator

section ContinuousOn

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure X}
  {f : X → ℝ} {s : Set X}

/-- Multiplication by the class `TauCeti.linftyOfContinuousOn μ hf hs hC` of `f` acts by
`x ↦ f x • g x`. -/
theorem multiplicationOperator_linftyOfContinuousOn_ae (hf : ContinuousOn f s)
    (hs : MeasurableSet s) (hC : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C) (g : Lp E p (μ.restrict s)) :
    multiplicationOperator (TauCeti.linftyOfContinuousOn μ hf hs hC) g
      =ᵐ[μ.restrict s] fun x ↦ f x • g x := by
  filter_upwards [multiplicationOperator_ae (TauCeti.linftyOfContinuousOn μ hf hs hC) g,
    TauCeti.coeFn_linftyOfContinuousOn (μ := μ) hf hs hC] with x hx h₁
  rw [hx, h₁]

/-- Multiplication by the class of a function bounded by one on `s` does not increase the norm. -/
theorem norm_multiplicationOperator_linftyOfContinuousOn_apply_le (hf : ContinuousOn f s)
    (hs : MeasurableSet s) (hC : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C) (h₁ : ∀ x ∈ s, ‖f x‖ ≤ 1)
    (g : Lp E p (μ.restrict s)) :
    ‖multiplicationOperator (TauCeti.linftyOfContinuousOn μ hf hs hC) g‖ ≤ ‖g‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [multiplicationOperator_linftyOfContinuousOn_ae hf hs hC g, ae_restrict_mem hs]
    with x hx hxs
  rw [hx, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (h₁ x hxs)

/-- Multiplications by the classes of two functions summing to one on `s` add up to the
identity. -/
theorem multiplicationOperator_linftyOfContinuousOn_add_eq_one {g : X → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hs : MeasurableSet s)
    (hCf : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C) (hCg : ∃ C, ∀ x ∈ s, ‖g x‖ ≤ C)
    (h : ∀ x ∈ s, f x + g x = 1) :
    multiplicationOperator (E := E) (p := p) (TauCeti.linftyOfContinuousOn μ hf hs hCf) +
      multiplicationOperator (TauCeti.linftyOfContinuousOn μ hg hs hCg) = 1 := by
  ext u : 1
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (multiplicationOperator (TauCeti.linftyOfContinuousOn μ hf hs hCf) u)
      (multiplicationOperator (TauCeti.linftyOfContinuousOn μ hg hs hCg) u),
    multiplicationOperator_linftyOfContinuousOn_ae hf hs hCf u,
    multiplicationOperator_linftyOfContinuousOn_ae hg hs hCg u, ae_restrict_mem hs]
    with x hx h₁ h₂ hxs
  rw [add_apply, hx, Pi.add_apply, h₁, h₂, ← add_smul, h x hxs, one_smul,
    one_apply_eq_self]

end ContinuousOn

section CompLpL

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Composition with a continuous linear map commutes with multiplication by an `L∞` class. -/
theorem _root_.ContinuousLinearMap.compLpL_multiplicationOperator (L : E →L[𝕜] F)
    (a : Lp 𝕜 ∞ μ) (g : Lp E p μ) :
    L.compLpL p μ (multiplicationOperator a g) = multiplicationOperator a (L.compLpL p μ g) := by
  refine Lp.ext ?_
  filter_upwards [L.coeFn_compLpL (multiplicationOperator a g), multiplicationOperator_ae a g,
    multiplicationOperator_ae a (L.compLpL p μ g), L.coeFn_compLpL g] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

end CompLpL

section InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- On `L²`, the adjoint of multiplication by `a` is multiplication by `star a`. -/
@[simp]
theorem adjoint_multiplicationOperator (a : Lp 𝕜 ∞ μ) :
    ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := Lp E 2 μ) (F := Lp E 2 μ)
      (multiplicationOperator (E := E) (p := 2) a) =
      multiplicationOperator (E := E) (p := 2) (star a) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [multiplicationOperator_ae (star a) f,
    multiplicationOperator_ae a g, Lp.coeFn_star a] with x hf hg ha
  simp [hf, hg, ha, inner_smul_left, inner_smul_right]

end InnerProductSpace

section ExactNorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Over a nontrivially normed field, the operator norm of multiplication by `a` on `Lᵖ` is at
most its `L∞` norm. -/
theorem norm_multiplicationOperator_le (a : Lp 𝕜 ∞ μ) :
    ‖multiplicationOperator (E := E) (p := p) a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

/-- If `0 < c` and `c ≤ ‖a‖` almost everywhere on `s`, then multiplication by `a` scales the `Lᵖ`
norm of a constant indicator of `s` by at least `c`. -/
private theorem mul_norm_indicatorConstLp_le {a : Lp 𝕜 ∞ μ} {c : ℝ} (hc_pos : 0 < c)
    {s : Set α} (hs : MeasurableSet s) (hs_top : μ s ≠ ∞) (ha : ∀ᵐ x ∂μ, x ∈ s → c ≤ ‖a x‖)
    (v : E) :
    c * ‖indicatorConstLp p hs hs_top v‖ ≤
      ‖multiplicationOperator a (indicatorConstLp p hs hs_top v)‖ := by
  set f := indicatorConstLp p hs hs_top v
  refine (le_inv_mul_iff₀ hc_pos).1 (Lp.norm_le_mul_norm_of_ae_le_mul ?_)
  filter_upwards [multiplicationOperator_ae a f,
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hs_top) (c := v), ha] with x hmul hf hax
  rw [hmul, hf]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, norm_smul]
    exact (le_inv_mul_iff₀ hc_pos).2 (mul_le_mul_of_nonneg_right (hax hx) (norm_nonneg v))
  · simp [Set.indicator_of_notMem hx]

/-- On a sigma-finite measure space over a nontrivially normed field, the operator norm of
multiplication by `a` on `Lp E p μ` (`1 ≤ p ≤ ∞`) with values in a nontrivial space `E` is
exactly the `L∞` norm of `a`. -/
@[simp]
theorem norm_multiplicationOperator [SigmaFinite μ] [Nontrivial E] (a : Lp 𝕜 ∞ μ) :
    ‖multiplicationOperator (E := E) (p := p) a‖ = ‖a‖ := by
  apply le_antisymm (norm_multiplicationOperator_le a)
  by_contra hle
  set c := (‖multiplicationOperator (E := E) (p := p) a‖ + ‖a‖) / 2 with hc_def
  have hop_lt_c : ‖multiplicationOperator (E := E) (p := p) a‖ < c := by linarith [hc_def]
  have hc_pos : 0 < c := (norm_nonneg _).trans_lt hop_lt_c
  have hc_lt : c < ‖a‖ := by linarith [hc_def]
  have ha_meas := Lp.aestronglyMeasurable a
  set s := {x | c < ‖ha_meas.mk a x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const ha_meas.stronglyMeasurable_mk.norm.measurable
  have hs_ae : s =ᵐ[μ] {x | c < ‖a x‖} :=
    Filter.eventuallyEqSet_iff.2 (ha_meas.ae_eq_mk.symm.mono fun x hx ↦ by dsimp [s]; rw [hx])
  have hμs : μ s ≠ 0 := by
    rw [measure_congr hs_ae]
    exact measure_lt_norm_ne_zero hc_pos.le hc_lt
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set f := indicatorConstLp p ht hμt_top.ne v
  have hf_pos : 0 < ‖f‖ :=
    norm_pos_iff.2 fun hf0 ↦ (TauCeti.indicatorConstLp_eq_zero_iff.1 hf0).elim hμt_pos.ne' hv
  have hcancel : c * ‖f‖ ≤ ‖multiplicationOperator (E := E) (p := p) a‖ * ‖f‖ :=
    (mul_norm_indicatorConstLp_le hc_pos ht hμt_top.ne
      (ha_meas.ae_eq_mk.mono fun _ hmk hx ↦ by rw [hmk]; exact le_of_lt (hts hx)) v).trans
      (le_opNorm _ _)
  exact (not_le_of_gt hop_lt_c) (le_of_mul_le_mul_right hcancel hf_pos)

end ExactNorm

end MeasureTheory.Lp
