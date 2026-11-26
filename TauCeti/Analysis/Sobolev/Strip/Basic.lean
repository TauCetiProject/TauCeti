/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Jet
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Function.Lp.AeMem
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.EndpointEstimates
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The Sobolev space `W^{1,2}` on the strip with boundary conditions

Holomorphic strips `u : ℝ × [0, 1] → M` with boundary on two Lagrangians `L₀` and `L₁` are the
solutions counted by Lagrangian Floer homology. Their linearized operators `∂s + J ∂t + S` act on
sections `ξ` of a trivial bundle with fibre `V` over the strip `ℝ × [0, 1]` whose boundary values
lie in two subspaces `F₀` and `F₁` of `V`, the tangent spaces of the Lagrangians along the
boundary, in a trivialization along the strip. This file sets up the Sobolev space
`W^{1,2}_F(ℝ × [0, 1], V)` of such sections, with the same conventions as the Sobolev space of the
cylinder in `TauCeti.Analysis.Sobolev.Cylinder`, sharing its jets, strip measure and translation
of `Lᵖ` of the strip from `TauCeti.Analysis.Sobolev.Strip.Jet`.

* **Test sections** (`TauCeti.StripSobolev.testSection F₀ F₁`) are the `C²` maps
  `ξ : ℝ × ℝ → V` that vanish for `|s|` large, with `ξ (s, 0) ∈ F₀` and `ξ (s, 1) ∈ F₁` for every
  `s`. With `F₀ = F₁ = ⊤` there is no boundary condition, and enlarging `F₀` or `F₁` enlarges the
  space (`TauCeti.StripSobolev.H1_mono`).
* `TauCeti.StripSobolev.H1 F₀ F₁` is the closure in `L²(ℝ × [0, 1], V × V × V)` of the jets
  `(ξ, ∂s ξ, ∂t ξ)` of test sections, the completion of the test sections in the `W^{1,2}` norm.
  It is a closed subspace, hence complete, and its elements have a value, an `s`-derivative and a
  `t`-derivative in `L²` (`TauCeti.StripSobolev.valueL`, `TauCeti.StripSobolev.derivSL`,
  `TauCeti.StripSobolev.derivTL`), none of which depend on the boundary conditions it is
  considered with (`TauCeti.StripSobolev.valueL_inclusion`). An element is determined by its value
  (`TauCeti.StripSobolev.valueL_injective`): integrating by parts against test functions
  supported in the open strip `ℝ × (0, 1)` shows that the derivatives are the weak derivatives of
  the value (`TauCeti.StripSobolev.hasWeakLineDerivOn_derivSL`,
  `TauCeti.StripSobolev.hasWeakLineDerivOn_derivTL`), which vanish where the value does
  (`TauCeti.HasWeakLineDerivOn.ae_eq_zero_of_isOpen`).
* **Translation invariance.** Translating sections in the `s` direction is a linear isometric
  equivalence of `H1 F₀ F₁` (`TauCeti.StripSobolev.translate`): the norm is translation
  invariant, as the analysis of strips with long necks requires, unlike a norm built from a
  fixed compact chart.
* **Boundary traces.** The restriction of a test section to the two boundary lines
  `ℝ × {0}` and `ℝ × {1}` satisfies `‖ξ(·, 0)‖² + ‖ξ(·, 1)‖² ≤ 4 ‖ξ‖²_{W^{1,2}}`, from the
  one-dimensional trace estimate on each segment `{s} × [0, 1]`
  (`TauCeti.norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq`). It therefore extends to
  a bounded trace map `TauCeti.StripSobolev.traceL : H1 F₀ F₁ → L²(ℝ, V) × L²(ℝ, V)`, and when
  `F₀` and `F₁` are closed the traces of every element of `H1 F₀ F₁` take values in `F₀` and `F₁`
  almost everywhere (`TauCeti.StripSobolev.ae_traceL_fst_mem`,
  `TauCeti.StripSobolev.ae_traceL_snd_mem`). This is the sense in which elements of `H1 F₀ F₁`
  satisfy the boundary conditions. The trace does not depend on the boundary conditions an
  element is considered with (`TauCeti.StripSobolev.traceL_inclusion`), so the boundary
  conditions are faithful: for closed `F₀` and `F₁`, the jet of a `C²` section vanishing for `|s|`
  large lies in `H1 F₀ F₁` exactly when its boundary values lie in `F₀` and `F₁`
  (`TauCeti.StripSobolev.jetLp_mem_H1_iff`).
* **Green's formulas.** For `x`, `y ∈ H1 F₀ F₁`,
  `⟪∂t x, y⟫ + ⟪x, ∂t y⟫ = ⟪x(·, 1), y(·, 1)⟫ - ⟪x(·, 0), y(·, 0)⟫` in `L²`, the boundary values
  being the traces (`TauCeti.StripSobolev.inner_derivTL_add_inner_derivTL`), while
  `⟪∂s x, y⟫ + ⟪x, ∂s y⟫ = 0` (`TauCeti.StripSobolev.inner_derivSL_add_inner_derivSL`). They are
  the integrations by parts from which the formal adjoint of `∂s + J ∂t + S` and its boundary
  terms are computed.

The Rellich compactness of the restriction to `[-T, T] × [0, 1]` is
`TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL` in
`TauCeti.Analysis.Sobolev.Strip.Rellich`, and Peetre's argument for first-order operators on the
strip with boundary conditions is in `TauCeti.Analysis.Sobolev.Strip.Fredholm`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces and the trace theorem, and §3.1, on the linearized operator with totally real
  boundary conditions.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

/-- An almost everywhere statement about the first coordinate `s` holds almost everywhere on the
strip. -/
theorem ae_stripMeasure_of_ae_fst {p : ℝ → Prop} (h : ∀ᵐ s, p s) :
    ∀ᵐ z ∂stripMeasure, p z.1 := by
  rw [stripMeasure_eq_prod]
  exact ae_of_ae_fst h

/-- Almost every slice `t ↦ f (s, t)` of a square integrable section on the strip is integrable
on `[0, 1]`. -/
theorem ae_integrable_slice {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : MemLp f 2 stripMeasure) :
    ∀ᵐ s, Integrable (fun t ↦ f (s, t)) (volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [stripMeasure_eq_prod] at hf
  filter_upwards [((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).prod_right_ae,
    hf.aestronglyMeasurable.prodMk_left] with s hs hm
  exact ((memLp_two_iff_integrable_sq_norm hm).2 hs).integrable one_le_two

/-- Almost every slice `t ↦ f (s, t)` of a square integrable section on the strip is interval
integrable on `[0, 1]`. -/
theorem ae_intervalIntegrable_slice {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : MemLp f 2 stripMeasure) :
    ∀ᵐ s, IntervalIntegrable (fun t ↦ f (s, t)) volume 0 1 := by
  filter_upwards [ae_integrable_slice hf] with s hs
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 hs

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Test sections and the space `H1` -/

/-- The test sections of the trivial bundle with fibre `V` over the strip `ℝ × [0, 1]` with
boundary values in `F₀` and `F₁`: the `C²` maps `ξ : ℝ × ℝ → V` that vanish for `|s|` large, with
`ξ (s, 0) ∈ F₀` and `ξ (s, 1) ∈ F₁` for every `s`. -/
def testSection (F₀ F₁ : Submodule ℝ V) : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ (∀ s, ξ (s, 0) ∈ F₀) ∧ (∀ s, ξ (s, 1) ∈ F₁) ∧
    ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0}
  zero_mem' := ⟨contDiff_const, fun _ ↦ F₀.zero_mem, fun _ ↦ F₁.zero_mem, 0, fun _ _ _ ↦ rfl⟩
  add_mem' := by
    rintro ξ η ⟨hξ, hξ₀, hξ₁, R, hR⟩ ⟨hη, hη₀, hη₁, R', hR'⟩
    refine ⟨hξ.add hη, fun s ↦ F₀.add_mem (hξ₀ s) (hη₀ s), fun s ↦ F₁.add_mem (hξ₁ s) (hη₁ s),
      max R R', fun s t hs ↦ ?_⟩
    simp [hR s t ((le_max_left _ _).trans hs), hR' s t ((le_max_right _ _).trans hs)]
  smul_mem' := by
    rintro c ξ ⟨hξ, hξ₀, hξ₁, R, hR⟩
    exact ⟨contDiff_const.smul hξ, fun s ↦ F₀.smul_mem c (hξ₀ s), fun s ↦ F₁.smul_mem c (hξ₁ s),
      R, fun s t hs ↦ by simp [hR s t hs]⟩

variable {F₀ F₁ F₀' F₁' : Submodule ℝ V} {ξ : ℝ × ℝ → V}

/-- Membership in the test sections. -/
theorem mem_testSection_iff : ξ ∈ testSection F₀ F₁ ↔ ContDiff ℝ 2 ξ ∧ (∀ s, ξ (s, 0) ∈ F₀) ∧
    (∀ s, ξ (s, 1) ∈ F₁) ∧ ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0 :=
  Iff.rfl

/-- Weakening the boundary conditions enlarges the test sections. -/
theorem testSection_mono (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') :
    testSection F₀ F₁ ≤ testSection F₀' F₁' := fun _ ⟨hξ, hξ₀, hξ₁, hR⟩ ↦
  ⟨hξ, fun s ↦ h₀ (hξ₀ s), fun s ↦ h₁ (hξ₁ s), hR⟩

/-- A test section is `C¹`. -/
theorem contDiff_one_of_mem_testSection (hξ : ξ ∈ testSection F₀ F₁) : ContDiff ℝ 1 ξ :=
  (mem_testSection_iff.1 hξ).1.of_le (by norm_num)

/-- The jet of a test section is square integrable on the strip. -/
theorem memLp_jet (hξ : ξ ∈ testSection F₀ F₁) : MemLp (jet ξ) 2 stripMeasure := by
  obtain ⟨-, -, -, R, hR⟩ := mem_testSection_iff.1 hξ
  exact memLp_jet_of_contDiff (contDiff_one_of_mem_testSection hξ) hR

/-- The test sections are differentiable with square integrable jets. -/
instance : HasL2Jets (testSection F₀ F₁) :=
  ⟨fun _ hξ ↦ (contDiff_one_of_mem_testSection hξ).differentiable one_ne_zero, fun _ ↦ memLp_jet⟩

/-- The jet of a test section does not depend on the boundary conditions it is considered
with. -/
theorem jetLp_inclusion (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (ξ : testSection F₀ F₁) :
    jetLp (testSection F₀' F₁') (Submodule.inclusion (testSection_mono h₀ h₁) ξ) =
      jetLp (testSection F₀ F₁) ξ := by
  rw [jetLp_apply, jetLp_apply]
  rfl

variable (F₀ F₁) in
/-- The Sobolev space `W^{1,2}_F(ℝ × [0, 1], V)` of sections with boundary values in `F₀` and
`F₁`: the closure in `L²(ℝ × [0, 1], V × V × V)` of the jets of test sections, that is, the
completion of the test sections in the `W^{1,2}` norm. An element is an `L²` jet
`(ξ, ξ_s, ξ_t)`. It is the closure `TauCeti.StripSobolev.jetClosure` of the jets of the test
sections, the construction shared with the cylinder. -/
abbrev H1 : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  jetClosure (testSection F₀ F₁)

variable (F₀ F₁) in
/-- The jet of a test section, as an element of `H1`. -/
def jetH1 : testSection F₀ F₁ →ₗ[ℝ] H1 F₀ F₁ :=
  (jetLp (testSection F₀ F₁)).codRestrict (H1 F₀ F₁) jetLp_mem_jetClosure

@[simp]
theorem coe_jetH1 (ξ : testSection F₀ F₁) : (jetH1 F₀ F₁ ξ : Lp (V × V × V) 2 stripMeasure) =
    jetLp (testSection F₀ F₁) ξ :=
  (rfl)

/-- The jets of test sections are dense in `H1`. -/
theorem denseRange_jetH1 : DenseRange (jetH1 F₀ F₁) :=
  denseRange_codRestrict_jetLp _

/-- A closed subset of `H1` containing the jets of all test sections is everything. -/
theorem H1_induction {P : H1 F₀ F₁ → Prop} (hP : IsClosed {x | P x})
    (h : ∀ ξ : testSection F₀ F₁, P (jetH1 F₀ F₁ ξ)) (x : H1 F₀ F₁) : P x :=
  denseRange_jetH1.induction_on x hP h

/-- A closed relation on `H1` holding for the jets of all pairs of test sections holds for all
pairs. -/
theorem H1_induction₂ {P : H1 F₀ F₁ → H1 F₀ F₁ → Prop}
    (hP : IsClosed {p : H1 F₀ F₁ × H1 F₀ F₁ | P p.1 p.2})
    (h : ∀ ξ η : testSection F₀ F₁, P (jetH1 F₀ F₁ ξ) (jetH1 F₀ F₁ η)) (x y : H1 F₀ F₁) :
    P x y :=
  denseRange_jetH1.induction_on₂ hP h x y

/-- Weakening the boundary conditions enlarges `H1`. -/
theorem H1_mono (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') : H1 F₀ F₁ ≤ H1 F₀' F₁' := by
  rw [H1, H1, jetClosure_def, jetClosure_def]
  refine Submodule.topologicalClosure_mono ?_
  rintro _ ⟨ξ, rfl⟩
  exact ⟨Submodule.inclusion (testSection_mono h₀ h₁) ξ, jetLp_inclusion h₀ h₁ ξ⟩

/-- The jet in `H1` of a test section does not depend on the boundary conditions it is
considered with. -/
@[simp]
theorem inclusion_jetH1 (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (ξ : testSection F₀ F₁) :
    Submodule.inclusion (H1_mono h₀ h₁) (jetH1 F₀ F₁ ξ) =
      jetH1 F₀' F₁' (Submodule.inclusion (testSection_mono h₀ h₁) ξ) := by
  ext1
  rw [Submodule.coe_inclusion, coe_jetH1, coe_jetH1, jetLp_inclusion h₀ h₁]

/-! ### The components of an element of `H1` -/

variable (F₀ F₁) in
/-- The value `(ξ, ξ_s, ξ_t) ↦ ξ` of an element of `H1`, in `L²(ℝ × [0, 1], V)`. -/
def valueL : H1 F₀ F₁ →L[ℝ] Lp V 2 stripMeasure :=
  ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure).comp (H1 F₀ F₁).subtypeL

variable (F₀ F₁) in
/-- The `s`-derivative `(ξ, ξ_s, ξ_t) ↦ ξ_s` of an element of `H1`, in `L²(ℝ × [0, 1], V)`. -/
def derivSL : H1 F₀ F₁ →L[ℝ] Lp V 2 stripMeasure :=
  (((ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))).compLpL 2
    stripMeasure).comp (H1 F₀ F₁).subtypeL

variable (F₀ F₁) in
/-- The `t`-derivative `(ξ, ξ_s, ξ_t) ↦ ξ_t` of an element of `H1`, in `L²(ℝ × [0, 1], V)`. -/
def derivTL : H1 F₀ F₁ →L[ℝ] Lp V 2 stripMeasure :=
  (((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))).compLpL 2
    stripMeasure).comp (H1 F₀ F₁).subtypeL

/-- The value of an element of `H1` is represented by the first component of its jet. -/
theorem coeFn_valueL (x : H1 F₀ F₁) :
    valueL F₀ F₁ x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).1 :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- The `s`-derivative of an element of `H1` is represented by the second component of its
jet. -/
theorem coeFn_derivSL (x : H1 F₀ F₁) :
    derivSL F₀ F₁ x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).2.1 :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- The `t`-derivative of an element of `H1` is represented by the third component of its
jet. -/
theorem coeFn_derivTL (x : H1 F₀ F₁) :
    derivTL F₀ F₁ x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).2.2 :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- The value of an element of `H1` does not depend on the boundary conditions it is considered
with. -/
@[simp]
theorem valueL_inclusion (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (x : H1 F₀ F₁) :
    valueL F₀' F₁' (Submodule.inclusion (H1_mono h₀ h₁) x) = valueL F₀ F₁ x :=
  (rfl)

/-- The `s`-derivative of an element of `H1` does not depend on the boundary conditions it is
considered with. -/
@[simp]
theorem derivSL_inclusion (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (x : H1 F₀ F₁) :
    derivSL F₀' F₁' (Submodule.inclusion (H1_mono h₀ h₁) x) = derivSL F₀ F₁ x :=
  (rfl)

/-- The `t`-derivative of an element of `H1` does not depend on the boundary conditions it is
considered with. -/
@[simp]
theorem derivTL_inclusion (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (x : H1 F₀ F₁) :
    derivTL F₀' F₁' (Submodule.inclusion (H1_mono h₀ h₁) x) = derivTL F₀ F₁ x :=
  (rfl)

/-- The value of the jet of a test section is the section. -/
theorem valueL_jetH1 (ξ : testSection F₀ F₁) :
    valueL F₀ F₁ (jetH1 F₀ F₁ ξ) =ᵐ[stripMeasure] (ξ : ℝ × ℝ → V) := by
  filter_upwards [coeFn_valueL (jetH1 F₀ F₁ ξ), coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, coe_jetH1, h₂, jet_apply]

/-- The `s`-derivative of the jet of a test section is `∂s ξ`. -/
theorem derivSL_jetH1 (ξ : testSection F₀ F₁) :
    derivSL F₀ F₁ (jetH1 F₀ F₁ ξ) =ᵐ[stripMeasure]
      fun z ↦ fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0) := by
  filter_upwards [coeFn_derivSL (jetH1 F₀ F₁ ξ), coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, coe_jetH1, h₂, jet_apply]

/-- The `t`-derivative of the jet of a test section is `∂t ξ`. -/
theorem derivTL_jetH1 (ξ : testSection F₀ F₁) :
    derivTL F₀ F₁ (jetH1 F₀ F₁ ξ) =ᵐ[stripMeasure]
      fun z ↦ fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1) := by
  filter_upwards [coeFn_derivTL (jetH1 F₀ F₁ ξ), coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, coe_jetH1, h₂, jet_apply]

/-! ### Elements of `H1` are determined by their values -/

section Value

/-- The open strip `ℝ × (0, 1)`, of full measure in the closed strip. -/
theorem ae_mem_openStrip : ∀ᵐ z ∂stripMeasure, z ∈ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 := by
  rw [ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)]
  have h : (volume : Measure (ℝ × ℝ)) ((univ : Set ℝ) ×ˢ ({0, 1} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp [(Set.toFinite ({0, 1} : Set ℝ)).measure_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with z hz hzS
  refine ⟨mem_univ _, lt_of_le_of_ne hzS.2.1 fun h0 ↦ hz ⟨mem_univ _, ?_⟩,
    lt_of_le_of_ne hzS.2.2 fun h1 ↦ hz ⟨mem_univ _, ?_⟩⟩
  · simp [← h0]
  · simp [h1]

/-- Integration by parts against a test function supported in the open strip: the integral of
`φ ∂ ξ + (∂ φ) ξ` vanishes, in each of the two coordinate directions `e`. -/
private theorem integral_smul_fderiv_add_eq_zero {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφU : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1)
    {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSection F₀ F₁) {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1)) :
    ∫ z, (φ z • fderiv ℝ ξ z e + fderiv ℝ φ z e • ξ z) ∂stripMeasure = 0 := by
  obtain ⟨hξ1, -, -, R, hR⟩ := mem_testSection_iff.1 hξ
  set F : ℝ × ℝ → V := fun z ↦ φ z • fderiv ℝ ξ z e + fderiv ℝ φ z e • ξ z
  have hξd := hξ1.differentiable (by norm_num)
  have hφd := hφ.differentiable one_ne_zero
  have hFc : Continuous F :=
    ((hφ.continuous.smul ((hξ1.continuous_fderiv (by norm_num)).clm_apply continuous_const)).add
      (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul hξ1.continuous))
  have hΦ : ∀ z, HasFDerivAt (fun w ↦ φ w • ξ w)
      (φ z • fderiv ℝ ξ z + (fderiv ℝ φ z).smulRight (ξ z)) z := fun z ↦
    (hφd z).hasFDerivAt.smul (hξd z).hasFDerivAt
  have hF : ∀ z, jet ξ z = 0 → F z = 0 := fun z h ↦ by
    simp only [jet_apply, Prod.mk_eq_zero] at h
    have hd : fderiv ℝ ξ z e = 0 := by
      rcases he with rfl | rfl
      exacts [h.2.1, h.2.2]
    simp [F, hd, h.1]
  rw [integral_strip_eq_setIntegral_of_jet_eq_zero hR hF]
  rcases he with rfl | rfl
  · refine setIntegral_rect_eq_zero_of_hasDerivAt_fst (Φ := fun w ↦ φ w • ξ w) hFc
      (fun s t ↦ ?_) fun t ↦ ?_
    · have := (hΦ (s, t)).comp_hasDerivAt (f := fun x : ℝ ↦ (x, t)) s
        (HasDerivAt.prodMk (hasDerivAt_id' s) (hasDerivAt_const s t))
      simpa [F, Function.comp_def] using this
    · simp [hR R t (le_abs_self R), hR (-R) t (by rw [abs_neg]; exact le_abs_self R)]
  · refine setIntegral_rect_eq_zero_of_hasDerivAt_snd (Φ := fun w ↦ φ w • ξ w) hFc
      (fun s t ↦ ?_) fun s ↦ ?_
    · have := (hΦ (s, t)).comp_hasDerivAt (f := fun x : ℝ ↦ (s, x)) t
        (HasDerivAt.prodMk (hasDerivAt_const t s) (hasDerivAt_id' t))
      simpa [F, Function.comp_def] using this
    · have h₀ : φ (s, 0) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hφU h).2.1.false
      have h₁ : φ (s, 1) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hφU h).2.2.false
      simp [h₀, h₁]

variable [CompleteSpace V]

/-- The weak derivative identity on `H1`: for an `L²` jet `x ∈ H1`, a test function `φ` supported
in the open strip and a coordinate direction `e`, with `P` the component of the jet recording the
derivative in the direction `e`, `∫ φ P(x) + ∫ (∂_e φ) x₁ = 0`. -/
private theorem integral_smul_add_eq_zero_of_mem_H1 {x : Lp (V × V × V) 2 stripMeasure}
    (hx : x ∈ H1 F₀ F₁) {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) {e : ℝ × ℝ}
    (he : e = (1, 0) ∨ e = (0, 1)) {P : V × V × V →L[ℝ] V}
    (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) :
    ∫ z, φ z • P (x z) ∂stripMeasure + ∫ z, fderiv ℝ φ z e • (x z).1 ∂stripMeasure = 0 := by
  have hφ₂ : MemLp φ 2 stripMeasure := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hφe : MemLp (fun z ↦ fderiv ℝ φ z e) 2 stripMeasure :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφs.fderiv_apply (𝕜 := ℝ) e)
  set B : ℝ →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.lsmul ℝ ℝ
  set Λ : Lp (V × V × V) 2 stripMeasure →L[ℝ] V :=
    (B.lpPairing stripMeasure 2 2 (hφ₂.toLp φ)).comp (P.compLpL 2 stripMeasure) +
      (B.lpPairing stripMeasure 2 2 (hφe.toLp _)).comp
        ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure)
  have hΛ : ∀ f : Lp (V × V × V) 2 stripMeasure, Λ f =
      ∫ z, φ z • P (f z) ∂stripMeasure + ∫ z, fderiv ℝ φ z e • (f z).1 ∂stripMeasure := by
    intro f
    simp only [Λ, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.lpPairing_eq_integral]
    congr 1 <;> refine integral_congr_ae ?_
    · filter_upwards [hφ₂.coeFn_toLp, P.coeFn_compLp f] with z h₁ h₂
      simp [B, h₁, h₂]
    · filter_upwards [hφe.coeFn_toLp,
        (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLp f] with z h₁ h₂
      simp [B, h₁, h₂]
  -- `Λ` vanishes on the jets of test sections, hence on their closure `H1`.
  have hrange : Set.range (jetLp (testSection F₀ F₁)) ⊆ {f | Λ f = 0} := by
    rintro _ ⟨ξ, rfl⟩
    rw [mem_ofPred_eq, hΛ]
    have hξ := coeFn_jetLp ξ
    have hξ2 := (mem_testSection_iff.1 ξ.property).1
    have hint₁ : Integrable (fun z ↦ φ z • fderiv ℝ (ξ : ℝ × ℝ → V) z e) stripMeasure :=
      (hφ.continuous.smul ((hξ2.continuous_fderiv (by norm_num)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hφs.smul_right)
    have hint₂ : Integrable (fun z ↦ fderiv ℝ φ z e • (ξ : ℝ × ℝ → V) z) stripMeasure :=
      (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul
        hξ2.continuous).integrable_of_hasCompactSupport ((hφs.fderiv_apply (𝕜 := ℝ) e).smul_right)
    have e₁ : ∫ z, φ z • P (jetLp (testSection F₀ F₁) ξ z) ∂stripMeasure =
        ∫ z, φ z • fderiv ℝ (ξ : ℝ × ℝ → V) z e ∂stripMeasure :=
      integral_congr_ae (hξ.mono fun z hz ↦ by simp only [hz, hP])
    have e₂ : ∫ z, fderiv ℝ φ z e • (jetLp (testSection F₀ F₁) ξ z).1 ∂stripMeasure =
        ∫ z, fderiv ℝ φ z e • (ξ : ℝ × ℝ → V) z ∂stripMeasure :=
      integral_congr_ae (hξ.mono fun z hz ↦ by simp only [hz, jet_apply])
    rw [e₁, e₂, ← integral_add hint₁ hint₂]
    exact integral_smul_fderiv_add_eq_zero hφ hφU ξ.property he
  have hker : (H1 F₀ F₁ : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ {f | Λ f = 0} :=
    jetClosure_subset_of_isClosed (isClosed_eq Λ.continuous continuous_const) hrange
  rw [← hΛ]
  exact hker hx

/-- On the open strip `ℝ × (0, 1)`, the derivative component `P x` of an `L²` jet `x ∈ H1` in the
coordinate direction `e` is the weak derivative of its value `x₁` in the direction `e`. -/
private theorem hasWeakLineDerivOn_of_mem_H1 {x : Lp (V × V × V) 2 stripMeasure} (hx : x ∈ H1 F₀ F₁)
    {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1)) {P : V × V × V →L[ℝ] V}
    (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) :
    HasWeakLineDerivOn stripMeasure ⟨univ ×ˢ Ioo 0 1, isOpen_univ.prod isOpen_Ioo⟩
      (fun z ↦ (x z).1) (fun z ↦ P (x z)) e := by
  have hloc : ∀ Q : V × V × V →L[ℝ] V, LocallyIntegrableOn (fun z ↦ Q (x z))
      (univ ×ˢ Ioo 0 1) stripMeasure := fun Q ↦
    (((memLp_congr_ae (Q.coeFn_compLpL x)).1 (Lp.memLp _)).locallyIntegrable
      (by norm_num)).locallyIntegrableOn _
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨inferInstance, hloc (ContinuousLinearMap.fst ℝ V (V × V)), hloc P, fun φ ↦ ?_⟩
  have hl : ∀ z, lineDeriv ℝ (φ : ℝ × ℝ → ℝ) z e = fderiv ℝ φ z e := fun z ↦
    ((φ.contDiff.differentiable (by simp)) z).lineDeriv_eq_fderiv
  simp_rw [hl]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [add_comm]
  exact integral_smul_add_eq_zero_of_mem_H1 hx (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    φ.tsupport_subset he hP

/-- On the open strip `ℝ × (0, 1)`, the `s`-derivative of an element of `H1` is the weak
derivative of its value in the direction `(1, 0)`. -/
theorem hasWeakLineDerivOn_derivSL (x : H1 F₀ F₁) :
    HasWeakLineDerivOn stripMeasure ⟨univ ×ˢ Ioo 0 1, isOpen_univ.prod isOpen_Ioo⟩
      (valueL F₀ F₁ x) (derivSL F₀ F₁ x) (1, 0) :=
  ((hasWeakLineDerivOn_of_mem_H1 x.property (Or.inl rfl) (P := (ContinuousLinearMap.fst ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ by rw [jet_apply]; rfl).congr_ae
      (ae_restrict_of_ae (coeFn_valueL x).symm)).congr_ae_deriv
    (ae_restrict_of_ae (coeFn_derivSL x).symm)

/-- On the open strip `ℝ × (0, 1)`, the `t`-derivative of an element of `H1` is the weak
derivative of its value in the direction `(0, 1)`. -/
theorem hasWeakLineDerivOn_derivTL (x : H1 F₀ F₁) :
    HasWeakLineDerivOn stripMeasure ⟨univ ×ˢ Ioo 0 1, isOpen_univ.prod isOpen_Ioo⟩
      (valueL F₀ F₁ x) (derivTL F₀ F₁ x) (0, 1) :=
  ((hasWeakLineDerivOn_of_mem_H1 x.property (Or.inr rfl) (P := (ContinuousLinearMap.snd ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ by rw [jet_apply]; rfl).congr_ae
      (ae_restrict_of_ae (coeFn_valueL x).symm)).congr_ae_deriv
    (ae_restrict_of_ae (coeFn_derivTL x).symm)

/-- **An element of `H1` is determined by its value.** The value map `(ξ, ξ_s, ξ_t) ↦ ξ` is
injective on `H1`: if the value of an element of `H1` vanishes, so do its derivatives, as they are
its weak derivatives. Thus `H1` is a space of sections of the strip. -/
theorem valueL_injective : Function.Injective (valueL F₀ F₁) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have hv : ∀ᵐ z ∂stripMeasure, valueL F₀ F₁ x z = 0 := by
    rw [hx]
    exact Lp.coeFn_zero V 2 stripMeasure
  have hΩ : stripMeasure.restrict ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) = stripMeasure :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_openStrip
  -- Each derivative vanishes almost everywhere, as the weak derivative of `0`.
  have hderiv : ∀ {D : Lp V 2 stripMeasure} {e : ℝ × ℝ},
      HasWeakLineDerivOn stripMeasure ⟨univ ×ˢ Ioo 0 1, isOpen_univ.prod isOpen_Ioo⟩
        (valueL F₀ F₁ x) D e → ∀ᵐ z ∂stripMeasure, D z = 0 := fun h ↦ by
    have h' := h.ae_eq_zero_of_isOpen isOpen_univ (ae_restrict_of_ae (hv.mono fun z hz _ ↦ hz))
    simp only [TopologicalSpace.Opens.coe_mk, hΩ] at h'
    exact h'.mono fun z hz ↦ hz (mem_univ z)
  refine Subtype.ext ((Lp.eq_zero_iff_ae_eq_zero).2 ?_)
  filter_upwards [coeFn_valueL x, coeFn_derivSL x, coeFn_derivTL x, hv,
    hderiv (hasWeakLineDerivOn_derivSL x), hderiv (hasWeakLineDerivOn_derivTL x)]
    with z h₁ h₂ h₃ h₄ h₅ h₆
  exact Prod.ext (h₁.symm.trans h₄) (Prod.ext (h₂.symm.trans h₅) (h₃.symm.trans h₆))

end Value

/-! ### Translation in the `s` direction -/

section Translate

/-- The translate `z ↦ ξ (z + (a, 0))` of a test section is a test section. -/
theorem comp_add_mem_testSection (hξ : ξ ∈ testSection F₀ F₁) (a : ℝ) :
    (fun z ↦ ξ (z + (a, 0))) ∈ testSection F₀ F₁ := by
  obtain ⟨h2, h0, h1, R, hR⟩ := mem_testSection_iff.1 hξ
  refine ⟨h2.comp (contDiff_id.add contDiff_const), fun s ↦ by simpa using h0 (s + a),
    fun s ↦ by simpa using h1 (s + a), R + |a|, fun s t hs ↦ ?_⟩
  have h := abs_add_le (s + a) (-a)
  rw [add_neg_cancel_right, abs_neg] at h
  simpa using hR (s + a) t (by linarith)

/-- The test sections are invariant under translation in the `s` direction, so translation by
`a`, `TauCeti.StripSobolev.translate (testSection F₀ F₁) a`, is a linear isometric equivalence of
`H1 F₀ F₁`. -/
instance : IsTranslationInvariant (testSection F₀ F₁) :=
  ⟨fun _ hξ a ↦ comp_add_mem_testSection hξ a⟩

/-- Translation of the jet of a test section is the jet of its translate. -/
theorem translate_jetH1 (a : ℝ) (ξ : testSection F₀ F₁) :
    translate (testSection F₀ F₁) a (jetH1 F₀ F₁ ξ) =
      jetH1 F₀ F₁ ⟨_, comp_add_mem_testSection ξ.property a⟩ :=
  Subtype.ext <| by rw [coe_translate, coe_jetH1, coe_jetH1, translateLp_jetLp]

/-- Translation by `0` is the identity. -/
@[simp]
theorem translate_zero (x : H1 F₀ F₁) : translate (testSection F₀ F₁) 0 x = x :=
  Subtype.ext <| by rw [coe_translate, translateLp_zero]

/-- Translations compose by adding the translation lengths. -/
@[simp]
theorem translate_translate (a b : ℝ) (x : H1 F₀ F₁) :
    translate (testSection F₀ F₁) a (translate (testSection F₀ F₁) b x) =
      translate (testSection F₀ F₁) (a + b) x :=
  Subtype.ext <| by rw [coe_translate, coe_translate, coe_translate, translateLp_translateLp]

end Translate

/-! ### Boundary traces -/

/-- The restriction of a test section to a horizontal line `ℝ × {t}` is in `Lᵖ` for every
`p`. -/
theorem memLp_slice (hξ : ξ ∈ testSection F₀ F₁) (t : ℝ) {p : ℝ≥0∞} :
    MemLp (fun s ↦ ξ (s, t)) p volume := by
  obtain ⟨h2, -, -, R, hR⟩ := mem_testSection_iff.1 hξ
  refine (h2.continuous.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs ↦ hR s t ?_)
  rw [mem_Icc, ← abs_le, not_le] at hs
  exact hs.le

variable (F₀ F₁) in
/-- The boundary values `(ξ (·, 0), ξ (·, 1))` of a test section, in `L²(ℝ, V) × L²(ℝ, V)`. -/
def traceₗ : testSection F₀ F₁ →ₗ[ℝ] Lp V 2 (volume : Measure ℝ) × Lp V 2 (volume : Measure ℝ)
    where
  toFun ξ := ((memLp_slice ξ.property 0).toLp _, (memLp_slice ξ.property 1).toLp _)
  map_add' ξ η := by
    refine Prod.ext ?_ ?_ <;>
    · simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, ← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun s ↦ rfl)
  map_smul' c ξ := by
    refine Prod.ext ?_ ?_ <;>
    · simp only [SetLike.val_smul, RingHom.id_apply, Prod.smul_fst, Prod.smul_snd,
        ← MemLp.toLp_const_smul]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun s ↦ rfl)

/-- The boundary values of a test section are the classes of its restrictions to the boundary
lines `ℝ × {0}` and `ℝ × {1}`. -/
theorem traceₗ_apply (ξ : testSection F₀ F₁) :
    traceₗ F₀ F₁ ξ = ((memLp_slice ξ.property 0).toLp _, (memLp_slice ξ.property 1).toLp _) :=
  (rfl)

/-- The boundary values of a test section do not depend on the boundary conditions it is
considered with. -/
@[simp]
theorem traceₗ_inclusion (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (ξ : testSection F₀ F₁) :
    traceₗ F₀' F₁' (Submodule.inclusion (testSection_mono h₀ h₁) ξ) = traceₗ F₀ F₁ ξ :=
  (rfl)

/-- The first boundary value of a test section is represented by `s ↦ ξ (s, 0)`. -/
theorem coeFn_traceₗ_fst (ξ : testSection F₀ F₁) :
    (traceₗ F₀ F₁ ξ).1 =ᵐ[volume] fun s ↦ (ξ : ℝ × ℝ → V) (s, 0) :=
  MemLp.coeFn_toLp (memLp_slice ξ.property 0)

/-- The second boundary value of a test section is represented by `s ↦ ξ (s, 1)`. -/
theorem coeFn_traceₗ_snd (ξ : testSection F₀ F₁) :
    (traceₗ F₀ F₁ ξ).2 =ᵐ[volume] fun s ↦ (ξ : ℝ × ℝ → V) (s, 1) :=
  MemLp.coeFn_toLp (memLp_slice ξ.property 1)

end NormedSpace

section Trace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {F₀ F₁ F₀' F₁' : Submodule ℝ V} {ξ : ℝ × ℝ → V}

/-- **The trace estimate on a segment.** For a `C¹` map `ξ` and every `s`, the values of `ξ` at
the two ends of the segment `{s} × [0, 1]` are controlled by the jet of `ξ` along the segment:
`‖ξ (s, 0)‖² + ‖ξ (s, 1)‖² ≤ 4 ∫₀¹ ‖jet ξ (s, t)‖² dt`. -/
theorem norm_sq_add_norm_sq_le_integral_jet (hξ : ContDiff ℝ 1 ξ) (s : ℝ) :
    ‖ξ (s, 0)‖ ^ 2 + ‖ξ (s, 1)‖ ^ 2 ≤ ∫ t in Icc (0 : ℝ) 1, 4 * ‖jet ξ (s, t)‖ ^ 2 := by
  have hderiv : ∀ t, deriv (fun t ↦ ξ (s, t)) t = fderiv ℝ ξ (s, t) (0, 1) := fun t ↦
    (hasDerivAt_slice_right ((hξ.differentiable one_ne_zero) (s, t))).deriv
  have h := norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq
    (g := fun t ↦ ξ (s, t)) (hξ.comp (contDiff_const.prodMk contDiff_id)).contDiffOn
    zero_lt_one
  simp only [hderiv] at h
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at h
  have := hξ.continuous_fderiv one_ne_zero
  have := continuous_jet hξ
  have := hξ.continuous
  refine h.trans (setIntegral_mono_on ?_ ?_ measurableSet_Icc fun t _ ↦ ?_)
  · exact Continuous.integrableOn_Icc (by fun_prop)
  · exact Continuous.integrableOn_Icc (by fun_prop)
  · nlinarith [norm_nonneg (ξ (s, t)), norm_nonneg (fderiv ℝ ξ (s, t) (0, 1)),
      norm_le_norm_jet ξ (s, t), norm_fderiv_zero_one_le_norm_jet ξ (s, t)]

/-- **The trace estimate on the strip.** The boundary values of a test section are bounded in
`L²` by twice its `W^{1,2}` norm. -/
theorem norm_traceₗ_le (ξ : testSection F₀ F₁) :
    ‖traceₗ F₀ F₁ ξ‖ ≤ 2 * ‖jetH1 F₀ F₁ ξ‖ := by
  have hj := memLp_jet ξ.property
  have h0 := memLp_slice ξ.property 0 (p := 2)
  have h1 := memLp_slice ξ.property 1 (p := 2)
  have hμ := stripMeasure_eq_prod
  have hint : Integrable (fun z ↦ 4 * ‖jet (ξ : ℝ × ℝ → V) z‖ ^ 2) stripMeasure :=
    (hj.integrable_norm_pow two_ne_zero).const_mul 4
  -- Integrate the trace estimate on the segments `{s} × [0, 1]` over `s`.
  have hsq : ‖h0.toLp _‖ ^ 2 + ‖h1.toLp _‖ ^ 2 ≤ 4 * ‖jetH1 F₀ F₁ ξ‖ ^ 2 := by
    rw [h0.norm_toLp_sq, h1.norm_toLp_sq, ← Submodule.norm_coe, coe_jetH1, jetLp_apply,
      hj.norm_toLp_sq, ← integral_add (h0.integrable_norm_pow two_ne_zero)
        (h1.integrable_norm_pow two_ne_zero), ← integral_const_mul]
    rw [hμ] at hint ⊢
    rw [integral_prod _ hint]
    exact integral_mono ((h0.integrable_norm_pow two_ne_zero).add
      (h1.integrable_norm_pow two_ne_zero)) hint.integral_prod_left
      fun s ↦ norm_sq_add_norm_sq_le_integral_jet (contDiff_one_of_mem_testSection ξ.property) s
  have hle : ∀ a : ℝ, 0 ≤ a → a ^ 2 ≤ 4 * ‖jetH1 F₀ F₁ ξ‖ ^ 2 → a ≤ 2 * ‖jetH1 F₀ F₁ ξ‖ :=
    fun a ha h ↦ (pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero).1 (by nlinarith)
  rw [traceₗ_apply, Prod.norm_def]
  exact max_le (hle _ (norm_nonneg _) (by nlinarith [sq_nonneg ‖h1.toLp _‖]))
    (hle _ (norm_nonneg _) (by nlinarith [sq_nonneg ‖h0.toLp _‖]))

variable [CompleteSpace V]

variable (F₀ F₁) in
/-- The **trace** of an element of `H1`: the continuous extension of the boundary values
`(ξ (·, 0), ξ (·, 1))` of test sections to `H1 F₀ F₁ → L²(ℝ, V) × L²(ℝ, V)`. -/
def traceL : H1 F₀ F₁ →L[ℝ] Lp V 2 (volume : Measure ℝ) × Lp V 2 (volume : Measure ℝ) :=
  (traceₗ F₀ F₁).extendOfNorm (jetH1 F₀ F₁)

/-- The trace of the jet of a test section is its boundary values. -/
@[simp]
theorem traceL_jetH1 (ξ : testSection F₀ F₁) : traceL F₀ F₁ (jetH1 F₀ F₁ ξ) = traceₗ F₀ F₁ ξ :=
  LinearMap.extendOfNorm_eq (f := traceₗ F₀ F₁) (e := jetH1 F₀ F₁) denseRange_jetH1
    ⟨2, norm_traceₗ_le⟩ ξ

/-- The trace is bounded by twice the `W^{1,2}` norm. -/
theorem norm_traceL_le (x : H1 F₀ F₁) : ‖traceL F₀ F₁ x‖ ≤ 2 * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (f := traceₗ F₀ F₁) (e := jetH1 F₀ F₁) denseRange_jetH1 2
    norm_traceₗ_le x

/-- **Boundary condition at `t = 0`.** If `F₀` is closed, the trace on `ℝ × {0}` of every
element of `H1 F₀ F₁` takes values in `F₀` almost everywhere. -/
theorem ae_traceL_fst_mem (hF₀ : IsClosed (F₀ : Set V)) (x : H1 F₀ F₁) :
    ∀ᵐ s, (traceL F₀ F₁ x).1 s ∈ F₀ := by
  refine H1_induction (P := fun x ↦ ∀ᵐ s, (traceL F₀ F₁ x).1 s ∈ F₀)
    ((Lp.isClosed_setOf_ae_mem hF₀).preimage (continuous_fst.comp (traceL F₀ F₁).continuous))
    (fun ξ ↦ ?_) x
  rw [traceL_jetH1]
  filter_upwards [coeFn_traceₗ_fst ξ] with s hs
  rw [hs]
  exact (mem_testSection_iff.1 ξ.property).2.1 s

/-- **Boundary condition at `t = 1`.** If `F₁` is closed, the trace on `ℝ × {1}` of every
element of `H1 F₀ F₁` takes values in `F₁` almost everywhere. -/
theorem ae_traceL_snd_mem (hF₁ : IsClosed (F₁ : Set V)) (x : H1 F₀ F₁) :
    ∀ᵐ s, (traceL F₀ F₁ x).2 s ∈ F₁ := by
  refine H1_induction (P := fun x ↦ ∀ᵐ s, (traceL F₀ F₁ x).2 s ∈ F₁)
    ((Lp.isClosed_setOf_ae_mem hF₁).preimage (continuous_snd.comp (traceL F₀ F₁).continuous))
    (fun ξ ↦ ?_) x
  rw [traceL_jetH1]
  filter_upwards [coeFn_traceₗ_snd ξ] with s hs
  rw [hs]
  exact (mem_testSection_iff.1 ξ.property).2.2.1 s

/-- The trace of an element of `H1` does not depend on the boundary conditions it is considered
with. -/
@[simp]
theorem traceL_inclusion (h₀ : F₀ ≤ F₀') (h₁ : F₁ ≤ F₁') (x : H1 F₀ F₁) :
    traceL F₀' F₁' (Submodule.inclusion (H1_mono h₀ h₁) x) = traceL F₀ F₁ x := by
  refine H1_induction
    (P := fun x ↦ traceL F₀' F₁' (Submodule.inclusion (H1_mono h₀ h₁) x) = traceL F₀ F₁ x)
    (isClosed_eq ((traceL F₀' F₁').continuous.comp (continuous_subtypeVal.subtype_mk _))
      (traceL F₀ F₁).continuous) (fun ξ ↦ ?_) x
  rw [inclusion_jetH1 h₀ h₁, traceL_jetH1, traceL_jetH1, traceₗ_inclusion h₀ h₁]

/-- **The boundary conditions are faithful.** If `F₀` and `F₁` are closed, the jet of a `C²`
section vanishing for `|s|` large lies in `H1 F₀ F₁` exactly when the boundary values of the
section lie in `F₀` and `F₁`, that is, when it is a test section for these boundary
conditions. -/
theorem jetLp_mem_H1_iff (hF₀ : IsClosed (F₀ : Set V)) (hF₁ : IsClosed (F₁ : Set V))
    (ξ : testSection (⊤ : Submodule ℝ V) ⊤) :
    jetLp (testSection ⊤ ⊤) ξ ∈ H1 F₀ F₁ ↔ (ξ : ℝ × ℝ → V) ∈ testSection F₀ F₁ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · have := jetLp_mem_jetClosure (S := testSection F₀ F₁) ⟨ξ, h⟩
    rwa [← jetLp_inclusion le_top le_top] at this
  have htr : traceL F₀ F₁ ⟨_, h⟩ = traceₗ ⊤ ⊤ ξ := by
    rw [← traceL_inclusion le_top le_top, ← traceL_jetH1]
    exact congrArg _ (Subtype.ext (by rw [Submodule.coe_inclusion, coe_jetH1]))
  obtain ⟨hξ, -, -, hR⟩ := mem_testSection_iff.1 ξ.property
  have hall {F : Submodule ℝ V} (hF : IsClosed (F : Set V)) (t : ℝ)
      (h : ∀ᵐ s, (ξ : ℝ × ℝ → V) (s, t) ∈ F) (s : ℝ) : (ξ : ℝ × ℝ → V) (s, t) ∈ F :=
    Set.eq_univ_iff_forall.1 ((hF.preimage (hξ.continuous.comp
      (continuous_id.prodMk continuous_const))).dense_iff.1 (Measure.dense_of_ae h)) s
  refine mem_testSection_iff.2 ⟨hξ, hall hF₀ 0 ?_, hall hF₁ 1 ?_, hR⟩
  · filter_upwards [ae_traceL_fst_mem hF₀ ⟨_, h⟩, coeFn_traceₗ_fst ξ] with s h₁ h₂
    rwa [htr, h₂] at h₁
  · filter_upwards [ae_traceL_snd_mem hF₁ ⟨_, h⟩, coeFn_traceₗ_snd ξ] with s h₁ h₂
    rwa [htr, h₂] at h₁

end Trace

/-! ### Green's formulas -/

section Green

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {F₀ F₁ : Submodule ℝ V} {ξ η : ℝ × ℝ → V}

open scoped InnerProductSpace

/-- The fundamental theorem of calculus on a segment `{s} × [0, 1]` for the inner product of two
`C¹` maps. -/
theorem integral_inner_fderiv_add_inner_fderiv (hξ : ContDiff ℝ 1 ξ) (hη : ContDiff ℝ 1 η)
    (s : ℝ) :
    ∫ t in Icc (0 : ℝ) 1, (⟪fderiv ℝ ξ (s, t) (0, 1), η (s, t)⟫_ℝ +
        ⟪ξ (s, t), fderiv ℝ η (s, t) (0, 1)⟫_ℝ) =
      ⟪ξ (s, 1), η (s, 1)⟫_ℝ - ⟪ξ (s, 0), η (s, 0)⟫_ℝ := by
  have hd : ∀ t, HasDerivAt (fun t ↦ ⟪ξ (s, t), η (s, t)⟫_ℝ)
      (⟪fderiv ℝ ξ (s, t) (0, 1), η (s, t)⟫_ℝ + ⟪ξ (s, t), fderiv ℝ η (s, t) (0, 1)⟫_ℝ) t :=
    fun t ↦ by
      rw [add_comm]
      exact (hasDerivAt_slice_right (hξ.differentiable one_ne_zero (s, t))).inner ℝ
        (hasDerivAt_slice_right (hη.differentiable one_ne_zero (s, t)))
  have := hξ.continuous_fderiv one_ne_zero
  have := hη.continuous_fderiv one_ne_zero
  have := hξ.continuous
  have := hη.continuous
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The integral over a line `ℝ × {t}` of the `s`-derivative of the inner product of two `C¹`
maps, one of which vanishes for `|s|` large, is zero. -/
theorem integral_inner_fderiv_add_inner_fderiv_eq_zero (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiff ℝ 1 η) {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) (t : ℝ) :
    ∫ s, (⟪fderiv ℝ ξ (s, t) (1, 0), η (s, t)⟫_ℝ + ⟪ξ (s, t), fderiv ℝ η (s, t) (1, 0)⟫_ℝ) =
      0 := by
  have hd : ∀ s, HasDerivAt (fun s ↦ ⟪ξ (s, t), η (s, t)⟫_ℝ)
      (⟪fderiv ℝ ξ (s, t) (1, 0), η (s, t)⟫_ℝ + ⟪ξ (s, t), fderiv ℝ η (s, t) (1, 0)⟫_ℝ) s :=
    fun s ↦ by
      rw [add_comm]
      exact (hasDerivAt_slice_left (hξ.differentiable one_ne_zero (s, t))).inner ℝ
        (hasDerivAt_slice_left (hη.differentiable one_ne_zero (s, t)))
  -- Outside `[-R, R]` the section `ξ` and its `s`-derivative vanish.
  have hK : ∀ s, s ∉ Icc (-R) R → ξ (s, t) = 0 ∧ fderiv ℝ ξ (s, t) (1, 0) = 0 := by
    intro s hs
    rw [mem_Icc, ← abs_le, not_le] at hs
    have h := jet_eq_zero_of_lt_abs hR (z := (s, t)) hs
    rw [jet_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h⟩
  have := hξ.continuous_fderiv one_ne_zero
  have := hη.continuous_fderiv one_ne_zero
  have := hξ.continuous
  have := hη.continuous
  refine integral_eq_zero_of_hasDerivAt_of_integrable hd ?_ ?_
  · refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs ↦ ?_)
    obtain ⟨h₁, h₂⟩ := hK s hs
    simp [h₁, h₂]
  · refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs ↦ ?_)
    simp [(hK s hs).1]

/-- For test sections `ξ`, `η` and an operator `D` on `H1` acting on jets as the derivative in a
direction `v`, `⟪D ξ, η⟫ + ⟪ξ, D η⟫` in `L²` is the integral over the strip of the integrable
function `⟪∂_v ξ, η⟫ + ⟪ξ, ∂_v η⟫`. -/
private theorem inner_add_inner_jetH1_eq_integral {D : H1 F₀ F₁ →L[ℝ] Lp V 2 stripMeasure}
    {v : ℝ × ℝ} (hD : ∀ ξ : testSection F₀ F₁,
      D (jetH1 F₀ F₁ ξ) =ᵐ[stripMeasure] fun z ↦ fderiv ℝ (ξ : ℝ × ℝ → V) z v)
    (ξ η : testSection F₀ F₁) :
    Integrable (fun z ↦ ⟪fderiv ℝ (ξ : ℝ × ℝ → V) z v, (η : ℝ × ℝ → V) z⟫_ℝ +
        ⟪(ξ : ℝ × ℝ → V) z, fderiv ℝ (η : ℝ × ℝ → V) z v⟫_ℝ) stripMeasure ∧
      ⟪D (jetH1 F₀ F₁ ξ), valueL F₀ F₁ (jetH1 F₀ F₁ η)⟫_ℝ +
          ⟪valueL F₀ F₁ (jetH1 F₀ F₁ ξ), D (jetH1 F₀ F₁ η)⟫_ℝ =
        ∫ z, (⟪fderiv ℝ (ξ : ℝ × ℝ → V) z v, (η : ℝ × ℝ → V) z⟫_ℝ +
          ⟪(ξ : ℝ × ℝ → V) z, fderiv ℝ (η : ℝ × ℝ → V) z v⟫_ℝ) ∂stripMeasure := by
  have hae : (fun z ↦ ⟪D (jetH1 F₀ F₁ ξ) z, valueL F₀ F₁ (jetH1 F₀ F₁ η) z⟫_ℝ +
      ⟪valueL F₀ F₁ (jetH1 F₀ F₁ ξ) z, D (jetH1 F₀ F₁ η) z⟫_ℝ) =ᵐ[stripMeasure]
        fun z ↦ ⟪fderiv ℝ (ξ : ℝ × ℝ → V) z v, (η : ℝ × ℝ → V) z⟫_ℝ +
          ⟪(ξ : ℝ × ℝ → V) z, fderiv ℝ (η : ℝ × ℝ → V) z v⟫_ℝ := by
    filter_upwards [hD ξ, valueL_jetH1 η, valueL_jetH1 ξ, hD η] with z h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄]
  refine ⟨((L2.integrable_inner (𝕜 := ℝ) _ _).add (L2.integrable_inner _ _)).congr hae, ?_⟩
  rw [L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner _ _)
    (L2.integrable_inner _ _), integral_congr_ae hae]

/-- Green's formula in the `s` direction for test sections. -/
private theorem inner_derivSL_add_inner_derivSL_jetH1 (ξ η : testSection F₀ F₁) :
    ⟪derivSL F₀ F₁ (jetH1 F₀ F₁ ξ), valueL F₀ F₁ (jetH1 F₀ F₁ η)⟫_ℝ +
        ⟪valueL F₀ F₁ (jetH1 F₀ F₁ ξ), derivSL F₀ F₁ (jetH1 F₀ F₁ η)⟫_ℝ = 0 := by
  obtain ⟨hint, heq⟩ := inner_add_inner_jetH1_eq_integral derivSL_jetH1 ξ η
  rw [heq]
  -- Integrate over each line `ℝ × {t}` first.
  rw [stripMeasure_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  obtain ⟨-, -, -, R, hR⟩ := mem_testSection_iff.1 ξ.property
  refine (integral_congr_ae (Eventually.of_forall fun t ↦ ?_)).trans (integral_zero _ ℝ)
  exact integral_inner_fderiv_add_inner_fderiv_eq_zero (contDiff_one_of_mem_testSection ξ.property)
    (contDiff_one_of_mem_testSection η.property) hR t

/-- **Green's formula in the `s` direction.** For `x`, `y ∈ H1 F₀ F₁`,
`⟪∂s x, y⟫ + ⟪x, ∂s y⟫ = 0` in `L²`: the strip has no boundary in the `s` direction. -/
theorem inner_derivSL_add_inner_derivSL (x y : H1 F₀ F₁) :
    ⟪derivSL F₀ F₁ x, valueL F₀ F₁ y⟫_ℝ + ⟪valueL F₀ F₁ x, derivSL F₀ F₁ y⟫_ℝ = 0 := by
  induction x, y using H1_induction₂ with
  | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
  | h ξ η => exact inner_derivSL_add_inner_derivSL_jetH1 ξ η

variable [CompleteSpace V]

/-- Green's formula in the `t` direction for test sections. -/
private theorem inner_derivTL_add_inner_derivTL_jetH1 (ξ η : testSection F₀ F₁) :
    ⟪derivTL F₀ F₁ (jetH1 F₀ F₁ ξ), valueL F₀ F₁ (jetH1 F₀ F₁ η)⟫_ℝ +
        ⟪valueL F₀ F₁ (jetH1 F₀ F₁ ξ), derivTL F₀ F₁ (jetH1 F₀ F₁ η)⟫_ℝ =
      ⟪(traceL F₀ F₁ (jetH1 F₀ F₁ ξ)).2, (traceL F₀ F₁ (jetH1 F₀ F₁ η)).2⟫_ℝ -
        ⟪(traceL F₀ F₁ (jetH1 F₀ F₁ ξ)).1, (traceL F₀ F₁ (jetH1 F₀ F₁ η)).1⟫_ℝ := by
  obtain ⟨hint, heq⟩ := inner_add_inner_jetH1_eq_integral derivTL_jetH1 ξ η
  rw [heq, L2.inner_def, L2.inner_def,
    ← integral_sub (L2.integrable_inner _ _) (L2.integrable_inner _ _), traceL_jetH1,
    traceL_jetH1]
  -- Integrate the fundamental theorem of calculus on the segments `{s} × [0, 1]` over `s`.
  rw [stripMeasure_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_traceₗ_fst ξ, coeFn_traceₗ_snd ξ, coeFn_traceₗ_fst η,
    coeFn_traceₗ_snd η] with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact integral_inner_fderiv_add_inner_fderiv (contDiff_one_of_mem_testSection ξ.property)
    (contDiff_one_of_mem_testSection η.property) s

/-- **Green's formula in the `t` direction.** For `x`, `y ∈ H1 F₀ F₁`,
`⟪∂t x, y⟫ + ⟪x, ∂t y⟫ = ⟪x(·, 1), y(·, 1)⟫ - ⟪x(·, 0), y(·, 0)⟫` in `L²`, the boundary values
being the traces. This is the boundary term in the formal adjoint of `∂s + J ∂t`. -/
theorem inner_derivTL_add_inner_derivTL (x y : H1 F₀ F₁) :
    ⟪derivTL F₀ F₁ x, valueL F₀ F₁ y⟫_ℝ + ⟪valueL F₀ F₁ x, derivTL F₀ F₁ y⟫_ℝ =
      ⟪(traceL F₀ F₁ x).2, (traceL F₀ F₁ y).2⟫_ℝ - ⟪(traceL F₀ F₁ x).1, (traceL F₀ F₁ y).1⟫_ℝ := by
  induction x, y using H1_induction₂ with
  | hP => exact isClosed_eq (by fun_prop) (by fun_prop)
  | h ξ η => exact inner_derivTL_add_inner_derivTL_jetH1 ξ η

end Green

end TauCeti.StripSobolev
