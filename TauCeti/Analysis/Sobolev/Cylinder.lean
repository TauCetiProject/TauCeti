/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Sobolev.Strip.Basic
public import TauCeti.Analysis.Sobolev.Strip.Operator
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.MeasureTheory.Measure.Haar.Prod

/-!
# The Sobolev space `W^{1,2}` on the cylinder and Peetre's argument

Let `V` be a finite-dimensional real normed space. Sections of the trivial bundle with fibre `V`
over the cylinder `ℝ × S¹` are maps `ξ : ℝ × ℝ → V` of period one in the second variable `t`, and
the fundamental domain of the cylinder is the strip `ℝ × [0, 1]` with its Lebesgue measure
`TauCeti.StripSobolev.stripMeasure`. This file sets up the Sobolev space `W^{1,2}(ℝ × S¹, V)`
and the functional analysis that turns an elliptic estimate for a first-order operator with
bounded coefficients on the cylinder into finite-dimensional kernel and closed range. It is the
setting of the linearized operators of Floer theory along Floer cylinders.

* The strip measure is the product of Lebesgue measure and Lebesgue measure on `[0, 1]`
  (`TauCeti.CylinderSobolev.stripMeasure_eq_prod`). A section that is bounded on a box
  `[-R, R] × [0, 1]` and vanishes outside it lies in every `Lᵖ` of the strip
  (`TauCeti.CylinderSobolev.memLp_stripMeasure_of_bound_of_eq_zero`), in particular a continuous
  section vanishing for `|s|` large (`TauCeti.CylinderSobolev.memLp_stripMeasure_of_continuous`)
  and a product section `φ(s) ψ(t)` with `φ` compactly supported
  (`TauCeti.CylinderSobolev.memLp_smul_of_hasCompactSupport`). A section depending continuously
  on `t` alone is essentially bounded (`TauCeti.CylinderSobolev.memLp_top_comp_snd`), and
  multiplication by a continuous family of invertible maps depending on `t` alone maps `L²` onto
  `L²` (`TauCeti.CylinderSobolev.surjective_operatorMultiplication_comp_snd`).
* **Test sections** (`TauCeti.CylinderSobolev.testSection`) are the `C²` maps of period one in
  `t` that vanish for `|s|` large.
* The **jet** of a section is `jet ξ = (ξ, ∂s ξ, ∂t ξ)` (`TauCeti.StripSobolev.jet`). The jet of
  a test section is square integrable on the strip (`TauCeti.CylinderSobolev.memLp_jet`), which
  gives the linear map `TauCeti.StripSobolev.jetLp (testSection V)` into
  `L²(ℝ × [0, 1], V × V × V)`. Its norm is the `W^{1,2}` norm up to a factor between `1` and `√3`.
  The `L²` jets and their closure are the constructions `TauCeti.StripSobolev.jetLp` and
  `TauCeti.StripSobolev.jetClosure` of `TauCeti.Analysis.Sobolev.Strip.Jet`, shared with the strip
  with boundary conditions. The test sections are invariant under translation in `s`
  (`TauCeti.CylinderSobolev.comp_add_right_mem_testSection`), so the translation
  `TauCeti.StripSobolev.translate (testSection V) a` of that file is a linear isometric
  equivalence of `H1 V`.
* `TauCeti.CylinderSobolev.H1` is the closure of the jets of test sections: the completion of the
  test sections in the `W^{1,2}` norm, realized inside `L²` as a closed subspace, hence complete.
  An element is an `L²` jet `(ξ, ξ_s, ξ_t)`, and it is determined by its value `ξ`
  (`TauCeti.CylinderSobolev.valueL_injective`): `H1` lies in the Sobolev space of the strip with
  no boundary conditions (`TauCeti.CylinderSobolev.H1_le_strip`), whose elements are determined
  by their values (`TauCeti.StripSobolev.valueL_injective`).
* **Rellich's theorem on the cylinder.** The value on a compact piece `[-T, T] × [0, 1]`
  (`TauCeti.StripSobolev.restrictValue`) is a compact operator on `H1`
  (`TauCeti.CylinderSobolev.isCompactOperator_restrictValue_comp_subtypeL`). The proof cuts a test
  section off near `[-T, T] × [0, 1]`, bounds the result and its derivative in `L²(ℝ²)` by the
  `W^{1,2}` norm on the strip through periodicity in `t`
  (`TauCeti.StripSobolev.eLpNorm_fderiv_smul_le`), and applies the Fréchet–Kolmogorov criterion
  for `C¹` functions `TauCeti.totallyBounded_of_contDiff_of_eLpNorm_fderiv_le`.
* A first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` with an essentially bounded coefficient field
  `M` acts on `L²` jets by `TauCeti.jetOperator stripMeasure M`; the steps of Peetre's argument
  shared with the strip with boundary conditions are in
  `TauCeti.Analysis.Sobolev.Strip.Operator`. **Peetre's argument**: if `D` satisfies the
  semi-Fredholm estimate

  `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

  (`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`) for all test sections, then its extension
  to `H1` has finite-dimensional kernel
  (`TauCeti.CylinderSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`) and closed range
  (`TauCeti.CylinderSobolev.isClosed_range_jetOperator_comp_subtypeL`), by Rellich's theorem and
  `TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le`.
  The estimate is stated in the form proved for the linearized Floer operator in
  `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`.
* **An estimate from below.** If `D` moreover bounds every test section in `L²` over the whole
  strip, `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`, the compact error term disappears: the extension satisfies
  `‖x‖ ≤ K ‖D x‖` on `H1`
  (`TauCeti.CylinderSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`), so
  it is injective (`TauCeti.CylinderSobolev.ker_jetOperator_comp_subtypeL_eq_bot`).
* Integrals of functions of period one in `t` over `ℝ × [-1, 2]` are controlled by those over the
  strip (`TauCeti.setLIntegral_univ_prod_Icc_neg_one_two_le`), and the smooth cutoff comes from
  `IsCompact.exists_contDiff_cutoff_eventuallyEq_one`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S` on the
  cylinder.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces, Rellich's theorem and the semi-Fredholm estimate.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.16 (Rellich–Kondrachov) and Theorem 4.26 (Fréchet–Kolmogorov).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The strip measure is the product of Lebesgue measure and Lebesgue measure on `[0, 1]`. -/
theorem stripMeasure_eq_prod :
    stripMeasure = (volume : Measure ℝ).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [stripMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

omit [NormedSpace ℝ V] in
/-- A section bounded on `[-R, R] × [0, 1]` and vanishing for `|s| > R` lies in every `Lᵖ` of the
strip. -/
theorem memLp_stripMeasure_of_bound_of_eq_zero {u : ℝ × ℝ → V}
    (hu : AEStronglyMeasurable u stripMeasure) {C R : ℝ}
    (hC : ∀ z ∈ Icc (-R) R ×ˢ Icc 0 1, ‖u z‖ ≤ C) (hR : ∀ z : ℝ × ℝ, R < |z.1| → u z = 0)
    (p : ℝ≥0∞) : MemLp u p stripMeasure := by
  set K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  have hK : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : u =ᵐ[stripMeasure] K.indicator u := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ ?_
    by_cases hzR : |z.1| ≤ R
    · rw [indicator_of_mem (show z ∈ K from ⟨abs_le.1 hzR, hz.2⟩)]
    · rw [hR z (not_le.1 hzR), indicator_apply_eq_zero.2 fun _ ↦ hR z (not_le.1 hzR)]
  refine (memLp_congr_ae hae).2 ((memLp_indicator_iff_restrict hK.nullMeasurableSet).2 ?_)
  have : IsFiniteMeasure (stripMeasure.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ, stripMeasure, Measure.restrict_apply hK]
    exact (measure_mono inter_subset_left).trans_lt
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)⟩
  exact MemLp.of_bound hu.restrict C ((ae_restrict_mem hK).mono hC)

omit [NormedSpace ℝ V] in
/-- A continuous section vanishing for `|s| > R` lies in every `Lᵖ` of the strip. -/
theorem memLp_stripMeasure_of_continuous {u : ℝ × ℝ → V} (hu : Continuous u) {R : ℝ}
    (hR : ∀ z : ℝ × ℝ, R < |z.1| → u z = 0) (p : ℝ≥0∞) : MemLp u p stripMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-R) R ×ˢ Icc (0 : ℝ) 1) hu.continuousOn
  exact memLp_stripMeasure_of_bound_of_eq_zero hu.aestronglyMeasurable hC hR p

omit [NormedSpace ℝ V] in
/-- A section depending continuously on `t` alone is essentially bounded on the strip. -/
theorem memLp_top_comp_snd {f : ℝ → V} (hf : Continuous f) :
    MemLp (fun z : ℝ × ℝ ↦ f z.2) ∞ stripMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hf.continuousOn
  exact memLp_top_of_bound (hf.comp continuous_snd).aestronglyMeasurable C
    (ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ hC z.2 hz.2)

/-- A product section `φ(s) ψ(t)`, with `φ` continuous of compact support and `ψ` continuous,
lies in every `Lᵖ` of the strip. -/
theorem memLp_smul_of_hasCompactSupport {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {ψ : ℝ → V} (hψ : Continuous ψ) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ × ℝ ↦ φ z.1 • ψ z.2) p stripMeasure := by
  obtain ⟨R, -, hR⟩ := hφc.exists_pos_le_norm
  exact memLp_stripMeasure_of_continuous (u := fun z : ℝ × ℝ ↦ φ z.1 • ψ z.2)
    ((hφ.comp continuous_fst).smul (hψ.comp continuous_snd)) (R := R)
    (fun z hz ↦ by rw [hR z.1 (by rw [Real.norm_eq_abs]; exact hz.le), zero_smul]) p

variable (V) in
/-- The test sections of the trivial bundle with fibre `V` over the cylinder: `C²` maps
`ξ : ℝ × ℝ → V` of period one in `t` that vanish for `|s|` large. -/
def testSection : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ (∀ s t, ξ (s, t + 1) = ξ (s, t)) ∧
    ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0}
  zero_mem' := ⟨contDiff_const, fun _ _ ↦ rfl, 0, fun _ _ _ ↦ rfl⟩
  add_mem' := by
    rintro ξ η ⟨hξ, hξp, R, hR⟩ ⟨hη, hηp, R', hR'⟩
    refine ⟨hξ.add hη, fun s t ↦ by simp [hξp, hηp], max R R', fun s t hs ↦ ?_⟩
    simp [hR s t ((le_max_left _ _).trans hs), hR' s t ((le_max_right _ _).trans hs)]
  smul_mem' := by
    rintro c ξ ⟨hξ, hξp, R, hR⟩
    exact ⟨contDiff_const.smul hξ, fun s t ↦ by simp [hξp], R, fun s t hs ↦ by simp [hR s t hs]⟩

/-- Membership in the test sections. -/
theorem mem_testSection_iff {ξ : ℝ × ℝ → V} : ξ ∈ testSection V ↔ ContDiff ℝ 2 ξ ∧
    (∀ s t, ξ (s, t + 1) = ξ (s, t)) ∧ ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0 :=
  Iff.rfl

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a map of period one in `t` has period one in `t`. -/
theorem jet_add_one_of_periodic (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (s t : ℝ) :
    jet ξ (s, t + 1) = jet ξ (s, t) := by
  have hper : (fun z ↦ ξ (z + ((0 : ℝ), (1 : ℝ)))) = ξ :=
    funext fun ⟨s, t⟩ ↦ by simpa using hξp s t
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := ξ) (x := (s, t)) ((0 : ℝ), (1 : ℝ))
  rw [hper] at h
  simp only [Prod.mk_add_mk, add_zero] at h
  simp [jet_apply, ← h, hξp]

/-- The jet of a test section has period one in `t`. -/
theorem jet_add_one (hξ : ξ ∈ testSection V) (s t : ℝ) : jet ξ (s, t + 1) = jet ξ (s, t) :=
  jet_add_one_of_periodic (mem_testSection_iff.1 hξ).2.1 s t

/-- The jet of a test section tends to zero as `|s| → ∞`. -/
theorem tendsto_jet_comap_fst_cocompact (hξ : ξ ∈ testSection V) :
    Tendsto (jet ξ) (comap Prod.fst (cocompact ℝ)) (𝓝 0) := by
  obtain ⟨-, -, R, hR⟩ := mem_testSection_iff.1 hξ
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ᶠ z : ℝ × ℝ in comap Prod.fst (cocompact ℝ), R < |z.1| :=
    tendsto_comap.eventually ((tendsto_norm_cocompact_atTop.eventually_gt_atTop R).mono
      fun s hs ↦ by rwa [Real.norm_eq_abs] at hs)
  filter_upwards [hev] with z hz
  exact (jet_eq_zero_of_lt_abs hR hz).symm

/-- The jet of a test section is square integrable on the strip. -/
theorem memLp_jet (hξ : ξ ∈ testSection V) : MemLp (jet ξ) 2 stripMeasure := by
  obtain ⟨hξ2, -, R, hR⟩ := mem_testSection_iff.1 hξ
  exact memLp_jet_of_contDiff (hξ2.of_le (by norm_num)) hR

/-- The test sections are differentiable with square integrable jets. -/
instance : HasL2Jets (testSection V) :=
  ⟨fun _ hξ ↦ (mem_testSection_iff.1 hξ).1.differentiable (by norm_num), fun _ ↦ memLp_jet⟩

/-- The translate `ξ (· + a, ·)` of a test section is a test section. -/
theorem comp_add_right_mem_testSection (hξ : ξ ∈ testSection V) (a : ℝ) :
    (fun z ↦ ξ (z + (a, 0))) ∈ testSection V := by
  obtain ⟨hξ2, hξp, R, hR⟩ := mem_testSection_iff.1 hξ
  refine ⟨hξ2.comp (contDiff_id.add contDiff_const), fun s t ↦ by simpa using hξp (s + a) t,
    R + |a|, fun s t hs ↦ ?_⟩
  have := abs_add_le (s + a) (-a)
  rw [add_neg_cancel_right, abs_neg] at this
  simpa using hR (s + a) t (by linarith)

/-- The test sections are invariant under translation in the `s` direction. -/
instance : IsTranslationInvariant (testSection V) :=
  ⟨fun _ hξ a ↦ comp_add_right_mem_testSection hξ a⟩

variable (V) in
/-- The Sobolev space `W^{1,2}(ℝ × S¹, V)`: the closure in `L²(ℝ × [0, 1], V × V × V)` of the jets
of test sections, that is, the completion of the test sections in the `W^{1,2}` norm. An element
is an `L²` jet `(ξ, ξ_s, ξ_t)`; it is determined by its value `ξ`
(`TauCeti.CylinderSobolev.valueL_injective`). -/
abbrev H1 : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  jetClosure (testSection V)

/-- The value `(ξ, ξ_s, ξ_t) ↦ ξ` of an element of `H1`, in `L²(ℝ × [0, 1], V)`. It is injective
(`TauCeti.CylinderSobolev.valueL_injective`). -/
def valueL : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure).comp (H1 V).subtypeL

/-- The value of an element of `H1` is represented by the first component of its jet. -/
theorem coeFn_valueL (x : H1 V) :
    valueL x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).1 :=
  (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL _

/-! ### Elements of `H1` are determined by their values -/

/-- A test section of the cylinder is a test section of the strip with no boundary
conditions. -/
theorem testSection_le_strip : testSection V ≤ StripSobolev.testSection (⊤ : Submodule ℝ V) ⊤ :=
  fun _ hξ ↦ by
    obtain ⟨h2, -, hR⟩ := mem_testSection_iff.1 hξ
    exact StripSobolev.mem_testSection_iff.2
      ⟨h2, fun _ ↦ Submodule.mem_top, fun _ ↦ Submodule.mem_top, hR⟩

/-- The jet of a test section of the cylinder is its jet as a test section of the strip. -/
theorem jetLp_eq_strip (ξ : testSection V) :
    jetLp (testSection V) ξ =
      jetLp (StripSobolev.testSection ⊤ ⊤) (Submodule.inclusion testSection_le_strip ξ) := by
  rw [jetLp_apply, jetLp_apply]
  exact MemLp.toLp_congr _ _ (by rw [Submodule.coe_inclusion])

/-- `H1` of the cylinder lies in `H1` of the strip with no boundary conditions. -/
theorem H1_le_strip : H1 V ≤ StripSobolev.H1 (⊤ : Submodule ℝ V) ⊤ := by
  rw [H1, StripSobolev.H1, jetClosure_def, jetClosure_def]
  refine Submodule.topologicalClosure_mono ?_
  rintro _ ⟨ξ, rfl⟩
  exact ⟨Submodule.inclusion testSection_le_strip ξ, (jetLp_eq_strip ξ).symm⟩

/-- The value of an element of `H1` is its value as an element of `H1` of the strip with no
boundary conditions. -/
theorem valueL_eq_strip (x : H1 V) :
    valueL x = StripSobolev.valueL ⊤ ⊤ (Submodule.inclusion H1_le_strip x) := by
  refine Lp.ext ((coeFn_valueL x).trans ?_)
  filter_upwards [StripSobolev.coeFn_valueL (Submodule.inclusion H1_le_strip x)] with z hz
  rw [hz, Submodule.coe_inclusion]

/-- **An element of `H1` is determined by its value.** The value map `(ξ, ξ_s, ξ_t) ↦ ξ` is
injective on `H1`, as it is on `H1` of the strip (`TauCeti.StripSobolev.valueL_injective`). Thus
`H1` is a space of sections of the cylinder, the Sobolev space `W^{1,2}(ℝ × S¹, V)`. -/
theorem valueL_injective [CompleteSpace V] : Function.Injective (valueL (V := V)) := by
  intro x y h
  rw [valueL_eq_strip, valueL_eq_strip] at h
  exact Submodule.inclusion_injective _ (StripSobolev.valueL_injective h)

/-! ### The cutoff -/

/-- A smooth cutoff on `ℝ × ℝ` equal to `1` on `[-T, T] × [0, 1]`, supported in a bounded subset
of `ℝ × [-1, 2]`, with topological support in `ℝ × [-1, 2]`. -/
private theorem exists_cutoff (T : ℝ) : ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ 2 χ ∧ (∀ z, |χ z| ≤ 1) ∧
    (∀ z ∈ Icc (-T) T ×ˢ Icc (0 : ℝ) 1, χ z = 1) ∧
    (∀ z, χ z ≠ 0 → z ∈ Icc (-(|T| + 2)) (|T| + 2) ×ˢ Icc (-1 : ℝ) 2) ∧
    tsupport χ ⊆ univ ×ˢ Icc (-1 : ℝ) 2 ∧ ∃ C, ∀ z, ‖fderiv ℝ χ z‖ ≤ C := by
  have hKU : Icc (-T) T ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (-(|T| + 2)) (|T| + 2) ×ˢ Ioo (-1 : ℝ) 2 :=
    prod_mono (Icc_subset_Ioo (by linarith [le_abs_self T]) (by linarith [le_abs_self T]))
      (Icc_subset_Ioo (by norm_num) (by norm_num))
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχU⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_contDiff_cutoff_eventuallyEq_one
      (isOpen_Ioo.prod isOpen_Ioo) hKU
  refine ⟨χ, hχ.of_le (by simp), fun z ↦ ?_, fun z hz ↦ (hχ1 z hz).self_of_nhds,
    fun z hz ↦ prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self (hχU (subset_tsupport χ hz)),
    hχU.trans (prod_mono (subset_univ _) Ioo_subset_Icc_self), ?_⟩
  · obtain ⟨h₀, h₁⟩ := hχr (mem_range_self z)
    exact abs_le.2 ⟨by linarith, h₁⟩
  · exact (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (hχc.fderiv (𝕜 := ℝ))

private theorem cutoff_estimates (T : ℝ) : ∃ (χ : ℝ × ℝ → ℝ) (A : ℝ),
    (∀ z ∈ Icc (-T) T ×ˢ Icc (0 : ℝ) 1, χ z = 1) ∧
    (∀ z, χ z ≠ 0 → z ∈ Icc (-(|T| + 2)) (|T| + 2) ×ˢ Icc (-1 : ℝ) 2) ∧
    ∀ ξ ∈ testSection V, ContDiff ℝ 2 (fun z ↦ χ z • ξ z) ∧
      eLpNorm (fun z ↦ χ z • ξ z) 2 volume ≤ 2 * eLpNorm (jet ξ) 2 stripMeasure ∧
      eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume ≤
        ENNReal.ofReal A * eLpNorm (jet ξ) 2 stripMeasure := by
  obtain ⟨χ, hχ, hχ1, hχT, hχB, hχP, C, hC⟩ := exists_cutoff T
  refine ⟨χ, 2 * (C + 2), hχT, hχB, fun ξ hξ ↦ ?_⟩
  set P : Set (ℝ × ℝ) := univ ×ˢ Icc (-1 : ℝ) 2
  have hP : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Icc
  have hξ2 := (mem_testSection_iff.1 hξ).1
  have hjm : AEStronglyMeasurable (jet ξ) volume :=
    (continuous_jet (hξ2.of_le (by norm_num))).aestronglyMeasurable
  have hper := TauCeti.eLpNorm_restrict_univ_prod_Icc_neg_one_two_le hjm (jet_add_one hξ)
  have hf : ContDiff ℝ 2 (fun z ↦ χ z • ξ z) := hχ.smul hξ2
  refine ⟨hf, ?_, ?_⟩
  · have hsub : Function.support (fun z ↦ χ z • ξ z) ⊆ P := fun z hz ↦
      ⟨mem_univ _, (hχB z (left_ne_zero_of_smul hz)).2⟩
    rw [← eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable hsub]
    refine (eLpNorm_mono hf.continuous.aestronglyMeasurable fun z ↦ ?_).trans hper
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχ1 z)).trans (norm_le_norm_jet ξ z)
  · calc eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume
        ≤ ENNReal.ofReal (C + 2) * eLpNorm (jet ξ) 2 (volume.restrict P) :=
          eLpNorm_fderiv_smul_le (hχ.of_le (by norm_num)) hχ1 hC hP hχP (hξ2.of_le (by norm_num))
      _ ≤ ENNReal.ofReal (C + 2) * (2 * eLpNorm (jet ξ) 2 stripMeasure) := by gcongr
      _ = ENNReal.ofReal (2 * (C + 2)) * eLpNorm (jet ξ) 2 stripMeasure := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring

/-! ### Compactness of the restriction to a compact piece of the cylinder -/

/-- An element of `H1` of norm less than `2` is a limit of jets of test sections of jet norm at
most `2`, as `{f | ‖f‖ < 2}` is open (`IsOpen.inter_closure`). -/
private theorem mem_closure_image_jetLp (x : H1 V) (hx : ‖x‖ < 2) :
    (x : Lp (V × V × V) 2 stripMeasure) ∈
      closure (jetLp (testSection V) ''
        {ξ | eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure ≤ 2}) := by
  have hxH : (x : Lp (V × V × V) 2 stripMeasure) ∈ closure (Set.range (jetLp (testSection V))) := by
    rw [← coe_jetClosure (testSection V)]
    exact x.property
  refine closure_mono ?_ ((isOpen_lt continuous_norm continuous_const).inter_closure
    ⟨(Submodule.norm_coe x).trans_lt hx, hxH⟩)
  rintro _ ⟨hnorm, ξ, rfl⟩
  refine ⟨ξ, ?_, rfl⟩
  rw [mem_ofPred_eq, norm_jetLp] at hnorm
  simpa using (ENNReal.le_ofReal_iff_toReal_le (memLp_jet ξ.property).ne (by norm_num)).2 hnorm.le

/-- **Rellich's theorem on the cylinder.** The value on the compact piece `[-T, T] × [0, 1]` is a
compact operator from `W^{1,2}(ℝ × S¹, V)` to `L²`. -/
theorem isCompactOperator_restrictValue_comp_subtypeL [FiniteDimensional ℝ V] (T : ℝ) :
    IsCompactOperator ((restrictValue (V := V) T).comp (H1 V).subtypeL) := by
  obtain ⟨χ, A, hχT, hχB, hest⟩ := cutoff_estimates (V := V) T
  set rect : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc 0 1
  set S := {f : Lp V 2 (volume : Measure (ℝ × ℝ)) | ∃ ξ ∈ testSection V,
      eLpNorm (jet ξ) 2 stripMeasure ≤ 2 ∧ f =ᵐ[volume] fun z ↦ χ z • ξ z}
  -- The cut-off test sections of jet norm at most `2` are totally bounded in `L²` of the plane.
  have htb : TotallyBounded S := by
    refine totallyBounded_of_contDiff_of_eLpNorm_fderiv_le (by norm_num)
      (s := Icc (-(|T| + 2)) (|T| + 2) ×ˢ Icc (-1 : ℝ) 2)
      ((isBounded_Icc _ _).prod (isBounded_Icc _ _)) (M := ENNReal.ofReal A * 2 ⊔ 4)
      (by finiteness) fun f ⟨ξ, hξ, hξ2, hf⟩ ↦
        ⟨fun z ↦ χ z • ξ z, (hest ξ hξ).1.of_le (by norm_num), fun z hz ↦ ?_,
          le_sup_of_le_right ((hest ξ hξ).2.1.trans ?_),
          le_sup_of_le_left ((hest ξ hξ).2.2.trans (by gcongr)), hf⟩
    · by_contra h
      exact hz (hχB z (left_ne_zero_of_smul h))
    · calc 2 * eLpNorm (jet ξ) 2 stripMeasure ≤ 2 * 2 := by gcongr
        _ = 4 := by norm_num
  -- Restriction from `L²(ℝ × ℝ)` to `L²([-T, T] × [0, 1])`.
  let Res : Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (stripMeasure.restrict rect) :=
    (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 rect).comp
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc 0 1))
  -- On a test section the restricted value is the restriction of the cut-off section.
  have hsub : restrictValue T '' (jetLp (testSection V) ''
      {ξ | eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure ≤ 2}) ⊆ Res '' S := by
    rintro _ ⟨_, ⟨ξ, hξ, rfl⟩, rfl⟩
    have hmem : MemLp (fun z ↦ χ z • (ξ : ℝ × ℝ → V) z) 2 volume :=
      (hest ξ ξ.property).2.1.trans_lt (ENNReal.mul_lt_top (by simp) (memLp_jet ξ.property))
    refine ⟨hmem.toLp _, ⟨ξ, ξ.property, hξ, hmem.coeFn_toLp⟩, Lp.ext ?_⟩
    have h₁ := coeFn_restrictValue T (jetLp (testSection V) ξ)
    have h₂ : (jetLp (testSection V) ξ : ℝ × ℝ → V × V × V) =ᵐ[stripMeasure.restrict rect]
        jet (ξ : ℝ × ℝ → V) := ae_restrict_of_ae (coeFn_jetLp ξ)
    have h₃ : Res (hmem.toLp _) =ᵐ[stripMeasure.restrict rect] hmem.toLp _ :=
      (LpToLpRestrictCLM_coeFn ℝ _ _).trans (ae_restrict_of_ae (LpToLpRestrictCLM_coeFn ℝ _ _))
    have h₄ : (hmem.toLp _ : ℝ × ℝ → V) =ᵐ[stripMeasure.restrict rect]
        fun z ↦ χ z • (ξ : ℝ × ℝ → V) z :=
      ae_restrict_of_ae (ae_restrict_of_ae hmem.coeFn_toLp)
    filter_upwards [h₁, h₂, h₃, h₄, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
      with z h₁ h₂ h₃ h₄ hz
    rw [h₃, h₄, h₁, h₂, hχT z hz, one_smul, jet_apply]
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨ball 0 1, ball_mem_nhds 0 one_pos, _,
      (htb.image Res.uniformContinuous).closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact closure_mono hsub (image_closure_subset_closure_image (restrictValue T).continuous
    ⟨_, mem_closure_image_jetLp x ((mem_ball_zero_iff.1 hx).trans one_lt_two), rfl⟩)

/-! ### First-order operators with bounded coefficients and Peetre's estimate -/

section Operator

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Multiplication by a continuous family `Φ_t` of invertible maps depending on `t` alone, the
operator `f ↦ (z ↦ Φ_{z.2} (f z))`, maps `L²` of the strip onto `L²`: multiplication by the
inverses `Φ_t⁻¹` is a right inverse. -/
theorem surjective_operatorMultiplication_comp_snd [CompleteSpace V] {Φ : ℝ → V →L[ℝ] W}
    (hΦ : Continuous Φ) (hΦi : ∀ t, (Φ t).IsInvertible) :
    Function.Surjective (Lp.operatorMultiplication 2 ((memLp_top_comp_snd hΦ).toLp _)) := by
  have hΦinv : Continuous fun t ↦ (Φ t).inverse := continuous_iff_continuousAt.2 fun t ↦
    ((hΦi t).contDiffAt_map_inverse (n := 0)).continuousAt.comp hΦ.continuousAt
  set A := (memLp_top_comp_snd hΦ).toLp _
  set B := (memLp_top_comp_snd hΦinv).toLp _
  refine fun g ↦ ⟨Lp.operatorMultiplication 2 B g, Lp.ext ?_⟩
  filter_upwards [Lp.operatorMultiplication_ae A (Lp.operatorMultiplication 2 B g),
    Lp.operatorMultiplication_ae B g, (memLp_top_comp_snd hΦ).coeFn_toLp,
    (memLp_top_comp_snd hΦinv).coeFn_toLp] with z h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, (hΦi z.2).self_apply_inverse]

/-- The **semi-Fredholm estimate** with constants `C` and `T` for the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` on the cylinder: for every `C²` section `ξ` of period one in `t` that
vanishes for `s ∉ (a, b)`,

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`. This is the form proved for the linearized Floer
operator in `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`. -/
def HasSemiFredholmEstimate (M : ℝ × ℝ → V × V × V →L[ℝ] W) (C T : ℝ) : Prop :=
  ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
    ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
        C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
          ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)

/-- The defining property of `TauCeti.CylinderSobolev.HasSemiFredholmEstimate`. -/
theorem hasSemiFredholmEstimate_iff {M : ℝ × ℝ → V × V × V →L[ℝ] W} {C T : ℝ} :
    HasSemiFredholmEstimate M C T ↔
      ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
        ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
          ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
              ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
            C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
              ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  Iff.rfl

/-- A semi-Fredholm estimate for test sections, as for the linearized Floer operator, gives
`‖f‖ ≤ √C (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the jets of test sections. -/
theorem norm_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ} (hest : HasSemiFredholmEstimate M C T) (ξ : testSection V) :
    ‖jetLp (testSection V) ξ‖ ≤
      √(max C 0) * (‖jetOperator stripMeasure M (jetLp (testSection V) ξ)‖ +
        ‖restrictValue T (jetLp (testSection V) ξ)‖) := by
  obtain ⟨hξ, hper, R, hR⟩ := mem_testSection_iff.1 ξ.property
  have hR₀ : ∀ s t, max R 0 ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR s t ((le_max_left R 0).trans hs)
  exact norm_jetLp_le_of_setIntegral_le hM (hξ.of_le (by norm_num)) hR₀
    (hest hξ hper (neg_le_self (le_max_right R 0)) fun s t hs ↦
      hR₀ s t (by rwa [mem_Ioo, ← abs_lt, not_lt] at hs))

/-- **Peetre's argument on the cylinder: finite-dimensional kernel.** Let `M` be an essentially
bounded coefficient field on the cylinder, and suppose the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm estimate
(`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`)

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]` for every `C²` section `ξ` of period one in `t` vanishing for
`s ∉ (a, b)`. Then the extension of `D` to `W^{1,2}(ℝ × S¹, V)` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate M C T) :
    FiniteDimensional ℝ ((jetOperator stripMeasure M).comp (H1 V).subtypeL).ker :=
  finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le
    (isCompactOperator_restrictValue_comp_subtypeL T) (norm_jetLp_le hM hest)

/-- **Peetre's argument on the cylinder: closed range.** Under the semi-Fredholm estimate of
`finiteDimensional_ker_jetOperator_comp_subtypeL`, the extension of `D` to
`W^{1,2}(ℝ × S¹, V)` has closed range in `L²(ℝ × S¹, W)`. -/
theorem isClosed_range_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate M C T) :
    IsClosed (((jetOperator stripMeasure M).comp (H1 V).subtypeL).range :
      Set (Lp W 2 stripMeasure)) :=
  isClosed_range_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le
    (isCompactOperator_restrictValue_comp_subtypeL T) (norm_jetLp_le hM hest)

/-- **An estimate from below on `W^{1,2}`.** Let `M` be an essentially bounded coefficient field on
the cylinder whose first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm
estimate (`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`), and suppose that `D` also bounds the
value of every test section in `L²` over the whole strip: `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`. Then the
extension of `D` to `W^{1,2}(ℝ × S¹, V)` is bounded below: `‖x‖ ≤ K ‖D x‖` for every `x`. The
global `L²` bound removes the compact error term of the semi-Fredholm estimate. -/
theorem exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ}
    (hest : HasSemiFredholmEstimate M C T)
    (hL2 : ∀ ξ : testSection V, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ∃ K : ℝ≥0, ∀ x : H1 V, ‖x‖ ≤ K * ‖(jetOperator stripMeasure M).comp (H1 V).subtypeL x‖ :=
  ⟨⟨√(max C 0) * (1 + √(max C' 0)), by positivity⟩,
    norm_le_mul_norm_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le (Real.sqrt_nonneg _)
      (norm_jetLp_le hM hest) fun ξ ↦
        have ⟨hξ, _, _, hR⟩ := mem_testSection_iff.1 ξ.property
        norm_restrictValue_jetLp_le hM T hξ.continuous hR (hL2 ξ)⟩

/-- **Injectivity on `W^{1,2}`.** Under the hypotheses of
`TauCeti.CylinderSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`, a semi-Fredholm
estimate together with a global `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` on test sections, the extension
of `D` to `W^{1,2}(ℝ × S¹, V)` has trivial kernel. -/
theorem ker_jetOperator_comp_subtypeL_eq_bot {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ} (hest : HasSemiFredholmEstimate M C T)
    (hL2 : ∀ ξ : testSection V, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ((jetOperator stripMeasure M).comp (H1 V).subtypeL).ker = ⊥ := by
  obtain ⟨K, hK⟩ := exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL hM hest hL2
  exact LinearMap.ker_eq_bot.2 ((ContinuousLinearMap.antilipschitz_of_bound _ hK).injective)

end Operator

end TauCeti.CylinderSobolev
