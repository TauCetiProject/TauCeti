/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The Sobolev space `W^{1,2}` on the cylinder and Peetre's argument

Let `V` be a finite-dimensional real normed space. Sections of the trivial bundle with fibre `V`
over the cylinder `ℝ × S¹` are maps `ξ : ℝ × ℝ → V` of period one in the second variable `t`, and
the fundamental domain of the cylinder is the strip `ℝ × [0, 1]` with its Lebesgue measure
`TauCeti.CylinderSobolev.stripMeasure`. This file sets up the Sobolev space `W^{1,2}(ℝ × S¹, V)`
and the functional analysis that turns an elliptic estimate for a first-order operator with
bounded coefficients on the cylinder into finite-dimensional kernel and closed range. It is the
setting of the linearized operators of Floer theory along Floer cylinders.

* **Test sections** (`TauCeti.CylinderSobolev.testSection`) are the `C²` maps of period one in
  `t` that vanish for `|s|` large.
* The **jet** of a section is `jet ξ = (ξ, ∂s ξ, ∂t ξ)`. The jet of a test section is square
  integrable on the strip (`TauCeti.CylinderSobolev.memLp_jet`), which gives the linear map
  `TauCeti.CylinderSobolev.jetL` into `L²(ℝ × [0, 1], V × V × V)`. Its norm is the `W^{1,2}` norm
  up to a factor between `1` and `√3`.
* `TauCeti.CylinderSobolev.H1` is the closure of the jets of test sections: the completion of the
  test sections in the `W^{1,2}` norm, realized inside `L²` as a closed subspace, hence complete.
  An element is an `L²` jet `(ξ, ξ_s, ξ_t)`, and it is determined by its value `ξ`
  (`TauCeti.CylinderSobolev.valueL_injective`): integrating by parts against test functions
  supported in the open strip `ℝ × (0, 1)` shows that `ξ_s` and `ξ_t` are the weak derivatives of
  `ξ` (`TauCeti.HasWeakLineDerivOn`), which vanish where `ξ` does
  (`TauCeti.HasWeakLineDerivOn.ae_eq_zero_of_isOpen`).
* **Rellich's theorem on the cylinder.** The value on a compact piece `[-T, T] × [0, 1]`
  (`TauCeti.CylinderSobolev.restrictValue`) is a compact operator on `H1`
  (`TauCeti.CylinderSobolev.isCompactOperator_restrictValue_comp_subtypeL`). The proof cuts a test
  section off near `[-T, T] × [0, 1]`, bounds the result and its derivative in `L²(ℝ²)` by the
  `W^{1,2}` norm on the strip through periodicity in `t`, and applies the Fréchet–Kolmogorov
  criterion `TauCeti.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl` with the
  translation estimate `ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`.
* A first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` with an essentially bounded coefficient field
  `M` acts on `L²` jets by `TauCeti.CylinderSobolev.jetOperator M`. **Peetre's argument**: if `D`
  satisfies the semi-Fredholm estimate

  `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

  (`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`) for all test sections, then its extension
  to `H1` has finite-dimensional kernel
  (`TauCeti.CylinderSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`) and closed range
  (`TauCeti.CylinderSobolev.isClosed_range_jetOperator_comp_subtypeL`), by Rellich's theorem and
  `ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`. The estimate is stated in the
  form proved for the linearized Floer operator in
  `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`.
* Integrals of functions of period one in `t` over `ℝ × [-1, 2]` are controlled by those over the
  strip (`TauCeti.lintegral_Icc_neg_one_two_le`), and the smooth cutoff comes from
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

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lebesgue measure on the strip `ℝ × [0, 1]`, the fundamental domain of the cylinder
`ℝ × S¹`. -/
abbrev stripMeasure : Measure (ℝ × ℝ) := volume.restrict (univ ×ˢ Icc 0 1)

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

/-- The jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`. -/
def jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V :=
  (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))

/-- The components of the jet. -/
theorem jet_apply (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    jet ξ z = (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) :=
  (rfl)

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a test section is continuous. -/
theorem continuous_jet (hξ : ξ ∈ testSection V) : Continuous (jet ξ) := by
  have h := hξ.1.continuous_fderiv (by norm_num)
  have h0 := hξ.1.continuous
  unfold jet
  fun_prop

/-- The jet is additive on test sections. -/
theorem jet_add (hξ : ξ ∈ testSection V) (hη : η ∈ testSection V) :
    jet (ξ + η) = jet ξ + jet η := by
  funext z
  have h₁ := (hξ.1.differentiable (by norm_num)) z
  have h₂ := (hη.1.differentiable (by norm_num)) z
  simp [jet, fderiv_add h₁ h₂]

/-- The jet commutes with scalar multiplication. -/
theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) : jet (c • ξ) = c • jet ξ := by
  funext z
  simp [jet, fderiv_const_smul_field]

/-- The jet of a test section has period one in `t`. -/
theorem jet_add_one (hξ : ξ ∈ testSection V) (s t : ℝ) : jet ξ (s, t + 1) = jet ξ (s, t) := by
  have hper : (fun z ↦ ξ (z + ((0 : ℝ), (1 : ℝ)))) = ξ :=
    funext fun ⟨s, t⟩ ↦ by simpa using hξ.2.1 s t
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := ξ) (x := (s, t)) ((0 : ℝ), (1 : ℝ))
  rw [hper] at h
  simp only [Prod.mk_add_mk, add_zero] at h
  simp [jet, ← h, hξ.2.1]

/-- The jet of a section vanishing for `|s| ≥ R` vanishes for `|s| > R`. -/
theorem jet_eq_zero_of_lt_abs {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {z : ℝ × ℝ}
    (hz : R < |z.1|) : jet ξ z = 0 := by
  have : ∀ᶠ w : ℝ × ℝ in 𝓝 z, R < |w.1| :=
    (continuous_abs.comp continuous_fst).continuousAt.eventually (lt_mem_nhds hz)
  have h : ξ =ᶠ[𝓝 z] 0 := by
    filter_upwards [this] with w hw
    exact hR w.1 w.2 hw.le
  simp [jet, h.fderiv_eq, h.eq_of_nhds]

/-- For a section vanishing for `|s| ≥ R`, the integral over the strip of a function vanishing
wherever the jet of the section vanishes is its integral over `[-R, R] × [0, 1]`. -/
private theorem integral_strip_eq_setIntegral_of_jet_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {F : ℝ × ℝ → E}
    (hF : ∀ z, jet ξ z = 0 → F z = 0) :
    ∫ z, F z ∂stripMeasure = ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, F z :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc)
    (prod_mono (subset_univ _) subset_rfl) fun z hz ↦ hF z (jet_eq_zero_of_lt_abs hR (by
      have h : z.1 ∉ Icc (-R) R := fun h ↦ hz.2 ⟨h, hz.1.2⟩
      rwa [mem_Icc, ← abs_le, not_le] at h))

/-- The jet of a test section is square integrable on the strip. -/
theorem memLp_jet (hξ : ξ ∈ testSection V) : MemLp (jet ξ) 2 stripMeasure := by
  obtain ⟨-, -, R, hR⟩ := id hξ
  set K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hae : jet ξ =ᵐ[stripMeasure] K.indicator (jet ξ) := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
    · rw [indicator_of_notMem hzK]
      refine jet_eq_zero_of_lt_abs hR ?_
      by_contra h
      exact hzK ⟨abs_le.1 (not_lt.1 h), hz.2⟩
  refine (memLp_congr_ae hae).2 ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet]
  have : IsFiniteMeasure (stripMeasure.restrict K) :=
    isFiniteMeasure_restrict.2 ((Measure.restrict_apply_le _ K).trans_lt
      hK.measure_lt_top).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_jet hξ).continuousOn
  exact MemLp.of_bound (continuous_jet hξ).aestronglyMeasurable C
    ((ae_restrict_mem hK.measurableSet).mono hC)

variable (V) in
/-- The `L²` jet `(ξ, ∂s ξ, ∂t ξ)` of a test section, as a linear map into
`L²(ℝ × [0, 1], V × V × V)`. -/
def jetL : testSection V →ₗ[ℝ] Lp (V × V × V) 2 stripMeasure where
  toFun ξ := (memLp_jet ξ.2).toLp (jet (ξ : ℝ × ℝ → V))
  map_add' ξ η := by
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_add ξ.2 η.2])
  map_smul' c ξ := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_smul])

/-- The `L²` jet of a test section is represented by its jet. -/
theorem coeFn_jetL (ξ : testSection V) : jetL V ξ =ᵐ[stripMeasure] jet (ξ : ℝ × ℝ → V) :=
  MemLp.coeFn_toLp (memLp_jet ξ.2)

/-- The `L²` jet of a test section is the class of its jet. -/
theorem jetL_apply (ξ : testSection V) :
    jetL V ξ = (memLp_jet ξ.2).toLp (jet (ξ : ℝ × ℝ → V)) :=
  (rfl)

/-- The norm of the `L²` jet of a test section is the `L²` norm of its jet on the strip. -/
theorem norm_jetL (ξ : testSection V) :
    ‖jetL V ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure).toReal := by
  rw [jetL_apply, Lp.norm_toLp]

variable (V) in
/-- The Sobolev space `W^{1,2}(ℝ × S¹, V)`: the closure in `L²(ℝ × [0, 1], V × V × V)` of the jets
of test sections, that is, the completion of the test sections in the `W^{1,2}` norm. An element
is an `L²` jet `(ξ, ξ_s, ξ_t)`; it is determined by its value `ξ`
(`TauCeti.CylinderSobolev.valueL_injective`). -/
def H1 : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  (LinearMap.range (jetL V)).topologicalClosure

/-- `H1` is a closed subspace of `L²`. -/
theorem isClosed_H1 : IsClosed (H1 V : Set (Lp (V × V × V) 2 stripMeasure)) :=
  Submodule.isClosed_topologicalClosure _

/-- `H1` is complete: it is a closed subspace of the complete space `L²`. -/
instance [CompleteSpace V] : CompleteSpace (H1 V) :=
  Submodule.topologicalClosure.completeSpace _

/-- The jet of a test section lies in `H1`. -/
theorem jetL_mem_H1 (ξ : testSection V) : jetL V ξ ∈ H1 V :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ ξ)

/-- The value `(ξ, ξ_s, ξ_t) ↦ ξ` of an element of `H1`, in `L²(ℝ × [0, 1], V)`. It is injective
(`TauCeti.CylinderSobolev.valueL_injective`). -/
def valueL : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure).comp (H1 V).subtypeL

/-- The value of an element of `H1` is represented by the first component of its jet. -/
theorem coeFn_valueL (x : H1 V) :
    valueL x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).1 :=
  (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL _

/-! ### Elements of `H1` are determined by their values -/

section Value

/-- The open strip `ℝ × (0, 1)`, of full measure in the closed strip. -/
private theorem ae_mem_openStrip : ∀ᵐ z ∂stripMeasure, z ∈ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 := by
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
    {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSection V) {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1)) :
    ∫ z, (φ z • fderiv ℝ ξ z e + fderiv ℝ φ z e • ξ z) ∂stripMeasure = 0 := by
  obtain ⟨hξ1, -, R, hR⟩ := hξ
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
    simp only [jet, Prod.mk_eq_zero] at h
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
    (hx : x ∈ H1 V) {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ)
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
    · filter_upwards [hφ₂.coeFn_toLp, P.coeFn_compLpL f] with z h₁ h₂
      simp [B, h₁, h₂]
    · filter_upwards [hφe.coeFn_toLp,
        (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL f] with z h₁ h₂
      simp [B, h₁, h₂]
  -- `Λ` vanishes on the jets of test sections, hence on their closure `H1`.
  have hrange : Set.range (jetL V) ⊆ {f | Λ f = 0} := by
    rintro _ ⟨ξ, rfl⟩
    rw [mem_ofPred_eq, hΛ]
    have hξ := coeFn_jetL ξ
    have hint₁ : Integrable (fun z ↦ φ z • fderiv ℝ (ξ : ℝ × ℝ → V) z e) stripMeasure :=
      (hφ.continuous.smul ((ξ.2.1.continuous_fderiv (by norm_num)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hφs.smul_right)
    have hint₂ : Integrable (fun z ↦ fderiv ℝ φ z e • (ξ : ℝ × ℝ → V) z) stripMeasure :=
      (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul
        ξ.2.1.continuous).integrable_of_hasCompactSupport ((hφs.fderiv_apply (𝕜 := ℝ) e).smul_right)
    have e₁ : ∫ z, φ z • P (jetL V ξ z) ∂stripMeasure =
        ∫ z, φ z • fderiv ℝ (ξ : ℝ × ℝ → V) z e ∂stripMeasure :=
      integral_congr_ae (hξ.mono fun z hz ↦ by simp only [hz, hP])
    have e₂ : ∫ z, fderiv ℝ φ z e • (jetL V ξ z).1 ∂stripMeasure =
        ∫ z, fderiv ℝ φ z e • (ξ : ℝ × ℝ → V) z ∂stripMeasure :=
      integral_congr_ae (hξ.mono fun z hz ↦ by simp only [hz, jet_apply])
    rw [e₁, e₂, ← integral_add hint₁ hint₂]
    exact integral_smul_fderiv_add_eq_zero hφ hφU ξ.2 he
  have hker : (H1 V : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ {f | Λ f = 0} := by
    rw [H1, Submodule.topologicalClosure_coe, LinearMap.coe_range]
    exact closure_minimal hrange (isClosed_eq Λ.continuous continuous_const)
  rw [← hΛ]
  exact hker hx

/-- On the open strip `ℝ × (0, 1)`, the derivative component `P x` of an `L²` jet `x ∈ H1` in the
coordinate direction `e` is the weak derivative of its value `x₁` in the direction `e`. -/
private theorem hasWeakLineDerivOn_of_mem_H1 {x : Lp (V × V × V) 2 stripMeasure} (hx : x ∈ H1 V)
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

/-- **An element of `H1` is determined by its value.** The value map `(ξ, ξ_s, ξ_t) ↦ ξ` is
injective on `H1`: if the value of an `L²` jet in `H1` vanishes, so do its derivative components,
as they are its weak derivatives. Thus `H1` is a space of sections of the cylinder, the Sobolev
space `W^{1,2}(ℝ × S¹, V)`. -/
theorem valueL_injective : Function.Injective (valueL (V := V)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have hx₁ : ∀ᵐ z ∂stripMeasure, ((x : Lp (V × V × V) 2 stripMeasure) z).1 = 0 := by
    have h := coeFn_valueL x
    rw [hx] at h
    filter_upwards [h, Lp.coeFn_zero V 2 stripMeasure] with z h₁ h₂
    simpa using h₁.symm.trans h₂
  have hΩ : stripMeasure.restrict ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) = stripMeasure :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_openStrip
  -- Each derivative component vanishes almost everywhere, as the weak derivative of `0`.
  have hcomp : ∀ {e : ℝ × ℝ} {P : V × V × V →L[ℝ] V}, (e = (1, 0) ∨ e = (0, 1)) →
      (∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) →
      ∀ᵐ z ∂stripMeasure, P ((x : Lp (V × V × V) 2 stripMeasure) z) = 0 := by
    intro e P he hP
    have h := (hasWeakLineDerivOn_of_mem_H1 x.2 he hP).ae_eq_zero_of_isOpen isOpen_univ
      (ae_restrict_of_ae (hx₁.mono fun z hz _ ↦ hz))
    simp only [TopologicalSpace.Opens.coe_mk, hΩ] at h
    exact h.mono fun z hz ↦ hz (mem_univ z)
  have h₂ := hcomp (Or.inl rfl) (P := (ContinuousLinearMap.fst ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ rfl
  have h₃ := hcomp (Or.inr rfl) (P := (ContinuousLinearMap.snd ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ rfl
  refine Subtype.ext ((Lp.eq_zero_iff_ae_eq_zero).2 ?_)
  filter_upwards [hx₁, h₂, h₃] with z h₁ h₂ h₃
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

end Value

/-! ### The cutoff -/

private theorem norm_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : ‖ξ z‖ ≤ ‖jet ξ z‖ :=
  norm_fst_le (jet ξ z)

private theorem norm_fderiv_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z (1, 0)‖ ≤ ‖jet ξ z‖ :=
  (norm_fst_le ((fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) : V × V)).trans (norm_snd_le (jet ξ z))

private theorem norm_fderiv_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z (0, 1)‖ ≤ ‖jet ξ z‖ :=
  (norm_snd_le ((fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) : V × V)).trans (norm_snd_le (jet ξ z))

private theorem norm_fderiv_le_two_mul_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z‖ ≤ 2 * ‖jet ξ z‖ := by
  linarith [(fderiv ℝ ξ z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one,
    norm_fderiv_one_zero_le_norm_jet ξ z, norm_fderiv_zero_one_le_norm_jet ξ z]

/-- A smooth cutoff on `ℝ × ℝ` equal to `1` on `[-T, T] × [0, 1]`, supported in a bounded subset
of `ℝ × [-1, 2]`, and vanishing near every point outside `ℝ × [-1, 2]`. -/
private theorem exists_cutoff (T : ℝ) : ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ 2 χ ∧ (∀ z, |χ z| ≤ 1) ∧
    (∀ z ∈ Icc (-T) T ×ˢ Icc (0 : ℝ) 1, χ z = 1) ∧
    (∀ z, χ z ≠ 0 → z ∈ Icc (-(|T| + 2)) (|T| + 2) ×ˢ Icc (-1 : ℝ) 2) ∧
    (∀ z : ℝ × ℝ, z.2 ∉ Icc (-1 : ℝ) 2 → χ =ᶠ[𝓝 z] 0) ∧ ∃ C, ∀ z, ‖fderiv ℝ χ z‖ ≤ C := by
  have hKU : Icc (-T) T ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (-(|T| + 2)) (|T| + 2) ×ˢ Ioo (-1 : ℝ) 2 :=
    prod_mono (Icc_subset_Ioo (by linarith [le_abs_self T]) (by linarith [le_abs_self T]))
      (Icc_subset_Ioo (by norm_num) (by norm_num))
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχU⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_contDiff_cutoff_eventuallyEq_one
      (isOpen_Ioo.prod isOpen_Ioo) hKU
  refine ⟨χ, hχ.of_le (by simp), fun z ↦ ?_, fun z hz ↦ (hχ1 z hz).self_of_nhds,
    fun z hz ↦ prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self (hχU (subset_tsupport χ hz)),
    fun z hz ↦ notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (Ioo_subset_Icc_self (hχU h).2), ?_⟩
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
  have hjm : AEStronglyMeasurable (jet ξ) volume := (continuous_jet hξ).aestronglyMeasurable
  have hper := TauCeti.eLpNorm_Icc_neg_one_two_le hjm (jet_add_one hξ)
  have hf : ContDiff ℝ 2 (fun z ↦ χ z • ξ z) := hχ.smul hξ.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨hf, ?_, ?_⟩
  · have hsub : Function.support (fun z ↦ χ z • ξ z) ⊆ P := fun z hz ↦
      ⟨mem_univ _, (hχB z (left_ne_zero_of_smul hz)).2⟩
    rw [← eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable hsub]
    refine (eLpNorm_mono hf.continuous.aestronglyMeasurable fun z ↦ ?_).trans hper
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχ1 z)).trans (norm_le_norm_jet ξ z)
  · have hpt : ∀ z, ‖fderiv ℝ (fun z ↦ χ z • ξ z) z‖ ≤ (C + 2) * ‖P.indicator (jet ξ) z‖ := by
      intro z
      by_cases hz : z ∈ P
      · rw [indicator_of_mem hz,
          fderiv_fun_smul (hχ.differentiable (by norm_num) z) (hξ.1.differentiable (by norm_num) z)]
        calc _ ≤ ‖χ z‖ * ‖fderiv ℝ ξ z‖ + ‖fderiv ℝ χ z‖ * ‖ξ z‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
          _ ≤ 1 * (2 * ‖jet ξ z‖) + C * ‖jet ξ z‖ := by
              gcongr
              exacts [(Real.norm_eq_abs _).trans_le (hχ1 z), norm_fderiv_le_two_mul_norm_jet ξ z,
                hC z, norm_le_norm_jet ξ z]
          _ = (C + 2) * ‖jet ξ z‖ := by ring
      · have hz' : z.2 ∉ Icc (-1 : ℝ) 2 := fun h ↦ hz ⟨mem_univ _, h⟩
        have h0 : (fun z ↦ χ z • ξ z) =ᶠ[𝓝 z] 0 := by
          filter_upwards [hχP z hz'] with w hw
          simp [hw]
        rw [h0.fderiv_eq]
        simp only [fderiv_zero, Pi.zero_apply, norm_zero]
        positivity
    calc eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume
        ≤ ENNReal.ofReal (C + 2) * eLpNorm (P.indicator (jet ξ)) 2 volume :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            (hf.continuous_fderiv (by norm_num)).aestronglyMeasurable
            (Eventually.of_forall hpt) 2
      _ = ENNReal.ofReal (C + 2) * eLpNorm (jet ξ) 2 (volume.restrict P) := by
          rw [eLpNorm_indicator_eq_eLpNorm_restrict hP.nullMeasurableSet]
      _ ≤ ENNReal.ofReal (C + 2) * (2 * eLpNorm (jet ξ) 2 stripMeasure) := by gcongr
      _ = ENNReal.ofReal (2 * (C + 2)) * eLpNorm (jet ξ) 2 stripMeasure := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring

/-! ### Compactness of the restriction to a compact piece of the cylinder -/

/-- The value of an `L²` jet on the cylinder, restricted to the compact piece
`[-T, T] × [0, 1]`. -/
def restrictValue (T : ℝ) :
    Lp (V × V × V) 2 stripMeasure →L[ℝ]
      Lp V 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)) :=
  (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 (Icc (-T) T ×ˢ Icc 0 1)).comp
    ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure)

/-- The restricted value of an `L²` jet is represented by the first component of the jet. -/
theorem coeFn_restrictValue (T : ℝ) (f : Lp (V × V × V) 2 stripMeasure) :
    restrictValue T f =ᵐ[stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)] fun z ↦ (f z).1 :=
  (LpToLpRestrictCLM_coeFn ℝ _ _).trans
    (ae_restrict_of_ae ((ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL f))

/-- The cut-off test sections of jet norm at most `2` form a totally bounded subset of
`L²(ℝ × ℝ, V)`, by the Fréchet–Kolmogorov criterion. -/
private theorem totallyBounded_setOf_cutoff [FiniteDimensional ℝ V] {χ : ℝ × ℝ → ℝ} {A : ℝ}
    {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B) (hχB : ∀ z, χ z ≠ 0 → z ∈ B)
    (hest : ∀ ξ ∈ testSection V, ContDiff ℝ 2 (fun z ↦ χ z • ξ z) ∧
      eLpNorm (fun z ↦ χ z • ξ z) 2 volume ≤ 2 * eLpNorm (jet ξ) 2 stripMeasure ∧
      eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume ≤
        ENNReal.ofReal A * eLpNorm (jet ξ) 2 stripMeasure) :
    TotallyBounded {f : Lp V 2 (volume : Measure (ℝ × ℝ)) | ∃ ξ ∈ testSection V,
      eLpNorm (jet ξ) 2 stripMeasure ≤ 2 ∧ f =ᵐ[volume] fun z ↦ χ z • ξ z} := by
  refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl (p := 2) (by norm_num)
    hB ?_ (M := 4) (by norm_num) ?_ ?_
  · rintro f ⟨ξ, -, -, hf⟩
    filter_upwards [hf] with z hz hzB
    rw [hz]
    by_contra h
    exact hzB (hχB z (left_ne_zero_of_smul h))
  · rintro f ⟨ξ, hξ, hξ2, hf⟩
    rw [eLpNorm_congr_ae hf]
    calc _ ≤ 2 * eLpNorm (jet ξ) 2 stripMeasure := (hest ξ hξ).2.1
      _ ≤ 2 * 2 := by gcongr
      _ = 4 := by norm_num
  · intro ε hε
    obtain ⟨r, -, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hr : 0 < r := ENNReal.ofReal_pos.1 hrpos
    set A₀ := max A 0
    refine ⟨r / (2 * A₀ + 1), by positivity, ?_⟩
    rintro f ⟨ξ, hξ, hξ2, hf⟩ h hh
    have hae : (fun z ↦ f (z + h) - f z) =ᵐ[volume]
        fun z ↦ χ (z + h) • ξ (z + h) - χ z • ξ z :=
      ((measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hf).sub hf
    rw [eLpNorm_congr_ae hae]
    calc _ ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume :=
          ((hest ξ hξ).1.of_le (by norm_num)).eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv
            (by norm_num) h
      _ ≤ ENNReal.ofReal ‖h‖ * (ENNReal.ofReal A₀ * 2) := by
          rw [ofReal_norm]
          gcongr
          calc _ ≤ ENNReal.ofReal A * eLpNorm (jet ξ) 2 stripMeasure := (hest ξ hξ).2.2
            _ ≤ ENNReal.ofReal A₀ * 2 := by
                gcongr
                exact le_max_left _ _
      _ = ENNReal.ofReal (‖h‖ * (2 * A₀)) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ ENNReal.ofReal r := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc ‖h‖ * (2 * A₀) ≤ r / (2 * A₀ + 1) * (2 * A₀ + 1) := by
                gcongr
                linarith
            _ = r := div_mul_cancel₀ _ (by positivity)
      _ ≤ ε := hrε.le

/-- An element of `H1` of norm less than `1` is a limit of jets of test sections of jet norm at
most `2`. -/
private theorem mem_closure_image_jetL (x : H1 V) (hx : ‖x‖ < 1) :
    (x : Lp (V × V × V) 2 stripMeasure) ∈
      closure (jetL V '' {ξ | eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure ≤ 2}) := by
  have hxH : (x : Lp (V × V × V) 2 stripMeasure) ∈ closure (Set.range (jetL V)) := by
    have : (x : Lp (V × V × V) 2 stripMeasure) ∈
        ((LinearMap.range (jetL V)).topologicalClosure : Set _) := x.2
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range] at this
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨_, ⟨ξ, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hxH (min ε 1) (lt_min hε one_pos)
  refine ⟨jetL V ξ, ⟨ξ, ?_, rfl⟩, hb.trans_le (min_le_left _ _)⟩
  have hnorm : ‖jetL V ξ‖ < 2 := by
    have := norm_le_norm_add_norm_sub' (jetL V ξ) (x : Lp (V × V × V) 2 stripMeasure)
    rw [← dist_eq_norm, dist_comm] at this
    have hx' : ‖(x : Lp (V × V × V) 2 stripMeasure)‖ < 1 := hx
    linarith [min_le_right ε 1]
  have hnorm' : (eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure).toReal < 2 := by
    rwa [norm_jetL] at hnorm
  have := (ENNReal.le_ofReal_iff_toReal_le (memLp_jet ξ.2).ne (by norm_num)).2 hnorm'.le
  simpa using this

/-- **Rellich's theorem on the cylinder.** The value on the compact piece `[-T, T] × [0, 1]` is a
compact operator from `W^{1,2}(ℝ × S¹, V)` to `L²`. -/
theorem isCompactOperator_restrictValue_comp_subtypeL [FiniteDimensional ℝ V] (T : ℝ) :
    IsCompactOperator ((restrictValue (V := V) T).comp (H1 V).subtypeL) := by
  obtain ⟨χ, A, hχT, hχB, hest⟩ := cutoff_estimates (V := V) T
  set rect : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc 0 1
  set S := {f : Lp V 2 (volume : Measure (ℝ × ℝ)) | ∃ ξ ∈ testSection V,
      eLpNorm (jet ξ) 2 stripMeasure ≤ 2 ∧ f =ᵐ[volume] fun z ↦ χ z • ξ z}
  have htb : TotallyBounded S :=
    totallyBounded_setOf_cutoff (isBounded_Icc _ _ |>.prod (isBounded_Icc _ _)) hχB hest
  -- Restriction from `L²(ℝ × ℝ)` to `L²([-T, T] × [0, 1])`.
  let Res : Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (stripMeasure.restrict rect) :=
    (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 rect).comp
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc 0 1))
  -- On a test section the restricted value is the restriction of the cut-off section.
  have hsub : restrictValue T '' (jetL V '' {ξ | eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure ≤ 2})
      ⊆ Res '' S := by
    rintro _ ⟨_, ⟨ξ, hξ, rfl⟩, rfl⟩
    have hmem : MemLp (fun z ↦ χ z • (ξ : ℝ × ℝ → V) z) 2 volume :=
      (hest ξ ξ.2).2.1.trans_lt (ENNReal.mul_lt_top (by simp) (memLp_jet ξ.2))
    refine ⟨hmem.toLp _, ⟨ξ, ξ.2, hξ, hmem.coeFn_toLp⟩, Lp.ext ?_⟩
    have h₁ := coeFn_restrictValue T (jetL V ξ)
    have h₂ : (jetL V ξ : ℝ × ℝ → V × V × V) =ᵐ[stripMeasure.restrict rect]
        jet (ξ : ℝ × ℝ → V) := ae_restrict_of_ae (coeFn_jetL ξ)
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
    ⟨_, mem_closure_image_jetL x (by simpa using hx), rfl⟩)

/-! ### First-order operators with bounded coefficients and Peetre's estimate -/

section Operator

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

open scoped Classical in
/-- The first-order operator `f ↦ (z ↦ M z (f z))` on `L²` jets on the cylinder, for an
essentially bounded coefficient field `M`; on the jet of a section `ξ` it is
`ξ ↦ M (ξ, ∂s ξ, ∂t ξ)`. If `M` is not essentially bounded, it is `0` by convention. -/
def jetOperator (M : ℝ × ℝ → V × V × V →L[ℝ] W) :
    Lp (V × V × V) 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure :=
  if hM : MemLp M ∞ stripMeasure then
    (ContinuousLinearMap.id ℝ (V × V × V →L[ℝ] W)).holderL stripMeasure ∞ 2 2 (hM.toLp M)
  else 0

/-- The first-order operator of a coefficient field that is not essentially bounded is `0`. -/
theorem jetOperator_of_not_memLp {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ¬ MemLp M ∞ stripMeasure) : jetOperator M = 0 := by
  simp [jetOperator, hM]

/-- The first-order operator of an essentially bounded coefficient field acts pointwise on
`L²` jets. -/
theorem coeFn_jetOperator {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    (f : Lp (V × V × V) 2 stripMeasure) :
    jetOperator M f =ᵐ[stripMeasure] fun z ↦ M z (f z) := by
  simp only [jetOperator, hM, ↓reduceDIte, ContinuousLinearMap.holderL_apply_apply]
  filter_upwards [(ContinuousLinearMap.id ℝ (V × V × V →L[ℝ] W)).coeFn_holder (r := 2)
    (hM.toLp M) f, hM.coeFn_toLp] with z h₁ h₂
  rw [h₁, ContinuousLinearMap.id_apply, h₂]

/-- On the jet of a test section `ξ`, the first-order operator of a coefficient field `M` is
`z ↦ M z (ξ z, ∂s ξ z, ∂t ξ z)`. -/
theorem jetOperator_jetL_ae_eq {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    (ξ : testSection V) :
    jetOperator M (jetL V ξ) =ᵐ[stripMeasure] fun z ↦ M z (jet (ξ : ℝ × ℝ → V) z) := by
  filter_upwards [coeFn_jetOperator hM (jetL V ξ), coeFn_jetL ξ] with z h₁ h₂
  rw [h₁, h₂]

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

private theorem sq_norm_jet_le (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖jet ξ z‖ ^ 2 ≤ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  have h : ‖jet ξ z‖ ≤ √(‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) := by
    simp only [jet, Prod.norm_def, max_le_iff]
    refine ⟨?_, ?_, ?_⟩ <;> refine Real.le_sqrt_of_sq_le ?_ <;> nlinarith [sq_nonneg ‖ξ z‖,
      sq_nonneg ‖fderiv ℝ ξ z (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ z (0, 1)‖]
  calc ‖jet ξ z‖ ^ 2 ≤ (√(‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 +
        ‖ξ z‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt (by positivity)

/-- The squared `L²` norm of the jet of a test section is at most its `W^{1,2}` energy. -/
private theorem sq_norm_jetL_le_integral (ξ : testSection V) :
    ‖jetL V ξ‖ ^ 2 ≤ ∫ z, (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 + ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) ∂stripMeasure := by
  have hjm := memLp_jet ξ.2
  rw [jetL_apply, hjm.norm_toLp_sq]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ by positivity) ?_
    (Eventually.of_forall fun z ↦ sq_norm_jet_le _ z)
  refine ((hjm.integrable_norm_pow two_ne_zero).const_mul 3).mono' ?_
    (Eventually.of_forall fun z ↦ ?_)
  · have h := ξ.2.1.continuous_fderiv (by norm_num)
    have h0 := ξ.2.1.continuous
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · have h₁ := norm_fderiv_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) z
    have h₂ := norm_fderiv_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) z
    have h₃ := norm_le_norm_jet (ξ : ℝ × ℝ → V) z
    rw [Real.norm_of_nonneg (by positivity)]
    linarith [pow_le_pow_left₀ (norm_nonneg _) h₁ 2, pow_le_pow_left₀ (norm_nonneg _) h₂ 2,
      pow_le_pow_left₀ (norm_nonneg _) h₃ 2]

/-- The squared `L²` norm of the restricted value of the jet of a test section is the integral of
`‖ξ‖²` over `[-T, T] × [0, 1]`. -/
private theorem sq_norm_restrictValue_jetL (T : ℝ) (ξ : testSection V) :
    ‖restrictValue T (jetL V ξ)‖ ^ 2 =
      ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 := by
  have hμ : stripMeasure.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) =
      volume.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc),
      inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]
  rw [← Lp.integral_norm_sq_eq_norm_sq, ← hμ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictValue T (jetL V ξ), ae_restrict_of_ae (coeFn_jetL ξ)]
    with z h₁ h₂
  rw [h₁, h₂, jet_apply]

/-- A semi-Fredholm estimate for test sections, as for the linearized Floer operator, gives
`‖f‖ ≤ √C (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the jets of test sections. -/
private theorem norm_jetL_le {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ}
    (hest : HasSemiFredholmEstimate M C T)
    (ξ : testSection V) :
    ‖jetL V ξ‖ ≤ √(max C 0) * (‖jetOperator M (jetL V ξ)‖ +
      ‖restrictValue T (jetL V ξ)‖) := by
  obtain ⟨hξ, hper, R, hR⟩ := ξ.2
  set R₀ := max R 0
  have hR₀ : ∀ s t, R₀ ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR s t ((le_max_left R 0).trans hs)
  have hvan : ∀ s t, s ∉ Ioo (-R₀) R₀ → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR₀ s t (by rwa [mem_Ioo, ← abs_lt, not_lt] at hs)
  set x := ‖jetOperator M (jetL V ξ)‖
  set y := ‖restrictValue T (jetL V ξ)‖
  -- The squared norms of the two terms of the estimate as integrals.
  have hx : x ^ 2 = ∫ z in Icc (-R₀) R₀ ×ˢ Icc (0 : ℝ) 1,
      ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 := by
    have hae : (fun z ↦ ‖jetOperator M (jetL V ξ) z‖ ^ 2) =ᵐ[stripMeasure]
        fun z ↦ ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 :=
      (jetOperator_jetL_ae_eq hM ξ).mono fun z hz ↦ by simp only [hz]
    rw [← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae hae]
    exact integral_strip_eq_setIntegral_of_jet_eq_zero hR₀ fun z hz ↦ by
      rw [hz, map_zero, norm_zero, zero_pow two_ne_zero]
  have hy : y ^ 2 = ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 :=
    sq_norm_restrictValue_jetL T ξ
  have hmain := hest hξ hper (neg_le_self (le_max_right R 0)) hvan
  rw [← integral_strip_eq_setIntegral_of_jet_eq_zero hR₀ fun z hz ↦ by
    simp [jet, Prod.ext_iff] at hz; simp [hz.1, hz.2.1, hz.2.2], ← hx, ← hy] at hmain
  -- Conclude by taking square roots.
  have hsq : ‖jetL V ξ‖ ^ 2 ≤ (√(max C 0) * (x + y)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
    calc ‖jetL V ξ‖ ^ 2 ≤ C * (x ^ 2 + y ^ 2) := (sq_norm_jetL_le_integral ξ).trans hmain
      _ ≤ max C 0 * (x ^ 2 + y ^ 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (x + y) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          nlinarith [norm_nonneg (jetOperator M (jetL V ξ)),
            norm_nonneg (restrictValue T (jetL V ξ))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- The estimate of `norm_jetL_le` extends from the jets of test sections to `H¹`, with a
compact error term. -/
private theorem exists_compact_estimate [FiniteDimensional ℝ V] {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate M C T) :
    ∃ K : H1 V →L[ℝ] Lp V 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)),
      IsCompactOperator K ∧ ∀ x : H1 V,
        ‖x‖ ≤ √(max C 0) * ‖(jetOperator M).comp (H1 V).subtypeL x‖ + ‖K x‖ := by
  set c := √(max C 0)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  set D := jetOperator M
  refine ⟨c • (restrictValue T).comp (H1 V).subtypeL,
    (isCompactOperator_restrictValue_comp_subtypeL T).smul c, ?_⟩
  -- The estimate holds on a closed set containing the jets of all test sections.
  set S : Set (Lp (V × V × V) 2 stripMeasure) := {f | ‖f‖ ≤ c * ‖D f‖ + c * ‖restrictValue T f‖}
  have hS : IsClosed S := isClosed_le continuous_norm
    ((continuous_const.mul (continuous_norm.comp D.continuous)).add
      (continuous_const.mul (continuous_norm.comp (restrictValue T).continuous)))
  have hrange : Set.range (jetL V) ⊆ S := by
    rintro _ ⟨ξ, rfl⟩
    have := norm_jetL_le hM hest ξ
    simp only [S, mem_ofPred_eq]
    linarith
  have hH1 : (H1 V : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ S := by
    rw [H1, Submodule.topologicalClosure_coe, LinearMap.coe_range]
    exact closure_minimal hrange hS
  intro x
  have := hH1 x.2
  simp only [S, mem_ofPred_eq] at this
  simpa [smul_apply, norm_smul, Real.norm_of_nonneg hc] using this

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
    FiniteDimensional ℝ ((jetOperator M).comp (H1 V).subtypeL).ker := by
  obtain ⟨K, hK, hbound⟩ := exists_compact_estimate hM hest
  exact ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate _ hK hbound

/-- **Peetre's argument on the cylinder: closed range.** Under the semi-Fredholm estimate of
`finiteDimensional_ker_jetOperator_comp_subtypeL`, the extension of `D` to
`W^{1,2}(ℝ × S¹, V)` has closed range in `L²(ℝ × S¹, W)`. -/
theorem isClosed_range_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate M C T) :
    IsClosed (((jetOperator M).comp (H1 V).subtypeL).range :
      Set (Lp W 2 stripMeasure)) := by
  obtain ⟨K, hK, hbound⟩ := exists_compact_estimate hM hest
  exact ContinuousLinearMap.isClosed_range_of_compact_estimate _ hK hbound

end Operator

end TauCeti.CylinderSobolev
