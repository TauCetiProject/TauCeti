/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
public import TauCeti.MeasureTheory.Function.Lp.Norm
public import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The Sobolev space `W^{1,2}` on the cylinder

Sections of a trivial bundle with fibre `V` over the cylinder `ℝ × S¹`, with `S¹ = ℝ / ℤ`, are
maps `ξ : ℝ × ℝ → V` of period one in the second variable `t`. This file constructs the Sobolev
space `W^{1,2}(ℝ × S¹, V)` of such sections, for a real normed space `V`, together with the
compactness of restriction to a finite cylinder, which is what makes linear elliptic operators
on the cylinder, such as the linearized Floer operator along a Floer trajectory, semi-Fredholm.

**Test sections.** A test section (`TauCeti.CylinderSobolev.testSections`) is a `C²` map
`ξ : ℝ × ℝ → V` with `ξ (s, t + 1) = ξ (s, t)` that vanishes for `s` outside a bounded interval.
Its *jet* `TauCeti.CylinderSobolev.jet ξ z = (ξ z, ∂ₛ ξ z, ∂ₜ ξ z)` takes values in `V³` with the
Euclidean combination `‖(a, b, c)‖² = ‖a‖² + ‖b‖² + ‖c‖²` of the norms
(`TauCeti.CylinderSobolev.Jet`).

**The Sobolev space.** Let `μ` be Lebesgue measure on the fundamental domain `ℝ × [0, 1]`
(`TauCeti.CylinderSobolev.stripMeasure`). The jet of a test section is square integrable for `μ`,
and the jet map is linear (`TauCeti.CylinderSobolev.jetLp`). The space
`TauCeti.CylinderSobolev.W12 V` is the closure of the jets of test sections in `L²(μ, V³)`; it is
complete, and the test sections are dense in it (`TauCeti.CylinderSobolev.denseRange_toW12`). Its
norm is the `W^{1,2}` norm

`‖ξ‖² = ∫_{ℝ × [0, 1]} (‖∂ₛ ξ‖² + ‖∂ₜ ξ‖² + ‖ξ‖²)`

(`TauCeti.CylinderSobolev.norm_toW12_sq`). An element is a value together with its two weak
partial derivatives; the value is the continuous linear map `TauCeti.CylinderSobolev.valueL` to
`L²(μ, V)`. A linear map out of the test sections which is bounded by the `W^{1,2}` norm extends to
`W^{1,2}` by `LinearMap.extendOfNorm`, along the dense map `TauCeti.CylinderSobolev.toW12`.

**Compactness of restriction (Rellich).** For `V` finite dimensional and every `T`, the
restriction of the value to the finite cylinder `[-T, T] × [0, 1]`,
`TauCeti.CylinderSobolev.restrictValue T : W12 V →L[ℝ] L²([-T, T] × [0, 1], V)`, is a compact
operator (`TauCeti.CylinderSobolev.isCompactOperator_restrictValue`). The proof multiplies a test
section by a smooth cutoff `β`, equal to `1` on `[-T, T] × [0, 1]` and supported in
`(-|T| - 2, |T| + 2) × (-1, 2)`. By periodicity the cut-off sections have `W^{1,2}` norms on the
whole plane bounded by a multiple of their norms on the cylinder, they are supported in a fixed
bounded set, and their translates move in `L²` at most linearly in the translation
(`ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`). The Fréchet–Kolmogorov criterion
(`TauCeti.FrechetKolmogorov.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`)
makes the cut-off sections of norm at most one a totally bounded set of `L²(ℝ²)`, and restricting
them to `[-T, T] × [0, 1]` gives the restricted values.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.1
  (Sobolev spaces and the Rellich theorem) and Section 3.1 (the Fredholm setup on cylinders).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology Metric
open scoped ENNReal NNReal

namespace TauCeti.CylinderSobolev

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lebesgue measure on the fundamental domain `ℝ × [0, 1]` of the cylinder `ℝ × (ℝ / ℤ)`. -/
abbrev stripMeasure : Measure (ℝ × ℝ) :=
  volume.restrict (univ ×ˢ Icc (0 : ℝ) 1)

/-- The test sections of the cylinder: `C²` maps `ξ : ℝ × ℝ → V` of period one in `t` which vanish
for `s` outside a bounded interval. -/
def testSections : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ (∀ s t, ξ (s, t + 1) = ξ (s, t)) ∧
    ∃ a b : ℝ, ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0}
  add_mem' := by
    rintro ξ η ⟨hξ, hξp, a, b, hab⟩ ⟨hη, hηp, a', b', hab'⟩
    refine ⟨hξ.add hη, fun s t ↦ by simp [hξp, hηp], min a a', max b b', fun s t hs ↦ ?_⟩
    have h₁ : s ∉ Ioo a b := fun h ↦ hs ⟨(min_le_left _ _).trans_lt h.1,
      h.2.trans_le (le_max_left _ _)⟩
    have h₂ : s ∉ Ioo a' b' := fun h ↦ hs ⟨(min_le_right _ _).trans_lt h.1,
      h.2.trans_le (le_max_right _ _)⟩
    simp [hab s t h₁, hab' s t h₂]
  zero_mem' := ⟨contDiff_const, fun _ _ ↦ rfl, 0, 0, fun _ _ _ ↦ rfl⟩
  smul_mem' := by
    rintro c ξ ⟨hξ, hξp, a, b, hab⟩
    exact ⟨hξ.const_smul c, fun s t ↦ by simp [hξp], a, b, fun s t hs ↦ by simp [hab s t hs]⟩

variable {V}

theorem mem_testSections {ξ : ℝ × ℝ → V} :
    ξ ∈ testSections V ↔ ContDiff ℝ 2 ξ ∧ (∀ s t, ξ (s, t + 1) = ξ (s, t)) ∧
      ∃ a b : ℝ, ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0 :=
  Iff.rfl

theorem contDiff_of_mem_testSections {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSections V) :
    ContDiff ℝ 2 ξ :=
  hξ.1

theorem periodic_of_mem_testSections {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSections V) (s t : ℝ) :
    ξ (s, t + 1) = ξ (s, t) :=
  hξ.2.1 s t

theorem exists_forall_notMem_Ioo_of_mem_testSections {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSections V) :
    ∃ a b : ℝ, ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0 :=
  hξ.2.2

variable (V) in
/-- The fibre `V³` of first-order jets `(ξ, ∂ₛ ξ, ∂ₜ ξ)`, with the Euclidean combination
`‖(a, b, c)‖² = ‖a‖² + ‖b‖² + ‖c‖²` of the norms. -/
abbrev Jet : Type _ :=
  PiLp 2 fun _ : Fin 3 ↦ V

/-- The first-order jet `(ξ z, ∂ₛ ξ z, ∂ₜ ξ z)` of a map `ξ : ℝ × ℝ → V` at `z`. -/
def jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : Jet V :=
  WithLp.toLp 2 ![ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)]

@[simp]
theorem jet_apply_zero (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : jet ξ z 0 = ξ z :=
  (rfl)

@[simp]
theorem jet_apply_one (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : jet ξ z 1 = fderiv ℝ ξ z (1, 0) :=
  (rfl)

@[simp]
theorem jet_apply_two (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : jet ξ z 2 = fderiv ℝ ξ z (0, 1) :=
  (rfl)

/-- The squared norm of a jet is `‖∂ₛ ξ‖² + ‖∂ₜ ξ‖² + ‖ξ‖²`. -/
theorem norm_jet_sq (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖jet ξ z‖ ^ 2 = ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, jet_apply_zero, jet_apply_one, jet_apply_two]
  ring

theorem norm_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : ‖ξ z‖ ≤ ‖jet ξ z‖ :=
  PiLp.norm_apply_le (jet ξ z) 0

theorem norm_fderiv_apply_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z (1, 0)‖ ≤ ‖jet ξ z‖ :=
  PiLp.norm_apply_le (jet ξ z) 1

theorem norm_fderiv_apply_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖fderiv ℝ ξ z (0, 1)‖ ≤ ‖jet ξ z‖ :=
  PiLp.norm_apply_le (jet ξ z) 2

theorem continuous_jet {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) : Continuous (jet ξ) := by
  have hd := hξ.continuous_fderiv one_ne_zero
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i
  · exact hξ.continuous
  · exact hd.clm_apply continuous_const
  · exact hd.clm_apply continuous_const

theorem jet_add {ξ η : ℝ × ℝ → V} {z : ℝ × ℝ} (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) : jet (ξ + η) z = jet ξ z + jet η z := by
  ext i
  fin_cases i <;> simp [fderiv_add hξ hη]

theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : jet (c • ξ) z = c • jet ξ z := by
  ext i
  fin_cases i <;> simp [fderiv_const_smul_field c]

/-- A continuous map of period one in `t` that vanishes for `s` outside a bounded interval is in
`Lᵖ` of the fundamental domain. -/
theorem memLp_stripMeasure {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) {a b : ℝ} (hab : ∀ s t, s ∉ Ioo a b → f (s, t) = 0) (p : ℝ≥0∞) :
    MemLp f p (stripMeasure) := by
  set K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have heq : f =ᵐ[stripMeasure] K.indicator f := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ ?_
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
    · rw [indicator_of_notMem hzK]
      exact hab z.1 z.2 fun h ↦ hzK ⟨Ioo_subset_Icc_self h, hz.2⟩
  refine (memLp_congr_ae heq).2
    ((memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2 ?_)
  have : IsFiniteMeasure ((stripMeasure).restrict K) :=
    isFiniteMeasure_restrict.2 ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_restrict_of_forall_mem hK.measurableSet hC)


theorem memLp_jet {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSections V) (p : ℝ≥0∞) :
    MemLp (jet ξ) p (stripMeasure) := by
  obtain ⟨a, b, hab⟩ := exists_forall_notMem_Ioo_of_mem_testSections hξ
  refine memLp_stripMeasure (continuous_jet ((contDiff_of_mem_testSections hξ).of_le
    (by norm_num))) (a := a - 1) (b := b + 1) (fun s t hs ↦ ?_) p
  have h : ξ =ᶠ[𝓝 (s, t)] 0 := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hab
    fun h ↦ hs ⟨by linarith [h.1], by linarith [h.2]⟩
  ext i
  fin_cases i <;> simp [h.fderiv_eq, h.eq_of_nhds]

variable (V) in
/-- The jets of test sections, as square integrable functions on the fundamental domain. -/
def jetLp : testSections V →ₗ[ℝ] Lp (Jet V) 2 (stripMeasure) where
  toFun ξ := (memLp_jet ξ.2 2).toLp (jet ξ)
  map_add' ξ η := by
    have hξ := (contDiff_of_mem_testSections ξ.2).differentiable two_ne_zero
    have hη := (contDiff_of_mem_testSections η.2).differentiable two_ne_zero
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ jet_add (hξ z) (hη z))
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by
      simpa only [Submodule.coe_smul, Pi.smul_apply] using jet_smul c (ξ : ℝ × ℝ → V) z)

theorem jetLp_apply (ξ : testSections V) : jetLp V ξ = (memLp_jet ξ.2 2).toLp (jet ξ) :=
  (rfl)

theorem coeFn_jetLp (ξ : testSections V) : jetLp V ξ =ᵐ[stripMeasure] jet ξ :=
  (memLp_jet ξ.2 2).coeFn_toLp

variable (V) in
/-- The Sobolev space `W^{1,2}` of sections of the cylinder `ℝ × (ℝ / ℤ)` with values in `V`: the
closure in `L²(ℝ × [0, 1], V³)` of the jets `(ξ, ∂ₛ ξ, ∂ₜ ξ)` of test sections. -/
def W12 : Submodule ℝ (Lp (Jet V) 2 (stripMeasure)) :=
  (LinearMap.range (jetLp V)).topologicalClosure

instance [CompleteSpace V] : CompleteSpace (W12 V) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

variable (V) in
/-- A test section as an element of `W^{1,2}`. -/
def toW12 : testSections V →ₗ[ℝ] W12 V :=
  (jetLp V).codRestrict (W12 V) fun ξ ↦
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (jetLp V) ξ)

@[simp]
theorem coe_toW12 (ξ : testSections V) : (toW12 V ξ : Lp (Jet V) 2 (stripMeasure)) = jetLp V ξ :=
  (rfl)

/-- The test sections are dense in `W^{1,2}`. -/
theorem denseRange_toW12 : DenseRange (toW12 V) := by
  have h : Subtype.val ∘ toW12 V = jetLp V := funext coe_toW12
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  simp only [W12, Submodule.topologicalClosure_coe, LinearMap.coe_range]
  exact (congrArg (closure ∘ range) h).symm.subset

/-- **The `W^{1,2}` norm of a test section.** -/
theorem norm_toW12_sq (ξ : testSections V) :
    ‖toW12 V ξ‖ ^ 2 = ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
      (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 + ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 +
        ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) := by
  rw [← Submodule.norm_coe, coe_toW12, jetLp_apply, MemLp.norm_toLp_sq]
  simp only [norm_jet_sq]

variable (V) in
/-- The value of an element of `W^{1,2}`, as a function in `L²(ℝ × [0, 1], V)`. -/
def valueL : W12 V →L[ℝ] Lp V 2 (stripMeasure) :=
  ((PiLp.proj 2 (fun _ : Fin 3 ↦ V) 0 : Jet V →L[ℝ] V).compLpL 2 (stripMeasure)).comp
    (W12 V).subtypeL

theorem coeFn_valueL_toW12 (ξ : testSections V) :
    valueL V (toW12 V ξ) =ᵐ[stripMeasure] ξ := by
  have h := (PiLp.proj 2 (fun _ : Fin 3 ↦ V) 0 : Jet V →L[ℝ] V).coeFn_compLpL (jetLp V ξ)
  filter_upwards [h, coeFn_jetLp ξ] with z hz hz'
  simp [valueL, hz, hz']

variable (V) in
/-- The restriction of the value of an element of `W^{1,2}` to the finite cylinder
`[-T, T] × [0, 1]`. -/
def restrictValue (T : ℝ) :
    W12 V →L[ℝ] Lp V 2 ((stripMeasure).restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1)) :=
  (LpToLpRestrictCLM (ℝ × ℝ) V ℝ (stripMeasure) 2 (Icc (-T) T ×ˢ Icc (0 : ℝ) 1)).comp (valueL V)

theorem coeFn_restrictValue_toW12 (T : ℝ) (ξ : testSections V) :
    restrictValue V T (toW12 V ξ) =ᵐ[(stripMeasure).restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1)]
      ξ := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) (valueL V (toW12 V ξ)),
    ae_restrict_of_ae (coeFn_valueL_toW12 ξ)] with z hz hz'
  rw [restrictValue, ContinuousLinearMap.comp_apply, hz, hz']

/-- **The `L²` norm of the restriction of a test section to `[-T, T] × [0, 1]`.** -/
theorem norm_restrictValue_toW12_sq (T : ℝ) (ξ : testSections V) :
    ‖restrictValue V T (toW12 V ξ)‖ ^ 2 =
      ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  rw [integral_congr_ae ((coeFn_restrictValue_toW12 T ξ).mono fun z hz ↦ by rw [hz])]
  rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc)]
  congr 2
  ext z
  simp only [mem_inter_iff, mem_prod, mem_univ, true_and]
  tauto


/-! ### Compactness of restriction to a finite cylinder -/

/-- Lebesgue measure on `ℝ × ℝ` is invariant under translations. -/
private theorem isAddRightInvariant_volume_prod :
    (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- For a function of period `k` in `t`, the integral over `ℝ × [k, k + 1]` is the integral over
the fundamental domain. -/
private theorem setLIntegral_univ_prod_Icc_add_eq {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) (k : ℝ)
    (hk : ∀ s t, F (s, t + k) = F (s, t)) :
    ∫⁻ z in univ ×ˢ Icc k (k + 1), F z = ∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, F z := by
  have hpre : (· + ((0 : ℝ), k)) ⁻¹' (univ ×ˢ Icc k (k + 1)) = univ ×ˢ Icc (0 : ℝ) 1 := by
    ext z
    simp [add_comm k]
  have := isAddRightInvariant_volume_prod
  have hmp := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) ((0 : ℝ), k)
  rw [← hmp.setLIntegral_comp_preimage (MeasurableSet.univ.prod measurableSet_Icc) hF, hpre]
  refine setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc) fun z _ ↦ ?_
  obtain ⟨s, t⟩ := z
  simpa using hk s t

/-- For a function of period one in `t`, the integral over `ℝ × [-1, 2]` is at most three times
the integral over the fundamental domain. -/
private theorem setLIntegral_univ_prod_Icc_neg_one_two_le {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hper : ∀ s t, F (s, t + 1) = F (s, t)) :
    ∫⁻ z in univ ×ˢ Icc (-1 : ℝ) 2, F z ≤ 3 * ∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, F z := by
  have hsub : (univ : Set ℝ) ×ˢ Icc (-1 : ℝ) 2 ⊆ ((univ : Set ℝ) ×ˢ Icc (-1 : ℝ) (-1 + 1) ∪
      (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1) ∪ (univ : Set ℝ) ×ˢ Icc (1 : ℝ) (1 + 1) := by
    rintro ⟨s, t⟩ ⟨-, ht₁, ht₂⟩
    simp only [mem_union, mem_prod, mem_univ, mem_Icc, true_and]
    by_cases h₀ : t ≤ 0
    · exact Or.inl (Or.inl ⟨ht₁, by linarith⟩)
    by_cases h₁ : t ≤ 1
    · exact Or.inl (Or.inr ⟨by linarith, h₁⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hm : ∀ s t, F (s, t + -1) = F (s, t) := fun s t ↦ by
    simpa using (hper s (t + -1)).symm
  calc ∫⁻ z in univ ×ˢ Icc (-1 : ℝ) 2, F z
      ≤ ∫⁻ z in (univ ×ˢ Icc (-1 : ℝ) (-1 + 1) ∪ univ ×ˢ Icc (0 : ℝ) 1) ∪
          univ ×ˢ Icc (1 : ℝ) (1 + 1), F z := lintegral_mono_set hsub
    _ ≤ ((∫⁻ z in univ ×ˢ Icc (-1 : ℝ) (-1 + 1), F z) + ∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, F z) +
          ∫⁻ z in univ ×ˢ Icc (1 : ℝ) (1 + 1), F z :=
        (lintegral_union_le _ _ _).trans (add_le_add_left (lintegral_union_le _ _ _) _)
    _ = 3 * ∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, F z := by
        have h₁ := setLIntegral_univ_prod_Icc_add_eq hF (-1) hm
        have h₂ := setLIntegral_univ_prod_Icc_add_eq hF 1 hper
        rw [h₁, h₂]
        ring

/-- For a continuous function of period one in `t`, the `L²` norm over `ℝ × [-1, 2]` is at most
three times the `L²` norm over the fundamental domain. -/
private theorem eLpNorm_restrict_univ_prod_Icc_neg_one_two_le {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × ℝ → E} (hf : Continuous f) (hper : ∀ s t, f (s, t + 1) = f (s, t)) :
    eLpNorm f 2 (volume.restrict (univ ×ˢ Icc (-1 : ℝ) 2)) ≤ 3 * eLpNorm f 2 (stripMeasure) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  have hmeas : Measurable fun z ↦ ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal :=
    (hf.eNorm.measurable).pow_const _
  calc (∫⁻ z in univ ×ˢ Icc (-1 : ℝ) 2, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
      ≤ (3 * ∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) :=
        ENNReal.rpow_le_rpow (setLIntegral_univ_prod_Icc_neg_one_two_le hmeas fun s t ↦ by
          rw [hper]) (by positivity)
    _ = 3 ^ (1 / (2 : ℝ≥0∞).toReal) *
          (∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
            (1 / (2 : ℝ≥0∞).toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ 3 * (∫⁻ z in univ ×ˢ Icc (0 : ℝ) 1, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
            (1 / (2 : ℝ≥0∞).toReal) := by
        gcongr
        calc (3 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) ≤ 3 ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 3 := ENNReal.rpow_one 3

/-- The bump in `s`: equal to `1` on `[-|T| - 1, |T| + 1]` and supported in
`(-|T| - 2, |T| + 2)`. -/
private def sBump (T : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨|T| + 1, |T| + 2, by positivity, by linarith⟩

/-- The bump in `t`: equal to `1` on `[-1/2, 3/2]` and supported in `(-1, 2)`. -/
private def tBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1, 3 / 2, one_pos, by norm_num⟩

/-- The cutoff `β(s, t)`, equal to `1` on `[-T, T] × [0, 1]` and supported in the bounded set
`[-|T| - 2, |T| + 2] × [-1, 2]`. -/
private def cutoff (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  sBump T z.1 * tBump z.2

private theorem contDiff_cutoff (T : ℝ) : ContDiff ℝ 2 (cutoff T) :=
  ((sBump T).contDiff.comp contDiff_fst).mul (tBump.contDiff.comp contDiff_snd)

private theorem abs_cutoff_le_one (T : ℝ) (z : ℝ × ℝ) : |cutoff T z| ≤ 1 := by
  rw [cutoff, abs_mul, abs_of_nonneg (sBump T).nonneg, abs_of_nonneg tBump.nonneg]
  exact (mul_le_mul (sBump T).le_one tBump.le_one tBump.nonneg zero_le_one).trans_eq (one_mul 1)

private theorem cutoff_eq_one {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ Icc (-T) T ×ˢ Icc (0 : ℝ) 1) :
    cutoff T z = 1 := by
  obtain ⟨⟨hs₁, hs₂⟩, ht₁, ht₂⟩ := hz
  have h₁ : sBump T z.1 = 1 := (sBump T).one_of_mem_closedBall <| by
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    change |z.1| ≤ |T| + 1
    rw [abs_le]
    constructor <;> linarith [neg_abs_le T, le_abs_self T]
  have h₂ : tBump z.2 = 1 := tBump.one_of_mem_closedBall <| by
    rw [mem_closedBall, Real.dist_eq]
    change |z.2 - 1 / 2| ≤ 1
    rw [abs_le]
    constructor <;> linarith
  rw [cutoff, h₁, h₂, one_mul]

/-- The bounded set `[-|T| - 2, |T| + 2] × [-1, 2]` outside which the cutoff vanishes. -/
private def cutoffBox (T : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(|T| + 2)) (|T| + 2) ×ˢ Icc (-1 : ℝ) 2

private theorem cutoff_eq_zero {T : ℝ} {z : ℝ × ℝ} (hz : z ∉ cutoffBox T) : cutoff T z = 0 := by
  by_contra h
  have h₁ : sBump T z.1 ≠ 0 := left_ne_zero_of_mul h
  have h₂ : tBump z.2 ≠ 0 := right_ne_zero_of_mul h
  rw [← mem_support, (sBump T).support_eq, mem_ball, Real.dist_eq, sub_zero] at h₁
  rw [← mem_support, tBump.support_eq, mem_ball, Real.dist_eq] at h₂
  change |z.1| < |T| + 2 at h₁
  change |z.2 - 1 / 2| < 3 / 2 at h₂
  rw [abs_lt] at h₁ h₂
  exact hz ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The cutoff vanishes near every point whose `t`-coordinate lies outside `[-1, 2]`. -/
private theorem cutoff_eventuallyEq_zero {T : ℝ} {z : ℝ × ℝ} (hz : z.2 ∉ Icc (-1 : ℝ) 2) :
    cutoff T =ᶠ[𝓝 z] 0 := by
  have hopen : IsOpen {w : ℝ × ℝ | w.2 ∉ Icc (-1 : ℝ) 2} :=
    isClosed_Icc.isOpen_compl.preimage continuous_snd
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact cutoff_eq_zero fun h ↦ hw h.2

private theorem isCompact_cutoffBox (T : ℝ) : IsCompact (cutoffBox T) :=
  isCompact_Icc.prod isCompact_Icc

private theorem hasCompactSupport_cutoff (T : ℝ) : HasCompactSupport (cutoff T) :=
  HasCompactSupport.intro (isCompact_cutoffBox T) fun _ hz ↦ cutoff_eq_zero hz

private theorem exists_forall_norm_fderiv_cutoff_le (T : ℝ) :
    ∃ M, ∀ z, ‖fderiv ℝ (cutoff T) z‖ ≤ M :=
  ((contDiff_cutoff T).continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    ((hasCompactSupport_cutoff T).fderiv (𝕜 := ℝ))


/-- The jet of a map of period one in `t` has period one in `t`. -/
private theorem jet_periodic {ξ : ℝ × ℝ → V} (hξ : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (s t : ℝ) :
    jet ξ (s, t + 1) = jet ξ (s, t) := by
  have hcomp : (fun z : ℝ × ℝ ↦ ξ (z + (0, 1))) = ξ := funext fun ⟨a, b⟩ ↦ by
    simpa using hξ a b
  have hd : fderiv ℝ ξ (s, t + 1) = fderiv ℝ ξ (s, t) := by
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := ξ) (x := (s, t)) ((0 : ℝ), (1 : ℝ))
    rw [hcomp] at h
    simpa using h.symm
  ext i
  fin_cases i <;> simp [hξ, hd]

/-- The `L²` norm of the jet of a test section is its `W^{1,2}` norm. -/
private theorem eLpNorm_jet_eq (ξ : testSections V) :
    eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 (stripMeasure) = ENNReal.ofReal ‖toW12 V ξ‖ := by
  rw [← Submodule.norm_coe, coe_toW12, jetLp_apply, Lp.norm_toLp,
    ENNReal.ofReal_toReal (memLp_jet ξ.2 2).eLpNorm_ne_top]

/-- The cut-off section `β ξ` of a map `ξ`, for the cutoff `β` of `[-T, T] × [0, 1]`. -/
private def cutoffSection (T : ℝ) (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  cutoff T z • ξ z

private theorem contDiff_cutoffSection (T : ℝ) (ξ : testSections V) :
    ContDiff ℝ 2 (cutoffSection T (ξ : ℝ × ℝ → V)) :=
  (contDiff_cutoff T).smul (contDiff_of_mem_testSections ξ.2)

private theorem cutoffSection_eq_zero {T : ℝ} (ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    (hz : z ∉ cutoffBox T) : cutoffSection T ξ z = 0 := by
  simp [cutoffSection, cutoff_eq_zero hz]

private theorem memLp_cutoffSection (T : ℝ) (ξ : testSections V) :
    MemLp (cutoffSection T (ξ : ℝ × ℝ → V)) 2 volume :=
  (contDiff_cutoffSection T ξ).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_cutoffBox T) fun _ hz ↦ cutoffSection_eq_zero _ hz)

/-- The cut-off section vanishes where `t ∉ [-1, 2]`. -/
private theorem support_cutoffSection_subset (T : ℝ) (ξ : ℝ × ℝ → V) :
    support (cutoffSection T ξ) ⊆ univ ×ˢ Icc (-1 : ℝ) 2 := fun _ hz ↦
  ⟨mem_univ _, by_contra fun h ↦ hz (cutoffSection_eq_zero ξ fun hb ↦ h hb.2)⟩

/-- The derivative of the cut-off section vanishes where `t ∉ [-1, 2]`. -/
private theorem support_fderiv_cutoffSection_subset (T : ℝ) (ξ : ℝ × ℝ → V) :
    support (fderiv ℝ (cutoffSection T ξ)) ⊆ univ ×ˢ Icc (-1 : ℝ) 2 := by
  intro z hz
  refine ⟨mem_univ _, by_contra fun h ↦ hz ?_⟩
  have hz' : cutoffSection T ξ =ᶠ[𝓝 z] 0 := by
    filter_upwards [cutoff_eventuallyEq_zero (T := T) h] with w hw
    simp [cutoffSection, hw]
  rw [hz'.fderiv_eq, fderiv_zero, Pi.zero_apply]

/-- The `L²` norm of the jet of a test section over `ℝ × [-1, 2]` is at most three times its
`W^{1,2}` norm. -/
private theorem eLpNorm_jet_restrict_le (ξ : testSections V) :
    eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 (volume.restrict (univ ×ˢ Icc (-1 : ℝ) 2)) ≤
      3 * ENNReal.ofReal ‖toW12 V ξ‖ := by
  rw [← eLpNorm_jet_eq]
  exact eLpNorm_restrict_univ_prod_Icc_neg_one_two_le
    (continuous_jet ((contDiff_of_mem_testSections ξ.2).of_le (by norm_num)))
    (jet_periodic (periodic_of_mem_testSections ξ.2))

/-- The `L²` norm of the cut-off section on the plane is at most three times the `W^{1,2}` norm. -/
private theorem eLpNorm_cutoffSection_le (T : ℝ) (ξ : testSections V) :
    eLpNorm (cutoffSection T (ξ : ℝ × ℝ → V)) 2 volume ≤ 3 * ENNReal.ofReal ‖toW12 V ξ‖ := by
  rw [← eLpNorm_restrict_eq_of_support_subset (memLp_cutoffSection T ξ).aestronglyMeasurable
    (support_cutoffSection_subset T _)]
  refine (eLpNorm_mono (memLp_cutoffSection T ξ).aestronglyMeasurable.restrict fun z ↦ ?_).trans
    (eLpNorm_jet_restrict_le ξ)
  rw [cutoffSection, norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (abs_cutoff_le_one T z)).trans
    (norm_le_norm_jet _ z)

/-- The pointwise bound `‖D(β ξ)‖ ≤ (2 + M) ‖jet ξ‖` for a cutoff with `‖Dβ‖ ≤ M`. -/
private theorem norm_fderiv_cutoffSection_le {T M : ℝ} (hM : ∀ z, ‖fderiv ℝ (cutoff T) z‖ ≤ M)
    (ξ : testSections V) (z : ℝ × ℝ) :
    ‖fderiv ℝ (cutoffSection T (ξ : ℝ × ℝ → V)) z‖ ≤ (2 + M) * ‖jet (ξ : ℝ × ℝ → V) z‖ := by
  have hξd := (contDiff_of_mem_testSections ξ.2).differentiable two_ne_zero
  have hcd := (contDiff_cutoff T).differentiable two_ne_zero
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM z)
  have hfd : ‖fderiv ℝ (ξ : ℝ × ℝ → V) z‖ ≤ 2 * ‖jet (ξ : ℝ × ℝ → V) z‖ :=
    (ContinuousLinearMap.opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one _).trans (by
      linarith [norm_fderiv_apply_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) z,
        norm_fderiv_apply_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) z])
  have hcs : cutoffSection T (ξ : ℝ × ℝ → V) = fun y ↦ cutoff T y • (ξ : ℝ × ℝ → V) y := rfl
  rw [hcs, fderiv_fun_smul (hcd z) (hξd z)]
  calc ‖cutoff T z • fderiv ℝ (ξ : ℝ × ℝ → V) z +
        (fderiv ℝ (cutoff T) z).smulRight ((ξ : ℝ × ℝ → V) z)‖
      ≤ |cutoff T z| * ‖fderiv ℝ (ξ : ℝ × ℝ → V) z‖ +
          ‖fderiv ℝ (cutoff T) z‖ * ‖(ξ : ℝ × ℝ → V) z‖ :=
        (norm_add_le _ _).trans (by
          rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply])
    _ ≤ 1 * (2 * ‖jet (ξ : ℝ × ℝ → V) z‖) + M * ‖jet (ξ : ℝ × ℝ → V) z‖ := by
        gcongr
        · exact abs_cutoff_le_one T z
        · exact hM z
        · exact norm_le_norm_jet _ z
    _ = (2 + M) * ‖jet (ξ : ℝ × ℝ → V) z‖ := by ring

/-- The `L²` norm on the plane of the derivative of the cut-off section is bounded by the `W^{1,2}`
norm. -/
private theorem eLpNorm_fderiv_cutoffSection_le {T M : ℝ}
    (hM : ∀ z, ‖fderiv ℝ (cutoff T) z‖ ≤ M) (ξ : testSections V) :
    eLpNorm (fderiv ℝ (cutoffSection T (ξ : ℝ × ℝ → V))) 2 volume ≤
      ENNReal.ofReal (2 + M) * (3 * ENNReal.ofReal ‖toW12 V ξ‖) := by
  have hcont := (contDiff_cutoffSection T ξ).continuous_fderiv two_ne_zero
  rw [← eLpNorm_restrict_eq_of_support_subset hcont.aestronglyMeasurable
    (support_fderiv_cutoffSection_subset T _)]
  exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hcont.aestronglyMeasurable
    (ae_of_all _ (norm_fderiv_cutoffSection_le hM ξ)) 2).trans
    (by gcongr; exact eLpNorm_jet_restrict_le ξ)

/-- The translates of the cut-off sections of test sections of norm less than one move in `L²`
uniformly little under small translations. -/
private theorem exists_pos_forall_eLpNorm_cutoffSection_comp_add_sub_le (T : ℝ) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ δ > 0, ∀ ξ : testSections V, ‖toW12 V ξ‖ < 1 → ∀ h : ℝ × ℝ, ‖h‖ < δ →
      eLpNorm (fun x ↦ cutoffSection T (ξ : ℝ × ℝ → V) (x + h) -
        cutoffSection T (ξ : ℝ × ℝ → V) x) 2 volume ≤ ε := by
  have := isAddRightInvariant_volume_prod
  obtain ⟨M, hM⟩ := exists_forall_norm_fderiv_cutoff_le T
  -- `‖h‖ₑ * C` is small for small `h`.
  set C : ℝ≥0∞ := ENNReal.ofReal (2 + M) * 3
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have ht : Tendsto (fun h : ℝ × ℝ ↦ ‖h‖ₑ * C) (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun h : ℝ × ℝ ↦ ‖h‖ₑ) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_eNorm (E := ℝ × ℝ)).tendsto 0
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hC)
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 ((tendsto_order.1 ht).2 ε hε)
  refine ⟨δ, hδ, fun ξ hξ h hh ↦ ?_⟩
  have hc := (contDiff_cutoffSection T ξ).of_le (m := 1) (by norm_num)
  refine (hc.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv (by norm_num) h).trans ?_
  calc ‖h‖ₑ * eLpNorm (fderiv ℝ (cutoffSection T (ξ : ℝ × ℝ → V))) 2 volume
      ≤ ‖h‖ₑ * (ENNReal.ofReal (2 + M) * (3 * 1)) := by
        gcongr
        exact (eLpNorm_fderiv_cutoffSection_le hM ξ).trans
          (by gcongr; exact ENNReal.ofReal_le_one.2 hξ.le)
    _ = ‖h‖ₑ * C := by rw [mul_one]
    _ ≤ ε := (hδε (by simpa using hh)).le

/-- **The cut-off sections of norm less than one form a totally bounded set of `L²(ℝ²)`**, by the
Fréchet–Kolmogorov criterion: they are bounded in `L²`, supported in a fixed bounded set, and their
translates move at most linearly in the translation. -/
private theorem totallyBounded_cutoffSection [FiniteDimensional ℝ V] (T : ℝ) :
    TotallyBounded ((fun ξ : testSections V ↦ (memLp_cutoffSection T ξ).toLp _) ''
      {ξ | ‖toW12 V ξ‖ < 1}) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl ENNReal.ofNat_ne_top
    (isCompact_cutoffBox T).isBounded ?_ (M := 3) (by norm_num) ?_ ?_
  · rintro _ ⟨ξ, -, rfl⟩
    filter_upwards [(memLp_cutoffSection T ξ).coeFn_toLp] with z hz hzB
    rw [hz, cutoffSection_eq_zero _ hzB]
  · rintro _ ⟨ξ, hξ, rfl⟩
    rw [eLpNorm_congr_ae (memLp_cutoffSection T ξ).coeFn_toLp]
    calc eLpNorm (cutoffSection T (ξ : ℝ × ℝ → V)) 2 volume
        ≤ 3 * ENNReal.ofReal ‖toW12 V ξ‖ := eLpNorm_cutoffSection_le T ξ
      _ ≤ 3 * 1 := by gcongr; exact ENNReal.ofReal_le_one.2 (le_of_lt hξ)
      _ = 3 := mul_one 3
  · intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_pos_forall_eLpNorm_cutoffSection_comp_add_sub_le (V := V) T hε
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨ξ, hξ, rfl⟩ h hh
    -- The translation increments of the class are those of the function.
    have := isAddRightInvariant_volume_prod
    have hL := (memLp_cutoffSection T ξ).coeFn_toLp
    refine le_of_eq_of_le (eLpNorm_congr_ae ?_) (hδε ξ hξ h hh)
    filter_upwards [(measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hL,
      hL] with x hx hx'
    simp only [Function.comp_apply] at hx
    rw [hx, hx']

/-- Restricting the cut-off section of a test section to `[-T, T] × [0, 1]` gives its restricted
value. -/
private theorem restrictValue_toW12_eq (T : ℝ) (ξ : testSections V) :
    restrictValue V T (toW12 V ξ) =
      ((LpToLpRestrictCLM (ℝ × ℝ) V ℝ (stripMeasure) 2 (Icc (-T) T ×ˢ Icc (0 : ℝ) 1)).comp
        (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc (0 : ℝ) 1)))
        ((memLp_cutoffSection T ξ).toLp _) := by
  have hR : MeasurableSet (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  refine Lp.ext ?_
  filter_upwards [coeFn_restrictValue_toW12 T ξ,
    LpToLpRestrictCLM_coeFn ℝ (Icc (-T) T ×ˢ Icc (0 : ℝ) 1)
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc (0 : ℝ) 1)
        ((memLp_cutoffSection T ξ).toLp _)),
    ae_restrict_of_ae (LpToLpRestrictCLM_coeFn ℝ (univ ×ˢ Icc (0 : ℝ) 1)
      ((memLp_cutoffSection T ξ).toLp (cutoffSection T (ξ : ℝ × ℝ → V)))),
    ae_restrict_of_ae (ae_restrict_of_ae (memLp_cutoffSection T ξ).coeFn_toLp),
    ae_restrict_mem hR] with z h₁ h₂ h₃ h₄ hz
  rw [h₁, ContinuousLinearMap.comp_apply, h₂, h₃, h₄]
  simp [cutoffSection, cutoff_eq_one hz]

/-- **Rellich's theorem on the cylinder.** For finite-dimensional `V`, restricting the value of an
element of `W^{1,2}(ℝ × S¹, V)` to the finite cylinder `[-T, T] × [0, 1]` is a compact operator
into `L²`. -/
theorem isCompactOperator_restrictValue [FiniteDimensional ℝ V] (T : ℝ) :
    IsCompactOperator (restrictValue V T) := by
  set Φ := (LpToLpRestrictCLM (ℝ × ℝ) V ℝ (stripMeasure) 2 (Icc (-T) T ×ˢ Icc (0 : ℝ) 1)).comp
    (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc (0 : ℝ) 1))
  set A := (fun ξ : testSections V ↦ (memLp_cutoffSection T ξ).toLp _) '' {ξ | ‖toW12 V ξ‖ < 1}
  -- The restricted values of test sections of norm less than one lie in the totally bounded
  -- image `Φ '' A`, and these test sections are dense in the unit ball.
  refine ⟨closure (Φ '' A), isCompact_iff_totallyBounded_isComplete.2
    ⟨((totallyBounded_cutoffSection T).image Φ.uniformContinuous).closure,
      isClosed_closure.isComplete⟩, ?_⟩
  refine mem_of_superset (ball_mem_nhds 0 one_pos) fun x hx ↦ ?_
  have hx' : x ∈ closure (ball 0 1 ∩ range (toW12 V)) :=
    denseRange_toW12.open_subset_closure_inter isOpen_ball hx
  have hsub : restrictValue V T '' (ball 0 1 ∩ range (toW12 V)) ⊆ Φ '' A := by
    rintro _ ⟨_, ⟨hy, ξ, rfl⟩, rfl⟩
    exact ⟨_, ⟨ξ, by simpa using hy, rfl⟩, (restrictValue_toW12_eq T ξ).symm⟩
  exact closure_mono hsub
    (image_closure_subset_closure_image (restrictValue V T).continuous (mem_image_of_mem _ hx'))

end TauCeti.CylinderSobolev
