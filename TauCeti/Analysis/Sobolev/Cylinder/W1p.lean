/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Sobolev.Cylinder.Morrey
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Sobolev spaces `W^{1,p}` of the cylinder and their Sobolev embedding for `p > 2`

Let `V` be a real normed space. Sections of the trivial bundle with fibre `V` over the cylinder
`ℝ × S¹` are maps `ξ : ℝ × ℝ → V` of period one in `t`, and the test sections
`TauCeti.CylinderSobolev.testSection` are the `C²` ones vanishing for `|s|` large. For
`1 ≤ p < ∞` the Sobolev space `W^{1,p}(ℝ × S¹, V)` is the completion of the test sections in the
`W^{1,p}` norm, realized inside `Lᵖ(ℝ × [0, 1], V × V × V)` as the closure of their `Lᵖ` jets
`(ξ, ∂s ξ, ∂t ξ)` (`TauCeti.CylinderSobolev.W1p`, the construction
`TauCeti.StripSobolev.jetClosure`); for `p = 2` it is `TauCeti.CylinderSobolev.H1`. This file
packages the jets of test sections as elements of `W^{1,p}`
(`TauCeti.CylinderSobolev.toW1p`), which are dense. The norm is computed on the strip
`ℝ × [0, 1]`, a fundamental domain of the cylinder, and does not single out a compact piece of
it: translation along the cylinder, `TauCeti.StripSobolev.translate p (testSection V) a`, is a
linear isometric equivalence of `W^{1,p}`, and it sends the jet of a test section to the jet of
its translate (`TauCeti.CylinderSobolev.translate_toW1p`).

Since the cylinder has dimension two, for `p > 2` Morrey's estimate
(`TauCeti.CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet`) bounds a test section pointwise by the
`Lᵖ` norm of its jet. A test section is a bounded continuous function on `ℝ × ℝ`
(`TauCeti.CylinderSobolev.testSectionToBCF`), so the estimate extends the inclusion of the test
sections to a continuous linear map

`TauCeti.CylinderSobolev.continuousValue p : W^{1,p}(ℝ × S¹, V) →L[ℝ] (ℝ × ℝ →ᵇ V)`,

the **Sobolev embedding** `W^{1,p} ⊂ C⁰_b`. It sends the jet of a test section to the section itself
(`TauCeti.CylinderSobolev.coe_continuousValue_toW1p`), and it is the continuous representative of
the value of every element: the value `ξ` of an `Lᵖ` jet `(ξ, ξ_s, ξ_t) ∈ W^{1,p}`
(`TauCeti.CylinderSobolev.valueL`) agrees almost everywhere on the strip with
`continuousValue p` of it (`TauCeti.CylinderSobolev.valueL_ae_eq_continuousValue`). The
continuous representative is a section of the cylinder, of period one in `t`
(`TauCeti.CylinderSobolev.continuousValue_add_one`), it commutes with translation
(`TauCeti.CylinderSobolev.continuousValue_translate`), and it tends to zero along both ends,
uniformly in `t` (`TauCeti.CylinderSobolev.tendsto_continuousValue_comap_fst_cocompact`). In
particular a nonzero constant section, although bounded with vanishing derivative, is the
continuous representative of no element of `W^{1,p}`. Since `continuousValue p` is continuous,
convergence in `W^{1,p}` implies uniform convergence of the continuous representatives.

This is the setting of the nonlinear Floer operator on increments of a map of the cylinder: for
`p > 2` an element of `W^{1,p}` is a continuous section, so it can be inserted into the nonlinear
coefficients `J(u)` and `X_K(u)`, and the quadratic estimate for the Floer operator
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_jet`, in
the namespace `TauCeti.SymplecticForm`) is stated with the `Lᵖ` norms of jets, which are the
norms of test sections in `W^{1,p}`
(`TauCeti.CylinderSobolev.norm_toW1p`). For `p ≤ 2` Morrey's estimate fails, and
`continuousValue p` is `0` by the convention of `LinearMap.extendOfNorm`.

## Main definitions

* `TauCeti.CylinderSobolev.toW1p p`: the jet of a test section, as an element of `W1p V p`.
* `TauCeti.CylinderSobolev.testSectionToBCF`: a test section as a bounded continuous function.
* `TauCeti.CylinderSobolev.continuousValue p`: the Sobolev embedding `W^{1,p} ⊂ C⁰_b`, `p > 2`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4 (Morrey's inequality) and
  §5.6.3 (the general Sobolev inequalities).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.1,
  on the Sobolev embedding `W^{1,p} ⊂ C⁰` for `p > 2` on surfaces, and Section 3.5, on the
  `W^{1,p}` setting of the nonlinear Cauchy–Riemann operator.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.CylinderSobolev

open StripSobolev (jet jet_apply stripMeasure jetLp jetClosure coeFn_jetLp norm_jetLp
  jetLp_mem_jetClosure denseRange_codRestrict_jetLp coe_translate translateLp_jetLp
  exists_forall_mem_strip_norm_le)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The jets of test sections in `W^{1,p}` -/

section W1p

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The jet of a test section, as an element of `W1p V p`. -/
def toW1p : testSection V →ₗ[ℝ] W1p V p :=
  (jetLp p (testSection V)).codRestrict (W1p V p) jetLp_mem_jetClosure

variable {p}

@[simp]
theorem coe_toW1p (ξ : testSection V) :
    (toW1p p ξ : Lp (V × V × V) p stripMeasure) = jetLp p (testSection V) ξ :=
  (rfl)

/-- The norm of the jet of a test section in `W1p V p` is the `Lᵖ` norm of its jet on the
strip. -/
theorem norm_toW1p (ξ : testSection V) :
    ‖toW1p p ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) p stripMeasure).toReal := by
  rw [← Submodule.norm_coe, coe_toW1p, norm_jetLp]

/-- The jets of test sections are dense in `W1p V p`. -/
theorem denseRange_toW1p : DenseRange (toW1p (V := V) p) :=
  denseRange_codRestrict_jetLp p _

/-- A closed subset of `W1p V p` containing the jets of all test sections is everything. -/
@[elab_as_elim]
theorem W1p_induction {P : W1p V p → Prop} (hP : IsClosed {x | P x})
    (h : ∀ ξ : testSection V, P (toW1p p ξ)) (x : W1p V p) : P x :=
  denseRange_toW1p.induction_on x hP h

/-- The value of the jet of a test section is the test section. -/
theorem valueL_toW1p_ae_eq (ξ : testSection V) :
    valueL p (toW1p p ξ) =ᵐ[stripMeasure] (ξ : ℝ × ℝ → V) := by
  filter_upwards [coeFn_valueL (toW1p p ξ), coeFn_jetLp p ξ] with z h₁ h₂
  rw [h₁, coe_toW1p, h₂, jet_apply]

/-- Translation along the cylinder sends the jet of a test section to the jet of its
translate. -/
@[simp]
theorem translate_toW1p (a : ℝ) (ξ : testSection V) :
    StripSobolev.translate p (testSection V) a (toW1p p ξ) =
      toW1p p ⟨_, comp_add_right_mem_testSection ξ.property a⟩ :=
  Subtype.ext <| by rw [coe_translate, coe_toW1p, coe_toW1p, translateLp_jetLp]

end W1p

/-! ### Test sections as bounded continuous functions -/

section BCF

variable {ξ : ℝ × ℝ → V}

/-- A test section of the cylinder is bounded on `ℝ × ℝ`: it is bounded on the strip, and it has
period one in `t`. -/
theorem exists_forall_norm_le_of_mem_testSection (hξ : ξ ∈ testSection V) :
    ∃ C, ∀ z, ‖ξ z‖ ≤ C := by
  obtain ⟨hξ2, hper, R, hR⟩ := mem_testSection_iff.1 hξ
  obtain ⟨C, -, hC⟩ := exists_forall_mem_strip_norm_le hξ2.continuous (R := R)
    fun z hz ↦ hR z.1 z.2 hz.le
  refine ⟨C, fun ⟨s, t⟩ ↦ ?_⟩
  have hper' : Function.Periodic (fun t ↦ ξ (s, t)) 1 := fun t ↦ hper s t
  have h := hper'.sub_int_mul_eq (x := t) ⌊t⌋
  simp only [mul_one, Int.self_sub_floor] at h
  rw [← h]
  exact hC _ ⟨mem_univ _, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- A test section, as a bounded continuous function on `ℝ × ℝ`. -/
def testSectionToBCF : testSection V →ₗ[ℝ] (ℝ × ℝ →ᵇ V) where
  toFun ξ := BoundedContinuousFunction.ofNormedAddCommGroup (ξ : ℝ × ℝ → V)
    ((mem_testSection_iff.1 ξ.property).1.continuous)
    (exists_forall_norm_le_of_mem_testSection ξ.property).choose
    (exists_forall_norm_le_of_mem_testSection ξ.property).choose_spec
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
theorem coe_testSectionToBCF (ξ : testSection V) :
    ⇑(testSectionToBCF ξ) = (ξ : ℝ × ℝ → V) :=
  (rfl)

end BCF

/-! ### The Sobolev embedding for `p > 2` -/

section Embedding

variable [CompleteSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Morrey's estimate for test sections.** For `2 < p < ∞` there is a constant `C` bounding the
supremum norm of every test section by `C` times the `W^{1,p}` norm of its jet. -/
theorem exists_norm_testSectionToBCF_le (hp : 2 < p) (hpt : p ≠ ∞) :
    ∃ C : ℝ, ∀ ξ : testSection V, ‖testSectionToBCF ξ‖ ≤ C * ‖toW1p p ξ‖ := by
  lift p to ℝ≥0 using hpt
  obtain ⟨C, hC⟩ := exists_enorm_le_mul_eLpNorm_jet (V := V) (p := p) (by exact_mod_cast hp)
  refine ⟨C, fun ξ ↦ ?_⟩
  obtain ⟨hξ2, hper, -⟩ := mem_testSection_iff.1 ξ.property
  have hfin := (memLp_jet ξ.property p).eLpNorm_ne_top
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun z ↦ ?_
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
    (hC (hξ2.of_le (by norm_num)) hper z)
  rw [ENNReal.toReal_mul, toReal_eNorm, ENNReal.coe_toReal] at h
  rwa [coe_testSectionToBCF, norm_toW1p]

variable (p) in
/-- **The Sobolev embedding `W^{1,p} ⊂ C⁰_b` of the cylinder**, for `2 < p < ∞`: the continuous
linear map from `W^{1,p}(ℝ × S¹, V)` to the bounded continuous functions on `ℝ × ℝ` extending the
inclusion of the test sections (`TauCeti.CylinderSobolev.coe_continuousValue_toW1p`). It is the
continuous representative of the value of an element
(`TauCeti.CylinderSobolev.valueL_ae_eq_continuousValue`). For `p ≤ 2` it is `0`, by the
convention of `LinearMap.extendOfNorm`. -/
def continuousValue : W1p V p →L[ℝ] (ℝ × ℝ →ᵇ V) :=
  testSectionToBCF.extendOfNorm (toW1p p)

/-- The Sobolev embedding sends the jet of a test section to the test section, as a bounded
continuous function. -/
theorem continuousValue_toW1p (hp : 2 < p) (hpt : p ≠ ∞) (ξ : testSection V) :
    continuousValue p (toW1p p ξ) = testSectionToBCF ξ := by
  -- Elaborating the extension lemma with `toW1p` fixed, before matching it against the goal,
  -- keeps the unification of the two `W1p V p` structures cheap.
  have hd : DenseRange (toW1p (V := V) p) := denseRange_toW1p
  have h := LinearMap.extendOfNorm_eq (f := testSectionToBCF) (e := toW1p p) hd
    (exists_norm_testSectionToBCF_le (V := V) hp hpt) ξ
  exact h

/-- The Sobolev embedding sends the jet of a test section to the test section. -/
theorem coe_continuousValue_toW1p (hp : 2 < p) (hpt : p ≠ ∞) (ξ : testSection V) :
    ⇑(continuousValue p (toW1p p ξ)) = (ξ : ℝ × ℝ → V) := by
  rw [continuousValue_toW1p hp hpt, coe_testSectionToBCF]

/-- Evaluating the image under the Sobolev embedding at a point is continuous on `W1p V p`. -/
private theorem continuous_eval_const_continuousValue (z : ℝ × ℝ) :
    Continuous fun x : W1p V p ↦ continuousValue p x z :=
  (BoundedContinuousFunction.evalCLM ℝ z).continuous.comp (continuousValue p).continuous

omit [CompleteSpace V] in
/-- Every element of `W1p V p` is the limit of the jets of a sequence of test sections. -/
private theorem exists_seq_tendsto_toW1p (x : W1p V p) :
    ∃ ξ : ℕ → testSection V, Tendsto (fun n ↦ toW1p p (ξ n)) atTop (𝓝 x) := by
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_toW1p (V := V) (p := p) x)
  choose ξ hξ using hy
  exact ⟨ξ, by simpa only [hξ] using hlim⟩

/-- **The continuous representative.** For `2 < p < ∞`, the value of an element of
`W^{1,p}(ℝ × S¹, V)` agrees almost everywhere on the strip with its image under the Sobolev
embedding, a bounded continuous function. -/
theorem valueL_ae_eq_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    valueL p x =ᵐ[stripMeasure] continuousValue p x := by
  obtain ⟨ξ, hξ⟩ := exists_seq_tendsto_toW1p x
  -- The values converge in `Lᵖ`, so a subsequence converges almost everywhere.
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((valueL p).continuous.tendsto x).comp hξ)).exists_seq_tendsto_ae
  -- The continuous representatives converge uniformly, so pointwise.
  have hcont := ((continuousValue p).continuous.tendsto x).comp hξ
  filter_upwards [hns, ae_all_iff.2 fun n ↦ valueL_toW1p_ae_eq (p := p) (ξ (ns n))]
    with z hz hzn
  refine tendsto_nhds_unique hz ?_
  have hev := (((BoundedContinuousFunction.evalCLM ℝ z).continuous.tendsto _).comp
    (hcont.comp hmono.tendsto_atTop))
  refine hev.congr fun n ↦ ?_
  simp only [Function.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    coe_continuousValue_toW1p hp hpt, hzn n]

/-- **The continuous representative is a section of the cylinder**: it has period one in `t`. -/
theorem continuousValue_add_one (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) (s t : ℝ) :
    continuousValue p x (s, t + 1) = continuousValue p x (s, t) := by
  refine W1p_induction (isClosed_eq (continuous_eval_const_continuousValue _)
      (continuous_eval_const_continuousValue _)) (fun ξ ↦ ?_) x
  simp only [coe_continuousValue_toW1p hp hpt]
  exact (mem_testSection_iff.1 ξ.property).2.1 s t

/-- **The continuous representative decays along the ends.** For `2 < p < ∞`, the image of an
element of `W^{1,p}(ℝ × S¹, V)` under the Sobolev embedding tends to zero as `|s| → ∞`,
uniformly in `t`. -/
theorem tendsto_continuousValue_comap_fst_cocompact (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    Tendsto (continuousValue p x) (comap Prod.fst (cocompact ℝ)) (𝓝 0) := by
  obtain ⟨ξ, hξ⟩ := exists_seq_tendsto_toW1p x
  have hunif := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
    (((continuousValue p).continuous.tendsto x).comp hξ)
  refine hunif.tendsto_of_eventually_tendsto (L := fun _ ↦ 0)
    (Eventually.of_forall fun n ↦ ?_) tendsto_const_nhds
  simp only [Function.comp_apply, coe_continuousValue_toW1p hp hpt]
  -- The value of a test section is the first component of its jet, which decays.
  simpa [Function.comp_def, jet_apply] using
    (continuous_fst.tendsto 0).comp (tendsto_jet_comap_fst_cocompact (ξ n).property)

/-- **The Sobolev embedding commutes with translation**: the continuous representative of the
translate of an element of `W1p V p` is the translate of its continuous representative. -/
theorem continuousValue_translate (hp : 2 < p) (hpt : p ≠ ∞) (a : ℝ) (x : W1p V p)
    (z : ℝ × ℝ) :
    continuousValue p (StripSobolev.translate p (testSection V) a x) z =
      continuousValue p x (z + (a, 0)) := by
  refine W1p_induction (isClosed_eq ((continuous_eval_const_continuousValue z).comp
    (StripSobolev.translate p (testSection V) a).continuous)
      (continuous_eval_const_continuousValue _)) (fun ξ ↦ ?_) x
  rw [translate_toW1p, coe_continuousValue_toW1p hp hpt, coe_continuousValue_toW1p hp hpt]

end Embedding

end TauCeti.CylinderSobolev
