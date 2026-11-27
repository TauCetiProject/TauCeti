/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Sobolev.Strip.Basic
import TauCeti.Analysis.Sobolev.Strip.Morrey
import TauCeti.Topology.Compactness.Normed

/-!
# The Sobolev spaces `W^{1,p}` of the strip with boundary conditions, and their embedding into
continuous sections for `p > 2`

Let `V` be a real normed space and `F₀`, `F₁` two subspaces of `V`. The test sections
`TauCeti.StripSobolev.testSection F₀ F₁` of the trivial bundle with fibre `V` over the strip
`ℝ × [0, 1]` are the `C²` maps `ξ : ℝ × ℝ → V` vanishing for `|s|` large, with boundary values
`ξ (s, 0) ∈ F₀` and `ξ (s, 1) ∈ F₁`. For `1 ≤ p < ∞` the Sobolev space
`W^{1,p}_F(ℝ × [0, 1], V)` is the completion of the test sections in the `W^{1,p}` norm, realized
inside `Lᵖ(ℝ × [0, 1], V × V × V)` as the closure of their `Lᵖ` jets `(ξ, ∂s ξ, ∂t ξ)`
(`TauCeti.StripSobolev.W1p F₀ F₁ p`, the construction `TauCeti.StripSobolev.jetClosure` shared
with the cylinder); for `p = 2` it is `TauCeti.StripSobolev.H1 F₀ F₁`. The jets of test sections
(`TauCeti.StripSobolev.toW1p`) are dense in it. Its norm is translation invariant: translation in
the `s` direction, `TauCeti.StripSobolev.translate p (testSection F₀ F₁) a`, is a linear isometric
equivalence of `W1p F₀ F₁ p`, so a section and its translate along the strip have the same
`W^{1,p}` norm, which no norm built from one fixed compact piece of the strip would give.

Since the strip has dimension two, for `p > 2` Morrey's estimate up to the boundary
(`TauCeti.StripSobolev.exists_enorm_le_mul_eLpNorm_jet`) bounds the restriction of a test section to
the closed strip pointwise by the `Lᵖ` norm of its jet. This restriction is a bounded continuous
function on `ℝ × [0, 1]` (`TauCeti.StripSobolev.testSectionToBCF`, with `[0, 1]` the unit interval
`unitInterval`), so the estimate extends the restriction of the test sections to a continuous
linear map

`TauCeti.StripSobolev.continuousValue F₀ F₁ p : W^{1,p}_F(ℝ × [0, 1], V) →L[ℝ] (ℝ × [0, 1] →ᵇ V)`,

the **Sobolev embedding** `W^{1,p} ⊂ C⁰_b` of the strip. It sends the jet of a test section to the
test section (`TauCeti.StripSobolev.continuousValue_toW1p_apply`), and it is the continuous
representative of every element: the value `ξ` of an `Lᵖ` jet `(ξ, ξ_s, ξ_t) ∈ W^{1,p}`, the
bounded linear map `TauCeti.StripSobolev.valueL F₀ F₁ p` to `Lᵖ(ℝ × [0, 1], V)`, agrees almost
everywhere on the strip with it (`TauCeti.StripSobolev.valueL_ae_eq_continuousValue`), and it is
the only continuous function on the closed strip doing so
(`TauCeti.StripSobolev.continuousValue_apply_eq_of_ae_eq`).

For closed subspaces `F₀` and `F₁`, the continuous representative satisfies the boundary
conditions at every point of the two boundary lines
(`TauCeti.StripSobolev.continuousValue_apply_zero_mem`,
`TauCeti.StripSobolev.continuousValue_apply_one_mem`), not only almost everywhere as the traces of
elements of `H1 F₀ F₁` do. The boundary conditions are faithful: the jet of a `C²` section vanishing
for `|s|` large lies in `W1p F₀ F₁ p` exactly when its boundary values lie in `F₀` and `F₁`
(`TauCeti.StripSobolev.jetLp_mem_W1p_iff`). The continuous representative also commutes with
translation (`TauCeti.StripSobolev.continuousValue_translate`) and tends to zero along both ends,
uniformly in `t` (`TauCeti.StripSobolev.tendsto_continuousValue_comap_fst_cocompact`); in
particular a nonzero constant section, although it satisfies boundary conditions such as `ℝ ⊂ ℂ`
on both edges and has vanishing derivative, is the continuous representative of no element of
`W^{1,p}`. Since `continuousValue F₀ F₁ p` is continuous, convergence in `W^{1,p}` implies uniform
convergence of the continuous representatives on the closed strip.

This is the functional setting of the nonlinear Cauchy–Riemann operator on increments of a
holomorphic strip with boundary on two Lagrangians, in a trivialization in which their tangent
spaces along the boundary are `F₀` and `F₁`: for `p > 2` an element of `W^{1,p}` is a continuous
section, so it can be inserted into the nonlinear coefficients, and its boundary values lie in the
linearized boundary conditions. For `p ≤ 2` Morrey's estimate fails, and `continuousValue F₀ F₁ p`
is `0` by the convention of `LinearMap.extendOfNorm`. The nonlinear sections of
`TauCeti.Analysis.Sobolev.QuasilinearSection` evaluate their coefficients at continuous
representatives defined on the whole plane, where the strip measure lives; for the strip these
are the images under `TauCeti.StripSobolev.continuousValueIccExtend F₀ F₁ p`, the Sobolev embedding
followed by the extension from the closed strip that is constant in `t` on either side of it, as
`Set.IccExtend` does for functions on an interval. The first component of the jet of every element
of `W^{1,p}` agrees with it almost everywhere on the strip
(`TauCeti.StripSobolev.fst_ae_eq_continuousValueIccExtend`).

## Main definitions

* `TauCeti.StripSobolev.W1p F₀ F₁ p`: the Sobolev space `W^{1,p}_F(ℝ × [0, 1], V)`.
* `TauCeti.StripSobolev.toW1p F₀ F₁ p`: the jet of a test section, as an element of it.
* `TauCeti.StripSobolev.testSectionToBCF`: a test section on the closed strip, as a bounded
  continuous function.
* `TauCeti.StripSobolev.continuousValue F₀ F₁ p`: the Sobolev embedding `W^{1,p} ⊂ C⁰_b`, `p > 2`.
* `TauCeti.StripSobolev.continuousValueIccExtend F₀ F₁ p`: the Sobolev embedding followed by the
  extension from the closed strip to the plane that is constant in `t` outside `[0, 1]`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4 (Morrey's inequality) and
  §5.6.3 (the general Sobolev inequalities).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.1,
  on the Sobolev embedding `W^{1,p} ⊂ C⁰` for `p > 2` on surfaces, and Sections 3.1 and 3.5, on
  the `W^{1,p}` setting of the nonlinear Cauchy–Riemann operator with totally real boundary
  conditions.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology unitInterval
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F₀ F₁ : Submodule ℝ V}

/-! ### The Sobolev spaces `W^{1,p}` -/

section W1p

variable (F₀ F₁) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The Sobolev space `W^{1,p}_F(ℝ × [0, 1], V)` of sections with boundary values in `F₀` and
`F₁`: the closure in `Lᵖ(ℝ × [0, 1], V × V × V)` of the jets of test sections. For `1 ≤ p < ∞` it
is the completion of the test sections in the `W^{1,p}` norm; for `p = ∞` it is only the closure of
the test sections, not `W^{1,∞}`. An element is an `Lᵖ` jet `(ξ, ξ_s, ξ_t)`. For `p = 2` it is
`TauCeti.StripSobolev.H1 F₀ F₁`. -/
abbrev W1p : Submodule ℝ (Lp (V × V × V) p stripMeasure) :=
  jetClosure p (testSection F₀ F₁)

/-- The jet of a test section, as an element of `W1p F₀ F₁ p`: the map
`TauCeti.StripSobolev.toJetClosure` for the test sections, whose coercion, norm, density,
induction and translation lemmas (`TauCeti.StripSobolev.coe_toJetClosure`,
`TauCeti.StripSobolev.norm_toJetClosure`, `TauCeti.StripSobolev.denseRange_toJetClosure`,
`TauCeti.StripSobolev.jetClosure_induction`, `TauCeti.StripSobolev.translate_toJetClosure`) apply
to it. -/
abbrev toW1p : testSection F₀ F₁ →ₗ[ℝ] W1p F₀ F₁ p :=
  toJetClosure p (testSection F₀ F₁)

end W1p

/-! ### Test sections as bounded continuous functions on the closed strip -/

section BCF

variable {ξ : ℝ × ℝ → V}

/-- A test section is bounded on the closed strip `ℝ × [0, 1]`. -/
theorem exists_forall_norm_le_of_mem_testSection (hξ : ξ ∈ testSection F₀ F₁) :
    ∃ C, ∀ z : ℝ × I, ‖ξ (z.1, z.2)‖ ≤ C := by
  obtain ⟨hξ2, -, -, R, hR⟩ := mem_testSection_iff.1 hξ
  obtain ⟨C, -, hC⟩ := exists_forall_mem_strip_norm_le hξ2.continuous (R := R)
    fun z hz ↦ hR z.1 z.2 hz.le
  exact ⟨C, fun z ↦ hC _ ⟨mem_univ _, z.2.property⟩⟩

/-- A test section on the closed strip `ℝ × [0, 1]`, as a bounded continuous function on
`ℝ × unitInterval`. -/
def testSectionToBCF : testSection F₀ F₁ →ₗ[ℝ] (ℝ × I →ᵇ V) where
  toFun ξ := BoundedContinuousFunction.ofNormedAddCommGroup (fun z ↦ (ξ : ℝ × ℝ → V) (z.1, z.2))
    ((mem_testSection_iff.1 ξ.property).1.continuous.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)))
    (exists_forall_norm_le_of_mem_testSection ξ.property).choose
    (exists_forall_norm_le_of_mem_testSection ξ.property).choose_spec
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
theorem testSectionToBCF_apply (ξ : testSection F₀ F₁) (z : ℝ × I) :
    testSectionToBCF ξ z = (ξ : ℝ × ℝ → V) (z.1, z.2) :=
  (rfl)

end BCF

/-! ### The Sobolev embedding for `p > 2` -/

section Embedding

variable [CompleteSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Morrey's estimate for test sections.** For `2 < p < ∞` there is a constant `C` bounding the
supremum norm on the closed strip of every test section by `C` times the `W^{1,p}` norm of its
jet. -/
theorem exists_norm_testSectionToBCF_le (hp : 2 < p) (hpt : p ≠ ∞) :
    ∃ C : ℝ, ∀ ξ : testSection F₀ F₁, ‖testSectionToBCF ξ‖ ≤ C * ‖toW1p F₀ F₁ p ξ‖ := by
  lift p to ℝ≥0 using hpt
  obtain ⟨C, hC⟩ := exists_enorm_le_mul_eLpNorm_jet (V := V) (p := p) (by exact_mod_cast hp)
  refine ⟨C, fun ξ ↦ ?_⟩
  have hξ := contDiff_one_of_mem_testSection ξ.property
  have hfin := (memLp_jet ξ.property p).eLpNorm_ne_top
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun z ↦ ?_
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
    (hC hξ.contDiffOn hξ.continuous.continuousOn (z.1, z.2) ⟨mem_univ _, z.2.property⟩)
  rw [ENNReal.toReal_mul, toReal_eNorm, ENNReal.coe_toReal] at h
  rwa [testSectionToBCF_apply, norm_toJetClosure]

variable (F₀ F₁ p) in
/-- **The Sobolev embedding `W^{1,p} ⊂ C⁰_b` of the strip**, for `2 < p < ∞`: the continuous
linear map from `W^{1,p}_F(ℝ × [0, 1], V)` to the bounded continuous functions on the closed strip
extending the restriction of the test sections
(`TauCeti.StripSobolev.continuousValue_toW1p_apply`). It is the continuous representative of the
value of an element (`TauCeti.StripSobolev.valueL_ae_eq_continuousValue`). For `p ≤ 2` it is `0`, by
the convention of `LinearMap.extendOfNorm`. -/
def continuousValue : W1p F₀ F₁ p →L[ℝ] (ℝ × I →ᵇ V) :=
  testSectionToBCF.extendOfNorm (toW1p F₀ F₁ p)

/-- The Sobolev embedding sends the jet of a test section to the test section on the closed strip,
as a bounded continuous function. -/
theorem continuousValue_toW1p (hp : 2 < p) (hpt : p ≠ ∞) (ξ : testSection F₀ F₁) :
    continuousValue F₀ F₁ p (toW1p F₀ F₁ p ξ) = testSectionToBCF ξ := by
  -- Elaborating the extension lemma with `toW1p` fixed, before matching it against the goal,
  -- keeps the unification of the two `W1p F₀ F₁ p` structures cheap.
  have hd : DenseRange (toW1p F₀ F₁ p) := denseRange_toJetClosure p _
  have h := LinearMap.extendOfNorm_eq (f := testSectionToBCF) (e := toW1p F₀ F₁ p) hd
    (exists_norm_testSectionToBCF_le hp hpt) ξ
  exact h

/-- The Sobolev embedding sends the jet of a test section to the test section, at every point of
the closed strip. -/
theorem continuousValue_toW1p_apply (hp : 2 < p) (hpt : p ≠ ∞) (ξ : testSection F₀ F₁)
    (z : ℝ × I) :
    continuousValue F₀ F₁ p (toW1p F₀ F₁ p ξ) z = (ξ : ℝ × ℝ → V) (z.1, z.2) := by
  rw [continuousValue_toW1p hp hpt, testSectionToBCF_apply]

/-- Evaluating the image under the Sobolev embedding at a point is continuous on `W1p F₀ F₁ p`. -/
private theorem continuous_eval_const_continuousValue (z : ℝ × I) :
    Continuous fun x : W1p F₀ F₁ p ↦ continuousValue F₀ F₁ p x z :=
  (BoundedContinuousFunction.evalCLM ℝ z).continuous.comp (continuousValue F₀ F₁ p).continuous

/-- **The continuous representative.** For `2 < p < ∞`, the value of an element of
`W^{1,p}_F(ℝ × [0, 1], V)` agrees almost everywhere on the strip with its image under the Sobolev
embedding, read on the closed strip through the projection `Set.projIcc` of `ℝ` onto `[0, 1]`. -/
theorem valueL_ae_eq_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p F₀ F₁ p) :
    valueL F₀ F₁ p x =ᵐ[stripMeasure]
      fun z ↦ continuousValue F₀ F₁ p x (z.1, projIcc 0 1 zero_le_one z.2) := by
  refine (coeFn_valueL x).trans
    (fst_ae_eq_of_forall_toJetClosure (continuousValue F₀ F₁ p).continuous (fun ξ ↦ ?_) x)
  filter_upwards [coeFn_jetLp p ξ, ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)]
    with z hz hzs
  simp only [continuousValue_toW1p_apply hp hpt, projIcc_of_mem zero_le_one hzs.2, coe_toJetClosure,
    hz, jet_apply]

variable (F₀ F₁ p) in
/-- **The Sobolev embedding of the strip, read on the plane.** The image of an element of
`W^{1,p}_F(ℝ × [0, 1], V)` under the Sobolev embedding `TauCeti.StripSobolev.continuousValue`,
extended from the closed strip to `ℝ × ℝ` by precomposition with `(s, t) ↦ (s, projIcc 0 1 t)`, so
that it is constant in `t` on either side of the strip. On the closed strip it is the continuous
representative (`TauCeti.StripSobolev.continuousValueIccExtend_apply_coe`), and for `2 < p < ∞` the
first component of the jet of every element agrees with it almost everywhere on the strip
(`TauCeti.StripSobolev.fst_ae_eq_continuousValueIccExtend`). -/
def continuousValueIccExtend : W1p F₀ F₁ p →L[ℝ] (ℝ × ℝ →ᵇ V) :=
  BoundedContinuousFunction.compContinuousCLM V ℝ
    ⟨fun z ↦ (z.1, projIcc 0 1 zero_le_one z.2),
      continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)⟩ ∘L
    continuousValue F₀ F₁ p

/-- The extended Sobolev embedding at a point of the plane is the Sobolev embedding at the nearest
point of the closed strip on the same vertical line. -/
theorem continuousValueIccExtend_apply (x : W1p F₀ F₁ p) (z : ℝ × ℝ) :
    continuousValueIccExtend F₀ F₁ p x z =
      continuousValue F₀ F₁ p x (z.1, projIcc 0 1 zero_le_one z.2) :=
  (rfl)

/-- On the closed strip the extended Sobolev embedding is the Sobolev embedding. -/
@[simp]
theorem continuousValueIccExtend_apply_coe (x : W1p F₀ F₁ p) (z : ℝ × I) :
    continuousValueIccExtend F₀ F₁ p x (z.1, z.2) = continuousValue F₀ F₁ p x z := by
  rw [continuousValueIccExtend_apply, projIcc_val]

/-- For `2 < p < ∞`, the first component of the jet of an element of `W^{1,p}_F(ℝ × [0, 1], V)`
is its continuous representative, read on the plane through
`TauCeti.StripSobolev.continuousValueIccExtend`, almost everywhere on the strip. -/
theorem fst_ae_eq_continuousValueIccExtend (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p F₀ F₁ p) :
    ∀ᵐ z ∂stripMeasure,
      ((x : Lp (V × V × V) p stripMeasure) z).1 = continuousValueIccExtend F₀ F₁ p x z := by
  filter_upwards [coeFn_valueL x, valueL_ae_eq_continuousValue hp hpt x] with z h₁ h₂
  rw [← h₁, h₂, continuousValueIccExtend_apply]

/-- **Uniqueness of the continuous representative.** For `2 < p < ∞`, a function continuous on the
closed strip whose restriction agrees almost everywhere with the value of an element of
`W^{1,p}_F(ℝ × [0, 1], V)` is its image under the Sobolev embedding. -/
theorem continuousValue_apply_eq_of_ae_eq (hp : 2 < p) (hpt : p ≠ ∞) {x : W1p F₀ F₁ p}
    {u : ℝ × ℝ → V} (hu : ContinuousOn u (univ ×ˢ Icc 0 1))
    (h : valueL F₀ F₁ p x =ᵐ[stripMeasure] u) (z : ℝ × I) :
    continuousValue F₀ F₁ p x z = u (z.1, z.2) := by
  have hc : Continuous fun z : ℝ × ℝ ↦
      continuousValue F₀ F₁ p x (z.1, projIcc 0 1 zero_le_one z.2) :=
    (continuousValue F₀ F₁ p x).continuous.comp
      (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))
  have hint : (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ closure (interior (univ ×ˢ Icc 0 1)) := by
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq, closure_univ,
      closure_Ioo zero_ne_one]
  have heq := Measure.eqOn_of_ae_eq ((valueL_ae_eq_continuousValue hp hpt x).symm.trans h)
    hc.continuousOn hu hint (x := (z.1, (z.2 : ℝ))) ⟨mem_univ _, z.2.property⟩
  simpa only [projIcc_val] using heq

/-- **The boundary condition on `ℝ × {0}`.** For a closed subspace `F₀`, the continuous
representative of every element of `W^{1,p}_F(ℝ × [0, 1], V)` takes values in `F₀` at every point
of the boundary line `ℝ × {0}`. -/
theorem continuousValue_apply_zero_mem (hp : 2 < p) (hpt : p ≠ ∞) (hF₀ : IsClosed (F₀ : Set V))
    (x : W1p F₀ F₁ p) (s : ℝ) : continuousValue F₀ F₁ p x (s, 0) ∈ F₀ := by
  refine jetClosure_induction (hF₀.preimage (continuous_eval_const_continuousValue _))
    (fun ξ ↦ ?_) x
  simpa [continuousValue_toW1p_apply hp hpt] using (mem_testSection_iff.1 ξ.property).2.1 s

/-- **The boundary condition on `ℝ × {1}`.** For a closed subspace `F₁`, the continuous
representative of every element of `W^{1,p}_F(ℝ × [0, 1], V)` takes values in `F₁` at every point
of the boundary line `ℝ × {1}`. -/
theorem continuousValue_apply_one_mem (hp : 2 < p) (hpt : p ≠ ∞) (hF₁ : IsClosed (F₁ : Set V))
    (x : W1p F₀ F₁ p) (s : ℝ) : continuousValue F₀ F₁ p x (s, 1) ∈ F₁ := by
  refine jetClosure_induction (hF₁.preimage (continuous_eval_const_continuousValue _))
    (fun ξ ↦ ?_) x
  simpa [continuousValue_toW1p_apply hp hpt] using (mem_testSection_iff.1 ξ.property).2.2.1 s

/-- **Faithfulness of the boundary conditions.** For closed subspaces `F₀` and `F₁` and
`2 < p < ∞`, the jet of a `C²` section vanishing for `|s|` large lies in `W1p F₀ F₁ p` exactly when
the boundary values of the section lie in `F₀` and `F₁`, that is, when it is a test section for
these boundary conditions. -/
theorem jetLp_mem_W1p_iff (hp : 2 < p) (hpt : p ≠ ∞) (hF₀ : IsClosed (F₀ : Set V))
    (hF₁ : IsClosed (F₁ : Set V)) (ξ : testSection (⊤ : Submodule ℝ V) ⊤) :
    jetLp p (testSection ⊤ ⊤) ξ ∈ W1p F₀ F₁ p ↔ (ξ : ℝ × ℝ → V) ∈ testSection F₀ F₁ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · have := jetLp_mem_jetClosure (p := p) (S := testSection F₀ F₁) ⟨ξ, h⟩
    rwa [← jetLp_inclusion le_top le_top] at this
  obtain ⟨hξ, -, -, hR⟩ := mem_testSection_iff.1 ξ.property
  -- The continuous representative of the jet is the section itself.
  have hval (z : ℝ × I) : continuousValue F₀ F₁ p ⟨_, h⟩ z = (ξ : ℝ × ℝ → V) (z.1, z.2) :=
    continuousValue_apply_eq_of_ae_eq hp hpt hξ.continuous.continuousOn
      ((coeFn_valueL _).trans ((coeFn_jetLp p ξ).mono fun z hz ↦ by simp only [hz, jet_apply])) z
  refine mem_testSection_iff.2 ⟨hξ, fun s ↦ ?_, fun s ↦ ?_, hR⟩
  · simpa [hval] using continuousValue_apply_zero_mem hp hpt hF₀ ⟨_, h⟩ s
  · simpa [hval] using continuousValue_apply_one_mem hp hpt hF₁ ⟨_, h⟩ s

/-- **The continuous representative decays along the ends.** The image of an element of
`W^{1,p}_F(ℝ × [0, 1], V)` under the Sobolev embedding tends to zero as `|s| → ∞`, uniformly in
`t`. -/
theorem tendsto_continuousValue_comap_fst_cocompact (hp : 2 < p) (hpt : p ≠ ∞)
    (x : W1p F₀ F₁ p) :
    Tendsto (continuousValue F₀ F₁ p x) (comap Prod.fst (cocompact ℝ)) (𝓝 0) := by
  refine tendsto_of_forall_tendsto_toJetClosure (continuousValue F₀ F₁ p).continuous
    (fun ξ ↦ ?_) x
  rw [continuousValue_toW1p hp hpt]
  obtain ⟨-, -, -, R, hR⟩ := mem_testSection_iff.1 ξ.property
  exact tendsto_comap_fst_cocompact_of_eq_zero fun z hz ↦ by
    rw [testSectionToBCF_apply, hR _ _ hz.le]

/-- **The Sobolev embedding commutes with translation**: the continuous representative of the
translate of an element of `W1p F₀ F₁ p` is the translate of its continuous representative. -/
theorem continuousValue_translate (hp : 2 < p) (hpt : p ≠ ∞) (a : ℝ) (x : W1p F₀ F₁ p)
    (z : ℝ × I) :
    continuousValue F₀ F₁ p (translate p (testSection F₀ F₁) a x) z =
      continuousValue F₀ F₁ p x (z.1 + a, z.2) := by
  refine jetClosure_induction (isClosed_eq ((continuous_eval_const_continuousValue z).comp
    (translate p (testSection F₀ F₁) a).continuous)
      (continuous_eval_const_continuousValue _)) (fun ξ ↦ ?_) x
  rw [translate_toJetClosure, continuousValue_toW1p_apply hp hpt,
    continuousValue_toW1p_apply hp hpt]
  simp

end Embedding

end TauCeti.StripSobolev
