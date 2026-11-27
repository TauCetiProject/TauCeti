/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Sobolev.Cylinder.Morrey
import TauCeti.Algebra.Order.Floor.Ring

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
(`TauCeti.CylinderSobolev.toW1p`), which are dense. The jet of a sum, difference or multiple is
almost everywhere the sum, difference or multiple of the jets
(`TauCeti.CylinderSobolev.coeFn_W1p_add`, `TauCeti.CylinderSobolev.coeFn_W1p_sub`,
`TauCeti.CylinderSobolev.coeFn_W1p_smul`). The norm is computed on the strip
`ℝ × [0, 1]`, a fundamental domain of the cylinder, and does not single out a compact piece of
it: translation along the cylinder, `TauCeti.StripSobolev.translate p (testSection V) a`, is a
linear isometric equivalence of `W^{1,p}`, and it sends the jet of a test section to the jet of
its translate (`TauCeti.StripSobolev.translate_toJetClosure`).

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
`continuousValue p` of it (`TauCeti.CylinderSobolev.valueL_ae_eq_continuousValue`;
`TauCeti.CylinderSobolev.fst_ae_eq_continuousValue` for the first component of the jet). Two
continuous representatives are uniformly within the norm of the embedding times the `W^{1,p}`
distance (`ContinuousLinearMap.norm_apply_sub_apply_le`, in
`TauCeti.Topology.ContinuousMap.Bounded.Normed`). The
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
(`TauCeti.StripSobolev.norm_toJetClosure`). For `p ≤ 2` Morrey's estimate fails, and
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

open StripSobolev (jet jet_apply stripMeasure toJetClosure coe_toJetClosure
  norm_toJetClosure denseRange_toJetClosure jetClosure_induction translate_toJetClosure coeFn_jetLp
  exists_forall_mem_strip_norm_le fst_ae_eq_of_forall_toJetClosure
  tendsto_of_forall_tendsto_toJetClosure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The jets of test sections in `W^{1,p}` -/

section W1p

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The jet of a test section, as an element of `W1p V p`: the map
`TauCeti.StripSobolev.toJetClosure` for the test sections, whose coercion, norm, density,
induction and translation lemmas (`TauCeti.StripSobolev.coe_toJetClosure`,
`TauCeti.StripSobolev.norm_toJetClosure`, `TauCeti.StripSobolev.denseRange_toJetClosure`,
`TauCeti.StripSobolev.jetClosure_induction`, `TauCeti.StripSobolev.translate_toJetClosure`) apply
to it. -/
abbrev toW1p : testSection V →ₗ[ℝ] W1p V p :=
  toJetClosure p (testSection V)

variable {p}

/-- The value of the jet of a test section is the test section. -/
theorem valueL_toW1p_ae_eq (ξ : testSection V) :
    valueL p (toW1p p ξ) =ᵐ[stripMeasure] (ξ : ℝ × ℝ → V) := by
  filter_upwards [coeFn_valueL (toW1p p ξ), coeFn_jetLp p ξ] with z h₁ h₂
  rw [h₁, coe_toJetClosure, h₂, jet_apply]

/-- The jet of a sum of elements of `W1p V p` is the sum of their jets, almost everywhere. -/
theorem coeFn_W1p_add (x y : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((x + y : W1p V p) : Lp (V × V × V) p stripMeasure) z =
      (x : Lp (V × V × V) p stripMeasure) z + (y : Lp (V × V × V) p stripMeasure) z := by
  filter_upwards [Lp.coeFn_add (x : Lp (V × V × V) p stripMeasure) y] with z hz
  rw [Submodule.coe_add, hz, Pi.add_apply]

/-- The jet of a difference of elements of `W1p V p` is the difference of their jets, almost
everywhere. -/
theorem coeFn_W1p_sub (x y : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((x - y : W1p V p) : Lp (V × V × V) p stripMeasure) z =
      (x : Lp (V × V × V) p stripMeasure) z - (y : Lp (V × V × V) p stripMeasure) z := by
  filter_upwards [Lp.coeFn_sub (x : Lp (V × V × V) p stripMeasure) y] with z hz
  rw [Submodule.coe_sub, hz, Pi.sub_apply]

/-- The jet of a multiple of an element of `W1p V p` is the multiple of its jet, almost
everywhere. -/
theorem coeFn_W1p_smul (c : ℝ) (x : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((c • x : W1p V p) : Lp (V × V × V) p stripMeasure) z =
      c • (x : Lp (V × V × V) p stripMeasure) z := by
  filter_upwards [Lp.coeFn_smul c (x : Lp (V × V × V) p stripMeasure)] with z hz
  rw [Submodule.coe_smul, hz, Pi.smul_apply]

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
  rw [← hper'.apply_fract t]
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
  rwa [coe_testSectionToBCF, norm_toJetClosure]

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
  have hd : DenseRange (toW1p (V := V) p) := denseRange_toJetClosure p _
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

/-- **The continuous representative.** For `2 < p < ∞`, the value of an element of
`W^{1,p}(ℝ × S¹, V)` agrees almost everywhere on the strip with its image under the Sobolev
embedding, a bounded continuous function. -/
theorem valueL_ae_eq_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    valueL p x =ᵐ[stripMeasure] continuousValue p x := by
  refine (coeFn_valueL x).trans (fst_ae_eq_of_forall_toJetClosure (continuousValue p).continuous
    (φ := id) (fun ξ ↦ ?_) x)
  filter_upwards [coeFn_jetLp p ξ] with z hz
  simp only [coe_toJetClosure, hz, jet_apply, id, coe_continuousValue_toW1p hp hpt]

/-- The first component of the jet of an element of `W1p V p` is its continuous representative,
almost everywhere on the strip. -/
theorem fst_ae_eq_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((x : Lp (V × V × V) p stripMeasure) z).1 = continuousValue p x z := by
  filter_upwards [coeFn_valueL x, valueL_ae_eq_continuousValue hp hpt x] with z h₁ h₂
  rw [← h₁, h₂]

/-- **The continuous representative is a section of the cylinder**: it has period one in `t`. -/
theorem continuousValue_add_one (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) (s t : ℝ) :
    continuousValue p x (s, t + 1) = continuousValue p x (s, t) := by
  refine jetClosure_induction (isClosed_eq (continuous_eval_const_continuousValue _)
      (continuous_eval_const_continuousValue _)) (fun ξ ↦ ?_) x
  simp only [coe_continuousValue_toW1p hp hpt]
  exact (mem_testSection_iff.1 ξ.property).2.1 s t

/-- **The continuous representative decays along the ends.** For `2 < p < ∞`, the image of an
element of `W^{1,p}(ℝ × S¹, V)` under the Sobolev embedding tends to zero as `|s| → ∞`,
uniformly in `t`. -/
theorem tendsto_continuousValue_comap_fst_cocompact (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    Tendsto (continuousValue p x) (comap Prod.fst (cocompact ℝ)) (𝓝 0) := by
  refine tendsto_of_forall_tendsto_toJetClosure (continuousValue p).continuous (fun ξ ↦ ?_) x
  rw [coe_continuousValue_toW1p hp hpt]
  -- The value of a test section is the first component of its jet, which decays.
  simpa [Function.comp_def, jet_apply] using
    (continuous_fst.tendsto 0).comp (tendsto_jet_comap_fst_cocompact ξ.property)

/-- **The Sobolev embedding commutes with translation**: the continuous representative of the
translate of an element of `W1p V p` is the translate of its continuous representative. -/
theorem continuousValue_translate (hp : 2 < p) (hpt : p ≠ ∞) (a : ℝ) (x : W1p V p)
    (z : ℝ × ℝ) :
    continuousValue p (StripSobolev.translate p (testSection V) a x) z =
      continuousValue p x (z + (a, 0)) := by
  refine jetClosure_induction (isClosed_eq ((continuous_eval_const_continuousValue z).comp
    (StripSobolev.translate p (testSection V) a).continuous)
      (continuous_eval_const_continuousValue _)) (fun ξ ↦ ?_) x
  rw [translate_toJetClosure, coe_continuousValue_toW1p hp hpt, coe_continuousValue_toW1p hp hpt]

end Embedding

end TauCeti.CylinderSobolev
