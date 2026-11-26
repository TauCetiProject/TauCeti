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
`1 ≤ p < ∞` this file defines the Sobolev space `W^{1,p}(ℝ × S¹, V)` as the completion of the test
sections in the `W^{1,p}` norm, realized inside `Lᵖ(ℝ × [0, 1], V × V × V)` as the closure of their
`Lᵖ` jets `(ξ, ∂s ξ, ∂t ξ)` (`TauCeti.CylinderSobolev.W1p`), exactly as
`TauCeti.CylinderSobolev.H1` realizes `W^{1,2}`; for `p = 2` the two agree
(`TauCeti.CylinderSobolev.W1p_two`). The norm is computed on the strip `ℝ × [0, 1]`, a fundamental
domain of the cylinder, and does not single out a compact piece of it: translation along the
cylinder is a linear isometric equivalence of `W^{1,p}` (`TauCeti.CylinderSobolev.translateW1p`).

Since the cylinder has dimension two, for `p > 2` Morrey's estimate
(`TauCeti.CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet`) bounds a test section pointwise by the
`Lᵖ` norm of its jet. A test section is a bounded continuous function on `ℝ × ℝ`
(`TauCeti.CylinderSobolev.testSectionToBCF`), so the estimate extends the inclusion of the test
sections to a continuous linear map

`TauCeti.CylinderSobolev.continuousValue p : W^{1,p}(ℝ × S¹, V) →L[ℝ] (ℝ × ℝ →ᵇ V)`,

the **Sobolev embedding** `W^{1,p} ⊂ C⁰_b`. It sends the jet of a test section to the section itself
(`TauCeti.CylinderSobolev.coe_continuousValue_toW1p`), and it is the continuous representative of
the value of every element: the value `ξ` of an `Lᵖ` jet `(ξ, ξ_s, ξ_t) ∈ W^{1,p}`
(`TauCeti.CylinderSobolev.valueLp`) agrees almost everywhere on the strip with
`continuousValue p` of it (`TauCeti.CylinderSobolev.valueLp_ae_eq_continuousValue`). The
continuous representative is a section of the cylinder, of period one in `t`
(`TauCeti.CylinderSobolev.continuousValue_add_one`), it commutes with translation
(`TauCeti.CylinderSobolev.continuousValue_translateW1p`), and it tends to zero along both ends,
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

* `TauCeti.CylinderSobolev.lpJet p`: the `Lᵖ` jet of a test section.
* `TauCeti.CylinderSobolev.W1p V p`: the Sobolev space `W^{1,p}(ℝ × S¹, V)`.
* `TauCeti.CylinderSobolev.toW1p p`: the jet of a test section, as an element of `W1p V p`.
* `TauCeti.CylinderSobolev.valueLp p`: the value `(ξ, ξ_s, ξ_t) ↦ ξ`, in `Lᵖ`.
* `TauCeti.CylinderSobolev.translateW1p p a`: translation by `a` along the cylinder.
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

open StripSobolev (jet stripMeasure memLp_jet_of_contDiff exists_forall_mem_strip_norm_le
  jet_add jet_smul)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The `Lᵖ` jets of test sections and their closure -/

section W1p

variable {ξ : ℝ × ℝ → V}

/-- The jet of a test section lies in every `Lᵖ` of the strip. -/
theorem memLp_jet_of_mem_testSection (hξ : ξ ∈ testSection V) (p : ℝ≥0∞) :
    MemLp (jet ξ) p stripMeasure := by
  obtain ⟨hξ2, -, R, hR⟩ := mem_testSection_iff.1 hξ
  exact memLp_jet_of_contDiff (hξ2.of_le (by norm_num)) hR

variable (V) (p : ℝ≥0∞)

/-- The `Lᵖ` jet `(ξ, ∂s ξ, ∂t ξ)` of a test section of the cylinder, as a linear map into
`Lᵖ(ℝ × [0, 1], V × V × V)`. For `p = 2` it is `TauCeti.StripSobolev.jetLp (testSection V)`
(`TauCeti.CylinderSobolev.lpJet_two`). -/
def lpJet : testSection V →ₗ[ℝ] Lp (V × V × V) p stripMeasure where
  toFun ξ := (memLp_jet_of_mem_testSection ξ.property p).toLp (jet (ξ : ℝ × ℝ → V))
  map_add' ξ η := by
    obtain ⟨hξ, -⟩ := mem_testSection_iff.1 ξ.property
    obtain ⟨hη, -⟩ := mem_testSection_iff.1 η.property
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by
      rw [jet_add (hξ.differentiable (by norm_num)) (hη.differentiable (by norm_num))])
  map_smul' c ξ := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_smul])

/-- The Sobolev space `W^{1,p}(ℝ × S¹, V)`: the closure in `Lᵖ(ℝ × [0, 1], V × V × V)` of the
`Lᵖ` jets of test sections, that is, the completion of the test sections in the `W^{1,p}` norm.
An element is an `Lᵖ` jet `(ξ, ξ_s, ξ_t)`. -/
def W1p [Fact (1 ≤ p)] : Submodule ℝ (Lp (V × V × V) p stripMeasure) :=
  (LinearMap.range (lpJet V p)).topologicalClosure

variable {V p}

/-- The `Lᵖ` jet of a test section is represented by its jet. -/
theorem coeFn_lpJet (ξ : testSection V) :
    lpJet V p ξ =ᵐ[stripMeasure] jet (ξ : ℝ × ℝ → V) :=
  MemLp.coeFn_toLp (memLp_jet_of_mem_testSection ξ.property p)

/-- The norm of the `Lᵖ` jet of a test section is the `Lᵖ` norm of its jet on the strip. -/
theorem norm_lpJet (ξ : testSection V) :
    ‖lpJet V p ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) p stripMeasure).toReal :=
  Lp.norm_toLp _ (memLp_jet_of_mem_testSection ξ.property p)

/-- For `p = 2`, the `Lᵖ` jet is the `L²` jet of `TauCeti.StripSobolev.jetLp`. -/
theorem lpJet_two : lpJet V 2 = StripSobolev.jetLp (testSection V) :=
  LinearMap.ext fun _ ↦ by rw [StripSobolev.jetLp_apply]; rfl

variable [Fact (1 ≤ p)]

/-- The definition of `W1p`: the closure of the `Lᵖ` jets of test sections. -/
theorem W1p_def : W1p V p = (LinearMap.range (lpJet V p)).topologicalClosure :=
  (rfl)

/-- `W1p V p` is the closure of the set of `Lᵖ` jets of test sections. -/
theorem coe_W1p :
    (W1p V p : Set (Lp (V × V × V) p stripMeasure)) = closure (Set.range (lpJet V p)) := by
  rw [W1p_def, Submodule.topologicalClosure_coe, LinearMap.coe_range]

/-- `W1p V p` is a closed subspace of `Lᵖ`. -/
theorem isClosed_W1p : IsClosed (W1p V p : Set (Lp (V × V × V) p stripMeasure)) :=
  Submodule.isClosed_topologicalClosure _

/-- `W1p V p` is complete: it is a closed subspace of the complete space `Lᵖ`. -/
instance [CompleteSpace V] : CompleteSpace (W1p V p) :=
  Submodule.topologicalClosure.completeSpace _

/-- The `Lᵖ` jet of a test section lies in `W1p V p`. -/
theorem lpJet_mem_W1p (ξ : testSection V) : lpJet V p ξ ∈ W1p V p :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ ξ)

variable (p) in
/-- The jet of a test section, as an element of `W1p V p`. -/
def toW1p : testSection V →ₗ[ℝ] W1p V p :=
  (lpJet V p).codRestrict (W1p V p) lpJet_mem_W1p

@[simp]
theorem coe_toW1p (ξ : testSection V) :
    (toW1p p ξ : Lp (V × V × V) p stripMeasure) = lpJet V p ξ :=
  (rfl)

/-- The norm of the jet of a test section in `W1p V p` is the `Lᵖ` norm of its jet on the
strip. -/
theorem norm_toW1p (ξ : testSection V) :
    ‖toW1p p ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) p stripMeasure).toReal := by
  rw [← Submodule.norm_coe, coe_toW1p, norm_lpJet]

/-- The jets of test sections are dense in `W1p V p`. -/
theorem denseRange_toW1p : DenseRange (toW1p (V := V) p) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact coe_W1p.subset

/-- A closed subset of `W1p V p` containing the jets of all test sections is everything. -/
theorem W1p_induction {P : W1p V p → Prop} (hP : IsClosed {x | P x})
    (h : ∀ ξ : testSection V, P (toW1p p ξ)) (x : W1p V p) : P x :=
  denseRange_toW1p.induction_on x hP h

/-- **`W^{1,2}` is `H1`.** For `p = 2`, `W1p` is the Sobolev space
`TauCeti.CylinderSobolev.H1` of the cylinder. -/
theorem W1p_two : W1p V 2 = H1 V := by
  rw [W1p_def, lpJet_two]
  exact (StripSobolev.jetClosure_def _).symm

variable (p) in
/-- The value `(ξ, ξ_s, ξ_t) ↦ ξ` of an element of `W1p V p`, in `Lᵖ(ℝ × [0, 1], V)`. -/
def valueLp : W1p V p →L[ℝ] Lp V p stripMeasure :=
  ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL p stripMeasure).comp (W1p V p).subtypeL

/-- The value of an element of `W1p V p` is represented by the first component of its jet. -/
theorem coeFn_valueLp (x : W1p V p) :
    valueLp p x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) p stripMeasure) z).1 :=
  (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL _

/-- The value of the jet of a test section is the test section. -/
theorem valueLp_toW1p_ae_eq (ξ : testSection V) :
    valueLp p (toW1p p ξ) =ᵐ[stripMeasure] (ξ : ℝ × ℝ → V) := by
  filter_upwards [coeFn_valueLp (toW1p p ξ), coeFn_lpJet (p := p) ξ] with z h₁ h₂
  rw [h₁, coe_toW1p, h₂, StripSobolev.jet_apply]

/-! ### Translation along the cylinder -/

/-- The translate of the `Lᵖ` jet of a test section is the `Lᵖ` jet of its translate. -/
theorem translateLp_lpJet (a : ℝ) (ξ : testSection V) :
    StripSobolev.translateLp a (lpJet V p ξ) =
      lpJet V p ⟨_, comp_add_right_mem_testSection ξ.property a⟩ := by
  refine Lp.ext ?_
  filter_upwards [StripSobolev.coeFn_translateLp a (lpJet V p ξ),
    (StripSobolev.measurePreserving_add_strip a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_lpJet (p := p) ξ),
    coeFn_lpJet (p := p) ⟨_, comp_add_right_mem_testSection ξ.property a⟩] with z h₁ h₂ h₃
  rw [h₁, h₃, StripSobolev.jet_comp_add_right]
  exact h₂

/-- Translation along the cylinder maps `W1p V p` into itself. -/
theorem translateLp_mem_W1p (a : ℝ) {f : Lp (V × V × V) p stripMeasure} (hf : f ∈ W1p V p) :
    StripSobolev.translateLp a f ∈ W1p V p := by
  have h : closure (Set.range (lpJet V p)) ⊆
      StripSobolev.translateLp a ⁻¹' (W1p V p : Set (Lp (V × V × V) p stripMeasure)) := by
    refine closure_minimal ?_ (isClosed_W1p.preimage (StripSobolev.translateLp a).continuous)
    rintro _ ⟨ξ, rfl⟩
    rw [mem_preimage, translateLp_lpJet]
    exact lpJet_mem_W1p _
  exact h (by rw [← coe_W1p]; exact hf)

variable (p) in
/-- Translation by `a` along the cylinder, `x ↦ x (· + a, ·)`, as a linear isometric equivalence
of `W1p V p`: the `W^{1,p}` norm of the cylinder is invariant under translation. Its inverse is
translation by `-a` (`TauCeti.CylinderSobolev.translateW1p_symm`). -/
def translateW1p (a : ℝ) : W1p V p ≃ₗᵢ[ℝ] W1p V p :=
  ((StripSobolev.translateLp a).submoduleMap (W1p V p)).trans <|
    LinearIsometryEquiv.ofEq _ _ <| le_antisymm
      (Submodule.map_le_iff_le_comap.2 fun _ ↦ translateLp_mem_W1p a)
      fun f hf ↦ ⟨_, translateLp_mem_W1p (-a) hf, by simp⟩

/-- Translation on `W1p V p` is translation of `Lᵖ` jets. -/
@[simp]
theorem coe_translateW1p (a : ℝ) (x : W1p V p) :
    (translateW1p p a x : Lp (V × V × V) p stripMeasure) = StripSobolev.translateLp a x :=
  (rfl)

/-- The translate of the jet of a test section is the jet of its translate. -/
theorem translateW1p_toW1p (a : ℝ) (ξ : testSection V) :
    translateW1p p a (toW1p p ξ) = toW1p p ⟨_, comp_add_right_mem_testSection ξ.property a⟩ :=
  Subtype.ext (translateLp_lpJet a ξ)

/-- The inverse of translation by `a` on `W1p V p` is translation by `-a`. -/
@[simp]
theorem translateW1p_symm (a : ℝ) :
    (translateW1p (V := V) p a).symm = translateW1p p (-a) :=
  LinearIsometryEquiv.ext fun x ↦ (translateW1p p a).symm_apply_eq.2 <| Subtype.ext <| by simp

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
  have h := (show Function.Periodic (fun t ↦ ξ (s, t)) 1 from hper s).sub_int_mul_eq
    (x := t) ⌊t⌋
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
  have hfin := (memLp_jet_of_mem_testSection ξ.property p).eLpNorm_ne_top
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
(`TauCeti.CylinderSobolev.valueLp_ae_eq_continuousValue`). For `p ≤ 2` or `p = ∞` it is `0`, by
the convention of `LinearMap.extendOfNorm`. -/
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
theorem valueLp_ae_eq_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    valueLp p x =ᵐ[stripMeasure] continuousValue p x := by
  obtain ⟨ξ, hξ⟩ := exists_seq_tendsto_toW1p x
  -- The values converge in `Lᵖ`, so a subsequence converges almost everywhere.
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((valueLp p).continuous.tendsto x).comp hξ)).exists_seq_tendsto_ae
  -- The continuous representatives converge uniformly, so pointwise.
  have hcont := ((continuousValue p).continuous.tendsto x).comp hξ
  filter_upwards [hns, ae_all_iff.2 fun n ↦ valueLp_toW1p_ae_eq (p := p) (ξ (ns n))]
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
  refine W1p_induction (P := fun x ↦ continuousValue p x (s, t + 1) = continuousValue p x (s, t))
    (isClosed_eq (continuous_eval_const_continuousValue _)
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
  obtain ⟨-, -, R, hR⟩ := mem_testSection_iff.1 (ξ n).property
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ᶠ z : ℝ × ℝ in comap Prod.fst (cocompact ℝ), R < |z.1| :=
    tendsto_comap.eventually ((tendsto_norm_cocompact_atTop.eventually_gt_atTop R).mono
      fun s hs ↦ by rwa [Real.norm_eq_abs] at hs)
  filter_upwards [hev] with z hz
  exact (hR z.1 z.2 hz.le).symm

/-- **The Sobolev embedding commutes with translation**: the continuous representative of the
translate of an element of `W1p V p` is the translate of its continuous representative. -/
theorem continuousValue_translateW1p (hp : 2 < p) (hpt : p ≠ ∞) (a : ℝ) (x : W1p V p)
    (z : ℝ × ℝ) : continuousValue p (translateW1p p a x) z = continuousValue p x (z + (a, 0)) := by
  refine W1p_induction
    (P := fun x ↦ continuousValue p (translateW1p p a x) z = continuousValue p x (z + (a, 0)))
    (isClosed_eq ((continuous_eval_const_continuousValue z).comp (translateW1p p a).continuous)
      (continuous_eval_const_continuousValue _)) (fun ξ ↦ ?_) x
  rw [translateW1p_toW1p, coe_continuousValue_toW1p hp hpt, coe_continuousValue_toW1p hp hpt]

end Embedding

end TauCeti.CylinderSobolev
