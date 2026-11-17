/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Sobolev space `W^{1,2}` on the strip with linear boundary conditions

Let `V` be a real normed space and `L₀`, `L₁` two subspaces of `V`. Sections of the trivial
bundle with fibre `V` over the strip `ℝ × [0, 1]` with boundary values in `L₀` along `t = 0` and
in `L₁` along `t = 1` are the domain of the linearized Floer operators of strips with Lagrangian,
or more generally totally real, boundary conditions. This file sets up the Sobolev space of such
sections, the strip counterpart of `TauCeti.CylinderSobolev.H1`.

* **Test sections** (`TauCeti.StripSobolev.testSection L₀ L₁`) are the compactly supported `C²`
  maps `ξ : ℝ × ℝ → V` with `ξ (s, 0) ∈ L₀` and `ξ (s, 1) ∈ L₁` for every `s`. Only their values on
  the strip matter below.
* The jet `(ξ, ∂s ξ, ∂t ξ)` (`TauCeti.CylinderSobolev.jet`) of a test section is square integrable
  on the strip (`TauCeti.StripSobolev.memLp_jet`), for the Lebesgue measure
  `TauCeti.CylinderSobolev.stripMeasure` of `ℝ × [0, 1]`. This gives the linear map
  `TauCeti.StripSobolev.jetₗ` into `L²(ℝ × [0, 1], V × V × V)`, whose norm is the `W^{1,2}` norm
  up to a factor between `1` and `√3`.
* `TauCeti.StripSobolev.H1 L₀ L₁` is the closure of the jets of test sections: the completion of
  the test sections in the `W^{1,2}` norm, realized inside `L²` as a closed subspace, hence
  complete when `V` is.
* **Translation invariance.** Translation in the `s` direction, `ξ ↦ ξ (· + a, ·)`, preserves the
  test sections and acts on `L²` jets as an isometry
  (`TauCeti.StripSobolev.translateL`, `TauCeti.StripSobolev.translateL_jetₗ`). It maps `H1 L₀ L₁`
  onto itself (`TauCeti.StripSobolev.translateL_mem_H1_iff`), so the `W^{1,2}` norm of a section
  and of its translates agree (`TauCeti.StripSobolev.norm_jetₗ_translate`). This is the
  translation-invariant norm of the strip, which a norm built from one compact piece of the strip
  does not have.

The boundary conditions are imposed on the test sections; they hold for the elements of `H1` in
the sense of this closure. First-order operators with essentially bounded coefficients act on the
`L²` jets by `TauCeti.CylinderSobolev.jetOperator`, which only depends on the strip and not on the
periodicity of the cylinder. For linear isotropic boundary conditions the Cauchy–Riemann operator
`∂s + J ∂t` on `H1 L₀ L₁` is studied in `TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Strip`.

## Main definitions

* `TauCeti.StripSobolev.testSection L₀ L₁`: the test sections with boundary values in `L₀`, `L₁`.
* `TauCeti.StripSobolev.jetₗ`: the `L²` jet of a test section.
* `TauCeti.StripSobolev.H1 L₀ L₁`: the Sobolev space `W^{1,2}` of the strip with these boundary
  conditions.
* `TauCeti.StripSobolev.translateL a`: translation by `a` in the `s` direction on `L²` jets.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B
  and Section 3.1, on Sobolev spaces of sections with totally real boundary conditions.
* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), Section 3, on the Sobolev completion of sections over the strip with Lagrangian boundary
  conditions.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

open CylinderSobolev (stripMeasure jet jet_apply jet_smul jet_comp_add_right
  measurePreserving_add_right_stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {L₀ L₁ : Submodule ℝ V}

variable (L₀ L₁) in
/-- The test sections over the strip with boundary values in `L₀` and `L₁`: the compactly
supported `C²` maps `ξ : ℝ × ℝ → V` with `ξ (s, 0) ∈ L₀` and `ξ (s, 1) ∈ L₁` for every `s`. -/
def testSection : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ HasCompactSupport ξ ∧ (∀ s, ξ (s, 0) ∈ L₀) ∧
    ∀ s, ξ (s, 1) ∈ L₁}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, fun _ ↦ L₀.zero_mem,
    fun _ ↦ L₁.zero_mem⟩
  add_mem' := by
    rintro ξ η ⟨hξ, hξc, hξ₀, hξ₁⟩ ⟨hη, hηc, hη₀, hη₁⟩
    exact ⟨hξ.add hη, hξc.add hηc, fun s ↦ L₀.add_mem (hξ₀ s) (hη₀ s),
      fun s ↦ L₁.add_mem (hξ₁ s) (hη₁ s)⟩
  smul_mem' := by
    rintro c ξ ⟨hξ, hξc, hξ₀, hξ₁⟩
    exact ⟨contDiff_const.smul hξ, hξc.smul_left, fun s ↦ L₀.smul_mem c (hξ₀ s),
      fun s ↦ L₁.smul_mem c (hξ₁ s)⟩

/-- Membership in the test sections. -/
theorem mem_testSection_iff {ξ : ℝ × ℝ → V} : ξ ∈ testSection L₀ L₁ ↔
    ContDiff ℝ 2 ξ ∧ HasCompactSupport ξ ∧ (∀ s, ξ (s, 0) ∈ L₀) ∧ ∀ s, ξ (s, 1) ∈ L₁ :=
  Iff.rfl

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a test section is continuous. -/
theorem continuous_jet (hξ : ξ ∈ testSection L₀ L₁) : Continuous (jet ξ) := by
  have hξ2 := (mem_testSection_iff.1 hξ).1
  have h := hξ2.continuous_fderiv (by norm_num)
  have h0 := hξ2.continuous
  simp only [funext (jet_apply ξ)]
  fun_prop

/-- The jet of a test section has compact support: it vanishes off the support of the section. -/
theorem hasCompactSupport_jet (hξ : ξ ∈ testSection L₀ L₁) : HasCompactSupport (jet ξ) := by
  refine (mem_testSection_iff.1 hξ).2.1.mono' fun z hz ↦ ?_
  by_contra h
  exact hz (by simp [jet_apply, image_eq_zero_of_notMem_tsupport h,
    fderiv_of_notMem_tsupport ℝ h])

/-- The jet is additive on test sections. -/
theorem jet_add (hξ : ξ ∈ testSection L₀ L₁) (hη : η ∈ testSection L₀ L₁) :
    jet (ξ + η) = jet ξ + jet η := by
  funext z
  have h₁ := ((mem_testSection_iff.1 hξ).1.differentiable (by norm_num)) z
  have h₂ := ((mem_testSection_iff.1 hη).1.differentiable (by norm_num)) z
  simp [jet_apply, fderiv_add h₁ h₂]

/-- The jet of a test section is square integrable on the strip. -/
theorem memLp_jet (hξ : ξ ∈ testSection L₀ L₁) : MemLp (jet ξ) 2 stripMeasure :=
  (continuous_jet hξ).memLp_of_hasCompactSupport (hasCompactSupport_jet hξ)

variable (L₀ L₁) in
/-- The `L²` jet `(ξ, ∂s ξ, ∂t ξ)` of a test section, as a linear map into
`L²(ℝ × [0, 1], V × V × V)`. -/
def jetₗ : testSection L₀ L₁ →ₗ[ℝ] Lp (V × V × V) 2 stripMeasure where
  toFun ξ := (memLp_jet ξ.2).toLp (jet (ξ : ℝ × ℝ → V))
  map_add' ξ η := by
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_add ξ.2 η.2])
  map_smul' c ξ := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_smul])

/-- The `L²` jet of a test section is represented by its jet. -/
theorem coeFn_jetₗ (ξ : testSection L₀ L₁) :
    jetₗ L₀ L₁ ξ =ᵐ[stripMeasure] jet (ξ : ℝ × ℝ → V) :=
  MemLp.coeFn_toLp (memLp_jet ξ.2)

/-- The `L²` jet of a test section is the class of its jet. -/
theorem jetₗ_apply (ξ : testSection L₀ L₁) :
    jetₗ L₀ L₁ ξ = (memLp_jet ξ.2).toLp (jet (ξ : ℝ × ℝ → V)) :=
  (rfl)

/-- The squared norm of the `L²` jet of a test section is the integral of the squared norm of its
jet over the strip. -/
theorem sq_norm_jetₗ (ξ : testSection L₀ L₁) :
    ‖jetₗ L₀ L₁ ξ‖ ^ 2 = ∫ z, ‖jet (ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure := by
  rw [jetₗ_apply, (memLp_jet ξ.2).norm_toLp_sq]

variable (L₀ L₁) in
/-- The Sobolev space `W^{1,2}` of the strip `ℝ × [0, 1]` with boundary values in `L₀` and `L₁`:
the closure in `L²(ℝ × [0, 1], V × V × V)` of the jets of test sections, that is, the completion
of the test sections in the `W^{1,2}` norm. An element is an `L²` jet `(ξ, ξ_s, ξ_t)`. -/
def H1 : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  (LinearMap.range (jetₗ L₀ L₁)).topologicalClosure

/-- The definition of `H1`: the closure of the span of the jets of test sections. -/
theorem H1_def : H1 L₀ L₁ = (LinearMap.range (jetₗ L₀ L₁)).topologicalClosure :=
  (rfl)

/-- `H1` is the closure of the set of jets of test sections. -/
theorem coe_H1 :
    (H1 L₀ L₁ : Set (Lp (V × V × V) 2 stripMeasure)) = closure (Set.range (jetₗ L₀ L₁)) := by
  rw [H1_def, Submodule.topologicalClosure_coe, LinearMap.coe_range]

/-- A closed set containing the jets of all test sections contains `H1`. -/
theorem H1_subset_of_isClosed {S : Set (Lp (V × V × V) 2 stripMeasure)} (hS : IsClosed S)
    (h : Set.range (jetₗ L₀ L₁) ⊆ S) : (H1 L₀ L₁ : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ S := by
  rw [coe_H1]
  exact closure_minimal h hS

/-- `H1` is a closed subspace of `L²`. -/
theorem isClosed_H1 : IsClosed (H1 L₀ L₁ : Set (Lp (V × V × V) 2 stripMeasure)) :=
  Submodule.isClosed_topologicalClosure _

/-- `H1` is complete: it is a closed subspace of the complete space `L²`. -/
instance [CompleteSpace V] : CompleteSpace (H1 L₀ L₁) :=
  Submodule.topologicalClosure.completeSpace _

/-- The jet of a test section lies in `H1`. -/
theorem jetₗ_mem_H1 (ξ : testSection L₀ L₁) : jetₗ L₀ L₁ ξ ∈ H1 L₀ L₁ :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ ξ)

/-- The jets of test sections are dense in `H1`. -/
theorem denseRange_codRestrict_jetₗ :
    DenseRange ((jetₗ L₀ L₁).codRestrict (H1 L₀ L₁) jetₗ_mem_H1) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact coe_H1.subset

/-! ### Translation in the `s` direction -/

/-- The translate `ξ (· + a, ·)` of a test section is a test section. -/
theorem comp_add_right_mem_testSection (hξ : ξ ∈ testSection L₀ L₁) (a : ℝ) :
    (fun z ↦ ξ (z + (a, 0))) ∈ testSection L₀ L₁ := by
  obtain ⟨hξ2, hξc, hξ₀, hξ₁⟩ := mem_testSection_iff.1 hξ
  refine ⟨hξ2.comp (contDiff_id.add contDiff_const), ?_, fun s ↦ by simpa using hξ₀ (s + a),
    fun s ↦ by simpa using hξ₁ (s + a)⟩
  exact hξc.comp_homeomorph (Homeomorph.addRight ((a, 0) : ℝ × ℝ))

variable (V) in
/-- Translation by `a` in the `s` direction on `L²` jets on the strip,
`f ↦ f (· + a, ·)`. It is a linear isometry (`TauCeti.StripSobolev.norm_translateL`). -/
def translateL (a : ℝ) : Lp (V × V × V) 2 stripMeasure →L[ℝ] Lp (V × V × V) 2 stripMeasure :=
  (Lp.compMeasurePreservingₗᵢ ℝ _
    (measurePreserving_add_right_stripMeasure a)).toContinuousLinearMap

/-- Translation acts on representatives by composition. -/
theorem coeFn_translateL (a : ℝ) (f : Lp (V × V × V) 2 stripMeasure) :
    translateL V a f =ᵐ[stripMeasure] fun z ↦ f (z + (a, 0)) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Translation preserves the norm of `L²` jets. -/
@[simp]
theorem norm_translateL (a : ℝ) (f : Lp (V × V × V) 2 stripMeasure) :
    ‖translateL V a f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- Translation by `a + b` is translation by `b` followed by translation by `a`. -/
theorem translateL_add (a b : ℝ) (f : Lp (V × V × V) 2 stripMeasure) :
    translateL V (a + b) f = translateL V a (translateL V b f) := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_translateL (a + b) f, coeFn_translateL a (translateL V b f),
    (measurePreserving_add_right_stripMeasure a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateL b f)] with z h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃]
  congr 1
  ext <;> simp [add_assoc]

/-- Translation by `0` is the identity. -/
@[simp]
theorem translateL_zero (f : Lp (V × V × V) 2 stripMeasure) : translateL V 0 f = f := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_translateL 0 f] with z h
  rw [h, Prod.mk_zero_zero, add_zero]

/-- The translate of the `L²` jet of a test section is the `L²` jet of its translate. -/
theorem translateL_jetₗ (a : ℝ) (ξ : testSection L₀ L₁) :
    translateL V a (jetₗ L₀ L₁ ξ) =
      jetₗ L₀ L₁ ⟨_, comp_add_right_mem_testSection ξ.2 a⟩ := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_translateL a (jetₗ L₀ L₁ ξ),
    (measurePreserving_add_right_stripMeasure a).quasiMeasurePreserving.ae_eq_comp (coeFn_jetₗ ξ),
    coeFn_jetₗ ⟨_, comp_add_right_mem_testSection ξ.2 a⟩] with z h₁ h₂ h₃
  rw [h₁, h₃, jet_comp_add_right]
  exact h₂

/-- Translation maps `H1` into itself. -/
theorem translateL_mem_H1 (a : ℝ) {f : Lp (V × V × V) 2 stripMeasure} (hf : f ∈ H1 L₀ L₁) :
    translateL V a f ∈ H1 L₀ L₁ := by
  have h : (H1 L₀ L₁ : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ translateL V a ⁻¹' H1 L₀ L₁ :=
    H1_subset_of_isClosed (isClosed_H1.preimage (translateL V a).continuous) <| by
      rintro _ ⟨ξ, rfl⟩
      rw [mem_preimage, translateL_jetₗ]
      exact jetₗ_mem_H1 _
  exact h hf

/-- An `L²` jet lies in `H1` exactly when its translate does: translation maps `H1` onto
itself. -/
theorem translateL_mem_H1_iff (a : ℝ) {f : Lp (V × V × V) 2 stripMeasure} :
    translateL V a f ∈ H1 L₀ L₁ ↔ f ∈ H1 L₀ L₁ := by
  refine ⟨fun h ↦ ?_, translateL_mem_H1 a⟩
  have := translateL_mem_H1 (-a) h
  rwa [← translateL_add, neg_add_cancel, translateL_zero] at this

/-- **The `W^{1,2}` norm on the strip is translation invariant**: a test section and its
translate in the `s` direction have `L²` jets of the same norm. -/
theorem norm_jetₗ_translate (a : ℝ) (ξ : testSection L₀ L₁) :
    ‖jetₗ L₀ L₁ ⟨_, comp_add_right_mem_testSection ξ.2 a⟩‖ = ‖jetₗ L₀ L₁ ξ‖ := by
  rw [← translateL_jetₗ, norm_translateL]

end TauCeti.StripSobolev
