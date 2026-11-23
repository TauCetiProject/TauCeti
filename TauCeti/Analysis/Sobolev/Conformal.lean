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
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.Sobolev.JetOperator
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# The Sobolev space `W^{1,2}_0` of a planar domain with a conformal metric

Let `U ⊆ ℝ × ℝ` be open and let `ρ` be continuous and positive on `U`
(`TauCeti.ConformalSobolev.IsWeight`). The conformal metric `ρ (ds² + dt²)` on `U` has volume form
`ρ ds dt`, and the density `|dξ|²` of the differential of a map `ξ : U → V` in this metric is
`ρ⁻¹ (‖∂s ξ‖² + ‖∂t ξ‖²)`. In the `W^{1,2}` norm of this metric the two factors of `ρ` cancel in
the derivative term, because the Dirichlet energy of a surface is conformally invariant, and only
the zeroth-order term sees the metric:

`‖ξ‖²_{W^{1,2}} = ∫_U (‖∂s ξ‖² + ‖∂t ξ‖² + ρ ‖ξ‖²) ds dt`.

A Riemann surface with cylindrical ends embedded in the plane, such as the pair of pants
`ℂ ∖ {0, 1}` of Floer theory, is of this form: the cylindrical metric is `ρ |dw|²` for a weight `ρ`
blowing up like `|w - c|⁻²` at the punctures `c` (see
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev`). This file sets up the Sobolev space in
the plane coordinates, as the linearized Floer operator `ξ ↦ ∂s ξ + J ∂t ξ + A ξ` is written in
`TauCeti.Geometry.Symplectic.Floer.Linearization`, and the functional analysis that turns an
elliptic estimate on such a domain into finite-dimensional kernel and closed range.

* **Test sections** (`TauCeti.ConformalSobolev.testSection`) are the `C²` maps `ξ : ℝ × ℝ → V`
  with compact support inside `U`.
* The **jet** of a section is `jet ρ ξ = (√ρ ξ, ∂s ξ, ∂t ξ)`, whose squared `L²` norm on `U` is at
  most the squared `W^{1,2}` norm above (`TauCeti.ConformalSobolev.sq_norm_le_integral`). The jets
  of test sections are square integrable (`TauCeti.ConformalSobolev.memLp_jet`), and their classes
  form the subspace `TauCeti.ConformalSobolev.jetSubmodule` of `L²(U, V × V × V)`.
* `TauCeti.ConformalSobolev.H1` is its closure, the completion of the test sections in a norm
  equivalent to the `W^{1,2}` norm, that is, the Sobolev space `W^{1,2}_0(U, V)`; it is a
  closed subspace of `L²` and hence complete. An element is an `L²` jet `(η, ξ_s, ξ_t)` whose
  **weighted value** `η = √ρ ξ` determines it
  (`TauCeti.ConformalSobolev.weightedValueL_injective`): the derivative components are the weak
  derivatives of `ξ = η / √ρ` on `U`, which vanish where `η` does.
* **Rellich's theorem.** On a compact set `K ⊆ U` the weighted value is a compact operator from
  `H1` to `L²(K)`
  (`TauCeti.ConformalSobolev.isCompactOperator_restrictWeightedValue_comp_subtypeL`). A smooth
  cutoff equal to `1` on `K` and supported in `U` turns the test sections of bounded norm
  into sections of the plane of bounded `W^{1,2}(ℝ²)` norm supported in a fixed compact set, to
  which the Fréchet–Kolmogorov criterion `TauCeti.totallyBounded_of_contDiff_of_eLpNorm_fderiv_le`
  applies; on `K` the weight `√ρ` is a bounded multiplier.
* **Weighted values on compact sets.** The restricted weighted value of the jet of `ξ` has squared
  norm `∫_K ρ ‖ξ‖²` (`TauCeti.ConformalSobolev.norm_restrictWeightedValue_sq`); since `ρ` is bounded
  below on a compact set `K ⊆ U`, it controls the `L²` norm of `ξ` over `K`
  (`TauCeti.ConformalSobolev.exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq`).
* **First-order operators.** A coefficient field `M : U → L(V × V × V, W)`, essentially bounded on
  `U`, acts on `L²` jets by `f ↦ M f` (`TauCeti.jetOperator (volume.restrict U) M`). On the jet
  of a test section `ξ` this is the first-order operator `ξ ↦ M (√ρ ξ, ∂s ξ, ∂t ξ)`
  (`TauCeti.ConformalSobolev.jetOperator_toLp_jet_ae_eq`), and its restriction to `H1` is the
  realization of that operator from `W^{1,2}_0(U, V)` to `L²(U, W)`.
* **Peetre's argument.** An operator `D` on `H1` satisfying an estimate
  `‖x‖ ≤ C (‖D x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x` of test sections `ξ` has finite-dimensional
  kernel (`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`) and closed range
  (`TauCeti.ConformalSobolev.isClosed_range_of_estimate`), by Rellich's theorem and
  `ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on surfaces with cylindrical ends, Rellich's theorem and the
  semi-Fredholm estimate.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.16 (Rellich–Kondrachov) and Theorem 4.26 (Fréchet–Kolmogorov).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace TauCeti.ConformalSobolev

/-- A **conformal weight** on a set `U` of the plane: `U` is open, and `ρ` is continuous and
positive on `U`. It is the conformal factor of the metric `ρ (ds² + dt²)` on `U`. -/
structure IsWeight (U : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : Prop where
  isOpen : IsOpen U
  continuousOn : ContinuousOn ρ U
  pos : ∀ z ∈ U, 0 < ρ z

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}

/-! ### Test sections and their jets -/

variable (V) in
/-- The test sections over `U`: `C²` maps `ξ : ℝ × ℝ → V` with compact support inside `U`. -/
def testSection (U : Set (ℝ × ℝ)) : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro ξ η ⟨hξ, hξc, hξU⟩ ⟨hη, hηc, hηU⟩
    exact ⟨hξ.add hη, hξc.add hηc, (tsupport_add ξ η).trans (union_subset hξU hηU)⟩
  smul_mem' := by
    rintro c ξ ⟨hξ, hξc, hξU⟩
    exact ⟨contDiff_const.smul hξ, hξc.smul_left (f := fun _ ↦ c),
      (tsupport_smul_subset_right (fun _ ↦ c) ξ).trans hξU⟩

/-- Membership in the test sections. -/
theorem mem_testSection_iff {ξ : ℝ × ℝ → V} :
    ξ ∈ testSection V U ↔ ContDiff ℝ 2 ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U :=
  Iff.rfl

/-- The jet `(√ρ ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V` for the weight `ρ`. -/
def jet (ρ : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V :=
  (√(ρ z) • ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))

/-- The components of the jet. -/
theorem jet_apply (ρ : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    jet ρ ξ z = (√(ρ z) • ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) :=
  (rfl)

variable {ξ η : ℝ × ℝ → V}

/-- The jet is additive on differentiable maps. -/
theorem jet_add (hξ : Differentiable ℝ ξ) (hη : Differentiable ℝ η) :
    jet ρ (ξ + η) = jet ρ ξ + jet ρ η := by
  funext z
  simp [jet, fderiv_add (hξ z) (hη z)]

/-- The jet commutes with scalar multiplication. -/
theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) : jet ρ (c • ξ) = c • jet ρ ξ := by
  funext z
  simp [jet, fderiv_const_smul_field, smul_comm c]

/-- The jet of a map vanishes outside its topological support. -/
theorem jet_eq_zero_of_notMem_tsupport {z : ℝ × ℝ} (hz : z ∉ tsupport ξ) : jet ρ ξ z = 0 := by
  have h : ξ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz
  simp [jet, h.fderiv_eq, h.eq_of_nhds]

/-- The support of the jet lies in the topological support of the map. -/
theorem support_jet_subset (ρ : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V) :
    Function.support (jet ρ ξ) ⊆ tsupport ξ := fun _ hz ↦ by
  by_contra h
  exact hz (jet_eq_zero_of_notMem_tsupport h)

/-- The jet of a test section is continuous. -/
theorem continuous_jet (hρ : IsWeight U ρ) (hξ : ξ ∈ testSection V U) :
    Continuous (jet ρ ξ) := by
  obtain ⟨hξ2, -, hξU⟩ := mem_testSection_iff.1 hξ
  have hd := hξ2.continuous_fderiv (by norm_num)
  have h₀ : Continuous fun z ↦ √(ρ z) • ξ z :=
    (((hρ.continuousOn.sqrt).smul hξ2.continuous.continuousOn)).continuous_of_tsupport_subset
      hρ.isOpen ((tsupport_smul_subset_right _ ξ).trans hξU)
  exact h₀.prodMk ((hd.clm_apply continuous_const).prodMk (hd.clm_apply continuous_const))

/-- The jet of a test section has compact support. -/
theorem hasCompactSupport_jet (hξ : ξ ∈ testSection V U) : HasCompactSupport (jet ρ ξ) :=
  (mem_testSection_iff.1 hξ).2.1.mono' (support_jet_subset ρ ξ)

/-- The jet of a test section is square integrable on `U`. -/
theorem memLp_jet (hρ : IsWeight U ρ) (hξ : ξ ∈ testSection V U) :
    MemLp (jet ρ ξ) 2 (volume.restrict U) :=
  (continuous_jet hρ hξ).memLp_of_hasCompactSupport (hasCompactSupport_jet hξ)

/-- The squared norm of a jet is at most the `W^{1,2}` density
`ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²`. -/
theorem sq_norm_jet_le {z : ℝ × ℝ} (hz : 0 ≤ ρ z) (ξ : ℝ × ℝ → V) :
    ‖jet ρ ξ z‖ ^ 2 ≤ ρ z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 := by
  have h₀ : ‖√(ρ z) • ξ z‖ ^ 2 = ρ z * ‖ξ z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hz]
  rw [← h₀]
  simp only [jet, Prod.norm_def]
  set a := ‖√(ρ z) • ξ z‖
  set b := ‖fderiv ℝ ξ z (1, 0)‖
  set c := ‖fderiv ℝ ξ z (0, 1)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  rcases max_choice a (max b c) with h | h <;> rw [h]
  · nlinarith [ha, hb, hc]
  · rcases max_choice b c with h' | h' <;> rw [h'] <;> nlinarith [ha, hb, hc]

/-! ### The Sobolev space -/

variable (V U ρ) in
/-- The `L²` classes of the jets of test sections, a subspace of `L²(U, V × V × V)`. -/
def jetSubmodule : Submodule ℝ (Lp (V × V × V) 2 (volume.restrict U)) where
  carrier := {f | ∃ ξ ∈ testSection V U, f =ᵐ[volume.restrict U] jet ρ ξ}
  zero_mem' := ⟨0, zero_mem _, (Lp.coeFn_zero _ _ _).trans (Eventually.of_forall fun z ↦ by
    simp [jet, Prod.zero_eq_mk])⟩
  add_mem' := by
    rintro f g ⟨ξ, hξ, hf⟩ ⟨η, hη, hg⟩
    refine ⟨ξ + η, add_mem hξ hη, (Lp.coeFn_add f g).trans ((hf.add hg).trans
      (Eventually.of_forall fun z ↦ ?_))⟩
    rw [jet_add ((mem_testSection_iff.1 hξ).1.differentiable (by norm_num))
      ((mem_testSection_iff.1 hη).1.differentiable (by norm_num))]
  smul_mem' := by
    rintro c f ⟨ξ, hξ, hf⟩
    refine ⟨c • ξ, Submodule.smul_mem _ c hξ, (Lp.coeFn_smul c f).trans ?_⟩
    filter_upwards [hf] with z hz
    simp [hz, jet_smul]

/-- Membership in the subspace of jets of test sections. -/
theorem mem_jetSubmodule_iff {f : Lp (V × V × V) 2 (volume.restrict U)} :
    f ∈ jetSubmodule V U ρ ↔ ∃ ξ ∈ testSection V U, f =ᵐ[volume.restrict U] jet ρ ξ :=
  Iff.rfl

/-- The class of the jet of a test section lies in the subspace of jets of test sections. -/
theorem toLp_jet_mem_jetSubmodule (hρ : IsWeight U ρ) (hξ : ξ ∈ testSection V U) :
    (memLp_jet hρ hξ).toLp (jet ρ ξ) ∈ jetSubmodule V U ρ :=
  ⟨ξ, hξ, MemLp.coeFn_toLp _⟩

variable (V U ρ) in
/-- The Sobolev space `W^{1,2}_0(U, V)` of the conformal metric `ρ (ds² + dt²)`: the closure in
`L²(U, V × V × V)` of the jets `(√ρ ξ, ∂s ξ, ∂t ξ)` of test sections, that is, the completion of the
test sections in a norm equivalent to `(∫_U (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²))^{1/2}`. An element is
determined by its weighted value (`TauCeti.ConformalSobolev.weightedValueL_injective`). -/
def H1 : Submodule ℝ (Lp (V × V × V) 2 (volume.restrict U)) :=
  (jetSubmodule V U ρ).topologicalClosure

/-- The definition of `H1`: the closure of the jets of test sections. -/
theorem H1_def : H1 V U ρ = (jetSubmodule V U ρ).topologicalClosure :=
  (rfl)

/-- The jets of test sections lie in `H1`. -/
theorem jetSubmodule_le_H1 : jetSubmodule V U ρ ≤ H1 V U ρ :=
  Submodule.le_topologicalClosure _

/-- `H1` is a closed subspace of `L²`. -/
theorem isClosed_H1 : IsClosed (H1 V U ρ : Set (Lp (V × V × V) 2 (volume.restrict U))) :=
  Submodule.isClosed_topologicalClosure _

/-- `H1` is complete: it is a closed subspace of the complete space `L²`. -/
instance [CompleteSpace V] : CompleteSpace (H1 V U ρ) :=
  Submodule.topologicalClosure.completeSpace _

/-- A closed set containing the jets of all test sections contains `H1`. -/
theorem H1_subset_of_isClosed {S : Set (Lp (V × V × V) 2 (volume.restrict U))} (hS : IsClosed S)
    (h : (jetSubmodule V U ρ : Set (Lp (V × V × V) 2 (volume.restrict U))) ⊆ S) :
    (H1 V U ρ : Set (Lp (V × V × V) 2 (volume.restrict U))) ⊆ S := by
  rw [H1_def, Submodule.topologicalClosure_coe]
  exact closure_minimal h hS

/-- The jets of test sections are dense in `H1`. -/
theorem dense_setOf_mem_jetSubmodule :
    Dense {x : H1 V U ρ | (x : Lp (V × V × V) 2 (volume.restrict U)) ∈ jetSubmodule V U ρ} := by
  rw [Subtype.dense_iff]
  intro f hf
  rw [SetLike.mem_coe, H1_def, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hf
  refine closure_mono (fun g hg ↦ ?_) hf
  exact ⟨⟨g, jetSubmodule_le_H1 hg⟩, hg, rfl⟩

/-- The squared norm of the `L²` jet of a test section is at most its `W^{1,2}` energy
`∫_U (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`. -/
theorem sq_norm_le_integral (hρ : IsWeight U ρ) {f : Lp (V × V × V) 2 (volume.restrict U)}
    (hξ : ξ ∈ testSection V U) (hf : f =ᵐ[volume.restrict U] jet ρ ξ) :
    ‖f‖ ^ 2 ≤ ∫ z in U, (ρ z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) := by
  have hjm := memLp_jet hρ hξ
  have hfj : f = hjm.toLp (jet ρ ξ) := Lp.ext (hf.trans hjm.coeFn_toLp.symm)
  rw [hfj, hjm.norm_toLp_sq]
  have hU := ae_restrict_mem (μ := volume) hρ.isOpen.measurableSet
  have hc := continuous_jet hρ hξ
  -- The energy density agrees on `U` with the sum of the squared norms of the jet components.
  have hg : Integrable (fun z ↦ ‖(jet ρ ξ z).1‖ ^ 2 + ‖(jet ρ ξ z).2.1‖ ^ 2 +
      ‖(jet ρ ξ z).2.2‖ ^ 2) (volume.restrict U) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hasCompactSupport_jet (ρ := ρ) hξ).mono' fun z hz ↦
        subset_tsupport _ fun h ↦ hz (by simp [h]))
  have heq : (fun z ↦ ‖(jet ρ ξ z).1‖ ^ 2 + ‖(jet ρ ξ z).2.1‖ ^ 2 + ‖(jet ρ ξ z).2.2‖ ^ 2)
      =ᵐ[volume.restrict U] fun z ↦ ρ z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 := by
    filter_upwards [hU] with z hz
    simp [jet, norm_smul, mul_pow, Real.sq_sqrt (hρ.pos z hz).le]
  refine integral_mono_ae (hjm.integrable_norm_pow two_ne_zero) (hg.congr heq) ?_
  filter_upwards [hU] with z hz
  exact sq_norm_jet_le (hρ.pos z hz).le ξ

/-! ### The weighted value determines an element of `H1` -/

variable (V U ρ) in
/-- The weighted value `(√ρ ξ, ξ_s, ξ_t) ↦ √ρ ξ` of an element of `H1`, in `L²(U, V)`. It is
injective (`TauCeti.ConformalSobolev.weightedValueL_injective`). -/
def weightedValueL : H1 V U ρ →L[ℝ] Lp V 2 (volume.restrict U) :=
  ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 (volume.restrict U)).comp (H1 V U ρ).subtypeL

/-- The weighted value of an element of `H1` is represented by the first component of its jet. -/
theorem coeFn_weightedValueL (x : H1 V U ρ) :
    weightedValueL V U ρ x =ᵐ[volume.restrict U]
      fun z ↦ ((x : Lp (V × V × V) 2 (volume.restrict U)) z).1 :=
  (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL _

section Value

/-- Integration by parts over `U`: for a test function `φ` supported in `U` and a test section
`ξ`, the integral over `U` of `φ ∂_e ξ + (∂_e φ) ξ` vanishes. -/
private theorem setIntegral_smul_fderiv_add_eq_zero {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hξ : ξ ∈ testSection V U) (e : ℝ × ℝ) :
    (∫ z in U, φ z • fderiv ℝ ξ z e) + ∫ z in U, fderiv ℝ φ z e • ξ z = 0 := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  obtain ⟨hξ2, -, -⟩ := mem_testSection_iff.1 hξ
  have hξ1 : ContDiff ℝ 1 ξ := hξ2.of_le (by norm_num)
  have hdξ := (hξ1.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := e))
  have hdφ := (hφ.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := e))
  have h₁ : Integrable fun z ↦ φ z • fderiv ℝ ξ z e :=
    (hφ.continuous.smul hdξ).integrable_of_hasCompactSupport hφc.smul_right
  have h₂ : Integrable fun z ↦ fderiv ℝ φ z e • ξ z :=
    (hdφ.smul hξ1.continuous).integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) e).smul_right
  have h₃ : Integrable fun z ↦ φ z • ξ z :=
    (hφ.continuous.smul hξ1.continuous).integrable_of_hasCompactSupport hφc.smul_right
  -- Both integrands vanish off `U`, so the integrals over `U` are integrals over the plane.
  have hU : ∀ z ∉ U, φ z • fderiv ℝ ξ z e + fderiv ℝ φ z e • ξ z = 0 := fun z hz ↦ by
    have h : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (hφU h)
    simp [h.fderiv_eq, h.eq_of_nhds]
  rw [← integral_add h₁.restrict h₂.restrict, setIntegral_eq_integral_of_forall_compl_eq_zero hU,
    integral_add h₁ h₂, integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h₂ h₁ h₃
    (fun z _ ↦ hφ.differentiable one_ne_zero z) (fun z _ ↦ hξ1.differentiable one_ne_zero z),
    neg_add_cancel]

/-- The quotient `g / √ρ` of a continuous function `g` with compact support inside `U` is
continuous with compact support. -/
private theorem continuous_div_sqrt (hρ : IsWeight U ρ) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Continuous (fun z ↦ g z / √(ρ z)) ∧ HasCompactSupport (fun z ↦ g z / √(ρ z)) := by
  have hsupp : Function.support (fun z ↦ g z / √(ρ z)) ⊆ tsupport g := fun z hz ↦
    subset_tsupport _ fun h ↦ hz (by simp [h])
  exact ⟨(hg.continuousOn.div hρ.continuousOn.sqrt fun z hz ↦
    (Real.sqrt_pos.2 (hρ.pos z hz)).ne').continuous_of_tsupport_subset hρ.isOpen
      ((closure_minimal hsupp (isClosed_tsupport g)).trans hgU), hgc.mono' hsupp⟩

/-- The weak derivative identity on `H1`: for an `L²` jet `x ∈ H1`, a test function `φ` supported
in `U` and a direction `e`, with `P` the component of the jet recording the derivative in the
direction `e`, `∫_U φ P(x) + ∫_U (∂_e φ / √ρ) x₁ = 0`. -/
private theorem integral_smul_add_eq_zero_of_mem_H1 [CompleteSpace V] (hρ : IsWeight U ρ)
    {x : Lp (V × V × V) 2 (volume.restrict U)} (hx : x ∈ H1 V U ρ) {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) {e : ℝ × ℝ}
    {P : V × V × V →L[ℝ] V} (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ρ ξ z) = fderiv ℝ ξ z e) :
    (∫ z in U, φ z • P (x z)) + ∫ z in U, (fderiv ℝ φ z e / √(ρ z)) • (x z).1 = 0 := by
  obtain ⟨hψc, hψs⟩ := continuous_div_sqrt hρ
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hφc.fderiv_apply (𝕜 := ℝ) e)
    ((tsupport_fderiv_apply_subset ℝ e).trans hφU)
  have hφ₂ : MemLp φ 2 (volume.restrict U) := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hψ₂ : MemLp (fun z ↦ fderiv ℝ φ z e / √(ρ z)) 2 (volume.restrict U) :=
    hψc.memLp_of_hasCompactSupport hψs
  set B : ℝ →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.lsmul ℝ ℝ
  set Λ : Lp (V × V × V) 2 (volume.restrict U) →L[ℝ] V :=
    (B.lpPairing (volume.restrict U) 2 2 (hφ₂.toLp φ)).comp (P.compLpL 2 (volume.restrict U)) +
      (B.lpPairing (volume.restrict U) 2 2 (hψ₂.toLp _)).comp
        ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 (volume.restrict U))
  have hΛ : ∀ f : Lp (V × V × V) 2 (volume.restrict U), Λ f =
      ∫ z, φ z • P (f z) ∂(volume.restrict U) +
        ∫ z, (fderiv ℝ φ z e / √(ρ z)) • (f z).1 ∂(volume.restrict U) := by
    intro f
    simp only [Λ, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.lpPairing_eq_integral]
    congr 1 <;> refine integral_congr_ae ?_
    · filter_upwards [hφ₂.coeFn_toLp, P.coeFn_compLp f] with z h₁ h₂
      simp [B, h₁, h₂]
    · filter_upwards [hψ₂.coeFn_toLp,
        (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLp f] with z h₁ h₂
      simp [B, h₁, h₂]
  -- `Λ` vanishes on the jets of test sections, hence on their closure `H1`.
  have hjet :
      (jetSubmodule V U ρ : Set (Lp (V × V × V) 2 (volume.restrict U))) ⊆ {f | Λ f = 0} := by
    rintro f ⟨ξ, hξ, hf⟩
    rw [mem_ofPred_eq, hΛ, ← setIntegral_smul_fderiv_add_eq_zero hφ hφc hφU hξ e]
    congr 1 <;> refine integral_congr_ae ?_
    · exact hf.mono fun z hz ↦ by simp only [hz, hP]
    · filter_upwards [hf, ae_restrict_mem hρ.isOpen.measurableSet] with z hz hzU
      rw [hz, jet_apply, smul_smul, div_mul_cancel₀ _ (Real.sqrt_pos.2 (hρ.pos z hzU)).ne']
  have hker := H1_subset_of_isClosed (isClosed_eq Λ.continuous continuous_const) hjet hx
  rw [mem_ofPred_eq, hΛ] at hker
  exact hker

/-- **An element of `H1` is determined by its weighted value.** The weighted value map
`(√ρ ξ, ξ_s, ξ_t) ↦ √ρ ξ` is injective on `H1`: if the weighted value of an `L²` jet in `H1`
vanishes, so do its derivative components, as they are the weak derivatives of `ξ` on `U`. Thus
`H1` is a space of sections over `U`, the Sobolev space `W^{1,2}_0(U, V)` of the metric
`ρ (ds² + dt²)`. -/
theorem weightedValueL_injective [CompleteSpace V]
    (hρ : IsWeight U ρ) : Function.Injective (weightedValueL V U ρ) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have hx₁ : ∀ᵐ z ∂(volume.restrict U), ((x : Lp (V × V × V) 2 (volume.restrict U)) z).1 = 0 := by
    have h := coeFn_weightedValueL x
    rw [hx] at h
    filter_upwards [h, Lp.coeFn_zero V 2 (volume.restrict U)] with z h₁ h₂
    simpa using h₁.symm.trans h₂
  -- Each derivative component is orthogonal to every test function, hence vanishes.
  have hcomp : ∀ {e : ℝ × ℝ} {P : V × V × V →L[ℝ] V},
      (∀ (ξ : ℝ × ℝ → V) z, P (jet ρ ξ z) = fderiv ℝ ξ z e) →
      ∀ᵐ z ∂(volume.restrict U), P ((x : Lp (V × V × V) 2 (volume.restrict U)) z) = 0 := by
    intro e P hP
    have hloc : LocallyIntegrableOn (fun z ↦ P ((x : Lp (V × V × V) 2 (volume.restrict U)) z)) U
        (volume.restrict U) :=
      (((memLp_congr_ae (P.coeFn_compLpL (x : Lp (V × V × V) 2 (volume.restrict U)))).1
        (Lp.memLp _)).locallyIntegrable (by norm_num)).locallyIntegrableOn _
    have h := hρ.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun φ hφ hφc hφU ↦ by
      have hint := integral_smul_add_eq_zero_of_mem_H1 hρ x.property (hφ.of_le (by simp)) hφc hφU hP
      have h0 : ∫ z in U, (fderiv ℝ φ z e / √(ρ z)) •
          ((x : Lp (V × V × V) 2 (volume.restrict U)) z).1 = 0 :=
        integral_eq_zero_of_ae (hx₁.mono fun z hz ↦ by simp [hz])
      rw [h0, add_zero] at hint
      exact hint
    filter_upwards [h, ae_restrict_mem hρ.isOpen.measurableSet] with z hz hzU
    exact hz hzU
  have h₂ := hcomp (e := (1, 0)) (P := (ContinuousLinearMap.fst ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ by simp [jet_apply]
  have h₃ := hcomp (e := (0, 1)) (P := (ContinuousLinearMap.snd ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ by simp [jet_apply]
  refine Subtype.ext ((Lp.eq_zero_iff_ae_eq_zero).2 ?_)
  filter_upwards [hx₁, h₂, h₃] with z h₁ h₂ h₃
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

end Value

/-! ### Rellich's theorem on compact subsets of `U` -/

variable (V U) in
/-- The weighted value `(√ρ ξ, ξ_s, ξ_t) ↦ √ρ ξ` of an `L²` jet over `U`, restricted to a set
`K`. -/
def restrictWeightedValue (K : Set (ℝ × ℝ)) :
    Lp (V × V × V) 2 (volume.restrict U) →L[ℝ] Lp V 2 ((volume.restrict U).restrict K) :=
  (LpToLpRestrictCLM (ℝ × ℝ) V ℝ (volume.restrict U) 2 K).comp
    ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 (volume.restrict U))

/-- The restricted weighted value of an `L²` jet is represented by the first component of the
jet. -/
theorem coeFn_restrictWeightedValue (K : Set (ℝ × ℝ))
    (f : Lp (V × V × V) 2 (volume.restrict U)) :
    restrictWeightedValue V U K f =ᵐ[(volume.restrict U).restrict K] fun z ↦ (f z).1 :=
  (LpToLpRestrictCLM_coeFn ℝ _ _).trans
    (ae_restrict_of_ae ((ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL f))

/-- On a measurable set `K ⊆ U`, the squared norm of the restricted weighted value of the class of
the jet of `ξ` is the weighted `L²` energy `∫_K ρ ‖ξ‖²`. -/
theorem norm_restrictWeightedValue_sq (hρ : IsWeight U ρ) {K : Set (ℝ × ℝ)}
    (hK : MeasurableSet K) (hKU : K ⊆ U) {f : Lp (V × V × V) 2 (volume.restrict U)}
    (hf : f =ᵐ[volume.restrict U] jet ρ ξ) :
    ‖restrictWeightedValue V U K f‖ ^ 2 = ∫ z in K, ρ z * ‖ξ z‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc ∫ z, ‖restrictWeightedValue V U K f z‖ ^ 2 ∂((volume.restrict U).restrict K) =
        ∫ z, ρ z * ‖ξ z‖ ^ 2 ∂((volume.restrict U).restrict K) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_restrictWeightedValue K f, ae_restrict_of_ae hf,
          ae_restrict_mem hK] with z h₁ h₂ hz
        rw [h₁, h₂]
        simp [jet_apply, norm_smul, mul_pow, Real.sq_sqrt (hρ.pos z (hKU hz)).le]
    _ = ∫ z in K, ρ z * ‖ξ z‖ ^ 2 := by rw [Measure.restrict_restrict hK, inter_eq_left.2 hKU]

/-- On a compact set `K ⊆ U`, where the weight is bounded below, the `L²` norm over `K` of a
section `ξ` continuous on `K` is controlled by the restricted weighted value of the class of its
jet. -/
theorem exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq (hρ : IsWeight U ρ)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContinuousOn ξ K → ∀ ⦃f : Lp (V × V × V) 2 (volume.restrict U)⦄,
      f =ᵐ[volume.restrict U] jet ρ ξ →
      ∫ z in K, ‖ξ z‖ ^ 2 ≤ B * ‖restrictWeightedValue V U K f‖ ^ 2 := by
  -- The inverse of the weight is bounded on `K`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ (ρ z)⁻¹)
    ((hρ.continuousOn.mono hKU).inv₀ fun z hz ↦ (hρ.pos z (hKU hz)).ne')
  refine ⟨|B|, fun ξ hξ f hf ↦ ?_⟩
  rw [norm_restrictWeightedValue_sq hρ hK.measurableSet hKU hf, ← integral_const_mul]
  have hcξ : ContinuousOn (fun z ↦ ‖ξ z‖ ^ 2) K := hξ.norm.pow 2
  refine setIntegral_mono_on (hcξ.integrableOn_compact hK)
    ((continuousOn_const.mul ((hρ.continuousOn.mono hKU).mul hcξ)).integrableOn_compact
      hK) hK.measurableSet fun z hz ↦ ?_
  have hρz := hρ.pos z (hKU hz)
  have hBz : (ρ z)⁻¹ ≤ |B| := by
    have h := hB z hz
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hρz)] at h
    exact h.trans (le_abs_self B)
  calc ‖ξ z‖ ^ 2 = (ρ z)⁻¹ * (ρ z * ‖ξ z‖ ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hρz.ne', one_mul]
    _ ≤ |B| * (ρ z * ‖ξ z‖ ^ 2) := mul_le_mul_of_nonneg_right hBz (by positivity)

/-- A continuous function with compact support inside `U` is bounded by a multiple of `√ρ`. -/
private theorem exists_abs_le_mul_sqrt (hρ : IsWeight U ρ) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    ∃ A, 0 ≤ A ∧ ∀ z, |g z| ≤ A * √(ρ z) := by
  obtain ⟨hc, hcs⟩ := continuous_div_sqrt hρ hg hgc hgU
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨max C 0, le_max_right _ _, fun z ↦ ?_⟩
  by_cases hz : z ∈ U
  · have hs := Real.sqrt_pos.2 (hρ.pos z hz)
    have h := (hC z).trans (le_max_left C 0)
    rwa [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_le_iff₀ hs] at h
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hgU h), abs_zero]
    exact mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)

/-- A smooth cutoff equal to `1` on a compact set `K ⊆ U`, with compact support inside `U`, whose
value and derivative are bounded by a multiple of `√ρ`. -/
private theorem exists_cutoff (hρ : IsWeight U ρ) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ (χ : ℝ × ℝ → ℝ) (A : ℝ), ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, χ z = 1) ∧ (∀ z, |χ z| ≤ 1) ∧ 0 ≤ A ∧ (∀ z, |χ z| ≤ A * √(ρ z)) ∧
      ∀ z, ‖fderiv ℝ χ z‖ ≤ A * √(ρ z) := by
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hρ.isOpen hKU
  have hdc : Continuous fun z ↦ ‖fderiv ℝ χ z‖ := (hχ.continuous_fderiv (by simp)).norm
  have hdsupp : tsupport (fun z ↦ ‖fderiv ℝ χ z‖) ⊆ tsupport χ :=
    closure_minimal (fun z hz ↦ tsupport_fderiv_subset (𝕜 := ℝ)
      (subset_tsupport _ fun h ↦ hz (by simp [h]))) (isClosed_tsupport χ)
  obtain ⟨A₀, hA₀, h₀⟩ := exists_abs_le_mul_sqrt hρ hχ.continuous hχc hχU
  obtain ⟨A₁, -, h₁⟩ := exists_abs_le_mul_sqrt hρ hdc (hχc.fderiv (𝕜 := ℝ)).norm
    (hdsupp.trans hχU)
  refine ⟨χ, max A₀ A₁, hχ.of_le (by simp), hχc, hχU, fun z hz ↦ (hχ1 z hz).self_of_nhds,
    fun z ↦ ?_, le_max_of_le_left hA₀, fun z ↦ (h₀ z).trans ?_, fun z ↦ ?_⟩
  · obtain ⟨h0, h1⟩ := hχr (mem_range_self z)
    rwa [abs_of_nonneg h0]
  · gcongr
    exact le_max_left _ _
  · have h := h₁ z
    rw [abs_norm] at h
    exact h.trans (by gcongr; exact le_max_right _ _)

/-- The cut-off test sections: the cut-off section and its derivative are bounded in `L²` of the
plane by the `L²` norm of the jet over `U`. -/
private theorem cutoff_estimates {χ : ℝ × ℝ → ℝ} {A : ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχU : tsupport χ ⊆ U) (hχ1 : ∀ z, |χ z| ≤ 1) (hA0 : 0 ≤ A) (hA : ∀ z, |χ z| ≤ A * √(ρ z))
    (hA' : ∀ z, ‖fderiv ℝ χ z‖ ≤ A * √(ρ z)) (hξ : ξ ∈ testSection V U) :
    ContDiff ℝ 2 (fun z ↦ χ z • ξ z) ∧
      eLpNorm (fun z ↦ χ z • ξ z) 2 volume ≤
        ENNReal.ofReal A * eLpNorm (jet ρ ξ) 2 (volume.restrict U) ∧
      eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume ≤
        ENNReal.ofReal (A + 2) * eLpNorm (jet ρ ξ) 2 (volume.restrict U) := by
  obtain ⟨hξ2, -, -⟩ := mem_testSection_iff.1 hξ
  have hf : ContDiff ℝ 2 (fun z ↦ χ z • ξ z) := hχ.smul hξ2
  have hts : tsupport (fun z ↦ χ z • ξ z) ⊆ U := (tsupport_smul_subset_left χ ξ).trans hχU
  -- The zeroth-order part `‖ξ‖` is controlled through the weighted value `√ρ ξ`.
  have hval : ∀ {c : ℝ × ℝ → ℝ}, (∀ z, c z ≤ A * √(ρ z)) →
      ∀ z, c z * ‖ξ z‖ ≤ A * ‖jet ρ ξ z‖ := by
    intro c hc z
    calc c z * ‖ξ z‖ ≤ A * √(ρ z) * ‖ξ z‖ := by gcongr; exact hc z
      _ = A * ‖√(ρ z) • ξ z‖ := by rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]; ring
      _ ≤ A * ‖jet ρ ξ z‖ := by gcongr; exact norm_fst_le (jet ρ ξ z)
  have hd : ∀ z, ‖fderiv ℝ ξ z‖ ≤ 2 * ‖jet ρ ξ z‖ := fun z ↦ by
    have h₁ : ‖fderiv ℝ ξ z (1, 0)‖ ≤ ‖jet ρ ξ z‖ :=
      (norm_fst_le ((fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) : V × V)).trans
        (norm_snd_le (jet ρ ξ z))
    have h₂ : ‖fderiv ℝ ξ z (0, 1)‖ ≤ ‖jet ρ ξ z‖ :=
      (norm_snd_le ((fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) : V × V)).trans
        (norm_snd_le (jet ρ ξ z))
    linarith [(fderiv ℝ ξ z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one]
  refine ⟨hf, ?_, ?_⟩
  · rw [← eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable
      ((subset_tsupport _).trans hts)]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf.continuous.aestronglyMeasurable.restrict
      (Eventually.of_forall fun z ↦ ?_) 2
    rw [norm_smul, Real.norm_eq_abs]
    exact hval (c := fun z ↦ |χ z|) hA z
  · have hdc := hf.continuous_fderiv (by norm_num)
    rw [← eLpNorm_restrict_eq_of_support_subset hdc.aestronglyMeasurable
      ((support_fderiv_subset ℝ).trans hts)]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdc.aestronglyMeasurable.restrict
      (Eventually.of_forall fun z ↦ ?_) 2
    rw [fderiv_fun_smul (hχ.differentiable (by norm_num) z) (hξ2.differentiable (by norm_num) z)]
    calc _ ≤ ‖χ z‖ * ‖fderiv ℝ ξ z‖ + ‖fderiv ℝ χ z‖ * ‖ξ z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1 * (2 * ‖jet ρ ξ z‖) + A * ‖jet ρ ξ z‖ :=
          add_le_add (mul_le_mul ((Real.norm_eq_abs _).trans_le (hχ1 z)) (hd z) (norm_nonneg _)
            zero_le_one) (hval (c := fun z ↦ ‖fderiv ℝ χ z‖) hA' z)
      _ = (A + 2) * ‖jet ρ ξ z‖ := by ring

/-- An element of `H1` of norm less than `2` is a limit of jets of test sections of norm less
than `2`, as `{f | ‖f‖ < 2}` is open (`IsOpen.inter_closure`). -/
private theorem mem_closure_setOf_norm_lt (x : H1 V U ρ) (hx : ‖x‖ < 2) :
    (x : Lp (V × V × V) 2 (volume.restrict U)) ∈
      closure {f | f ∈ jetSubmodule V U ρ ∧ ‖f‖ < 2} := by
  have hxH : (x : Lp (V × V × V) 2 (volume.restrict U)) ∈
      closure (jetSubmodule V U ρ : Set (Lp (V × V × V) 2 (volume.restrict U))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact x.property
  refine closure_mono ?_ ((isOpen_lt continuous_norm continuous_const).inter_closure
    ⟨(Submodule.norm_coe x).trans_lt hx, hxH⟩)
  rintro f ⟨hf2, hf⟩
  exact ⟨hf, hf2⟩

/-- On a compact set `K ⊆ U` the weight `√ρ` is a bounded multiplier: restriction to `K` followed
by multiplication by `√ρ` is a continuous linear map from `L²` of the plane to `L²(K)`. -/
private theorem exists_restrict_sqrt_smul (hρ : IsWeight U ρ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ Res : Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 ((volume.restrict U).restrict K),
      ∀ g, (Res g : ℝ × ℝ → V) =ᵐ[(volume.restrict U).restrict K] fun z ↦ √(ρ z) • g z := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hρ.continuousOn.mono hKU).sqrt
  have : IsFiniteMeasure ((volume.restrict U).restrict K) :=
    isFiniteMeasure_restrict.2 ((Measure.restrict_apply_le U K).trans_lt hK.measure_lt_top).ne
  have hm : MemLp (fun z ↦ √(ρ z)) ∞ ((volume.restrict U).restrict K) :=
    MemLp.of_bound ((hρ.continuousOn.mono hKU).sqrt.aestronglyMeasurable hK.measurableSet) B
      ((ae_restrict_mem hK.measurableSet).mono hB)
  set R₁ := LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U
  set R₂ := LpToLpRestrictCLM (ℝ × ℝ) V ℝ (volume.restrict U) 2 K
  set B : ℝ →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨(B.holderL ((volume.restrict U).restrict K) ∞ 2 2 (hm.toLp _)).comp (R₂.comp R₁),
    fun g ↦ ?_⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.holderL_apply_apply]
  filter_upwards [B.coeFn_holder (r := 2) (hm.toLp _) (R₂ (R₁ g)), hm.coeFn_toLp,
    (LpToLpRestrictCLM_coeFn ℝ K (R₁ g)).trans
      (ae_restrict_of_ae (LpToLpRestrictCLM_coeFn ℝ U g))] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, ContinuousLinearMap.lsmul_apply]

/-- **Rellich's theorem on a domain with a conformal metric.** For a compact set `K ⊆ U`, the
weighted value on `K` is a compact operator from `W^{1,2}_0(U, V)` to `L²(K, V)`. -/
theorem isCompactOperator_restrictWeightedValue_comp_subtypeL [FiniteDimensional ℝ V]
    (hρ : IsWeight U ρ) {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompactOperator ((restrictWeightedValue V U K).comp (H1 V U ρ).subtypeL) := by
  obtain ⟨χ, A, hχ, hχc, hχU, hχK, hχ1, hA0, hA, hA'⟩ := exists_cutoff hρ hK hKU
  have hest := fun ξ (hξ : ξ ∈ testSection V U) ↦ cutoff_estimates hχ hχU hχ1 hA0 hA hA' hξ
  set S := {f : Lp V 2 (volume : Measure (ℝ × ℝ)) | ∃ ξ ∈ testSection V U,
      eLpNorm (jet ρ ξ) 2 (volume.restrict U) ≤ 2 ∧ f =ᵐ[volume] fun z ↦ χ z • ξ z}
  -- The cut-off test sections of jet norm at most `2` are totally bounded in `L²` of the plane.
  have htb : TotallyBounded S := by
    have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    refine totallyBounded_of_contDiff_of_eLpNorm_fderiv_le (by norm_num) hχc.isCompact.isBounded
      (M := ENNReal.ofReal (A + 2) * 2) (by finiteness) fun f ⟨ξ, hξ, hξ2, hf⟩ ↦
        ⟨fun z ↦ χ z • ξ z, (hest ξ hξ).1.of_le (by norm_num), fun z hz ↦ ?_,
          (hest ξ hξ).2.1.trans ?_, (hest ξ hξ).2.2.trans (by gcongr), hf⟩
    · simp [image_eq_zero_of_notMem_tsupport hz]
    · gcongr
      linarith
  -- On `K` the multiplier `√ρ` takes the cut-off section `χ ξ = ξ` to the weighted value `√ρ ξ`.
  obtain ⟨Res, hRes⟩ := exists_restrict_sqrt_smul (V := V) hρ hK hKU
  have hsub : restrictWeightedValue V U K '' {f | f ∈ jetSubmodule V U ρ ∧ ‖f‖ < 2} ⊆
      Res '' S := by
    rintro _ ⟨f, ⟨⟨ξ, hξ, hf⟩, hf2⟩, rfl⟩
    have hjm := memLp_jet hρ hξ
    have hξ2 : eLpNorm (jet ρ ξ) 2 (volume.restrict U) ≤ 2 := by
      have hfj : f = hjm.toLp (jet ρ ξ) := Lp.ext (hf.trans hjm.coeFn_toLp.symm)
      rw [hfj, Lp.norm_toLp] at hf2
      simpa using (ENNReal.le_ofReal_iff_toReal_le hjm.eLpNorm_ne_top (by norm_num)).2 hf2.le
    have hmem : MemLp (fun z ↦ χ z • ξ z) 2 volume :=
      (hest ξ hξ).2.1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hjm)
    refine ⟨hmem.toLp _, ⟨ξ, hξ, hξ2, hmem.coeFn_toLp⟩, Lp.ext ?_⟩
    filter_upwards [coeFn_restrictWeightedValue K f, ae_restrict_of_ae (μ := volume.restrict U) hf,
      hRes (hmem.toLp _), ae_restrict_of_ae (ae_restrict_of_ae hmem.coeFn_toLp),
      ae_restrict_mem hK.measurableSet] with z h₁ h₂ h₃ h₄ hz
    rw [h₃, h₄, h₁, h₂, hχK z hz, one_smul, jet_apply]
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨ball 0 1, ball_mem_nhds 0 one_pos, _,
      (htb.image Res.uniformContinuous).closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact closure_mono hsub (image_closure_subset_closure_image
    (restrictWeightedValue V U K).continuous
      ⟨_, mem_closure_setOf_norm_lt x ((mem_ball_zero_iff.1 hx).trans one_lt_two), rfl⟩)

/-! ### First-order operators with bounded coefficients -/

section Operator

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- On the `L²` class of the jet of a test section `ξ`, the first-order operator of a coefficient
field `M` is `z ↦ M z (√ρ ξ z, ∂s ξ z, ∂t ξ z)`. -/
theorem jetOperator_toLp_jet_ae_eq (hρ : IsWeight U ρ) {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ (volume.restrict U)) (hξ : ξ ∈ testSection V U) :
    jetOperator (volume.restrict U) M ((memLp_jet hρ hξ).toLp (jet ρ ξ)) =ᵐ[volume.restrict U]
      fun z ↦ M z (jet ρ ξ z) := by
  filter_upwards [coeFn_jetOperator hM ((memLp_jet hρ hξ).toLp (jet ρ ξ)),
    (memLp_jet hρ hξ).coeFn_toLp] with z h₁ h₂
  rw [h₁, h₂]

end Operator

/-! ### Peetre's argument -/

section Peetre

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An estimate on the jets of test sections extends to `H1`, with a compact error term. -/
private theorem compact_estimate [FiniteDimensional ℝ V] (hρ : IsWeight U ρ)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) (D : H1 V U ρ →L[ℝ] F) {C : ℝ}
    (hest : ∀ x : H1 V U ρ, (x : Lp (V × V × V) 2 (volume.restrict U)) ∈ jetSubmodule V U ρ →
      ‖x‖ ≤ C * (‖D x‖ + ‖restrictWeightedValue V U K x‖)) :
    IsCompactOperator (C • (restrictWeightedValue V U K).comp (H1 V U ρ).subtypeL) ∧
      ∀ x, ‖x‖ ≤ C * ‖D x‖ + ‖(C • (restrictWeightedValue V U K).comp (H1 V U ρ).subtypeL) x‖ := by
  refine ⟨(isCompactOperator_restrictWeightedValue_comp_subtypeL hρ hK hKU).smul C, fun x ↦ ?_⟩
  set R := (restrictWeightedValue V U K).comp (H1 V U ρ).subtypeL
  -- The estimate holds on a closed set containing the dense set of jets of test sections.
  have hS : IsClosed {x : H1 V U ρ | ‖x‖ ≤ C * (‖D x‖ + ‖R x‖)} :=
    isClosed_le continuous_norm (continuous_const.mul
      ((continuous_norm.comp D.continuous).add (continuous_norm.comp R.continuous)))
  have hx : ‖x‖ ≤ C * (‖D x‖ + ‖R x‖) := by
    have h := hS.closure_subset_iff.2 (show {y : H1 V U ρ |
      (y : Lp (V × V × V) 2 (volume.restrict U)) ∈ jetSubmodule V U ρ} ⊆ _ from
        fun y hy ↦ hest y hy)
    rw [dense_setOf_mem_jetSubmodule.closure_eq] at h
    exact h (mem_univ x)
  have hCR : ‖(C • R) x‖ = |C| * ‖R x‖ := by simp [norm_smul]
  rw [hCR]
  calc ‖x‖ ≤ C * ‖D x‖ + C * ‖R x‖ := by linarith
    _ ≤ C * ‖D x‖ + |C| * ‖R x‖ := by gcongr; exact le_abs_self C

/-- **Peetre's argument: finite-dimensional kernel.** Let `K ⊆ U` be compact and let `D` be a
continuous linear map on `W^{1,2}_0(U, V)` satisfying `‖x‖ ≤ C (‖D x‖ + ‖√ρ ξ‖_{L²(K)})` on the
jets `x` of test sections `ξ`. Then `D` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_of_estimate [FiniteDimensional ℝ V] (hρ : IsWeight U ρ)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) (D : H1 V U ρ →L[ℝ] F) {C : ℝ}
    (hest : ∀ x : H1 V U ρ, (x : Lp (V × V × V) 2 (volume.restrict U)) ∈ jetSubmodule V U ρ →
      ‖x‖ ≤ C * (‖D x‖ + ‖restrictWeightedValue V U K x‖)) :
    FiniteDimensional ℝ D.ker := by
  obtain ⟨hc, hb⟩ := compact_estimate hρ hK hKU D hest
  exact ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate D hc hb

/-- **Peetre's argument: closed range.** Under the estimate of
`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`, `D` has closed range. -/
theorem isClosed_range_of_estimate [FiniteDimensional ℝ V] (hρ : IsWeight U ρ)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) (D : H1 V U ρ →L[ℝ] F) {C : ℝ}
    (hest : ∀ x : H1 V U ρ, (x : Lp (V × V × V) 2 (volume.restrict U)) ∈ jetSubmodule V U ρ →
      ‖x‖ ≤ C * (‖D x‖ + ‖restrictWeightedValue V U K x‖)) :
    IsClosed (D.range : Set F) := by
  obtain ⟨hc, hb⟩ := compact_estimate hρ hK hKU D hest
  exact ContinuousLinearMap.isClosed_range_of_compact_estimate D hc hb

end Peetre

end TauCeti.ConformalSobolev
