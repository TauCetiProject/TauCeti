/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.NumberTheory.Padics.Measure.Basic
public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic

/-!
# Locally analytic distributions on `ℤ_p`

Let `K` be a complete nontrivially normed field which is a `ℤ_p`-algebra with contractive
`ℤ_p`-action, such as a complete normed extension of `ℚ_p`. The locally analytic functions on
`ℤ_p` with values in `K` are the algebraic direct limit `TauCeti.LocallyAnalytic p K K` of the
analytic stages `LA_h(K)`. A *locally analytic distribution* is a `K`-linear functional on this
direct limit whose restriction to every stage `LA_h(K)` is bounded. These functionals form the
submodule `TauCeti.LocallyAnalyticDistribution p K` of the algebraic dual.

Equivalently, a distribution is a family of continuous linear functionals `μ_h` on the stages
that is compatible with re-expansion, `μ_{h+1} ∘ transition = μ_h`. The restriction to the stage
of level `h` is the linear map `LocallyAnalyticDistribution.stage h`, and
`LocallyAnalyticDistribution.stagesEquiv` identifies distributions with compatible families. The
operator norms of the restrictions are the stage seminorms
`LocallyAnalyticDistribution.stageSeminorm h`. They increase with `h`, since re-expansion does
not increase norms, and together they separate distributions. No topology is put on the space of
distributions here.

A measure, a continuous linear functional on `C(ℤ_p, K)`, defines a distribution by integrating
evaluated coefficient vectors (`LocallyAnalyticDistribution.ofMeasure`). Its stage seminorms are
bounded by the norm of the measure, and a measure is determined by the distribution it defines,
since locally analytic functions are dense in `C(ℤ_p, K)`.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution p K`: the `K`-linear functionals on `LA(ℤ_p, K)` that are
  bounded on every analytic stage.
* `TauCeti.LocallyAnalyticDistribution.stage h`: restriction to the stage `LA_h(K)`.
* `TauCeti.LocallyAnalyticDistribution.compatibleStageFunctionals p K`: the families of
  continuous linear functionals on the stages compatible with re-expansion.
* `TauCeti.LocallyAnalyticDistribution.stagesEquiv`: distributions are compatible families.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm h`: the operator norm on `LA_h(K)`.
* `TauCeti.LocallyAnalyticDistribution.ofMeasure`: measures as distributions.

## Main results

* `TauCeti.LocallyAnalyticDistribution.ext`: a distribution is determined by its restrictions.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mono`: the stage seminorms increase with
  the level.
* `TauCeti.LocallyAnalyticDistribution.eq_zero_of_forall_stageSeminorm_eq_zero`: the stage
  seminorms separate distributions.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_ofMeasure_le`: the stage seminorms of a
  measure are bounded by its norm.
* `TauCeti.LocallyAnalyticDistribution.ofMeasure_injective`: a measure is determined by its
  restriction to locally analytic functions.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

open AnalyticStage LocallyAnalytic

variable (p K) in
/-- The locally analytic distributions on `ℤ_p` with values in `K`: the `K`-linear functionals
on the locally analytic functions `LA(ℤ_p, K)` whose restriction to every analytic stage
`LA_h(K)` is continuous, that is, bounded for the Gauss norm. -/
def LocallyAnalyticDistribution : Submodule K (Module.Dual K (LocallyAnalytic p K K)) where
  carrier := {μ | ∀ h, Continuous (μ ∘ₗ ofStage K h)}
  add_mem' {μ ν} hμ hν h := by
    simpa only [LinearMap.add_comp, LinearMap.coe_add] using (hμ h).add (hν h)
  zero_mem' h := by
    rw [LinearMap.zero_comp]
    exact continuous_zero.congr fun c ↦ (LinearMap.zero_apply c).symm
  smul_mem' a μ hμ h := by
    simpa only [LinearMap.smul_comp, LinearMap.coe_smul] using (hμ h).const_smul a

namespace LocallyAnalyticDistribution

/-- A functional is a distribution when it is continuous on every analytic stage. -/
theorem mem_iff {μ : Module.Dual K (LocallyAnalytic p K K)} :
    μ ∈ LocallyAnalyticDistribution p K ↔ ∀ h, Continuous (μ ∘ₗ ofStage K h) :=
  Iff.rfl

/-- The restriction of a distribution to the analytic stage `LA_h(K)`. -/
noncomputable def stage (h : ℕ) :
    LocallyAnalyticDistribution p K →ₗ[K] AnalyticStage p h K →L[K] K where
  toFun μ := ⟨(μ : Module.Dual K (LocallyAnalytic p K K)) ∘ₗ ofStage K h, μ.2 h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The restriction to a stage applies the distribution to the class of a coefficient vector. -/
@[simp]
theorem stage_apply (h : ℕ) (μ : LocallyAnalyticDistribution p K) (c : AnalyticStage p h K) :
    stage h μ c = (μ : Module.Dual K (LocallyAnalytic p K K)) (ofStage K h c) :=
  (rfl)

/-- The restrictions of a distribution are compatible with re-expansion. -/
theorem stage_comp_transitionLE (μ : LocallyAnalyticDistribution p K) {h k : ℕ} (hhk : h ≤ k) :
    stage k μ ∘L transitionLE K hhk = stage h μ := by
  ext c
  simp

/-- The restrictions of a distribution are compatible with adjacent re-expansion. -/
theorem stage_comp_transition (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    stage (h + 1) μ ∘L transition K = stage h μ := by
  ext c
  simp

/-- A distribution is determined by its restrictions to the analytic stages. -/
@[ext]
theorem ext {μ ν : LocallyAnalyticDistribution p K} (H : ∀ h, stage h μ = stage h ν) : μ = ν := by
  refine Subtype.ext <| Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ ?_
  simpa [ofStage_def] using DFunLike.congr_fun (H h) c

variable (p K) in
/-- The families of continuous linear functionals on the analytic stages that are compatible with
re-expansion, `μ_{h+1} ∘ transition = μ_h`. -/
def compatibleStageFunctionals : Submodule K (∀ h : ℕ, AnalyticStage p h K →L[K] K) where
  carrier := {μ | ∀ h, μ (h + 1) ∘L transition K = μ h}
  add_mem' {μ ν} hμ hν h := by
    simp only [Pi.add_apply, ContinuousLinearMap.add_comp, hμ h, hν h]
  zero_mem' h := by simp
  smul_mem' a μ hμ h := by
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_comp, hμ h]

/-- A family is compatible when it is compatible with adjacent re-expansion. -/
@[simp]
theorem mem_compatibleStageFunctionals_iff {μ : ∀ h : ℕ, AnalyticStage p h K →L[K] K} :
    μ ∈ compatibleStageFunctionals p K ↔ ∀ h, μ (h + 1) ∘L transition K = μ h :=
  Iff.rfl

/-- A compatible family is compatible with re-expansion between any two levels. -/
theorem comp_transitionLE_of_mem_compatibleStageFunctionals
    {μ : ∀ h : ℕ, AnalyticStage p h K →L[K] K} (hμ : μ ∈ compatibleStageFunctionals p K)
    {h k : ℕ} (hhk : h ≤ k) :
    μ k ∘L transitionLE K hhk = μ h := by
  induction k, hhk using Nat.le_induction with
  | base => rw [transitionLE_self, ContinuousLinearMap.comp_id]
  | succ k hhk ih =>
    rw [transitionLE_succ K hhk, ← ContinuousLinearMap.comp_assoc,
      mem_compatibleStageFunctionals_iff.mp hμ k, ih]

/-- The functional on the direct limit induced by a compatible family. -/
private noncomputable def liftFamily (μ : compatibleStageFunctionals p K) :
    Module.Dual K (LocallyAnalytic p K K) :=
  Module.DirectLimit.lift K ℕ _ _ (fun h ↦ (μ.1 h : AnalyticStage p h K →ₗ[K] K))
    fun _ _ hhk ↦ DFunLike.congr_fun (comp_transitionLE_of_mem_compatibleStageFunctionals μ.2 hhk)

/-- The functional induced by a compatible family restricts to the members of the family. -/
private theorem liftFamily_ofStage (μ : compatibleStageFunctionals p K) (h : ℕ)
    (c : AnalyticStage p h K) : liftFamily μ (ofStage K h c) = μ.1 h c :=
  lift_ofStage K _ _ h c

/-- Distributions are the compatible families of continuous linear functionals on the analytic
stages. The forward map takes the restrictions of a distribution; the inverse is Mathlib's
universal property of the direct limit. -/
noncomputable def stagesEquiv :
    LocallyAnalyticDistribution p K ≃ₗ[K] compatibleStageFunctionals p K where
  toFun μ := ⟨fun h ↦ stage h μ, stage_comp_transition μ⟩
  invFun μ :=
    ⟨liftFamily μ, fun h ↦ by
      convert (μ.1 h).continuous using 1
      ext c
      exact liftFamily_ofStage μ h c⟩
  left_inv μ := by
    ext h c
    exact lift_ofStage K _ (fun _ _ hhk ↦ DFunLike.congr_fun (stage_comp_transitionLE μ hhk)) h c
  right_inv μ := by
    ext h c
    exact liftFamily_ofStage μ h c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The compatible family of a distribution consists of its restrictions to the stages. -/
@[simp]
theorem stagesEquiv_apply (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    (stagesEquiv μ : ∀ h : ℕ, AnalyticStage p h K →L[K] K) h = stage h μ :=
  (rfl)

/-- The distribution of a compatible family restricts to the members of the family. -/
@[simp]
theorem stage_stagesEquiv_symm (μ : compatibleStageFunctionals p K) (h : ℕ) :
    stage h (stagesEquiv.symm μ) = μ.1 h := by
  rw [← stagesEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The distribution of a compatible family applies the members of the family on the stages. -/
@[simp]
theorem coe_stagesEquiv_symm_apply_ofStage (μ : compatibleStageFunctionals p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    (stagesEquiv.symm μ : Module.Dual K (LocallyAnalytic p K K)) (ofStage K h c) = μ.1 h c := by
  rw [← stage_apply, stage_stagesEquiv_symm]

/-- The stage seminorm of level `h`: the operator norm of the restriction of a distribution to
the analytic stage `LA_h(K)`. -/
noncomputable def stageSeminorm (h : ℕ) : Seminorm K (LocallyAnalyticDistribution p K) :=
  (normSeminorm K (AnalyticStage p h K →L[K] K)).comp (stage h)

/-- The stage seminorm is the operator norm of the restriction. -/
@[simp]
theorem stageSeminorm_apply (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h μ = ‖stage h μ‖ :=
  (rfl)

/-- The stage seminorms increase with the level: re-expansion does not increase the Gauss norm,
so a distribution bounded on a finer stage is bounded by the same constant on a coarser one. -/
theorem stageSeminorm_mono (μ : LocallyAnalyticDistribution p K) :
    Monotone fun h ↦ stageSeminorm h μ := by
  intro h k hhk
  simp only [stageSeminorm_apply]
  rw [← stage_comp_transitionLE μ hhk]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (opNorm_transitionLE_le_one hhk))

/-- The stage seminorms separate distributions. -/
theorem eq_zero_of_forall_stageSeminorm_eq_zero {μ : LocallyAnalyticDistribution p K}
    (hμ : ∀ h, stageSeminorm h μ = 0) : μ = 0 :=
  ext fun h ↦ by
    rw [map_zero]
    exact (ContinuousLinearMap.opNorm_zero_iff _).mp (hμ h)

/-- A measure on `ℤ_p` with values in `K` defines a locally analytic distribution, integrating the
continuous function obtained by evaluating a locally analytic coefficient vector. -/
noncomputable def ofMeasure : AbstractMeasure ℤ_[p] K K →ₗ[K] LocallyAnalyticDistribution p K where
  toFun μ := ⟨(AbstractMeasure.toCLMEquiv μ : C(ℤ_[p], K) →ₗ[K] K) ∘ₗ LocallyAnalytic.eval K,
    fun h ↦ by
      convert (AbstractMeasure.toCLMEquiv μ ∘L AnalyticStage.eval K).continuous using 1
      ext c
      simp⟩
  map_add' μ ν := Subtype.ext <| LinearMap.ext fun f ↦ by simp
  map_smul' a μ := Subtype.ext <| LinearMap.ext fun f ↦ by simp

/-- The distribution of a measure integrates evaluated locally analytic functions. -/
@[simp]
theorem coe_ofMeasure_apply (μ : AbstractMeasure ℤ_[p] K K) (f : LocallyAnalytic p K K) :
    (ofMeasure μ : Module.Dual K (LocallyAnalytic p K K)) f = μ (LocallyAnalytic.eval K f) :=
  AbstractMeasure.coe_toCLMEquiv μ _

/-- The restriction of the distribution of a measure to a stage is the measure composed with
stage evaluation. -/
@[simp]
theorem stage_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) (h : ℕ) :
    stage h (ofMeasure μ) = AbstractMeasure.toCLMEquiv μ ∘L AnalyticStage.eval K := by
  ext c
  simp

/-- The stage seminorms of the distribution of a measure are bounded by the norm of the measure,
since evaluation does not increase norms. -/
theorem stageSeminorm_ofMeasure_le (μ : AbstractMeasure ℤ_[p] K K) (h : ℕ) :
    stageSeminorm h (ofMeasure μ) ≤ ‖AbstractMeasure.toCLMEquiv μ‖ := by
  rw [stageSeminorm_apply, stage_ofMeasure]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) AnalyticStage.opNorm_eval_le_one)

/-- A measure is determined by the distribution it defines, since locally analytic functions are
dense in the continuous functions. -/
theorem ofMeasure_injective : Function.Injective (ofMeasure (p := p) (K := K)) := by
  intro μ ν hμν
  have hcomp : (μ : C(ℤ_[p], K) → K) ∘ LocallyAnalytic.eval K =
      (ν : C(ℤ_[p], K) → K) ∘ LocallyAnalytic.eval K := by
    funext f
    simpa using LinearMap.congr_fun (congrArg Subtype.val hμν) f
  exact AbstractMeasure.ext fun f ↦ congrFun
    ((denseRange_eval (p := p) (E := K) K).equalizer (map_continuous μ) (map_continuous ν)
      hcomp) f

end LocallyAnalyticDistribution

end TauCeti
