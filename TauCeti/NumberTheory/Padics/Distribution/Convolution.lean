/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Monoid
public import TauCeti.NumberTheory.Padics.Distribution.Dual
public import TauCeti.NumberTheory.Padics.Distribution.StageConvolution
public import TauCeti.NumberTheory.Padics.Distribution.Translation
import TauCeti.NumberTheory.Padics.Measure.Pushforward

/-!
# Point masses and additive convolution of locally analytic distributions on `ℤ_p`

Let `K` be a complete nontrivially normed field with contractive `ℤ_p`-action. Using the
two-variable addition re-expansion `TauCeti.AnalyticStage.comul` and the stage-level right
convolution operator `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage` (from
`TauCeti.NumberTheory.Padics.Distribution.StageConvolution`), this file equips the space
`TauCeti.LocallyAnalyticDistribution p K` with point masses and its genuine additive convolution
`K`-algebra structure directly across the analytic stages:

* `TauCeti.LocallyAnalyticDistribution.dirac`: the point-mass distribution `δ_x` at `x ∈ ℤ_p`,
  evaluating locally analytic functions at `x`, with `stageSeminorm h (dirac x) = 1` at every
  analytic level `h`;
* `One (LocallyAnalyticDistribution p K)` and `Mul (LocallyAnalyticDistribution p K)`: the unit
  `1 = dirac 0` and the additive convolution `μ * ν`, defined on each analytic stage `LA_h(K)` by
  `(stage h μ) ∘ convolveFunRightStage (stage h ν)`, equivalently
  `(stage h μ ⊗ stage h ν) ∘ comul`;
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: submultiplicativity of every stage
  seminorm, `stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν`;
* `CommRing (LocallyAnalyticDistribution p K)` and `Algebra K (LocallyAnalyticDistribution p K)`:
  the commutative convolution `K`-algebra structure, proved from the counit, cocommutativity,
  transition compatibility, and coassociativity of `comul` without appealing to the Amice
  transform or assuming characteristic zero;
* `TauCeti.LocallyAnalyticDistribution.convolveFunRight`: the right-handed convolution action of
  distributions on locally analytic test functions, sending `f` to `x ↦ ν (y ↦ f (x + y))` and
  satisfying `(μ * ν) f = μ (convolveFunRight ν f)`;
* `TauCeti.LocallyAnalyticDistribution.ofMeasure_map_add_prodMk'` and
  `TauCeti.LocallyAnalyticDistribution.ofMulMeasure`: compatibility of `ofMeasure` with native
  additive measure convolution on `ℤ_p`, bundled as an injective `K`-algebra homomorphism
  `D(Multiplicative ℤ_p, K) →ₐ[K] LocallyAnalyticDistribution p K`.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.dirac`: point-mass distribution at `x ∈ ℤ_p`.
* `TauCeti.LocallyAnalyticDistribution.diracHom`: the monoid homomorphism
  `Multiplicative ℤ_p →* LocallyAnalyticDistribution p K` sending `ofAdd x` to `dirac x`.
* `TauCeti.LocallyAnalyticDistribution.convolveFunRight`: right convolution on `LA(ℤ_p, K)`.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure`: the convolution `K`-algebra embedding
  `D(Multiplicative ℤ_p, K) →ₐ[K] LocallyAnalyticDistribution p K`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_dirac`: every point mass has stage seminorm
  `1` at every level.
* `TauCeti.LocallyAnalyticDistribution.dirac_injective`: `dirac` is injective.
* `TauCeti.LocallyAnalyticDistribution.stage_mul`: stage restriction of `μ * ν` is
  `prodFunctional (stage h μ) (stage h ν) _ ∘L comul K`.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: stage seminorms are submultiplicative.
* `TauCeti.LocallyAnalyticDistribution.dirac_add`: `dirac (x + y) = dirac x * dirac y`.
* `TauCeti.LocallyAnalyticDistribution.coe_mul_apply`,
  `TauCeti.LocallyAnalyticDistribution.eval_convolveFunRight_zero`,
  `TauCeti.LocallyAnalyticDistribution.convolveFunRight_injective`,
  `TauCeti.LocallyAnalyticDistribution.convolveFunRight_dirac`,
  `TauCeti.LocallyAnalyticDistribution.convolveFunRight_mul`: evaluation, zero-evaluation recovery,
  faithfulness, Dirac specialization, and module action for right convolution.
* `TauCeti.LocallyAnalyticDistribution.ofMeasure_map_add_prodMk'`: `ofMeasure` intertwines
  pushforward product-measure convolution along `+ : ℤ_p × ℤ_p → ℤ_p` with distribution
  convolution.
* `TauCeti.LocallyAnalyticDistribution.ofMulMeasure_injective`: `ofMulMeasure` is injective.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open scoped AbstractMeasure ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace TauCeti.LocallyAnalyticDistribution

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

open AnalyticStage LocallyAnalytic

/-! ### Point-mass distributions -/

/-- **Point-mass locally analytic distribution** `δ_x` at `x ∈ ℤ_p`, induced by the Dirac measure
at `x`. -/
noncomputable def dirac (x : ℤ_[p]) : LocallyAnalyticDistribution p K :=
  ofMeasure (AbstractMeasure.dirac K x)

/-- The image of a Dirac measure under `ofMeasure` is `dirac`. -/
@[simp]
theorem ofMeasure_dirac (x : ℤ_[p]) :
    ofMeasure (p := p) (K := K) (AbstractMeasure.dirac K x) = dirac x :=
  (rfl)

/-- `dirac x` evaluates a locally analytic function at `x`. -/
@[simp]
theorem coe_dirac_apply (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    (dirac (K := K) x : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f x := by
  rw [dirac, coe_ofMeasure_apply, AbstractMeasure.dirac_apply]

/-- On the analytic stage `LA_h(K)`, `dirac x` evaluates the series of `c` at `x`. -/
theorem stage_dirac_apply (h : ℕ) (x : ℤ_[p]) (c : AnalyticStage p h K) :
    stage h (dirac (K := K) x) c = AnalyticStage.eval K c x := by
  simp

/-- On every analytic stage `LA_h(K)`, the point mass `dirac x` has operator norm `1`. -/
@[simp]
theorem norm_stage_dirac (h : ℕ) (x : ℤ_[p]) :
    ‖stage h (dirac (p := p) (K := K) x)‖ = 1 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ ?_
    rw [stage_dirac_apply, one_mul]
    exact (ContinuousMap.norm_coe_le_norm (AnalyticStage.eval K c) x).trans (norm_eval_le K c)
  · let c : AnalyticStage p h K := single (PadicInt.toZModPow h x, 0) 1
    have hc_norm : ‖c‖ = 1 := by simp [c]
    have hc_eval : stage h (dirac (p := p) (K := K) x) c = 1 := by
      rw [stage_dirac_apply]
      simp [c, eval_single]
    have hle := (stage h (dirac (p := p) (K := K) x)).le_opNorm c
    rw [hc_eval, hc_norm, norm_one, mul_one] at hle
    exact hle

/-- Every point mass `dirac x` has stage seminorm equal to `1` at every analytic level `h`. -/
theorem stageSeminorm_dirac (h : ℕ) (x : ℤ_[p]) :
    stageSeminorm h (dirac (p := p) (K := K) x) = 1 := by
  simp

/-- Every point-mass distribution is nonzero. -/
@[simp]
theorem dirac_ne_zero (x : ℤ_[p]) : dirac (p := p) (K := K) x ≠ 0 := by
  intro hx
  have h1 := stageSeminorm_dirac (p := p) (K := K) 0 x
  rw [hx, map_zero] at h1
  exact zero_ne_one h1

/-- Distinct points of `ℤ_p` define distinct point-mass distributions, separated by locally
constant indicator functions of residue discs. -/
theorem dirac_injective : Function.Injective (dirac (p := p) (K := K)) := by
  intro x y hxy
  refine PadicInt.ext_of_toZModPow.mp fun h ↦ ?_
  have heval := DFunLike.congr_fun (congrArg (stage h) hxy)
    (single (PadicInt.toZModPow h x, 0) (1 : K))
  simp only [stage_dirac_apply, eval_single, pow_zero, one_smul] at heval
  by_contra hne
  simp [Ne.symm hne] at heval

/-- Two point-mass distributions are equal if and only if they are supported at the same point. -/
@[simp]
theorem dirac_inj {x y : ℤ_[p]} : dirac (p := p) (K := K) x = dirac y ↔ x = y :=
  dirac_injective.eq_iff

/-! ### Stage-level right convolution specializations -/

/-- For a distribution `ν`, the stage-level right convolution operators commute with adjacent
transitions. -/
theorem convolveFunRightStage_stage_transition (ν : LocallyAnalyticDistribution p K) {h : ℕ}
    (c : AnalyticStage p h K) :
    convolveFunRightStage (stage (h + 1) ν) (transition K c) =
      transition K (convolveFunRightStage (stage h ν) c) := by
  rw [convolveFunRightStage_transition, stage_comp_transition]

/-- For a distribution `ν`, the stage-level right convolution operators commute with multi-level
transitions. -/
theorem convolveFunRightStage_stage_transitionLE (ν : LocallyAnalyticDistribution p K) {h k : ℕ}
    (hhk : h ≤ k) (c : AnalyticStage p h K) :
    convolveFunRightStage (stage k ν) (transitionLE K hhk c) =
      transitionLE K hhk (convolveFunRightStage (stage h ν) c) := by
  rw [convolveFunRightStage_transitionLE, stage_comp_transitionLE]

/-- Stage-level right convolution with a Dirac distribution at `x` is translation by `x`. -/
@[simp]
theorem convolveFunRightStage_stage_dirac_apply (x : ℤ_[p]) {h : ℕ} (c : AnalyticStage p h K) :
    convolveFunRightStage (stage h (dirac x)) c = AnalyticStage.translate K x c := by
  ext i
  simp

/-! ### Stage-by-stage additive convolution and `CommRing` / `Algebra` structure -/

/-- The convolution unit of `LocallyAnalyticDistribution p K` is the point mass `dirac 0`. -/
noncomputable instance : One (LocallyAnalyticDistribution p K) where
  one := dirac 0

/-- The convolution unit `1` is the point mass at `0`. -/
theorem one_def : (1 : LocallyAnalyticDistribution p K) = dirac 0 := (rfl)

/-- The point mass at `0` is the convolution unit `1`. -/
@[simp]
theorem dirac_zero : dirac (p := p) (K := K) 0 = 1 := (rfl)

/-- The convolution unit `1` evaluates a locally analytic function at `0`. -/
@[simp]
theorem coe_one_apply (f : LocallyAnalytic p K K) :
    ((1 : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f 0 :=
  coe_dirac_apply 0 f

instance : Nontrivial (LocallyAnalyticDistribution p K) :=
  nontrivial_of_ne 1 0 (dirac_ne_zero 0)

/-- **Additive convolution of locally analytic distributions**, defined on each analytic stage
`LA_h(K)` by composing `stage h μ` with `convolveFunRightStage (stage h ν)`. -/
noncomputable instance : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν := stagesEquiv.symm
    ⟨fun h ↦ (stage h μ).comp (convolveFunRightStage (stage h ν)),
      mem_compatibleStageFunctionals_iff.mpr fun h ↦ by
        ext c
        simp only [ContinuousLinearMap.comp_apply, convolveFunRightStage_stage_transition]
        rw [← ContinuousLinearMap.comp_apply (stage (h + 1) μ), stage_comp_transition μ h]⟩

/-- On the stage `LA_h(K)`, the convolution unit `1` evaluates the `(0, 0)`-coordinate. -/
@[simp]
theorem stage_one (h : ℕ) :
    stage h (1 : LocallyAnalyticDistribution p K) = evalCLM K (0, 0) := by
  ext c
  rw [one_def, stage_dirac_apply, eval_apply_zero, evalCLM_apply]

/-- Restricting the convolution `μ * ν` to stage `h` composes `stage h μ` with the stage-level
right convolution operator of `stage h ν`. -/
theorem stage_mul_eq_comp_convolveFunRightStage (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stage h (μ * ν) = (stage h μ).comp (convolveFunRightStage (stage h ν)) :=
  stage_stagesEquiv_symm _ h

/-- On the stage `LA_h(K)`, `μ * ν` is the two-variable product functional of `stage h μ` and
`stage h ν` composed with `comul K`. -/
theorem stage_mul (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stage h (μ * ν) =
      (prodFunctional (stage h μ) (stage h ν)
        ((stage h ν).bound.imp fun _ hb ↦ hb.2)).comp (comul K) := by
  ext c
  rw [stage_mul_eq_comp_convolveFunRightStage, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, prodFunctional_apply, curryEquiv_comul]
  exact congrArg (stage h μ) (by ext i; simp)

/-- **Submultiplicativity of the stage seminorms** under additive convolution. -/
theorem stageSeminorm_mul_le (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stageSeminorm_apply, stage_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [opNorm_prodFunctional]
  exact mul_le_of_le_one_right (by positivity) opNorm_comul_le_one

/-- Every stage seminorm of the convolution unit `1` equals `1`. -/
theorem stageSeminorm_one (h : ℕ) :
    stageSeminorm h (1 : LocallyAnalyticDistribution p K) = 1 := by
  simp

noncomputable instance : MulZeroClass (LocallyAnalyticDistribution p K) where
  zero_mul ν := LocallyAnalyticDistribution.ext fun h ↦ by
    simp [stage_mul_eq_comp_convolveFunRightStage]
  mul_zero μ := LocallyAnalyticDistribution.ext fun h ↦ by
    simp [stage_mul_eq_comp_convolveFunRightStage]

noncomputable instance : Distrib (LocallyAnalyticDistribution p K) where
  left_distrib μ ν₁ ν₂ := LocallyAnalyticDistribution.ext fun h ↦ by
    simp [stage_mul_eq_comp_convolveFunRightStage]
  right_distrib μ₁ μ₂ ν := LocallyAnalyticDistribution.ext fun h ↦ by
    simp [stage_mul_eq_comp_convolveFunRightStage]

noncomputable instance : NonUnitalNonAssocRing (LocallyAnalyticDistribution p K) where
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero

noncomputable instance : Ring (LocallyAnalyticDistribution p K) where
  mul_assoc μ ν ρ := LocallyAnalyticDistribution.ext fun h ↦ by
    simp only [stage_mul_eq_comp_convolveFunRightStage, convolveFunRightStage_comp,
      ContinuousLinearMap.comp_assoc]
  one_mul ν := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
    simp [stage_mul_eq_comp_convolveFunRightStage]
  mul_one μ := LocallyAnalyticDistribution.ext fun h ↦ by
    rw [stage_mul_eq_comp_convolveFunRightStage, stage_one, convolveFunRightStage_evalCLM_zero,
      ContinuousLinearMap.comp_id]

/-- Locally analytic distributions form a commutative ring under additive convolution, with unit
`1 = dirac 0`. -/
noncomputable instance : CommRing (LocallyAnalyticDistribution p K) where
  mul_comm μ ν := LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
    simp only [stage_mul, ContinuousLinearMap.comp_apply]
    rw [← prodFunctional_comp_congrLeft_prodComm (stage h ν)
      ((stage h ν).bound.imp fun _ hb ↦ hb.2) (stage h μ)
      ((stage h μ).bound.imp fun _ hb ↦ hb.2)]
    simp

/-- Locally analytic distributions form a commutative `K`-algebra under additive convolution, with
scalar action inherited without diamond from the defining `Submodule K`. -/
noncomputable instance : Algebra K (LocallyAnalyticDistribution p K) :=
  have hsmul_mul (r : K) (μ ν : LocallyAnalyticDistribution p K) : (r • μ) * ν = r • (μ * ν) :=
    LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ by
      simp [stage_mul_eq_comp_convolveFunRightStage]
  Algebra.ofModule hsmul_mul fun r μ ν ↦ by
    rw [mul_comm, hsmul_mul, mul_comm]

-- Defeq sanity checks against `Submodule` additive and module structures.
example : (inferInstance : CommRing (LocallyAnalyticDistribution p K)).toAddCommGroup =
    Submodule.addCommGroup (LocallyAnalyticDistribution p K) := rfl

example : (inferInstance : Algebra K (LocallyAnalyticDistribution p K)).toModule =
    Submodule.module (LocallyAnalyticDistribution p K) := rfl

/-- A scalar distribution `algebraMap K _ a` evaluates a locally analytic function at `0`, scaled
by `a`. -/
@[simp]
theorem coe_algebraMap_apply (a : K) (f : LocallyAnalytic p K K) :
    (algebraMap K (LocallyAnalyticDistribution p K) a :
      Module.Dual K (LocallyAnalytic p K K)) f = a * LocallyAnalytic.eval K f 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp

/-- On the stage `LA_h(K)`, `algebraMap K _ a` is `a • evalCLM K (0, 0)`. -/
@[simp]
theorem stage_algebraMap (h : ℕ) (a : K) :
    stage h (algebraMap K (LocallyAnalyticDistribution p K) a) = a • evalCLM K (0, 0) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, stage_one]

/-- Every stage seminorm of a scalar distribution `algebraMap K _ a` equals `‖a‖`. -/
theorem stageSeminorm_algebraMap (h : ℕ) (a : K) :
    stageSeminorm h (algebraMap K (LocallyAnalyticDistribution p K) a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, stageSeminorm_one, mul_one]

/-- Convolution of point-mass distributions corresponds to addition in `ℤ_p`. -/
theorem dirac_add (x y : ℤ_[p]) :
    dirac (p := p) (K := K) (x + y) = dirac x * dirac y := by
  refine LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ ?_
  rw [stage_mul_eq_comp_convolveFunRightStage, ContinuousLinearMap.comp_apply,
    convolveFunRightStage_stage_dirac_apply, stage_dirac_apply, stage_dirac_apply,
    AnalyticStage.eval_translate, add_comm]

/-- Point-mass distributions as a monoid homomorphism from `Multiplicative ℤ_p`. -/
noncomputable def diracHom : Multiplicative ℤ_[p] →* LocallyAnalyticDistribution p K where
  toFun x := dirac x.toAdd
  map_one' := dirac_zero
  map_mul' x y := dirac_add x.toAdd y.toAdd

/-- `diracHom` sends `x : Multiplicative ℤ_p` to `dirac x.toAdd`. -/
@[simp]
theorem diracHom_apply (x : Multiplicative ℤ_[p]) :
    diracHom (p := p) (K := K) x = dirac x.toAdd := (rfl)

/-! ### Comparison with native convolution of measures -/

/-- **Compatibility of `ofMeasure` with additive convolution of measures on `ℤ_p`.** Pushing the
product measure `μ.prodMk' ν` forward along `+ : ℤ_p × ℤ_p → ℤ_p` and viewing the result as a
locally analytic distribution gives the stage-wise convolution `ofMeasure μ * ofMeasure ν`. -/
theorem ofMeasure_map_add_prodMk' (μ ν : D(ℤ_[p], K)) :
    ofMeasure (p := p) (K := K)
        (AbstractMeasure.map ⟨fun q : ℤ_[p] × ℤ_[p] ↦ q.1 + q.2, continuous_add⟩ (μ.prodMk' ν)) =
      ofMeasure μ * ofMeasure ν := by
  refine LocallyAnalyticDistribution.ext fun h ↦ ContinuousLinearMap.ext fun c ↦ ?_
  simp only [stage_ofMeasure, ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv,
    AbstractMeasure.map_apply, AbstractMeasure.prodMk'_apply,
    stage_mul_eq_comp_convolveFunRightStage]
  refine congrArg μ (ContinuousMap.ext fun x ↦ ?_)
  simp only [ContinuousMap.comp_apply, ContinuousLinearMap.comp_apply,
    AbstractMeasure.coe_toCLMEquiv, AbstractMeasure.contractSnd_apply, eval_convolveFunRightStage]
  refine congrArg ν (ContinuousMap.ext fun y ↦ ?_)
  simp

/-- **Embedding of multiplicative `ℤ_p`-measures as a `K`-algebra homomorphism.** Transports a
measure on `Multiplicative ℤ_p` along `Homeomorph.ofAdd.symm` and views it as a locally analytic
distribution on `ℤ_p`, intertwining Mathlib's measure convolution with distribution convolution. -/
noncomputable def ofMulMeasure :
    D(Multiplicative ℤ_[p], K) →ₐ[K] LocallyAnalyticDistribution p K :=
  AlgHom.ofLinearMap
    (ofMeasure.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).toLinearMap)
    (by simp [AbstractMeasure.coe_arrowCongrLeft, AbstractMeasure.one_def])
    (fun μ ν ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      have hpush : AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm (μ * ν) =
          AbstractMeasure.map ⟨fun q : ℤ_[p] × ℤ_[p] ↦ q.1 + q.2, continuous_add⟩
            ((AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ).prodMk'
              (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm ν)) := by
        ext g
        simp only [AbstractMeasure.mul_def, AbstractMeasure.arrowCongrLeft_apply,
          AbstractMeasure.map_apply, AbstractMeasure.prodMk'_apply]
        refine congrArg μ (ContinuousMap.ext fun x ↦ ?_)
        simp only [ContinuousMap.comp_apply, AbstractMeasure.contractSnd_apply,
          AbstractMeasure.arrowCongrLeft_apply]
        refine congrArg ν (ContinuousMap.ext fun y ↦ ?_)
        simp [ContinuousMap.comp_apply, toAdd_mul]
      rw [hpush, ofMeasure_map_add_prodMk'])

/-- `ofMulMeasure` applies `ofMeasure` after transporting along `Homeomorph.ofAdd.symm`. -/
theorem ofMulMeasure_apply (μ : D(Multiplicative ℤ_[p], K)) :
    ofMulMeasure (p := p) (K := K) μ =
      ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ) :=
  (rfl)

/-- Transporting an additive `ℤ_p`-measure along `Homeomorph.ofAdd` and applying `ofMulMeasure`
recovers `ofMeasure`. -/
@[simp]
theorem ofMulMeasure_ofAdd (μ : D(ℤ_[p], K)) :
    ofMulMeasure (p := p) (K := K) (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd μ) =
      ofMeasure μ := by
  rw [ofMulMeasure_apply, ← AbstractMeasure.arrowCongrLeft_symm, LinearEquiv.symm_apply_apply]

/-- `ofMulMeasure` sends the Dirac measure at `x : Multiplicative ℤ_p` to `dirac x.toAdd`. -/
@[simp]
theorem ofMulMeasure_dirac (x : Multiplicative ℤ_[p]) :
    ofMulMeasure (p := p) (K := K) (AbstractMeasure.dirac K x) = dirac x.toAdd := by
  simp [ofMulMeasure_apply, AbstractMeasure.coe_arrowCongrLeft]

/-- The `K`-algebra homomorphism `ofMulMeasure` is injective. -/
theorem ofMulMeasure_injective :
    Function.Injective (ofMulMeasure (p := p) (K := K)) :=
  ofMeasure_injective.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).injective

/-- Every stage seminorm of `ofMulMeasure μ` is bounded by the measure norm of `μ`. -/
theorem stageSeminorm_ofMulMeasure_le (μ : D(Multiplicative ℤ_[p], K)) (h : ℕ) :
    stageSeminorm h (ofMulMeasure (p := p) (K := K) μ) ≤ ‖AbstractMeasure.toCLMEquiv μ‖ := by
  rw [ofMulMeasure_apply, AbstractMeasure.coe_arrowCongrLeft]
  exact (stageSeminorm_ofMeasure_le _ h).trans (AbstractMeasure.norm_toCLMEquiv_map_le μ _)

/-! ### Right convolution on test functions -/

/-- Stage-level right convolution is associative with respect to distribution convolution. -/
theorem convolveFunRightStage_stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    convolveFunRightStage (stage h (μ * ν)) =
      (convolveFunRightStage (stage h μ)).comp (convolveFunRightStage (stage h ν)) := by
  rw [stage_mul_eq_comp_convolveFunRightStage, convolveFunRightStage_comp]

/-- Right convolution of a locally analytic function with a distribution: sends `f` to the locally
analytic function `x ↦ ν (y ↦ f (x + y))`. -/
noncomputable def convolveFunRight :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalytic p K K →ₗ[K] LocallyAnalytic p K K where
  toFun ν := Module.DirectLimit.map
    (fun h ↦ (convolveFunRightStage (stage h ν)).toLinearMap)
    (fun _ _ hhk ↦ LinearMap.ext (convolveFunRightStage_stage_transitionLE ν hhk))
  map_add' ν₁ ν₂ := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.DirectLimit.map_apply_of,
      ContinuousLinearMap.coe_coe, map_add, _root_.add_apply]
  map_smul' a ν := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply,
      Module.DirectLimit.map_apply_of, ContinuousLinearMap.coe_coe, map_smul,
      _root_.smul_apply]

/-- Right convolution restricts to `convolveFunRightStage (stage h ν)` on stage `h`. -/
@[simp]
theorem convolveFunRight_ofStage (ν : LocallyAnalyticDistribution p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    convolveFunRight ν (ofStage K h c) =
      ofStage K h (convolveFunRightStage (stage h ν) c) := by
  simp [convolveFunRight, ofStage_def]

/-- Evaluating `convolveFunRight ν f` at `x` applies `ν` to the translate of `f` by `x`. -/
@[simp]
theorem eval_convolveFunRight (ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K)
    (x : ℤ_[p]) :
    LocallyAnalytic.eval K (convolveFunRight ν f) x =
      (ν : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.translate K x f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, eval_ofStage, eval_convolveFunRightStage,
    LocallyAnalytic.translate_ofStage, stage_apply]

/-- Evaluating `convolveFunRight ν f` at `0` recovers `ν f`. -/
theorem eval_convolveFunRight_zero (ν : LocallyAnalyticDistribution p K)
    (f : LocallyAnalytic p K K) :
    LocallyAnalytic.eval K (convolveFunRight ν f) 0 =
      (ν : Module.Dual K (LocallyAnalytic p K K)) f := by
  simp

/-- The right convolution action `convolveFunRight` is injective. -/
theorem convolveFunRight_injective :
    Function.Injective (convolveFunRight (p := p) (K := K)) := by
  intro μ ν hμν
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  simpa only [eval_convolveFunRight_zero] using
    congrArg (fun T ↦ LocallyAnalytic.eval K (T f) 0) hμν

/-- Right convolution with a Dirac distribution at `x` is translation by `x`. -/
@[simp]
theorem convolveFunRight_dirac (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    convolveFunRight (dirac x) f = LocallyAnalytic.translate K x f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, convolveFunRightStage_stage_dirac_apply,
    LocallyAnalytic.translate_ofStage]

/-- Right convolution with `1` is the identity on locally analytic functions. -/
@[simp]
theorem convolveFunRight_one (f : LocallyAnalytic p K K) :
    convolveFunRight (1 : LocallyAnalyticDistribution p K) f = f := by
  rw [one_def, convolveFunRight_dirac, LocallyAnalytic.translate_zero]

/-- Applying the convolution `μ * ν` to `f` applies `μ` to `convolveFunRight ν f`. -/
@[simp]
theorem coe_mul_apply (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    ((μ * ν : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (convolveFunRight ν f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, ← stage_apply, ← stage_apply,
    stage_mul_eq_comp_convolveFunRightStage, ContinuousLinearMap.comp_apply]

/-- Right convolution turns `LocallyAnalytic p K K` into a module action of the convolution
algebra: `convolveFunRight (μ * ν) = convolveFunRight μ ∘ convolveFunRight ν`. -/
theorem convolveFunRight_mul (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    convolveFunRight (μ * ν) f = convolveFunRight μ (convolveFunRight ν f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, convolveFunRight_ofStage, convolveFunRight_ofStage,
    convolveFunRightStage_stage_mul, ContinuousLinearMap.comp_apply]

end TauCeti.LocallyAnalyticDistribution
