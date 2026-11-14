/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.GaussianLimit

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.IsGaussianProcess

/-!
# Coordinate vector Brownian motion

An indexed family of scalar processes `B : ι → ℝ≥0 → Ω → ℝ` is a **coordinate vector pre-Brownian
motion** (`TauCeti.Probability.IsPreBrownianVector B P`) if each `B i` satisfies
`ProbabilityTheory.IsPreBrownianReal` and the coordinate path maps `ω ↦ (B i · ω)` are mutually
independent (`ProbabilityTheory.iIndepFun`). Requiring almost-sure sample-path continuity in every
coordinate defines **coordinate vector Brownian motion** (`TauCeti.Probability.IsBrownianVector`).

Because independent Gaussian processes are jointly Gaussian (`iIndepFun.isGaussianProcess_prod`),
`IsPreBrownianVector` is equivalent to joint centered Gaussianity on `ι × ℝ≥0` with cross-covariance
`δᵢⱼ min s t`. From this we derive invariance under row-orthonormal and orthogonal matrices,
multivariate Gaussian increment laws, and independence of future increments from the past.

## Main declarations

* `TauCeti.Probability.IsPreBrownianVector`, `TauCeti.Probability.IsBrownianVector`: coordinate
  vector pre-Brownian and Brownian motion indexed by `ι`.
* `TauCeti.Probability.isPreBrownianVector_iff_isGaussianProcess`: centered Gaussian `δᵢⱼ min s t`
  covariance characterization.
* `TauCeti.Probability.IsPreBrownianVector.mulVec_of_mul_transpose_eq_one`,
  `TauCeti.Probability.IsPreBrownianVector.orthogonal`,
  `TauCeti.Probability.IsBrownianVector.orthogonal`: row-orthonormal and orthogonal invariance.
* `TauCeti.Probability.IsPreBrownianVector.hasLaw_toLp_sub`,
  `TauCeti.Probability.IsPreBrownianVector.indepFun_sub_past`: multivariate Gaussian increment laws
  and past independence.
* `TauCeti.Probability.isPreBrownianVector_eval_pi_gaussianLimit`: canonical coordinate vector
  pre-Brownian motion on `ι → ℝ≥0 → ℝ` for finite `ι`.

## References

* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, §1.1, §2.2.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1, §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Matrix

namespace TauCeti.Probability

variable {ι κ Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B C : ι → ℝ≥0 → Ω → ℝ}

/-- An `ι`-indexed family of scalar processes is a **coordinate vector pre-Brownian motion** under
`P` if every coordinate satisfies `ProbabilityTheory.IsPreBrownianReal` and the coordinate paths are
mutually independent as `(ℝ≥0 → ℝ)`-valued random variables. -/
structure IsPreBrownianVector (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop where
  /-- Each coordinate process is a scalar pre-Brownian motion. -/
  isPreBrownianReal : ∀ i, IsPreBrownianReal (B i) P
  /-- The coordinate paths are mutually independent in the product `σ`-algebra on `ℝ≥0 → ℝ`. -/
  iIndepFun : iIndepFun (fun i ω t ↦ B i t ω) P

/-- An `ι`-indexed family of scalar processes is a **coordinate vector Brownian motion** under `P`
if it is a coordinate vector pre-Brownian motion and every coordinate has a.s. continuous paths. -/
structure IsBrownianVector (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownianVector B P where
  /-- Each coordinate has almost-surely continuous paths. -/
  ae_continuous : ∀ i, ∀ᵐ ω ∂P, Continuous (B i · ω)

namespace IsBrownianVector

/-- Each coordinate of a vector Brownian motion is a scalar Brownian motion. -/
theorem isBrownianReal (hB : IsBrownianVector B P) (i : ι) : IsBrownianReal (B i) P :=
  ⟨hB.isPreBrownianReal i, hB.ae_continuous i⟩

/-- Construct `IsBrownianVector` from coordinatewise `IsBrownianReal` and path independence. -/
theorem of_isBrownianReal (h₁ : ∀ i, IsBrownianReal (B i) P)
    (h₂ : iIndepFun (fun i ω t ↦ B i t ω) P) : IsBrownianVector B P :=
  ⟨⟨fun i ↦ (h₁ i).toIsPreBrownianReal, h₂⟩, fun i ↦ (h₁ i).cont⟩

end IsBrownianVector

/-- `IsBrownianVector B P` holds iff every coordinate satisfies `IsBrownianReal` and coordinate
paths are mutually independent. -/
theorem isBrownianVector_iff :
    IsBrownianVector B P ↔
      (∀ i, IsBrownianReal (B i) P) ∧ iIndepFun (fun i ω t ↦ B i t ω) P :=
  ⟨fun h ↦ ⟨h.isBrownianReal, h.iIndepFun⟩, fun ⟨h₁, h₂⟩ ↦ .of_isBrownianReal h₁ h₂⟩

namespace IsPreBrownianVector

/-- A space carrying a coordinate vector pre-Brownian motion is a probability space. -/
theorem isProbabilityMeasure (hB : IsPreBrownianVector B P) : IsProbabilityMeasure P :=
  hB.iIndepFun.iIndep.isProbabilityMeasure

/-- Fixed-time a.e. modifications preserve `IsPreBrownianVector`. -/
theorem congr (hB : IsPreBrownianVector B P) (h : ∀ i t, B i t =ᵐ[P] C i t) :
    IsPreBrownianVector C P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).congr (h i), hB.iIndepFun.process_congr h⟩

/-- Over an empty index type (`d = 0`), `IsPreBrownianVector` holds vacuously. -/
theorem of_isEmpty [IsEmpty ι] [IsProbabilityMeasure P] (B : ι → ℝ≥0 → Ω → ℝ) :
    IsPreBrownianVector B P :=
  ⟨fun i ↦ isEmptyElim i, .of_subsingleton⟩

/-- Restricting coordinates along an injective map preserves `IsPreBrownianVector`. -/
theorem precomp {g : κ → ι} (hg : Function.Injective g) (hB : IsPreBrownianVector B P) :
    IsPreBrownianVector (fun k ↦ B (g k)) P :=
  ⟨fun k ↦ hB.isPreBrownianReal (g k), hB.iIndepFun.precomp hg⟩

/-- The joint family `(i, t) ↦ B i t` is a Gaussian process on `ι × ℝ≥0`. -/
theorem isGaussianProcess (hB : IsPreBrownianVector B P) :
    IsGaussianProcess (fun (p : ι × ℝ≥0) ω ↦ B p.1 p.2 ω) P :=
  hB.iIndepFun.isGaussianProcess_prod fun i ↦ (hB.isPreBrownianReal i).isGaussianProcess

/-- Every coordinate time marginal of a vector pre-Brownian motion is a.e. measurable. -/
theorem aemeasurable (hB : IsPreBrownianVector B P) (i : ι) (t : ℝ≥0) :
    AEMeasurable (B i t) P :=
  (hB.isPreBrownianReal i).aemeasurable t

/-- Every coordinate time marginal of a vector pre-Brownian motion is centered. -/
@[simp]
theorem integral_eval (hB : IsPreBrownianVector B P) (i : ι) (t : ℝ≥0) : P[B i t] = 0 :=
  (hB.isPreBrownianReal i).integral_eval t

/-- Every coordinate of a vector pre-Brownian motion starts at `0` almost surely. -/
theorem eval_zero_ae_eq_zero (hB : IsPreBrownianVector B P) (i : ι) : ∀ᵐ ω ∂P, B i 0 ω = 0 :=
  (hB.isPreBrownianReal i).eval_zero_ae_eq_zero

/-- Every coordinate time marginal of a vector pre-Brownian motion is square-integrable. -/
theorem memLp_two_eval (hB : IsPreBrownianVector B P) (i : ι) (t : ℝ≥0) : MemLp (B i t) 2 P :=
  ((hB.isPreBrownianReal i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- Cross-covariance of coordinates of `B`: `min s t` on the diagonal and `0` off the diagonal. -/
theorem covariance_eval [DecidableEq ι] (hB : IsPreBrownianVector B P) (i j : ι) (s t : ℝ≥0) :
    cov[B i s, B j t; P] = if i = j then (min s t : ℝ) else 0 := by
  have := hB.isProbabilityMeasure
  split_ifs with hij
  · exact hij ▸ (hB.isPreBrownianReal i).covariance_eval s t
  · exact ((hB.iIndepFun.indepFun hij).comp (measurable_pi_apply s)
      (measurable_pi_apply t)).covariance_eq_zero (hB.memLp_two_eval i s) (hB.memLp_two_eval j t)

/-- Uncurried form of `IsPreBrownianVector.covariance_eval` for lambda expressions. -/
theorem covariance_fun_eval [DecidableEq ι] (hB : IsPreBrownianVector B P)
    (i j : ι) (s t : ℝ≥0) :
    cov[fun ω ↦ B i s ω, fun ω ↦ B j t ω; P] = if i = j then (min s t : ℝ) else 0 :=
  hB.covariance_eval i j s t

/-- Distinct coordinates of a vector pre-Brownian motion cannot agree a.e. at any `t > 0`. -/
theorem ne_ae_eq_of_pos (hB : IsPreBrownianVector B P) {i j : ι} (hij : i ≠ j)
    {t : ℝ≥0} (ht : 0 < t) : ¬ (B i t =ᵐ[P] B j t) := by
  classical
  intro heq
  have := hB.isProbabilityMeasure
  have hcov0 : cov[B i t, B j t; P] = 0 := by simp [hB.covariance_eval, hij]
  have hcongr : cov[B i t, B j t; P] = cov[B i t, B i t; P] := by
    rw [covariance, covariance, integral_congr_ae heq]
    exact integral_congr_ae (heq.mono fun _ hω ↦ by dsimp only; rw [hω])
  rw [hcongr, (hB.isPreBrownianReal i).covariance_eval, min_self] at hcov0
  linarith [NNReal.coe_pos.mpr ht]

/-- Negating every coordinate preserves `IsPreBrownianVector`. -/
theorem neg (hB : IsPreBrownianVector B P) : IsPreBrownianVector (-B) P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).neg,
    hB.iIndepFun.comp (fun _ x t ↦ -x t) fun _ ↦ .of_eval fun t ↦ (measurable_pi_apply t).neg⟩

/-- Brownian diffusive scaling `(√c)⁻¹ * B i (c * t)` (`c ≠ 0`) preserves `IsPreBrownianVector`. -/
theorem smul (hB : IsPreBrownianVector B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownianVector (fun i t ω ↦ (√(c : ℝ))⁻¹ * B i (c * t) ω) P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).smul hc,
    hB.iIndepFun.comp (fun _ x t ↦ (√(c : ℝ))⁻¹ * x (c * t))
      fun _ ↦ .of_eval fun t ↦ (measurable_pi_apply (c * t)).const_mul _⟩

/-- Deterministic time shift `B i (t₀ + t) - B i t₀` preserves `IsPreBrownianVector`. -/
theorem shift (hB : IsPreBrownianVector B P) (t₀ : ℝ≥0) :
    IsPreBrownianVector (fun i t ω ↦ B i (t₀ + t) ω - B i t₀ ω) P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).shift t₀,
    hB.iIndepFun.comp (fun _ x t ↦ x (t₀ + t) - x t₀)
      fun _ ↦ .of_eval fun t ↦ (measurable_pi_apply (t₀ + t)).sub (measurable_pi_apply t₀)⟩

end IsPreBrownianVector

namespace IsBrownianVector

/-- Indistinguishable coordinatewise modifications preserve `IsBrownianVector`. -/
theorem congr_indistinguishable (hB : IsBrownianVector B P) (h : ∀ i, B i ≡ᵐ[P] C i) :
    IsBrownianVector C P :=
  ⟨hB.toIsPreBrownianVector.congr fun i t ↦ (h i).mono fun _ hω ↦ hω t,
    fun i ↦ (hB.ae_continuous i).mp ((h i).mono fun _ hω hc ↦ by simpa [funext hω] using hc)⟩

/-- Over an empty index type (`d = 0`), `IsBrownianVector` holds vacuously. -/
theorem of_isEmpty [IsEmpty ι] [IsProbabilityMeasure P] (B : ι → ℝ≥0 → Ω → ℝ) :
    IsBrownianVector B P :=
  ⟨.of_isEmpty B, fun i ↦ isEmptyElim i⟩

/-- Restricting coordinates along an injective map preserves `IsBrownianVector`. -/
theorem precomp {g : κ → ι} (hg : Function.Injective g) (hB : IsBrownianVector B P) :
    IsBrownianVector (fun k ↦ B (g k)) P :=
  ⟨hB.toIsPreBrownianVector.precomp hg, fun k ↦ hB.ae_continuous (g k)⟩

/-- On a countable index type, almost every path `t ↦ (i ↦ B i t ω)` is jointly continuous. -/
theorem ae_continuous_pi [Countable ι] (hB : IsBrownianVector B P) :
    ∀ᵐ ω ∂P, Continuous (fun t i ↦ B i t ω) :=
  (ae_all_iff.mpr hB.ae_continuous).mono fun _ ↦ continuous_pi

/-- Negating every coordinate preserves `IsBrownianVector`. -/
theorem neg (hB : IsBrownianVector B P) : IsBrownianVector (-B) P :=
  ⟨hB.toIsPreBrownianVector.neg, fun i ↦ (hB.isBrownianReal i).neg.cont⟩

/-- Brownian diffusive scaling `(√c)⁻¹ * B i (c * t)` (`c ≠ 0`) preserves `IsBrownianVector`. -/
theorem smul (hB : IsBrownianVector B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianVector (fun i t ω ↦ (√(c : ℝ))⁻¹ * B i (c * t) ω) P :=
  ⟨hB.toIsPreBrownianVector.smul hc, fun i ↦ ((hB.isBrownianReal i).smul hc).cont⟩

/-- Deterministic time shift `B i (t₀ + t) - B i t₀` preserves `IsBrownianVector`. -/
theorem shift (hB : IsBrownianVector B P) (t₀ : ℝ≥0) :
    IsBrownianVector (fun i t ω ↦ B i (t₀ + t) ω - B i t₀ ω) P :=
  ⟨hB.toIsPreBrownianVector.shift t₀, fun i ↦ ((hB.isBrownianReal i).shift t₀).cont⟩

end IsBrownianVector

/-- For `[Unique ι]`, `IsPreBrownianVector B P` iff `IsPreBrownianReal (B default) P`. -/
@[simp]
theorem isPreBrownianVector_unique_iff [Unique ι] :
    IsPreBrownianVector B P ↔ IsPreBrownianReal (B default) P :=
  ⟨fun h ↦ h.isPreBrownianReal default, fun h ↦
    have := h.isGaussianProcess.isProbabilityMeasure
    ⟨fun i ↦ Unique.eq_default i ▸ h, .of_subsingleton⟩⟩

/-- For `[Unique ι]`, `IsBrownianVector B P` is equivalent to `IsBrownianReal (B default) P`. -/
@[simp]
theorem isBrownianVector_unique_iff [Unique ι] :
    IsBrownianVector B P ↔ IsBrownianReal (B default) P := by
  rw [isBrownianVector_iff]
  exact ⟨fun ⟨h, _⟩ ↦ h default, fun h ↦
    have := h.isGaussianProcess.isProbabilityMeasure
    ⟨fun i ↦ Unique.eq_default i ▸ h, .of_subsingleton⟩⟩

/-- Bijective reindexing of coordinates preserves and reflects `IsPreBrownianVector`. -/
theorem isPreBrownianVector_precomp_of_bijective {g : κ → ι} (hg : Function.Bijective g) :
    IsPreBrownianVector (fun k ↦ B (g k)) P ↔ IsPreBrownianVector B P := by
  let e := Equiv.ofBijective g hg
  exact ⟨fun h ↦ by simpa [e, Equiv.ofBijective_apply_symm_apply] using h.precomp e.symm.injective,
    fun h ↦ h.precomp hg.injective⟩

/-- Bijective reindexing of coordinates preserves and reflects `IsBrownianVector`. -/
theorem isBrownianVector_precomp_of_bijective {g : κ → ι} (hg : Function.Bijective g) :
    IsBrownianVector (fun k ↦ B (g k)) P ↔ IsBrownianVector B P := by
  let e := Equiv.ofBijective g hg
  exact ⟨fun h ↦ by simpa [e, Equiv.ofBijective_apply_symm_apply] using h.precomp e.symm.injective,
    fun h ↦ h.precomp hg.injective⟩

/-- A centered jointly Gaussian family `B : ι → ℝ≥0 → Ω → ℝ` with cross-covariance `δᵢⱼ min s t`
is a coordinate vector pre-Brownian motion. -/
theorem isPreBrownianVector_of_isGaussianProcess [DecidableEq ι]
    (hG : IsGaussianProcess (fun (p : ι × ℝ≥0) ω ↦ B p.1 p.2 ω) P)
    (hmean : ∀ i t, P[B i t] = 0)
    (hcov : ∀ i j s t, cov[B i s, B j t; P] = if i = j then (min s t : ℝ) else 0) :
    IsPreBrownianVector B P where
  isPreBrownianReal i :=
    (hG.comp_right (Prod.mk i)).isPreBrownianReal_of_covariance (hmean i) fun s t hst ↦ by
      simpa [Function.comp_def, min_eq_left (NNReal.coe_le_coe.mpr hst)] using hcov i i s t
  iIndepFun := (hG.comp_right fun p : (_ : ι) × ℝ≥0 ↦ (p.1, p.2)).iIndepFun_of_covariance_eq_zero
    (fun i t ↦ hG.aemeasurable (i, t)) fun i j hij s t ↦ by simpa [hij] using hcov i j s t

/-- Intrinsic Gaussian characterization of `IsPreBrownianVector`: joint centered Gaussianity on
`ι × ℝ≥0` with cross-covariance `if i = j then min s t else 0`. -/
theorem isPreBrownianVector_iff_isGaussianProcess [DecidableEq ι] :
    IsPreBrownianVector B P ↔
      IsGaussianProcess (fun (p : ι × ℝ≥0) ω ↦ B p.1 p.2 ω) P ∧
        (∀ i t, P[B i t] = 0) ∧
        (∀ i j s t, cov[B i s, B j t; P] = if i = j then (min s t : ℝ) else 0) :=
  ⟨fun h ↦ ⟨h.isGaussianProcess, h.integral_eval, h.covariance_eval⟩,
    fun ⟨hG, hm, hc⟩ ↦ isPreBrownianVector_of_isGaussianProcess hG hm hc⟩

namespace IsPreBrownianVector

/-- Applying a row-orthonormal matrix `A : Matrix κ ι ℝ` (`A * Aᵀ = 1`) to a coordinate vector
pre-Brownian motion yields a coordinate vector pre-Brownian motion indexed by `κ`. -/
theorem mulVec_of_mul_transpose_eq_one [Fintype ι] [DecidableEq κ]
    (hB : IsPreBrownianVector B P) {A : Matrix κ ι ℝ} (hA : A * Aᵀ = 1) :
    IsPreBrownianVector (fun k t ω ↦ ∑ i, A k i * B i t ω) P := by
  classical
  have := hB.isProbabilityMeasure
  refine isPreBrownianVector_of_isGaussianProcess
    (hB.isGaussianProcess.of_isGaussianProcess fun q ↦ ⟨univ ×ˢ {q.2},
      { toFun z := ∑ i : ι,
          A q.1 i * z ⟨(i, q.2), mem_product.mpr ⟨mem_univ i, mem_singleton_self q.2⟩⟩
        map_add' _ _ := by simp [mul_add, sum_add_distrib]
        map_smul' _ _ := by simp [mul_sum, mul_left_comm]
        cont := by fun_prop }, fun _ ↦ by simp [restrict_def]⟩)
    (fun k t ↦ by
      rw [integral_finsetSum _ fun i _ ↦ ((hB.isPreBrownianReal i).integrable_eval t).const_mul _]
      simp [integral_const_mul, hB.integral_eval])
    fun k₁ k₂ s t ↦ ?_
  rw [covariance_fun_sum_fun_sum (fun i ↦ (hB.memLp_two_eval i s).const_mul _)
    (fun j ↦ (hB.memLp_two_eval j t).const_mul _)]
  have hentry (i j : ι) : cov[fun ω ↦ A k₁ i * B i s ω, fun ω ↦ A k₂ j * B j t ω; P] =
      A k₁ i * A k₂ j * if i = j then (min s t : ℝ) else 0 := by
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_fun_eval]; ring
  have horth : ∑ i : ι, A k₁ i * A k₂ i = if k₁ = k₂ then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun (congr_fun hA k₁) k₂
  simp only [hentry, mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte, ← sum_mul, horth]
  split_ifs <;> simp

/-- Applying `O ∈ Matrix.orthogonalGroup ι ℝ` preserves `IsPreBrownianVector`. -/
theorem orthogonal [Fintype ι] [DecidableEq ι] (hB : IsPreBrownianVector B P)
    {O : Matrix ι ι ℝ} (hO : O ∈ Matrix.orthogonalGroup ι ℝ) :
    IsPreBrownianVector (fun k t ω ↦ (O *ᵥ (B · t ω)) k) P :=
  hB.mulVec_of_mul_transpose_eq_one ((Matrix.mem_orthogonalGroup_iff ι ℝ).1 hO)

/-- Weak Markov independence: `(i, t) ↦ B i (t₀ + t) - B i t₀` is independent of
`(i, u) ↦ B i u` (`u ≤ t₀`). -/
theorem indepFun_shift (hB : IsPreBrownianVector B P) (t₀ : ℝ≥0) :
    IndepFun (fun ω i t ↦ B i (t₀ + t) ω - B i t₀ ω)
      (fun ω i (u : Set.Iic t₀) ↦ B i u ω) P := by
  classical
  have := hB.isProbabilityMeasure
  let X : ι × ℝ≥0 → Ω → ℝ := fun p ω ↦ B p.1 (t₀ + p.2) ω - B p.1 t₀ ω
  let Y : ι × Set.Iic t₀ → Ω → ℝ := fun q ω ↦ B q.1 q.2 ω
  have hXY : IsGaussianProcess (Sum.elim X Y) P :=
    hB.isGaussianProcess.of_isGaussianProcess fun
      | .inl (i, t) => ⟨{(i, t₀ + t), (i, t₀)},
          { toFun z := z ⟨(i, t₀ + t), by simp⟩ - z ⟨(i, t₀), by simp⟩
            map_add' _ _ := by simp; abel
            map_smul' _ _ := by simp; ring
            cont := by fun_prop }, fun _ ↦ by simp [X, restrict_def]⟩
      | .inr (j, u) => ⟨{(j, u.1)},
          { toFun z := z ⟨(j, u.1), by simp⟩, map_add' _ _ := rfl, map_smul' _ _ := rfl
            cont := by fun_prop }, fun _ ↦ by simp [Y, restrict_def]⟩
  refine (hXY.indepFun_of_covariance_eq_zero
    (fun p ↦ (hB.aemeasurable p.1 (t₀ + p.2)).sub (hB.aemeasurable p.1 t₀))
    (fun q ↦ hB.aemeasurable q.1 q.2) fun ⟨i, t⟩ ⟨j, u, hu⟩ ↦ ?_).comp
    (.of_eval fun i ↦ .of_eval fun t ↦ measurable_pi_apply (i, t))
    (.of_eval fun i ↦ .of_eval fun u ↦ measurable_pi_apply (i, u))
  change cov[B i (t₀ + t) - B i t₀, B j u; P] = 0
  rw [covariance_sub_left (hB.memLp_two_eval i (t₀ + t)) (hB.memLp_two_eval i t₀)
    (hB.memLp_two_eval j u), hB.covariance_eval, hB.covariance_eval]
  split_ifs with hij
  · have hu1 : (u : ℝ) ≤ ((t₀ + t : ℝ≥0) : ℝ) := by
      push_cast; linarith [NNReal.coe_le_coe.mpr hu, t.coe_nonneg]
    rw [min_eq_right hu1, min_eq_right (NNReal.coe_le_coe.mpr hu), sub_self]
  · simp

/-- For `s ≤ t`, the vector increment `B · t - B · s` is independent of `(B · u)_{u ≤ s}`. -/
theorem indepFun_sub_past (hB : IsPreBrownianVector B P) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω i ↦ B i t ω - B i s ω) (fun ω i (u : Set.Iic s) ↦ B i u ω) P := by
  simpa [Function.comp_def, add_tsub_cancel_of_le hst] using (hB.indepFun_shift s).comp
    (φ := fun (x : ι → ℝ≥0 → ℝ) i ↦ x i (t - s))
    (.of_eval fun i ↦ (measurable_pi_apply (t - s)).comp (measurable_pi_apply i)) measurable_id

/-- For `s ≤ t` and finite `ι`, `i ↦ B i t - B i s` has law
`Measure.pi (fun _ ↦ gaussianReal 0 (t - s))`. -/
theorem hasLaw_sub_pi [Fintype ι] (hB : IsPreBrownianVector B P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω i ↦ B i t ω - B i s ω) (Measure.pi fun _ : ι ↦ gaussianReal 0 (t - s)) P :=
  (hB.iIndepFun.comp (fun _ x ↦ x t - x s)
    fun _ ↦ (measurable_pi_apply t).sub (measurable_pi_apply s)).hasLaw_pi
    fun i ↦ (hB.isPreBrownianReal i).hasLaw_sub_of_le hst

/-- For `s ≤ t` and finite `ι`, `WithLp.toLp 2 (B · t - B · s)` has law
`multivariateGaussian 0 ((t - s) • 1)`. -/
theorem hasLaw_toLp_sub [Fintype ι] [DecidableEq ι] (hB : IsPreBrownianVector B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ WithLp.toLp 2 fun i ↦ B i t ω - B i s ω)
      (multivariateGaussian 0 (((t - s : ℝ≥0) : ℝ) • (1 : Matrix ι ι ℝ))) P := by
  refine (HasLaw.mk (by fun_prop) ?_).fun_comp (hB.hasLaw_sub_pi hst)
  have hscale : (fun _ : ι ↦ gaussianReal 0 (t - s)) =
      fun _ : ι ↦ (gaussianReal 0 1).map (fun x : ℝ ↦ √((t - s : ℝ≥0) : ℝ) * x) := by
    ext _; rw [gaussianReal_map_const_mul]; simp [Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hcomm : (WithLp.toLp 2 ∘ fun (x : ι → ℝ) (i : ι) ↦ √((t - s : ℝ≥0) : ℝ) * x i) =
      (fun z : EuclideanSpace ℝ ι ↦ (0 : EuclideanSpace ℝ ι) + √((t - s : ℝ≥0) : ℝ) • z) ∘
        WithLp.toLp 2 := by ext x i; simp
  have hstd : stdGaussian (EuclideanSpace ℝ ι) = multivariateGaussian 0 (1 : Matrix ι ι ℝ) := by
    simp [multivariateGaussian]
  rw [hscale, ← Measure.pi_map_pi fun _ ↦ by fun_prop, Measure.map_map (by fun_prop) (by fun_prop),
    hcomm, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian, hstd,
    map_add_smul_multivariateGaussian 0 Matrix.PosSemidef.one 0]
  simp [Real.sq_sqrt (NNReal.coe_nonneg _)]

end IsPreBrownianVector

namespace IsBrownianVector

/-- Applying a row-orthonormal matrix `A` (`A * Aᵀ = 1`) preserves `IsBrownianVector`. -/
theorem mulVec_of_mul_transpose_eq_one [Fintype ι] [DecidableEq κ]
    (hB : IsBrownianVector B P) {A : Matrix κ ι ℝ} (hA : A * Aᵀ = 1) :
    IsBrownianVector (fun k t ω ↦ ∑ i, A k i * B i t ω) P :=
  ⟨hB.toIsPreBrownianVector.mulVec_of_mul_transpose_eq_one hA,
    fun _ ↦ (ae_all_iff.mpr hB.ae_continuous).mono fun _ _ ↦ by fun_prop⟩

/-- Applying `O ∈ Matrix.orthogonalGroup ι ℝ` preserves `IsBrownianVector`. -/
theorem orthogonal [Fintype ι] [DecidableEq ι] (hB : IsBrownianVector B P)
    {O : Matrix ι ι ℝ} (hO : O ∈ Matrix.orthogonalGroup ι ℝ) :
    IsBrownianVector (fun k t ω ↦ (O *ᵥ (B · t ω)) k) P :=
  hB.mulVec_of_mul_transpose_eq_one ((Matrix.mem_orthogonalGroup_iff ι ℝ).1 hO)

end IsBrownianVector

section Constructions

/-- Product construction of `IsPreBrownianVector` from scalar pre-Brownian motions on factors. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.isPreBrownianVector_pi
    [Fintype ι] {Ω₀ : ι → Type*} [∀ i, MeasurableSpace (Ω₀ i)]
    {P₀ : ∀ i, Measure (Ω₀ i)} {B₀ : ∀ i, ℝ≥0 → Ω₀ i → ℝ}
    (hB₀ : ∀ i, IsPreBrownianReal (B₀ i) (P₀ i)) :
    IsPreBrownianVector (fun i t (ω : ∀ j, Ω₀ j) ↦ B₀ i t (ω i)) (Measure.pi P₀) where
  isPreBrownianReal i :=
    have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
    ⟨fun I ↦ ((hB₀ i).hasLaw I).comp (measurePreserving_eval P₀ i).hasLaw⟩
  iIndepFun := by
    classical
    have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
    refine ProbabilityTheory.iIndepFun.iIndepFun_process₀
      (fun i t ↦ ((hB₀ i).aemeasurable t).comp_quasiMeasurePreserving
        (measurePreserving_eval P₀ i).quasiMeasurePreserving) fun I J ↦ ?_
    let K : Finset ℝ≥0 := I.attach.biUnion J
    exact ((iIndepFun_pi fun j ↦ .of_eval fun t : K ↦ (hB₀ j).aemeasurable t).precomp
      (Subtype.val_injective (p := (· ∈ I)))).comp
      (fun i g (t : J i) ↦ g ⟨t.1, mem_biUnion.mpr ⟨i, mem_attach _ _, t.2⟩⟩)
      fun _ ↦ .of_eval fun _ ↦ measurable_pi_apply _

/-- Product construction of `IsBrownianVector` from scalar Brownian motions on factors. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.isBrownianVector_pi
    [Fintype ι] {Ω₀ : ι → Type*} [∀ i, MeasurableSpace (Ω₀ i)]
    {P₀ : ∀ i, Measure (Ω₀ i)} {B₀ : ∀ i, ℝ≥0 → Ω₀ i → ℝ}
    (hB₀ : ∀ i, IsBrownianReal (B₀ i) (P₀ i)) :
    IsBrownianVector (fun i t (ω : ∀ j, Ω₀ j) ↦ B₀ i t (ω i)) (Measure.pi P₀) :=
  ⟨IsPreBrownianReal.isPreBrownianVector_pi fun i ↦ (hB₀ i).toIsPreBrownianReal, fun i ↦
    have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
    (measurePreserving_eval P₀ i).quasiMeasurePreserving.ae (hB₀ i).cont⟩

/-- Canonical coordinate vector pre-Brownian motion on `ι → ℝ≥0 → ℝ` under `Measure.pi`. -/
theorem isPreBrownianVector_eval_pi_gaussianLimit [Fintype ι] :
    IsPreBrownianVector (fun i t (ω : ι → ℝ≥0 → ℝ) ↦ ω i t)
      (Measure.pi fun _ : ι ↦ gaussianLimit) :=
  IsPreBrownianReal.isPreBrownianVector_pi fun _ ↦ isPreBrownianReal_eval_gaussianLimit

end Constructions

end TauCeti.Probability
