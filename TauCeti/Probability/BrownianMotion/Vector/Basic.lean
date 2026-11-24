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
public import Mathlib.Probability.ProductMeasure
public import TauCeti.Probability.BrownianMotion.ProjectiveLimit

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.IsGaussianProcess
import TauCeti.Probability.Moments.Covariance

/-!
# Coordinate vector Brownian motion

An indexed family `B : ι → ℝ≥0 → Ω → ℝ` is a **coordinate vector pre-Brownian motion**
(`IsPreBrownianVector B P`) if each `B i` satisfies `IsPreBrownianReal` and the coordinate paths
are mutually independent (`iIndepFun`); adding a.s. path continuity defines `IsBrownianVector`.
Joint Gaussianity (`iIndepFun.isGaussianProcess_prod`) yields equivalence with centered Gaussian
covariance `δᵢⱼ min s t`, invariance under row-orthonormal/orthogonal matrices, multivariate
Gaussian increment laws, Markov independence from the past, and `Measure.infinitePi`/`pi` models.

## References

* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, §1.1, §2.2.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1, §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Matrix

namespace TauCeti.Probability

variable {ι κ Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B C : ι → ℝ≥0 → Ω → ℝ}

/-- Coordinate vector pre-Brownian motion: mutually independent `IsPreBrownianReal` coordinates. -/
structure IsPreBrownianVector (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  /-- Each coordinate process is a scalar pre-Brownian motion. -/
  isPreBrownianReal : ∀ i, IsPreBrownianReal (B i) P
  /-- The coordinate paths are mutually independent in the product `σ`-algebra on `ℝ≥0 → ℝ`. -/
  iIndepFun : iIndepFun (fun i ω t ↦ B i t ω) P

/-- Coordinate vector Brownian motion: `IsPreBrownianVector` with a.s. continuous coordinates. -/
structure IsBrownianVector (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianVector B P where
  /-- Each coordinate has almost-surely continuous paths. -/
  ae_continuous : ∀ i, ∀ᵐ ω ∂P, Continuous (B i · ω)

namespace IsPreBrownianVector

/-- A space carrying a coordinate vector pre-Brownian motion is a probability space. -/
theorem isProbabilityMeasure (hB : IsPreBrownianVector B P) : IsProbabilityMeasure P :=
  hB.iIndepFun.iIndep.isProbabilityMeasure

/-- Fixed-time a.e. modifications preserve `IsPreBrownianVector`. -/
theorem congr (hB : IsPreBrownianVector B P) (h : ∀ i t, B i t =ᵐ[P] C i t) :
    IsPreBrownianVector C P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).congr (h i), hB.iIndepFun.process_congr h⟩

/-- Over `[IsEmpty ι]`, any process family on a probability space is `IsPreBrownianVector`. -/
theorem of_isEmpty [IsEmpty ι] [IsProbabilityMeasure P] (B : ι → ℝ≥0 → Ω → ℝ) :
    IsPreBrownianVector B P := ⟨fun i ↦ isEmptyElim i, .of_subsingleton⟩

/-- Restricting coordinates along an injective map preserves `IsPreBrownianVector`. -/
theorem precomp {g : κ → ι} (hg : Function.Injective g) (hB : IsPreBrownianVector B P) :
    IsPreBrownianVector (fun k ↦ B (g k)) P :=
  ⟨fun k ↦ hB.isPreBrownianReal (g k), hB.iIndepFun.precomp hg⟩

/-- The joint family `(i, t) ↦ B i t` is a Gaussian process on `ι × ℝ≥0`. -/
theorem isGaussianProcess (hB : IsPreBrownianVector B P) :
    IsGaussianProcess (fun (p : ι × ℝ≥0) ω ↦ B p.1 p.2 ω) P :=
  hB.iIndepFun.isGaussianProcess_prod fun i ↦ (hB.isPreBrownianReal i).isGaussianProcess

/-- Every coordinate time marginal of a vector pre-Brownian motion is a.e. measurable. -/
theorem aemeasurable (hB : IsPreBrownianVector B P) (i : ι) (t : ℝ≥0) : AEMeasurable (B i t) P :=
  (hB.isPreBrownianReal i).aemeasurable t

/-- Every coordinate time marginal of a vector pre-Brownian motion is centered. -/
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
  have := hB.isProbabilityMeasure; split_ifs with hij
  · exact hij ▸ (hB.isPreBrownianReal i).covariance_eval s t
  · exact ((hB.iIndepFun.indepFun hij).comp (measurable_pi_apply s)
      (measurable_pi_apply t)).covariance_eq_zero (hB.memLp_two_eval i s) (hB.memLp_two_eval j t)

/-- Uncurried form of `IsPreBrownianVector.covariance_eval` for lambda expressions. -/
theorem covariance_fun_eval [DecidableEq ι] (hB : IsPreBrownianVector B P) (i j : ι) (s t : ℝ≥0) :
    cov[fun ω ↦ B i s ω, fun ω ↦ B j t ω; P] = if i = j then (min s t : ℝ) else 0 :=
  hB.covariance_eval i j s t

/-- Distinct coordinates of a vector pre-Brownian motion cannot agree a.e. at any `t > 0`. -/
theorem not_ae_eq_of_ne_of_pos (hB : IsPreBrownianVector B P) {i j : ι} (hij : i ≠ j)
    {t : ℝ≥0} (ht : 0 < t) : ¬ (B i t =ᵐ[P] B j t) := by
  classical
  intro heq; have := hB.isProbabilityMeasure
  have hcov0 : cov[B i t, B j t; P] = 0 := by simp [hB.covariance_eval, hij]
  rw [TauCeti.covariance_congr_ae .rfl heq.symm, (hB.isPreBrownianReal i).covariance_eval,
    min_self] at hcov0; linarith [NNReal.coe_pos.mpr ht]

/-- Negating every coordinate preserves `IsPreBrownianVector`. -/
theorem neg (hB : IsPreBrownianVector B P) : IsPreBrownianVector (-B) P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).neg,
    hB.iIndepFun.comp (fun _ x t ↦ -x t) fun _ ↦ .of_eval fun t ↦ (measurable_pi_apply t).neg⟩

/-- Brownian diffusive scaling `(√c)⁻¹ * B i (c * t)` (`c ≠ 0`) preserves `IsPreBrownianVector`. -/
theorem smul (hB : IsPreBrownianVector B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownianVector (fun i t ω ↦ (√(c : ℝ))⁻¹ * B i (c * t) ω) P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).smul hc, hB.iIndepFun.comp
    (fun _ x t ↦ (√(c : ℝ))⁻¹ * x (c * t)) fun _ ↦ .of_eval fun t ↦
      (measurable_pi_apply (c * t)).const_mul _⟩

/-- Deterministic time shift `B i (t₀ + t) - B i t₀` preserves `IsPreBrownianVector`. -/
theorem shift (hB : IsPreBrownianVector B P) (t₀ : ℝ≥0) :
    IsPreBrownianVector (fun i t ω ↦ B i (t₀ + t) ω - B i t₀ ω) P :=
  ⟨fun i ↦ (hB.isPreBrownianReal i).shift t₀, hB.iIndepFun.comp (fun _ x t ↦ x (t₀ + t) - x t₀)
    fun _ ↦ .of_eval fun t ↦ (measurable_pi_apply (t₀ + t)).sub (measurable_pi_apply t₀)⟩

end IsPreBrownianVector

/-- For `[Unique ι]`, `IsPreBrownianVector B P` iff `IsPreBrownianReal (B default) P`. -/
@[simp]
theorem isPreBrownianVector_unique_iff [Unique ι] :
    IsPreBrownianVector B P ↔ IsPreBrownianReal (B default) P :=
  ⟨fun h ↦ h.isPreBrownianReal default, fun h ↦ have := h.isGaussianProcess.isProbabilityMeasure
    ⟨fun i ↦ Unique.eq_default i ▸ h, .of_subsingleton⟩⟩

/-- Bijective reindexing of coordinates preserves and reflects `IsPreBrownianVector`. -/
theorem isPreBrownianVector_precomp_of_bijective {g : κ → ι} (hg : Function.Bijective g) :
    IsPreBrownianVector (fun k ↦ B (g k)) P ↔ IsPreBrownianVector B P :=
  let e := Equiv.ofBijective g hg
  ⟨fun h ↦ by simpa [e, Equiv.ofBijective_apply_symm_apply] using h.precomp e.symm.injective,
    fun h ↦ h.precomp hg.injective⟩

/-- Centered Gaussian families with covariance `δᵢⱼ min s t` satisfy `IsPreBrownianVector`. -/
theorem _root_.ProbabilityTheory.IsGaussianProcess.isPreBrownianVector_of_covariance
    [DecidableEq ι] (hG : IsGaussianProcess (fun (p : ι × ℝ≥0) ω ↦ B p.1 p.2 ω) P)
    (hmean : ∀ i t, P[B i t] = 0)
    (hcov : ∀ i j s t, cov[B i s, B j t; P] = if i = j then (min s t : ℝ) else 0) :
    IsPreBrownianVector B P where
  isPreBrownianReal i :=
    (hG.comp_right (Prod.mk i)).isPreBrownianReal_of_covariance (hmean i) fun s t hst ↦ by
      simpa [Function.comp_def, min_eq_left (NNReal.coe_le_coe.mpr hst)] using hcov i i s t
  iIndepFun := (hG.comp_right fun p : (_ : ι) × ℝ≥0 ↦ (p.1, p.2)).iIndepFun_of_covariance_eq_zero
    (fun i t ↦ hG.aemeasurable (i, t)) fun i j hij s t ↦ by simpa [hij] using hcov i j s t

/-- Centered Gaussian characterization of `IsPreBrownianVector` via covariance `δᵢⱼ min s t`. -/
theorem isPreBrownianVector_iff_isGaussianProcess [DecidableEq ι] :
    IsPreBrownianVector B P ↔ IsGaussianProcess (fun (p : ι × ℝ≥0) ω ↦ B p.1 p.2 ω) P ∧
      (∀ i t, P[B i t] = 0) ∧
      ∀ i j s t, cov[B i s, B j t; P] = if i = j then (min s t : ℝ) else 0 :=
  ⟨fun h ↦ ⟨h.isGaussianProcess, h.integral_eval, h.covariance_eval⟩,
    fun ⟨hG, hm, hc⟩ ↦ hG.isPreBrownianVector_of_covariance hm hc⟩

namespace IsPreBrownianVector

/-- Applying a row-orthonormal matrix `A` (`A * Aᵀ = 1`) preserves `IsPreBrownianVector`. -/
theorem mulVec_of_mul_transpose_eq_one [Fintype ι] [DecidableEq κ]
    (hB : IsPreBrownianVector B P) {A : Matrix κ ι ℝ} (hA : A * Aᵀ = 1) :
    IsPreBrownianVector (fun k t ω ↦ (A *ᵥ (B · t ω)) k) P := by
  classical
  have := hB.isProbabilityMeasure
  refine ((hB.isGaussianProcess.comp_right fun p : ι × (κ × ℝ≥0) ↦ (p.1, p.2.2)).sum_comp_left
    univ fun i (q : κ × ℝ≥0) ↦ .lsmul ℝ ℝ (A q.1 i)).isPreBrownianVector_of_covariance
    (fun k t ↦ by
      simp only [Matrix.mulVec, dotProduct]
      rw [integral_finsetSum _ fun i _ ↦ ((hB.isPreBrownianReal i).integrable_eval t).const_mul _]
      simp [integral_const_mul, hB.integral_eval]) fun k₁ k₂ s t ↦ ?_
  have horth : ∑ i : ι, A k₂ i * A k₁ i = if k₁ = k₂ then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm] using congr_fun (congr_fun hA k₂) k₁
  simp only [Matrix.mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (fun i ↦ (hB.memLp_two_eval i s).const_mul _)
    (fun j ↦ (hB.memLp_two_eval j t).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_fun_eval,
    mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte, ← mul_assoc, ← sum_mul, horth]
  split_ifs <;> simp

/-- Applying `O ∈ Matrix.orthogonalGroup ι ℝ` preserves `IsPreBrownianVector`. -/
theorem mulVec_of_mem_orthogonalGroup [Fintype ι] [DecidableEq ι] (hB : IsPreBrownianVector B P)
    {O : Matrix ι ι ℝ} (hO : O ∈ Matrix.orthogonalGroup ι ℝ) :
    IsPreBrownianVector (fun k t ω ↦ (O *ᵥ (B · t ω)) k) P :=
  hB.mulVec_of_mul_transpose_eq_one ((Matrix.mem_orthogonalGroup_iff ι ℝ).1 hO)

/-- `(i, t) ↦ B i (t₀ + t) - B i t₀` is independent of `(i, u) ↦ B i u` (`u ≤ t₀`). -/
theorem indepFun_shift (hB : IsPreBrownianVector B P) (t₀ : ℝ≥0) :
    IndepFun (fun ω i t ↦ B i (t₀ + t) ω - B i t₀ ω) (fun ω i (u : Set.Iic t₀) ↦ B i u ω) P := by
  classical
  have := hB.isProbabilityMeasure
  refine ((hB.isGaussianProcess.of_isGaussianProcess (Y := Sum.elim
      (fun (p : ι × ℝ≥0) ω ↦ B p.1 (t₀ + p.2) ω - B p.1 t₀ ω)
      (fun (q : ι × Set.Iic t₀) ω ↦ B q.1 q.2 ω)) fun
    | .inl (i, t) => ⟨{(i, t₀ + t), (i, t₀)}, ContinuousLinearMap.proj ⟨(i, t₀ + t), by simp⟩ -
        ContinuousLinearMap.proj ⟨(i, t₀), by simp⟩, fun _ ↦ by simp [restrict_def]⟩
    | .inr (j, u) => ⟨{(j, u.val)}, ContinuousLinearMap.proj ⟨(j, u.val), by simp⟩,
        fun _ ↦ by simp [restrict_def]⟩).indepFun_of_covariance_eq_zero
    (fun p ↦ (hB.aemeasurable p.1 (t₀ + p.2)).sub (hB.aemeasurable p.1 t₀))
    (fun q ↦ hB.aemeasurable q.1 q.2) fun ⟨i, t⟩ ⟨j, u, hu⟩ ↦ ?_).comp
    (.of_eval fun i ↦ .of_eval fun t ↦ measurable_pi_apply (i, t))
    (.of_eval fun i ↦ .of_eval fun u ↦ measurable_pi_apply (i, u))
  rw [covariance_fun_sub_left (hB.memLp_two_eval i _) (hB.memLp_two_eval i _)
    (hB.memLp_two_eval j _), hB.covariance_eval, hB.covariance_eval]
  split_ifs with hij
  · dsimp only
    rw [min_eq_right (NNReal.coe_le_coe.mpr (le_trans (c := t₀ + t) hu le_self_add)),
      min_eq_right (NNReal.coe_le_coe.mpr hu), sub_self]
  · simp

/-- For `s ≤ t`, the vector increment `B · t - B · s` is independent of `(B · u)_{u ≤ s}`. -/
theorem indepFun_sub_past (hB : IsPreBrownianVector B P) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω i ↦ B i t ω - B i s ω) (fun ω i (u : Set.Iic s) ↦ B i u ω) P := by
  simpa [Function.comp_def, add_tsub_cancel_of_le hst] using (hB.indepFun_shift s).comp
    (φ := fun (x : ι → ℝ≥0 → ℝ) i ↦ x i (t - s))
    (.of_eval fun i ↦ (measurable_pi_apply (t - s)).comp (measurable_pi_apply i)) measurable_id

/-- For `s ≤ t`, `B · t - B · s` has law `Measure.pi (fun _ ↦ gaussianReal 0 (t - s))`. -/
theorem hasLaw_sub_pi [Fintype ι] (hB : IsPreBrownianVector B P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω i ↦ B i t ω - B i s ω) (Measure.pi fun _ : ι ↦ gaussianReal 0 (t - s)) P :=
  (hB.iIndepFun.comp (fun _ x ↦ x t - x s)
    fun _ ↦ (measurable_pi_apply t).sub (measurable_pi_apply s)).hasLaw_pi
    fun i ↦ (hB.isPreBrownianReal i).hasLaw_sub_of_le hst

/-- For `s ≤ t`, `WithLp.toLp 2 (B · t - B · s)` has law `multivariateGaussian 0 ((t - s) • 1)`. -/
theorem hasLaw_toLp_sub [Fintype ι] [DecidableEq ι] (hB : IsPreBrownianVector B P)
    {s t : ℝ≥0} (hst : s ≤ t) : HasLaw (fun ω ↦ WithLp.toLp 2 fun i ↦ B i t ω - B i s ω)
      (multivariateGaussian 0 (((t - s : ℝ≥0) : ℝ) • (1 : Matrix ι ι ℝ))) P :=
  (HasLaw.mk (by fun_prop) (by simpa using (multivariateGaussian_smul_one_eq_map_pi 0 _).symm)
    ).fun_comp (hB.hasLaw_sub_pi hst)

end IsPreBrownianVector

namespace IsBrownianVector

/-- Each coordinate of a vector Brownian motion is a scalar Brownian motion. -/
theorem isBrownianReal (hB : IsBrownianVector B P) (i : ι) : IsBrownianReal (B i) P :=
  ⟨hB.isPreBrownianReal i, hB.ae_continuous i⟩

/-- Construct `IsBrownianVector` from coordinatewise `IsBrownianReal` and path independence. -/
theorem of_isBrownianReal (h₁ : ∀ i, IsBrownianReal (B i) P)
    (h₂ : iIndepFun (fun i ω t ↦ B i t ω) P) : IsBrownianVector B P :=
  ⟨⟨fun i ↦ (h₁ i).toIsPreBrownianReal, h₂⟩, fun i ↦ (h₁ i).cont⟩

/-- Indistinguishable coordinatewise modifications preserve `IsBrownianVector`. -/
theorem congr_indist (hB : IsBrownianVector B P) (h : ∀ i, B i ≡ᵐ[P] C i) :
    IsBrownianVector C P :=
  ⟨hB.toIsPreBrownianVector.congr fun i t ↦ (h i).mono fun _ hω ↦ hω t,
    fun i ↦ (hB.ae_continuous i).mp ((h i).mono fun _ hω hc ↦ by simpa [funext hω] using hc)⟩

/-- Over `[IsEmpty ι]`, any process family on a probability space satisfies `IsBrownianVector`. -/
theorem of_isEmpty [IsEmpty ι] [IsProbabilityMeasure P] (B : ι → ℝ≥0 → Ω → ℝ) :
    IsBrownianVector B P := ⟨.of_isEmpty B, fun i ↦ isEmptyElim i⟩

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

/-- Applying a row-orthonormal matrix `A` (`A * Aᵀ = 1`) preserves `IsBrownianVector`. -/
theorem mulVec_of_mul_transpose_eq_one [Fintype ι] [DecidableEq κ] (hB : IsBrownianVector B P)
    {A : Matrix κ ι ℝ} (hA : A * Aᵀ = 1) : IsBrownianVector (fun k t ω ↦ (A *ᵥ (B · t ω)) k) P :=
  ⟨hB.toIsPreBrownianVector.mulVec_of_mul_transpose_eq_one hA, fun _ ↦
    (ae_all_iff.mpr hB.ae_continuous).mono fun _ _ ↦ by
      simp only [Matrix.mulVec, dotProduct]; fun_prop⟩

/-- Applying `O ∈ Matrix.orthogonalGroup ι ℝ` preserves `IsBrownianVector`. -/
theorem mulVec_of_mem_orthogonalGroup [Fintype ι] [DecidableEq ι] (hB : IsBrownianVector B P)
    {O : Matrix ι ι ℝ} (hO : O ∈ Matrix.orthogonalGroup ι ℝ) :
    IsBrownianVector (fun k t ω ↦ (O *ᵥ (B · t ω)) k) P :=
  hB.mulVec_of_mul_transpose_eq_one ((Matrix.mem_orthogonalGroup_iff ι ℝ).1 hO)

end IsBrownianVector

/-- `IsBrownianVector B P` iff every coordinate is `IsBrownianReal` and paths are independent. -/
theorem isBrownianVector_iff : IsBrownianVector B P ↔
    (∀ i, IsBrownianReal (B i) P) ∧ iIndepFun (fun i ω t ↦ B i t ω) P :=
  ⟨fun h ↦ ⟨h.isBrownianReal, h.iIndepFun⟩, fun ⟨h₁, h₂⟩ ↦ .of_isBrownianReal h₁ h₂⟩

/-- For `[Unique ι]`, `IsBrownianVector B P` is equivalent to `IsBrownianReal (B default) P`. -/
@[simp]
theorem isBrownianVector_unique_iff [Unique ι] :
    IsBrownianVector B P ↔ IsBrownianReal (B default) P :=
  ⟨fun h ↦ h.isBrownianReal default, fun h ↦ have := h.isGaussianProcess.isProbabilityMeasure
    .of_isBrownianReal (fun i ↦ Unique.eq_default i ▸ h) .of_subsingleton⟩

/-- Bijective reindexing of coordinates preserves and reflects `IsBrownianVector`. -/
theorem isBrownianVector_precomp_of_bijective {g : κ → ι} (hg : Function.Bijective g) :
    IsBrownianVector (fun k ↦ B (g k)) P ↔ IsBrownianVector B P :=
  let e := Equiv.ofBijective g hg
  ⟨fun h ↦ by simpa [e, Equiv.ofBijective_apply_symm_apply] using h.precomp e.symm.injective,
    fun h ↦ h.precomp hg.injective⟩

section Constructions

variable {Ω₀ : ι → Type*} [∀ i, MeasurableSpace (Ω₀ i)] {P₀ : ∀ i, Measure (Ω₀ i)}
  {B₀ : ∀ i, ℝ≥0 → Ω₀ i → ℝ}

/-- Infinite-product construction of `IsPreBrownianVector` from scalar pre-Brownian factors. -/
theorem isPreBrownianVector_infinitePi (hB₀ : ∀ i, IsPreBrownianReal (B₀ i) (P₀ i)) :
    IsPreBrownianVector (fun i t (ω : ∀ j, Ω₀ j) ↦ B₀ i t (ω i)) (Measure.infinitePi P₀) where
  isPreBrownianReal i := have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
    ⟨fun I ↦ ((hB₀ i).hasLaw I).comp (measurePreserving_eval_infinitePi P₀ i).hasLaw⟩
  iIndepFun := by
    have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
    let qmp i := (measurePreserving_eval_infinitePi P₀ i).quasiMeasurePreserving
    refine iIndepFun.iIndepFun_process₀
      (fun i t ↦ ((hB₀ i).aemeasurable t).comp_quasiMeasurePreserving (qmp i)) fun I J ↦ ?_
    have hm (i : I) : AEMeasurable (fun (x : Ω₀ i) (t : J i) ↦ B₀ i t x) (P₀ i) :=
      .of_eval fun t ↦ (hB₀ i).aemeasurable t
    exact (((iIndepFun_infinitePi (P := P₀) (X := fun _ ↦ id) fun _ ↦ measurable_id).precomp
      Subtype.val_injective).comp (fun i ↦ (hm i).mk _) fun i ↦ (hm i).measurable_mk).congr
      fun i ↦ (qmp i).ae (hm i).ae_eq_mk.symm

/-- Infinite-product construction of `IsBrownianVector` from scalar Brownian factors. -/
theorem isBrownianVector_infinitePi (hB₀ : ∀ i, IsBrownianReal (B₀ i) (P₀ i)) :
    IsBrownianVector (fun i t (ω : ∀ j, Ω₀ j) ↦ B₀ i t (ω i)) (Measure.infinitePi P₀) :=
  ⟨isPreBrownianVector_infinitePi fun i ↦ (hB₀ i).toIsPreBrownianReal, fun i ↦
    have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
    (measurePreserving_eval_infinitePi P₀ i).quasiMeasurePreserving.ae (hB₀ i).cont⟩

/-- Canonical coordinate vector pre-Brownian motion on `ι → ℝ≥0 → ℝ` under `Measure.infinitePi`. -/
theorem isPreBrownianVector_eval_infinitePi_brownianProjectiveLimit :
    IsPreBrownianVector (fun i t (ω : ι → ℝ≥0 → ℝ) ↦ ω i t)
      (Measure.infinitePi fun _ : ι ↦ brownianProjectiveLimit) :=
  isPreBrownianVector_infinitePi fun _ ↦ isPreBrownianReal_eval_brownianProjectiveLimit

/-- Product construction of `IsPreBrownianVector` from scalar pre-Brownian factors. -/
theorem isPreBrownianVector_pi [Fintype ι] (hB₀ : ∀ i, IsPreBrownianReal (B₀ i) (P₀ i)) :
    IsPreBrownianVector (fun i t (ω : ∀ j, Ω₀ j) ↦ B₀ i t (ω i)) (Measure.pi P₀) :=
  have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
  Measure.infinitePi_eq_pi (μ := P₀) ▸ isPreBrownianVector_infinitePi hB₀

/-- Product construction of `IsBrownianVector` from scalar Brownian factors. -/
theorem isBrownianVector_pi [Fintype ι] (hB₀ : ∀ i, IsBrownianReal (B₀ i) (P₀ i)) :
    IsBrownianVector (fun i t (ω : ∀ j, Ω₀ j) ↦ B₀ i t (ω i)) (Measure.pi P₀) :=
  have := fun j ↦ (hB₀ j).isGaussianProcess.isProbabilityMeasure
  Measure.infinitePi_eq_pi (μ := P₀) ▸ isBrownianVector_infinitePi hB₀

/-- Canonical coordinate vector pre-Brownian motion on `ι → ℝ≥0 → ℝ` under `Measure.pi`. -/
theorem isPreBrownianVector_eval_pi_brownianProjectiveLimit [Fintype ι] :
    IsPreBrownianVector (fun i t (ω : ι → ℝ≥0 → ℝ) ↦ ω i t)
      (Measure.pi fun _ : ι ↦ brownianProjectiveLimit) :=
  Measure.infinitePi_eq_pi (μ := fun _ : ι ↦ brownianProjectiveLimit) ▸
    isPreBrownianVector_eval_infinitePi_brownianProjectiveLimit

end Constructions

end TauCeti.Probability
