/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod
public import TauCeti.Probability.BrownianMotion.ProjectiveLimit
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# The Brownian bridge

For a real process `B` and a horizon `T`, the *Brownian bridge* of `B` on `[0, T]` is
`t ↦ B t - (t / T) B T`. When `B` is a pre-Brownian motion it is a centered Gaussian process
with covariance `min s t - s t / T` on `[0, T]`, its marginal at `t ≤ T` is the centered Gaussian
law of variance `t (T - t) / T`, it vanishes at the horizon, and on `[0, T]` it is independent of
the endpoint `B T`. Consequently `B t = brownianBridge B T t + (t / T) B T` splits Brownian motion
on `[0, T]` into the endpoint and an independent bridge.

The law `TauCeti.brownianBridgeMeasure T` of the bridge path on `[0, T]` is the same for every
pre-Brownian motion whose path map `ω ↦ (B t ω)_{t ≤ T}` is almost everywhere measurable, and for
such a process the kernel `TauCeti.brownianBridgeKernel T`, which for `T ≠ 0` sends `x` to the law
of the bridge from `0` to `x`, disintegrates the law of the Brownian path on `[0, T]` with respect
to its endpoint `B T`. This is the precise form of conditioning Brownian motion on its endpoint,
an event of probability zero.

The bridge of the standard horizon `T = 1`, `t ↦ B t - t B 1`, is the Gaussian limit of the
uniform empirical process; the supremum of its absolute value and its squared integral are the
limit laws of the Kolmogorov–Smirnov and Cramér–von Mises statistics.

The degenerate horizon `T = 0` is allowed: then `t / T = 0`, the bridge is `B` itself, and the
statements restricted to `t ≤ T` concern the single time `0`.

## Main definitions

* `TauCeti.brownianBridge B T`: the process `t ↦ B t - (t / T) B T`.
* `TauCeti.brownianBridgeMeasure T`: the law of the Brownian bridge path on `[0, T]`.
* `TauCeti.brownianBridgeKernel T`: the Markov kernel sending `x` to the law of
  `t ↦ X t + (t / T) x` for a Brownian bridge `X` on `[0, T]`; for `T ≠ 0` this is the Brownian
  bridge from `0` to `x`.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess_brownianBridge`: the bridge of a
  pre-Brownian motion is a Gaussian process.
* `ProbabilityTheory.IsPreBrownianReal.integral_brownianBridge`: it is centered.
* `ProbabilityTheory.IsPreBrownianReal.covariance_brownianBridge`: for `s, t ≤ T`,
  `cov[brownianBridge B T s, brownianBridge B T t] = min s t - s t / T`.
* `ProbabilityTheory.IsPreBrownianReal.hasLaw_brownianBridge`: for `t ≤ T` the bridge at time
  `t` has law `gaussianReal 0 (t (T - t) / T)`.
* `ProbabilityTheory.IsPreBrownianReal.indepFun_brownianBridge`: the bridge on `[0, T]` is
  independent of `B T`.
* `ProbabilityTheory.IsBrownianReal.ae_continuous_brownianBridge`: the bridge of a Brownian
  motion has almost surely continuous paths.
* `ProbabilityTheory.IsPreBrownianReal.hasLaw_brownianBridgeMeasure`: the bridge path of a
  pre-Brownian motion with almost everywhere measurable path on `[0, T]` has law
  `brownianBridgeMeasure T`.
* `ProbabilityTheory.IsPreBrownianReal.map_prodMk_eq_compProd_brownianBridgeKernel`: the joint
  law of `B T` and the path on `[0, T]` is `gaussianReal 0 T ⊗ₘ brownianBridgeKernel T`.
* `TauCeti.ae_brownianBridgeKernel_apply_eq`: for `T ≠ 0` the bridge from `0` to `x` ends at `x`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §5.6.B.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {T t : ℝ≥0}

/-- The **Brownian bridge** of the process `B` on `[0, T]`: the process `t ↦ B t - (t / T) B T`.
It is pinned at `0` at time `T` when `T ≠ 0`, and for the horizon `T = 0` it is `B` itself. -/
noncomputable def brownianBridge (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω - (t / T : ℝ) * B T ω

theorem brownianBridge_def :
    brownianBridge B T t = fun ω ↦ B t ω - (t / T : ℝ) * B T ω := (rfl)

@[simp]
theorem brownianBridge_apply (ω : Ω) :
    brownianBridge B T t ω = B t ω - (t / T : ℝ) * B T ω := (rfl)

/-- A process splits into its bridge on `[0, T]` and the linear interpolation of its endpoint. -/
theorem brownianBridge_add_mul (ω : Ω) :
    brownianBridge B T t ω + (t / T : ℝ) * B T ω = B t ω := by
  simp

/-- The bridge vanishes at a nonzero horizon. -/
theorem brownianBridge_self (hT : T ≠ 0) (ω : Ω) : brownianBridge B T T ω = 0 := by
  simp [hT]

/-- At the degenerate horizon `T = 0` the bridge is the process itself. -/
@[simp]
theorem brownianBridge_zero_right : brownianBridge B 0 = B := by
  ext t ω
  simp

/-- Each value of the bridge is measurable when the process is measurable at `t` and at `T`. -/
@[fun_prop]
theorem measurable_brownianBridge [MeasurableSpace Ω] (ht : Measurable (B t))
    (hT : Measurable (B T)) : Measurable (brownianBridge B T t) := by
  rw [brownianBridge_def]
  fun_prop

/-- Each value of the bridge is almost everywhere measurable when the process is almost everywhere
measurable at `t` and at `T`. -/
@[fun_prop]
theorem aemeasurable_brownianBridge [MeasurableSpace Ω] {P : Measure Ω}
    (ht : AEMeasurable (B t) P) (hT : AEMeasurable (B T) P) :
    AEMeasurable (brownianBridge B T t) P := by
  rw [brownianBridge_def]
  fun_prop

/-- The path of the bridge at `ω` is continuous whenever the path of the process is. -/
theorem continuous_brownianBridge {ω : Ω} (h : Continuous (B · ω)) :
    Continuous (brownianBridge B T · ω) := by
  simp only [brownianBridge_apply]
  fun_prop

end TauCeti

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {T s t : ℝ≥0}

/-- Each value of the bridge is a linear function of finitely many values of the process. -/
private lemma exists_brownianBridge_eq_linear (B : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) :
    ∃ I : Finset ℝ≥0, ∃ L : (I → ℝ) →L[ℝ] ℝ,
      ∀ ω, brownianBridge B T t ω = L (I.restrict (B · ω)) := by
  classical
  exact ⟨{t, T},
    { toFun x := x ⟨t, by simp⟩ - (t / T : ℝ) * x ⟨T, by simp⟩
      map_add' x y := by simp; ring
      map_smul' c x := by simp; ring },
    by simp⟩

/-- The bridge of a pre-Brownian motion is a Gaussian process. -/
theorem isGaussianProcess_brownianBridge (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IsGaussianProcess (brownianBridge B T) P :=
  hB.isGaussianProcess.of_isGaussianProcess (exists_brownianBridge_eq_linear B T)

/-- The bridge of a pre-Brownian motion is centered. -/
theorem integral_brownianBridge (hB : IsPreBrownianReal B P) (T t : ℝ≥0) :
    P[brownianBridge B T t] = 0 := by
  simp only [brownianBridge_apply]
  rw [integral_sub (hB.integrable_eval t) ((hB.integrable_eval T).const_mul _),
    integral_const_mul, hB.integral_eval, hB.integral_eval]
  simp

/-- The covariance of the bridge with the underlying pre-Brownian motion. -/
theorem covariance_brownianBridge_eval (hB : IsPreBrownianReal B P) (T s t : ℝ≥0) :
    cov[brownianBridge B T s, B t; P] = min s t - (s / T : ℝ) * min T t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hL (u : ℝ≥0) : MemLp (B u) 2 P := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  rw [brownianBridge_def, covariance_fun_sub_left (hL s) ((hL T).const_mul _) (hL t),
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval]

/-- On `[0, T]` the bridge of a pre-Brownian motion is uncorrelated with the endpoint. -/
theorem covariance_brownianBridge_eval_self (hB : IsPreBrownianReal B P) (hs : s ≤ T) :
    cov[brownianBridge B T s, B T; P] = 0 := by
  rw [covariance_brownianBridge_eval hB, min_self, min_eq_left hs]
  rcases eq_or_ne T 0 with rfl | hT
  · simp [nonpos_iff_eq_zero.1 hs]
  · field_simp
    ring

/-- The covariance of the bridge of a pre-Brownian motion: for `s, t ≤ T`,
`cov[brownianBridge B T s, brownianBridge B T t] = min s t - s t / T`. -/
theorem covariance_brownianBridge (hB : IsPreBrownianReal B P) (hs : s ≤ T) (ht : t ≤ T) :
    cov[brownianBridge B T s, brownianBridge B T t; P] = min s t - (s * t / T : ℝ) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hL (u : ℝ≥0) : MemLp (B u) 2 P := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hX : MemLp (brownianBridge B T s) 2 P :=
    (hB.isGaussianProcess_brownianBridge T).hasGaussianLaw_eval s |>.memLp_two
  rw [brownianBridge_def (t := t), covariance_fun_sub_right hX (hL t) ((hL T).const_mul _),
    covariance_const_mul_right, covariance_brownianBridge_eval_self hB hs,
    covariance_brownianBridge_eval hB, min_eq_right ht]
  ring

/-- The variance of the bridge of a pre-Brownian motion at a time `t ≤ T`. -/
theorem variance_brownianBridge (hB : IsPreBrownianReal B P) (ht : t ≤ T) :
    Var[brownianBridge B T t; P] = t * (T - t) / T := by
  rw [← covariance_self ((hB.isGaussianProcess_brownianBridge T).aemeasurable t),
    covariance_brownianBridge hB ht ht, min_self]
  rcases eq_or_ne T 0 with rfl | hT
  · simp [nonpos_iff_eq_zero.1 ht]
  · field_simp

/-- The marginal law of the bridge of a pre-Brownian motion at a time `t ≤ T` is the centered
Gaussian law of variance `t (T - t) / T`. -/
theorem hasLaw_brownianBridge (hB : IsPreBrownianReal B P) (ht : t ≤ T) :
    HasLaw (brownianBridge B T t) (gaussianReal 0 (t * (T - t) / T)) P := by
  have hG := (hB.isGaussianProcess_brownianBridge T).hasGaussianLaw_eval t
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, integral_brownianBridge hB, variance_brownianBridge hB ht]
  congr 1
  ext
  have h : (0 : ℝ) ≤ t * (T - t) / T := div_nonneg (mul_nonneg t.property
      (sub_nonneg.2 ht)) T.property
  simpa [NNReal.coe_sub ht] using h

/-- The bridge of a pre-Brownian motion on `[0, T]` is independent of the endpoint `B T`. -/
theorem indepFun_brownianBridge (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IndepFun (fun ω (t : Set.Iic T) ↦ brownianBridge B T t ω) (B T) P := by
  classical
  have h := IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun t : Set.Iic T ↦ brownianBridge B T t) (Y := fun _ : Unit ↦ B T) (P := P) ?_
    (fun t ↦ (hB.isGaussianProcess_brownianBridge T).aemeasurable t)
    (fun _ ↦ hB.aemeasurable T)
    (fun t _ ↦ covariance_brownianBridge_eval_self hB t.property)
  · exact h.comp measurable_id (measurable_pi_apply ())
  refine hB.isGaussianProcess.of_isGaussianProcess ?_
  rintro (⟨t, -⟩ | -)
  · exact exists_brownianBridge_eq_linear B T t
  · exact ⟨{T},
      { toFun x := x ⟨T, by simp⟩
        map_add' x y := by simp
        map_smul' c x := by simp },
      by simp⟩

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The bridge of a Brownian motion has almost surely continuous paths. -/
theorem ae_continuous_brownianBridge (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Continuous (brownianBridge B T · ω) := by
  filter_upwards [hB.cont] with ω h using continuous_brownianBridge h

end ProbabilityTheory.IsBrownianReal

/-! ### The law of the bridge and the endpoint kernel -/

namespace TauCeti

open Probability

variable {T : ℝ≥0}

/-- The law of the Brownian bridge on `[0, T]`, a probability measure on paths `Set.Iic T → ℝ`
with the product σ-algebra: the law of the bridge of the canonical pre-Brownian motion. By
`ProbabilityTheory.IsPreBrownianReal.hasLaw_brownianBridgeMeasure` it is the law of the bridge
of every pre-Brownian motion whose path map `ω ↦ (B t ω)_{t ≤ T}` is almost everywhere
measurable. -/
noncomputable def brownianBridgeMeasure (T : ℝ≥0) : Measure (Set.Iic T → ℝ) :=
  brownianProjectiveLimit.map fun ω (t : Set.Iic T) ↦ brownianBridge (fun t ω ↦ ω t) T t ω

instance (T : ℝ≥0) : IsProbabilityMeasure (brownianBridgeMeasure T) := by
  unfold brownianBridgeMeasure
  infer_instance

/-- Almost every path of the Brownian bridge on `[0, T]`, `T ≠ 0`, vanishes at `T`. -/
theorem ae_brownianBridgeMeasure_apply_eq_zero (hT : T ≠ 0) :
    ∀ᵐ g ∂brownianBridgeMeasure T, g ⟨T, le_rfl⟩ = 0 := by
  rw [brownianBridgeMeasure, ae_map_iff
    (Measurable.of_eval fun t ↦ by fun_prop).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)]
  exact Filter.Eventually.of_forall fun ω ↦ brownianBridge_self hT ω

/-- The **endpoint kernel** of Brownian motion on `[0, T]`: the law of `t ↦ X t + (t / T) x` for
`X` with law `brownianBridgeMeasure T`. For `T ≠ 0` this is the Brownian bridge from `0` to `x`.
For `T = 0` the kernel is constant, equal to `brownianBridgeMeasure 0`, and the endpoint `x` only
matters up to the `gaussianReal 0 0`-null set `{x ≠ 0}`.
By `ProbabilityTheory.IsPreBrownianReal.map_prodMk_eq_compProd_brownianBridgeKernel` it
disintegrates the law of a pre-Brownian path on `[0, T]` with respect to its endpoint. -/
noncomputable def brownianBridgeKernel (T : ℝ≥0) : Kernel ℝ (Set.Iic T → ℝ) :=
  (Kernel.deterministic id measurable_id ×ₖ Kernel.const ℝ (brownianBridgeMeasure T)).map
    fun p (t : Set.Iic T) ↦ p.2 t + (t / T : ℝ) * p.1

@[simp]
theorem brownianBridgeKernel_apply (x : ℝ) :
    brownianBridgeKernel T x =
      (brownianBridgeMeasure T).map fun g (t : Set.Iic T) ↦ g t + (t / T : ℝ) * x := by
  rw [brownianBridgeKernel, Kernel.map_apply _ (by fun_prop)]
  simp only [Kernel.prod_apply, Kernel.deterministic_apply, id_eq, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map (by fun_prop) (by fun_prop), Function.comp_def]

instance (T : ℝ≥0) : IsMarkovKernel (brownianBridgeKernel T) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The bridge from `0` to `x` on `[0, T]`, `T ≠ 0`, ends at `x` almost surely. -/
theorem ae_brownianBridgeKernel_apply_eq (hT : T ≠ 0) (x : ℝ) :
    ∀ᵐ g ∂brownianBridgeKernel T x, g ⟨T, le_rfl⟩ = x := by
  rw [brownianBridgeKernel_apply, ae_map_iff (Measurable.of_eval fun t ↦ by fun_prop).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)]
  filter_upwards [ae_brownianBridgeMeasure_apply_eq_zero hT] with g hg
  simp [hg, hT]

end TauCeti

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti TauCeti.Probability BrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- The finite-dimensional laws of the bridge of a pre-Brownian motion on `[0, T]` are images of
the finite-dimensional laws of Brownian motion, so they do not depend on the process. -/
private lemma map_restrict_brownianBridge (hB : IsPreBrownianReal B P) (I : Finset (Set.Iic T)) :
    P.map (fun ω ↦ I.restrict fun t : Set.Iic T ↦ brownianBridge B T t ω) =
      (projectiveFamily (insert T (I.map (Function.Embedding.subtype _)))).map
        fun x (i : I) ↦
          x ⟨i.val.val, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ i.property)⟩ -
          (i.val.val / T : ℝ) * x ⟨T, Finset.mem_insert_self _ _⟩ := by
  set J := insert T (I.map (Function.Embedding.subtype _))
  have hJ := hB.hasLaw J
  rw [← hJ.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hJ.aemeasurable]
  -- the bridge restricted to `I` is the linear image of the process restricted to `J`
  refine congrArg (Measure.map · P) (funext fun ω ↦ funext fun i ↦ ?_)
  simp

/-- The path of the bridge of a pre-Brownian motion on `[0, T]` has law `brownianBridgeMeasure T`
as soon as the path of the process on `[0, T]` is almost everywhere measurable. -/
theorem hasLaw_brownianBridgeMeasure (hB : IsPreBrownianReal B P)
    (hm : AEMeasurable (fun ω (t : Set.Iic T) ↦ B t ω) P) :
    HasLaw (fun ω (t : Set.Iic T) ↦ brownianBridge B T t ω) (brownianBridgeMeasure T) P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let Φ : (Set.Iic T → ℝ) → Set.Iic T → ℝ := fun g t ↦ g t - (t / T : ℝ) * g ⟨T, le_rfl⟩
  have hΦ : Measurable Φ := Measurable.of_eval fun t ↦ by fun_prop
  have hX : AEMeasurable (fun ω (t : Set.Iic T) ↦ brownianBridge B T t ω) P :=
    hΦ.comp_aemeasurable hm
  have hX₀ : Measurable fun (ω : ℝ≥0 → ℝ) (t : Set.Iic T) ↦ brownianBridge (fun t ω ↦ ω t) T t ω :=
    Measurable.of_eval fun t ↦ by fun_prop
  refine ⟨hX, IsProjectiveLimit.unique (P := fun I ↦ (P.map _).map I.restrict)
    (fun I ↦ rfl) fun I ↦ ?_⟩
  dsimp only
  rw [brownianBridgeMeasure, Measure.map_map (Finset.measurable_restrict I) hX₀,
    AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hX]
  exact (map_restrict_brownianBridge isPreBrownianReal_eval_brownianProjectiveLimit I).trans
    (map_restrict_brownianBridge hB I).symm

/-- **Endpoint disintegration of Brownian motion.** For a pre-Brownian motion whose path on
`[0, T]` is almost everywhere measurable, the joint law of the endpoint `B T` and the path on
`[0, T]` is `gaussianReal 0 T ⊗ₘ brownianBridgeKernel T`: given `B T = x`, the path on `[0, T]` is
a Brownian bridge from `0` to `x`. -/
theorem map_prodMk_eq_compProd_brownianBridgeKernel (hB : IsPreBrownianReal B P)
    (hm : AEMeasurable (fun ω (t : Set.Iic T) ↦ B t ω) P) :
    P.map (fun ω ↦ (B T ω, fun t : Set.Iic T ↦ B t ω)) =
      gaussianReal 0 T ⊗ₘ brownianBridgeKernel T := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hX := hasLaw_brownianBridgeMeasure hB hm
  have hY := hB.hasLaw_eval T
  have hprod : P.map (fun ω ↦ (B T ω, fun t : Set.Iic T ↦ brownianBridge B T t ω)) =
      (gaussianReal 0 T).prod (brownianBridgeMeasure T) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable).1
      (hB.indepFun_brownianBridge T).symm, hY.map_eq, hX.map_eq]
  let G : ℝ × (Set.Iic T → ℝ) → ℝ × (Set.Iic T → ℝ) :=
    fun p ↦ (p.1, fun t ↦ p.2 t + (t / T : ℝ) * p.1)
  have hG : Measurable G := measurable_fst.prodMk (Measurable.of_eval fun t ↦ by fun_prop)
  have hBG : (fun ω ↦ (B T ω, fun t : Set.Iic T ↦ B t ω)) =
      G ∘ fun ω ↦ (B T ω, fun t : Set.Iic T ↦ brownianBridge B T t ω) := by
    ext ω t <;> simp [G]
  rw [hBG, ← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable
    (hY.aemeasurable.prodMk hX.aemeasurable), hprod]
  ext s hs
  rw [Measure.map_apply hG hs, Measure.prod_apply (hG hs), Measure.compProd_apply hs]
  refine lintegral_congr fun x ↦ ?_
  rw [brownianBridgeKernel_apply,
    Measure.map_apply (Measurable.of_eval fun t ↦ by fun_prop) (measurable_prodMk_left hs)]
  -- both sides measure `{g | (x, fun t ↦ g t + (t / T) * x) ∈ s}`
  refine congrArg (brownianBridgeMeasure T) (Set.ext fun g ↦ ?_)
  simp [G]

end ProbabilityTheory.IsPreBrownianReal
