/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Weak derivatives pass to weak `L²` limits

Let `H` be a real Hilbert space. A function `f ∈ L²(Ω; H)` is tested against a test function `φ`
on `Ω` and a vector `y ∈ H` through the `L²(Ω; H)` inner product with `φ • y`:

`⟪∫ φ • f, y⟫ = ⟪f, φ • y⟫_{L²(Ω; H)}`

(`TestFunction.inner_integral_smul_eq_inner_toLp`). So the integral identities that define a weak
derivative are continuous for weak convergence in `L²(Ω; H)`. Hence if `Fₙ → f` in `L²(Ω; H)`, each
`Fₙ` has a weak derivative `Gₙ ∈ L²(Ω; H)` in the direction `v`, and `Gₙ → g` weakly in
`L²(Ω; H)`, then `g` is a weak derivative of `f`
(`TauCeti.hasWeakLineDerivOn_of_tendsto_inner_toLp`). Only weak convergence of the derivatives is
assumed, which is what a bound on `‖Gₙ‖_{L²}` provides through weak compactness of balls in a
Hilbert space; the strong `L¹` version is
`TauCeti.hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub`. Combining the two, if `Fₙ → f` in
`L²(Ω; H)` and the weak derivatives satisfy `∫_Ω ‖Gₙ‖² ≤ M`, then `f` has a weak derivative of
norm at most `√M` in `L²(Ω; H)` (`TauCeti.exists_hasWeakLineDerivOn_and_norm_le_of_tendsto`).

## Main declarations

* `TestFunction.memLp_smul_const`: `φ • y ∈ L²(Ω; H)` for a test function `φ` on `Ω`.
* `TestFunction.inner_integral_smul_eq_inner_toLp`: testing against `φ • y` as an `L²` inner
  product.
* `TauCeti.hasWeakLineDerivOn_of_tendsto_inner_toLp`: weak derivatives pass to weak `L²` limits.
* `TauCeti.exists_hasWeakLineDerivOn_and_norm_le_of_tendsto`: `L²`-bounded weak derivatives of an
  `L²` convergent sequence give a weak derivative of the limit with the same bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.3 (weak derivatives and their
  stability under limits).
-/

public section

namespace TauCeti

open Filter MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure E} {Ω : Opens E} {v : E}

omit [CompleteSpace H] in
/-- A test function on `Ω` times a fixed vector lies in `L²(Ω; H)`. -/
theorem _root_.TestFunction.memLp_smul_const [IsFiniteMeasureOnCompacts μ] (φ : 𝓓(Ω, ℝ))
    (y : H) :
    MemLp (fun x ↦ (φ : E → ℝ) x • y) 2 (μ.restrict Ω) :=
  ((φ.continuous.smul continuous_const).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.smul_right)).restrict _

/-- **Testing as an `L²` inner product.** For `f ∈ L²(Ω; H)`, a test function `φ` on `Ω` and
`y ∈ H`, `⟪∫ φ • f, y⟫ = ⟪f, φ • y⟫_{L²(Ω; H)}`. -/
theorem _root_.TestFunction.inner_integral_smul_eq_inner_toLp [IsLocallyFiniteMeasure μ]
    (φ : 𝓓(Ω, ℝ)) {f : E → H} (hf : MemLp f 2 (μ.restrict Ω))
    (y : H) :
    ⟪∫ x, (φ : E → ℝ) x • f x ∂μ, y⟫_ℝ =
      ⟪hf.toLp f, (φ.memLp_smul_const y).toLp (fun x ↦ (φ : E → ℝ) x • y)⟫_ℝ := by
  have hint : Integrable (fun x ↦ (φ : E → ℝ) x • f x) μ :=
    φ.integrable_smul (locallyIntegrableOn_of_locallyIntegrable_restrict
      (hf.locallyIntegrable one_le_two))
  have hset : ∫ x, (φ : E → ℝ) x • f x ∂μ = ∫ x in Ω, (φ : E → ℝ) x • f x ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
    rw [image_eq_zero_of_notMem_tsupport (fun hm ↦ hx (φ.tsupport_subset hm)), zero_smul]
  rw [hset, real_inner_comm, ← integral_inner hint.integrableOn, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, (φ.memLp_smul_const y).coeFn_toLp] with x h1 h2
  rw [h1, h2, inner_smul_right, inner_smul_right, real_inner_comm]

/-- **Weak derivatives pass to weak `L²` limits.** If `F n → f` in `L²(Ω; H)`, each `F n` has a
weak derivative `G n ∈ L²(Ω; H)` in the direction `v` on `Ω`, and `G n → g` weakly in `L²(Ω; H)`,
then `g` is a weak derivative of `f` in the direction `v` on `Ω`. -/
theorem hasWeakLineDerivOn_of_tendsto_inner_toLp [IsLocallyFiniteMeasure μ] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F G : ι → E → H} {f : E → H} {g : Lp H 2 (μ.restrict Ω)}
    (hF : ∀ n, HasWeakLineDerivOn μ Ω (F n) (G n) v)
    (hFm : ∀ n, MemLp (F n) 2 (μ.restrict Ω)) (hf : MemLp f 2 (μ.restrict Ω))
    (hGm : ∀ n, MemLp (G n) 2 (μ.restrict Ω))
    (hFf : Tendsto (fun n ↦ ∫ x in Ω, ‖F n x - f x‖ ^ 2 ∂μ) l (𝓝 0))
    (hGg : ∀ Ψ : Lp H 2 (μ.restrict Ω),
      Tendsto (fun n ↦ ⟪(hGm n).toLp (G n), Ψ⟫_ℝ) l (𝓝 ⟪g, Ψ⟫_ℝ)) :
    HasWeakLineDerivOn μ Ω f g v := by
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
    locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable one_le_two),
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable one_le_two),
    fun φ ↦ ?_⟩
  set ψ : 𝓓(Ω, ℝ) := TestFunction.lineDerivCLM ℝ v φ
  have hψ (x : E) : lineDeriv ℝ (φ : E → ℝ) x v = (ψ : E → ℝ) x :=
    (TestFunction.lineDerivCLM_apply_of_le le_top).symm
  refine ext_inner_right ℝ fun y ↦ ?_
  set Ψ := (ψ.memLp_smul_const (μ := μ) y).toLp (fun x ↦ (ψ : E → ℝ) x • y)
  -- The `F`-side converges strongly, the `G`-side weakly.
  have h1 : Tendsto (fun n ↦ ⟪∫ x, lineDeriv ℝ (φ : E → ℝ) x v • F n x ∂μ, y⟫_ℝ) l
      (𝓝 ⟪∫ x, lineDeriv ℝ (φ : E → ℝ) x v • f x ∂μ, y⟫_ℝ) := by
    simp only [hψ, ψ.inner_integral_smul_eq_inner_toLp (hFm _),
      ψ.inner_integral_smul_eq_inner_toLp hf]
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) (?_ : Tendsto (fun n ↦ Real.sqrt (∫ x in Ω, ‖F n x - f x‖ ^ 2 ∂μ) * ‖Ψ‖) l
        (𝓝 0)))
    · rw [← inner_sub_left, ← MemLp.toLp_sub]
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (le_of_eq ?_)
        (norm_nonneg _))
      rw [← Real.sqrt_sq (norm_nonneg _), MemLp.norm_toLp_sq]
      simp only [Pi.sub_apply]
    · simpa using ((Real.continuous_sqrt.tendsto 0).comp hFf).mul_const ‖Ψ‖
  have h2 : Tendsto (fun n ↦ ⟪∫ x, (φ : E → ℝ) x • G n x ∂μ, y⟫_ℝ) l
      (𝓝 ⟪∫ x, (φ : E → ℝ) x • g x ∂μ, y⟫_ℝ) := by
    simp only [φ.inner_integral_smul_eq_inner_toLp (hGm _),
      φ.inner_integral_smul_eq_inner_toLp (Lp.memLp g), Lp.toLp_coeFn]
    exact hGg _
  rw [inner_neg_left]
  refine tendsto_nhds_unique (h1.congr fun n ↦ ?_) h2.neg
  rw [(hF n).integral_lineDeriv_smul_eq_neg_integral_smul φ, inner_neg_left]

/-- **`L²`-bounded weak derivatives pass to `L²` limits.** If `F n → f` in `L²(Ω; H)` and each
`F n` has a weak derivative `G n ∈ L²(Ω; H)` in the direction `v` on `Ω` with
`∫_Ω ‖G n‖² ≤ M`, then `f` has a weak derivative `g ∈ L²(Ω; H)` in the direction `v` on `Ω` with
`‖g‖ ≤ √M`: a subsequence of the `G n` converges weakly in `L²(Ω; H)`, and the norm is weakly
lower semicontinuous. -/
theorem exists_hasWeakLineDerivOn_and_norm_le_of_tendsto [IsLocallyFiniteMeasure μ] {M : ℝ}
    {F G : ℕ → E → H} {f : E → H} (hF : ∀ n, HasWeakLineDerivOn μ Ω (F n) (G n) v)
    (hFm : ∀ n, MemLp (F n) 2 (μ.restrict Ω)) (hf : MemLp f 2 (μ.restrict Ω))
    (hGm : ∀ n, MemLp (G n) 2 (μ.restrict Ω)) (hGM : ∀ n, ∫ x in Ω, ‖G n x‖ ^ 2 ∂μ ≤ M)
    (hFf : Tendsto (fun n ↦ ∫ x in Ω, ‖F n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ g : Lp H 2 (μ.restrict Ω), HasWeakLineDerivOn μ Ω f g v ∧ ‖g‖ ≤ Real.sqrt M := by
  set Gl : ℕ → Lp H 2 (μ.restrict Ω) := fun n ↦ (hGm n).toLp (G n)
  have hGl (n : ℕ) : ‖Gl n‖ ≤ Real.sqrt M := by
    rw [← Real.sqrt_sq (norm_nonneg _), MemLp.norm_toLp_sq]
    exact Real.sqrt_le_sqrt (hGM n)
  have hbdd : Bornology.IsBounded (Set.range Gl) :=
    isBounded_iff_forall_norm_le.2 ⟨Real.sqrt M, by rintro _ ⟨n, rfl⟩; exact hGl n⟩
  obtain ⟨g, φs, hφs, hweak⟩ := tendsto_subseq_toWeakSpace_of_isBounded
    (surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ)) hbdd
  have hinner (Ψ : Lp H 2 (μ.restrict Ω)) :
      Tendsto (fun k ↦ ⟪Gl (φs k), Ψ⟫_ℝ) atTop (𝓝 ⟪g, Ψ⟫_ℝ) := by
    have hc : Continuous fun w : WeakSpace ℝ (Lp H 2 (μ.restrict Ω)) ↦
        innerSL ℝ Ψ ((toWeakSpace ℝ _).symm w) :=
      WeakBilin.eval_continuous (topDualPairing ℝ _).flip (innerSL ℝ Ψ)
    simpa [Function.comp_def, real_inner_comm] using (hc.tendsto _).comp hweak
  refine ⟨g, hasWeakLineDerivOn_of_tendsto_inner_toLp (F := fun k ↦ F (φs k))
    (G := fun k ↦ G (φs k)) (fun k ↦ hF (φs k)) (fun k ↦ hFm (φs k)) hf (fun k ↦ hGm (φs k))
    (hFf.comp hφs.tendsto_atTop) hinner, ?_⟩
  -- Weak lower semicontinuity of the norm.
  have h3 := le_of_tendsto' (hinner g) fun k ↦ (real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hGl (φs k)) (norm_nonneg g))
  rw [real_inner_self_eq_norm_sq] at h3
  nlinarith [norm_nonneg g, Real.sqrt_nonneg M]

end TauCeti
