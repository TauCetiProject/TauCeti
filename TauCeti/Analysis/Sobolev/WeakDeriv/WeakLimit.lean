/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
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
`TauCeti.hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub`.

## Main declarations

* `TestFunction.memLp_smul_const`: `φ • y ∈ L²(Ω; H)` for a test function `φ` on `Ω`.
* `TestFunction.inner_integral_smul_eq_inner_toLp`: testing against `φ • y` as an `L²` inner
  product.
* `TauCeti.hasWeakLineDerivOn_of_tendsto_inner_toLp`: weak derivatives pass to weak `L²` limits.

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
      rfl
    · simpa using ((Real.continuous_sqrt.tendsto 0).comp hFf).mul_const ‖Ψ‖
  have h2 : Tendsto (fun n ↦ ⟪∫ x, (φ : E → ℝ) x • G n x ∂μ, y⟫_ℝ) l
      (𝓝 ⟪∫ x, (φ : E → ℝ) x • g x ∂μ, y⟫_ℝ) := by
    simp only [φ.inner_integral_smul_eq_inner_toLp (hGm _),
      φ.inner_integral_smul_eq_inner_toLp (Lp.memLp g), Lp.toLp_coeFn]
    exact hGg _
  rw [inner_neg_left]
  refine tendsto_nhds_unique (h1.congr fun n ↦ ?_) h2.neg
  rw [(hF n).integral_lineDeriv_smul_eq_neg_integral_smul φ, inner_neg_left]

end TauCeti
