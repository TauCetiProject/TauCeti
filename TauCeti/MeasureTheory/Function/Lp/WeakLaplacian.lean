/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.IntegralBoundedSmul

/-!
# The Laplacian on `Lᵖ` in the sense of distributions

Let `E` be a finite-dimensional real inner product space with its volume measure, `F` a real
Banach space and `1 ≤ p ≤ ∞`. An element `f ∈ Lᵖ(E; F)` has **Laplacian `g ∈ Lᵖ(E; F)` in the
sense of distributions** if

`∫ Δφ • f = ∫ φ • g` for every test function `φ ∈ 𝓓(E, ℝ)`.

The function `g` is then unique almost everywhere, so these pairs `(f, g)` form the graph of an
unbounded operator `TauCeti.weakLaplacianLp` on `Lᵖ(E; F)`, whose domain is
`{f ∈ Lᵖ : Δf ∈ Lᵖ}`. It is the natural `Lᵖ` realization of the Laplacian on the whole space,
with Mathlib's sign: on functions of class `C²` it is the classical Laplacian
(`TauCeti.mem_graph_weakLaplacianLp_of_contDiff`). For `1 ≤ p < ∞` it is the generator of the
heat semigroup (`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`).

The second result of the file is that `c - Δ` is injective on this domain for every `c > 0`
(`TauCeti.smul_sub_weakLaplacianLp_injective`): an `Lᵖ` solution of `Δf = c f` vanishes. For a
test function `ρ`, the convolution `ρ ⋆ f` is smooth, bounded because `f ∈ Lᵖ`, and solves
`Δ(ρ ⋆ f) = c (ρ ⋆ f)` classically, since its Laplacian at `y` is the pairing of `f` with the
Laplacian of the test function `t ↦ ρ(y - t)`. The maximum principle for `-Δ + c` on the whole
space (`TauCeti.eq_zero_of_laplacian_eq_mul_of_isBounded`) makes it vanish, and the values
`(ρ ⋆ f)(0)` are the pairings of `f` with all test functions. Vector-valued `f` are reduced to
the scalar case by continuous linear functionals.

## Main declarations

* `TauCeti.weakLaplacianLp`: the Laplacian in the sense of distributions as a partial linear map
  on `Lᵖ(E; F)`.
* `TauCeti.mem_graph_weakLaplacianLp_iff`, `TauCeti.mem_domain_weakLaplacianLp_iff`,
  `TauCeti.integral_laplacian_smul_eq_integral_smul_weakLaplacianLp`: its graph, its domain and
  its defining identity.
* `TauCeti.mem_graph_weakLaplacianLp_of_contDiff`: it extends the classical Laplacian.
* `TauCeti.eq_zero_of_mem_graph_weakLaplacianLp_smul`: an `Lᵖ` solution of `Δf = c f`, `c > 0`,
  is zero.
* `TauCeti.smul_sub_weakLaplacianLp_injective`: `c - Δ` is injective on the domain for `c > 0`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup and its generator).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.1 (the maximum principle).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace
open scoped Convolution Distributions ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [CompleteSpace F] in
/-- The Laplacian of a test function, multiplied by an `Lᵖ` function, is integrable. -/
private theorem integrable_laplacian_smul (φ : 𝓓((⊤ : Opens E), ℝ))
    (f : Lp F p (volume : Measure E)) :
    Integrable (fun x ↦ Δ (φ : E → ℝ) x • f x) volume := by
  have hf : LocallyIntegrableOn f (⊤ : Opens E) volume := by
    rw [Opens.coe_top, locallyIntegrableOn_univ]
    exact (Lp.memLp f).locallyIntegrable Fact.out
  simpa only [TestFunction.laplacianCLM_apply] using
    TestFunction.integrable_smul (LineDeriv.laplacianCLM ℝ E (𝓓((⊤ : Opens E), ℝ)) φ) hf

omit [CompleteSpace F] in
/-- A test function, multiplied by an `Lᵖ` function, is integrable. -/
private theorem integrable_testFunction_smul (φ : 𝓓((⊤ : Opens E), ℝ))
    (f : Lp F p (volume : Measure E)) :
    Integrable (fun x ↦ φ x • f x) volume := by
  have hf : LocallyIntegrableOn f (⊤ : Opens E) volume := by
    rw [Opens.coe_top, locallyIntegrableOn_univ]
    exact (Lp.memLp f).locallyIntegrable Fact.out
  exact TestFunction.integrable_smul φ hf

omit [CompleteSpace F] [Fact (1 ≤ p)] in
/-- Pairing anything with the zero class of `Lᵖ` gives zero. -/
private theorem integral_smul_coeFn_zero (k : E → ℝ) :
    ∫ x, k x • (0 : Lp F p (volume : Measure E)) x = 0 :=
  (integral_congr_ae <| (Lp.coeFn_zero F p volume).mono fun x hx ↦ by
    rw [hx, Pi.zero_apply, smul_zero]).trans (integral_zero E F)

/-- The pairs `(f, g)` of `Lᵖ` functions with `Δf = g` in the sense of distributions. -/
private def weakLaplacianGraph :
    Submodule ℝ (Lp F p (volume : Measure E) × Lp F p (volume : Measure E)) where
  carrier := {fg | ∀ φ : 𝓓((⊤ : Opens E), ℝ),
    ∫ x, Δ (φ : E → ℝ) x • fg.1 x = ∫ x, φ x • fg.2 x}
  add_mem' {fg₁ fg₂} h₁ h₂ φ := by
    have hl : ∫ x, Δ (φ : E → ℝ) x • (fg₁ + fg₂).1 x =
        ∫ x, (Δ (φ : E → ℝ) x • fg₁.1 x + Δ (φ : E → ℝ) x • fg₂.1 x) :=
      integral_congr_ae <| (Lp.coeFn_add fg₁.1 fg₂.1).mono fun x hx ↦ by
        simp only [Prod.fst_add, hx, Pi.add_apply, smul_add]
    have hr : ∫ x, φ x • (fg₁ + fg₂).2 x = ∫ x, (φ x • fg₁.2 x + φ x • fg₂.2 x) :=
      integral_congr_ae <| (Lp.coeFn_add fg₁.2 fg₂.2).mono fun x hx ↦ by
        simp only [Prod.snd_add, hx, Pi.add_apply, smul_add]
    rw [hl, hr, integral_add (integrable_laplacian_smul φ _) (integrable_laplacian_smul φ _),
      integral_add (integrable_testFunction_smul φ _) (integrable_testFunction_smul φ _), h₁ φ,
      h₂ φ]
  zero_mem' φ := (integral_smul_coeFn_zero _).trans (integral_smul_coeFn_zero _).symm
  smul_mem' c fg h φ := by
    have hl : ∫ x, Δ (φ : E → ℝ) x • (c • fg).1 x = ∫ x, c • (Δ (φ : E → ℝ) x • fg.1 x) :=
      integral_congr_ae <| (Lp.coeFn_smul c fg.1).mono fun x hx ↦ by
        simp only [Prod.smul_fst, hx, Pi.smul_apply, smul_comm c]
    have hr : ∫ x, φ x • (c • fg).2 x = ∫ x, c • (φ x • fg.2 x) :=
      integral_congr_ae <| (Lp.coeFn_smul c fg.2).mono fun x hx ↦ by
        simp only [Prod.smul_snd, hx, Pi.smul_apply, smul_comm c]
    have h' : ∫ x, Δ (φ : E → ℝ) x • fg.1 x = ∫ x, φ x • fg.2 x := h φ
    rw [hl, hr, integral_smul, integral_smul, h']

/-- An `Lᵖ` function all of whose pairings with test functions vanish is zero. -/
private theorem eq_zero_of_forall_integral_smul_eq_zero {g : Lp F p (volume : Measure E)}
    (h : ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, φ x • g x = 0) : g = 0 := by
  refine Lp.eq_zero_iff_ae_eq_zero.2 <| ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp g).locallyIntegrable Fact.out) fun ψ hψ hψc ↦ ?_
  exact h ⟨ψ, hψ, hψc, by simp⟩

private theorem weakLaplacianGraph_snd_eq_zero
    (fg : Lp F p (volume : Measure E) × Lp F p (volume : Measure E))
    (hfg : fg ∈ weakLaplacianGraph (E := E) (F := F) (p := p)) (h0 : fg.1 = 0) : fg.2 = 0 := by
  refine eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ ?_
  have h : ∫ x, Δ (φ : E → ℝ) x • fg.1 x = ∫ x, φ x • fg.2 x := hfg φ
  rw [← h, h0, integral_smul_coeFn_zero]

variable (E F p) in
/-- **The Laplacian on `Lᵖ` in the sense of distributions**, as a partial linear map on
`Lᵖ(E; F)`. Its domain consists of the `f ∈ Lᵖ` whose distributional Laplacian is again in `Lᵖ`,
and it sends such `f` to the unique `g ∈ Lᵖ` with `∫ Δφ • f = ∫ φ • g` for every test function
`φ` (`TauCeti.mem_graph_weakLaplacianLp_iff`). -/
def weakLaplacianLp : Lp F p (volume : Measure E) →ₗ.[ℝ] Lp F p (volume : Measure E) :=
  (weakLaplacianGraph (E := E) (F := F) (p := p)).toLinearPMap

/-- The graph of `TauCeti.weakLaplacianLp` consists of the pairs `(f, g)` with `Δf = g` in the
sense of distributions. -/
theorem mem_graph_weakLaplacianLp_iff {f g : Lp F p (volume : Measure E)} :
    (f, g) ∈ (weakLaplacianLp E F p).graph ↔
      ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, φ x • g x := by
  rw [weakLaplacianLp, Submodule.toLinearPMap_graph_eq _ weakLaplacianGraph_snd_eq_zero]
  rfl

/-- The domain of `TauCeti.weakLaplacianLp` consists of the `f ∈ Lᵖ` whose Laplacian in the
sense of distributions lies in `Lᵖ`. -/
theorem mem_domain_weakLaplacianLp_iff {f : Lp F p (volume : Measure E)} :
    f ∈ (weakLaplacianLp E F p).domain ↔
      ∃ g : Lp F p (volume : Measure E),
        ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, φ x • g x := by
  simp_rw [LinearPMap.mem_domain_iff, mem_graph_weakLaplacianLp_iff]

/-- **The defining identity of `TauCeti.weakLaplacianLp`**: `∫ Δφ • f = ∫ φ • Δf` for every `f`
in the domain and every test function `φ`. -/
theorem integral_laplacian_smul_eq_integral_smul_weakLaplacianLp
    (f : (weakLaplacianLp E F p).domain) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • (f : Lp F p (volume : Measure E)) x =
      ∫ x, φ x • weakLaplacianLp E F p f x :=
  mem_graph_weakLaplacianLp_iff.1 ((weakLaplacianLp E F p).mem_graph f) φ

/-- `TauCeti.weakLaplacianLp` sends `f` to `g` exactly when `Δf = g` in the sense of
distributions. -/
theorem weakLaplacianLp_apply_eq_iff (f : (weakLaplacianLp E F p).domain)
    {g : Lp F p (volume : Measure E)} :
    weakLaplacianLp E F p f = g ↔ ∀ φ : 𝓓((⊤ : Opens E), ℝ),
      ∫ x, Δ (φ : E → ℝ) x • (f : Lp F p (volume : Measure E)) x = ∫ x, φ x • g x := by
  rw [← mem_graph_weakLaplacianLp_iff, ← LinearPMap.image_iff f.2]
  exact eq_comm

/-- **On `C²` functions the distributional Laplacian is the classical one.** If `u` is of class
`C²` and `f, g ∈ Lᵖ` are the classes of `u` and `Δu`, then `(f, g)` lies in the graph of
`TauCeti.weakLaplacianLp`. -/
theorem mem_graph_weakLaplacianLp_of_contDiff {u : E → F} (hu : ContDiff ℝ 2 u)
    {f g : Lp F p (volume : Measure E)} (hf : f =ᵐ[volume] u) (hg : g =ᵐ[volume] Δ u) :
    (f, g) ∈ (weakLaplacianLp E F p).graph := by
  refine mem_graph_weakLaplacianLp_iff.2 fun φ ↦ ?_
  calc ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, Δ (φ : E → ℝ) x • u x :=
        integral_congr_ae (hf.mono fun x hx ↦ by simp only [hx])
    _ = ∫ x, φ x • Δ u x := hu.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian φ
    _ = ∫ x, φ x • g x := integral_congr_ae (hg.mono fun x hx ↦ by simp only [hx])

/-! ### `c - Δ` is injective -/

/-- The convolution `ρ ⋆ v` of a test function with an `Lᵖ` function is bounded. -/
private theorem isBounded_range_convolution {ρ : E → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) {v : E → ℝ} (hv : MemLp v p volume) :
    Bornology.IsBounded (range (ρ ⋆[lsmul ℝ ℝ, volume] v)) := by
  obtain ⟨R, hR⟩ := hρc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨B, hB⟩ := hρc.exists_bound_of_continuous hρ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine isBounded_iff_forall_norm_le.2 ⟨B * ((volume (closedBall (0 : E) R)) ^
    (1 - 1 / p.toReal) * eLpNorm v p volume).toReal, ?_⟩
  rintro _ ⟨y, rfl⟩
  -- Only the values of `v` on `W` enter: `ρ (y - t) = 0` for `t ∉ W`.
  have hzero : ∀ t ∉ closedBall y R, ρ (y - t) = 0 := fun t ht ↦ image_eq_zero_of_notMem_tsupport
    fun h ↦ ht (by rw [mem_closedBall, dist_comm, dist_eq_norm]; simpa using hR h)
  have hval : (ρ ⋆[lsmul ℝ ℝ, volume] v) y = ∫ t, ρ (y - t) • (closedBall y R).indicator v t := by
    rw [convolution_lsmul_swap]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    dsimp only
    by_cases ht : t ∈ closedBall y R
    · rw [indicator_of_mem ht]
    · rw [hzero t ht, zero_smul, zero_smul]
  have hW : volume (closedBall y R) ≠ ∞ := measure_closedBall_lt_top.ne
  obtain ⟨-, hle⟩ := integrable_smul_and_norm_integral_smul_le hW hB0
    (hρ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun t ↦ hB (y - t)) Fact.out
    (hv.indicator measurableSet_closedBall.nullMeasurableSet)
    (ae_of_all _ fun t ht ↦ indicator_of_notMem ht v)
  rw [hval]
  refine hle.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ ?_) hB0)
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (ENNReal.one_sub_one_div_toReal_nonneg Fact.out) measure_closedBall_lt_top.ne)
      hv.eLpNorm_ne_top
  · rw [Measure.addHaar_closedBall_center]
    gcongr
    exact eLpNorm_indicator_le v measurableSet_closedBall.nullMeasurableSet

/-- **A scalar `Lᵖ` solution of `Δv = c v`, `c > 0`, is orthogonal to every test function.** -/
private theorem integral_smul_eq_zero_of_laplacian_eq_smul {c : ℝ} (hc : 0 < c) {v : E → ℝ}
    (hv : MemLp v p volume)
    (h : ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, Δ (φ : E → ℝ) x • v x = ∫ x, φ x • (c * v x))
    (φ : 𝓓((⊤ : Opens E), ℝ)) : ∫ x, φ x • v x = 0 := by
  have hvl : LocallyIntegrable v volume := hv.locallyIntegrable Fact.out
  -- Mollify with the reflected test function `ρ = φ(-·)`.
  set ρ : E → ℝ := fun z ↦ φ (-z) with hρ_def
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := φ.contDiff.comp contDiff_neg
  have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (WithTop.coe_le_coe.2 le_top)
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg E)
  set u : E → ℝ := ρ ⋆[lsmul ℝ ℝ, volume] v with hu_def
  have hu : ContDiff ℝ 2 u :=
    hρc.contDiff_convolution_left (lsmul ℝ ℝ) hρ2 hvl
  -- `Δu(y)` is the pairing of `v` with the Laplacian of the test function `t ↦ ρ(y - t)`.
  have hΔu : ∀ y, Δ u y = c * u y := by
    intro y
    set g : E → ℝ := fun t ↦ ρ (y - t) with hg_def
    have hgd : ContDiff ℝ (⊤ : ℕ∞) g := hρ.comp (contDiff_const.sub contDiff_id)
    have hgc : HasCompactSupport g := by
      simpa [Function.comp_def, g, ← sub_eq_add_neg] using
        hρc.comp_homeomorph ((Homeomorph.neg E).trans (Homeomorph.addLeft y))
    let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨g, hgd, hgc, by simp⟩
    have hΔg : ∀ t, Δ g t = Δ ρ (y - t) := by
      have hcomp : g = (fun s ↦ ρ (s + y)) ∘ (LinearIsometryEquiv.neg ℝ (E := E)) := by
        ext t
        simp [hg_def, neg_add_eq_sub]
      intro t
      rw [hcomp, laplacian_comp_linearIsometryEquiv_right, laplacian_comp_add_right]
      simp [neg_add_eq_sub]
    have hlap : Δ u y = ∫ t, Δ ρ (y - t) • v t := by
      rw [hu_def, ← convolution_flip, HasCompactSupport.laplacian_convolution_right _ hρc hvl hρ2,
        convolution_def]
      simp [mul_comm]
    have hψ := h ψ
    simp only [ψ, TestFunction.coe_mk, hΔg] at hψ
    rw [hlap, hψ, hu_def, convolution_lsmul_swap, ← smul_eq_mul, ← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun t ↦ by simp only [g, smul_eq_mul]; ring)
  -- The maximum principle makes `u` vanish, and `u 0` is the pairing of `v` with `φ`.
  have hu0 := congrFun (eq_zero_of_laplacian_eq_mul_of_isBounded hc hu
    (isBounded_range_convolution hρ.continuous hρc hv) hΔu) 0
  rw [hu_def, convolution_lsmul_swap, Pi.zero_apply] at hu0
  simpa [hρ_def] using hu0

/-- **An `Lᵖ` solution of `Δf = c f`, `c > 0`, vanishes.** If the distributional Laplacian of
`f ∈ Lᵖ` is `c f` for a positive constant `c`, then `f = 0`. -/
theorem eq_zero_of_mem_graph_weakLaplacianLp_smul {c : ℝ} (hc : 0 < c)
    {f : Lp F p (volume : Measure E)} (h : (f, c • f) ∈ (weakLaplacianLp E F p).graph) :
    f = 0 := by
  rw [mem_graph_weakLaplacianLp_iff] at h
  refine eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ ?_
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  -- Apply the scalar statement to `ℓ ∘ f`.
  have hℓ : MemLp (fun x ↦ ℓ (f x)) p volume := ℓ.comp_memLp' (Lp.memLp f)
  have hscal : ∀ ψ : 𝓓((⊤ : Opens E), ℝ),
      ∫ x, Δ (ψ : E → ℝ) x • ℓ (f x) = ∫ x, ψ x • (c * ℓ (f x)) := by
    intro ψ
    have := congrArg ℓ (h ψ)
    rw [← ℓ.integral_comp_comm (integrable_laplacian_smul ψ f),
      ← ℓ.integral_comp_comm (integrable_testFunction_smul ψ _)] at this
    simp only [map_smul] at this
    refine this.trans (integral_congr_ae <| (Lp.coeFn_smul c f).mono fun x hx ↦ ?_)
    simp only [hx, Pi.smul_apply, map_smul, smul_eq_mul]
  rw [← ℓ.integral_comp_comm (integrable_testFunction_smul φ f)]
  simpa only [map_smul] using integral_smul_eq_zero_of_laplacian_eq_smul hc hℓ hscal φ

/-- **`c - Δ` is injective on `Lᵖ` for `c > 0`.** -/
theorem smul_sub_weakLaplacianLp_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective fun f : (weakLaplacianLp E F p).domain ↦
      c • (f : Lp F p (volume : Measure E)) - weakLaplacianLp E F p f := by
  intro f₁ f₂ h12
  have hmem := (weakLaplacianLp E F p).mem_graph (f₁ - f₂)
  rw [LinearPMap.map_sub, Submodule.coe_sub] at hmem
  have heq : weakLaplacianLp E F p f₁ - weakLaplacianLp E F p f₂ =
      c • ((f₁ : Lp F p (volume : Measure E)) - f₂) := by
    rw [smul_sub]
    simp only at h12
    linear_combination (norm := module) -h12
  rw [heq] at hmem
  exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_mem_graph_weakLaplacianLp_smul hc hmem))

end TauCeti
