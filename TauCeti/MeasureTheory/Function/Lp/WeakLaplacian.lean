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
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

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
    rw [hl, hr, integral_add (φ.integrable_laplacian_smul_of_memLp (Lp.memLp _))
      (φ.integrable_laplacian_smul_of_memLp (Lp.memLp _)),
      integral_add (φ.integrable_smul_of_memLp (Lp.memLp _))
        (φ.integrable_smul_of_memLp (Lp.memLp _)), h₁ φ, h₂ φ]
  zero_mem' φ := by simp
  smul_mem' c fg h φ := by
    have hl : ∫ x, Δ (φ : E → ℝ) x • (c • fg).1 x = ∫ x, c • (Δ (φ : E → ℝ) x • fg.1 x) :=
      integral_congr_ae <| (Lp.coeFn_smul c fg.1).mono fun x hx ↦ by
        simp only [Prod.smul_fst, hx, Pi.smul_apply, smul_comm c]
    have hr : ∫ x, φ x • (c • fg).2 x = ∫ x, c • (φ x • fg.2 x) :=
      integral_congr_ae <| (Lp.coeFn_smul c fg.2).mono fun x hx ↦ by
        simp only [Prod.smul_snd, hx, Pi.smul_apply, smul_comm c]
    have h' : ∫ x, Δ (φ : E → ℝ) x • fg.1 x = ∫ x, φ x • fg.2 x := h φ
    rw [hl, hr, integral_smul, integral_smul, h']

private theorem weakLaplacianGraph_snd_eq_zero
    (fg : Lp F p (volume : Measure E) × Lp F p (volume : Measure E))
    (hfg : fg ∈ weakLaplacianGraph (E := E) (F := F) (p := p)) (h0 : fg.1 = 0) : fg.2 = 0 := by
  refine Lp.eq_zero_of_forall_integral_testFunction_smul_eq_zero fun φ ↦ ?_
  have h : ∫ x, Δ (φ : E → ℝ) x • fg.1 x = ∫ x, φ x • fg.2 x := hfg φ
  simp [← h, h0]

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
    have hΔg : ∀ t, Δ g t = Δ ρ (y - t) := fun t ↦ congrFun (laplacian_comp_sub_left ρ y) t
    have hlap : Δ u y = ∫ t, Δ ρ (y - t) • v t := by
      rw [hu_def, ← convolution_flip, HasCompactSupport.laplacian_convolution_right _ hρc hvl hρ2,
        convolution_def]
      simp [mul_comm]
    have hψ := h ψ
    simp only [ψ, TestFunction.coe_mk, hΔg] at hψ
    rw [hlap, hψ, hu_def, convolution_lsmul_swap, ← smul_eq_mul, ← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun t ↦ by simp only [g, smul_eq_mul]; ring)
  -- `u` is bounded since `ρ` lies in the Hölder-conjugate space `L^{p'}`.
  have : (ENNReal.conjExponent p).HolderConjugate p :=
    (ENNReal.HolderConjugate.conjExponent Fact.out).symm
  have hub : Bornology.IsBounded (range u) :=
    isBounded_range_convolution_of_memLp (p := ENNReal.conjExponent p) (lsmul ℝ ℝ)
      (hρ.continuous.memLp_of_hasCompactSupport hρc) hv
  -- The maximum principle makes `u` vanish, and `u 0` is the pairing of `v` with `φ`.
  have hu0 := congrFun (eq_zero_of_laplacian_eq_mul_of_isBounded hc hu hub hΔu) 0
  rwa [hu_def, hρ_def, convolution_lsmul_comp_neg_apply_zero, Pi.zero_apply] at hu0

/-- **An `Lᵖ` solution of `Δf = c f`, `c > 0`, vanishes.** If the distributional Laplacian of
`f ∈ Lᵖ` is `c f` for a positive constant `c`, then `f = 0`. -/
theorem eq_zero_of_mem_graph_weakLaplacianLp_smul {c : ℝ} (hc : 0 < c)
    {f : Lp F p (volume : Measure E)} (h : (f, c • f) ∈ (weakLaplacianLp E F p).graph) :
    f = 0 := by
  rw [mem_graph_weakLaplacianLp_iff] at h
  refine Lp.eq_zero_of_forall_integral_testFunction_smul_eq_zero fun φ ↦ ?_
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  -- Apply the scalar statement to `ℓ ∘ f`.
  have hℓ : MemLp (fun x ↦ ℓ (f x)) p volume := ℓ.comp_memLp' (Lp.memLp f)
  have hscal : ∀ ψ : 𝓓((⊤ : Opens E), ℝ),
      ∫ x, Δ (ψ : E → ℝ) x • ℓ (f x) = ∫ x, ψ x • (c * ℓ (f x)) := by
    intro ψ
    have := congrArg ℓ (h ψ)
    rw [← ℓ.integral_comp_comm (ψ.integrable_laplacian_smul_of_memLp (Lp.memLp f)),
      ← ℓ.integral_comp_comm (ψ.integrable_smul_of_memLp (Lp.memLp _))] at this
    simp only [map_smul] at this
    refine this.trans (integral_congr_ae <| (Lp.coeFn_smul c f).mono fun x hx ↦ ?_)
    simp only [hx, Pi.smul_apply, map_smul, smul_eq_mul]
  rw [← ℓ.integral_comp_comm (φ.integrable_smul_of_memLp (Lp.memLp f))]
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
