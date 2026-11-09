/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.Harmonic.Analytic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Gain
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Interior regularity for semilinear Poisson equations in the plane

Let `U ⊆ ℂ` be open and let `w` be continuous on `U`. Say that `w` solves `Δw = f` on `U` in the
sense of distributions if `∫ Δφ · w = ∫ φ f` for every test function `φ ∈ 𝓓(U)`.

* **Linear gain.** If `f` is `C^k` on `U`, then `w` is `C^(k+1)` on `U`
  (`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq`). Near a point, write
  `w = (w + G ⋆ (χ f)) - G ⋆ (χ f)` for a cutoff `χ` equal to one near the point, with `G` the
  planar Newtonian kernel. The potential `G ⋆ (χ f)` is `C^(k+1)` and solves `-Δu = χ f` weakly
  (`TauCeti.contDiff_succ_planarNewtonianKernel_convolution`,
  `TauCeti.integral_laplacian_mul_planarNewtonianKernel_convolution`), so the first summand is
  weakly harmonic near the point. By Weyl's lemma (`TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn`) it
  is harmonic, hence real analytic.
* **Semilinear bootstrap.** If `Δw = F(x, w)` on `U` in the sense of distributions, with `F` of
  class `C^k` on `U × ℝ`, then `w` is `C^(k+1)` on `U`
  (`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`). Indeed, if `w` is `C^n`
  with `n ≤ k`, the right side `F(x, w(x))` is `C^n`, and the linear gain makes `w` of class
  `C^(n+1)`; starting from continuity, induction reaches every finite order up to `k + 1`. For
  `k ≥ 1` the solution is `C²` and solves the equation pointwise
  (`TauCeti.eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp`). In particular a continuous
  distributional solution with smooth `F` is smooth.

No growth condition on `F` is needed, because continuity of `w` makes `F(x, w(x))` locally bounded.
This is the step from a continuous weak solution of a nonlinear elliptic equation, such as the
reduced vortex equation of Taubes, to a smooth classical one.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.1 and Section 6.4.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III, §4.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace
open scoped Convolution ContDiff Distributions

variable {U : Opens ℂ} {w : ℂ → ℝ}

/-- **Interior regularity for Poisson's equation in the plane.** Let `w` be continuous on the open
set `U ⊆ ℂ` and solve `Δw = f` on `U` in the sense of distributions: `∫ Δφ · w = ∫ φ f` for every
test function `φ` on `U`. If `f` is `C^k` on `U`, then `w` is `C^(k+1)` on `U`. -/
theorem contDiffOn_succ_of_forall_integral_laplacian_mul_eq {f : ℂ → ℝ} {k : ℕ∞}
    (hw : ContinuousOn w U) (hf : ContDiffOn ℝ k f U)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, Δ (φ : ℂ → ℝ) x * w x = ∫ x, φ x * f x) :
    ContDiffOn ℝ ((k : ℕ∞ω) + 1) w U := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds hx)
  -- A cutoff equal to one on `closedBall x (r / 2)` and supported in `closedBall x r ⊆ U`.
  let b : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hbU : tsupport (b : ℂ → ℝ) ⊆ U := b.tsupport_eq ▸ hrU
  set g : ℂ → ℝ := fun z ↦ b z * f z with hg_def
  have hg : ContDiff ℝ k g :=
    hf.contDiff_smul_of_tsupport_subset U.isOpen b.contDiff.contDiffOn hbU
  have hgc : HasCompactSupport g := b.hasCompactSupport.mul_right
  set N := planarNewtonianKernel ⋆ g
  have hN : ContDiff ℝ ((k : ℕ∞ω) + 1) N := contDiff_succ_planarNewtonianKernel_convolution hg hgc
  -- `w + N` is weakly harmonic, hence harmonic, on `V = ball x (r / 2)`.
  let V : Opens ℂ := ⟨ball x (r / 2), isOpen_ball⟩
  have hVU : V ≤ U := fun y hy ↦ hrU (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (half_le_self hr.le)) hy)
  have hwV : ContinuousOn w V := hw.mono hVU
  have hcont : ContinuousOn (w + N) V := hwV.add hN.continuous.continuousOn
  have hharm : HarmonicOnNhd (w + N) V := by
    refine (harmonicOnNhd_iff_weaklyHarmonicOn (μ := volume) hcont).2
      (weaklyHarmonicOn_iff.2 ⟨hcont.locallyIntegrableOn V.isOpen.measurableSet, fun φ ↦ ?_⟩)
    have hw' : ∫ y, Δ (φ : ℂ → ℝ) y * w y = ∫ y, φ y * f y :=
      h ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
    have hN' := integral_laplacian_mul_planarNewtonianKernel_convolution hg.continuous hgc
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    -- The cutoff is one on the support of `φ`, so `∫ φ g = ∫ φ f`.
    have hφg : ∫ y, φ y * g y = ∫ y, φ y * f y := by
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      by_cases hy : y ∈ tsupport (φ : ℂ → ℝ)
      · simp [hg_def, b.one_of_mem_closedBall (ball_subset_closedBall (φ.tsupport_subset hy))]
      · simp [image_eq_zero_of_notMem_tsupport hy]
    have hint {u : ℂ → ℝ} (hu : ContinuousOn u V) : Integrable fun y ↦ Δ (φ : ℂ → ℝ) y * u y := by
      simpa [TestFunction.laplacianCLM_apply] using
        TestFunction.integrable_smul (LineDeriv.laplacianCLM ℝ ℂ (𝓓(V, ℝ)) φ)
          (hu.locallyIntegrableOn V.isOpen.measurableSet)
    simp only [Pi.add_apply, smul_eq_mul, mul_add]
    rw [integral_add (hint hwV) (hint hN.continuous.continuousOn), hw', hN', hφg, add_neg_cancel]
  have hwN : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (w + N) x :=
    (_root_.HarmonicAt.analyticAt (hharm x (mem_ball_self (half_pos hr)))).contDiffAt
  simpa using hwN.sub hN.contDiffAt

/-- **Interior regularity for semilinear Poisson equations in the plane.** Let `w` be continuous on
the open set `U ⊆ ℂ` and solve `Δw = F(x, w)` on `U` in the sense of distributions:
`∫ Δφ · w = ∫ φ(x) F(x, w(x)) dx` for every test function `φ` on `U`. If `F` is `C^k` on `U × ℝ`,
then `w` is `C^(k+1)` on `U`; in particular `w` is smooth when `F` is. -/
theorem contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp {F : ℂ × ℝ → ℝ} {k : ℕ∞}
    (hF : ContDiffOn ℝ k F (U ×ˢ univ)) (hw : ContinuousOn w U)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, Δ (φ : ℂ → ℝ) x * w x = ∫ x, φ x * F (x, w x)) :
    ContDiffOn ℝ ((k : ℕ∞ω) + 1) w U := by
  -- If `w` is `C^n` with `n ≤ k`, it is `C^(n+1)`.
  have hstep {n : ℕ} (hn : (n : ℕ∞) ≤ k) (hwn : ContDiffOn ℝ n w U) :
      ContDiffOn ℝ (n + 1) w U := by
    have hFn : ContDiffOn ℝ n (fun x ↦ F (x, w x)) U :=
      (hF.of_le (by exact_mod_cast hn)).comp (contDiffOn_id.prodMk hwn)
        fun x hx ↦ ⟨hx, mem_univ _⟩
    exact_mod_cast contDiffOn_succ_of_forall_integral_laplacian_mul_eq (k := n) hw hFn h
  have hnat : ∀ n : ℕ, (n : ℕ∞) ≤ k + 1 → ContDiffOn ℝ n w U := by
    intro n
    induction n with
    | zero => exact fun _ ↦ by simpa using hw
    | succ n ih =>
      intro hn
      have hnk : (n : ℕ∞) ≤ k := by
        rw [Nat.cast_succ] at hn
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hn
      exact_mod_cast hstep hnk (ih (hnk.trans le_self_add))
  have h' : ContDiffOn ℝ ((k + 1 : ℕ∞) : ℕ∞ω) w U := contDiffOn_iff_forall_nat_le.2 hnat
  exact_mod_cast h'

/-- **A continuous distributional solution of a semilinear Poisson equation is classical.** Let `w`
be continuous on the open set `U ⊆ ℂ` and solve `Δw = F(x, w)` on `U` in the sense of
distributions, with `F` of class `C¹` on `U × ℝ`. Then `w` is `C²` on `U` and `Δw = F(x, w)` at
every point of `U`. -/
theorem eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp {F : ℂ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) (hw : ContinuousOn w U)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, Δ (φ : ℂ → ℝ) x * w x = ∫ x, φ x * F (x, w x)) :
    EqOn (Δ w) (fun x ↦ F (x, w x)) U := by
  have hw2 : ContDiffOn ℝ 2 w U := by
    have h2 := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp (k := 1) hF hw h
    have h12 : ((1 : ℕ∞) : ℕ∞ω) + 1 = 2 := by norm_num
    rwa [h12] at h2
  refine hw2.eqOn_laplacian_of_forall_integral_laplacian_smul_eq (μ := volume)
    (hF.continuousOn.comp (continuousOn_id.prodMk hw) fun x hx ↦ ⟨hx, mem_univ _⟩)
    fun φ ↦ ?_
  simpa only [smul_eq_mul] using h φ

end TauCeti
