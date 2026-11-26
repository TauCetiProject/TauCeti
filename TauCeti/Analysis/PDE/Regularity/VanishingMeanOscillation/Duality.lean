/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Regularity
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.PDE.DirichletProblem.HomogeneousSobolev
import TauCeti.Analysis.Sobolev.D1p0.Restriction
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Whole-space `W^{1,p}` estimates for coefficients of small BMO norm, `1 < p < ∞`

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ`, neither symmetric nor continuous in general, whose field of operators `a(x)` has small
BMO seminorm (`TauCeti.bmoSeminorm`): its mean oscillation is at most `δ` on every ball. Let `u` be
a finite-energy weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` on `ℝ^{n+1}`,

that is an element of the homogeneous Sobolev space `D^{1,2}(ℝ^{n+1})` (`TauCeti.D1p0`), recorded
by its gradient field, with `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`. Such a
solution exists and is unique for every `G ∈ L²`
(`TauCeti.PDE.existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner`). This file proves
the `W^{1,p}` estimate

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`

off the energy exponent `p = 2`, with `C` and the threshold `δ` depending only on `n`, `p`, `λ` and
`Λ`, and the membership `∇u ∈ Lᵖ` as a conclusion:

* for `2 < p < ∞` and every `G ∈ Lᵖ`
  (`TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le`);
* for `1 < p < 2` and every `G ∈ L² ∩ Lᵖ`
  (`TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le_of_lt_two`).

At `p = 2` the estimate is the energy estimate `λ ‖∇u‖_{L²} ≤ ‖G‖_{L²}`
(`TauCeti.PDE.mul_norm_le_of_forall_integral_matrixBilinearForm_eq_integral_inner`), which needs no
smallness of the oscillation. Together these give the whole range `1 < p < ∞`.

The a priori estimate
`TauCeti.PDE.exists_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_setAverage_le` covers
`2 < p < ∞` for solutions already known to have `∇u ∈ Lᵖ`. Krylov's sharp function method behind
it works with the `L²` mean oscillation of `∇u` and does not reach `p < 2`; that range is reached
here by duality.

## The argument

* **Regularity above `2`.** On every ball `B(0, R)`, `u` is the gradient of a function in
  `H¹(B(0, R))` (`TauCeti.D1p0.exists_w1p_gradient_ae_eq`) which solves the equation there, and
  the interior regularity theorem
  `TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`, whose VMO modulus
  hypothesis at the scale `4R` is implied by the bound on the BMO seminorm, gives
  `‖∇u‖_{Lᵖ(B(0, R/2))} ≤ C (‖G‖_{Lᵖ} + |B(0, R)|^(1/p - 1/2) ‖∇u‖_{L²})`. Since `p > 2` and
  `∇u ∈ L²`, the last term tends to `0` as `R → ∞`, and Fatou's lemma gives the estimate on the
  whole space.
* **Duality below `2`.** For `1 < p < 2` let `p' > 2` be the Hölder conjugate exponent, and let
  `Φ` be bounded and vanish off a set of finite measure. The adjoint problem
  `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼv) = -div Φ` has a finite-energy solution `v`. The transposed coefficients are
  uniformly elliptic with the same constants and their BMO seminorm is at most twice that of `a`,
  since transposition is the adjoint of operators, an isometry. So the first step gives
  `‖∇v‖_{L^{p'}} ≤ C ‖Φ‖_{L^{p'}}`. Testing the equation of `v` with `u` and that of `u` with `v`
  gives `∫ ⟨∇u, Φ⟩ = ∫ ⟨G, ∇v⟩`
  (`TauCeti.PDE.integral_inner_eq_integral_inner_of_forall_transpose`), which Hölder's inequality
  bounds by `C ‖G‖_{Lᵖ} ‖Φ‖_{L^{p'}}`. Norming `∇u` by such `Φ`
  (`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`) gives the
  estimate. The hypothesis `G ∈ L²` makes the pairing `∫ ⟨G, ∇v⟩` the limit of the pairings with
  test gradients.

## Main declarations

* `TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le`:
  the whole-space `W^{1,p}` regularity and estimate, `2 < p < ∞`.
* `TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le_of_lt_two`:
  the whole-space `W^{1,p}` regularity and estimate, `1 < p < 2`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.8.
* G. Di Fazio, *Lᵖ estimates for divergence form elliptic equations with discontinuous
  coefficients*, Boll. Un. Mat. Ital. A (7) **10** (1996), 409–420, Theorem 2.1.
* P. Auscher, M. Qafsaoui, *Observations on `W^{1,p}` estimates for divergence elliptic equations
  with VMO coefficients*, Boll. Un. Mat. Ital. B (8) **5** (2002), 487–509, Theorem 1.1.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace Matrix
open scoped ENNReal NNReal Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The operator of the transposed matrix is the adjoint, so transposing a coefficient field at most
doubles the BMO seminorm of its field of operators. -/
private theorem bmoSeminorm_toEuclideanCLM_transpose_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) {δ : ℝ}
    (hbmo : bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume ≤ ENNReal.ofReal (δ / 2)) :
    bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ) volume ≤ ENNReal.ofReal δ := by
  have hstar : LipschitzWith 1 (star : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1))) → _) :=
    LipschitzWith.of_dist_le_mul fun S T => by
      simpa [dist_eq_norm, star_sub] using (norm_star (S - T)).le
  have heq : (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ) =
      star ∘ fun x => toEuclideanCLM (𝕜 := ℝ) (a x) := by
    ext1 x
    simp only [Function.comp_apply, ← map_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial]
  rw [heq]
  refine (hstar.bmoSeminorm_comp_le (aestronglyMeasurable_toEuclideanCLM_iff.2 ha)).trans ?_
  calc 2 * ((1 : ℝ≥0) : ℝ≥0∞) * bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume
      ≤ 2 * 1 * ENNReal.ofReal (δ / 2) := by gcongr; simp
    _ = ENNReal.ofReal δ := by
      rw [mul_one, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
      ring_nf

/-- Fatou's lemma along the balls `B(0, R)`: an `L²` field whose `Lᵖ` norm on `B(0, R/2)` is at
most `C (X + |B(0, R)|^(1/p - 1/2) ‖g‖_{L²})` for every `R > 0`, with `p > 2`, has `Lᵖ` norm at
most `C X`, since the second term tends to `0` as `R → ∞`. -/
private theorem eLpNorm_le_of_forall_eLpNorm_restrict_ball_le
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (hg2 : MemLp g 2 volume) {C : ℝ≥0} {X : ℝ≥0∞}
    (hloc : ∀ R : ℝ, 0 < R → eLpNorm g p (volume.restrict (ball 0 (R / 2))) ≤
      C * (X + volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R) ^ (p.toReal⁻¹ - 2⁻¹) *
        eLpNorm g 2 volume)) :
    eLpNorm g p volume ≤ C * X := by
  -- The term with `‖g‖_{L²}` vanishes as `R → ∞`, since `p > 2`.
  have he : p.toReal⁻¹ - 2⁻¹ < 0 := by
    have hp2 : 2 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp_top).2 hp
    exact sub_neg.2 (inv_strictAnti₀ two_pos hp2)
  have hball : Tendsto (fun k : ℕ => volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) (k + 1)))
      atTop (𝓝 ∞) := by
    have h := tendsto_measure_iUnion_atTop (μ := volume)
      (s := fun k : ℕ => ball (0 : EuclideanSpace ℝ (Fin (n + 1))) (k + 1))
      fun i j hij => ball_subset_ball (by
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith)
    rwa [iUnion_ball_nat_succ, measure_univ_of_isAddLeftInvariant] at h
  have hbound : Tendsto (fun k : ℕ => (C : ℝ≥0∞) * (X +
      volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) (k + 1)) ^ (p.toReal⁻¹ - 2⁻¹) *
        eLpNorm g 2 volume)) atTop (𝓝 (C * X)) := by
    have hpow := (ENNReal.continuous_rpow_const (y := p.toReal⁻¹ - 2⁻¹)).tendsto ∞ |>.comp hball
    rw [ENNReal.top_rpow_of_neg he] at hpow
    have hmul := ENNReal.Tendsto.mul_const hpow (Or.inr hg2.eLpNorm_ne_top)
    rw [zero_mul] at hmul
    simpa using ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hmul) (Or.inr ENNReal.coe_ne_top)
  -- Fatou's lemma along the balls `B(0, (k + 1) / 2)`.
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := volume) (p := p)
    (f := fun k : ℕ => (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((k + 1) / 2)).indicator g)
    (fun k => hg2.aestronglyMeasurable.indicator
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))))) g
    hg2.aestronglyMeasurable (ae_of_all _ fun x => ?_)).trans ?_
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * ‖x‖)
    filter_upwards [eventually_ge_atTop k] with j hj
    have hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((j + 1) / 2) := by
      rw [mem_ball_zero_iff]
      have : (k : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    rw [indicator_of_mem hx]
  · rw [← hbound.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
    rw [eLpNorm_indicator_eq_eLpNorm_restrict
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))).nullMeasurableSet]
    exact hloc (k + 1) (by positivity)

/-- **Whole-space `W^{1,p}` regularity for coefficients of small BMO norm, `2 < p < ∞`.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with constants `λ, Λ`, whose field of operators `a(x)` has BMO seminorm at most
`δ`. Let `u` be an element of the homogeneous Sobolev space `D^{1,2}_0(ℝ^{n+1})`
(`TauCeti.D1p0`), recorded by its gradient field, which solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly,
that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ Lᵖ`. Then `∇u ∈ Lᵖ` and

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

Unlike the a priori estimate
`TauCeti.PDE.exists_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_setAverage_le`, nothing
is assumed about the integrability of `∇u` beyond `L²`. The coefficients need not be symmetric or
continuous. -/
theorem exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume ≤ ENNReal.ofReal δ →
        ∀ (u : D1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            ∫ x, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
                ((u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) x) =
              ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp G p volume →
          MemLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ∧
            eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ≤
              C * eLpNorm G p volume := by
  obtain ⟨C, δ, hδ, hreg⟩ :=
    exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le (n := n) hp hp_top lam Lam
  refine ⟨C, δ, hδ, fun {a} ha hell hbmo u G hu hG => ?_⟩
  set g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    ⇑(u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))))
  have hg2 : MemLp g 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1))))))
  -- On the ball `B(0, R)`, `u` is the gradient of an `H¹` function solving the equation there,
  -- and the interior regularity theorem applies at the scale `4R`.
  have hlim : eLpNorm g p volume ≤ C * eLpNorm G p volume := by
    refine eLpNorm_le_of_forall_eLpNorm_restrict_ball_le hp hp_top hg2 fun R hR => ?_
    set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball 0 R, isOpen_ball⟩
    obtain ⟨v, hv⟩ := D1p0.exists_w1p_gradient_ae_eq (le_top : B ≤ ⊤) (convex_ball 0 R)
      isBounded_ball u
    have hvB := energyFormH1_ofTestFunctionₗ_eq_integral_inner_of_gradient_ae_eq (le_top : B ≤ ⊤)
      (fun ψ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hu ψ) hv
    obtain ⟨-, hle⟩ := hreg ha hell ((vmoModulus_le_bmoSeminorm _ _ (4 * R)).trans hbmo)
      (Ω := B) (x₀ := 0) hR le_rfl subset_rfl v G hvB (hG.restrict _)
    have hvg : W1p.gradient v =ᵐ[volume.restrict (ball 0 R)] g := hv
    rw [eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (half_le_self hR.le)) hvg.symm)]
    refine hle.trans ?_
    rw [eLpNorm_congr_ae hvg]
    gcongr <;> exact Measure.restrict_le_self
  exact ⟨hlim.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hG.eLpNorm_lt_top), hlim⟩

/-- **Whole-space `W^{1,p}` estimate for coefficients of small BMO norm, `1 < p < 2`.** Let
`1 < p < 2` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with constants `λ, Λ`, whose field of operators `a(x)` has BMO seminorm at most
`δ`. Let `u` be an element of the homogeneous Sobolev space `D^{1,2}_0(ℝ^{n+1})`
(`TauCeti.D1p0`), recorded by its gradient field, which solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly,
that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ L² ∩ Lᵖ`. Then
`∇u ∈ Lᵖ` and

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

The hypothesis `G ∈ L²` is what makes `u` the finite-energy solution with datum `G`; the constant
does not depend on `‖G‖_{L²}`. The coefficients need not be symmetric or continuous. -/
theorem exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le_of_lt_two
    {p : ℝ≥0∞} (hp : 1 < p) (hp2 : p < 2) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume ≤ ENNReal.ofReal δ →
        ∀ (u : D1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            ∫ x, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
                ((u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) x) =
              ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp G 2 volume → MemLp G p volume →
          MemLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ∧
            eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ≤
              C * eLpNorm G p volume := by
  -- The Hölder conjugate exponent `q = 1 + (p - 1)⁻¹` lies in `(2, ∞)`.
  set q := ENNReal.conjExponent p
  have : p.HolderConjugate q := .conjExponent hp.le
  have hq2 : 2 < q := by
    have h1 : p - 1 < 1 := by
      rw [ENNReal.sub_lt_iff_lt_right ENNReal.one_ne_top hp.le]
      simpa [one_add_one_eq_two] using hp2
    exact one_add_one_eq_two.symm.trans_lt
      (ENNReal.add_lt_add_left ENNReal.one_ne_top (ENNReal.one_lt_inv.2 h1))
  obtain ⟨C, δ, hδ, hreg⟩ := exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le (n := n) hq2
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp).ne lam Lam
  refine ⟨C, δ / 2, half_pos hδ, fun {a} ha hell hbmo u G hu hG2 hGp => ?_⟩
  have haT : AEStronglyMeasurable (fun x => (a x)ᵀ) volume :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable ha
  have hg2 : MemLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))))) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1))))))
  -- Norm `∇u` by bounded test fields `Φ` vanishing off a set of finite measure.
  have hle := hg2.aestronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℝ)
    (q := p) (q' := q) (C := C * eLpNorm G p volume) fun Φ s hs hΦs hΦ => by
    have hΦ2 : MemLp Φ 2 volume := hΦ.mono_exponent_of_measure_support_ne_top hΦs hs le_top
    -- The finite-energy solution `v` of the adjoint problem `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼv) = -div Φ` has
    -- `‖∇v‖_{L^q} ≤ C ‖Φ‖_{L^q}`, and `∫ ⟨∇u, Φ⟩ = ∫ ⟨G, ∇v⟩`.
    obtain ⟨v, hv, -⟩ := existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner
      (Omega := ⊤) (by rw [Opens.coe_top]; exact hell.transpose) haT.restrict (hΦ2.restrict _)
    obtain ⟨-, hvq⟩ := hreg haT hell.transpose (bmoSeminorm_toEuclideanCLM_transpose_le ha hbmo)
      v Φ (fun ψ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hv ψ)
      (hΦ.mono_exponent_of_measure_support_ne_top hΦs hs le_top)
    have hpair := integral_inner_eq_integral_inner_of_forall_transpose ha.restrict
      (fun x _ => hell.opNorm_matrixBilinearForm_le (mem_univ x)) (hG2.restrict _)
      (hΦ2.restrict _) (fun ψ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hu ψ)
      hv
    simp only [Opens.coe_top, Measure.restrict_univ] at hpair
    rw [hpair]
    calc _ ≤ eLpNorm G p volume * eLpNorm _ q volume := enorm_integral_inner_le
      _ ≤ eLpNorm G p volume * (C * eLpNorm Φ q volume) := by gcongr
      _ = C * eLpNorm G p volume * eLpNorm Φ q volume := by ring
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hGp.eLpNorm_lt_top), hle⟩

end PDE

end TauCeti
