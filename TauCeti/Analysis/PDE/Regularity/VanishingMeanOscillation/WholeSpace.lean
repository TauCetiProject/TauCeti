/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem.HomogeneousSobolev
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Regularity
import TauCeti.Analysis.Sobolev.D1p0.Restriction
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# The whole-space `W^{1,p}` estimate for coefficients of small BMO seminorm, `1 < p < ∞`

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ`, neither symmetric nor continuous in general, whose field of operators
`x ↦ a(x)` has BMO seminorm (`TauCeti.bmoSeminorm`) at most a threshold `δ`: its mean oscillation
is small on balls of every radius. Let `u` be a finite-energy weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `ℝ^{n+1}`,

that is an element of the homogeneous Sobolev space `D^{1,2}(ℝ^{n+1})` (`TauCeti.D1p0`), recorded
by its gradient field, with `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, where
`G ∈ L²`. This file proves, for every `1 < p < ∞`, that `G ∈ Lᵖ` implies `∇u ∈ Lᵖ` with

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`,

where `C` and `δ > 0` depend only on `n`, `p`, `λ` and `Λ`
(`exists_memLp_and_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_bmoSeminorm_le`, in the
namespace `TauCeti.PDE`).
Nothing is assumed about the integrability of `∇u` beyond `L²`: membership in `Lᵖ` is part of the
conclusion. This is the full range of Di Fazio's and Auscher–Qafsaoui's `W^{1,p}` theory in the
whole space, on both sides of `p = 2`. The a priori estimate
`TauCeti.PDE.exists_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_setAverage_le` covers
`2 < p < ∞` only, and only for solutions already known to have `∇u ∈ Lᵖ`.

## The argument

* **`2 < p < ∞`.** On every ball `B(0, R)` the solution is the gradient of a function in `H¹` of
  the ball (`TauCeti.D1p0.exists_w1p_gradient_ae_eq`) that solves the same equation there. The
  interior regularity theorem for coefficients of small mean oscillation below the radius `4R`
  (`TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`) applies at every
  radius, since the VMO modulus of `a` is at most its BMO seminorm, and gives
  `‖∇u‖_{Lᵖ(B(0, R/2))} ≤ C (‖G‖_{Lᵖ} + |B(0, R)|^(1/p - 1/2) ‖∇u‖_{L²})`.
  The exponent `1/p - 1/2` is negative, so the last term vanishes as `R → ∞`, and Fatou's lemma
  gives the global estimate.
* **`p = 2`.** This is the energy estimate `λ ‖∇u‖_{L²} ≤ ‖G‖_{L²}`
  (`TauCeti.PDE.mul_norm_le_of_forall_integral_matrixBilinearForm_eq_integral_inner`).
* **`1 < p < 2`, by duality.** Let `p'` be the Hölder conjugate exponent, so `p' > 2`. A bounded
  field `H` vanishing off a set of finite measure lies in `L² ∩ L^{p'}`, and the adjoint problem
  `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼw) = -div H` has a solution `w ∈ D^{1,2}(ℝ^{n+1})`
  (`TauCeti.PDE.existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner`). The
  transposed coefficients are uniformly elliptic with the same constants, and their BMO seminorm is
  at most twice that of `a`, since the operator of `Aᵀ` is the adjoint of that of `A`. So the case
  `p' > 2` gives `‖∇w‖_{L^{p'}} ≤ C ‖H‖_{L^{p'}}`. Testing the two equations with each other
  (`TauCeti.PDE.integral_matrixBilinearForm_eq_integral_inner_of_forall`),
  `∫ ⟨∇u, H⟩ = ∫ ⟨aᵀ ∇w, ∇u⟩ = ∫ ⟨a ∇u, ∇w⟩ = ∫ ⟨G, ∇w⟩`,
  which is at most `‖G‖_{Lᵖ} C ‖H‖_{L^{p'}}` by Hölder's inequality. Since such fields `H` norm
  `Lᵖ` (`AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`), this bounds
  `‖∇u‖_{Lᵖ}`.

## References

* G. Di Fazio, *Lᵖ estimates for divergence form elliptic equations with discontinuous
  coefficients*, Boll. Un. Mat. Ital. A (7) **10** (1996), 409–420, Theorem 2.1.
* P. Auscher, M. Qafsaoui, *Observations on `W^{1,p}` estimates for divergence elliptic equations
  with VMO coefficients*, Boll. Un. Mat. Ital. B (8) **5** (2002), 487–509, Theorem 1.1.
* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace Matrix
open scoped ENNReal NNReal Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The exponent conjugate to `p < 2` is greater than `2`. -/
private theorem two_lt_of_lt_two {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p < 2) : 2 < q := by
  by_contra hq
  have h := ENNReal.add_lt_add_of_lt_of_le (ENNReal.inv_ne_top.2 two_ne_zero)
    (ENNReal.inv_lt_inv.2 hp) (ENNReal.inv_le_inv.2 (not_lt.1 hq))
  rw [ENNReal.HolderConjugate.inv_add_inv_eq_one p q, ENNReal.inv_two_add_inv_two] at h
  exact lt_irrefl _ h

/-- Transposing the coefficients at most doubles the BMO seminorm of their operators: the operator
of `Aᵀ` is the adjoint of the operator of `A`, and taking adjoints is a linear isometry. -/
private theorem bmoSeminorm_toEuclideanCLM_transpose_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) :
    bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ) volume ≤
      2 * bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume := by
  have h := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))
    (F := EuclideanSpace ℝ (Fin (n + 1)))).lipschitzWith.bmoSeminorm_comp_le
      (aestronglyMeasurable_toEuclideanCLM_iff.2 ha)
  convert h using 2
  · ext x
    simp only [Function.comp_apply, adjoint_toEuclideanCLM,
      conjTranspose_eq_transpose_of_trivial]
  · simp

/-- The gradient field of an element of `D^{1,2}(ℝ^{n+1})` is a.e. strongly measurable, and has
finite `L²` norm, for Lebesgue measure. -/
private theorem aestronglyMeasurable_and_eLpNorm_ne_top_coe_d1p0
    (u : D1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2) :
    AEStronglyMeasurable (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))))) volume ∧
      eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))))) 2 volume ≠ ∞ := by
  have h := And.intro (Lp.aestronglyMeasurable (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))))))
    (Lp.eLpNorm_ne_top (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))))))
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

/-- **From balls to the whole space.** Let `e < 0` and `B < ∞`. If for every `R > 0` the `Lᵖ` norm
of `g` on `B(0, R/2)` is at most `C (A + |B(0, R)|^e B)`, then `‖g‖_{Lᵖ} ≤ C A`: the factor
`|B(0, R)|^e` tends to zero as `R → ∞`, and Fatou's lemma along the balls `B(0, k + 1)` passes the
bound to the whole space. -/
private theorem eLpNorm_le_of_forall_eLpNorm_restrict_ball_le {F : Type*} [NormedAddCommGroup F]
    {g : EuclideanSpace ℝ (Fin (n + 1)) → F} (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞}
    {e : ℝ} (he : e < 0) {A B C : ℝ≥0∞} (hB : B ≠ ∞) (hC : C ≠ ∞)
    (h : ∀ R : ℝ, 0 < R → eLpNorm g p (volume.restrict (ball 0 (R / 2))) ≤
      C * (A + volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R) ^ e * B)) :
    eLpNorm g p volume ≤ C * A := by
  have hV : Tendsto (fun k : ℕ => volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (2 * ((k : ℝ) + 1))) ^ e) atTop (𝓝 0) := by
    have hmono : Monotone fun k : ℕ =>
        ball (0 : EuclideanSpace ℝ (Fin (n + 1))) (2 * ((k : ℝ) + 1)) :=
      fun k l hkl => ball_subset_ball (by gcongr)
    have hunion : (⋃ k : ℕ, ball (0 : EuclideanSpace ℝ (Fin (n + 1))) (2 * ((k : ℝ) + 1))) =
        univ := by
      refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
      obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      exact ⟨k, mem_ball_zero_iff.2 (by linarith)⟩
    have hvol := tendsto_measure_iUnion_atTop (μ := volume) hmono
    rw [hunion, measure_univ_of_isAddLeftInvariant] at hvol
    have h := (ENNReal.continuous_rpow_const (y := e)).tendsto ∞ |>.comp hvol
    rwa [Function.comp_def, ENNReal.top_rpow_of_neg he] at h
  have hlim : Tendsto (fun k : ℕ => C * (A + volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (2 * ((k : ℝ) + 1))) ^ e * B)) atTop (𝓝 (C * A)) := by
    have h := ENNReal.Tendsto.const_mul (a := C) ((tendsto_const_nhds (x := A)).add
      (ENNReal.Tendsto.mul_const hV (Or.inr hB))) (Or.inr hC)
    simpa only [zero_mul, add_zero] using h
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (f := fun k : ℕ => (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((k : ℝ) + 1)).indicator g)
    (fun k => hg.indicator (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))
      (ε := (k : ℝ) + 1))) g hg (ae_of_all _ fun x => ?_)).trans ?_
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun k hk => ?_)
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    exact (indicator_of_mem (mem_ball_zero_iff.2 (by linarith)) g).symm
  · rw [← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]
    have hk := h (2 * ((k : ℝ) + 1)) (by positivity)
    rwa [mul_div_cancel_left₀ _ two_ne_zero] at hk

/-- **Whole-space `W^{1,p}` regularity, `2 < p < ∞`.** For coefficients of small BMO seminorm, a
finite-energy weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` with `G ∈ Lᵖ` has `∇u ∈ Lᵖ`, with
`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`. The interior regularity theorem bounds `∇u` on `B(0, R/2)` by `‖G‖_{Lᵖ}`
and `|B(0, R)|^(1/p - 1/2) ‖∇u‖_{L²}`, and the second term vanishes as `R → ∞`. -/
private theorem exists_memLp_and_eLpNorm_le_of_two_lt {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞)
    (lam Lam : ℝ) :
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
  obtain ⟨hgm, hg2⟩ := aestronglyMeasurable_and_eLpNorm_ne_top_coe_d1p0 u
  have hexp : p.toReal⁻¹ - 2⁻¹ < 0 := by
    have hp2 : 2 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal (by simp) hp_top).2 hp
    linarith [inv_strictAnti₀ two_pos hp2]
  -- The interior estimate on every ball `B(0, R)`, with the norms on the right taken globally.
  refine (fun hle => ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hG.eLpNorm_lt_top),
    hle⟩) (eLpNorm_le_of_forall_eLpNorm_restrict_ball_le hgm hexp hg2 ENNReal.coe_ne_top
      fun R hR => ?_)
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball 0 R, isOpen_ball⟩
  obtain ⟨v, hv⟩ := D1p0.exists_w1p_gradient_ae_eq (le_top : B ≤ ⊤) (convex_ball 0 R)
    isBounded_ball u
  have hvB := energyFormH1_ofTestFunctionₗ_eq_integral_inner_of_gradient_ae_eq
    (le_top : B ≤ ⊤)
    (fun φ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hu φ) hv
  have hle := (hreg (r₀ := 4 * R) ha hell ((vmoModulus_le_bmoSeminorm _ _ _).trans hbmo)
    (Ω := B) (x₀ := 0) hR le_rfl subset_rfl v G hvB (hG.restrict _)).2
  have hvR : W1p.gradient v =ᵐ[volume.restrict (ball 0 R)]
      (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))))) := hv
  rw [eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (half_le_self hR.le)) hvR), eLpNorm_congr_ae hvR] at hle
  refine hle.trans ?_
  gcongr
  all_goals exact Measure.restrict_le_self

/-- **Testing two finite-energy solutions with each other.** Let `a` be measurable and bounded, let
`u ∈ D^{1,2}(ℝ^{n+1})` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` and `w ∈ D^{1,2}(ℝ^{n+1})` solve the adjoint
equation `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼw) = -div H`, with `G, H ∈ L²`. Then `∫ ⟨∇u, H⟩ = ∫ ⟨G, ∇w⟩`: both are
`∫ ⟨a ∇u, ∇w⟩`. -/
private theorem integral_inner_eq_integral_inner_of_transpose
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
    (ha : AEStronglyMeasurable a volume) (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {u w : D1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : MemLp G 2 volume) (hH : MemLp H 2 volume)
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      ∫ x, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
          ((u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
            Set (EuclideanSpace ℝ (Fin (n + 1)))))) x) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hw : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      ∫ x, matrixBilinearForm (a x)ᵀ (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
          ((w : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
            Set (EuclideanSpace ℝ (Fin (n + 1)))))) x) =
        ∫ x, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∫ x, ⟪(u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))))) x, H x⟫_ℝ =
      ∫ x, ⟪G x, (w : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))))) x⟫_ℝ := by
  have haT : AEStronglyMeasurable (fun x => (a x)ᵀ) volume :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable ha
  have e1 := integral_matrixBilinearForm_eq_integral_inner_of_forall (Omega := ⊤)
    (a := fun x => (a x)ᵀ) (by simpa only [Opens.coe_top, Measure.restrict_univ] using haT)
    (fun x _ => (norm_matrixBilinearForm_transpose (a x)).trans_le (hbd x))
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hH)
    (fun φ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hw φ) u
  have e2 := integral_matrixBilinearForm_eq_integral_inner_of_forall (Omega := ⊤)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using ha) (fun x _ => hbd x)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hG)
    (fun φ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hu φ) w
  simp only [Opens.coe_top, Measure.restrict_univ, matrixBilinearForm_transpose_apply] at e1 e2
  rw [← e2, e1]
  exact integral_congr_ae (ae_of_all _ fun x => real_inner_comm _ _)

/-- **The estimate for `1 < p < 2`, by duality.** The case of the conjugate exponent `q > 2`,
applied to the transposed coefficients and a bounded datum `H` of finite-measure support, bounds
`∫ ⟨∇u, H⟩ = ∫ ⟨G, ∇w⟩` by `C ‖G‖_{Lᵖ} ‖H‖_{L^q}`, and such `H` norm `Lᵖ`. -/
private theorem exists_memLp_and_eLpNorm_le_of_lt_two {p : ℝ≥0∞} (hp : 1 < p) (hp2 : p < 2)
    (lam Lam : ℝ) :
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
          MemLp G 2 volume →
          eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ≤
              C * eLpNorm G p volume := by
  set q := p.conjExponent
  have : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp.le
  obtain ⟨C, δ, hδ, hreg⟩ := exists_memLp_and_eLpNorm_le_of_two_lt (n := n)
    (two_lt_of_lt_two hp2) (ENNReal.conjExponent_ne_top hp) lam Lam
  refine ⟨C, δ / 2, half_pos hδ, fun {a} ha hell hbmo u G hu hG2 => ?_⟩
  have haT : AEStronglyMeasurable (fun x => (a x)ᵀ) volume :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable ha
  have hbmoT : bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ) volume ≤
      ENNReal.ofReal δ := by
    refine (bmoSeminorm_toEuclideanCLM_transpose_le ha).trans ?_
    calc 2 * bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume ≤
          2 * ENNReal.ofReal (δ / 2) := by gcongr
      _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
        ring_nf
  refine AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le
    (aestronglyMeasurable_and_eLpNorm_ne_top_coe_d1p0 u).1 (𝕜 := ℝ) (q' := q)
    fun H s hs hsupp hH => ?_
  have hH2 : MemLp H 2 volume := hH.mono_exponent_of_measure_support_ne_top hsupp hs le_top
  -- The adjoint problem `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼw) = -div H` has a finite-energy solution `w`.
  obtain ⟨w, hw, -⟩ := existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner
    (Omega := ⊤) (hell.transpose.mono_set (subset_univ _))
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using haT)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hH2)
  have hw' := fun φ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hw φ
  rw [integral_inner_eq_integral_inner_of_transpose ha
    (fun x => hell.opNorm_matrixBilinearForm_le (mem_univ x)) hG2 hH2 hu hw']
  calc _ ≤ eLpNorm G p volume * eLpNorm (w : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
            Set (EuclideanSpace ℝ (Fin (n + 1)))))) q volume :=
        enorm_integral_inner_le
    _ ≤ eLpNorm G p volume * (C * eLpNorm H q volume) := by
        gcongr
        exact (hreg haT hell.transpose hbmoT w H hw'
          (hH.mono_exponent_of_measure_support_ne_top hsupp hs le_top)).2
    _ = C * eLpNorm G p volume * eLpNorm H q volume := by ring

/-- **The estimate for `p = 2`** is the energy estimate `λ ‖∇u‖_{L²} ≤ ‖G‖_{L²}`. -/
private theorem eLpNorm_coe_d1p0_le_of_uniformlyEllipticOn {lam Lam : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    {u : D1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      ∫ x, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
          ((u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
            Set (EuclideanSpace ℝ (Fin (n + 1)))))) x) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hG : MemLp G 2 volume) :
    eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))))) 2 volume ≤
      Real.toNNReal lam⁻¹ * eLpNorm G 2 volume := by
  have hlam := hell.pos
  have hen := mul_norm_le_of_forall_integral_matrixBilinearForm_eq_integral_inner
    (Omega := ⊤) (hell.mono_set (subset_univ _))
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using ha)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hG)
    (fun φ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hu φ)
  simp only [Opens.coe_top, Measure.restrict_univ] at hen
  have h : ENNReal.ofReal ‖u‖ = eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    rw [← Submodule.norm_coe, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  change _ ≤ ENNReal.ofReal lam⁻¹ * _
  rw [← h]
  calc ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal (lam⁻¹ * (eLpNorm G 2 volume).toReal) :=
        ENNReal.ofReal_le_ofReal ((le_inv_mul_iff₀ hlam).2 hen)
    _ = ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (eLpNorm G 2 volume).toReal :=
        ENNReal.ofReal_mul (inv_nonneg.2 hlam.le)
    _ ≤ ENNReal.ofReal lam⁻¹ * eLpNorm G 2 volume := by
        gcongr
        exact ENNReal.ofReal_toReal_le

/-- **The whole-space `W^{1,p}` estimate for coefficients of small BMO seminorm, `1 < p < ∞`.** Let
`1 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with constants `λ, Λ`, whose field of operators has BMO seminorm at most `δ`.
Let `u` be an element of the homogeneous Sobolev space `D^{1,2}_0(ℝ^{n+1})` (`TauCeti.D1p0`),
recorded by its gradient field, which solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ L² ∩ Lᵖ`. Then `∇u ∈ Lᵖ` and

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed, and nothing is assumed about the integrability
of `∇u` beyond `L²`. For `p > 2` the estimate comes from interior regularity on large balls, for
`p = 2` it is the energy estimate, and for `p < 2` it follows by duality from the case of the
conjugate exponent, applied to the transposed coefficients. -/
theorem exists_memLp_and_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_bmoSeminorm_le
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
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
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · obtain ⟨C, δ, hδ, h⟩ := exists_memLp_and_eLpNorm_le_of_lt_two (n := n) hp hp2 lam Lam
    refine ⟨C, δ, hδ, fun ha hell hbmo u G hu hG2 hG => ?_⟩
    have hle := h ha hell hbmo u G hu hG2
    exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hG.eLpNorm_lt_top), hle⟩
  · refine ⟨Real.toNNReal lam⁻¹, 1, one_pos, fun ha hell _ u G hu hG2 _ => ?_⟩
    have hle := eLpNorm_coe_d1p0_le_of_uniformlyEllipticOn ha hell hu hG2
    exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hG2.eLpNorm_lt_top), hle⟩
  · obtain ⟨C, δ, hδ, h⟩ := exists_memLp_and_eLpNorm_le_of_two_lt (n := n) hp2 hp_top lam Lam
    exact ⟨C, δ, hδ, fun ha hell hbmo u G hu _ hG => h ha hell hbmo u G hu hG⟩

end PDE

end TauCeti
