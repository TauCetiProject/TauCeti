/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Analytic.SingularDirection
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Analysis.Polynomial.SimpleRoots.Basic
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Derivative
import TauCeti.RingTheory.Polynomial.Monic.Roots
import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# The Nash Weierstrass preparation and division theorems

Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite,
and suppose that the vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d`
at `t₀`. By the real analytic Weierstrass preparation theorem
(`AnalyticAt.exists_weierstrassPreparation_real`), near `p₀` one has
`f (x, t) = P_x (t - t₀) * u (x, t)` where `P_x = TauCeti.Polynomial.monicOfCoeff (c · x)` is a
monic polynomial of degree `d` with real analytic coefficients vanishing at `x₀` and `u` is a
nonvanishing real analytic unit. This file proves that the coefficient germs `c i` at `x₀` and the
unit germ `u` at `p₀` are in fact *Nash germs* (`TauCeti.IsNashAt.exists_weierstrassPreparation`),
and deduces the Nash Weierstrass division theorems
(`TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff` and
`TauCeti.IsNashAt.exists_weierstrassDivision`) together with general-position linear coordinate
changes (`TauCeti.IsNashAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`).

## Proof outline

1. **Nashness of the preparation coefficients and unit.** Let `F` be a holomorphic extension of `f`
   on an open neighborhood `V` whose realification has semialgebraic domain and graph
   (`TauCeti.IsNashAt.exists_complexification`). Differentiating in the real vertical direction
   shows by induction on `k` that every complex vertical derivative of `F` also has semialgebraic
   real and imaginary parts on `V` (`TauCeti.IsSemialgebraicOn.iteratedDerivInr_scalar`). Shrinking
   to a polydisc `ball x₀ δ × ball t₀ R` inside `V` on which the complexified Weierstrass unit `U`
   is nonvanishing and all `d` complex roots of `P_x` lie in `ball 0 R`, a tuple `c' : Fin d → ℝ`
   equals `fun i ↦ c i x` if and only if there exist `r ≤ d` pairwise distinct points `z l` in
   `ball 0 R` with multiplicities `m l` summing to `d` such that `w ↦ F (x, w)` vanishes to exact
   order `m l` at `t₀ + z l` (characterized by vanishing of the first `m l` vertical derivatives
   and nonvanishing of the `m l`-th) and `c'` gives the coefficients of
   `∏ l, (X - C (z l)) ^ m l`. Eliminating the root coordinates via Tarski–Seidenberg
   (`TauCeti.IsSemialgebraic.setOf_exists_sumElim`) makes the graph of `x ↦ fun i ↦ c i x`
   semialgebraic on `ball x₀ δ`, so each `c i` is Nash at `x₀` by the local Nash graph criterion.
   Exact division of Nash germs (`TauCeti.IsNashAt.of_eventuallyEq_mul_left`) then makes the unit
   `u` Nash at `p₀`.

2. **Nash Weierstrass division.** Rather than repeating root-cluster elimination for Hermite
   interpolation, division by a Nash Weierstrass polynomial `P_x` is deduced from preparation by
   Nirenberg's perturbation argument (Bochnak–Coste–Roy, Proposition 8.2.2): introducing one
   auxiliary real parameter `ε`, the Nash germ `H (x, ε, t) = P_x (t - t₀) - ε * g (x, t)` has
   vertical slice `(t - t₀) ^ d` at `(x₀, 0)`, hence admits a Nash Weierstrass preparation
   `P_{A (x, ε)} (t - t₀) * U (x, ε, t)`. At `ε = 0`, uniqueness of the real Weierstrass
   preparation (`TauCeti.eventuallyEq_of_weierstrassPreparation_sumElim_real`) identifies
   `A (x, 0) = c x` and `U (x, 0, t) = 1`; differentiating the factorization with respect to `ε`
   at `ε = 0` (`TauCeti.IsNashAt.fderiv_apply`) yields
   `g = P_x * (-∂_ε U) + ∑ i, (-∂_ε A_i) * (t - t₀) ^ i` with Nash quotient and remainder
   coefficients.

## Main declarations

* `TauCeti.IsNashAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: general-position linear
  change of coordinates making a non-identically-zero Nash germ regular in the vertical variable.
* `TauCeti.IsNashAt.exists_weierstrassPreparation`: **Nash Weierstrass preparation theorem.**
* `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`,
  `TauCeti.IsNashAt.exists_weierstrassDivision`: **Nash Weierstrass division theorems.**

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Sections 8.1 and 8.2.
* J. M. Ruiz, *The Basic Theory of Power Series*, Advanced Lectures in Mathematics, Vieweg, 1993,
  Chapter III.
* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
-/

public section

open Complex Filter Function Metric MvPolynomial Polynomial Set Topology

namespace TauCeti

/-! ### Linear coordinate changes and general position -/

section LinearCoordinates

variable {σ : Type*} [Fintype σ]

/-- **General position in the vertical variable for Nash germs.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be
a Nash germ at `p` that does not vanish on a neighborhood of `p`. Then there exist a continuous
linear automorphism `L` of `σ ⊕ Unit → ℝ` and coordinates `(x₀, t₀)` with
`L (Sum.elim x₀ (fun _ ↦ t₀)) = p` such that `f ∘ L` is a Nash germ at `Sum.elim x₀ (fun _ ↦ t₀)`
and its vertical slice `t ↦ f (L (Sum.elim x₀ (fun _ ↦ t)))` has finite analytic order at `t₀`. -/
theorem IsNashAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top
    {f : (σ ⊕ Unit → ℝ) → ℝ} {p : σ ⊕ Unit → ℝ} (hf : IsNashAt f p) (hf0 : ¬ f =ᶠ[𝓝 p] 0) :
    ∃ (L : (σ ⊕ Unit → ℝ) ≃L[ℝ] (σ ⊕ Unit → ℝ)) (x₀ : σ → ℝ) (t₀ : ℝ),
      L (Sum.elim x₀ (fun _ ↦ t₀)) = p ∧
      IsNashAt (f ∘ L) (Sum.elim x₀ (fun _ ↦ t₀)) ∧
      analyticOrderAt (fun t ↦ f (L (Sum.elim x₀ (fun _ ↦ t)))) t₀ ≠ ⊤ := by
  let E := ContinuousLinearEquiv.piProdEquivPiSumUnique ℝ σ Unit ℝ
  have han : AnalyticAt ℝ (f ∘ E) (E.symm p) :=
    hf.analyticAt.comp_of_eq (E.analyticAt _) (E.apply_symm_apply p)
  have hne : ¬ (f ∘ E) =ᶠ[𝓝 (E.symm p)] 0 := fun h0 ↦ hf0 <| by
    filter_upwards [E.symm.continuous.continuousAt.eventually h0] with y hy
    simpa [Function.comp_apply] using hy
  obtain ⟨M, ⟨x₀, t₀⟩, hM, hord⟩ := han.exists_continuousLinearEquiv_analyticOrderAt_ne_top hne
  let L := E.symm.trans (M.trans E)
  have hLp : L (Sum.elim x₀ (fun _ ↦ t₀)) = p := by
    have hE : E.symm (Sum.elim x₀ (fun _ ↦ t₀)) = (x₀, t₀) := by simp [E]
    simp only [L, ContinuousLinearEquiv.trans_apply, hE, hM, E.apply_symm_apply]
  refine ⟨L, x₀, t₀, hLp, L.isNashAt_comp_iff.mpr (hLp.symm ▸ hf), ?_⟩
  simpa [L, E, Function.comp_def] using hord

end LinearCoordinates

/-! ### Nash Weierstrass preparation -/

section Preparation

variable {σ : Type*} [Fintype σ]

/-- By the holomorphic identity principle on real points, any holomorphic extension `F` of `f` near
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)` agrees as a germ with the complexified Weierstrass factorization of
`f`. -/
private theorem eventuallyEq_complexification_weierstrassPreparation {d : ℕ}
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} {u : (σ → ℝ) × ℝ → ℝ}
    {V : Set (σ ⊕ Unit → ℂ)} {F : (σ ⊕ Unit → ℂ) → ℂ}
    (hVo : IsOpen V)
    (hz₀V : (fun j : σ ⊕ Unit ↦ Complex.ofReal (Sum.elim x₀ (fun _ : Unit ↦ t₀) j)) ∈ V)
    (hFV : AnalyticOnNhd ℂ F V)
    (hFr : ∀ y : σ ⊕ Unit → ℝ, (fun j ↦ (y j : ℂ)) ∈ V → F (fun j ↦ (y j : ℂ)) = f y)
    {C : Fin d → (σ → ℂ) → ℂ} (hCan : ∀ i, AnalyticAt ℂ (C i) (fun j ↦ (x₀ j : ℂ)))
    (hCc_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun j ↦ (x j : ℂ)) = c i x)
    {rU : ℝ} (hrU : 0 < rU) {U : (σ ⊕ Unit → ℂ) → ℂ}
    (hU : AnalyticOnNhd ℂ U
      (ball (fun j : σ ⊕ Unit ↦ Complex.ofReal (Sum.elim x₀ (fun _ : Unit ↦ t₀) j)) rU))
    (hUr : ∀ y ∈ ball (Sum.elim x₀ (fun _ : Unit ↦ t₀)) rU,
      U (fun j ↦ (y j : ℂ)) = u (y ∘ Sum.inl, y (Sum.inr ())))
    (hfac : ∀ᶠ p in 𝓝 (x₀, t₀), f (Sum.elim p.1 (fun _ ↦ p.2)) =
      (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p) :
    F =ᶠ[𝓝 (fun j : σ ⊕ Unit ↦ Complex.ofReal (Sum.elim x₀ (fun _ : Unit ↦ t₀) j))] fun z ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (z ∘ Sum.inl))).eval
        (z (Sum.inr ()) - (t₀ : ℂ)) * U z := by
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let z₀ : σ ⊕ Unit → ℂ := fun j ↦ (p₀ j : ℂ)
  have hC_sum (i : Fin d) : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ C i (z ∘ Sum.inl)) z₀ := by
    have hproj : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z ∘ Sum.inl) z₀ :=
      analyticAt_pi_iff.mpr fun j ↦
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inl j)).analyticAt z₀
    exact (hCan i).comp_of_eq hproj rfl
  have hRHS_an : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (z ∘ Sum.inl))).eval
        (z (Sum.inr ()) - (t₀ : ℂ)) * U z) z₀ := by
    have hsub : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z (Sum.inr ()) - (t₀ : ℂ)) z₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inr ())).analyticAt z₀)
        |>.fun_sub analyticAt_const
    exact ((Polynomial.analyticAt_eval_monicOfCoeff _).comp
      ((AnalyticAt.pi hC_sum).prod hsub)).fun_mul (hU z₀ (mem_ball_self hrU))
  refine (hFV z₀ hz₀V).eventuallyEq_of_eventually_real hRHS_an ?_
  have hp_real : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ (fun j ↦ (p j : ℂ))) (𝓝 p₀) (𝓝 z₀) :=
    tendsto_pi_nhds.mpr fun j ↦
      Complex.continuous_ofReal.continuousAt.comp ((continuous_apply j).continuousAt)
  have hp_prod : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ (p ∘ Sum.inl, p (Sum.inr ())))
      (𝓝 p₀) (𝓝 (x₀, t₀)) :=
    ((ContinuousLinearEquiv.piProdEquivPiSumUnique ℝ σ Unit ℝ).symm.continuous.tendsto' p₀
      (x₀, t₀) (by simp [p₀])).congr fun _ ↦ by simp
  have hp_inl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, t₀)).comp hp_prod
  filter_upwards [hp_real.eventually (hVo.mem_nhds hz₀V), ball_mem_nhds p₀ hrU,
    hp_prod.eventually hfac, hp_inl.eventually hCc_ev] with p hpV hpU hpf hpC
  have hp_eq : Sum.elim (p ∘ Sum.inl) (fun _ : Unit ↦ p (Sum.inr ())) = p := Sum.elim_comp_inl_inr p
  rw [hp_eq] at hpf
  rw [hFr p hpV, hpf, Complex.ofReal_mul, ← hUr p hpU]
  congr 1
  simp only [Polynomial.eval_monicOfCoeff, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * _) (hpC i).symm

/-- For a Nash germ `f` with real Weierstrass preparation `(c, u)` at `(x₀, t₀)`, there exist an
open set `V`, a holomorphic extension `F` of `f` on `V` with semialgebraic realified graph on `V`,
and radii `R, δ > 0` such that for all `x ∈ ball x₀ δ`, every root of
`monicOfCoeff (fun i ↦ (c i x : ℂ))` lies in `ball 0 R`, and for every `ζ ∈ ball 0 R`,
`Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ t₀ + ζ) ∈ V` and the analytic order of
`w ↦ F (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w))` at `t₀ + ζ` equals the root multiplicity of
`ζ` in `monicOfCoeff (fun i ↦ (c i x : ℂ))`. -/
private theorem exists_polydisc_weierstrass_rootMultiplicity {d : ℕ}
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} {u : (σ → ℝ) × ℝ → ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (x₀, t₀)) (hu0 : u (x₀, t₀) ≠ 0)
    (hfac : ∀ᶠ p in 𝓝 (x₀, t₀), f (Sum.elim p.1 (fun _ ↦ p.2)) =
      (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p) :
    ∃ (V : Set (σ ⊕ Unit → ℂ)) (F : (σ ⊕ Unit → ℂ) → ℂ) (R δ : ℝ),
      IsOpen V ∧ AnalyticOnNhd ℂ F V ∧
      IsSemialgebraicOn
        (fun a ↦ complexToRealPi Unit (fun _ ↦ F ((complexToRealPi (σ ⊕ Unit)).symm a)))
        ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V) ∧
      0 < R ∧ 0 < δ ∧
      (∀ x ∈ ball x₀ δ, ∀ ζ : ℂ, ‖ζ‖ < R →
        Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ (t₀ : ℂ) + ζ) ∈ V ∧
        analyticOrderAt (fun w ↦ F (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w)))
            ((t₀ : ℂ) + ζ) =
          ((Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).rootMultiplicity ζ : ℕ∞)) ∧
      ∀ x ∈ ball x₀ δ, ∀ ζ : ℂ,
        (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).IsRoot ζ → ‖ζ‖ < R := by
  -- Complexify `f`, the coefficients `c i`, and the unit `u`, and match germs near `z₀`.
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let z₀ : σ ⊕ Unit → ℂ := fun j ↦ (p₀ j : ℂ)
  obtain ⟨V, hVo, hz₀V, -, -, -, F, hFV, hFr, -, hFS⟩ := hf.exists_complexification univ_mem
  obtain ⟨C, hC, hCc, -⟩ := exists_complexification_family hc
  have hu_sum : AnalyticAt ℝ (fun p : σ ⊕ Unit → ℝ ↦ u (p ∘ Sum.inl, p (Sum.inr ()))) p₀ := by
    simpa [Function.comp_def] using
      hu.comp_of_eq
        ((ContinuousLinearEquiv.piProdEquivPiSumUnique ℝ σ Unit ℝ).symm.analyticAt p₀)
        (by simp [p₀])
  obtain ⟨rU, hrU, U, hU, hUr, -⟩ := hu_sum.exists_complexification
  have hCc_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun j ↦ (x j : ℂ)) = c i x := eventually_all.mpr hCc
  have hF_eq := eventuallyEq_complexification_weierstrassPreparation hVo hz₀V hFV hFr
    hC hCc_ev hrU hU hUr hfac
  have hUz₀ : U z₀ ≠ 0 := by
    rw [hUr p₀ (mem_ball_self hrU)]
    exact Complex.ofReal_ne_zero.mpr hu0
  -- Choose `R` for the complex polydisc where `U ≠ 0` and `F = P * U`, then `δ` bounding the roots.
  obtain ⟨R, hR, hballZ⟩ := Metric.mem_nhds_iff.mp <|
    inter_mem (inter_mem (hVo.mem_nhds hz₀V) (ball_mem_nhds z₀ hrU)) <|
      inter_mem ((hU z₀ (mem_ball_self hrU)).continuousAt.eventually_ne hUz₀) hF_eq
  have hbound_ev : ∀ᶠ x in 𝓝 x₀, ∀ i : Fin d, ‖(c i x : ℂ)‖ < (R / 3) ^ (d - (i : ℕ)) := by
    refine eventually_all.mpr fun i ↦ ?_
    have hcont : ContinuousAt (fun x ↦ ‖(c i x : ℂ)‖) x₀ :=
      continuous_norm.continuousAt.comp
        (Complex.continuous_ofReal.continuousAt.comp (hc i).continuousAt)
    have hval0 : ‖(c i x₀ : ℂ)‖ = 0 := by simp [hc0]
    exact hcont.eventually
      (hval0.symm ▸ gt_mem_nhds (pow_pos (div_pos hR zero_lt_three) (d - (i : ℕ))))
  obtain ⟨δ, hδ, hballX⟩ := Metric.mem_nhds_iff.mp <|
    inter_mem (ball_mem_nhds x₀ hR) (inter_mem hCc_ev hbound_ev)
  refine ⟨V, F, R, δ, hVo, hFV, hFS, hR, hδ, fun x hx ζ hζ ↦ ?_, fun x hx ζ hroot ↦ ?_⟩
  swap
  · have hle : ‖ζ‖ ≤ 2 * (R / 3) :=
      hroot.norm_le_two_mul (Polynomial.monic_monicOfCoeff _) fun k hk ↦ by
        rw [Polynomial.natDegree_monicOfCoeff] at hk ⊢
        rw [Polynomial.coeff_monicOfCoeff _ ⟨k, hk⟩]
        exact ((hballX hx).2.2 ⟨k, hk⟩).le
    linarith
  -- Compute the vertical slice order at `t₀ + ζ` from the local factorization `F = P * U`.
  have hz_mem (w : ℂ) (hw : w ∈ ball (t₀ : ℂ) R) :
      Sum.elim (fun i ↦ (x i : ℂ)) (fun _ : Unit ↦ w) ∈ ball z₀ R := by
    rw [mem_ball, dist_pi_lt_iff hR]
    rintro (i | ⟨⟩)
    · simpa [z₀, p₀, dist_eq_norm, ← Complex.ofReal_sub] using
        (dist_pi_lt_iff hR).mp (mem_ball.mp (hballX hx).1) i
    · simpa [z₀, p₀] using mem_ball.mp hw
  have hw_ball : (t₀ : ℂ) + ζ ∈ ball (t₀ : ℂ) R := by simpa [dist_eq_norm] using hζ
  have hz₀_pt := hz_mem ((t₀ : ℂ) + ζ) hw_ball
  refine ⟨(hballZ hz₀_pt).1.1, ?_⟩
  let P : ℂ[X] := Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))
  have hCP : (fun i ↦ C i (fun j ↦ (x j : ℂ))) = fun i ↦ (c i x : ℂ) := funext (hballX hx).2.1
  have hslice_eq : (fun w ↦ F (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w))) =ᶠ[𝓝 ((t₀ : ℂ) + ζ)]
      fun w ↦ P.eval (w - (t₀ : ℂ)) * U (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w)) := by
    filter_upwards [isOpen_ball.mem_nhds hw_ball] with w hw
    have hmem : F (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w)) = _ := (hballZ (hz_mem w hw)).2.2
    simpa only [Sum.elim_comp_inl, Sum.elim_inr, hCP, P] using hmem
  have hU_slice_an : AnalyticAt ℂ
      (fun w ↦ U (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w))) ((t₀ : ℂ) + ζ) :=
    (hU _ (hballZ hz₀_pt).1.2).comp_of_eq (analyticAt_sumElim_const _ _) rfl
  rw [analyticOrderAt_congr hslice_eq]
  simpa only [add_sub_cancel_left] using
    Polynomial.analyticOrderAt_eval_sub_mul_of_ne_zero (Polynomial.monic_monicOfCoeff _).ne_zero
      (t₀ : ℂ) hU_slice_an (hballZ hz₀_pt).2.1

/-- The locus where `r` complex coordinates encoded as real and imaginary parts are pairwise
distinct is semialgebraic. -/
private theorem isSemialgebraic_rootCluster_pairwise_ne {α : Type*} {r : ℕ} :
    let ν := α ⊕ (Fin r ⊕ Fin r)
    IsSemialgebraic {v : ν → ℝ | ∀ l l' : Fin r, l ≠ l' →
      (v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I ≠
        (v (.inr (.inl l')) : ℂ) + (v (.inr (.inr l')) : ℂ) * Complex.I} := by
  intro ν
  let Z : Fin r → MvPolynomial ν ℂ := fun l ↦
    MvPolynomial.X (.inr (.inl l)) + MvPolynomial.X (.inr (.inr l)) * MvPolynomial.C Complex.I
  let Spair (l l' : Fin r) : Set (ν → ℝ) :=
    if l ≠ l' then {v | MvPolynomial.eval (fun s ↦ (v s : ℂ)) (Z l - Z l') = 0}ᶜ else univ
  have hSpair (l l' : Fin r) : IsSemialgebraic (Spair l l') := by
    dsimp only [Spair]
    split_ifs
    · exact (isSemialgebraic_setOf_eval_ofReal_eq_zero (Z l - Z l')).compl
    · exact isSemialgebraic_univ
  convert IsSemialgebraic.iInter (fun l ↦ IsSemialgebraic.iInter fun l' ↦ hSpair l l') using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Spair]
  refine forall_congr' fun l ↦ forall_congr' fun l' ↦ ?_
  by_cases hll : l ≠ l' <;> simp [hll, Z, sub_eq_zero]

omit [Fintype σ] in
/-- The locus where `d` real polynomial-coefficient variables match the lower coefficients of
`∏ l, (X - C (z l)) ^ (m l : ℕ)` for complex roots `z l` encoded as real and imaginary parts is
semialgebraic. -/
private theorem isSemialgebraic_rootCluster_coeff {d r : ℕ} (m : Fin r → ℕ) :
    let ν := (σ ⊕ Fin d) ⊕ (Fin r ⊕ Fin r)
    IsSemialgebraic {v : ν → ℝ | ∀ i : Fin d, (v (.inl (.inr i)) : ℂ) =
      (∏ l : Fin r,
        (Polynomial.X - Polynomial.C
          ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I)) ^ m l).coeff
        (i : ℕ)} := by
  intro ν
  let Z : Fin r → MvPolynomial ν ℂ := fun l ↦
    MvPolynomial.X (.inr (.inl l)) + MvPolynomial.X (.inr (.inr l)) * MvPolynomial.C Complex.I
  let Qpoly : Polynomial (MvPolynomial ν ℂ) :=
    ∏ l : Fin r, (Polynomial.X - Polynomial.C (Z l)) ^ m l
  convert IsSemialgebraic.iInter (fun i : Fin d ↦
    isSemialgebraic_setOf_eval_ofReal_eq_zero
      (MvPolynomial.X (.inl (.inr i)) - Qpoly.coeff (i : ℕ))) using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, map_sub, MvPolynomial.eval_X, sub_eq_zero]
  refine forall_congr' fun i ↦ Eq.congr_right ?_
  have hmap : Qpoly.map (MvPolynomial.eval fun s ↦ (v s : ℂ)) =
      ∏ l : Fin r, (Polynomial.X - Polynomial.C
        ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I)) ^ m l := by
    simp [Qpoly, Z, Polynomial.map_prod]
  simpa only [Polynomial.coeff_map] using
    (congrArg (fun p : ℂ[X] ↦ p.coeff (i : ℕ)) hmap).symm

/-- On `ball x₀ δ`, each fixed root-cluster shape `(r, m)` defines a semialgebraic relation on
`(x, c')` after projecting out the `r` complex root coordinates. -/
private theorem isSemialgebraic_rootCluster_branch {d : ℕ} {V : Set (σ ⊕ Unit → ℂ)}
    {F : (σ ⊕ Unit → ℂ) → ℂ} (hVo : IsOpen V) (hFV : AnalyticOnNhd ℂ F V)
    (hFS : IsSemialgebraicOn
      (fun a ↦ complexToRealPi Unit (fun _ ↦ F ((complexToRealPi (σ ⊕ Unit)).symm a)))
      ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V))
    (x₀ : σ → ℝ) (t₀ R δ : ℝ) (r : ℕ) (m : Fin r → ℕ) :
    IsSemialgebraic {w : σ ⊕ Fin d → ℝ |
      w ∘ Sum.inl ∈ ball x₀ δ ∧
      ∃ y : Fin r ⊕ Fin r → ℝ,
        let z : Fin r → ℂ := fun l ↦ (y (.inl l) : ℂ) + (y (.inr l) : ℂ) * Complex.I
        (∀ l, (y (.inl l)) ^ 2 + (y (.inr l)) ^ 2 < R ^ 2) ∧
        (∀ l l', l ≠ l' → z l ≠ z l') ∧
        (∀ l,
          Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l) ∈ V ∧
          (∀ k : Fin (m l), iteratedDerivInr k F
            (Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l)) = 0) ∧
          iteratedDerivInr (m l) F
            (Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l)) ≠ 0) ∧
        ∀ i : Fin d, (w (.inr i) : ℂ) =
          (∏ l, (Polynomial.X - Polynomial.C (z l)) ^ m l).coeff (i : ℕ)} := by
  let ν := (σ ⊕ Fin d) ⊕ (Fin r ⊕ Fin r)
  let xP : σ → MvPolynomial ν ℝ := fun i ↦ MvPolynomial.X (.inl (.inl i))
  let zRe : Fin r → MvPolynomial ν ℝ := fun l ↦ MvPolynomial.X (.inr (.inl l))
  let zIm : Fin r → MvPolynomial ν ℝ := fun l ↦ MvPolynomial.X (.inr (.inr l))
  have hS_norm : IsSemialgebraic {v : ν → ℝ |
      ∀ l, (v (.inr (.inl l))) ^ 2 + (v (.inr (.inr l))) ^ 2 < R ^ 2} := by
    convert IsSemialgebraic.iInter (fun l : Fin r ↦
      isSemialgebraic_eval_lt (zRe l ^ 2 + zIm l ^ 2) (MvPolynomial.C (R ^ 2))) using 1
    ext v
    simp [zRe, zIm]
  let pIn (l : Fin r) : (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → MvPolynomial ν ℝ :=
    Sum.elim (Sum.elim xP (fun _ ↦ MvPolynomial.C t₀ + zRe l))
      (Sum.elim (fun _ ↦ 0) (fun _ ↦ zIm l))
  have hpIn (l : Fin r) (v : ν → ℝ) :
      (complexToRealPi (σ ⊕ Unit)).symm (fun s ↦ MvPolynomial.eval v (pIn l s)) =
        Sum.elim (fun i ↦ (v (.inl (.inl i)) : ℂ))
          (fun _ ↦ (t₀ : ℂ) + ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I)) := by
    ext (i | ⟨⟩) <;> simp [pIn, xP, zRe, zIm, add_assoc]
  have h_eq (l : Fin r) (k : ℕ) :
      IsSemialgebraic {v : ν → ℝ |
        let pt := Sum.elim (fun i ↦ (v (.inl (.inl i)) : ℂ))
          (fun _ ↦ (t₀ : ℂ) + ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I))
        pt ∈ V ∧ iteratedDerivInr k F pt = 0} := by
    convert ((hFS.iteratedDerivInr_scalar hVo hFV k).isSemialgebraic_inter_setOf_eq_const
      0).preimage_eval (pIn l) using 1
    ext v
    simp [hpIn, Complex.ext_iff, funext_iff]
  have h_ne (l : Fin r) (k : ℕ) :
      IsSemialgebraic {v : ν → ℝ |
        let pt := Sum.elim (fun i ↦ (v (.inl (.inl i)) : ℂ))
          (fun _ ↦ (t₀ : ℂ) + ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I))
        pt ∈ V ∧ iteratedDerivInr k F pt ≠ 0} := by
    convert ((hFS.iteratedDerivInr_scalar hVo hFV k).isSemialgebraic_inter_setOf_ne_const
      0).preimage_eval (pIn l) using 1
    ext v
    simp [hpIn, Complex.ext_iff, funext_iff]
  have hS_mult : IsSemialgebraic {v : ν → ℝ | ∀ l : Fin r,
      let pt := Sum.elim (fun i ↦ (v (.inl (.inl i)) : ℂ))
        (fun _ ↦ (t₀ : ℂ) + ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I))
      pt ∈ V ∧ (∀ k : Fin (m l), iteratedDerivInr k F pt = 0) ∧
        iteratedDerivInr (m l) F pt ≠ 0} := by
    convert IsSemialgebraic.iInter (fun l : Fin r ↦
      (IsSemialgebraic.iInter fun k : Fin (m l) ↦ h_eq l k).inter (h_ne l (m l))) using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
    refine forall_congr' fun _ ↦ ?_
    exact ⟨fun ⟨hV, hk0, hkne⟩ ↦ ⟨fun k ↦ ⟨hV, hk0 k⟩, hV, hkne⟩,
      fun ⟨hk0, hV, hkne⟩ ↦ ⟨hV, fun k ↦ (hk0 k).2, hkne⟩⟩
  have hproj := (((hS_norm.inter
      (isSemialgebraic_rootCluster_pairwise_ne (α := σ ⊕ Fin d) (r := r))).inter hS_mult).inter
    (isSemialgebraic_rootCluster_coeff (σ := σ) (d := d) m)).setOf_exists_sumElim
  convert ((isSemialgebraic_ball x₀ δ).preimage_comp Sum.inl).inter hproj using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨fun ⟨hx, y, hy⟩ ↦ ⟨hx, y, ⟨⟨⟨hy.1, hy.2.1⟩, hy.2.2.1⟩, hy.2.2.2⟩⟩,
    fun ⟨hx, y, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩ ↦ ⟨hx, y, h1, h2, h3, h4⟩⟩

/-- The lower coefficients of the real analytic Weierstrass preparation of a Nash germ are Nash
germs. -/
private theorem isNashAt_weierstrassPreparation_coeff {d : ℕ}
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} {u : (σ → ℝ) × ℝ → ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (x₀, t₀)) (hu0 : u (x₀, t₀) ≠ 0)
    (hfac : ∀ᶠ p in 𝓝 (x₀, t₀), f (Sum.elim p.1 (fun _ ↦ p.2)) =
      (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p) (i : Fin d) :
    IsNashAt (c i) x₀ := by
  -- Express the graph of `c` on `ball x₀ δ` as a finite union over root-cluster shapes `(r, m)`.
  obtain ⟨V, F, R, δ, hVo, hFV, hFS, hR, hδ, hord, hroots⟩ :=
    exists_polydisc_weierstrass_rootMultiplicity hf hc hc0 hu hu0 hfac
  refine (forall_isNashAt_apply_iff_exists_isSemialgebraicOn (g := fun x j ↦ c j x)).mpr
    ⟨AnalyticAt.pi hc, ball x₀ δ, isOpen_ball, mem_ball_self hδ, ?_⟩ i
  refine isSemialgebraicOn_def.mpr ⟨isSemialgebraic_ball x₀ δ, ?_⟩
  convert IsSemialgebraic.iUnion (fun r : Fin (d + 1) ↦
    IsSemialgebraic.iUnion fun m : {m : Fin (r : ℕ) → Fin (d + 1) // ∑ l, (m l : ℕ) = d} ↦
      isSemialgebraic_rootCluster_branch hVo hFV hFS x₀ t₀ R δ r (fun l ↦ (m.val l : ℕ))) using 1
  ext w
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_iUnion, mem_ofPred_eq]
  let x := w ∘ Sum.inl
  let P : ℂ[X] := Polynomial.monicOfCoeff (fun j ↦ (c j x : ℂ))
  have hP_monic : P.Monic := Polynomial.monic_monicOfCoeff _
  have hP_coeff (j : Fin d) : P.coeff (j : ℕ) = (c j x : ℂ) := Polynomial.coeff_monicOfCoeff _ j
  have hnorm (z : ℂ) : ‖z‖ < R ↔ z.re ^ 2 + z.im ^ 2 < R ^ 2 := by
    rw [← sq_lt_sq₀ (norm_nonneg z) hR.le, Complex.sq_norm, Complex.normSq_apply]
    simp only [sq]
  constructor
  · -- Forward direction: factor `P` over `ℂ` into distinct roots inside `ball 0 R`.
    rintro ⟨hx, hcx⟩
    obtain ⟨r, z, m, hm_pos, hm_sum, hz_root, hz_inj, hmult, hprod⟩ :=
      hP_monic.exists_eq_prod_X_sub_C_pow_rootMultiplicity (IsAlgClosed.splits P)
    rw [Polynomial.natDegree_monicOfCoeff] at hm_sum
    have hr_le : r ≤ d := calc
      r = ∑ _ : Fin r, 1 := by simp
      _ ≤ ∑ l, m l := Finset.sum_le_sum fun l _ ↦ hm_pos l
      _ = d := hm_sum
    have hm_le (l : Fin r) : m l ≤ d :=
      hm_sum ▸ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)
    let r' : Fin (d + 1) := ⟨r, Nat.lt_succ_of_le hr_le⟩
    let m' : {m : Fin (r' : ℕ) → Fin (d + 1) // ∑ l, (m l : ℕ) = d} :=
      ⟨fun l ↦ ⟨m l, Nat.lt_succ_of_le (hm_le l)⟩, hm_sum⟩
    refine ⟨r', m', hx, Sum.elim (fun l ↦ (z l).re) (fun l ↦ (z l).im), ?_, ?_, ?_, ?_⟩
    · intro l
      simpa using (hnorm (z l)).mp (hroots x hx (z l) (hz_root l))
    · intro l l' hne
      simpa [Complex.re_add_im] using hz_inj.ne hne
    · intro l
      obtain ⟨hptV, hord_eq⟩ := hord x hx (z l) (hroots x hx (z l) (hz_root l))
      simp only [Sum.elim_inl, Sum.elim_inr, Complex.re_add_im]
      have hord' := ((hFV _ hptV).analyticOrderAt_sumElim_eq_nat_iff (m l)).mp
        (hord_eq.trans (congrArg Nat.cast (hmult l)))
      exact ⟨hptV, fun k ↦ hord'.1 k k.isLt, hord'.2⟩
    · intro j
      have hcj : w (.inr j) = c j x := (congrFun hcx j).symm
      rw [hcj, ← hP_coeff j, ← hprod]
      simp [Complex.re_add_im, m', r']
  · -- Reverse direction: recover `P` from `d` roots counted with vertical-slice multiplicity.
    rintro ⟨r, m, hx, y, hyR, hpair, hderiv, hcoeff⟩
    refine ⟨hx, ?_⟩
    let z : Fin (r : ℕ) → ℂ := fun l ↦ (y (.inl l) : ℂ) + (y (.inr l) : ℂ) * Complex.I
    have hzR (l : Fin (r : ℕ)) : ‖z l‖ < R :=
      (hnorm (z l)).mpr (by simpa [z] using hyR l)
    have hmult (l : Fin (r : ℕ)) : P.rootMultiplicity (z l) = (m.val l : ℕ) := by
      obtain ⟨hptV, hk0, hkne⟩ := hderiv l
      obtain ⟨-, hord_eq⟩ := hord x hx (z l) (hzR l)
      exact Nat.cast_injective (R := ℕ∞) <| hord_eq.symm.trans <|
        ((hFV _ hptV).analyticOrderAt_sumElim_eq_nat_iff (m.val l : ℕ)).mpr
          ⟨fun k hk ↦ hk0 ⟨k, hk⟩, hkne⟩
    have hP_eq := hP_monic.eq_prod_X_sub_C_pow_of_le_rootMultiplicity (z := z)
      (m := fun l ↦ (m.val l : ℕ)) (by rw [Polynomial.natDegree_monicOfCoeff, m.property])
      (fun _ _ h ↦ by_contra fun hne ↦ hpair _ _ hne h) (fun l ↦ (hmult l).ge)
    funext j
    apply Complex.ofReal_injective
    rw [← hP_coeff j, hP_eq]
    exact (hcoeff j).symm

/-- **Nash Weierstrass preparation theorem.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d` at `t₀`. Then there exist Nash
coefficient germs `c : Fin d → (σ → ℝ) → ℝ` at `x₀` vanishing at `x₀` and a Nash germ `u` at
`Sum.elim x₀ (fun _ ↦ t₀)` nonvanishing there such that near `Sum.elim x₀ (fun _ ↦ t₀)`,
`f p = (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p`. -/
theorem IsNashAt.exists_weierstrassPreparation {f : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (c : Fin d → (σ → ℝ) → ℝ) (u : (σ ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) ∧ u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0 ∧
      f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p := by
  let E := ContinuousLinearEquiv.piProdEquivPiSumUnique ℝ σ Unit ℝ
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  have hf_prod : AnalyticAt ℝ (f ∘ E) (x₀, t₀) :=
    hf.analyticAt.comp_of_eq (E.analyticAt (x₀, t₀)) (by simp [E])
  have hd_prod : analyticOrderAt (fun t ↦ (f ∘ E) (x₀, t)) t₀ = d := by
    simpa [E, Function.comp_def] using hd
  obtain ⟨c, u₀, hc_an, hc0, hu₀_an, hu₀_ne, hfac_prod⟩ :=
    hf_prod.exists_weierstrassPreparation_real hd_prod
  have hc_nash (i : Fin d) : IsNashAt (c i) x₀ :=
    isNashAt_weierstrassPreparation_coeff hf hc_an hc0 hu₀_an hu₀_ne
      (hfac_prod.mono fun q hq ↦ by simpa [E, Function.comp_def] using hq) i
  let u : (σ ⊕ Unit → ℝ) → ℝ := fun p ↦ u₀ (E.symm p)
  have hu_an : AnalyticAt ℝ u p₀ :=
    hu₀_an.comp_of_eq (E.symm.analyticAt p₀) (by simp [E, p₀])
  have hu_ne : u p₀ ≠ 0 := by simpa [u, E, p₀] using hu₀_ne
  have hfac : f =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p := by
    filter_upwards [(E.symm.continuous.tendsto' p₀ (x₀, t₀) (by simp [E, p₀])).eventually hfac_prod]
      with p hp
    rw [Function.comp_apply, E.apply_symm_apply] at hp
    simpa [u, E] using hp
  have hP_nash : IsNashAt
      (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀)) p₀ :=
    IsNashAt.eval_monicOfCoeff
      (fun i ↦ (hc_nash i).comp fun j ↦ isNashAt_apply (σ := σ ⊕ Unit) (.inl j))
      ((isNashAt_apply (σ := σ ⊕ Unit) (.inr ())).fun_sub (isNashAt_const t₀))
  have hP_ne0 : ¬ (fun p : σ ⊕ Unit → ℝ ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀)) =ᶠ[𝓝 p₀]
      0 := by
    intro h0
    have hline : Tendsto (fun t : ℝ ↦ Sum.elim x₀ (fun _ : Unit ↦ t)) (𝓝 t₀) (𝓝 p₀) :=
      tendsto_pi_nhds.mpr fun j ↦ by cases j <;> [exact tendsto_const_nhds; exact tendsto_id]
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hline.eventually h0)
    have hs_mem : t₀ + δ / 2 ∈ ball t₀ δ := by
      rw [mem_ball, dist_self_add_left, Real.norm_of_nonneg (by positivity)]
      linarith
    have hpow : (δ / 2) ^ d = 0 := by
      simpa [Polynomial.eval_monicOfCoeff, hc0] using hball hs_mem
    exact pow_ne_zero d (by positivity) hpow
  exact ⟨c, u, hc_nash, hc0, hf.of_eventuallyEq_mul_left hP_nash hP_ne0 hu_an hfac, hu_ne, hfac⟩

end Preparation

/-! ### Nash Weierstrass division -/

section Division

variable {σ : Type*} [Fintype σ]

/-- Continuous linear map embedding `x : σ → ℝ` at `ε = 0` into `σ ⊕ Unit → ℝ`. -/
private def embedZero (σ : Type*) : (σ → ℝ) →L[ℝ] (σ ⊕ Unit → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ match j with
    | .inl i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) i
    | .inr _ => 0

@[simp]
private theorem embedZero_apply {σ : Type*} (x : σ → ℝ) :
    embedZero σ x = Sum.elim x (fun _ ↦ 0) := by
  ext (i | ⟨⟩) <;> simp [embedZero]

/-- Continuous linear map embedding `(x, t) : σ ⊕ Unit → ℝ` at `ε = 0` into
`(σ ⊕ Unit) ⊕ Unit → ℝ`. -/
private def embedZeroProd (σ : Type*) : (σ ⊕ Unit → ℝ) →L[ℝ] ((σ ⊕ Unit) ⊕ Unit → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ match j with
    | .inl (.inl i) => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (.inl i)
    | .inl (.inr _) => 0
    | .inr _ => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (.inr ())

@[simp]
private theorem embedZeroProd_apply {σ : Type*} (p : σ ⊕ Unit → ℝ) :
    embedZeroProd σ p =
      Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (fun _ ↦ p (Sum.inr ())) := by
  ext ((i | ⟨⟩) | ⟨⟩) <;> simp [embedZeroProd]

/-- Continuous linear projection forgetting the perturbation coordinate `ε` from
`((σ ⊕ Unit) ⊕ Unit) → ℝ` to `σ ⊕ Unit → ℝ`. -/
private def projDropMiddle (σ : Type*) : ((σ ⊕ Unit) ⊕ Unit → ℝ) →L[ℝ] (σ ⊕ Unit → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ match j with
    | .inl i =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (σ ⊕ Unit) ⊕ Unit ↦ ℝ) (.inl (.inl i))
    | .inr _ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (σ ⊕ Unit) ⊕ Unit ↦ ℝ) (.inr ())

@[simp]
private theorem projDropMiddle_apply {σ : Type*} (q : (σ ⊕ Unit) ⊕ Unit → ℝ) :
    projDropMiddle σ q = Sum.elim ((q ∘ Sum.inl) ∘ Sum.inl) (fun _ ↦ q (Sum.inr ())) := by
  ext (i | ⟨⟩) <;> simp [projDropMiddle]

omit [Fintype σ] in
/-- Differentiating the perturbed preparation
`P_x (t - t₀) - ε * g (x, t) = P_{A (x, ε)} (t - t₀) * U (x, ε, t)` with respect to `ε` at `ε = 0`,
where `A (x, 0) = c x` and `U (x, 0, t) = 1`, yields the Weierstrass division identity for `g`. -/
private theorem weierstrassDivision_eq_of_perturbed_preparation [Finite σ] {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g : (σ ⊕ Unit → ℝ) → ℝ}
    {A : Fin d → ((σ ⊕ Unit) → ℝ) → ℝ} {U : ((σ ⊕ Unit) ⊕ Unit → ℝ) → ℝ}
    {p : σ ⊕ Unit → ℝ} {t₀ : ℝ}
    (hA_diff : ∀ i, DifferentiableAt ℝ (A i) (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)))
    (hU_diff : DifferentiableAt ℝ U
      (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (fun _ ↦ p (Sum.inr ()))))
    (hA0 : ∀ i, A i (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) = c i (p ∘ Sum.inl))
    (hU0 : U (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (fun _ ↦ p (Sum.inr ()))) = 1)
    (heq : ∀ᶠ s in 𝓝 (0 : ℝ),
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) - s * g p =
        (Polynomial.monicOfCoeff
          (fun i ↦ A i (Sum.elim (p ∘ Sum.inl) (fun _ ↦ s)))).eval (p (Sum.inr ()) - t₀) *
          U (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ s)) (fun _ ↦ p (Sum.inr ())))) :
    g p =
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) *
        (- fderiv ℝ U
          (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (fun _ ↦ p (Sum.inr ())))
          (Sum.elim (Sum.elim 0 (fun _ ↦ 1)) (fun _ ↦ 0))) +
      ∑ i : Fin d,
        (- fderiv ℝ (A i) (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (Sum.elim 0 (fun _ ↦ 1))) *
          (p (Sum.inr ()) - t₀) ^ (i : ℕ) := by
  let _ := Fintype.ofFinite σ
  let x := p ∘ Sum.inl
  let t := p (Sum.inr ())
  let vA : σ ⊕ Unit → ℝ := Sum.elim 0 (fun _ ↦ 1)
  let vU : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim vA (fun _ ↦ 0)
  let y₀ : σ ⊕ Unit → ℝ := Sum.elim x (fun _ ↦ 0)
  let q₀ : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim y₀ (fun _ ↦ t)
  -- Derivatives along the `ε`-parameter lines at `ε = 0`.
  have hlineA : HasDerivAt (fun s : ℝ ↦ Sum.elim x (fun _ : Unit ↦ s)) vA 0 := by
    have h1 : (fun s : ℝ ↦ Sum.elim x (fun _ : Unit ↦ s)) = fun s ↦ y₀ + s • vA := by
      ext s (i | ⟨⟩) <;> simp [y₀, vA]
    rw [h1]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const vA).const_add y₀
  have hlineU : HasDerivAt (fun s : ℝ ↦ Sum.elim (Sum.elim x (fun _ : Unit ↦ s)) (fun _ ↦ t))
      vU 0 := by
    have h1 : (fun s : ℝ ↦ Sum.elim (Sum.elim x (fun _ : Unit ↦ s)) (fun _ : Unit ↦ t)) =
        fun s ↦ q₀ + s • vU := by
      ext s ((i | ⟨⟩) | ⟨⟩) <;> simp [q₀, y₀, vU, vA]
    rw [h1]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const vU).const_add q₀
  -- Differentiate both sides of the perturbed preparation identity at `s = 0`.
  have hd_lhs : HasDerivAt
      (fun s : ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) - s * g p)
      (- g p) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (g p)).const_sub
      ((Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀))
  have hd_P : HasDerivAt
      (fun s : ℝ ↦ (Polynomial.monicOfCoeff
        (fun i ↦ A i (Sum.elim x (fun _ ↦ s)))).eval (t - t₀))
      (∑ i : Fin d, fderiv ℝ (A i) y₀ vA * (t - t₀) ^ (i : ℕ)) 0 := by
    simp_rw [Polynomial.eval_monicOfCoeff]
    exact (HasDerivAt.fun_sum fun i _ ↦
      (((hA_diff i).hasFDerivAt.comp_hasDerivAt 0 hlineA).mul_const
        ((t - t₀) ^ (i : ℕ)))).const_add ((t - t₀) ^ d)
  have hd_U : HasDerivAt
      (fun s : ℝ ↦ U (Sum.elim (Sum.elim x (fun _ ↦ s)) (fun _ ↦ t)))
      (fderiv ℝ U q₀ vU) 0 :=
    hU_diff.hasFDerivAt.comp_hasDerivAt 0 hlineU
  have heq_deriv := (hd_lhs.congr_of_eventuallyEq (heq.mono fun _ hs ↦ hs.symm)).unique
    (hd_P.mul hd_U)
  have hP0_eq : (Polynomial.monicOfCoeff (fun i ↦ A i y₀)).eval (t - t₀) =
      (Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) := by
    simp [y₀, x, hA0]
  rw [hU0, hP0_eq, mul_one] at heq_deriv
  have hgp := neg_eq_iff_eq_neg.mp heq_deriv
  rw [hgp, neg_add, add_comm, ← Finset.sum_neg_distrib]
  simp only [mul_neg, neg_mul, x, t, y₀, q₀, vA, vU]

/-- From a real analytic Weierstrass preparation `(A, U)` of the perturbed germ
`P_x (t - t₀) - ε * g (x, t)`, uniqueness at `ε = 0` identifies `A (x, 0) = c x` and
`U (x, 0, t) = 1`, and differentiating in `ε` at `0` produces the germ-level Weierstrass division
identity for `g`. -/
private theorem weierstrassDivision_eventuallyEq_of_perturbed_preparation {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {A : Fin d → ((σ ⊕ Unit) → ℝ) → ℝ} {U : ((σ ⊕ Unit) ⊕ Unit → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hA : ∀ i, AnalyticAt ℝ (A i) (Sum.elim x₀ (fun _ ↦ 0)))
    (hU : AnalyticAt ℝ U (Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀)))
    (hU0 : U (Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀)) ≠ 0)
    (hH_prep : (fun q : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i ((q ∘ Sum.inl) ∘ Sum.inl))).eval
          (q (Sum.inr ()) - t₀) - q (.inl (.inr ())) * g (projDropMiddle σ q))
        =ᶠ[𝓝 (Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀))]
      fun q ↦ (Polynomial.monicOfCoeff (fun i ↦ A i (q ∘ Sum.inl))).eval
        (q (Sum.inr ()) - t₀) * U q) :
    g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) *
        (- fderiv ℝ U (embedZeroProd σ p) (Sum.elim (Sum.elim 0 (fun _ ↦ 1)) (fun _ ↦ 0))) +
      ∑ i : Fin d,
        (- fderiv ℝ (A i) (embedZero σ (p ∘ Sum.inl)) (Sum.elim 0 (fun _ ↦ 1))) *
          (p (Sum.inr ()) - t₀) ^ (i : ℕ) := by
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let y₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ 0)
  let q₀ : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim y₀ (fun _ ↦ t₀)
  let ιY := embedZero σ
  let ιQ := embedZeroProd σ
  have hιY_x₀ : ιY x₀ = y₀ := by simp [ιY, y₀]
  have hιQ_p₀ : ιQ p₀ = q₀ := by simp [ιQ, p₀, q₀, y₀]
  have hιQ_tendsto : Tendsto ιQ (𝓝 p₀) (𝓝 q₀) := ιQ.continuous.tendsto' p₀ q₀ hιQ_p₀
  -- Restrict to `ε = 0` and apply uniqueness of real Weierstrass preparation.
  have hslice0 : (fun p : σ ⊕ Unit → ℝ ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * 1)
      =ᶠ[𝓝 p₀]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ A i (ιY (p ∘ Sum.inl)))).eval
        (p (Sum.inr ()) - t₀) * U (ιQ p) := by
    filter_upwards [hιQ_tendsto.eventually hH_prep] with p hp
    simpa [ιQ, ιY] using hp
  obtain ⟨hcA, h1U⟩ := eventuallyEq_of_weierstrassPreparation_sumElim_real
    hc hc0 analyticAt_const
    (fun i ↦ (hA i).comp_of_eq (ιY.analyticAt x₀) hιY_x₀)
    (hU.comp_of_eq (ιQ.analyticAt p₀) hιQ_p₀) (by simpa [ιQ] using hU0) hslice0
  -- Differentiate the perturbed preparation at `ε = 0` at every point near `p₀`.
  have hinl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_pi fun i : σ ↦ continuous_apply (Sum.inl i)).tendsto' p₀ x₀ (by simp [p₀])
  have hιY_p : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ ιY (p ∘ Sum.inl)) (𝓝 p₀) (𝓝 y₀) :=
    (ιY.continuous.tendsto' x₀ y₀ hιY_x₀).comp hinl
  filter_upwards [
    hιY_p.eventually (eventually_all.mpr fun i ↦ (hA i).eventually_analyticAt),
    hιQ_tendsto.eventually hU.eventually_analyticAt,
    hinl.eventually (eventually_all.mpr fun i ↦ (hcA i).symm),
    h1U.symm,
    hιQ_tendsto.eventually hH_prep.eventually_nhds] with p hAd hUd hAc hU1 hHp
  have hline_cont : Continuous (fun s : ℝ ↦
      Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ : Unit ↦ s)) (fun _ : Unit ↦ p (Sum.inr ()))) :=
    continuous_pi fun j ↦ by
      rcases j with (i | ⟨⟩) | ⟨⟩ <;>
        [exact continuous_const; exact continuous_id; exact continuous_const]
  have hline_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) - s * g p =
        (Polynomial.monicOfCoeff
          (fun i ↦ A i (Sum.elim (p ∘ Sum.inl) (fun _ ↦ s)))).eval (p (Sum.inr ()) - t₀) *
          U (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ s)) (fun _ ↦ p (Sum.inr ()))) := by
    filter_upwards [(hline_cont.tendsto' 0 (ιQ p) (by simp [ιQ])).eventually hHp] with s hs
    have hdrop : projDropMiddle σ
        (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ : Unit ↦ s)) (fun _ : Unit ↦ p (Sum.inr ()))) =
        p := by
      rw [projDropMiddle_apply, Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_inr]
      exact Sum.elim_comp_inl_inr p
    simpa only [hdrop, Sum.elim_comp_inl, Sum.elim_inl, Sum.elim_inr] using hs
  simpa [ιQ, ιY] using weierstrassDivision_eq_of_perturbed_preparation
    (fun i ↦ by simpa [ιY] using (hAd i).differentiableAt)
    (by simpa [ιQ] using hUd.differentiableAt) (by simpa [ιY] using hAc)
    (by simpa [ιQ] using hU1) hline_ev

/-- **Nash Weierstrass division by a Nash Weierstrass polynomial.** Let `c : Fin d → (σ → ℝ) → ℝ`
be Nash germs at `x₀` vanishing at `x₀`, with `σ` finite, and let `g : (σ ⊕ Unit → ℝ) → ℝ` be a
Nash germ at `Sum.elim x₀ (fun _ ↦ t₀)`. Then there exist a Nash germ `q` at
`Sum.elim x₀ (fun _ ↦ t₀)` and Nash germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near
`Sum.elim x₀ (fun _ ↦ t₀)`,
`g p = (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
  ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision_monicOfCoeff {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀))) (hc : ∀ i, IsNashAt (c i) x₀)
    (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ) := by
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let y₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ 0)
  let q₀ : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim y₀ (fun _ ↦ t₀)
  let πH := projDropMiddle σ
  let H : ((σ ⊕ Unit) ⊕ Unit → ℝ) → ℝ := fun q ↦
    (Polynomial.monicOfCoeff (fun i ↦ c i ((q ∘ Sum.inl) ∘ Sum.inl))).eval (q (Sum.inr ()) - t₀) -
      q (.inl (.inr ())) * g (πH q)
  have hπH_q₀ : πH q₀ = Sum.elim x₀ (fun _ ↦ t₀) := by simp [πH, q₀, y₀]
  have hH_nash : IsNashAt H q₀ := by
    have hP : IsNashAt (fun q : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i ((q ∘ Sum.inl) ∘ Sum.inl))).eval
          (q (Sum.inr ()) - t₀)) q₀ :=
      IsNashAt.eval_monicOfCoeff
        (fun i ↦ (hc i).comp fun j ↦ isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inl (.inl j)))
        ((isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inr ())).fun_sub (isNashAt_const t₀))
    have hg_comp : IsNashAt (g ∘ πH) q₀ := (hπH_q₀.symm ▸ hg).comp_continuousLinearMap
    exact hP.fun_sub ((isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inl (.inr ()))).fun_mul hg_comp)
  have hH_ord : analyticOrderAt (fun t ↦ H (Sum.elim y₀ (fun _ ↦ t))) t₀ = d := by
    have hslice : (fun t : ℝ ↦ H (Sum.elim y₀ (fun _ ↦ t))) =
        fun t ↦ ((Polynomial.X - Polynomial.C t₀) ^ d).eval t := by
      funext t
      simp [H, y₀, Polynomial.eval_monicOfCoeff, hc0]
    rw [hslice, Polynomial.analyticOrderAt_eval (pow_ne_zero d (Polynomial.X_sub_C_ne_zero t₀)),
      Polynomial.rootMultiplicity_X_sub_C_pow]
  obtain ⟨A, U, hA, -, hU, hU0, hH_prep⟩ := hH_nash.exists_weierstrassPreparation hH_ord
  let vA : σ ⊕ Unit → ℝ := Sum.elim 0 (fun _ ↦ 1)
  let vU : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim vA (fun _ ↦ 0)
  have hιQ_p₀ : embedZeroProd σ p₀ = Sum.elim y₀ (fun _ ↦ t₀) := by simp [p₀, y₀]
  have hιY_x₀ : embedZero σ x₀ = y₀ := by simp [y₀]
  have hq_nash : IsNashAt (fun p ↦ - fderiv ℝ U (embedZeroProd σ p) vU) p₀ :=
    (hιQ_p₀.symm ▸ (hU.fderiv_apply vU).fun_neg).comp_continuousLinearMap
  have hr_nash (i : Fin d) : IsNashAt (fun x ↦ - fderiv ℝ (A i) (embedZero σ x) vA) x₀ :=
    (hιY_x₀.symm ▸ ((hA i).fderiv_apply vA).fun_neg).comp_continuousLinearMap
  refine ⟨_, _, hq_nash, hr_nash, ?_⟩
  exact weierstrassDivision_eventuallyEq_of_perturbed_preparation
    (fun i ↦ (hc i).analyticAt) hc0 (fun i ↦ (hA i).analyticAt) hU.analyticAt hU0 hH_prep

/-- **Nash Weierstrass division theorem.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be Nash germs at
`Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d` at `t₀`. Then there exist a Nash
germ `q` at `Sum.elim x₀ (fun _ ↦ t₀)` and Nash germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that
near `Sum.elim x₀ (fun _ ↦ t₀)`,
`g p = f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision {f g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.fun_div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.analyticAt.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end Division

end TauCeti
