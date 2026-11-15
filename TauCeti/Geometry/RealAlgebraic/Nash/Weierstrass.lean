/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
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
   real and imaginary parts on `V` (`TauCeti.IsSemialgebraicOn.fderiv_apply`). Shrinking to a
   polydisc `ball x₀ δ × ball t₀ R` inside `V` on which the complexified Weierstrass unit `U` is
   nonvanishing and all `d` complex roots of `P_x` lie in `ball 0 R`, a tuple `c' : Fin d → ℝ`
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
* `TauCeti.IsNashAt.eval_monicOfCoeff`: evaluating a monic polynomial with Nash coefficients at a
  Nash argument yields a Nash germ.
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

/-- The continuous linear equivalence identifying `(σ → ℝ) × ℝ` with `σ ⊕ Unit → ℝ`. -/
private def prodRealEquivSumUnit (σ : Type*) :
    ((σ → ℝ) × ℝ) ≃L[ℝ] (σ ⊕ Unit → ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ (σ → ℝ)).prodCongr
      (ContinuousLinearEquiv.funUnique Unit ℝ ℝ).symm).trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ σ Unit (fun _ ↦ ℝ)).symm

@[simp]
private theorem prodRealEquivSumUnit_apply {σ : Type*} (q : (σ → ℝ) × ℝ) :
    prodRealEquivSumUnit σ q = Sum.elim q.1 (fun _ ↦ q.2) := by
  ext (i | ⟨⟩) <;> rfl

@[simp]
private theorem prodRealEquivSumUnit_symm_apply {σ : Type*} (p : σ ⊕ Unit → ℝ) :
    (prodRealEquivSumUnit σ).symm p = (p ∘ Sum.inl, p (Sum.inr ())) :=
  Prod.ext rfl rfl

@[simp]
private theorem sumElim_comp_inl_inr {σ α : Type*} (p : σ ⊕ Unit → α) :
    Sum.elim (p ∘ Sum.inl) (fun _ : Unit ↦ p (Sum.inr ())) = p := by
  ext (i | ⟨⟩) <;> rfl

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
  let E := prodRealEquivSumUnit σ
  have han : AnalyticAt ℝ (f ∘ E) (E.symm p) :=
    hf.analyticAt.comp_of_eq (E.analyticAt _) (E.apply_symm_apply p)
  have hne : ¬ (f ∘ E) =ᶠ[𝓝 (E.symm p)] 0 := fun h0 ↦ hf0 <| by
    filter_upwards [E.symm.continuous.continuousAt.eventually h0] with y hy
    simpa [Function.comp_apply] using hy
  obtain ⟨M, ⟨x₀, t₀⟩, hM, hord⟩ := han.exists_continuousLinearEquiv_analyticOrderAt_ne_top hne
  let L := E.symm.trans (M.trans E)
  have hLp : L (Sum.elim x₀ (fun _ ↦ t₀)) = p := by
    simp [L, E, hM]
  refine ⟨L, x₀, t₀, hLp, L.isNashAt_comp_iff.mpr (hLp.symm ▸ hf), ?_⟩
  simpa [L, E, Function.comp_def] using hord

/-- Evaluating a monic polynomial whose lower coefficients are Nash germs at `x` on a Nash germ
`g` at `x` produces a Nash germ at `x`. -/
theorem IsNashAt.eval_monicOfCoeff {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ} {g : (σ → ℝ) → ℝ}
    {x : σ → ℝ} (hc : ∀ i, IsNashAt (c i) x) (hg : IsNashAt g x) :
    IsNashAt (fun y ↦ (Polynomial.monicOfCoeff (fun i ↦ c i y)).eval (g y)) x := by
  have heq : (fun y ↦ (Polynomial.monicOfCoeff (fun i ↦ c i y)).eval (g y)) =
      (fun y ↦ g y ^ d) + ∑ i : Fin d, fun y ↦ c i y * g y ^ (i : ℕ) := by
    ext y
    simp [Polynomial.eval_monicOfCoeff, Finset.sum_apply]
  rw [heq]
  exact (hg.fun_pow d).add
    (Finset.univ.isNashAt_sum fun i _ ↦ (hc i).fun_mul (hg.fun_pow (i : ℕ)))

end LinearCoordinates

/-! ### Complex vertical derivatives of semialgebraic holomorphic functions -/

section ComplexVerticalDerivatives

variable {σ : Type*} [Fintype σ]

/-- The `k`-th complex derivative in the `Unit` coordinate of `F : (σ ⊕ Unit → ℂ) → ℂ`. -/
private noncomputable def complexVertDeriv (k : ℕ) (F : (σ ⊕ Unit → ℂ) → ℂ)
    (z : σ ⊕ Unit → ℂ) : ℂ :=
  iteratedDeriv k (fun w ↦ F (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) (z (Sum.inr ()))

omit [Fintype σ] in
@[simp]
private theorem complexVertDeriv_sumElim (k : ℕ) (F : (σ ⊕ Unit → ℂ) → ℂ)
    (x : σ → ℂ) (w : ℂ) :
    complexVertDeriv k F (Sum.elim x (fun _ ↦ w)) =
      iteratedDeriv k (fun ζ ↦ F (Sum.elim x (fun _ ↦ ζ))) w := by
  simp only [complexVertDeriv, Sum.elim_comp_inl, Sum.elim_inr]

/-- The vertical slice embedding `ζ ↦ Sum.elim x (fun _ ↦ ζ)` into `σ ⊕ Unit → ℂ` is analytic. -/
private theorem analyticAt_sumElim_const (x : σ → ℂ) (w : ℂ) :
    AnalyticAt ℂ (fun ζ : ℂ ↦ Sum.elim x (fun _ : Unit ↦ ζ)) w :=
  analyticAt_pi_iff.mpr fun j ↦ by
    cases j with
    | inl _ => exact analyticAt_const
    | inr _ => exact analyticAt_id

/-- For `F` holomorphic on `V`, the analytic order of the vertical slice
`ζ ↦ F (Sum.elim x (fun _ ↦ ζ))` at `w` equals `n` if and only if the first `n` vertical
derivatives vanish at `Sum.elim x (fun _ ↦ w)` and the `n`-th does not. -/
private theorem analyticOrderAt_sumElim_eq_nat_iff {V : Set (σ ⊕ Unit → ℂ)}
    {F : (σ ⊕ Unit → ℂ) → ℂ} (hFV : AnalyticOnNhd ℂ F V)
    {x : σ → ℂ} {w : ℂ} (hpt : Sum.elim x (fun _ ↦ w) ∈ V) (n : ℕ) :
    analyticOrderAt (fun ζ ↦ F (Sum.elim x (fun _ ↦ ζ))) w = n ↔
      (∀ k : Fin n, complexVertDeriv k F (Sum.elim x (fun _ ↦ w)) = 0) ∧
        complexVertDeriv n F (Sum.elim x (fun _ ↦ w)) ≠ 0 := by
  have hslice : AnalyticAt ℂ (fun ζ ↦ F (Sum.elim x (fun _ ↦ ζ))) w :=
    (hFV _ hpt).comp_of_eq (analyticAt_sumElim_const x w) rfl
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hslice]
  simp [Fin.forall_iff]

/-- On an open set where `G = complexVertDeriv k F` is holomorphic, the `(k + 1)`-th vertical
derivative equals the complex Fréchet derivative of `G` in the unit vertical direction. -/
private theorem complexVertDeriv_succ_eq_fderiv {V : Set (σ ⊕ Unit → ℂ)}
    {F : (σ ⊕ Unit → ℂ) → ℂ} {k : ℕ} (hG : AnalyticOnNhd ℂ (complexVertDeriv k F) V)
    {z : σ ⊕ Unit → ℂ} (hz : z ∈ V) :
    complexVertDeriv (k + 1) F z =
      fderiv ℂ (complexVertDeriv k F) z (Sum.elim 0 (fun _ ↦ 1)) := by
  let vℂ : σ ⊕ Unit → ℂ := Sum.elim 0 (fun _ ↦ 1)
  let φ : ℂ → (σ ⊕ Unit → ℂ) := fun w ↦ z + (w - z (Sum.inr ())) • vℂ
  have hφ_eq (w : ℂ) : φ w = Sum.elim (z ∘ Sum.inl) (fun _ ↦ w) := by
    ext (i | ⟨⟩) <;> simp [φ, vℂ]
  have hφ_deriv : HasDerivAt φ vℂ (z (Sum.inr ())) := by
    simpa [φ] using
      (((hasDerivAt_id (z (Sum.inr ()))).sub_const (z (Sum.inr ()))).smul_const vℂ).const_add z
  have hφz : φ (z (Sum.inr ())) = z := by simp [φ]
  have hGφ : HasFDerivAt (complexVertDeriv k F)
      (fderiv ℂ (complexVertDeriv k F) z) (φ (z (Sum.inr ()))) := by
    rw [hφz]
    exact (hG z hz).differentiableAt.hasFDerivAt
  have hstep : complexVertDeriv (k + 1) F z =
      deriv (fun w ↦ complexVertDeriv k F (φ w)) (z (Sum.inr ())) := by
    simp only [complexVertDeriv, hφ_eq, Sum.elim_comp_inl, Sum.elim_inr, iteratedDeriv_succ]
  rw [hstep]
  exact (hGφ.comp_hasDerivAt (z (Sum.inr ())) hφ_deriv).deriv

/-- If `L ∘ complexVertDeriv k F ∘ (complexToRealPi (σ ⊕ Unit)).symm` has semialgebraic graph on
`(complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V`, then so does the `(k + 1)`-th vertical derivative. -/
private theorem isSemialgebraicOn_comp_complexVertDeriv_succ {V : Set (σ ⊕ Unit → ℂ)}
    {F : (σ ⊕ Unit → ℂ) → ℂ} {k : ℕ} (hVo : IsOpen V)
    (hGa : AnalyticOnNhd ℂ (complexVertDeriv k F) V) (L : ℂ →L[ℝ] ℝ)
    (hLS : IsSemialgebraicOn
      (fun a (_ : Unit) ↦ L (complexVertDeriv k F ((complexToRealPi (σ ⊕ Unit)).symm a)))
      ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V)) :
    IsSemialgebraicOn
      (fun a (_ : Unit) ↦ L (complexVertDeriv (k + 1) F ((complexToRealPi (σ ⊕ Unit)).symm a)))
      ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V) := by
  let e := complexToRealPi (σ ⊕ Unit)
  let S := e.symm ⁻¹' V
  let vℂ : σ ⊕ Unit → ℂ := Sum.elim 0 (fun _ ↦ 1)
  let g : ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ) → ℝ := ⇑L ∘ fun b ↦ complexVertDeriv k F (e.symm b)
  have hSo : IsOpen S := hVo.preimage e.symm.continuous
  have hfd (a : (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ) (ha : a ∈ S) :
      HasFDerivAt g
        (L.comp (((fderiv ℂ (complexVertDeriv k F) (e.symm a)).restrictScalars ℝ).comp
          e.symm.toContinuousLinearMap)) a :=
    L.hasFDerivAt.comp a
      (((hGa (e.symm a) ha).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp
        a e.symm.hasFDerivAt)
  have hd : DifferentiableOn ℝ g S :=
    fun a ha ↦ (hfd a ha).differentiableAt.differentiableWithinAt
  have hgS : IsSemialgebraicOn (fun a (_ : Unit) ↦ g a) S := hLS
  refine (hgS.fderiv_apply hSo hd (e vℂ)).congr fun a ha ↦ funext fun _ ↦ ?_
  dsimp only
  rw [(hfd a ha).fderiv]
  simp [complexVertDeriv_succ_eq_fderiv hGa ha, vℂ, e]

/-- Every complex vertical derivative of a holomorphic function with semialgebraic realified graph
on an open set `V` is again holomorphic on `V` with semialgebraic realified graph on the same
domain. -/
private theorem analyticOnNhd_and_isSemialgebraicOn_complexVertDeriv {V : Set (σ ⊕ Unit → ℂ)}
    {F : (σ ⊕ Unit → ℂ) → ℂ} (hVo : IsOpen V) (hFV : AnalyticOnNhd ℂ F V)
    (hFS : IsSemialgebraicOn
      (fun a ↦ complexToRealPi Unit (fun _ ↦ F ((complexToRealPi (σ ⊕ Unit)).symm a)))
      ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V))
    (k : ℕ) :
    AnalyticOnNhd ℂ (complexVertDeriv k F) V ∧
      IsSemialgebraicOn
        (fun a ↦ complexToRealPi Unit
          (fun _ ↦ complexVertDeriv k F ((complexToRealPi (σ ⊕ Unit)).symm a)))
        ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V) := by
  induction k with
  | zero =>
    have h0 : complexVertDeriv 0 F = F := by
      ext z
      simp [complexVertDeriv, iteratedDeriv_zero]
    simpa only [h0] using ⟨hFV, hFS⟩
  | succ k ih =>
    obtain ⟨hGa, hGS⟩ := ih
    let vℂ : σ ⊕ Unit → ℂ := Sum.elim 0 (fun _ ↦ 1)
    have han : AnalyticOnNhd ℂ (complexVertDeriv (k + 1) F) V := by
      intro z hz
      have hfd : AnalyticAt ℂ (fun y ↦ fderiv ℂ (complexVertDeriv k F) y vℂ) z :=
        ((ContinuousLinearMap.apply ℂ ℂ vℂ).analyticAt _).comp (hGa z hz).fderiv
      refine hfd.congr ?_
      filter_upwards [hVo.mem_nhds hz] with y hy
      exact (complexVertDeriv_succ_eq_fderiv hGa hy).symm
    obtain ⟨hS, hcoords⟩ := isSemialgebraicOn_pi_iff.mp hGS
    refine ⟨han, isSemialgebraicOn_pi_iff.mpr ⟨hS, fun j ↦ ?_⟩⟩
    cases j with
    | inl u =>
      have hre : IsSemialgebraicOn
          (fun a (_ : Unit) ↦
            Complex.reCLM (complexVertDeriv k F ((complexToRealPi (σ ⊕ Unit)).symm a)))
          ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V) :=
        (hcoords (.inl u)).congr fun a _ ↦ funext fun _ ↦ by simp
      exact (isSemialgebraicOn_comp_complexVertDeriv_succ hVo hGa Complex.reCLM hre).congr
        fun a _ ↦ funext fun _ ↦ by simp
    | inr u =>
      have him : IsSemialgebraicOn
          (fun a (_ : Unit) ↦
            Complex.imCLM (complexVertDeriv k F ((complexToRealPi (σ ⊕ Unit)).symm a)))
          ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V) :=
        (hcoords (.inr u)).congr fun a _ ↦ funext fun _ ↦ by simp
      exact (isSemialgebraicOn_comp_complexVertDeriv_succ hVo hGa Complex.imCLM him).congr
        fun a _ ↦ funext fun _ ↦ by simp

/-- Pulling back a realified complex vertical derivative along real polynomial coordinates `(xP,
wRe, wIm)`: both the locus in `V` where it vanishes and the locus in `V` where it is nonzero are
semialgebraic. -/
private theorem isSemialgebraic_setOf_complexVertDeriv_eq_and_ne_zero {ν : Type*}
    {V : Set (σ ⊕ Unit → ℂ)} {H : (σ ⊕ Unit → ℂ) → ℂ}
    (hHS : IsSemialgebraicOn
      (fun a ↦ complexToRealPi Unit (fun _ ↦ H ((complexToRealPi (σ ⊕ Unit)).symm a)))
      ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V))
    (xP : σ → MvPolynomial ν ℝ) (wRe wIm : MvPolynomial ν ℝ) :
    let pt : (ν → ℝ) → (σ ⊕ Unit → ℂ) := fun v ↦
      Sum.elim (fun i ↦ (MvPolynomial.eval v (xP i) : ℂ))
        (fun _ ↦ (MvPolynomial.eval v wRe : ℂ) + (MvPolynomial.eval v wIm : ℂ) * Complex.I)
    IsSemialgebraic {v : ν → ℝ | pt v ∈ V ∧ H (pt v) = 0} ∧
      IsSemialgebraic {v : ν → ℝ | pt v ∈ V ∧ H (pt v) ≠ 0} := by
  intro pt
  let pIn : (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → MvPolynomial ν ℝ :=
    Sum.elim (Sum.elim xP (fun _ ↦ wRe)) (Sum.elim (fun _ ↦ 0) (fun _ ↦ wIm))
  have hpt (v : ν → ℝ) :
      (complexToRealPi (σ ⊕ Unit)).symm (fun s ↦ MvPolynomial.eval v (pIn s)) = pt v := by
    ext (i | ⟨⟩) <;> simp [pIn, pt]
  have hdom : IsSemialgebraic {v : ν → ℝ | pt v ∈ V} := by
    convert hHS.isSemialgebraic.preimage_eval pIn using 1
    ext v
    simp only [mem_ofPred_eq, mem_preimage, hpt]
  let q : ((σ ⊕ Unit) ⊕ (σ ⊕ Unit)) ⊕ (Unit ⊕ Unit) → MvPolynomial ν ℝ := Sum.elim pIn 0
  have hzero : IsSemialgebraic {v : ν → ℝ | pt v ∈ V ∧ H (pt v) = 0} := by
    convert hHS.graph.preimage_eval q using 1
    ext v
    rw [mem_ofPred_eq, mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn]
    have hinl : ((fun t ↦ MvPolynomial.eval v (q t)) ∘ Sum.inl) =
        fun s ↦ MvPolynomial.eval v (pIn s) := by
      ext s
      simp [q]
    have hinr : ((fun t ↦ MvPolynomial.eval v (q t)) ∘ Sum.inr) = 0 := by
      ext u
      simp [q]
    rw [hinl, hinr, mem_preimage, hpt]
    refine and_congr_right fun _ ↦ ?_
    simp [Complex.ext_iff, funext_iff]
  refine ⟨hzero, ?_⟩
  convert hdom.sdiff hzero using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  tauto

end ComplexVerticalDerivatives

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
    ((prodRealEquivSumUnit σ).symm.continuous.tendsto' p₀ (x₀, t₀) (by simp [p₀])).congr
      fun _ ↦ by simp
  have hp_inl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, t₀)).comp hp_prod
  filter_upwards [hp_real.eventually (hVo.mem_nhds hz₀V), ball_mem_nhds p₀ hrU,
    hp_prod.eventually hfac, hp_inl.eventually hCc_ev] with p hpV hpU hpf hpC
  rw [sumElim_comp_inl_inr] at hpf
  rw [hFr p hpV, hpf, Complex.ofReal_mul, ← hUr p hpU]
  congr 1
  simp only [Polynomial.eval_monicOfCoeff, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hci : C i ((fun j ↦ (p j : ℂ)) ∘ Sum.inl) = (c i (p ∘ Sum.inl) : ℂ) := hpC i
  rw [hci]

/-- For a nonzero complex polynomial `P` and a function `v : ℂ → ℂ` analytic and nonzero at
`w₀ + ζ`, the product `w ↦ P.eval (w - w₀) * v w` has analytic order `P.rootMultiplicity ζ` at
`w₀ + ζ`. -/
private theorem analyticOrderAt_eval_sub_mul_of_ne_zero {P : ℂ[X]} (hP : P ≠ 0)
    {v : ℂ → ℂ} {w₀ ζ : ℂ} (hv : AnalyticAt ℂ v (w₀ + ζ)) (hv0 : v (w₀ + ζ) ≠ 0) :
    analyticOrderAt (fun w ↦ P.eval (w - w₀) * v w) (w₀ + ζ) = (P.rootMultiplicity ζ : ℕ∞) := by
  have htr : AnalyticAt ℂ (fun w : ℂ ↦ w - w₀) (w₀ + ζ) :=
    analyticAt_id.fun_sub analyticAt_const
  have hP_an : AnalyticAt ℂ (fun w ↦ P.eval (w - w₀)) (w₀ + ζ) :=
    ((AnalyticOnNhd.eval_polynomial P) _ trivial).comp htr
  have htr' : deriv (fun w : ℂ ↦ w - w₀) (w₀ + ζ) ≠ 0 := by
    rw [deriv_sub_const, deriv_id'']; exact one_ne_zero
  have hP_ord : analyticOrderAt (fun w ↦ P.eval (w - w₀)) (w₀ + ζ) =
      (P.rootMultiplicity ζ : ℕ∞) := by
    have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := fun u ↦ P.eval u) htr htr'
    rw [Function.comp_def, add_sub_cancel_left, Polynomial.analyticOrderAt_eval hP] at hcomp
    exact hcomp
  have hv_ord : analyticOrderAt v (w₀ + ζ) = 0 := hv.analyticOrderAt_eq_zero.mpr hv0
  exact (analyticOrderAt_mul hP_an hv).trans (by rw [hP_ord, hv_ord, add_zero])

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
  choose ρ hρ C hC hCc _ using fun i ↦ (hc i).exists_complexification
  have hu_sum : AnalyticAt ℝ (fun p : σ ⊕ Unit → ℝ ↦ u (p ∘ Sum.inl, p (Sum.inr ()))) p₀ := by
    simpa [Function.comp_def] using
      hu.comp_of_eq ((prodRealEquivSumUnit σ).symm.analyticAt p₀) (by simp [p₀])
  obtain ⟨rU, hrU, U, hU, hUr, -⟩ := hu_sum.exists_complexification
  have hCc_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun j ↦ (x j : ℂ)) = c i x :=
    eventually_all.mpr fun i ↦ Filter.mem_of_superset (ball_mem_nhds x₀ (hρ i)) (hCc i)
  have hF_eq := eventuallyEq_complexification_weierstrassPreparation hVo hz₀V hFV hFr
    (fun i ↦ hC i _ (mem_ball_self (hρ i))) hCc_ev hrU hU hUr hfac
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
  exact analyticOrderAt_eval_sub_mul_of_ne_zero (Polynomial.monic_monicOfCoeff _).ne_zero
    hU_slice_an (hballZ hz₀_pt).2.1

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
          (∀ k : Fin (m l), complexVertDeriv k F
            (Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l)) = 0) ∧
          complexVertDeriv (m l) F
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
  have h_eq (l : Fin r) (k : ℕ) := isSemialgebraic_setOf_complexVertDeriv_eq_and_ne_zero
    (analyticOnNhd_and_isSemialgebraicOn_complexVertDeriv hVo hFV hFS k).2
    xP (MvPolynomial.C t₀ + zRe l) (zIm l)
  have hS_mult : IsSemialgebraic {v : ν → ℝ | ∀ l : Fin r,
      let pt := Sum.elim (fun i ↦ (v (.inl (.inl i)) : ℂ))
        (fun _ ↦ (t₀ : ℂ) + ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I))
      pt ∈ V ∧ (∀ k : Fin (m l), complexVertDeriv k F pt = 0) ∧
        complexVertDeriv (m l) F pt ≠ 0} := by
    convert IsSemialgebraic.iInter (fun l : Fin r ↦
      (IsSemialgebraic.iInter fun k : Fin (m l) ↦ (h_eq l k).1).inter (h_eq l (m l)).2) using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, xP, zRe, zIm, map_add,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Complex.ofReal_add, add_assoc]
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
      isSemialgebraic_rootCluster_branch hVo hFV hFS x₀ t₀ R δ r (fun l ↦ (m.1 l : ℕ))) using 1
  ext w
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_iUnion, mem_ofPred_eq]
  let x := w ∘ Sum.inl
  let P : ℂ[X] := Polynomial.monicOfCoeff (fun j ↦ (c j x : ℂ))
  have hP_monic : P.Monic := Polynomial.monic_monicOfCoeff _
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
      exact ⟨hptV, (analyticOrderAt_sumElim_eq_nat_iff hFV hptV (m l)).mp
        (hord_eq.trans (congrArg Nat.cast (hmult l)))⟩
    · intro j
      have hcj : w (.inr j) = c j x := (congrFun hcx j).symm
      rw [hcj, ← Polynomial.coeff_monicOfCoeff (fun k ↦ (c k x : ℂ)) j]
      change P.coeff (j : ℕ) = _
      rw [← hprod]
      simp [Complex.re_add_im, m']
      rfl
  · -- Reverse direction: recover `P` from `d` roots counted with vertical-slice multiplicity.
    rintro ⟨r, m, hx, y, hyR, hpair, hderiv, hcoeff⟩
    refine ⟨hx, ?_⟩
    let z : Fin (r : ℕ) → ℂ := fun l ↦ (y (.inl l) : ℂ) + (y (.inr l) : ℂ) * Complex.I
    have hzR (l : Fin (r : ℕ)) : ‖z l‖ < R :=
      (hnorm (z l)).mpr (by simpa [z] using hyR l)
    have hmult (l : Fin (r : ℕ)) : P.rootMultiplicity (z l) = (m.1 l : ℕ) := by
      obtain ⟨hptV, hk0, hkne⟩ := hderiv l
      obtain ⟨-, hord_eq⟩ := hord x hx (z l) (hzR l)
      exact Nat.cast_injective (R := ℕ∞) <| hord_eq.symm.trans <|
        (analyticOrderAt_sumElim_eq_nat_iff hFV hptV (m.1 l : ℕ)).mpr ⟨hk0, hkne⟩
    have hP_eq := hP_monic.eq_prod_X_sub_C_pow_of_le_rootMultiplicity (z := z)
      (m := fun l ↦ (m.1 l : ℕ)) (by rw [Polynomial.natDegree_monicOfCoeff, m.2])
      (fun _ _ h ↦ by_contra fun hne ↦ hpair _ _ hne h) (fun l ↦ (hmult l).ge)
    funext j
    apply Complex.ofReal_injective
    rw [← Polynomial.coeff_monicOfCoeff (fun k ↦ (c k x : ℂ)) j]
    change P.coeff (j : ℕ) = _
    rw [hP_eq, ← hcoeff j]
    rfl

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
  let E := prodRealEquivSumUnit σ
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
    simpa only [Function.comp_apply, u, E, prodRealEquivSumUnit_symm_apply,
      prodRealEquivSumUnit_apply, sumElim_comp_inl_inr] using hp
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
      tendsto_pi_nhds.mpr fun j ↦ by
        cases j with
        | inl _ => exact tendsto_const_nhds
        | inr _ => exact tendsto_id
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
      rcases j with (i | ⟨⟩) | ⟨⟩
      · exact continuous_const
      · exact continuous_id
      · exact continuous_const
  have hline_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) - s * g p =
        (Polynomial.monicOfCoeff
          (fun i ↦ A i (Sum.elim (p ∘ Sum.inl) (fun _ ↦ s)))).eval (p (Sum.inr ()) - t₀) *
          U (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ s)) (fun _ ↦ p (Sum.inr ()))) := by
    filter_upwards [(hline_cont.tendsto' 0 (ιQ p) (by simp [ιQ])).eventually hHp] with s hs
    simpa only [projDropMiddle_apply, Sum.elim_comp_inl, Sum.elim_inl, Sum.elim_inr,
      sumElim_comp_inl_inr] using hs
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
  have hπH_q₀ : πH q₀ = p₀ := by simp [πH, p₀, q₀, y₀]
  have hH_nash : IsNashAt H q₀ := by
    have hP : IsNashAt (fun q : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i ((q ∘ Sum.inl) ∘ Sum.inl))).eval
          (q (Sum.inr ()) - t₀)) q₀ :=
      IsNashAt.eval_monicOfCoeff
        (fun i ↦ (hc i).comp fun j ↦ isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inl (.inl j)))
        ((isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inr ())).fun_sub (isNashAt_const t₀))
    have hg_comp : IsNashAt (g ∘ πH) q₀ :=
      (show IsNashAt g (πH q₀) by simpa [hπH_q₀, p₀] using hg).comp_continuousLinearMap πH
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
  have hq_nash : IsNashAt (fun p ↦ - fderiv ℝ U (embedZeroProd σ p) vU) p₀ :=
    (show IsNashAt (fun z ↦ - fderiv ℝ U z vU) (embedZeroProd σ p₀) by
      simpa [p₀, q₀, y₀] using (hU.fderiv_apply vU).fun_neg).comp_continuousLinearMap
      (embedZeroProd σ)
  have hr_nash (i : Fin d) : IsNashAt (fun x ↦ - fderiv ℝ (A i) (embedZero σ x) vA) x₀ :=
    (show IsNashAt (fun y ↦ - fderiv ℝ (A i) y vA) (embedZero σ x₀) by
      simpa [y₀] using ((hA i).fderiv_apply vA).fun_neg).comp_continuousLinearMap (embedZero σ)
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
