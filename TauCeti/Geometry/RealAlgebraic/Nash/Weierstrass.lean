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
import Mathlib.RingTheory.Coprime.Lemmas
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Derivative
import TauCeti.Topology.Constructions.SumProd
import TauCeti.Topology.ContinuousOn.ClosedGraph

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

1. **Exact division of Nash germs (`TauCeti.IsNashAt.of_eventuallyEq_mul_left`).** If `g =ᶠ f * u`
   near `x`, with `f` and `g` Nash at `x`, `f` not identically zero near `x`, and `u` real analytic
   at `x`, then `u` is Nash at `x`. On an open ball `B` around `x` where `f` and `g` have
   semialgebraic graphs, the identity principle makes `t = {y ∈ B | f y ≠ 0}` dense in `B`; over
   `t` the equation `f y * z = g y` cuts out the graph of `u`, and continuity recovers the graph
   over `B` from its closure. Both `AnalyticAt ℝ u x` and `¬ f =ᶠ[𝓝 x] 0` are needed: for instance
   `x₁ ^ 3 = (x₁ ^ 2 + x₂ ^ 2) * u (x₁, x₂)` has a continuous semialgebraic quotient at the origin
   that is not analytic.

2. **Nashness of the preparation coefficients.** Let `F` be a holomorphic extension of `f` on an
   open neighborhood `V` whose realification has semialgebraic domain and graph
   (`TauCeti.IsNashAt.exists_complexification`). Differentiating in the real vertical direction
   shows by induction on `k` that every complex vertical derivative of `F` also has semialgebraic
   real and imaginary parts on `V` (`TauCeti.IsSemialgebraicOn.fderiv_apply`). Shrinking to a
   polydisc `ball x₀ δ × ball t₀ R` inside `V` on which the complexified Weierstrass unit `U` is
   nonvanishing and all `d` complex roots of `P_x` lie in `ball 0 R`, a tuple `c' : Fin d → ℝ`
   equals `fun i ↦ c i x` if and only if there exist `r ≤ d` pairwise distinct points `z l` in
   `ball 0 R` with positive multiplicities `m l` summing to `d` at which `w ↦ F (x, w)` vanishes to
   exact order `m l` (characterized by vanishing of the first `m l` vertical derivatives and
   nonvanishing of the `m l`-th) and `c'` gives the coefficients of `∏ l, (X - C (z l)) ^ m l`.
   Eliminating the root coordinates via Tarski–Seidenberg
   (`TauCeti.IsSemialgebraic.setOf_exists_sumElim`) makes the graph of `x ↦ fun i ↦ c i x`
   semialgebraic on `ball x₀ δ`, so each `c i` is Nash at `x₀` by the local Nash graph criterion.
   Exact division then makes the unit `u` Nash at `p₀`.

3. **Nash Weierstrass division.** Rather than repeating root-cluster elimination for Hermite
   interpolation, division by a Nash Weierstrass polynomial `P_x` is deduced from preparation by
   Nirenberg's perturbation argument (Bochnak–Coste–Roy, Proposition 8.2.2): introducing one
   auxiliary real parameter `ε`, the Nash germ `H (x, ε, t) = P_x (t - t₀) - ε * g (x, t)` has
   vertical slice `(t - t₀) ^ d` at `(x₀, 0)`, hence admits a Nash Weierstrass preparation
   `P_{A (x, ε)} (t - t₀) * U (x, ε, t)`. At `ε = 0`, uniqueness of the real Weierstrass
   preparation (`TauCeti.eventuallyEq_of_weierstrassPreparation_real`) identifies `A (x, 0) = c x`
   and `U (x, 0, t) = 1`; differentiating the factorization with respect to `ε` at `ε = 0`
   (`TauCeti.IsNashAt.fderiv_apply`) yields `g = P_x * (-∂_ε U) + ∑ i, (-∂_ε A_i) * (t - t₀) ^ i`
   with Nash quotient and remainder coefficients.

## Main declarations

* `TauCeti.IsNashAt.of_eventuallyEq_mul_left`, `TauCeti.IsNashAt.of_eventuallyEq_mul_right`:
  an analytic quotient of Nash germs by a non-identically-zero Nash factor is Nash.
* `TauCeti.IsNashAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: general-position linear
  change of coordinates making a non-identically-zero Nash germ regular in the vertical variable.
* `TauCeti.IsNashAt.eval_monicOfCoeff`: evaluating a monic polynomial with Nash coefficients at a
  Nash argument yields a Nash germ.
* `TauCeti.IsNashAt.exists_weierstrassPreparation`: **Nash Weierstrass preparation theorem.**
* `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`,
  `TauCeti.IsNashAt.exists_weierstrassDivision`: **Nash Weierstrass division theorems.**
* `TauCeti.eventuallyEq_of_weierstrassPreparation_sumElim`,
  `TauCeti.eventuallyEq_of_weierstrassDivision_sumElim`: uniqueness of local real Weierstrass
  preparation and division in `σ ⊕ Unit → ℝ` coordinates.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Sections 8.1 and 8.2.
* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
-/

public section

open Complex Filter Function Metric MvPolynomial Polynomial Set Topology

namespace TauCeti

section ExactDivision

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
/-- A scalar function continuous on a semialgebraic set `s` whose graph is semialgebraic over a
relatively dense subset `t ⊆ s` has semialgebraic graph over `s`. -/
private theorem isSemialgebraicOn_scalar_of_dense_subset [Finite σ] {u : (σ → ℝ) → ℝ}
    {s t : Set (σ → ℝ)}
    (hs : IsSemialgebraic s) (hu_cont : ContinuousOn u s) (hts : t ⊆ s) (hst : s ⊆ closure t)
    (hu_t : IsSemialgebraicOn (fun y (_ : Unit) ↦ u y) t) :
    IsSemialgebraicOn (fun y (_ : Unit) ↦ u y) s := by
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := ℝ) (ι := σ) (ι' := Unit)
  have he : ⇑e = ⇑(Equiv.sumArrowEquivProdArrow σ Unit ℝ) :=
    Homeomorph.coe_sumArrowHomeomorphProdArrow
  have hfst (z : σ ⊕ Unit → ℝ) : (e z).1 = z ∘ Sum.inl := by
    rw [he]
    exact funext (Equiv.sumArrowEquivProdArrow_apply_fst z)
  have hcl := (continuousOn_pi.mpr fun _ : Unit ↦ hu_cont).closure_graphOn_inter hts hst
  refine isSemialgebraicOn_def.mpr ⟨hs, ?_⟩
  have hsemi := hu_t.graph.closure.inter (hs.preimage_comp Sum.inl)
  rw [← he, ← e.preimage_closure] at hsemi
  convert hsemi using 1
  ext z
  have hz := Set.ext_iff.mp (congrArg (fun S ↦ e ⁻¹' S) hcl) z
  rw [he, mem_preimage_sumArrowEquivProdArrow_scalar_graphOn] at hz
  rw [mem_preimage_sumArrowEquivProdArrow_scalar_graphOn]
  simpa only [← he, mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true, hfst] using hz.symm

/-- **Exact division of Nash germs.** If `g =ᶠ[𝓝 x] f * u` with `f` and `g` Nash germs at `x`,
`f` not identically zero near `x`, and `u` real analytic at `x`, then `u` is a Nash germ at `x`. -/
theorem IsNashAt.of_eventuallyEq_mul_left {f g u : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hg : IsNashAt g x) (hf : IsNashAt f x) (hf0 : ¬ f =ᶠ[𝓝 x] 0)
    (hu : AnalyticAt ℝ u x) (h : g =ᶠ[𝓝 x] f * u) : IsNashAt u x := by
  obtain ⟨-, Uf, hUfo, hxUf, -, hfU⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hf
  obtain ⟨-, Ug, hUgo, hxUg, -, hgU⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp <|
    inter_mem (inter_mem (hUfo.mem_nhds hxUf) (hUgo.mem_nhds hxUg)) <|
      inter_mem (inter_mem hf.analyticAt.eventually_analyticAt hu.eventually_analyticAt) h
  let B := ball x r
  have hB : IsSemialgebraic B := isSemialgebraic_ball x r
  have hfB : IsSemialgebraicOn (fun y (_ : Unit) ↦ f y) B :=
    hfU.mono hB fun y hy ↦ (hball hy).1.1
  have hgB : IsSemialgebraicOn (fun y (_ : Unit) ↦ g y) B :=
    hgU.mono hB fun y hy ↦ (hball hy).1.2
  have hZ : IsSemialgebraic (B ∩ {y | f y = 0}) := by
    simpa only [funext_iff, forall_const] using
      hfB.isSemialgebraic_inter_setOf_eq (isSemialgebraicOn_const (fun _ : Unit ↦ (0 : ℝ)) hB)
  let t := B ∩ {y | f y ≠ 0}
  have ht : IsSemialgebraic t := by
    convert hB.sdiff hZ using 1
    ext y
    simp only [t, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hts : t ⊆ B := inter_subset_left
  have hst : B ⊆ closure t := fun y hy ↦ by
    by_contra hycl
    have hev : f =ᶠ[𝓝 y] 0 := by
      filter_upwards [(isOpen_ball.inter isClosed_closure.isOpen_compl).mem_nhds ⟨hy, hycl⟩]
        with w ⟨hwB, hwcl⟩
      by_contra hfw
      exact hwcl (subset_closure ⟨hwB, hfw⟩)
    have hfa : AnalyticOnNhd ℝ f B := fun w hw ↦ (hball hw).2.1.1
    have hzero := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x r).isPreconnected hy hev
    exact hf0 (eventually_of_mem (ball_mem_nhds x hr) fun w hw ↦ hzero hw)
  have hu_t : IsSemialgebraicOn (fun y (_ : Unit) ↦ u y) t := by
    refine isSemialgebraicOn_def.mpr ⟨ht, ?_⟩
    let t' : Set (σ ⊕ Unit → ℝ) := (fun z ↦ z ∘ Sum.inl) ⁻¹' t
    have ht' : IsSemialgebraic t' := ht.preimage_comp Sum.inl
    have hproj : IsSemialgebraicOn (fun z : σ ⊕ Unit → ℝ ↦ z ∘ Sum.inl) t' :=
      (isSemialgebraicOn_eval (fun i ↦ MvPolynomial.X (.inl i)) ht').congr
        fun z _ ↦ funext fun i ↦ MvPolynomial.eval_X _
    have hmul := ((hfB.mono ht hts).comp hproj fun _ hz ↦ hz).mul
      (isSemialgebraicOn_eval (fun _ : Unit ↦ MvPolynomial.X (.inr ())) ht')
    have hgr := (hgB.mono ht hts).comp hproj fun _ hz ↦ hz
    convert hmul.isSemialgebraic_inter_setOf_eq hgr using 1
    ext z
    rw [mem_preimage_sumArrowEquivProdArrow_scalar_graphOn]
    simp only [mem_inter_iff, mem_ofPred_eq, t', mem_preimage, funext_iff, Unique.forall_iff,
      Pi.mul_apply, Function.comp_apply, MvPolynomial.eval_X]
    refine and_congr_right fun hz ↦ ?_
    have hgu : g (z ∘ Sum.inl) = f (z ∘ Sum.inl) * u (z ∘ Sum.inl) := (hball hz.1).2.2
    rw [hgu, mul_eq_mul_left_iff]
    exact ⟨fun h' ↦ Or.inl h'.symm, fun h' ↦ (h'.resolve_right hz.2).symm⟩
  have huB := isSemialgebraicOn_scalar_of_dense_subset hB
    (AnalyticOnNhd.continuousOn fun y hy ↦ (hball hy).2.1.2) hts hst hu_t
  exact huB.isNashAt hu (ball_mem_nhds x hr)

/-- Right-factor version of `TauCeti.IsNashAt.of_eventuallyEq_mul_left`: if `g =ᶠ[𝓝 x] u * f` with
`f` and `g` Nash germs at `x`, `f` not identically zero near `x`, and `u` real analytic at `x`,
then `u` is a Nash germ at `x`. -/
theorem IsNashAt.of_eventuallyEq_mul_right {f g u : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hg : IsNashAt g x) (hf : IsNashAt f x) (hf0 : ¬ f =ᶠ[𝓝 x] 0)
    (hu : AnalyticAt ℝ u x) (h : g =ᶠ[𝓝 x] u * f) : IsNashAt u x :=
  hg.of_eventuallyEq_mul_left hf hf0 hu
    (h.trans (Eventually.of_forall fun y ↦ mul_comm (u y) (f y)))

end ExactDivision

/-! ### Linear coordinate changes and general position -/

section LinearCoordinates

variable {σ : Type*} [Fintype σ]

/-- The continuous linear equivalence identifying `(σ → ℝ) × ℝ` with `σ ⊕ Unit → ℝ`. -/
private noncomputable def prodRealEquivSumUnit (σ : Type*) [Fintype σ] :
    ((σ → ℝ) × ℝ) ≃L[ℝ] (σ ⊕ Unit → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ Sum.elim p.1 (fun _ ↦ p.2)
      invFun := fun z ↦ (z ∘ Sum.inl, z (Sum.inr ()))
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun z ↦ by ext (i | ⟨⟩) <;> rfl
      map_add' := fun _ _ ↦ by ext (i | ⟨⟩) <;> rfl
      map_smul' := fun _ _ ↦ by ext (i | ⟨⟩) <;> rfl }

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
    have hE : E.symm (Sum.elim x₀ (fun _ ↦ t₀)) = (x₀, t₀) := rfl
    simp [L, hE, hM]
  refine ⟨L, x₀, t₀, hLp, (isNashAt_comp_continuousLinearEquiv_iff L).mpr (hLp.symm ▸ hf), ?_⟩
  simpa [L, E, prodRealEquivSumUnit, Function.comp_def] using hord

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
    simp only [complexVertDeriv, iteratedDeriv_succ, hφ_eq]
    rfl
  rw [hstep]
  exact (hGφ.comp_hasDerivAt (z (Sum.inr ())) hφ_deriv).deriv

/-- Differentiating a real linear projection `L ∘ G ∘ e.symm` on `e.symm ⁻¹' V` in the realified
unit vertical direction recovers `L` applied to the next complex vertical derivative. -/
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
  rw [(hfd a ha).fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, ContinuousLinearMap.coe_restrictScalars',
    ← complexVertDeriv_succ_eq_fderiv hGa ha]

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
      simp only [complexVertDeriv, iteratedDeriv_zero]
      congr 1
      ext (i | ⟨⟩) <;> rfl
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
        fun s ↦ MvPolynomial.eval v (pIn s) := rfl
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

/-! ### Root clusters of monic complex polynomials -/

section RootCluster

/-- Every monic complex polynomial `P = monicOfCoeff c₀` whose roots lie in `ball 0 R` admits a
finite distinct-root cluster `(r, m, z)` in `ball 0 R` recovering its coefficients. -/
private theorem exists_rootCluster_of_monicOfCoeff {d : ℕ} {c₀ : Fin d → ℂ} {R : ℝ}
    (hroots : ∀ z, (Polynomial.monicOfCoeff c₀).IsRoot z → ‖z‖ < R) :
    let P := Polynomial.monicOfCoeff c₀
    ∃ (r : Fin (d + 1)) (m : Fin (r : ℕ) → Fin (d + 1)) (z : Fin (r : ℕ) → ℂ),
      ((∀ l, 0 < (m l : ℕ)) ∧ ∑ l, (m l : ℕ) = d) ∧
      (∀ l, ‖z l‖ < R) ∧
      Pairwise (fun l l' ↦ z l ≠ z l') ∧
      (∀ l, P.rootMultiplicity (z l) = (m l : ℕ)) ∧
      ∀ i : Fin d, c₀ i = (∏ l, (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ)).coeff (i : ℕ) := by
  classical
  intro P
  have hPmon : P.Monic := Polynomial.monic_monicOfCoeff c₀
  have hPdeg : P.natDegree = d := Polynomial.natDegree_monicOfCoeff c₀
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hsum_roots : ∑ a ∈ P.roots.toFinset, P.roots.count a = d := by
    rw [Multiset.toFinset_sum_count_eq, ← hsplit.natDegree_eq_card_roots, hPdeg]
  have hpos_mem {a : ℂ} (ha : a ∈ P.roots.toFinset) : 0 < P.roots.count a :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ha)
  have hcard_le : P.roots.toFinset.card ≤ d := by
    calc P.roots.toFinset.card = ∑ _a ∈ P.roots.toFinset, 1 := by simp
      _ ≤ ∑ a ∈ P.roots.toFinset, P.roots.count a := Finset.sum_le_sum fun a ha ↦ hpos_mem ha
      _ = d := hsum_roots
  let e : Fin P.roots.toFinset.card ≃ P.roots.toFinset :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe P.roots.toFinset)).symm
  let r : Fin (d + 1) := ⟨P.roots.toFinset.card, Nat.lt_succ_of_le hcard_le⟩
  have hm_le (l : Fin (r : ℕ)) : P.roots.count (e l : ℂ) ≤ d := by
    rw [← hsum_roots]
    exact Finset.single_le_sum (f := fun a ↦ P.roots.count a) (fun _ _ ↦ Nat.zero_le _) (e l).2
  let m : Fin (r : ℕ) → Fin (d + 1) := fun l ↦
    ⟨P.roots.count (e l : ℂ), Nat.lt_succ_of_le (hm_le l)⟩
  let z : Fin (r : ℕ) → ℂ := fun l ↦ (e l : ℂ)
  have hsum_m : ∑ l : Fin (r : ℕ), (m l : ℕ) = d := by
    calc ∑ l : Fin (r : ℕ), (m l : ℕ)
        = ∑ x : P.roots.toFinset, P.roots.count (x : ℂ) :=
          e.sum_comp (fun x : P.roots.toFinset ↦ P.roots.count (x : ℂ))
      _ = ∑ a ∈ P.roots.toFinset, P.roots.count a :=
          Finset.sum_coe_sort P.roots.toFinset (fun a ↦ P.roots.count a)
      _ = d := hsum_roots
  have hprod_eq : (∏ l : Fin (r : ℕ), (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ)) = P := by
    calc (∏ l : Fin (r : ℕ), (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ))
        = ∏ x : P.roots.toFinset, (Polynomial.X - Polynomial.C (x : ℂ)) ^ P.roots.count (x : ℂ) :=
          e.prod_comp (fun x : P.roots.toFinset ↦
            (Polynomial.X - Polynomial.C (x : ℂ)) ^ P.roots.count (x : ℂ))
      _ = ∏ a ∈ P.roots.toFinset, (Polynomial.X - Polynomial.C a) ^ P.roots.count a :=
          Finset.prod_coe_sort P.roots.toFinset
            (fun a ↦ (Polynomial.X - Polynomial.C a) ^ P.roots.count a)
      _ = (P.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod :=
          (Finset.prod_multiset_map_count P.roots _).symm
      _ = P := (hsplit.eq_prod_roots_of_monic hPmon).symm
  refine ⟨r, m, z, ⟨fun l ↦ hpos_mem (e l).2, hsum_m⟩, fun l ↦ ?_, fun l l' hne hzz ↦ hne ?_,
    fun l ↦ (Polynomial.count_roots P).symm, fun i ↦ ?_⟩
  · exact hroots (z l) ((Polynomial.mem_roots hPmon.ne_zero).mp
      (Multiset.mem_toFinset.mp (e l).2))
  · exact e.injective (Subtype.ext hzz)
  · rw [hprod_eq, Polynomial.coeff_monicOfCoeff]

/-- Conversely, any pairwise distinct tuple `z` whose root multiplicities in `P = monicOfCoeff c₀`
sum to `d` uniquely determines the lower coefficients `c₀`. -/
private theorem eq_of_rootCluster_monicOfCoeff {d : ℕ} {c₀ c' : Fin d → ℂ}
    {r : Fin (d + 1)} {m : Fin (r : ℕ) → Fin (d + 1)} {z : Fin (r : ℕ) → ℂ}
    (hm_sum : ∑ l, (m l : ℕ) = d) (hpair : Pairwise (fun l l' ↦ z l ≠ z l'))
    (hmult : ∀ l, (Polynomial.monicOfCoeff c₀).rootMultiplicity (z l) = (m l : ℕ))
    (hcoeff : ∀ i : Fin d,
      c' i = (∏ l, (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ)).coeff (i : ℕ)) :
    c' = c₀ := by
  let P := Polynomial.monicOfCoeff c₀
  let Q : ℂ[X] := ∏ l : Fin (r : ℕ), (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ)
  have hQmon : Q.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun l _ ↦ (Polynomial.monic_X_sub_C (z l)).pow _
  have hQdeg : Q.natDegree = d := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun l _ ↦ (Polynomial.monic_X_sub_C (z l)).pow _]
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    exact hm_sum
  have hcop : Pairwise (IsCoprime on fun l : Fin (r : ℕ) ↦
      (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ)) :=
    fun l l' hne ↦ (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr (hpair hne)).isUnit).pow
  have hdvd : Q ∣ P := Fintype.prod_dvd_of_coprime hcop fun l ↦ by
    rw [← hmult l]
    exact Polynomial.pow_rootMultiplicity_dvd P (z l)
  have hPQ : P = ∏ l : Fin (r : ℕ), (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hQmon
      (Polynomial.monic_monicOfCoeff c₀) hdvd (by rw [Polynomial.natDegree_monicOfCoeff, hQdeg])
  funext i
  rw [hcoeff i, ← hPQ, Polynomial.coeff_monicOfCoeff]

end RootCluster

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
    simp only [Polynomial.eval_monicOfCoeff]
    have hsub : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z (Sum.inr ()) - (t₀ : ℂ)) z₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inr ())).analyticAt z₀)
        |>.fun_sub analyticAt_const
    exact ((hsub.pow d).fun_add (Finset.analyticAt_fun_sum Finset.univ fun i _ ↦
      (hC_sum i).fun_mul (hsub.pow (i : ℕ)))).fun_mul (hU z₀ (mem_ball_self hrU))
  refine (hFV z₀ hz₀V).eventuallyEq_of_eventually_real hRHS_an ?_
  have hp_real : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ (fun j ↦ (p j : ℂ))) (𝓝 p₀) (𝓝 z₀) :=
    tendsto_pi_nhds.mpr fun j ↦
      Complex.continuous_ofReal.continuousAt.comp ((continuous_apply j).continuousAt)
  have hp_prod : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ (p ∘ Sum.inl, p (Sum.inr ())))
      (𝓝 p₀) (𝓝 (x₀, t₀)) := (prodRealEquivSumUnit σ).symm.continuous.tendsto p₀
  have hp_inl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, t₀)).comp hp_prod
  filter_upwards [hp_real.eventually (hVo.mem_nhds hz₀V), ball_mem_nhds p₀ hrU,
    hp_prod.eventually hfac, hp_inl.eventually hCc_ev] with p hpV hpU hpf hpC
  have hp_eta : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (Sum.inr ())) = p := by
    ext (i | ⟨⟩) <;> rfl
  rw [hp_eta] at hpf
  rw [hFr p hpV, hpf, Complex.ofReal_mul, ← hUr p hpU]
  congr 1
  simp only [Polynomial.eval_monicOfCoeff, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hci : C i ((fun j ↦ (p j : ℂ)) ∘ Sum.inl) = (c i (p ∘ Sum.inl) : ℂ) := hpC i
  rw [hci]

/-- Shrinking to a polydisc `ball x₀ δ × ball t₀ R` where the complexification `F` of a Nash germ
`f` has semialgebraic vertical derivatives, the complexified Weierstrass unit is nonvanishing, and
all complex roots of `monicOfCoeff (c · x)` lie in `ball 0 R` with multiplicity equal to the
analytic order of `F (x, ·)`. -/
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
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let z₀ : σ ⊕ Unit → ℂ := fun j ↦ (p₀ j : ℂ)
  obtain ⟨V, hVo, hz₀V, -, -, -, F, hFV, hFr, -, hFS⟩ := hf.exists_complexification univ_mem
  choose ρ hρ C hC hCc _ using fun i ↦ (hc i).exists_complexification
  have hu_sum : AnalyticAt ℝ (fun p : σ ⊕ Unit → ℝ ↦ u (p ∘ Sum.inl, p (Sum.inr ()))) p₀ :=
    hu.comp_of_eq ((prodRealEquivSumUnit σ).symm.analyticAt p₀) rfl
  obtain ⟨rU, hrU, U, hU, hUr, -⟩ := hu_sum.exists_complexification
  have hCc_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun j ↦ (x j : ℂ)) = c i x :=
    eventually_all.mpr fun i ↦ Filter.mem_of_superset (ball_mem_nhds x₀ (hρ i)) (hCc i)
  have hF_eq := eventuallyEq_complexification_weierstrassPreparation hVo hz₀V hFV hFr
    (fun i ↦ hC i _ (mem_ball_self (hρ i))) hCc_ev hrU hU hUr hfac
  have hUz₀ : U z₀ ≠ 0 := by
    rw [hUr p₀ (mem_ball_self hrU)]
    exact Complex.ofReal_ne_zero.mpr hu0
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
    have hmem : F (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w)) = _ :=
      (hballZ (hz_mem w hw)).2.2
    simpa only [Sum.elim_comp_inl, Sum.elim_inr, hCP, P] using hmem
  have hU_slice_an : AnalyticAt ℂ
      (fun w ↦ U (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w))) ((t₀ : ℂ) + ζ) := by
    have hemb : AnalyticAt ℂ (fun w : ℂ ↦ Sum.elim (fun i ↦ (x i : ℂ)) (fun _ : Unit ↦ w))
        ((t₀ : ℂ) + ζ) :=
      analyticAt_pi_iff.mpr fun j ↦ by
        cases j with
        | inl _ => exact analyticAt_const
        | inr _ => exact analyticAt_id
    exact (hU _ (hballZ hz₀_pt).1.2).comp_of_eq hemb rfl
  have htr : AnalyticAt ℂ (fun w : ℂ ↦ w - (t₀ : ℂ)) ((t₀ : ℂ) + ζ) :=
    analyticAt_id.fun_sub analyticAt_const
  have hP_slice_an : AnalyticAt ℂ (fun w ↦ P.eval (w - (t₀ : ℂ))) ((t₀ : ℂ) + ζ) :=
    ((AnalyticOnNhd.eval_polynomial P) _ trivial).comp htr
  have htr' : deriv (fun w : ℂ ↦ w - (t₀ : ℂ)) ((t₀ : ℂ) + ζ) ≠ 0 := by
    rw [deriv_sub_const, deriv_id'']; exact one_ne_zero
  have hP_ord : analyticOrderAt (fun w ↦ P.eval (w - (t₀ : ℂ))) ((t₀ : ℂ) + ζ) =
      (P.rootMultiplicity ζ : ℕ∞) := by
    have hP_ne : P ≠ 0 := (Polynomial.monic_monicOfCoeff _).ne_zero
    have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := fun u ↦ P.eval u) htr htr'
    have htr0 : (t₀ : ℂ) + ζ - (t₀ : ℂ) = ζ := add_sub_cancel_left _ _
    rw [Function.comp_def, htr0, Polynomial.analyticOrderAt_eval hP_ne] at hcomp
    exact hcomp
  have hU_ord : analyticOrderAt
      (fun w ↦ U (Sum.elim (fun i ↦ (x i : ℂ)) (fun _ ↦ w))) ((t₀ : ℂ) + ζ) = 0 :=
    hU_slice_an.analyticOrderAt_eq_zero.mpr (hballZ hz₀_pt).2.1
  rw [analyticOrderAt_congr hslice_eq]
  exact (analyticOrderAt_mul hP_slice_an hU_slice_an).trans (by rw [hP_ord, hU_ord, add_zero])

/-- On `ball x₀ δ`, each fixed root-cluster shape `(r, m)` defines a semialgebraic relation on
`(x, c')` after projecting out the `r` complex root coordinates. -/
private theorem isSemialgebraic_rootCluster_branch {d : ℕ} {V : Set (σ ⊕ Unit → ℂ)}
    {F : (σ ⊕ Unit → ℂ) → ℂ} (hVo : IsOpen V) (hFV : AnalyticOnNhd ℂ F V)
    (hFS : IsSemialgebraicOn
      (fun a ↦ complexToRealPi Unit (fun _ ↦ F ((complexToRealPi (σ ⊕ Unit)).symm a)))
      ((complexToRealPi (σ ⊕ Unit)).symm ⁻¹' V))
    (x₀ : σ → ℝ) (t₀ R δ : ℝ) (r : Fin (d + 1)) (m : Fin (r : ℕ) → Fin (d + 1)) :
    IsSemialgebraic {w : σ ⊕ Fin d → ℝ |
      ((∀ l, 0 < (m l : ℕ)) ∧ ∑ l, (m l : ℕ) = d) ∧
      w ∘ Sum.inl ∈ ball x₀ δ ∧
      ∃ y : Fin (r : ℕ) ⊕ Fin (r : ℕ) → ℝ,
        let z : Fin (r : ℕ) → ℂ := fun l ↦ (y (.inl l) : ℂ) + (y (.inr l) : ℂ) * Complex.I
        (∀ l, (y (.inl l)) ^ 2 + (y (.inr l)) ^ 2 < R ^ 2) ∧
        (∀ l l', l ≠ l' → z l ≠ z l') ∧
        (∀ l,
          Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l) ∈ V ∧
          (∀ k : Fin (m l : ℕ), complexVertDeriv k F
            (Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l)) = 0) ∧
          complexVertDeriv (m l : ℕ) F
            (Sum.elim (fun i ↦ (w (.inl i) : ℂ)) (fun _ ↦ (t₀ : ℂ) + z l)) ≠ 0) ∧
        ∀ i : Fin d, (w (.inr i) : ℂ) =
          (∏ l, (Polynomial.X - Polynomial.C (z l)) ^ (m l : ℕ)).coeff (i : ℕ)} := by
  by_cases hm : (∀ l, 0 < (m l : ℕ)) ∧ ∑ l, (m l : ℕ) = d
  · let ν := (σ ⊕ Fin d) ⊕ (Fin (r : ℕ) ⊕ Fin (r : ℕ))
    let xP : σ → MvPolynomial ν ℝ := fun i ↦ MvPolynomial.X (.inl (.inl i))
    let zRe : Fin (r : ℕ) → MvPolynomial ν ℝ := fun l ↦ MvPolynomial.X (.inr (.inl l))
    let zIm : Fin (r : ℕ) → MvPolynomial ν ℝ := fun l ↦ MvPolynomial.X (.inr (.inr l))
    let Z : Fin (r : ℕ) → MvPolynomial ν ℂ := fun l ↦
      MvPolynomial.X (.inr (.inl l)) + MvPolynomial.X (.inr (.inr l)) * MvPolynomial.C Complex.I
    have hZ_eval (v : ν → ℝ) (l : Fin (r : ℕ)) :
        MvPolynomial.eval (fun s ↦ (v s : ℂ)) (Z l) =
          (v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I := by
      simp [Z]
    have hS_norm : IsSemialgebraic {v : ν → ℝ |
        ∀ l, (v (.inr (.inl l))) ^ 2 + (v (.inr (.inr l))) ^ 2 < R ^ 2} := by
      convert IsSemialgebraic.iInter (fun l : Fin (r : ℕ) ↦
        isSemialgebraic_eval_lt (zRe l ^ 2 + zIm l ^ 2) (MvPolynomial.C (R ^ 2))) using 1
      ext v
      simp [zRe, zIm]
    have hS_pair : IsSemialgebraic {v : ν → ℝ | ∀ l l' : Fin (r : ℕ), l ≠ l' →
        (v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I ≠
          (v (.inr (.inl l')) : ℂ) + (v (.inr (.inr l')) : ℂ) * Complex.I} := by
      let Spair (l l' : Fin (r : ℕ)) : Set (ν → ℝ) :=
        if l ≠ l' then {v | MvPolynomial.eval (fun s ↦ (v s : ℂ)) (Z l - Z l') = 0}ᶜ else univ
      have hSpair (l l' : Fin (r : ℕ)) : IsSemialgebraic (Spair l l') := by
        dsimp only [Spair]
        split_ifs
        · exact (isSemialgebraic_setOf_eval_ofReal_eq_zero (Z l - Z l')).compl
        · exact isSemialgebraic_univ
      convert IsSemialgebraic.iInter (fun l ↦ IsSemialgebraic.iInter fun l' ↦ hSpair l l') using 1
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Spair]
      refine forall_congr' fun l ↦ forall_congr' fun l' ↦ ?_
      by_cases hll : l ≠ l' <;> simp [hll, hZ_eval, sub_eq_zero]
    have h_eq (l : Fin (r : ℕ)) (k : ℕ) := isSemialgebraic_setOf_complexVertDeriv_eq_and_ne_zero
      (analyticOnNhd_and_isSemialgebraicOn_complexVertDeriv hVo hFV hFS k).2
      xP (MvPolynomial.C t₀ + zRe l) (zIm l)
    have hS_mult : IsSemialgebraic {v : ν → ℝ | ∀ l : Fin (r : ℕ),
        let pt := Sum.elim (fun i ↦ (v (.inl (.inl i)) : ℂ))
          (fun _ ↦ (t₀ : ℂ) + ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I))
        pt ∈ V ∧ (∀ k : Fin (m l : ℕ), complexVertDeriv k F pt = 0) ∧
          complexVertDeriv (m l : ℕ) F pt ≠ 0} := by
      convert IsSemialgebraic.iInter (fun l : Fin (r : ℕ) ↦
        (IsSemialgebraic.iInter fun k : Fin (m l : ℕ) ↦ (h_eq l k).1).inter
          (h_eq l (m l : ℕ)).2) using 1
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, xP, zRe, zIm, map_add,
        MvPolynomial.eval_C, MvPolynomial.eval_X, Complex.ofReal_add, add_assoc]
      refine forall_congr' fun _ ↦ ?_
      exact ⟨fun ⟨hV, hk0, hkne⟩ ↦ ⟨fun k ↦ ⟨hV, hk0 k⟩, hV, hkne⟩,
        fun ⟨hk0, hV, hkne⟩ ↦ ⟨hV, fun k ↦ (hk0 k).2, hkne⟩⟩
    let Qpoly : Polynomial (MvPolynomial ν ℂ) :=
      ∏ l : Fin (r : ℕ), (Polynomial.X - Polynomial.C (Z l)) ^ (m l : ℕ)
    have hS_coeff : IsSemialgebraic {v : ν → ℝ | ∀ i : Fin d, (v (.inl (.inr i)) : ℂ) =
        (∏ l : Fin (r : ℕ),
          (Polynomial.X - Polynomial.C
            ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I)) ^ (m l : ℕ)).coeff
          (i : ℕ)} := by
      convert IsSemialgebraic.iInter (fun i : Fin d ↦
        isSemialgebraic_setOf_eval_ofReal_eq_zero
          (MvPolynomial.X (.inl (.inr i)) - Qpoly.coeff (i : ℕ))) using 1
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, map_sub, MvPolynomial.eval_X, sub_eq_zero]
      refine forall_congr' fun i ↦ Eq.congr_right ?_
      have hmap : Qpoly.map (MvPolynomial.eval fun s ↦ (v s : ℂ)) =
          ∏ l : Fin (r : ℕ), (Polynomial.X - Polynomial.C
            ((v (.inr (.inl l)) : ℂ) + (v (.inr (.inr l)) : ℂ) * Complex.I)) ^ (m l : ℕ) := by
        simp [Qpoly, Polynomial.map_prod, hZ_eval]
      simpa only [Polynomial.coeff_map] using
        (congrArg (fun p : ℂ[X] ↦ p.coeff (i : ℕ)) hmap).symm
    have hproj := (((hS_norm.inter hS_pair).inter hS_mult).inter hS_coeff).setOf_exists_sumElim
    convert ((isSemialgebraic_ball x₀ δ).preimage_comp Sum.inl).inter hproj using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun ⟨_, hx, y, hy⟩ ↦ ⟨hx, y, ⟨⟨⟨hy.1, hy.2.1⟩, hy.2.2.1⟩, hy.2.2.2⟩⟩,
      fun ⟨hx, y, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩ ↦ ⟨hm, hx, y, h1, h2, h3, h4⟩⟩
  · convert isSemialgebraic_empty using 1
    ext w
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hm', -⟩
    exact hm hm'

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
  obtain ⟨V, F, R, δ, hVo, hFV, hFS, hR, hδ, hord, hroots⟩ :=
    exists_polydisc_weierstrass_rootMultiplicity hf hc hc0 hu hu0 hfac
  refine (forall_isNashAt_apply_iff_exists_isSemialgebraicOn (g := fun x j ↦ c j x)).mpr
    ⟨AnalyticAt.pi hc, ball x₀ δ, isOpen_ball, mem_ball_self hδ, ?_⟩ i
  refine isSemialgebraicOn_def.mpr ⟨isSemialgebraic_ball x₀ δ, ?_⟩
  convert IsSemialgebraic.iUnion (fun r : Fin (d + 1) ↦
    IsSemialgebraic.iUnion fun m : Fin (r : ℕ) → Fin (d + 1) ↦
      isSemialgebraic_rootCluster_branch hVo hFV hFS x₀ t₀ R δ r m) using 1
  ext w
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_iUnion, mem_ofPred_eq]
  let x := w ∘ Sum.inl
  constructor
  · rintro ⟨hx, hcx⟩
    obtain ⟨r, m, z, hm, hzR, hpair, hmult, hcoeff⟩ :=
      exists_rootCluster_of_monicOfCoeff (c₀ := fun j ↦ (c j x : ℂ)) (hroots x hx)
    refine ⟨r, m, hm, hx, Sum.elim (fun l ↦ (z l).re) (fun l ↦ (z l).im), ?_, ?_, ?_, ?_⟩
    · intro l
      have hzl := hzR l
      rw [← sq_lt_sq₀ (norm_nonneg _) hR.le, Complex.sq_norm, normSq_apply] at hzl
      simpa only [Sum.elim_inl, Sum.elim_inr, sq] using hzl
    · intro l l' hne
      simpa only [Sum.elim_inl, Sum.elim_inr, Complex.re_add_im] using hpair hne
    · intro l
      simp only [Sum.elim_inl, Sum.elim_inr, Complex.re_add_im]
      obtain ⟨hptV, hord_eq⟩ := hord x hx (z l) (hzR l)
      have hslice_an : AnalyticAt ℂ
          (fun ζ ↦ F (Sum.elim (fun j ↦ (x j : ℂ)) (fun _ ↦ ζ))) ((t₀ : ℂ) + z l) :=
        (hFV _ hptV).comp_of_eq (analyticAt_pi_iff.mpr fun j ↦ by
          cases j with | inl _ => exact analyticAt_const | inr _ => exact analyticAt_id)
          (by ext (j | ⟨⟩) <;> rfl)
      have hderiv_iff := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hslice_an).mp
        (hord_eq.trans (congrArg Nat.cast (hmult l)))
      exact ⟨hptV, fun k ↦ hderiv_iff.1 k k.2, hderiv_iff.2⟩
    · intro j
      simp only [Sum.elim_inl, Sum.elim_inr, Complex.re_add_im]
      have hcj : w (.inr j) = c j x := (congrFun hcx j).symm
      rw [hcj]
      exact hcoeff j
  · rintro ⟨r, m, hm, hx, y, hyR, hpair, hderiv, hcoeff⟩
    refine ⟨hx, ?_⟩
    let z : Fin (r : ℕ) → ℂ := fun l ↦ (y (.inl l) : ℂ) + (y (.inr l) : ℂ) * Complex.I
    have hzR (l : Fin (r : ℕ)) : ‖z l‖ < R := by
      have hsq : ‖z l‖ ^ 2 < R ^ 2 := by
        rw [Complex.sq_norm, normSq_apply]
        simpa [z, sq] using hyR l
      exact lt_of_pow_lt_pow_left₀ 2 hR.le hsq
    have hmult (l : Fin (r : ℕ)) :
        (Polynomial.monicOfCoeff (fun j ↦ (c j x : ℂ))).rootMultiplicity (z l) = (m l : ℕ) := by
      obtain ⟨hptV, hk0, hkne⟩ := hderiv l
      obtain ⟨-, hord_eq⟩ := hord x hx (z l) (hzR l)
      have hslice_an : AnalyticAt ℂ
          (fun ζ ↦ F (Sum.elim (fun j ↦ (x j : ℂ)) (fun _ ↦ ζ))) ((t₀ : ℂ) + z l) :=
        (hFV _ hptV).comp_of_eq (analyticAt_pi_iff.mpr fun j ↦ by
          cases j with | inl _ => exact analyticAt_const | inr _ => exact analyticAt_id)
          (by ext (j | ⟨⟩) <;> rfl)
      have hord_m : analyticOrderAt
          (fun ζ ↦ F (Sum.elim (fun j ↦ (x j : ℂ)) (fun _ ↦ ζ))) ((t₀ : ℂ) + z l) = (m l : ℕ) :=
        (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hslice_an).mpr
          ⟨fun k hk ↦ hk0 ⟨k, hk⟩, hkne⟩
      exact Nat.cast_injective (R := ℕ∞) (hord_eq.symm.trans hord_m)
    have heq_c := eq_of_rootCluster_monicOfCoeff (c₀ := fun j ↦ (c j x : ℂ))
      (c' := fun j ↦ (w (.inr j) : ℂ)) hm.2 (fun l l' hne ↦ hpair l l' hne) hmult hcoeff
    funext j
    exact Complex.ofReal_injective (congrFun heq_c j).symm

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
  let fProd : (σ → ℝ) × ℝ → ℝ := fun q ↦ f (Sum.elim q.1 (fun _ ↦ q.2))
  have hf_prod : AnalyticAt ℝ fProd (x₀, t₀) :=
    hf.analyticAt.comp_of_eq (E.analyticAt (x₀, t₀)) rfl
  have hd_prod : analyticOrderAt (fun t ↦ fProd (x₀, t)) t₀ = d := hd
  obtain ⟨c, u₀, hc_an, hc0, hu₀_an, hu₀_ne, hfac_prod⟩ :=
    hf_prod.exists_weierstrassPreparation_real hd_prod
  have hc_nash (i : Fin d) : IsNashAt (c i) x₀ :=
    isNashAt_weierstrassPreparation_coeff hf hc_an hc0 hu₀_an hu₀_ne hfac_prod i
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let u : (σ ⊕ Unit → ℝ) → ℝ := fun p ↦ u₀ (E.symm p)
  have hu_an : AnalyticAt ℝ u p₀ := hu₀_an.comp_of_eq (E.symm.analyticAt p₀) rfl
  have hfac : f =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p := by
    filter_upwards [(E.symm.continuous.tendsto p₀).eventually hfac_prod] with p hp
    have heta : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (Sum.inr ())) = p := by
      ext (i | ⟨⟩) <;> rfl
    have hEsymm : E.symm p = (p ∘ Sum.inl, p (Sum.inr ())) := rfl
    dsimp only [fProd] at hp
    rw [hEsymm, heta] at hp
    exact hp
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
  exact ⟨c, u, hc_nash, hc0, hf.of_eventuallyEq_mul_left hP_nash hP_ne0 hu_an hfac, hu₀_ne, hfac⟩

/-- Uniqueness of the local real analytic Weierstrass preparation in `σ ⊕ Unit → ℝ` coordinates. -/
theorem eventuallyEq_of_weierstrassPreparation_sumElim {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    {c c' : Fin d → (σ → ℝ) → ℝ} {u u' : (σ ⊕ Unit → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀))) (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hc' : ∀ i, AnalyticAt ℝ (c' i) x₀) (hc'0 : ∀ i, c' i x₀ = 0)
    (hu' : AnalyticAt ℝ u' (Sum.elim x₀ (fun _ ↦ t₀))) (hu'0 : u' (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (h : (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p)
      =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))]
      fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c' i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) *
          u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] u' := by
  let E := prodRealEquivSumUnit σ
  have hE : E (x₀, t₀) = Sum.elim x₀ (fun _ ↦ t₀) := rfl
  obtain ⟨hcc', huu'⟩ := eventuallyEq_of_weierstrassPreparation_real (x₀ := x₀) (t₀ := t₀) hc hc0
    (hu.comp_of_eq (E.analyticAt (x₀, t₀)) hE) hu0
    hc' hc'0 (hu'.comp_of_eq (E.analyticAt (x₀, t₀)) hE) hu'0
    ((E.continuous.tendsto (x₀, t₀)).eventually h)
  refine ⟨hcc', ?_⟩
  filter_upwards [(E.symm.continuous.tendsto (Sum.elim x₀ (fun _ ↦ t₀))).eventually huu']
    with p hp
  simpa only [Function.comp_apply, E.apply_symm_apply] using hp

/-- Uniqueness of the local real analytic Weierstrass division in `σ ⊕ Unit → ℝ` coordinates. -/
theorem eventuallyEq_of_weierstrassDivision_sumElim {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {q q' : (σ ⊕ Unit → ℝ) → ℝ} {r r' : Fin d → (σ → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀))) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hq' : AnalyticAt ℝ q' (Sum.elim x₀ (fun _ ↦ t₀))) (hr' : ∀ i, AnalyticAt ℝ (r' i) x₀)
    (h : (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ))
      =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))]
      fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q' p +
          ∑ i : Fin d, r' i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  let E := prodRealEquivSumUnit σ
  have hE : E (x₀, t₀) = Sum.elim x₀ (fun _ ↦ t₀) := rfl
  obtain ⟨hqq', hrr'⟩ := eventuallyEq_of_weierstrassDivision_real (x₀ := x₀) (t₀ := t₀) hc hc0
    (hq.comp_of_eq (E.analyticAt (x₀, t₀)) hE) hr
    (hq'.comp_of_eq (E.analyticAt (x₀, t₀)) hE) hr'
    ((E.continuous.tendsto (x₀, t₀)).eventually h)
  refine ⟨?_, hrr'⟩
  filter_upwards [(E.symm.continuous.tendsto (Sum.elim x₀ (fun _ ↦ t₀))).eventually hqq']
    with p hp
  simpa only [Function.comp_apply, E.apply_symm_apply] using hp

end Preparation

/-! ### Nash Weierstrass division -/

section Division

variable {σ : Type*} [Fintype σ]

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
  have hd_lhs : HasDerivAt
      (fun s : ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) - s * g p)
      (- g p) 0 := by
    have hd_mul := ((hasDerivAt_id (0 : ℝ)).mul_const (g p)).const_sub
      ((Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀))
    rwa [one_mul] at hd_mul
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
  have hd_rhs := hd_P.mul hd_U
  have hP0_eq : (Polynomial.monicOfCoeff (fun i ↦ A i y₀)).eval (t - t₀) =
      (Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) := by
    congr 1; congr 1; funext i; exact hA0 i
  have heq_deriv : - g p =
      (∑ i : Fin d, fderiv ℝ (A i) y₀ vA * (t - t₀) ^ (i : ℕ)) * U q₀ +
        (Polynomial.monicOfCoeff (fun i ↦ A i y₀)).eval (t - t₀) * fderiv ℝ U q₀ vU :=
    (hd_lhs.congr_of_eventuallyEq (heq.mono fun _ hs ↦ hs.symm)).unique hd_rhs
  rw [hU0, hP0_eq, mul_one] at heq_deriv
  have hneg := congrArg Neg.neg heq_deriv
  rw [neg_neg, neg_add] at hneg
  rw [hneg, add_comm]
  congr 1
  · ring
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

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
  let H : ((σ ⊕ Unit) ⊕ Unit → ℝ) → ℝ := fun q ↦
    (Polynomial.monicOfCoeff (fun i ↦ c i ((q ∘ Sum.inl) ∘ Sum.inl))).eval (q (Sum.inr ()) - t₀) -
      q (.inl (.inr ())) * g (Sum.elim ((q ∘ Sum.inl) ∘ Sum.inl) (fun _ ↦ q (Sum.inr ())))
  have hH_nash : IsNashAt H q₀ := by
    have hP : IsNashAt (fun q : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i ((q ∘ Sum.inl) ∘ Sum.inl))).eval
          (q (Sum.inr ()) - t₀)) q₀ :=
      IsNashAt.eval_monicOfCoeff
        (fun i ↦ (hc i).comp fun j ↦ isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inl (.inl j)))
        ((isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inr ())).fun_sub (isNashAt_const t₀))
    have hg_comp : IsNashAt (fun q : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        g (Sum.elim ((q ∘ Sum.inl) ∘ Sum.inl) (fun _ ↦ q (Sum.inr ())))) q₀ := by
      refine hg.comp (g := fun q : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        Sum.elim ((q ∘ Sum.inl) ∘ Sum.inl) (fun _ ↦ q (Sum.inr ()))) ?_
      rintro (j | ⟨⟩)
      · exact isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inl (.inl j))
      · exact isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inr ())
    exact hP.fun_sub ((isNashAt_apply (σ := (σ ⊕ Unit) ⊕ Unit) (.inl (.inr ()))).fun_mul hg_comp)
  have hH_ord : analyticOrderAt (fun t ↦ H (Sum.elim y₀ (fun _ ↦ t))) t₀ = d := by
    have hslice : (fun t : ℝ ↦ H (Sum.elim y₀ (fun _ ↦ t))) =
        fun t ↦ ((Polynomial.X - Polynomial.C t₀) ^ d).eval t := by
      funext t
      simp [H, y₀, Polynomial.eval_monicOfCoeff, hc0]
    rw [hslice, Polynomial.analyticOrderAt_eval (pow_ne_zero d (Polynomial.X_sub_C_ne_zero t₀)),
      Polynomial.rootMultiplicity_X_sub_C_pow]
  obtain ⟨A, U, hA, hA0, hU, hU0, hH_prep⟩ := hH_nash.exists_weierstrassPreparation hH_ord
  let ιY : (σ → ℝ) → (σ ⊕ Unit → ℝ) := fun x ↦ Sum.elim x (fun _ ↦ 0)
  let ιQ : (σ ⊕ Unit → ℝ) → ((σ ⊕ Unit) ⊕ Unit → ℝ) :=
    fun p ↦ Sum.elim (ιY (p ∘ Sum.inl)) (fun _ ↦ p (Sum.inr ()))
  have hιY_an (x : σ → ℝ) : AnalyticAt ℝ ιY x :=
    analyticAt_pi_iff.mpr fun j ↦ by
      cases j with
      | inl i => exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) i).analyticAt x
      | inr _ => exact analyticAt_const
  have hιQ_an (p : σ ⊕ Unit → ℝ) : AnalyticAt ℝ ιQ p :=
    analyticAt_pi_iff.mpr fun j ↦ by
      rcases j with (i | ⟨⟩) | ⟨⟩
      · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (.inl i)).analyticAt p
      · exact analyticAt_const
      · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (.inr ())).analyticAt p
  have hιQ_p₀ : ιQ p₀ = q₀ := by ext ((i | ⟨⟩) | ⟨⟩) <;> rfl
  have hιQ_tendsto : Tendsto ιQ (𝓝 p₀) (𝓝 q₀) := by
    rw [← hιQ_p₀]
    exact (hιQ_an p₀).continuousAt
  have hslice0 : (fun p : σ ⊕ Unit → ℝ ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * 1)
      =ᶠ[𝓝 p₀]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ A i (ιY (p ∘ Sum.inl)))).eval
        (p (Sum.inr ()) - t₀) * U (ιQ p) := by
    filter_upwards [hιQ_tendsto.eventually hH_prep] with p hp
    simpa [H, ιQ, ιY] using hp
  have hU_p₀ : U (ιQ p₀) ≠ 0 := by
    rw [hιQ_p₀]
    exact hU0
  obtain ⟨hcA, h1U⟩ := eventuallyEq_of_weierstrassPreparation_sumElim
    (fun i ↦ (hc i).analyticAt) hc0 analyticAt_const one_ne_zero
    (fun i ↦ (hA i).analyticAt.comp_of_eq (hιY_an x₀) rfl) (fun i ↦ hA0 i)
    (hU.analyticAt.comp_of_eq (hιQ_an p₀) hιQ_p₀) hU_p₀ hslice0
  let vA : σ ⊕ Unit → ℝ := Sum.elim 0 (fun _ ↦ 1)
  let vU : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim vA (fun _ ↦ 0)
  let q : (σ ⊕ Unit → ℝ) → ℝ := fun p ↦ - fderiv ℝ U (ιQ p) vU
  let r : Fin d → (σ → ℝ) → ℝ := fun i x ↦ - fderiv ℝ (A i) (ιY x) vA
  have hq_nash : IsNashAt q p₀ := by
    have hUf : IsNashAt (fun z ↦ - fderiv ℝ U z vU) (ιQ p₀) := by
      rw [hιQ_p₀]
      exact (hU.fderiv_apply vU).fun_neg
    refine hUf.comp (g := ιQ) ?_
    rintro ((i | ⟨⟩) | ⟨⟩)
    · exact isNashAt_apply (σ := σ ⊕ Unit) (.inl i)
    · exact isNashAt_const 0
    · exact isNashAt_apply (σ := σ ⊕ Unit) (.inr ())
  have hr_nash (i : Fin d) : IsNashAt (r i) x₀ := by
    have hAf : IsNashAt (fun y ↦ - fderiv ℝ (A i) y vA) (ιY x₀) :=
      ((hA i).fderiv_apply vA).fun_neg
    refine hAf.comp (g := ιY) ?_
    rintro (j | ⟨⟩)
    · exact isNashAt_apply (σ := σ) j
    · exact isNashAt_const 0
  refine ⟨q, r, hq_nash, hr_nash, ?_⟩
  have hinl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_pi fun i : σ ↦ continuous_apply (Sum.inl i)).tendsto p₀
  have hιY_p : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ ιY (p ∘ Sum.inl)) (𝓝 p₀) (𝓝 y₀) :=
    (hιY_an x₀).continuousAt.tendsto.comp hinl
  have hιQ_p : Tendsto ιQ (𝓝 p₀) (𝓝 q₀) := hιQ_p₀ ▸ (hιQ_an p₀).continuousAt
  filter_upwards [
    hιY_p.eventually (eventually_all.mpr fun i ↦ (hA i).analyticAt.eventually_analyticAt),
    hιQ_p.eventually hU.analyticAt.eventually_analyticAt,
    hinl.eventually (eventually_all.mpr fun i ↦ (hcA i).symm),
    h1U.symm,
    hιQ_p.eventually hH_prep.eventually_nhds] with p hAd hUd hAc hU1 hHp
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
    have heta : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (Sum.inr ())) = p := by
      ext (i | ⟨⟩) <;> rfl
    filter_upwards [(hline_cont.tendsto 0).eventually hHp] with s hs
    simpa only [H, Sum.elim_comp_inl, Sum.elim_inl, Sum.elim_inr, heta] using hs
  exact weierstrassDivision_eq_of_perturbed_preparation
    (fun i ↦ (hAd i).differentiableAt) hUd.differentiableAt hAc hU1 hline_ev

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
