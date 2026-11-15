/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem

/-!
# Continuous dependence of the Dirichlet problem on its coefficients

For a divergence-form operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on an open set `Ω ⊆ ℝⁿ`, the
weak solution `u ∈ H¹₀(Ω)` of `L u = ℓ` depends Lipschitz continuously on the coefficients
`a, b, c` in `L^∞(Ω)` and on the forcing `ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*`, with constants governed by the
coercivity constant of the energy form. If `u` solves the problem for `(a, b, c, ℓ)`, whose energy
form `B` satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)`, and `u'` solves it for `(a', b', c', ℓ')`, then
testing both equations against `w = u - u'` gives

`C ‖u - u'‖² ≤ B(w, w) = (ℓ - ℓ')(w) - (B - B')(u', w)`,

and the difference of the energy forms is the energy form of the difference of the coefficients,
bounded by the `L^∞` bounds `Λ, β, γ` of `a - a'`, `b - b'` and `c - c'`. Hence
`‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Λ + β + γ) ‖u'‖) / C`. Only the first energy form needs to be coercive.

## Main declarations

* `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq`: the stability estimate for data in
  `H⁻¹(Ω)`.
* `TauCeti.PDE.norm_sub_le_of_isWeakSolutionDirichlet`: for a common right-hand side
  `f ∈ L²(Ω)` and coercivity constants `C, C'`, `‖u - u'‖ ≤ (Λ + β + γ) ‖f‖ / (C C')`.
* `TauCeti.PDE.tendsto_of_isWeakSolutionDirichlet`: weak solutions for coefficients converging in
  `L^∞(Ω)` to coefficients with a coercive energy form converge in `H¹₀(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.2.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, Theorem 4.1.1 (the first
  Strang lemma, the same perturbation argument for approximate forms).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped Matrix

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b b' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c c' : EuclideanSpace ℝ ι → ℝ} {C C' Lam beta gamma : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **Stability of the Dirichlet problem under perturbation of the coefficients and the data.**
Let `u ∈ H¹₀(Ω)` satisfy `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, where `B` is the energy form of
the coefficients `(a, b, c)` and satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)` with `0 < C`, and let
`u' ∈ H¹₀(Ω)` satisfy `B'(u', v) = ℓ'(v)` for the energy form `B'` of `(a', b', c')`. Suppose both
coefficient fields are essentially bounded and that almost everywhere on `Ω`
`|ηᵀ (a - a') ξ| ≤ Λ ‖η‖ ‖ξ‖`, `‖b - b'‖ ≤ β` and `|c - c'| ≤ γ`. Then
`‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Λ + β + γ) ‖u'‖) / C`.

The second energy form need not be coercive. -/
theorem norm_sub_le_of_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : 0 ≤ Lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' x) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hbeta : 0 ≤ beta) (hb : ∀ᵐ x ∂mu.restrict Omega, ‖b x - b' x‖ ≤ beta)
    (hgamma : 0 ≤ gamma) (hc : ∀ᵐ x ∂mu.restrict Omega, ‖c x - c' x‖ ≤ gamma)
    {ℓ ℓ' : StrongDual ℝ (W1p0 mu Omega 2)} {u u' : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) v = ℓ v)
    (hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a' b' c' (u' : W1p mu Omega 2) v = ℓ' v) :
    ‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Lam + beta + gamma) * ‖u'‖) / C := by
  set w := u - u'
  -- Test both equations against `w = u - u'` and compare the two energy forms at `u'`.
  have hdiff := norm_energyFormH1_le_of_bounds (a := a - a') (b := b - b') (c := c - c') hLam
    ha hb hc (u' : W1p mu Omega 2) w
  have hnorm (v : W1p0 mu Omega 2) : ‖(v : W1p mu Omega 2)‖ = ‖v‖ := Submodule.norm_coe v
  rw [energyFormH1_sub hcoeff hcoeff', hnorm, hnorm] at hdiff
  have hw : energyFormH1 a b c (w : W1p mu Omega 2) w =
      (ℓ - ℓ') w - (energyFormH1 a b c (u' : W1p mu Omega 2) w -
        energyFormH1 a' b' c' (u' : W1p mu Omega 2) w) := by
    -- The coercion of `w = u - u'` to `H¹(Ω)` is `↑u - ↑u'` by `rfl` (`Submodule.coe_sub`).
    have hsplit : energyFormH1 a b c (w : W1p mu Omega 2) w =
        energyFormH1 a b c (u : W1p mu Omega 2) w - energyFormH1 a b c (u' : W1p mu Omega 2) w :=
      energyFormH1_sub_left hcoeff (u : W1p mu Omega 2) w u'
    have hℓ : (ℓ - ℓ') w = ℓ w - ℓ' w := _root_.sub_apply ℓ ℓ' w
    linarith [hu w, hu' w]
  have hkey : C * ‖w‖ ^ 2 ≤ (‖ℓ - ℓ'‖ + (Lam + beta + gamma) * ‖u'‖) * ‖w‖ := by
    have hℓ := (le_abs_self _).trans ((ℓ - ℓ').le_opNorm w)
    have hd := (neg_le_abs _).trans hdiff
    calc C * ‖w‖ ^ 2 ≤ _ := hlower w
      _ = _ := hw
      _ ≤ ‖ℓ - ℓ'‖ * ‖w‖ + (Lam + beta + gamma) * (‖u'‖ * ‖w‖) := by linarith
      _ = _ := by ring
  rcases eq_or_lt_of_le (norm_nonneg w) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hC.le
  · rw [le_div_iff₀ hC]
    nlinarith [hkey, hpos]

/-- **Dependence of the weak solution on the coefficients.** Let `u` and `u'` be weak solutions
in `H¹₀(Ω)` of the Dirichlet problems for the two coefficient triples `(a, b, c)` and
`(a', b', c')` with the same right-hand side `f ∈ L²(Ω)`, whose energy forms are coercive on
`H¹₀(Ω)` with constants `C` and `C'`. If almost everywhere on `Ω` the differences of the
coefficients are bounded by `Λ`, `β` and `γ`, in the sense of the hypotheses of
`norm_sub_le_of_forall_energyFormH1_eq`, then `‖u - u'‖ ≤ (Λ + β + γ) ‖f‖ / (C C')`. -/
theorem norm_sub_le_of_isWeakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hC' : 0 < C')
    (hlower' : ∀ w : W1p0 mu Omega 2,
      C' * ‖w‖ ^ 2 ≤ energyFormH1 a' b' c' (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : 0 ≤ Lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' x) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hbeta : 0 ≤ beta) (hb : ∀ᵐ x ∂mu.restrict Omega, ‖b x - b' x‖ ≤ beta)
    (hgamma : 0 ≤ gamma) (hc : ∀ᵐ x ∂mu.restrict Omega, ‖c x - c' x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u u' : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) (hu' : IsWeakSolutionDirichlet a' b' c' f u') :
    ‖u - u'‖ ≤ (Lam + beta + gamma) * ‖f‖ / (C * C') := by
  have h := norm_sub_le_of_forall_energyFormH1_eq hcoeff hcoeff' hC hlower hLam ha hbeta hb
    hgamma hc hu.energyFormH1_eq_dirichletForcing hu'.energyFormH1_eq_dirichletForcing
  rw [sub_self (dirichletForcing f), ContinuousLinearMap.opNorm_zero, zero_add] at h
  have hu'f := norm_le_of_isWeakSolutionDirichlet hC' hlower' hu'
  calc ‖u - u'‖ ≤ (Lam + beta + gamma) * ‖u'‖ / C := h
    _ ≤ (Lam + beta + gamma) * (‖f‖ / C') / C := by gcongr
    _ = _ := by ring

/-- **Continuous dependence of the weak solution on the coefficients.** Let `u` be a weak
solution in `H¹₀(Ω)` of the Dirichlet problem for `(a, b, c)` with right-hand side `f ∈ L²(Ω)`,
whose energy form is coercive on `H¹₀(Ω)` with constant `C`, and let `u' i` be weak solutions for
a family of coefficient triples `(a' i, b' i, c' i)` with the same `f`. If the bounds `Λ i`, `β i`
and `γ i` on the differences `a - a' i`, `b - b' i` and `c - c' i` almost everywhere on `Ω`, in
the sense of the hypotheses of `norm_sub_le_of_forall_energyFormH1_eq`, tend to `0` along a
filter, then `u' i` tends to `u` in `H¹₀(Ω)`. The perturbed energy forms need not be coercive. -/
theorem tendsto_of_isWeakSolutionDirichlet {α : Type*} {l : Filter α}
    {a' : α → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b' : α → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c' : α → EuclideanSpace ℝ ι → ℝ} {Lam beta gamma : α → ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : ∀ i,
      MemLp (fun x => energyIntegrand (a' i x) (b' i x) (c' i x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : ∀ i, 0 ≤ Lam i)
    (ha : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' i x) *ᵥ ξ)| ≤ Lam i * ‖η‖ * ‖ξ‖)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hb : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ‖b x - b' i x‖ ≤ beta i)
    (hgamma : ∀ i, 0 ≤ gamma i)
    (hc : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ‖c x - c' i x‖ ≤ gamma i)
    (hlim : Filter.Tendsto (fun i => Lam i + beta i + gamma i) l (nhds 0))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2} {u' : α → W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u)
    (hu' : ∀ i, IsWeakSolutionDirichlet (a' i) (b' i) (c' i) f (u' i)) :
    Filter.Tendsto u' l (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- `‖u - u' i‖ ≤ (Λ i + β i + γ i) ‖u' i‖ / C`, so once `Λ i + β i + γ i ≤ C / 2` we get
  -- `‖u' i - u‖ ≤ 2 (Λ i + β i + γ i) ‖u‖ / C`, and these bounds tend to `0`.
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (((hlim.const_mul 2).mul_const ‖u‖).div_const C |>.trans
      (by rw [mul_zero, zero_mul, zero_div]))
  filter_upwards [hlim.eventually (ge_mem_nhds (half_pos hC))] with i hi
  have h := norm_sub_le_of_forall_energyFormH1_eq hcoeff (hcoeff' i) hC hlower (hLam i)
    (ha i) (hbeta i) (hb i) (hgamma i) (hc i) hu.energyFormH1_eq_dirichletForcing
    (hu' i).energyFormH1_eq_dirichletForcing
  rw [sub_self (dirichletForcing f), ContinuousLinearMap.opNorm_zero, zero_add,
    le_div_iff₀ hC] at h
  have htri := norm_le_norm_add_norm_sub u (u' i)
  have hδ : 0 ≤ Lam i + beta i + gamma i := by linarith [hLam i, hbeta i, hgamma i]
  rw [norm_sub_rev, le_div_iff₀ hC]
  nlinarith [mul_le_mul_of_nonneg_right hi (norm_nonneg (u - u' i)),
    mul_le_mul_of_nonneg_left htri hδ]

end PDE

end TauCeti
