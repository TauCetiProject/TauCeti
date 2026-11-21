/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Topology.Instances.Matrix

/-!
# Continuous dependence of the Dirichlet problem on its coefficients and data

For a divergence-form operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on an open set `Ω ⊆ ℝⁿ`, the
weak solution `u ∈ H¹(Ω)` of `L u = ℓ` with boundary values `u - g ∈ H¹₀(Ω)` depends Lipschitz
continuously on the coefficients `a, b, c` in `L^∞(Ω)`, on the forcing `ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*`
and on the boundary data `g ∈ H¹(Ω)`, with constants governed by the coercivity constant of the
energy form. Let `u` solve the problem for `(a, b, c, ℓ, g)`, whose energy form `B` satisfies
`C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)`, and let `u'` solve it for `(a', b', c', ℓ', g')`. With
`h = g - g'`, the function `w = u - u' - h` lies in `H¹₀(Ω)`, and testing both equations against
it gives

`C ‖w‖² ≤ B(w, w) = (ℓ - ℓ')(w) - (B - B')(u', w) - B(h, w)`.

The difference of the energy forms is the energy form of the difference of the coefficients,
bounded by the `L^∞` bounds `Λ, β, γ` of `a - a'`, `b - b'` and `c - c'`. Hence

`‖u - u'‖ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + ‖B‖ ‖h‖ + (Λ + β + γ) ‖u'‖) / C`,

where `‖B‖` is the norm of `B` as a bounded bilinear form on `H¹(Ω)`. Only the first energy form
needs to be coercive. In particular, solutions for coefficients, forcings and boundary
data converging to a coercive limit problem converge in `H¹(Ω)` to its solution. This is the
continuity of the solution map that makes the coefficient-to-solution map of a quasilinear
equation `-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = ℓ` continuous, as needed for a Schauder fixed-point argument.

Uniform convergence of the coefficients is not necessary: if the principal coefficients `a' i`
converge to `a` almost everywhere on `Ω`, with `a - a' i` bounded by one constant and the energy
forms of `(a' i, b, c)` uniformly coercive, then the solutions with the same forcing and the same
boundary values converge in `H¹(Ω)`. Testing with `w = u' i - u` gives
`C ‖w‖² ≤ ∫ ⟨(a - a' i) ∇u, ∇w⟩`, Young's inequality turns this into
`C² ‖w‖² ≤ ∫ ‖a - a' i‖² ‖∇u‖²`, and the right-hand side tends to `0` by dominated convergence.

## Main declarations

* `TauCeti.PDE.norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`: the stability
  estimate for data in `H⁻¹(Ω)` and boundary values in `H¹(Ω)`, from the two-problem energy
  estimate `TauCeti.PDE.norm_sub_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`.
* `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq`: its case of zero boundary values, for
  solutions in `H¹₀(Ω)`.
* `TauCeti.PDE.norm_sub_le_of_isWeakSolutionDirichlet`: for a common right-hand side
  `f ∈ L²(Ω)` and coercivity constants `C, C'`, `‖u - u'‖ ≤ (Λ + β + γ) ‖f‖ / (C C')`.
* `TauCeti.PDE.tendsto_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`: weak solutions for
  coefficients converging in `L^∞(Ω)`, forcings converging in `H⁻¹(Ω)` and boundary data
  converging in `H¹(Ω)` converge in `H¹(Ω)`, provided the limit energy form is coercive.
* `TauCeti.PDE.tendsto_of_isWeakSolutionDirichlet`: for zero boundary values and a common
  right-hand side `f ∈ L²(Ω)` the same conclusion holds in `H¹₀(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.2.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, Theorem 4.1.1 (the first
  Strang lemma, the same perturbation argument for approximate forms).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.2 (the Dirichlet problem `u - g ∈ W^{1,2}_0(Ω)` for weak solutions).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter MeasureTheory TopologicalSpace
open scoped Matrix Topology

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b b' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c c' : EuclideanSpace ℝ ι → ℝ} {C C' Lam beta gamma : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
-- The shortcut instances of the energy-form file, so that the operator norm of the bundled
-- energy form `TauCeti.PDE.energyFormH1L` is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-- **Stability of the Dirichlet problem under perturbation of the energy form, the data and
the boundary values.** Let `u ∈ H¹(Ω)` satisfy `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, where `B`
is the energy form of the coefficients `(a, b, c)` and satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)`
with `0 < C`, and let `u' ∈ H¹(Ω)` satisfy `B'(u', v) = ℓ'(v)` for the energy form `B'` of
`(a', b', c')`. Let `u - u'` differ from `h ∈ H¹(Ω)` by an element of `H¹₀(Ω)`, for instance
`h = g - g'` when `u - g` and `u' - g'` lie in `H¹₀(Ω)`. If `N ≥ 0` bounds the functional `B(h, ·)`
and `D ≥ 0` bounds the functional `B(u', ·) - B'(u', ·)` on `H¹₀(Ω)`, then

`‖u - u'‖ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + N + D) / C`.

One may take `N = ‖B‖ ‖h‖` with `‖B‖ = ‖energyFormH1L hcoeff‖`
(`TauCeti.PDE.abs_energyFormH1_le_norm_energyFormH1L_mul`), and when the coefficient
differences are bounded by `Λ`, `β` and `γ` almost everywhere one may take `D = (Λ + β + γ) ‖u'‖`
(`TauCeti.PDE.abs_energyFormH1_sub_energyFormH1_le`). The second energy form need not be
coercive. -/
theorem norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {ℓ ℓ' : StrongDual ℝ (W1p0 mu Omega 2)} {u u' h : W1p mu Omega 2} {N D : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ w : W1p0 mu Omega 2, |energyFormH1 a b c h (w : W1p mu Omega 2)| ≤ N * ‖w‖)
    (hD0 : 0 ≤ D)
    (hD : ∀ w : W1p0 mu Omega 2, |energyFormH1 a b c u' (w : W1p mu Omega 2) -
      energyFormH1 a' b' c' u' (w : W1p mu Omega 2)| ≤ D * ‖w‖)
    (huh : u - u' - h ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v)
    (hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a' b' c' u' (v : W1p mu Omega 2) = ℓ' v) :
    ‖u - u'‖ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + N + D) / C := by
  -- `u - u' = (u - u' - h) + h`, and the first summand is bounded by the two-problem estimate.
  calc ‖u - u'‖ = ‖u - u' - h + h‖ := by rw [sub_add_cancel]
    _ ≤ ‖u - u' - h‖ + ‖h‖ := norm_add_le _ _
    _ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + N + D) / C := by
      linarith only [norm_sub_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff
        hC hlower hN0 hN hD0 hD huh hu hu']

/-- **Stability of the Dirichlet problem under perturbation of the coefficients and the data.**
Let `u ∈ H¹₀(Ω)` satisfy `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, where `B` is the energy form of
the coefficients `(a, b, c)` and satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)` with `0 < C`, and let
`u' ∈ H¹₀(Ω)` satisfy `B'(u', v) = ℓ'(v)` for the energy form `B'` of `(a', b', c')`. Suppose both
coefficient fields are essentially bounded and that almost everywhere on `Ω`
`|ηᵀ (a - a') ξ| ≤ Λ ‖η‖ ‖ξ‖`, `‖b - b'‖ ≤ β` and `|c - c'| ≤ γ`. Then
`‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Λ + β + γ) ‖u'‖) / C`. This is the case of zero boundary values of
`norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`.

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
  -- The difference of the energy forms at `u'` is the energy form of the difference.
  have hD (w : W1p0 mu Omega 2) : |energyFormH1 a b c (u' : W1p mu Omega 2) w -
      energyFormH1 a' b' c' (u' : W1p mu Omega 2) w| ≤ (Lam + beta + gamma) * ‖u'‖ * ‖w‖ := by
    simpa only [Submodule.norm_coe u', Submodule.norm_coe w] using
      abs_energyFormH1_sub_energyFormH1_le hcoeff hcoeff' hLam ha hb hc (u' : W1p mu Omega 2)
        (w : W1p mu Omega 2)
  have h0 (w : W1p0 mu Omega 2) : |energyFormH1 a b c 0 (w : W1p mu Omega 2)| ≤ 0 * ‖w‖ := by
    rw [energyFormH1_zero_left, abs_zero, zero_mul]
  have hmem : (u : W1p mu Omega 2) - u' - 0 ∈ w1p0Submodule mu Omega 2 := by
    rw [sub_zero, ← Submodule.coe_sub, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact (u - u').property
  have h := norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff hC
    hlower le_rfl h0 (mul_nonneg (by linarith) (norm_nonneg _)) hD hmem hu hu'
  rw [norm_zero, zero_add, add_zero, ← Submodule.coe_sub, Submodule.norm_coe] at h
  exact h

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

/-- **Continuous dependence of the weak solution on the coefficients, the data and the boundary
values.** Let `u ∈ H¹(Ω)` solve `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)` with `u - g ∈ H¹₀(Ω)`,
where the energy form `B` of the essentially bounded coefficients `(a, b, c)` is coercive on
`H¹₀(Ω)` with constant `C`, and let `u' i ∈ H¹(Ω)` solve the problems for a family
`(a' i, b' i, c' i, ℓ' i)` with `u' i - g' i ∈ H¹₀(Ω)`. Suppose that the bounds `Λ i`, `β i` and
`γ i` on the differences `a - a' i`, `b - b' i` and `c - c' i` almost everywhere on `Ω`, in the
sense of the hypotheses of `norm_sub_le_of_forall_energyFormH1_eq`, tend to `0` along a filter,
that `ℓ' i → ℓ` in the norm of `H⁻¹(Ω)` and that `g' i → g` in `H¹(Ω)`. Then `u' i → u` in
`H¹(Ω)`. The perturbed energy forms need not be coercive. -/
theorem tendsto_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq {α : Type*} {l : Filter α}
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
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {ℓ' : α → StrongDual ℝ (W1p0 mu Omega 2)}
    (hℓ : Filter.Tendsto (fun i => ‖ℓ - ℓ' i‖) l (nhds 0)) {g u : W1p mu Omega 2}
    {g' u' : α → W1p mu Omega 2} (hg : Filter.Tendsto g' l (nhds g))
    (hug : u - g ∈ w1p0Submodule mu Omega 2)
    (hug' : ∀ i, u' i - g' i ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v)
    (hu' : ∀ i, ∀ v : W1p0 mu Omega 2,
      energyFormH1 (a' i) (b' i) (c' i) (u' i) (v : W1p mu Omega 2) = ℓ' i v) :
    Filter.Tendsto u' l (nhds u) := by
  -- With `δ i = Λ i + β i + γ i`, once `δ i ≤ C / 2` the stability estimate gives
  -- `‖u' i - u‖ ≤ 2 (C ‖g - g' i‖ + ‖ℓ - ℓ' i‖ + ‖B‖ ‖g - g' i‖ + δ i ‖u‖) / C`, which tends
  -- to `0`.
  set M := ‖energyFormH1L hcoeff‖
  have hg0 : Filter.Tendsto (fun i => ‖g - g' i‖) l (nhds 0) := by
    simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.1 hg
  have he : Filter.Tendsto (fun i => 2 * (C * ‖g - g' i‖ + ‖ℓ - ℓ' i‖ + M * ‖g - g' i‖ +
      (Lam i + beta i + gamma i) * ‖u‖) / C) l (nhds 0) := by
    simpa using ((((hg0.const_mul C).add hℓ).add (hg0.const_mul M)).add
      (hlim.mul_const ‖u‖)).const_mul 2 |>.div_const C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ he
  filter_upwards [hlim.eventually (ge_mem_nhds (half_pos hC))] with i hi
  have hδ : 0 ≤ Lam i + beta i + gamma i := by linarith [hLam i, hbeta i, hgamma i]
  -- The functional `B(g - g' i, ·)` has norm at most `‖B‖ ‖g - g' i‖`.
  have hN (w : W1p0 mu Omega 2) :
      |energyFormH1 a b c (g - g' i) (w : W1p mu Omega 2)| ≤ M * ‖g - g' i‖ * ‖w‖ := by
    rw [← Submodule.norm_coe w]
    exact abs_energyFormH1_le_norm_energyFormH1L_mul hcoeff _ _
  have hN0 : 0 ≤ M * ‖g - g' i‖ := mul_nonneg (energyFormH1L hcoeff).opNorm_nonneg (norm_nonneg _)
  have hD (w : W1p0 mu Omega 2) : |energyFormH1 a b c (u' i) (w : W1p mu Omega 2) -
      energyFormH1 (a' i) (b' i) (c' i) (u' i) (w : W1p mu Omega 2)| ≤
        (Lam i + beta i + gamma i) * ‖u' i‖ * ‖w‖ := by
    simpa only [Submodule.norm_coe] using abs_energyFormH1_sub_energyFormH1_le hcoeff
      (hcoeff' i) (hLam i) (ha i) (hb i) (hc i) (u' i) (w : W1p mu Omega 2)
  have hmem : u - u' i - (g - g' i) ∈ w1p0Submodule mu Omega 2 := by
    rw [← sub_sub_sub_comm, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact sub_mem ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hug)
      ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 (hug' i))
  have h := norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff hC hlower
    hN0 hN (mul_nonneg hδ (norm_nonneg _)) hD hmem hu (hu' i)
  rw [← sub_le_iff_le_add', le_div_iff₀ hC] at h
  -- Absorb `δ ‖u' i‖ ≤ δ ‖u‖ + δ ‖u - u' i‖ ≤ δ ‖u‖ + (C / 2) ‖u - u' i‖` into the left side.
  have h₁ := mul_le_mul_of_nonneg_left (norm_le_norm_add_norm_sub u (u' i)) hδ
  have h₂ := mul_le_mul_of_nonneg_right hi (norm_nonneg (u - u' i))
  rw [norm_sub_rev, le_div_iff₀ hC]
  linarith only [h, h₁, h₂]

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
  -- This is the case `g = g' i = 0` and `ℓ = ℓ' i = dirichletForcing f` in `H¹(Ω)`.
  have hmem (v : W1p0 mu Omega 2) : (v : W1p mu Omega 2) - 0 ∈ w1p0Submodule mu Omega 2 := by
    rw [sub_zero, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact v.property
  have hℓ : Filter.Tendsto (fun _ : α => ‖dirichletForcing f - dirichletForcing f‖) l (nhds 0) := by
    rw [sub_self (dirichletForcing f), ContinuousLinearMap.opNorm_zero]
    exact tendsto_const_nhds
  have h := tendsto_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff hcoeff' hC hlower
    hLam ha hbeta hb hgamma hc hlim hℓ tendsto_const_nhds (hmem u) (fun i => hmem (u' i))
    hu.energyFormH1_eq_dirichletForcing fun i => (hu' i).energyFormH1_eq_dirichletForcing
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  simpa only [← Submodule.coe_sub, Submodule.norm_coe] using h

/-- The perturbation estimate behind
`TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`. If `u` solves the problem for
`(a, b, c)` and `u'` solves it for `(a', b, c)` with the same forcing, `u' - u ∈ H¹₀(Ω)`, and the
energy form of `(a', b, c)` satisfies `C ‖w‖² ≤ B'(w, w)` on `H¹₀(Ω)`, then
`C² ‖u' - u‖² ≤ ∫_Ω ‖a - a'‖² ‖∇u‖²`. -/
private theorem norm_sub_sq_le_integral_of_forall_energyFormH1_eq
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a' b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {u u' : W1p mu Omega 2}
    (hG : Integrable (fun x => ‖matrixBilinearForm (a x - a' x)‖ ^ 2 *
      ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v)
    (hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a' b c u' v = ℓ v)
    (hsub : u' - u ∈ w1p0Submodule mu Omega 2) :
    ‖u' - u‖ ^ 2 ≤
      (∫ x in Omega, ‖matrixBilinearForm (a x - a' x)‖ ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu) /
        C ^ 2 := by
  set G := ∫ x in Omega, ‖matrixBilinearForm (a x - a' x)‖ ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu
  let w : W1p0 mu Omega 2 := ⟨u' - u, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hsub⟩
  have hnorm : ‖w‖ = ‖u' - u‖ := Submodule.norm_coe w
  -- Testing both equations against `w = u' - u` leaves only the difference of the coefficients.
  have hw : energyFormH1 a' b c (w : W1p mu Omega 2) w =
      energyFormH1 a b c u w - energyFormH1 a' b c u w := by
    have := energyFormH1_sub_left hcoeff' u' (w : W1p mu Omega 2) u
    linarith [hu w, hu' w]
  -- Pointwise, that difference is `(∇w)ᵀ (a - a') ∇u`, which Young's inequality bounds.
  have hyoung : energyFormH1 a b c u w - energyFormH1 a' b c u w ≤
      C / 2 * ‖W1p.gradient (w : W1p mu Omega 2)‖ ^ 2 + G / (2 * C) := by
    have hgrad := W1p.integral_norm_gradient_sq_eq_norm_gradient_sq (w : W1p mu Omega 2)
    have hgradint : Integrable (fun x => ‖W1p.gradient (w : W1p mu Omega 2) x‖ ^ 2)
        (mu.restrict Omega) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
    rw [energyFormH1_def, energyFormH1_def, ← integral_sub
      (integrable_energyIntegrand_jetField hcoeff u w)
      (integrable_energyIntegrand_jetField hcoeff' u w), ← hgrad, ← integral_const_mul,
      ← integral_div, ← integral_add (hgradint.const_mul _) (hG.div_const _)]
    refine integral_mono_ae ((integrable_energyIntegrand_jetField hcoeff u w).sub
      (integrable_energyIntegrand_jetField hcoeff' u w))
      ((hgradint.const_mul _).add (hG.div_const _)) (Eventually.of_forall fun x => ?_)
    have := matrixBilinearForm_apply_le_young (a x - a' x) hC
      (W1p.gradient (w : W1p mu Omega 2) x) (W1p.gradient u x)
    simp only [energyIntegrand_apply, jetField_apply, matrixBilinearForm_sub,
      sub_apply] at this ⊢
    linarith
  have hgw : ‖W1p.gradient (w : W1p mu Omega 2)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← Submodule.norm_coe w, W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
    nlinarith [sq_nonneg ‖W1p.value (w : W1p mu Omega 2)‖]
  have h := (hlower w).trans (hw.trans_le hyoung)
  have h2 : C * ‖w‖ ^ 2 ≤ G / C := by
    rw [show G / (2 * C) = G / C / 2 by ring] at h
    linarith [mul_le_mul_of_nonneg_left hgw hC.le]
  rw [le_div_iff₀ hC] at h2
  rw [← hnorm, le_div_iff₀ (by positivity)]
  linarith

/-- The dominated-convergence step behind
`TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`: if `a' i → a` almost everywhere on
`Ω` with `a - a' i` bounded by `Λ`, then `∫_Ω ‖a - a' i‖² ‖∇u‖² → 0`, and each of these integrands
is integrable. -/
private theorem tendsto_integral_norm_matrixBilinearForm_sub_sq_mul {α : Type*}
    {l : Filter α} [l.IsCountablyGenerated] {a' : α → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (ha' : ∀ i, AEStronglyMeasurable (a' i) (mu.restrict Omega))
    (hbound : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' i x) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hlim : ∀ᵐ x ∂mu.restrict Omega, Tendsto (fun i => a' i x) l (𝓝 (a x)))
    (u : W1p mu Omega 2) :
    (∀ i, Integrable (fun x => ‖matrixBilinearForm (a x - a' i x)‖ ^ 2 *
      ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega)) ∧
    Tendsto (fun i => ∫ x in Omega, ‖matrixBilinearForm (a x - a' i x)‖ ^ 2 *
      ‖W1p.gradient u x‖ ^ 2 ∂mu) l (𝓝 0) := by
  have hgradint : Integrable (fun x => ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  -- The norm is taken in the space of bilinear forms, named explicitly as in `Continuous.norm`.
  have hnorm : Continuous fun A : Matrix ι ι ℝ => ‖matrixBilinearForm A‖ :=
    Continuous.norm (E := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      continuous_matrixBilinearForm
  have hmeas (i : α) : AEStronglyMeasurable (fun x => ‖matrixBilinearForm (a x - a' i x)‖ ^ 2 *
      ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
    ((hnorm.comp_aestronglyMeasurable (ha.sub (ha' i))).pow 2).mul
      ((Lp.aestronglyMeasurable (W1p.gradient u)).norm.pow 2)
  -- The integrands are dominated by `max Λ 0 ^ 2 ‖∇u‖²`.
  have hdom (i : α) : ∀ᵐ x ∂mu.restrict Omega,
      ‖‖matrixBilinearForm (a x - a' i x)‖ ^ 2 * ‖W1p.gradient u x‖ ^ 2‖ ≤
        max Lam 0 ^ 2 * ‖W1p.gradient u x‖ ^ 2 := by
    filter_upwards [hbound i] with x hx
    have hop := matrixBilinearForm_opNorm_le_of_upper_bound (a x - a' i x) (le_max_right Lam 0)
      fun η ξ => (hx η ξ).trans (by gcongr; exact le_max_left Lam 0)
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
  refine ⟨fun i => (hgradint.const_mul _).mono' (hmeas i) (hdom i), ?_⟩
  rw [← integral_zero (EuclideanSpace ℝ ι) ℝ]
  refine tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hmeas)
    (Eventually.of_forall hdom) (hgradint.const_mul _) ?_
  filter_upwards [hlim] with x hx
  have h0 : Tendsto (fun i => ‖matrixBilinearForm (a x - a' i x)‖) l (𝓝 0) := by
    have h := (hnorm.tendsto (a x - a x)).comp ((tendsto_const_nhds (x := a x)).sub hx)
    rwa [show ‖matrixBilinearForm (a x - a x)‖ = 0 by
      rw [sub_self, ← matrixBilinearFormLinear_apply, map_zero]
      exact norm_zero (E := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)] at h
  simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] using
    (h0.pow 2).mul_const (‖W1p.gradient u x‖ ^ 2)

/-- **Continuous dependence of the weak solution on almost everywhere convergent principal
coefficients.** Let `u ∈ H¹(Ω)` satisfy `B(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)`, where `B` is the
energy form of the coefficients `(a, b, c)`, and let `u' i ∈ H¹(Ω)`, with `u' i - u ∈ H¹₀(Ω)`,
satisfy the same equation for the coefficients `(a' i, b, c)`, whose energy forms satisfy
`C ‖w‖² ≤ Bᵢ(w, w)` on `H¹₀(Ω)` with one constant `C > 0`. If `a' i → a` almost everywhere on `Ω`
along a countably generated filter and the differences `a - a' i` are bounded by one constant
`Λ` almost everywhere, then `u' i → u` in `H¹(Ω)`.

Compared with `TauCeti.PDE.tendsto_of_isWeakSolutionDirichlet`, the coefficients need not
converge uniformly; this is what continuity of the frozen-coefficient map of a quasilinear
equation `-div (A(x, u) ∇u) = ℓ` needs, since a convergent sequence of functions `u` converges
almost everywhere only along a subsequence, and not uniformly in general. The argument is the
continuity step of M. Chipot, *Elliptic Equations: An Introductory Course*, Section 11.2. -/
theorem tendsto_of_forall_energyFormH1_eq_of_tendsto_ae {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] {a' : α → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : ∀ i,
      MemLp (fun x => energyIntegrand (a' i x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ i, ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 (a' i) b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (ha' : ∀ i, AEStronglyMeasurable (a' i) (mu.restrict Omega))
    (hbound : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' i x) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hlim : ∀ᵐ x ∂mu.restrict Omega, Tendsto (fun i => a' i x) l (𝓝 (a x)))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {u : W1p mu Omega 2} {u' : α → W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v)
    (hu' : ∀ i, ∀ v : W1p0 mu Omega 2, energyFormH1 (a' i) b c (u' i) v = ℓ v)
    (hsub : ∀ i, u' i - u ∈ w1p0Submodule mu Omega 2) :
    Tendsto u' l (𝓝 u) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  -- The limit coefficient is measurable as an almost everywhere limit of measurable ones; matrices
  -- carry the product topology, which is metrizable.
  have ha := aestronglyMeasurable_of_tendsto_ae l ha' hlim
  obtain ⟨hint, hlim'⟩ :=
    tendsto_integral_norm_matrixBilinearForm_sub_sq_mul ha ha' hbound hlim u
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i => Real.sqrt ((∫ x in Omega,
      ‖matrixBilinearForm (a x - a' i x)‖ ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu) / C ^ 2))
    (fun _ => norm_nonneg _) (fun i => ?_)
    (by simpa only [zero_div, Real.sqrt_zero] using (hlim'.div_const (C ^ 2)).sqrt)
  rw [← Real.sqrt_sq (norm_nonneg (u' i - u))]
  exact Real.sqrt_le_sqrt (norm_sub_sq_le_integral_of_forall_energyFormH1_eq hcoeff
    (hcoeff' i) hC (hlower i) (hint i) hu (hu' i) (hsub i))

end PDE

end TauCeti
