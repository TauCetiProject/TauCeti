/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem

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

`‖u - u'‖ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + M ‖h‖ + (Λ + β + γ) ‖u'‖) / C`,

where `M` bounds the energy form on `H¹(Ω)`, `|B(v, w)| ≤ M ‖v‖ ‖w‖`. Only the first energy form
needs to be coercive. In particular, solutions for coefficients, forcings and boundary
data converging to a coercive limit problem converge in `H¹(Ω)` to its solution. This is the
continuity of the solution map that makes the coefficient-to-solution map of a quasilinear
equation `-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = ℓ` continuous, as needed for a Schauder fixed-point argument.

## Main declarations

* `TauCeti.PDE.norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`: the stability
  estimate for data in `H⁻¹(Ω)` and boundary values in `H¹(Ω)`.
* `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq`: its case of zero boundary values, for
  solutions in `H¹₀(Ω)`.
* `TauCeti.PDE.norm_sub_le_of_isWeakSolutionDirichlet`: for a common right-hand side
  `f ∈ L²(Ω)` and coercivity constants `C, C'`, `‖u - u'‖ ≤ (Λ + β + γ) ‖f‖ / (C C')`.
* `TauCeti.PDE.tendsto_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`: weak solutions for
  coefficients converging in `L^∞(Ω)`, forcings converging in `H⁻¹(Ω)` and boundary data
  converging in `H¹(Ω)` converge in `H¹(Ω)`, provided the limit energy form is coercive.
* `TauCeti.PDE.tendsto_of_isWeakSolutionDirichlet`: for zero boundary values and a common
  right-hand side `f ∈ L²(Ω)` the same conclusion holds in `H¹₀(Ω)`, with no bound `M` needed.

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

open MeasureTheory TopologicalSpace
open scoped Matrix

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b b' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c c' : EuclideanSpace ℝ ι → ℝ} {C C' Lam beta gamma : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **Stability of the Dirichlet problem under perturbation of the energy form, the data and
the boundary values.** Let `u ∈ H¹(Ω)` satisfy `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, where `B`
is the energy form of the coefficients `(a, b, c)` and satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)`
with `0 < C`, and let `u' ∈ H¹(Ω)` satisfy `B'(u', v) = ℓ'(v)` for the energy form `B'` of
`(a', b', c')`. Let `u - u'` differ from `h ∈ H¹(Ω)` by an element of `H¹₀(Ω)`, for instance
`h = g - g'` when `u - g` and `u' - g'` lie in `H¹₀(Ω)`. If `N ≥ 0` bounds the functional `B(h, ·)`
and `D ≥ 0` bounds the functional `B(u', ·) - B'(u', ·)` on `H¹₀(Ω)`, then

`‖u - u'‖ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + N + D) / C`.

When `|B(v, w)| ≤ M ‖v‖ ‖w‖` one may take `N = M ‖h‖`, and when the coefficient differences are
bounded by `Λ`, `β` and `γ` almost everywhere one may take `D = (Λ + β + γ) ‖u'‖`
(`TauCeti.PDE.norm_energyFormH1_le_of_bounds`). The second energy form need not be coercive. -/
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
  -- `C x² ≤ K x` with `0 ≤ x` and `0 ≤ K` gives `x ≤ K / C`; it is applied to `x = ‖w‖` below.
  have hdiv : ∀ x K : ℝ, 0 ≤ x → 0 ≤ K → C * x ^ 2 ≤ K * x → x ≤ K / C := fun x K hx hK hxK =>
    (le_div_iff₀ hC).2 (by nlinarith only [hxK, hC, hK, hx])
  -- Test both equations against `w = u - u' - h ∈ H¹₀(Ω)`:
  -- `B(w, w) = (ℓ - ℓ') w - (B(u', w) - B'(u', w)) - B(h, w)`.
  obtain ⟨w, hwu⟩ : ∃ w : W1p0 mu Omega 2, (w : W1p mu Omega 2) = u - u' - h :=
    ⟨⟨u - u' - h, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 huh⟩, rfl⟩
  have hw : energyFormH1 a b c (w : W1p mu Omega 2) w =
      (ℓ - ℓ') w - (energyFormH1 a b c u' w - energyFormH1 a' b' c' u' w) -
        energyFormH1 a b c h w := by
    rw [congrArg (fun z => energyFormH1 a b c z (w : W1p mu Omega 2)) hwu,
      energyFormH1_sub_left hcoeff, energyFormH1_sub_left hcoeff, sub_apply, ← hu w, ← hu' w]
    ring
  have hkey : C * ‖w‖ ^ 2 ≤ (‖ℓ - ℓ'‖ + N + D) * ‖w‖ := by
    have h₁ := hlower w
    rw [hw] at h₁
    linarith [(le_abs_self _).trans ((ℓ - ℓ').le_opNorm w), neg_abs_le
      (energyFormH1 a b c u' w - energyFormH1 a' b' c' u' w), hD w,
      neg_abs_le (energyFormH1 a b c h w), hN w]
  -- `‖w‖ ≤ (‖ℓ - ℓ'‖ + N + D) / C`, and `u - u' = w + h`.
  have hnorm : ‖(w : W1p mu Omega 2)‖ = ‖w‖ := Submodule.norm_coe w
  have hw0 : 0 ≤ ‖w‖ := by
    rw [← hnorm]
    exact norm_nonneg _
  have hK0 : 0 ≤ ‖ℓ - ℓ'‖ + N + D := add_nonneg (add_nonneg ((ℓ - ℓ').opNorm_nonneg) hN0) hD0
  have hwK := hdiv _ _ hw0 hK0 hkey
  calc ‖u - u'‖ = ‖(w : W1p mu Omega 2) + h‖ := by rw [hwu, sub_add_cancel]
    _ ≤ ‖(w : W1p mu Omega 2)‖ + ‖h‖ := norm_add_le _ _
    _ = ‖w‖ + ‖h‖ := by rw [hnorm]
    _ ≤ ‖h‖ + (‖ℓ - ℓ'‖ + N + D) / C := by linarith only [hwK]

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
    have hd := norm_energyFormH1_le_of_bounds (a := a - a') (b := b - b') (c := c - c') hLam
      ha hb hc (u' : W1p mu Omega 2) (w : W1p mu Omega 2)
    rw [energyFormH1_sub hcoeff hcoeff', Submodule.norm_coe, Submodule.norm_coe,
      Real.norm_eq_abs] at hd
    linarith only [hd]
  have h0 (w : W1p0 mu Omega 2) : |energyFormH1 a b c 0 (w : W1p mu Omega 2)| ≤ 0 * ‖w‖ := by
    rw [← sub_self (0 : W1p mu Omega 2), energyFormH1_sub_left hcoeff, sub_self, abs_zero,
      zero_mul]
  have hmem : (u : W1p mu Omega 2) - u' - 0 ∈ w1p0Submodule mu Omega 2 := by
    rw [sub_zero, ← Submodule.coe_sub, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact (u - u').2
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
where the energy form `B` of `(a, b, c)` is bounded, `|B(v, w)| ≤ M ‖v‖ ‖w‖` on `H¹(Ω)`, and
coercive on `H¹₀(Ω)` with constant `C`, and let `u' i ∈ H¹(Ω)` solve the problems for a family
`(a' i, b' i, c' i, ℓ' i)` with `u' i - g' i ∈ H¹₀(Ω)`. Suppose that the bounds `Λ i`, `β i` and
`γ i` on the differences `a - a' i`, `b - b' i` and `c - c' i` almost everywhere on `Ω`, in the
sense of the hypotheses of `norm_sub_le_of_forall_energyFormH1_eq`, tend to `0` along a filter,
that `ℓ' i → ℓ` in the norm of `H⁻¹(Ω)` and that `g' i → g` in `H¹(Ω)`. Then `u' i → u` in
`H¹(Ω)`. The perturbed energy forms need not be coercive. -/
theorem tendsto_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq {α : Type*} {l : Filter α}
    {a' : α → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b' : α → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c' : α → EuclideanSpace ℝ ι → ℝ} {Lam beta gamma : α → ℝ} {M : ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : ∀ i,
      MemLp (fun x => energyIntegrand (a' i x) (b' i x) (c' i x)) ⊤ (mu.restrict Omega))
    (hM : ∀ v w : W1p mu Omega 2, ‖energyFormH1 a b c v w‖ ≤ M * (‖v‖ * ‖w‖)) (hC : 0 < C)
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
  -- `‖u' i - u‖ ≤ 2 (C ‖g - g' i‖ + ‖ℓ - ℓ' i‖ + M ‖g - g' i‖ + δ i ‖u‖) / C`, which tends to `0`.
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
  -- The functional `B(g - g' i, ·)` has norm at most `M ‖g - g' i‖`.
  have hN (w : W1p0 mu Omega 2) :
      |energyFormH1 a b c (g - g' i) (w : W1p mu Omega 2)| ≤ M * ‖g - g' i‖ * ‖w‖ := by
    have hd := hM (g - g' i) (w : W1p mu Omega 2)
    rw [Submodule.norm_coe, Real.norm_eq_abs] at hd
    linarith only [hd]
  have hN0 : 0 ≤ M * ‖g - g' i‖ := by
    rcases (norm_nonneg (g - g' i)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
    · have hd := (norm_nonneg _).trans (hM (g - g' i) (g - g' i))
      nlinarith only [hd, hpos]
  -- The difference of the energy forms at `u' i` is the energy form of the difference.
  have hD (w : W1p0 mu Omega 2) : |energyFormH1 a b c (u' i) (w : W1p mu Omega 2) -
      energyFormH1 (a' i) (b' i) (c' i) (u' i) (w : W1p mu Omega 2)| ≤
        (Lam i + beta i + gamma i) * ‖u' i‖ * ‖w‖ := by
    have hd := norm_energyFormH1_le_of_bounds (a := a - a' i) (b := b - b' i) (c := c - c' i)
      (hLam i) (ha i) (hb i) (hc i) (u' i) (w : W1p mu Omega 2)
    rw [energyFormH1_sub hcoeff (hcoeff' i), Submodule.norm_coe, Real.norm_eq_abs] at hd
    linarith only [hd]
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
