/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# Root branches of the Newton coefficient equation

Let `b₁, …, b_m` be complex functions on a complex normed space `V`, and let

`P_y(W) = Wᵐ - b₁(y) W^(m-1) + ⋯ + (-1)ᵐ b_m(y)`

be the monic polynomial they define at each `y`. When the `b_j` are the Newton coefficients of the
normal moments of a current concentrating along a pseudoholomorphic curve `C`, the roots of `P_y`
are the candidate positions of the local branches of the limiting curve in the normal fibre, and
`TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton` gives the equation

`\bar∂ b_j + j ν b_j + μ ∑_{w ∈ R} \bar w e_{j-1}(R ∖ w) = r_j`,  `1 ≤ j ≤ m`,

with `R` the roots of `P_y`, `D_C = \bar∂ + ν W + μ \bar W` a real normal Cauchy–Riemann operator
and `r_j` a remainder. This is the equation satisfied by the elementary symmetric functions of `m`
solutions of `D_C`. This file goes the other way: it shows that the roots themselves solve `D_C`
where they are simple, so that away from the collisions of roots the root multigraph of `P` is a
union of graphs of solutions of `D_C`, that is, of pseudoholomorphic sections of the normal line.

* `TauCeti.prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum`: for a real-differentiable root
  branch `v` of `P`, that is `P_y(v(y)) = 0` near `x`,

  `∏_{w ∈ R ∖ v(x)} (v(x) - w) • (\bar∂ v + v ν + \bar v μ)(x) =
    ∑_{j=1}^{m} (-1)^(j-1) v(x)^(m-j) r_j`.

  The factor on the left is `P_x'(v(x))`, which is nonzero exactly when `v(x)` is a simple root.
* `TauCeti.conjWirtingerDeriv_add_add_eq_zero_of_root`: consequently a root branch through a simple
  root solves `D_C` at every point where the remainders vanish.
* `TauCeti.exists_contDiffAt_root_branch`: if the `b_j` are `Cⁿ` at `x`, `n ≠ 0`, then near a simple
  root `v₀` of `P_x` the zero set `{(y, w) : P_y(w) = 0}` is the graph of a `Cⁿ` function `v` with
  `v(x) = v₀` (implicit function theorem).
* `TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`: if the `b_j` are `C¹` and the
  equation holds with zero remainder near `x`, this branch solves `D_C v = 0` near `x`.

The collisions of roots, where `P'` vanishes and the branches must be normalized, are not treated
here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Finset Filter Topology ComplexConjugate

namespace TauCeti

/-- If `c_j = e_j(S)` for `1 ≤ j ≤ m`, the polynomial `Wᵐ + ∑_{j=1}^{m} (-1)ʲ c_j W^(m-j)` is
`∏_{w ∈ S} (W - w)`. -/
private theorem pow_add_sum_eq_prod {S : Multiset ℂ} {m : ℕ} (hS : Multiset.card S = m) {c : ℕ → ℂ}
    (hc : ∀ j ∈ Icc 1 m, c j = S.esymm j) (w : ℂ) :
    w ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * c j * w ^ (m - j) = (S.map fun u ↦ w - u).prod := by
  rw [Multiset.prod_map_sub_eq_pow_add_sum_esymm hS]
  exact congrArg _ (sum_congr rfl fun j hj ↦ by rw [hc j hj])

/-- A root of `Wᵐ + ∑_{j=1}^{m} (-1)ʲ c_j W^(m-j)`, with `c_j = e_j(S)`, lies in `S`. -/
private theorem mem_of_pow_add_sum_eq_zero {S : Multiset ℂ} {v : ℂ} {m : ℕ}
    (hS : Multiset.card S = m) {c : ℕ → ℂ} (hc : ∀ j ∈ Icc 1 m, c j = S.esymm j)
    (h : v ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * c j * v ^ (m - j) = 0) : v ∈ S := by
  rw [pow_add_sum_eq_prod hS hc] at h
  obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h)
  rwa [sub_eq_zero.1 hw0]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **The equation of a root branch.** Let `b₁, …, b_m : V → ℂ` and `v : V → ℂ` be real
differentiable at `x`, with `v(y)` a root of `P_y(W) = Wᵐ + ∑_{j=1}^{m} (-1)ʲ b_j(y) W^(m-j)` for
all `y` near `x`. Let `R` be a multiset of `m` points with `b_j(x) = e_j(R)`, so that `R` is the
multiset of roots of `P_x` and `v(x) ∈ R`, and let `ν, μ` be `(0,1)`-forms at `x`. Then, with the
remainders

`r_j = \bar∂ b_j(x) + j b_j(x) ν + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ`

of the equation of the elementary symmetric functions of `m` solutions of `\bar∂ + ν W + μ \bar W`,

`∏_{w ∈ R ∖ v(x)} (v(x) - w) • (\bar∂ v(x) + v(x) ν + \bar v(x) μ) =
  ∑_{j=1}^{m} (-1)^(j-1) v(x)^(m-j) r_j`. -/
theorem prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum {m : ℕ} {b : ℕ → V → ℂ}
    {v : V → ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, DifferentiableAt ℝ (b j) x)
    (hv : DifferentiableAt ℝ v x)
    (hroot : ∀ᶠ y in 𝓝 x, v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j) = 0)
    {R : Multiset ℂ} (hR : Multiset.card R = m) (hbR : ∀ j ∈ Icc 1 m, b j x = R.esymm j)
    (ν μ : V →L⋆[ℂ] ℂ) :
    ((R.erase (v x)).map fun w ↦ v x - w).prod •
        (conjWirtingerDeriv v x + v x • ν + conj (v x) • μ) =
      ∑ j ∈ Icc 1 m, ((-1) ^ (j - 1) * v x ^ (m - j)) •
        (conjWirtingerDeriv (b j) x + (j * b j x) • ν +
          (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ) := by
  have hvR : v x ∈ R := mem_of_pow_add_sum_eq_zero hR hbR hroot.self_of_nhds
  -- Differentiating `P_y(v(y)) = 0` gives `P_x'(v) \bar∂ v = ∑ (-1)^(j-1) v^(m-j) \bar∂ b_j`.
  have hterm : ∀ j ∈ Icc 1 m,
      DifferentiableAt ℝ (fun y ↦ (-1) ^ j * b j y * v y ^ (m - j)) x := fun j hj ↦
    ((differentiableAt_const _).mul (hb j hj)).mul (hv.pow _)
  have hroot' : (fun y ↦ v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j)) =ᶠ[𝓝 x]
      fun _ ↦ (0 : ℂ) := hroot
  have hzero : conjWirtingerDeriv
      (fun y ↦ v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j)) x = 0 := by
    rw [hroot'.conjWirtingerDeriv_eq]
    exact (differentiableAt_const _).conjWirtingerDeriv_eq_zero
  have hsum : conjWirtingerDeriv
      (fun y ↦ v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j)) x =
        conjWirtingerDeriv (fun y ↦ v y ^ m) x +
          conjWirtingerDeriv (fun y ↦ ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j)) x :=
    conjWirtingerDeriv_add (hv.pow m) (DifferentiableAt.fun_sum hterm)
  rw [hsum, conjWirtingerDeriv_fun_sum hterm, conjWirtingerDeriv_fun_pow hv] at hzero
  have hmul : ∀ j ∈ Icc 1 m, conjWirtingerDeriv (fun y ↦ (-1) ^ j * b j y * v y ^ (m - j)) x =
      ((-1) ^ j * b j x * ((m - j : ℕ) * v x ^ (m - j - 1))) • conjWirtingerDeriv v x -
        ((-1) ^ (j - 1) * v x ^ (m - j)) • conjWirtingerDeriv (b j) x := by
    intro j hj
    have hsign : (-1 : ℂ) ^ (j - 1) * (-1) = (-1) ^ j := by
      rw [← pow_succ, Nat.sub_add_cancel (mem_Icc.1 hj).1]
    rw [conjWirtingerDeriv_fun_mul (f := fun y ↦ (-1) ^ j * b j y) (g := fun y ↦ v y ^ (m - j))
        ((differentiableAt_const _).mul (hb j hj)) (hv.pow _),
      conjWirtingerDeriv_fun_pow hv,
      conjWirtingerDeriv_fun_mul (f := fun _ ↦ (-1) ^ j) (differentiableAt_const _) (hb j hj),
      (differentiableAt_const _).conjWirtingerDeriv_eq_zero, ← hsign]
    module
  rw [sum_congr rfl hmul, sum_sub_distrib, ← sum_smul, ← add_sub_assoc, ← add_smul,
    sub_eq_zero] at hzero
  -- The coefficient of `\bar∂ v` is `P_x'(v(x)) = ∏_{w ∈ R ∖ v(x)} (v(x) - w)`.
  have hP' : (m * v x ^ (m - 1) +
      ∑ j ∈ Icc 1 m, (-1) ^ j * b j x * ((m - j : ℕ) * v x ^ (m - j - 1))) =
        ((R.erase (v x)).map fun w ↦ v x - w).prod := by
    rw [Multiset.prod_map_sub_erase_eq_sum_esymm hR hvR]
    exact congrArg _ (sum_congr rfl fun j hj ↦ by rw [hbR j hj])
  -- The coefficients of `ν` and `μ` are `v(x) P_x'(v(x))` and `\bar v(x) P_x'(v(x))`.
  have hν : ∑ j ∈ Icc 1 m, (-1) ^ (j - 1) * v x ^ (m - j) * (j * b j x) =
      v x * ((R.erase (v x)).map fun w ↦ v x - w).prod := by
    rw [← Multiset.sum_mul_esymm_eq_mul_prod_map_sub_erase hR hvR]
    exact sum_congr rfl fun j hj ↦ by rw [hbR j hj]
  rw [hP'] at hzero
  simp only [smul_add, sum_add_distrib, smul_smul, ← sum_smul]
  rw [← hzero, hν, Multiset.sum_mul_sum_map_mul_esymm_erase hR hvR conj]
  module

/-- **Simple root branches solve `D_C`.** Under the hypotheses of
`TauCeti.prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum`, if `v(x)` is a simple root of
`P_x`, that is `R.count (v x) = 1`, and the remainders `r_j` all vanish, then
`\bar∂ v(x) + v(x) ν + \bar v(x) μ = 0`. -/
theorem conjWirtingerDeriv_add_add_eq_zero_of_root {m : ℕ} {b : ℕ → V → ℂ} {v : V → ℂ} {x : V}
    (hb : ∀ j ∈ Icc 1 m, DifferentiableAt ℝ (b j) x) (hv : DifferentiableAt ℝ v x)
    (hroot : ∀ᶠ y in 𝓝 x, v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j) = 0)
    {R : Multiset ℂ} (hR : Multiset.card R = m) (hbR : ∀ j ∈ Icc 1 m, b j x = R.esymm j)
    (hvR : R.count (v x) = 1) (ν μ : V →L⋆[ℂ] ℂ)
    (heq : ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) x + (j * b j x) • ν +
      (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ = 0) :
    conjWirtingerDeriv v x + v x • ν + conj (v x) • μ = 0 := by
  have h := prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum hb hv hroot hR hbR ν μ
  rw [sum_congr rfl fun j hj ↦ by rw [heq j hj, smul_zero], sum_const_zero] at h
  exact (smul_eq_zero.1 h).resolve_left (Multiset.prod_map_sub_erase_ne_zero hvR)

/-- **Root branches through a simple root.** Let `V` be complete, let `b₁, …, b_m : V → ℂ` be `Cⁿ`
at `x`, `n ≠ 0`, with `b_j(x) = e_j(R)` for a multiset `R` of `m` points, and let `v₀` be a simple
root of `P_x`, that is `R.count v₀ = 1`. Then near `(x, v₀)` the zero set of
`P_y(w) = wᵐ + ∑_{j=1}^{m} (-1)ʲ b_j(y) w^(m-j)` is the graph of a function `v` which is `Cⁿ` at
`x`, with `v(x) = v₀`. -/
theorem exists_contDiffAt_root_branch [CompleteSpace V] {n : WithTop ℕ∞} (hn : n ≠ 0) {m : ℕ}
    {b : ℕ → V → ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, ContDiffAt ℝ n (b j) x) {R : Multiset ℂ}
    (hR : Multiset.card R = m) (hbR : ∀ j ∈ Icc 1 m, b j x = R.esymm j) {v₀ : ℂ}
    (hv₀ : R.count v₀ = 1) :
    ∃ v : V → ℂ, v x = v₀ ∧ ContDiffAt ℝ n v x ∧
      ∀ᶠ p in 𝓝 (x, v₀),
        p.2 ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j p.1 * p.2 ^ (m - j) = 0 ↔ v p.1 = p.2 := by
  set F : V × ℂ → ℂ := fun p ↦ p.2 ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j p.1 * p.2 ^ (m - j)
    with hF
  set Q : Polynomial ℂ := (R.map fun u ↦ Polynomial.X - Polynomial.C u).prod with hQ
  have hmem : v₀ ∈ R := Multiset.count_pos.1 (by omega)
  -- At `y = x` the polynomial is `Q = ∏_{w ∈ R} (W - w)`.
  have hFx : (fun w ↦ F (x, w)) = fun w ↦ Q.eval w := by
    funext w
    simp only [hF, hQ, Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact pow_add_sum_eq_prod hR hbR w
  have hF0 : F (x, v₀) = 0 := by
    simp only [hF]
    rw [pow_add_sum_eq_prod hR hbR]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨v₀, hmem, sub_self v₀⟩)
  have hFc : ContDiffAt ℝ n F (x, v₀) := by
    refine (contDiffAt_snd.pow m).add (ContDiffAt.sum fun j hj ↦ ?_)
    exact (contDiffAt_const.mul (ContDiffAt.comp (x, v₀) (hb j hj) contDiffAt_fst)).mul
      (contDiffAt_snd.pow _)
  -- The partial derivative in `w` is multiplication by `Q'(v₀) = ∏_{w ∈ R ∖ v₀} (v₀ - w) ≠ 0`.
  have hQ' : Q.derivative.eval v₀ ≠ 0 := by
    rw [hQ, Polynomial.eval_multiset_prod_X_sub_C_derivative hmem]
    exact Multiset.prod_map_sub_erase_ne_zero hv₀
  have hpartial : fderiv ℝ F (x, v₀) ∘L ContinuousLinearMap.inr ℝ V ℂ =
      ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 _ hQ') : ℂ ≃L[ℝ] ℂ) :
        ℂ →L[ℝ] ℂ) := by
    have h₁ : HasFDerivAt (fun w ↦ F (x, w)) (fderiv ℝ F (x, v₀) ∘L ContinuousLinearMap.inr ℝ V ℂ)
        v₀ :=
      (hFc.differentiableAt hn).hasFDerivAt.comp v₀ (hasFDerivAt_prodMk_right x v₀)
    have h₂ : HasFDerivAt (fun w ↦ F (x, w))
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Q.derivative.eval v₀)).restrictScalars ℝ)
        v₀ := by
      rw [hFx]
      exact (Q.hasDerivAt v₀).hasFDerivAt.restrictScalars ℝ
    rw [h₁.unique h₂]
    ext w
    simp [mul_comm]
  have hinv : (fderiv ℝ F (x, v₀) ∘L ContinuousLinearMap.inr ℝ V ℂ).IsInvertible :=
    hpartial ▸ ContinuousLinearMap.isInvertible_equiv
  refine ⟨hFc.implicitFunction hn hinv, hFc.implicitFunction_apply_self hn hinv,
    hFc.contDiffAt_implicitFunction hn hinv, ?_⟩
  simpa only [hF0] using hFc.eventually_apply_eq_iff_implicitFunction hn hinv

/-- **Simple root branches solve `D_C`.** Let `V` be complete, let `b₁, …, b_m : V → ℂ` be `C¹` at
`x`, and for `y` near `x` let `R(y)` be the multiset of the `m` roots of
`P_y(W) = Wᵐ + ∑_{j=1}^{m} (-1)ʲ b_j(y) W^(m-j)`, that is `b_j(y) = e_j(R(y))`. Suppose that near
`x` the `b_j` satisfy the equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`.

Then through a simple root `v₀` of `P_x` there is a branch `v`, `C¹` at `x` with `v(x) = v₀`, whose
graph is the zero set of `P` near `(x, v₀)`, and `\bar∂ v + v ν + \bar v μ = 0` near `x`. -/
theorem exists_root_branch_conjWirtingerDeriv_add_add_eq_zero [CompleteSpace V] {m : ℕ}
    {b : ℕ → V → ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, ContDiffAt ℝ 1 (b j) x) {R : V → Multiset ℂ}
    (hR : ∀ᶠ y in 𝓝 x, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    {v₀ : ℂ} (hv₀ : (R x).count v₀ = 1) (ν μ : V → V →L⋆[ℂ] ℂ)
    (heq : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ v : V → ℂ, v x = v₀ ∧ ContDiffAt ℝ 1 v x ∧
      (∀ᶠ p in 𝓝 (x, v₀),
        p.2 ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j p.1 * p.2 ^ (m - j) = 0 ↔ v p.1 = p.2) ∧
      ∀ᶠ y in 𝓝 x, conjWirtingerDeriv v y + v y • ν y + conj (v y) • μ y = 0 := by
  obtain ⟨v, hvx, hvc, hgraph⟩ :=
    exists_contDiffAt_root_branch one_ne_zero hb hR.self_of_nhds.1 hR.self_of_nhds.2 hv₀
  refine ⟨v, hvx, hvc, hgraph, ?_⟩
  -- The graph of `v` lies in the zero set of `P` near `x`.
  have hgraph' : Tendsto (fun y ↦ (y, v y)) (𝓝 x) (𝓝 (x, v₀)) :=
    tendsto_id.prodMk_nhds (hvx ▸ hvc.continuousAt.tendsto)
  have hroot : ∀ᶠ y in 𝓝 x, v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j) = 0 :=
    (hgraph'.eventually hgraph).mono fun y hy ↦ hy.2 rfl
  -- The derivative `P_y'(v(y))` is continuous in `y` and nonzero at `x`, hence near `x`.
  set G : V → ℂ := fun y ↦ m * v y ^ (m - 1) +
    ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * ((m - j : ℕ) * v y ^ (m - j - 1)) with hG
  have hGc : ContinuousAt G x := by
    refine ((contDiffAt_const.mul (hvc.pow _)).add (ContDiffAt.sum fun j hj ↦ ?_)).continuousAt
    exact (contDiffAt_const.mul (hb j hj)).mul (contDiffAt_const.mul (hvc.pow _))
  -- At a root `v(y) ∈ R(y)`, `G(y)` is `∏_{w ∈ R(y) ∖ v(y)} (v(y) - w)`.
  have hGprod : ∀ y, Multiset.card (R y) = m → (∀ j ∈ Icc 1 m, b j y = (R y).esymm j) →
      v y ∈ R y → G y = (((R y).erase (v y)).map fun w ↦ v y - w).prod := by
    intro y hcard hbR hmem
    rw [Multiset.prod_map_sub_erase_eq_sum_esymm hcard hmem, hG]
    exact congrArg _ (sum_congr rfl fun j hj ↦ by rw [hbR j hj])
  have hGx : G x ≠ 0 := by
    have hmem : v x ∈ R x := hvx ▸ Multiset.count_pos.1 (by omega)
    rw [hGprod x hR.self_of_nhds.1 hR.self_of_nhds.2 hmem, hvx]
    exact Multiset.prod_map_sub_erase_ne_zero hv₀
  have hbd : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, DifferentiableAt ℝ (b j) y :=
    (eventually_all_finset _).2 fun j hj ↦
      ((hb j hj).eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y :=
    (hvc.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  filter_upwards [hR, heq, hroot, hroot.eventually_nhds, hGc.eventually_ne hGx, hbd, hvd] with
    y ⟨hcard, hbR⟩ hy hry hry' hGy hby hvy
  -- At `y`, `P_y'(v(y)) • D_C v(y)` is a combination of the vanishing remainders.
  have hmem : v y ∈ R y := mem_of_pow_add_sum_eq_zero hcard hbR hry
  have hne : (((R y).erase (v y)).map fun w ↦ v y - w).prod ≠ 0 :=
    hGprod y hcard hbR hmem ▸ hGy
  have h := prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum hby hvy hry' hcard hbR (ν y) (μ y)
  rw [sum_congr rfl fun j hj ↦ by rw [hy j hj, smul_zero], sum_const_zero] at h
  exact (smul_eq_zero.1 h).resolve_left hne

end TauCeti
