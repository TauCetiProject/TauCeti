/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Calculus.ContDiff.Resultant
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
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
* `TauCeti.conjWirtingerDeriv_add_add_eq_zero_of_root`: consequently, at a point `x` where `v(x)` is
  a simple root of `P_x` and the remainders `r_j(x)` vanish, `D_C v(x) = 0`.
* `TauCeti.exists_contDiffAt_root_branch`: if the `b_j` are `Cⁿ` at `x`, `n ≠ 0`, then near a simple
  root `v₀` of `P_x` the zero set `{(y, w) : P_y(w) = 0}` is the graph of a `Cⁿ` function `v` with
  `v(x) = v₀` (implicit function theorem).
* `TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`: if the `b_j` are `Cⁿ`, `n ≠ 0`,
  and the equation holds with zero remainder near `x`, this branch solves `D_C v = 0` near `x`.

At the collisions of roots, where `P'` vanishes, the roots need not be differentiable. When the
base is a domain `Ω ⊆ ℂ`, the collisions are nevertheless isolated:

* `TauCeti.setOf_nodup_mem_codiscreteWithin_of_conjWirtingerDeriv_add_add_eq_zero`: if the `b_j`
  are `C¹` on a connected open `Ω ⊆ ℂ` and satisfy the equation with zero remainder there, with
  continuous `ν` and `μ`, and the roots are distinct at one point, then the points of `Ω` where
  two roots collide have no accumulation point in `Ω`.

The proof uses the collision product `δ = ∏_{w ∈ R} ∏_{u ∈ R ∖ w} (w - u)`, up to sign the
discriminant of `P`. As the resultant of `P` and `P'` it is `C¹` in `y`
(`ContDiffOn.polynomial_resultant`), also across collisions. Near a point with distinct roots it is
a product of `m (m - 1)` differences of the branches above, each a solution of `D_C`, so
`|\bar∂ δ| ≤ m (m - 1) (|ν| + |μ|) |δ|` (`TauCeti.norm_conjWirtingerDeriv_finset_prod_le`). The
similarity principle in the form `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_norm_le` then makes
the zeros of `δ` isolated. Normalizing the root multigraph across the isolated collisions, with
branch multiplicities, is not done here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle).
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

/-- If `c_j = e_j(S)` for `1 ≤ j ≤ m` and `v ∈ S`, the derivative
`m v^(m-1) + ∑_{j=1}^{m} (-1)ʲ (m - j) c_j v^(m-j-1)` of `Wᵐ + ∑_{j=1}^{m} (-1)ʲ c_j W^(m-j)` at
`W = v` is `∏_{w ∈ S ∖ v} (v - w)`. -/
private theorem mul_pow_add_sum_eq_prod_erase {S : Multiset ℂ} {m : ℕ}
    (hS : Multiset.card S = m) {c : ℕ → ℂ} (hc : ∀ j ∈ Icc 1 m, c j = S.esymm j) {v : ℂ}
    (hv : v ∈ S) :
    m * v ^ (m - 1) + ∑ j ∈ Icc 1 m, (-1) ^ j * c j * ((m - j : ℕ) * v ^ (m - j - 1)) =
      ((S.erase v).map fun w ↦ v - w).prod := by
  rw [Multiset.prod_map_sub_erase_eq_sum_esymm hS hv]
  exact congrArg _ (sum_congr rfl fun j hj ↦ by rw [hc j hj])

/-- A root of `Wᵐ + ∑_{j=1}^{m} (-1)ʲ c_j W^(m-j)`, with `c_j = e_j(S)`, lies in `S`. -/
private theorem mem_of_pow_add_sum_eq_zero {S : Multiset ℂ} {v : ℂ} {m : ℕ}
    (hS : Multiset.card S = m) {c : ℕ → ℂ} (hc : ∀ j ∈ Icc 1 m, c j = S.esymm j)
    (h : v ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * c j * v ^ (m - j) = 0) : v ∈ S := by
  rw [pow_add_sum_eq_prod hS hc] at h
  exact Multiset.prod_map_sub_eq_zero_iff.1 h

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
  rw [sum_congr rfl hmul, sum_sub_distrib, ← sum_smul] at hzero
  -- The coefficient of `\bar∂ v` is `P_x'(v(x)) = ∏_{w ∈ R ∖ v(x)} (v(x) - w)`.
  have hdv : ((R.erase (v x)).map fun w ↦ v x - w).prod • conjWirtingerDeriv v x =
      ∑ j ∈ Icc 1 m, ((-1) ^ (j - 1) * v x ^ (m - j)) • conjWirtingerDeriv (b j) x := by
    rw [← mul_pow_add_sum_eq_prod_erase hR hbR hvR]
    linear_combination (norm := module) hzero
  -- The coefficients of `ν` and `μ` are `v(x) P_x'(v(x))` and `\bar v(x) P_x'(v(x))`.
  have hν : ∑ j ∈ Icc 1 m, (-1) ^ (j - 1) * v x ^ (m - j) * (j * b j x) =
      v x * ((R.erase (v x)).map fun w ↦ v x - w).prod := by
    rw [← Multiset.sum_mul_esymm_eq_mul_prod_map_sub_erase hR hvR]
    exact sum_congr rfl fun j hj ↦ by rw [hbR j hj]
  simp only [smul_add, sum_add_distrib, smul_smul, ← sum_smul]
  rw [← hdv, hν, Multiset.sum_mul_sum_map_mul_esymm_erase hR hvR conj]
  module

/-- Under the hypotheses of `TauCeti.prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum`, if
`P_x'(v(x)) = ∏_{w ∈ R ∖ v(x)} (v(x) - w)` is nonzero and the remainders `r_j` all vanish, then
`\bar∂ v(x) + v(x) ν + \bar v(x) μ = 0`. -/
private theorem conjWirtingerDeriv_add_add_eq_zero_of_prod_ne_zero {m : ℕ} {b : ℕ → V → ℂ}
    {v : V → ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, DifferentiableAt ℝ (b j) x)
    (hv : DifferentiableAt ℝ v x)
    (hroot : ∀ᶠ y in 𝓝 x, v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j) = 0)
    {R : Multiset ℂ} (hR : Multiset.card R = m) (hbR : ∀ j ∈ Icc 1 m, b j x = R.esymm j)
    (hne : ((R.erase (v x)).map fun w ↦ v x - w).prod ≠ 0) (ν μ : V →L⋆[ℂ] ℂ)
    (heq : ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) x + (j * b j x) • ν +
      (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ = 0) :
    conjWirtingerDeriv v x + v x • ν + conj (v x) • μ = 0 := by
  have h := prod_map_sub_smul_conjWirtingerDeriv_add_add_eq_sum hb hv hroot hR hbR ν μ
  rw [sum_congr rfl fun j hj ↦ by rw [heq j hj, smul_zero], sum_const_zero] at h
  exact (smul_eq_zero.1 h).resolve_left hne

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
    conjWirtingerDeriv v x + v x • ν + conj (v x) • μ = 0 :=
  conjWirtingerDeriv_add_add_eq_zero_of_prod_ne_zero hb hv hroot hR hbR
    (Multiset.prod_map_sub_erase_ne_zero hvR) ν μ heq

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

/-- **Simple root branches solve `D_C`.** Let `V` be complete, let `b₁, …, b_m : V → ℂ` be `Cⁿ` at
`x`, `n ≠ 0`, and for `y` near `x` let `R(y)` be the multiset of the `m` roots of
`P_y(W) = Wᵐ + ∑_{j=1}^{m} (-1)ʲ b_j(y) W^(m-j)`, that is `b_j(y) = e_j(R(y))`. Suppose that near
`x` the `b_j` satisfy the equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`.

Then through a simple root `v₀` of `P_x` there is a branch `v`, `Cⁿ` at `x` with `v(x) = v₀`, whose
graph is the zero set of `P` near `(x, v₀)`, and `\bar∂ v + v ν + \bar v μ = 0` near `x`. -/
theorem exists_root_branch_conjWirtingerDeriv_add_add_eq_zero [CompleteSpace V]
    {n : WithTop ℕ∞} (hn : n ≠ 0) {m : ℕ} {b : ℕ → V → ℂ} {x : V}
    (hb : ∀ j ∈ Icc 1 m, ContDiffAt ℝ n (b j) x) {R : V → Multiset ℂ}
    (hR : ∀ᶠ y in 𝓝 x, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    {v₀ : ℂ} (hv₀ : (R x).count v₀ = 1) (ν μ : V → V →L⋆[ℂ] ℂ)
    (heq : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ v : V → ℂ, v x = v₀ ∧ ContDiffAt ℝ n v x ∧
      (∀ᶠ p in 𝓝 (x, v₀),
        p.2 ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j p.1 * p.2 ^ (m - j) = 0 ↔ v p.1 = p.2) ∧
      ∀ᶠ y in 𝓝 x, conjWirtingerDeriv v y + v y • ν y + conj (v y) • μ y = 0 := by
  obtain ⟨v, hvx, hvc, hgraph⟩ :=
    exists_contDiffAt_root_branch hn hb hR.self_of_nhds.1 hR.self_of_nhds.2 hv₀
  refine ⟨v, hvx, hvc, hgraph, ?_⟩
  -- The graph of `v` lies in the zero set of `P` near `x`.
  have hgraph' : Tendsto (fun y ↦ (y, v y)) (𝓝 x) (𝓝 (x, v₀)) :=
    tendsto_id.prodMk_nhds (hvx ▸ hvc.continuousAt.tendsto)
  have hroot : ∀ᶠ y in 𝓝 x, v y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v y ^ (m - j) = 0 :=
    (hgraph'.eventually hgraph).mono fun y hy ↦ hy.2 rfl
  -- The derivative `P_y'(v(y))` is continuous in `y` and nonzero at `x`, hence near `x`.
  set G : V → ℂ := fun y ↦ m * v y ^ (m - 1) +
    ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * ((m - j : ℕ) * v y ^ (m - j - 1))
  have hGc : ContinuousAt G x := by
    refine ((contDiffAt_const.mul (hvc.pow _)).add (ContDiffAt.sum fun j hj ↦ ?_)).continuousAt
    exact (contDiffAt_const.mul (hb j hj)).mul (contDiffAt_const.mul (hvc.pow _))
  -- At a root `v(y) ∈ R(y)`, `G(y)` is `∏_{w ∈ R(y) ∖ v(y)} (v(y) - w)`.
  have hGprod : ∀ y, Multiset.card (R y) = m → (∀ j ∈ Icc 1 m, b j y = (R y).esymm j) →
      v y ∈ R y → G y = (((R y).erase (v y)).map fun w ↦ v y - w).prod :=
    fun y hcard hbR hmem ↦ mul_pow_add_sum_eq_prod_erase hcard hbR hmem
  have hGx : G x ≠ 0 := by
    have hmem : v x ∈ R x := hvx ▸ Multiset.count_pos.1 (by omega)
    rw [hGprod x hR.self_of_nhds.1 hR.self_of_nhds.2 hmem, hvx]
    exact Multiset.prod_map_sub_erase_ne_zero hv₀
  -- Differentiability near `x` comes from the `C¹` regularity, which `Cⁿ` implies.
  have h1 : (1 : WithTop ℕ∞) ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  have hbd : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, DifferentiableAt ℝ (b j) y :=
    (eventually_all_finset _).2 fun j hj ↦
      (((hb j hj).of_le h1).eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y :=
    ((hvc.of_le h1).eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  filter_upwards [hR, heq, hroot, hroot.eventually_nhds, hGc.eventually_ne hGx, hbd, hvd] with
    y ⟨hcard, hbR⟩ hy hry hry' hGy hby hvy
  -- At `y`, `P_y'(v(y)) ≠ 0` and the remainders vanish.
  have hmem : v y ∈ R y := mem_of_pow_add_sum_eq_zero hcard hbR hry
  exact conjWirtingerDeriv_add_add_eq_zero_of_prod_ne_zero hby hvy hry' hcard hbR
    (hGprod y hcard hbR hmem ▸ hGy) (ν y) (μ y) hy

/-! ### Collisions of root branches -/

section Collision

open MeasureTheory Polynomial

/-- The product `∏_{w ∈ S} ∏_{u ∈ S ∖ w} (w - u)` over ordered pairs of distinct members of a
multiset, which up to sign is the discriminant of `∏_{w ∈ S} (W - w)`. -/
private noncomputable def collisionProd (S : Multiset ℂ) : ℂ :=
  (S.map fun w ↦ ((S.erase w).map fun u ↦ w - u).prod).prod

/-- The collision product of `S` vanishes exactly when `S` has a repeated member. -/
private theorem collisionProd_ne_zero_iff {S : Multiset ℂ} : collisionProd S ≠ 0 ↔ S.Nodup := by
  rw [collisionProd, Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map,
    Multiset.nodup_iff_count_le_one]
  constructor
  · intro h a
    by_contra ha
    refine h ⟨a, Multiset.count_pos.1 (by omega), ?_⟩
    rw [Multiset.prod_map_sub_eq_zero_iff, ← Multiset.count_pos, Multiset.count_erase_self]
    omega
  · rintro h ⟨a, -, h0⟩
    rw [Multiset.prod_map_sub_eq_zero_iff, ← Multiset.count_pos, Multiset.count_erase_self] at h0
    have := h a
    omega

/-- Over a finite set, the collision product of the values of a function is the product of their
differences over ordered pairs of distinct indices. -/
private theorem collisionProd_map {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    collisionProd (s.val.map f) = ∏ a ∈ s, ∏ a' ∈ s.erase a, (f a - f a') := by
  rw [collisionProd, Multiset.map_map]
  refine (Finset.prod_map_val s _).trans (Finset.prod_congr rfl fun a ha ↦ ?_)
  rw [Function.comp_apply, ← Multiset.map_erase_of_mem f _ ha, ← Finset.erase_val, Multiset.map_map]
  exact Finset.prod_map_val _ _

/-- The collision product of `S` is the resultant of `Q = ∏_{w ∈ S} (W - w)` and its derivative,
`Res(Q, Q') = ∏_{w ∈ S} Q'(w)`. -/
private theorem resultant_derivative_prod_X_sub_C (S : Multiset ℂ) :
    ((S.map fun a ↦ X - C a).prod).resultant (derivative (S.map fun a ↦ X - C a).prod)
      (Multiset.card S) (Multiset.card S - 1) = collisionProd S := by
  set Q := (S.map fun a ↦ X - C a).prod with hQ
  have hdeg : Q.natDegree = Multiset.card S := natDegree_multiset_prod_X_sub_C_eq_card S
  have hsplit : Q.Splits := Splits.multisetProd fun f hf ↦ by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Splits.X_sub_C a
  have h := resultant_eq_prod_eval Q Q.derivative (Multiset.card S - 1)
    ((natDegree_derivative_le Q).trans (Nat.sub_le_sub_right hdeg.le 1)) hsplit
  rw [hdeg] at h
  rw [h, (monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a).leadingCoeff, one_pow,
    one_mul, hQ, roots_multiset_prod_X_sub_C, collisionProd]
  exact congrArg _ (Multiset.map_congr rfl fun w hw ↦ eval_multiset_prod_X_sub_C_derivative hw)

/-- Near a point `x` where the `m` members of `R(x)` are distinct, if continuous branches `v a` with
`v a x = a`, one through each member, stay in `R(y)`, then they are all of `R(y)`, and the
collision product of `R(y)` is the product of the differences of the branches. -/
private theorem collisionProd_eventuallyEq_prod {X : Type*} [TopologicalSpace X] {m : ℕ}
    {R : X → Multiset ℂ} {x : X}
    (hR : ∀ᶠ y in 𝓝 x, Multiset.card (R y) = m) (hx : (R x).Nodup) {v : ℂ → X → ℂ}
    (hvx : ∀ a ∈ (R x).toFinset, v a x = a)
    (hvc : ∀ a ∈ (R x).toFinset, ContinuousAt (v a) x)
    (hmem : ∀ᶠ y in 𝓝 x, ∀ a ∈ (R x).toFinset, v a y ∈ R y) :
    (fun y ↦ collisionProd (R y)) =ᶠ[𝓝 x]
      fun y ↦ ∏ a ∈ (R x).toFinset, ∏ a' ∈ (R x).toFinset.erase a, (v a y - v a' y) := by
  set F := (R x).toFinset
  have hFcard : F.card = m := by rw [Multiset.toFinset_card_of_nodup hx, hR.self_of_nhds]
  -- The branches are pairwise distinct near `x`.
  have hne : ∀ᶠ y in 𝓝 x, ∀ a ∈ F, ∀ a' ∈ F, a ≠ a' → v a y ≠ v a' y := by
    refine (eventually_all_finset F).2 fun a ha ↦ (eventually_all_finset F).2 fun a' ha' ↦ ?_
    by_cases h : a = a'
    · exact Eventually.of_forall fun _ h' ↦ absurd h h'
    · have h0 : v a x - v a' x ≠ 0 := by rw [hvx a ha, hvx a' ha']; exact sub_ne_zero.2 h
      filter_upwards [((hvc a ha).sub (hvc a' ha')).eventually_ne h0] with y hy _
        using sub_ne_zero.1 hy
  filter_upwards [hmem, hne, hR] with y hy hy' hRy
  have hnd : (F.val.map fun a ↦ v a y).Nodup :=
    Multiset.Nodup.map_on (fun a ha a' ha' h ↦ by_contra fun h' ↦ hy' a ha a' ha' h' h) F.nodup
  -- `m` distinct members of the `m`-element multiset `R(y)` exhaust it.
  have hS : F.val.map (fun a ↦ v a y) = R y := by
    refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun u hu ↦ ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hu
      exact hy a ha
    · rw [hRy, Multiset.card_map, Finset.card_val, hFcard]
  rw [← hS, collisionProd_map]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- When the elementary symmetric functions of `R(y)` are the `C¹` functions `b_j(y)` on `Ω`, so are
the coefficients of `∏_{w ∈ R(y)} (W - w)`. -/
private theorem contDiffOn_coeff_prod_X_sub_C {m : ℕ} {b : ℕ → V → ℂ} {R : V → Multiset ℂ}
    {Ω : Set V} (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) Ω)
    (hR : ∀ y ∈ Ω, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j) (k : ℕ) :
    ContDiffOn ℝ 1 (fun y ↦ ((R y).map fun a ↦ X - C a).prod.coeff k) Ω := by
  rcases lt_trichotomy k m with hk | rfl | hk
  · refine (contDiffOn_const (c := (-1 : ℂ) ^ (m - k)).mul
      (hb (m - k) (mem_Icc.2 ⟨by omega, by omega⟩))).congr fun y hy ↦ ?_
    rw [Multiset.prod_X_sub_C_coeff _ ((hR y hy).1 ▸ hk.le), (hR y hy).1,
      (hR y hy).2 _ (mem_Icc.2 ⟨by omega, by omega⟩)]
  · refine (contDiffOn_const (c := (1 : ℂ))).congr fun y hy ↦ ?_
    rw [Multiset.prod_X_sub_C_coeff _ (hR y hy).1.ge, (hR y hy).1]
    simp
  · refine (contDiffOn_const (c := (0 : ℂ))).congr fun y hy ↦ coeff_eq_zero_of_natDegree_lt ?_
    rw [natDegree_multiset_prod_X_sub_C_eq_card, (hR y hy).1]
    exact hk

/-- When the elementary symmetric functions of `R(y)` are `C¹` on `Ω`, so is the collision product
of `R(y)`, since it is a resultant. -/
private theorem contDiffOn_collisionProd {m : ℕ} {b : ℕ → V → ℂ} {R : V → Multiset ℂ}
    {Ω : Set V} (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) Ω)
    (hR : ∀ y ∈ Ω, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j) :
    ContDiffOn ℝ 1 (fun y ↦ collisionProd (R y)) Ω := by
  have hQ := contDiffOn_coeff_prod_X_sub_C hb hR
  have hQ' : ∀ k, ContDiffOn ℝ 1
      (fun y ↦ (derivative ((R y).map fun a ↦ X - C a).prod).coeff k) Ω := fun k ↦ by
    simp_rw [coeff_derivative]
    exact (hQ (k + 1)).mul contDiffOn_const
  refine (ContDiffOn.polynomial_resultant hQ hQ' m (m - 1)).congr fun y hy ↦ ?_
  rw [← (hR y hy).1]
  exact (resultant_derivative_prod_X_sub_C (R y)).symm

/-- The difference of two solutions of `\bar∂ v + v ν + \bar v μ = 0` at `x` satisfies
`‖\bar∂ (v - v')(x)‖ ≤ (‖ν‖ + ‖μ‖) ‖(v - v')(x)‖`. -/
private theorem norm_conjWirtingerDeriv_sub_le {v v' : V → ℂ} {x : V}
    (hv : DifferentiableAt ℝ v x) (hv' : DifferentiableAt ℝ v' x) (ν μ : V →L⋆[ℂ] ℂ)
    (hD : conjWirtingerDeriv v x + v x • ν + conj (v x) • μ = 0)
    (hD' : conjWirtingerDeriv v' x + v' x • ν + conj (v' x) • μ = 0) :
    ‖conjWirtingerDeriv (fun y ↦ v y - v' y) x‖ ≤ (‖ν‖ + ‖μ‖) * ‖v x - v' x‖ := by
  have heq : conjWirtingerDeriv (fun y ↦ v y - v' y) x =
      -((v x - v' x) • ν + conj (v x - v' x) • μ) := by
    rw [← Pi.sub_def, conjWirtingerDeriv_sub hv hv', map_sub]
    linear_combination (norm := module) hD - hD'
  rw [heq, norm_neg]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_conj]
  ring

/-- **The collision product at simple roots.** Under the hypotheses of
`TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`, at a point `x` where the `m`
roots `R(x)` are distinct, the collision product `δ(y) = ∏_{w ∈ R(y)} ∏_{u ∈ R(y) ∖ w} (w - u)`
satisfies `‖\bar∂ δ(x)‖ ≤ m (m - 1) (‖ν(x)‖ + ‖μ(x)‖) ‖δ(x)‖`: near `x` it is a product of
`m (m - 1)` differences of solutions of `\bar∂ v + v ν + \bar v μ = 0`. -/
private theorem norm_conjWirtingerDeriv_collisionProd_le [CompleteSpace V] {m : ℕ}
    {b : ℕ → V → ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, ContDiffAt ℝ 1 (b j) x) {R : V → Multiset ℂ}
    (hR : ∀ᶠ y in 𝓝 x, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (ν μ : V → V →L⋆[ℂ] ℂ)
    (heq : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    (hx : (R x).Nodup) :
    ‖conjWirtingerDeriv (fun y ↦ collisionProd (R y)) x‖ ≤
      m * ((m - 1 : ℕ) * (‖ν x‖ + ‖μ x‖)) * ‖collisionProd (R x)‖ := by
  set F := (R x).toFinset
  have hFcard : F.card = m := by rw [Multiset.toFinset_card_of_nodup hx, hR.self_of_nhds.1]
  -- A branch through each of the `m` simple roots.
  have hbranch : ∀ a ∈ F, ∃ v : V → ℂ, v x = a ∧ ContDiffAt ℝ 1 v x ∧
      (∀ᶠ p in 𝓝 (x, a),
        p.2 ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j p.1 * p.2 ^ (m - j) = 0 ↔ v p.1 = p.2) ∧
      ∀ᶠ y in 𝓝 x, conjWirtingerDeriv v y + v y • ν y + conj (v y) • μ y = 0 := fun a ha ↦
    exists_root_branch_conjWirtingerDeriv_add_add_eq_zero one_ne_zero hb hR
      (Multiset.count_eq_one_of_mem hx (Multiset.mem_toFinset.1 ha)) ν μ heq
  choose! v hvx hvc hgraph hD using hbranch
  -- Near `x` the branches are roots, so they are all the roots.
  have hmem : ∀ᶠ y in 𝓝 x, ∀ a ∈ F, v a y ∈ R y := by
    refine (eventually_all_finset F).2 fun a ha ↦ ?_
    have hva := (hvc a ha).continuousAt.tendsto
    rw [hvx a ha] at hva
    have ht : Tendsto (fun y ↦ (y, v a y)) (𝓝 x) (𝓝 (x, a)) := tendsto_id.prodMk_nhds hva
    filter_upwards [ht.eventually (hgraph a ha), hR] with y hy hRy
    exact mem_of_pow_add_sum_eq_zero hRy.1 hRy.2 (hy.2 rfl)
  have hprod := collisionProd_eventuallyEq_prod (hR.mono fun _ h ↦ h.1) hx hvx
    (fun a ha ↦ (hvc a ha).continuousAt) hmem
  -- Each difference of two branches solves the same real-linear equation.
  have hfactor : ∀ a ∈ F, ∀ a' ∈ F, DifferentiableAt ℝ (fun y ↦ v a y - v a' y) x ∧
      ‖conjWirtingerDeriv (fun y ↦ v a y - v a' y) x‖ ≤
        (‖ν x‖ + ‖μ x‖) * ‖v a x - v a' x‖ := fun a ha a' ha' ↦
    have hd := (hvc a ha).differentiableAt one_ne_zero
    have hd' := (hvc a' ha').differentiableAt one_ne_zero
    ⟨hd.sub hd', norm_conjWirtingerDeriv_sub_le hd hd' (ν x) (μ x) (hD a ha).self_of_nhds
      (hD a' ha').self_of_nhds⟩
  -- The inner products have `m - 1` factors, the outer product `m`.
  have hinner : ∀ a ∈ F, DifferentiableAt ℝ (fun y ↦ ∏ a' ∈ F.erase a, (v a y - v a' y)) x ∧
      ‖conjWirtingerDeriv (fun y ↦ ∏ a' ∈ F.erase a, (v a y - v a' y)) x‖ ≤
        ((m - 1 : ℕ) * (‖ν x‖ + ‖μ x‖)) * ‖∏ a' ∈ F.erase a, (v a x - v a' x)‖ := by
    intro a ha
    have hf : ∀ a' ∈ F.erase a, _ := fun a' ha' ↦ hfactor a ha a' (Finset.mem_of_mem_erase ha')
    refine ⟨(HasFDerivAt.finsetProd fun a' ha' ↦ (hf a' ha').1.hasFDerivAt).differentiableAt, ?_⟩
    have h := norm_conjWirtingerDeriv_finset_prod_le (fun a' ha' ↦ (hf a' ha').1)
      fun a' ha' ↦ (hf a' ha').2
    rwa [Finset.card_erase_of_mem ha, hFcard] at h
  have h := norm_conjWirtingerDeriv_finset_prod_le (fun a ha ↦ (hinner a ha).1)
    fun a ha ↦ (hinner a ha).2
  have hδx : collisionProd (R x) = ∏ a ∈ F, ∏ a' ∈ F.erase a, (v a x - v a' x) :=
    hprod.self_of_nhds
  rw [hFcard] at h
  rwa [hprod.conjWirtingerDeriv_eq, hδx]

/-- **Collisions of root branches are isolated.** Let `Ω ⊆ ℂ` be open and connected, and let
`b₁, …, b_m` be `C¹` on `Ω`, with `b_j(y) = e_j(R(y))` for the multiset `R(y)` of the `m` roots of
`P_y(W) = Wᵐ - b₁(y) W^(m-1) + ⋯ + (-1)ᵐ b_m(y)`. Suppose that on `Ω` the `b_j` satisfy the
equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`, with continuous coefficients `ν` and `μ`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`.

If the roots are distinct at one point of `Ω`, then the points of `Ω` where two roots collide are
isolated and have no accumulation point in `Ω`.

Away from the collisions the roots move along graphs of solutions of `D_C`
(`TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`). The collision product
`δ = ∏_{w ∈ R} ∏_{u ∈ R ∖ w} (w - u)`, up to sign the discriminant of `P`, is the resultant of
`P` and `P'`, hence `C¹` on `Ω`, and it satisfies `|\bar∂ δ| ≤ m (m - 1) (|ν| + |μ|) |δ|`. By the
similarity principle (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`) its zeros are
isolated unless it vanishes identically. -/
theorem setOf_nodup_mem_codiscreteWithin_of_conjWirtingerDeriv_add_add_eq_zero {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) {m : ℕ} {b : ℕ → ℂ → ℂ}
    (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) Ω) {R : ℂ → Multiset ℂ}
    (hR : ∀ y ∈ Ω, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ} (hν : ContinuousOn ν Ω) (hμ : ContinuousOn μ Ω)
    (heq : ∀ y ∈ Ω, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    (hne : ∃ y ∈ Ω, (R y).Nodup) :
    {y | (R y).Nodup} ∈ codiscreteWithin Ω := by
  set δ : ℂ → ℂ := fun y ↦ collisionProd (R y) with hδ
  have hmain := setOf_ne_zero_mem_codiscreteWithin_of_norm_le
    (K := fun y ↦ 2 * (m * ((m - 1 : ℕ) * (‖ν y‖ + ‖μ y‖)))) hΩ hΩc
    (contDiffOn_collisionProd hb hR)
    (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul
      (hν.norm.add hμ.norm))))
    (fun y hy hδy ↦ by
      -- `∂ₛδ + i ∂ₜδ = 2 \bar∂ δ`, bounded at simple roots by the collision estimate.
      have hev : ∀ᶠ z in 𝓝 y, z ∈ Ω := hΩ.mem_nhds hy
      rw [fderiv_apply_one_add_I_smul_fderiv_apply_I, norm_smul, Complex.norm_two, mul_assoc]
      refine mul_le_mul_of_nonneg_left (((conjWirtingerDeriv δ y).le_opNorm 1).trans ?_)
        zero_le_two
      rw [norm_one, mul_one]
      exact norm_conjWirtingerDeriv_collisionProd_le
        (fun j hj ↦ (hb j hj).contDiffAt (hΩ.mem_nhds hy)) (hev.mono hR) ν μ (hev.mono heq)
        (collisionProd_ne_zero_iff.1 hδy))
    (by
      obtain ⟨y, hy, hyn⟩ := hne
      exact ⟨y, hy, collisionProd_ne_zero_iff.2 hyn⟩)
  simpa only [hδ, collisionProd_ne_zero_iff] using hmain

end Collision

end TauCeti
