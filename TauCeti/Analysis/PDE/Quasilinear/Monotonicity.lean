/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.Sobolev.Poincare.W1p0
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Strong monotonicity and Lipschitz dependence for quasilinear equations

On an open set `Ω ⊆ ℝⁿ` consider the quasilinear divergence-form operator
`Q u = -∂ᵢ(Aⁱʲ(x, u) ∂ⱼu)`, with weak form

`Q(u, φ) = ∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = TauCeti.PDE.energyFormH1 (fun x ↦ A x (u x)) 0 0 u φ`,

where `A(·, s)` is uniformly elliptic with constants `λ, Λ` for every `s` and Lipschitz in `s`,
`|ηᵀ (A(x, s) - A(x, t)) ξ| ≤ L |s - t| ‖η‖ ‖ξ‖`. The operator `Q` is not monotone in general:
the dependence of the coefficient on `u` adds the term `(A(x, u) - A(x, v)) ∇v` to the difference
`A(x, u) ∇u - A(x, v) ∇v`, and nothing controls it when `∇v` is large. Existence of weak
solutions holds without monotonicity
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`), and so does
uniqueness (`TauCeti.PDE.eq_of_forall_energyFormH1_quasilinear_eq`), but neither gives a
quantitative dependence of the solution on the data.

This file proves that `Q` is **strongly monotone near a function with bounded gradient**. Suppose
`Ω` carries the Poincaré inequality `‖w‖₂ ≤ P ‖∇w‖₂` on `W^{1,2}_0(Ω)` and `‖∇v‖ ≤ K` almost
everywhere. Then for every `u` with `u - v ∈ W^{1,2}_0(Ω)`

`(λ - L K P) ‖∇(u - v)‖₂² ≤ Q(u, u - v) - Q(v, u - v)`

(`TauCeti.PDE.mul_norm_gradient_sub_sq_le_energyFormH1_quasilinear_sub`). When `L K P < λ` this
is a strong monotonicity estimate, and it gives **Lipschitz dependence of the solution on the
forcing** in `H¹`: if `u` and `v` are weak solutions of `Q u = ℓ` and `Q v = ℓ'` with the same
boundary values and `‖∇v‖ ≤ K`, then

`‖u - v‖_{H¹} ≤ (P² + 1) ‖ℓ - ℓ'‖ / (λ - L K P)`

(`TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_quasilinear_eq`), with the bounded-domain form
`TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`.
Only `v` needs a bounded gradient. For a coefficient independent of `u` (`L = 0`) the smallness
condition `L K P < λ` holds for every `K`, but `∇v` must still be essentially bounded; the general
linear estimate is in `TauCeti/Analysis/PDE/DirichletProblem/ContinuousDependence.lean`.

## The argument

Write `w = u - v`, so `∇u = ∇w + ∇v`. Pointwise,

`⟨A(u) ∇u, ∇w⟩ - ⟨A(v) ∇v, ∇w⟩ = ⟨A(u) ∇w, ∇w⟩ + ⟨(A(u) - A(v)) ∇v, ∇w⟩
  ≥ λ |∇w|² - L K |w| |∇w|`,

by ellipticity and the Lipschitz bound with `|u - v| = |w|`. Integrating, the Cauchy–Schwarz and
Poincaré inequalities bound `∫ |w| |∇w| ≤ ‖w‖₂ ‖∇w‖₂ ≤ P ‖∇w‖₂²`. For the Lipschitz estimate, test
both equations with `w ∈ W^{1,2}_0(Ω)`: the difference of the two left-hand sides is
`(ℓ - ℓ') w ≤ ‖ℓ - ℓ'‖ ‖w‖_{H¹}`, and `‖w‖_{H¹}² = ‖w‖₂² + ‖∇w‖₂² ≤ (P² + 1) ‖∇w‖₂²`.

## References

* M. Chipot, *Elliptic Equations: An Introductory Course*, Birkhäuser, 2009, Chapter 11
  (quasilinear equations).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Matrix

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {A : EuclideanSpace ℝ ι → ℝ → Matrix ι ι ℝ} {lam Lam L : ℝ}

/-- The pointwise inequality behind strong monotonicity: if `M` is elliptic with constant `λ`,
`|gᵀ (M - N) h| ≤ L |d| ‖g‖ ‖h‖` with `0 ≤ L` and `‖h‖ ≤ K`, then
`gᵀ M (g + h) - gᵀ N h ≥ λ ‖g‖² - L K |d| ‖g‖`. -/
private theorem le_matrixBilinearForm_add_sub_of_norm_le {M N : Matrix ι ι ℝ}
    {g h : EuclideanSpace ℝ ι} {d K : ℝ} (hL : 0 ≤ L)
    (hM : lam * ‖g‖ ^ 2 ≤ M.toQuadraticForm' g)
    (hMN : |g ⬝ᵥ ((M - N) *ᵥ h)| ≤ L * |d| * ‖g‖ * ‖h‖) (hh : ‖h‖ ≤ K) :
    lam * ‖g‖ ^ 2 - L * K * (|d| * ‖g‖) ≤
      matrixBilinearForm M g (g + h) - matrixBilinearForm N g h := by
  have hK : L * |d| * ‖g‖ * ‖h‖ ≤ L * K * (|d| * ‖g‖) := by
    have : L * |d| * ‖g‖ * ‖h‖ = L * (|d| * ‖g‖) * ‖h‖ := by ring
    rw [this, mul_right_comm L K]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  rw [matrixBilinearForm_add_sub_matrixBilinearForm]
  linarith [neg_abs_le (g ⬝ᵥ ((M - N) *ᵥ h))]

/-- The pointwise form of the monotonicity estimate: almost everywhere on `Ω`, the difference of
the two energy densities tested against `∇(u - v)` is at least
`λ ‖∇(u - v)‖² - L K |u - v| ‖∇(u - v)‖` where `‖∇v‖ ≤ K`. -/
private theorem ae_le_matrixBilinearForm_sub {K : ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (hL : 0 ≤ L) {u v : W1p mu Omega 2}
    (hvK : ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient v x‖ ≤ K) :
    ∀ᵐ x ∂mu.restrict Omega,
      lam * ‖W1p.gradient (u - v) x‖ ^ 2 -
          L * K * (‖W1p.value (u - v) x‖ * ‖W1p.gradient (u - v) x‖) ≤
        matrixBilinearForm (A x (W1p.value u x)) (W1p.gradient (u - v) x) (W1p.gradient u x) -
          matrixBilinearForm (A x (W1p.value v x)) (W1p.gradient (u - v) x)
            (W1p.gradient v x) := by
  filter_upwards [W1p.value_sub_ae u v, Lp.coeFn_sub (W1p.gradient u) (W1p.gradient v), hvK,
    ae_restrict_mem Omega.isOpen.measurableSet] with x hw hgw hxK hxΩ
  have hu : W1p.gradient u x = W1p.gradient (u - v) x + W1p.gradient v x := by
    rw [W1p.gradient_sub, hgw, Pi.sub_apply, sub_add_cancel]
  rw [hu, Real.norm_eq_abs, hw, Pi.sub_apply]
  exact le_matrixBilinearForm_add_sub_of_norm_le hL ((hA _).lower_bound hxΩ _)
    (hlip x hxΩ _ _ _ _) hxK

/-- **Strong monotonicity of the quasilinear operator near a function with bounded gradient.**
Let `A(x, s)` be uniformly elliptic with constants `λ, Λ` on `Ω` for every `s` and Lipschitz in
`s` with constant `L ≥ 0`, uniformly in `x ∈ Ω`, and let `Ω` carry the Poincaré inequality
`‖w‖₂ ≤ P ‖∇w‖₂` on `W^{1,2}_0(Ω)`. Let `u, v ∈ W^{1,2}(Ω)`, with `x ↦ A(x, u(x))` and
`x ↦ A(x, v(x))` measurable, satisfy `u - v ∈ W^{1,2}_0(Ω)` and `‖∇v‖ ≤ K` almost everywhere,
with `K ≥ 0`. Then

`(λ - L K P) ‖∇(u - v)‖₂² ≤ ∫_Ω ⟨A(x, u) ∇u - A(x, v) ∇v, ∇(u - v)⟩`. -/
theorem mul_norm_gradient_sub_sq_le_energyFormH1_quasilinear_sub {P K : ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤ P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    {u v : W1p mu Omega 2}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (mu.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (mu.restrict Omega))
    (hvK : ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient v x‖ ≤ K)
    (huv : u - v ∈ w1p0Submodule mu Omega 2) :
    (lam - L * K * P) * ‖W1p.gradient (u - v)‖ ^ 2 ≤
      energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u (u - v) -
        energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v (u - v) := by
  set w := u - v
  -- Freezing the coefficient at `z` gives a uniformly elliptic matrix field.
  have hint (z : W1p mu Omega 2)
      (hz : AEStronglyMeasurable (fun x ↦ A x (W1p.value z x)) (mu.restrict Omega)) :
      Integrable (fun x ↦ matrixBilinearForm (A x (W1p.value z x)) (W1p.gradient w x)
        (W1p.gradient z x)) (mu.restrict Omega) := by
    exact (UniformlyEllipticOn.apply_of_forall hA
      (W1p.value z)).integrable_matrixBilinearForm_gradient hz z w
  have hsq : Integrable (fun x ↦ ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hprod : Integrable (fun x ↦ ‖W1p.value w x‖ * ‖W1p.gradient w x‖) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value w)).norm.integrable_mul (Lp.memLp (W1p.gradient w)).norm
  -- Integrate the pointwise inequality.
  have hmono := integral_mono_ae ((hsq.const_mul lam).sub (hprod.const_mul (L * K)))
    ((hint u hAu).sub (hint v hAv)) (ae_le_matrixBilinearForm_sub hA hlip hL hvK)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hsq.const_mul lam) (hprod.const_mul (L * K)), integral_const_mul,
    integral_const_mul, integral_sub (hint u hAu) (hint v hAv),
    Lp.integral_norm_sq_eq_norm_sq] at hmono
  rw [energyFormH1_zero_zero_eq_setIntegral, energyFormH1_zero_zero_eq_setIntegral]
  -- Cauchy–Schwarz and Poincaré: `∫ |w| ‖∇w‖ ≤ ‖w‖₂ ‖∇w‖₂ ≤ P ‖∇w‖₂²`.
  have hCS : ∫ x in Omega, ‖W1p.value w x‖ * ‖W1p.gradient w x‖ ∂mu ≤
      P * ‖W1p.gradient w‖ ^ 2 := by
    refine (Lp.integral_norm_mul_norm_le (W1p.value w) (W1p.gradient w)).trans ?_
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hpoincare ⟨w, huv⟩) (norm_nonneg _)
  have hLK : L * K * ∫ x in Omega, ‖W1p.value w x‖ * ‖W1p.gradient w x‖ ∂mu ≤
      L * K * (P * ‖W1p.gradient w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hCS (mul_nonneg hL hK)
  nlinarith [hmono, hLK]

omit [DecidableEq ι] in
/-- Testing two weak equations `Q u = ℓ` and `Q v = ℓ'` with `u - v ∈ W^{1,2}_0(Ω)` bounds the
difference of the two energy forms by `‖ℓ - ℓ'‖ ‖u - v‖`. -/
private theorem energyFormH1_sub_le_opNorm_mul_norm {u v : W1p mu Omega 2}
    {ℓ ℓ' : StrongDual ℝ (W1p0 mu Omega 2)} (huv : u - v ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ φ : W1p0 mu Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u φ = ℓ φ)
    (hv : ∀ φ : W1p0 mu Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v φ = ℓ' φ) :
    energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u (u - v) -
      energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v (u - v) ≤ ‖ℓ - ℓ'‖ * ‖u - v‖ := by
  set W : W1p0 mu Omega 2 := ⟨u - v, huv⟩
  have hW : ‖W‖ = ‖u - v‖ := (Submodule.norm_coe W).symm
  have he : (ℓ - ℓ') W = energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u (u - v) -
      energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v (u - v) :=
    (sub_apply ℓ ℓ' W).trans (congrArg₂ (· - ·) (hu W).symm (hv W).symm)
  calc _ = (ℓ - ℓ') W := he.symm
    _ ≤ ‖(ℓ - ℓ') W‖ := le_abs_self _
    _ ≤ ‖ℓ - ℓ'‖ * ‖W‖ := (ℓ - ℓ').le_opNorm W
    _ = ‖ℓ - ℓ'‖ * ‖u - v‖ := by rw [hW]

/-- The arithmetic of the Lipschitz estimate: if `c > 0`, `Q, D, N ≥ 0`, `c G² ≤ D N` and
`N² ≤ Q G²`, then `N ≤ Q D / c`. -/
private theorem le_div_of_mul_sq_le {c G D N Q : ℝ} (hc : 0 < c) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hN : 0 ≤ N) (hmono : c * G ^ 2 ≤ D * N) (hnorm : N ^ 2 ≤ Q * G ^ 2) : N ≤ Q * D / c := by
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  rw [le_div_iff₀ hc]
  -- `c N² ≤ c Q G² ≤ Q D N`, and `N > 0`.
  have h : N * (N * c) ≤ N * (Q * D) := by
    nlinarith [mul_le_mul_of_nonneg_left hnorm hc.le, mul_le_mul_of_nonneg_left hmono hQ]
  exact le_of_mul_le_mul_left h hpos

/-- **Lipschitz dependence on the forcing for quasilinear equations.** Let `A(x, s)` be uniformly
elliptic with constants `λ, Λ` on `Ω` for every `s` and Lipschitz in `s` with constant `L ≥ 0`,
uniformly in `x ∈ Ω`, and let `Ω` carry the Poincaré inequality `‖w‖₂ ≤ P ‖∇w‖₂` on
`W^{1,2}_0(Ω)`. Let `u, v ∈ W^{1,2}(Ω)` be weak solutions of

`-div(A(x, u) ∇u) = ℓ`, `-div(A(x, v) ∇v) = ℓ'`

with the same boundary values `g`, `u - g, v - g ∈ W^{1,2}_0(Ω)`, and with `x ↦ A(x, u(x))` and
`x ↦ A(x, v(x))` measurable. If `‖∇v‖ ≤ K` almost everywhere, with `K ≥ 0` and `L K P < λ`, then

`‖u - v‖_{H¹} ≤ (P² + 1) ‖ℓ - ℓ'‖ / (λ - L K P)`. -/
theorem norm_sub_le_of_forall_energyFormH1_quasilinear_eq {P K : ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤ P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    (hLKP : L * K * P < lam)
    {g u v : W1p mu Omega 2} {ℓ ℓ' : StrongDual ℝ (W1p0 mu Omega 2)}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (mu.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (mu.restrict Omega))
    (hvK : ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient v x‖ ≤ K)
    (hug : u - g ∈ w1p0Submodule mu Omega 2) (hvg : v - g ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ φ : W1p0 mu Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u φ = ℓ φ)
    (hv : ∀ φ : W1p0 mu Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v φ = ℓ' φ) :
    ‖u - v‖ ≤ (P ^ 2 + 1) * ‖ℓ - ℓ'‖ / (lam - L * K * P) := by
  have huv : u - v ∈ w1p0Submodule mu Omega 2 := by
    simpa using (w1p0Submodule mu Omega 2).sub_mem hug hvg
  exact le_div_of_mul_sq_le (sub_pos.2 hLKP) (by positivity) (ℓ - ℓ').opNorm_nonneg
    (norm_nonneg _)
    ((mul_norm_gradient_sub_sq_le_energyFormH1_quasilinear_sub hA hlip hL hK hpoincare hAu hAv hvK
      huv).trans (energyFormH1_sub_le_opNorm_mul_norm huv hu hv))
    (W1p.norm_sq_le_mul_norm_gradient_sq_of_norm_value_le (hpoincare ⟨_, huv⟩))

/-- **Lipschitz dependence on the forcing on a bounded domain.** Let `Ω ⊆ B(z, R) ⊆ ℝⁿ⁺¹`, let
`A(x, s)` be uniformly elliptic with constants `λ, Λ` on `Ω` for every `s` and Lipschitz in `s`
with constant `L ≥ 0`, uniformly in `x ∈ Ω`. Let `u, v ∈ W^{1,2}(Ω)` be weak solutions of
`-div(A(x, u) ∇u) = ℓ` and `-div(A(x, v) ∇v) = ℓ'` with the same boundary values `g`, and with
`x ↦ A(x, u(x))` and `x ↦ A(x, v(x))` measurable. If `‖∇v‖ ≤ K` almost everywhere, with `K ≥ 0`
and `2 L K R < λ`, then `‖u - v‖_{H¹} ≤ ((2R)² + 1) ‖ℓ - ℓ'‖ / (λ - 2 L K R)`. -/
theorem norm_sub_le_of_forall_energyFormH1_quasilinear_eq_of_subset_ball
    {n : ℕ}
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ (Fin (n + 1)),
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (hL : 0 ≤ L) {K : ℝ} (hK : 0 ≤ K) {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hLKR : L * K * (2 * R) < lam)
    {g u v : W1p volume Omega 2} {ℓ ℓ' : StrongDual ℝ (W1p0 volume Omega 2)}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (volume.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (volume.restrict Omega))
    (hvK : ∀ᵐ x ∂volume.restrict Omega, ‖W1p.gradient v x‖ ≤ K)
    (hug : u - g ∈ w1p0Submodule volume Omega 2) (hvg : v - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ φ : W1p0 volume Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u φ = ℓ φ)
    (hv : ∀ φ : W1p0 volume Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v φ = ℓ' φ) :
    ‖u - v‖ ≤ ((2 * R) ^ 2 + 1) * ‖ℓ - ℓ'‖ / (lam - L * K * (2 * R)) :=
  norm_sub_le_of_forall_energyFormH1_quasilinear_eq hA hlip hL hK
    (fun w ↦ W1p.norm_value_le_mul_norm_gradient_of_subset_ball hOmega w.property) hLKR hAu hAv
    hvK hug hvg hu hv

end TauCeti.PDE
