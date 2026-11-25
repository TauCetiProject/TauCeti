/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet

/-!
# The scalar curvature of a cylinder jet

A metric of the form `g_t + dt²` on `M × ℝ`, for a path `t ↦ g_t` of metrics on `M`, reads in a
product chart with coordinates `(z, t)` as the block Gram matrix `fromBlocks A 0 0 1`: the time
direction is a unit vector orthogonal to the spatial directions, everywhere. Its coordinate jet
therefore has vanishing derivatives in every coefficient involving the time direction, and its
scalar curvature is a universal expression in the spatial jet and the first and second time
derivatives `A' = ∂ₜ A`, `A'' = ∂ₜ² A` of the spatial Gram matrix:

`Scal = Scal(A) - tr (A⁻¹ A'') + (3 / 4) tr ((A⁻¹ A')²) - (1 / 4) (tr (A⁻¹ A'))²`

(`TauCeti.Manifold.scalarCurvatureOfJet_fromBlocks_one`), where `Scal(A)` is the scalar curvature
of the spatial jet, that of the slice metric `g_t`. Writing `S = A⁻¹ A' / 2` for the shape operator
of the slices `t = const`, this is the classical identity
`Scal = Scal(g_t) - 2 tr S' - tr (S²) - (tr S)²`, obtained from the Gauss equation and the Riccati
equation of the slices. Here it is obtained from the Christoffel symbols of the block jet.

The time derivatives enter only through the second derivative `A''` linearly and through `A'`
quadratically, and no mixed space-time derivative survives. So reparametrising the time coordinate
by a function `φ` with `φ' = a` and `φ'' = b`, which turns `A'` into `a A'` and `A''` into
`a² A'' + b A'`, turns the scalar curvature `Scal` into
`(1 - a²) Scal(A) + a² Scal - b tr (A⁻¹ A')`.
On manifolds this is
`Bundle.ContMDiffRiemannianMetric.scalarCurvature_compTime_of_forall_inner_eq_cylinder`, the source
of the bending term in the Gromov–Lawson surgery construction.

## Main results

* `TauCeti.Manifold.scalarCurvatureOfJet_fromBlocks_one`: the scalar curvature of the jet of a
  cylinder metric `g_t + dt²`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 3, §3.2 (the
  curvature of metrics `dr² + g_r`, the radial curvature equation and the tangential curvature
  equation).
* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
  {dg : ι ⊕ Unit → ι ⊕ Unit → ι ⊕ Unit → ℝ} {ddg : ι ⊕ Unit → ι ⊕ Unit → ι ⊕ Unit → ι ⊕ Unit → ℝ}

variable (hA : IsUnit A) (hd₁ : ∀ k i, dg k (.inl i) (.inr ()) = 0)
  (hd₂ : ∀ k j, dg k (.inr ()) (.inl j) = 0) (hd₃ : ∀ k, dg k (.inr ()) (.inr ()) = 0)
  (hdd₁ : ∀ m k i, ddg m k (.inl i) (.inr ()) = 0) (hdd₂ : ∀ m k j, ddg m k (.inr ()) (.inl j) = 0)
  (hdd₃ : ∀ m k, ddg m k (.inr ()) (.inr ()) = 0)
  (hds : ∀ i j, dg (.inr ()) (.inl i) (.inl j) = dg (.inr ()) (.inl j) (.inl i))

include hA in
private theorem inv_fromBlocks_one :
    (fromBlocks A 0 0 (1 : Matrix Unit Unit ℝ))⁻¹ = fromBlocks A⁻¹ 0 0 1 := by
  rw [inv_fromBlocks_zero₁₂_of_isUnit_iff A 0 1 (iff_of_true hA isUnit_one)]
  simp

include hA hd₁ in
private theorem christoffel_inl_inl_inl (i j k : ι) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inl i) (.inl j) (.inl k) =
      christoffelOfJet A (fun k i j ↦ dg (.inl k) (.inl i) (.inl j)) i j k := by
  simp [christoffelOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₁]

include hA hd₁ in
private theorem christoffel_inl_inl_inr (i j : ι) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inl i) (.inl j) (.inr ()) =
      -(2⁻¹ * dg (.inr ()) (.inl i) (.inl j)) := by
  simp [christoffelOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₁]

include hA hd₁ hd₂ hds in
private theorem christoffel_inl_inr_inl (i k : ι) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inl i) (.inr ()) (.inl k) =
      2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) k i := by
  simp only [christoffelOfJet_def, inv_fromBlocks_one hA, hd₁, hd₂, sub_zero, zero_add, add_zero,
    Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, Matrix.mul_apply, of_apply]
  congr 1
  exact Finset.sum_congr rfl fun l _ ↦ by rw [hds]

include hA hd₁ hd₂ hds in
private theorem christoffel_inr_inl_inl (j k : ι) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inr ()) (.inl j) (.inl k) =
      2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) k j := by
  simp only [christoffelOfJet_def, inv_fromBlocks_one hA, hd₁, hd₂, sub_zero, zero_add, add_zero,
    Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, Matrix.mul_apply, of_apply]
  congr 1
  exact Finset.sum_congr rfl fun l _ ↦ by rw [hds]

include hA hd₂ hd₃ in
private theorem christoffel_inr_inr (a : ι ⊕ Unit) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inr ()) (.inr ()) a = 0 := by
  rcases a with k | ⟨⟩ <;>
    simp [christoffelOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₂, hd₃]

include hA hd₁ hd₂ hd₃ in
private theorem christoffel_inl_inr_inr (i : ι) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inl i) (.inr ()) (.inr ()) = 0 := by
  simp [christoffelOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₁, hd₂, hd₃]

include hA hd₁ hd₂ hd₃ in
private theorem christoffel_inr_inl_inr (j : ι) :
    christoffelOfJet (fromBlocks A 0 0 1) dg (.inr ()) (.inl j) (.inr ()) = 0 := by
  simp [christoffelOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₁, hd₂, hd₃]

include hA hd₁ hd₂ in
private theorem christoffelDeriv_inl_inl_inl_inl (m i j k : ι) :
    christoffelDerivOfJet (fromBlocks A 0 0 1) dg ddg (.inl m) (.inl i) (.inl j) (.inl k) =
      christoffelDerivOfJet A (fun k i j ↦ dg (.inl k) (.inl i) (.inl j))
        (fun m k i j ↦ ddg (.inl m) (.inl k) (.inl i) (.inl j)) m i j k := by
  simp [christoffelDerivOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₂,
    christoffel_inl_inl_inl hA hd₁]

include hA hd₁ hd₃ hdd₁ in
private theorem christoffelDeriv_inr_inl_inl_inr (j k : ι) :
    christoffelDerivOfJet (fromBlocks A 0 0 1) dg ddg (.inr ()) (.inl j) (.inl k) (.inr ()) =
      -(2⁻¹ * ddg (.inr ()) (.inr ()) (.inl j) (.inl k)) := by
  simp [christoffelDerivOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₁, hd₃, hdd₁]

include hA hd₁ hd₃ hdd₁ hdd₂ hdd₃ in
private theorem christoffelDeriv_inl_inr_inl_inr (j k : ι) :
    christoffelDerivOfJet (fromBlocks A 0 0 1) dg ddg (.inl j) (.inr ()) (.inl k) (.inr ()) =
      0 := by
  simp [christoffelDerivOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₁, hd₃, hdd₁,
    hdd₂, hdd₃]

include hA hd₂ hd₃ hdd₂ hdd₃ in
private theorem christoffelDeriv_inl_inr_inr_inl (i l : ι) :
    christoffelDerivOfJet (fromBlocks A 0 0 1) dg ddg (.inl i) (.inr ()) (.inr ()) (.inl l) =
      0 := by
  simp [christoffelDerivOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hdd₂, hdd₃,
    christoffel_inr_inr hA hd₂ hd₃]

include hA hd₁ hd₂ hds hdd₁ hdd₂ in
private theorem christoffelDeriv_inr_inl_inr_inl (i l : ι) :
    christoffelDerivOfJet (fromBlocks A 0 0 1) dg ddg (.inr ()) (.inl i) (.inr ()) (.inl l) =
      ∑ l', A⁻¹ l l' * (2⁻¹ * ddg (.inr ()) (.inr ()) (.inl i) (.inl l') -
        ∑ q, dg (.inr ()) (.inl q) (.inl l') *
          (2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) q i)) := by
  simp [christoffelDerivOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type, hd₂, hdd₁, hdd₂,
    christoffel_inl_inr_inl hA hd₁ hd₂ hds]

include hA hd₁ hd₂ hds in
private theorem riemann_inl_inl_inl_inl (i j k l : ι) :
    riemannOfJet (fromBlocks A 0 0 1) dg ddg (.inl i) (.inl j) (.inl k) (.inl l) =
      riemannOfJet A (fun k i j ↦ dg (.inl k) (.inl i) (.inl j))
          (fun m k i j ↦ ddg (.inl m) (.inl k) (.inl i) (.inl j)) i j k l +
        -(2⁻¹ * dg (.inr ()) (.inl j) (.inl k)) *
          (2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) l i) -
        -(2⁻¹ * dg (.inr ()) (.inl i) (.inl k)) *
          (2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) l j) := by
  simp only [riemannOfJet_def, Fintype.sum_sum_type, christoffelDeriv_inl_inl_inl_inl hA hd₁ hd₂,
    christoffel_inl_inl_inl hA hd₁, christoffel_inl_inl_inr hA hd₁,
    christoffel_inl_inr_inl hA hd₁ hd₂ hds, Finset.univ_unique, Finset.sum_singleton]
  ring

include hA hd₁ hd₂ hd₃ hds hdd₁ hdd₂ hdd₃ in
private theorem riemann_inr_inl_inl_inr (j k : ι) :
    riemannOfJet (fromBlocks A 0 0 1) dg ddg (.inr ()) (.inl j) (.inl k) (.inr ()) =
      -(2⁻¹ * ddg (.inr ()) (.inr ()) (.inl j) (.inl k)) -
        ∑ m, 2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) m k *
          -(2⁻¹ * dg (.inr ()) (.inl j) (.inl m)) := by
  simp only [riemannOfJet_def, Fintype.sum_sum_type,
    christoffelDeriv_inr_inl_inl_inr hA hd₁ hd₃ hdd₁,
    christoffelDeriv_inl_inr_inl_inr hA hd₁ hd₃ hdd₁ hdd₂ hdd₃, christoffel_inl_inl_inr hA hd₁,
    christoffel_inr_inl_inl hA hd₁ hd₂ hds, christoffel_inr_inl_inr hA hd₁ hd₂ hd₃,
    christoffel_inr_inr hA hd₂ hd₃, Finset.univ_unique, Finset.sum_singleton,
    Finset.sum_sub_distrib]
  simp

include hA hd₁ hd₂ hd₃ hds hdd₁ hdd₂ hdd₃ in
private theorem riemann_inl_inr_inr_inl (i l : ι) :
    riemannOfJet (fromBlocks A 0 0 1) dg ddg (.inl i) (.inr ()) (.inr ()) (.inl l) =
      -(∑ l', A⁻¹ l l' * (2⁻¹ * ddg (.inr ()) (.inr ()) (.inl i) (.inl l') -
        ∑ q, dg (.inr ()) (.inl q) (.inl l') *
          (2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) q i))) -
        ∑ m, 2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) m i *
          (2⁻¹ * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) l m) := by
  simp only [riemannOfJet_def, Fintype.sum_sum_type,
    christoffelDeriv_inl_inr_inr_inl hA hd₂ hd₃ hdd₂ hdd₃,
    christoffelDeriv_inr_inl_inr_inl hA hd₁ hd₂ hdd₁ hdd₂ hds,
    christoffel_inl_inr_inl hA hd₁ hd₂ hds,
    christoffel_inr_inl_inl hA hd₁ hd₂ hds, christoffel_inl_inr_inr hA hd₁ hd₂ hd₃,
    christoffel_inr_inr hA hd₂ hd₃, Finset.univ_unique, Finset.sum_singleton,
    Finset.sum_sub_distrib]
  simp only [zero_mul, zero_sub, Finset.sum_const_zero, mul_zero, add_zero]
  ring

/-! ### The contraction of the curvature coefficients

In terms of `B = A⁻¹`, `P = A'`, `Q = A''` and `S = B P`, the terms of the contraction which involve
the time derivatives are sums of entries of `S²`, `S` and `B Q`. -/

section Contraction

omit [DecidableEq ι]

variable {B P Q : Matrix ι ι ℝ}

private theorem sum_mul_apply_eq_mul_apply_of_isSymm_right (hP : P.IsSymm) (j i : ι) :
    ∑ k, B j k * P i k = (B * P) j i := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hP.apply i k]

private theorem sum_mul_apply_eq_mul_apply_of_isSymm_left (hB : B.IsSymm) (k m : ι) :
    ∑ j, B j k * P j m = (B * P) k m := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hB.apply k j]

private theorem trace_mul_self_eq_sum (S : Matrix ι ι ℝ) :
    (S * S).trace = ∑ i, ∑ j, S i j * S j i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem sum_sum_mul_apply_eq_trace (hQ : Q.IsSymm) :
    ∑ j, ∑ k, B j k * Q j k = (B * Q).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [hQ.apply j k]

/-- The terms of the spatial curvature coefficients coming from the time Christoffel symbols. -/
private theorem sum_cylinder_spatial (hP : P.IsSymm) :
    ∑ x, ∑ a, ∑ y, B x a * (-(2⁻¹ * P x a) * (2⁻¹ * (B * P) y y)) -
      ∑ x, ∑ a, ∑ y, B x a * (-(2⁻¹ * P y a) * (2⁻¹ * (B * P) y x)) =
    -(1 / 4) * (B * P).trace ^ 2 + 1 / 4 * ((B * P) * (B * P)).trace := by
  have F₁ := sum_mul_apply_eq_mul_apply_of_isSymm_right (B := B) hP
  have hS₂ := trace_mul_self_eq_sum (B * P)
  set S := B * P
  have hS₁ : S.trace = ∑ i, S i i := rfl
  have X₁ : ∑ x, ∑ a, ∑ y, B x a * (-(2⁻¹ * P x a) * (2⁻¹ * S y y)) =
      -(1 / 4) * S.trace ^ 2 := by
    calc _ = ∑ x, (-(1 / 4) * S.trace) * ∑ a, B x a * P x a := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hS₁, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun y _ ↦ by ring
      _ = _ := by simp only [F₁, ← Finset.mul_sum, ← hS₁]; ring
  have X₂ : ∑ x, ∑ a, ∑ y, B x a * (-(2⁻¹ * P y a) * (2⁻¹ * S y x)) =
      -(1 / 4) * (S * S).trace := by
    calc _ = ∑ x, ∑ y, -(1 / 4) * S y x * ∑ a, B x a * P y a := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ ↦ by ring
      _ = _ := by
          simp only [F₁, hS₂, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
  rw [X₁, X₂]
  ring

/-- The terms of the mixed curvature coefficients `R(∂ₜ, ∂ⱼ, ∂ₖ, ∂ₜ)`. -/
private theorem sum_cylinder_mixed (hB : B.IsSymm) (hQ : Q.IsSymm) :
    ∑ x, ∑ a, B x a * -(2⁻¹ * Q x a) -
      ∑ x, ∑ a, ∑ m, B x a * (2⁻¹ * (B * P) m a * -(2⁻¹ * P x m)) =
    -(1 / 2) * (B * Q).trace + 1 / 4 * ((B * P) * (B * P)).trace := by
  have F₂ := sum_mul_apply_eq_mul_apply_of_isSymm_left (P := P) hB
  have hBQ := sum_sum_mul_apply_eq_trace (B := B) hQ
  have hS₂ := trace_mul_self_eq_sum (B * P)
  set S := B * P
  have X₃ : ∑ x, ∑ a, B x a * -(2⁻¹ * Q x a) = -(1 / 2) * (B * Q).trace := by
    rw [← hBQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have X₄ : ∑ x, ∑ a, ∑ m, B x a * (2⁻¹ * S m a * -(2⁻¹ * P x m)) =
      -(1 / 4) * (S * S).trace := by
    calc _ = ∑ a, ∑ m, -(1 / 4) * S m a * ∑ x, B x a * P x m := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ by ring
      _ = _ := by
          simp only [F₂, hS₂, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
  rw [X₃, X₄]
  ring

/-- The terms of the curvature coefficients `R(∂ᵢ, ∂ₜ, ∂ₜ, ∂ᵢ)`. -/
private theorem sum_cylinder_time (hP : P.IsSymm) (hQ : Q.IsSymm) :
    -∑ x, ∑ l, B x l * (2⁻¹ * Q x l) + ∑ x, ∑ l, ∑ q, B x l * (P q l * (2⁻¹ * (B * P) q x)) -
      ∑ x, ∑ m, 2⁻¹ * (B * P) m x * (2⁻¹ * (B * P) x m) =
    -(1 / 2) * (B * Q).trace + 1 / 4 * ((B * P) * (B * P)).trace := by
  have F₁ := sum_mul_apply_eq_mul_apply_of_isSymm_right (B := B) hP
  have hBQ := sum_sum_mul_apply_eq_trace (B := B) hQ
  have hS₂ := trace_mul_self_eq_sum (B * P)
  set S := B * P
  have W₁ : ∑ x, ∑ l, B x l * (2⁻¹ * Q x l) = 1 / 2 * (B * Q).trace := by
    rw [← hBQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have W₂ : ∑ x, ∑ l, ∑ q, B x l * (P q l * (2⁻¹ * S q x)) = 1 / 2 * (S * S).trace := by
    calc _ = ∑ x, ∑ q, 1 / 2 * S q x * ∑ l, B x l * P q l := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ ↦ by ring
      _ = _ := by
          simp only [F₁, hS₂, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
  have W₃ : ∑ x, ∑ m, 2⁻¹ * S m x * (2⁻¹ * S x m) = 1 / 4 * (S * S).trace := by
    rw [hS₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  rw [W₁, W₂, W₃]
  ring

/-- The contraction of the curvature coefficients of a cylinder jet, after its Christoffel symbols
have been computed, in terms of `B = A⁻¹`, `P = A'` and `Q = A''`. -/
private theorem sum_cylinder_eq (R : ι → ι → ι → ι → ℝ) (hB : B.IsSymm) (hP : P.IsSymm)
    (hQ : Q.IsSymm) :
    ∑ x, ∑ a, B x a * (∑ y, (R y x a y + -(2⁻¹ * P x a) * (2⁻¹ * (B * P) y y) -
        -(2⁻¹ * P y a) * (2⁻¹ * (B * P) y x)) +
        (-(2⁻¹ * Q x a) - ∑ m, 2⁻¹ * (B * P) m a * -(2⁻¹ * P x m))) +
      (0 + ∑ x, (-∑ l, B x l * (2⁻¹ * Q x l - ∑ q, P q l * (2⁻¹ * (B * P) q x)) -
        ∑ m, 2⁻¹ * (B * P) m x * (2⁻¹ * (B * P) x m))) =
    ∑ j, ∑ k, B j k * ∑ i, R i j k i - (B * Q).trace + 3 / 4 * ((B * P) * (B * P)).trace -
      1 / 4 * (B * P).trace ^ 2 := by
  have h₁ := sum_cylinder_spatial (B := B) hP
  have h₂ := sum_cylinder_mixed (P := P) hB hQ
  have h₃ := sum_cylinder_time (B := B) hP hQ
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, zero_add] at h₁ h₂ h₃ ⊢
  linear_combination h₁ + h₂ + h₃

end Contraction

include hA hd₁ hd₂ hd₃ hdd₁ hdd₂ hdd₃ hds in
/-- **The scalar curvature of a cylinder jet.** Let the Gram matrix of a jet in the index set
`ι ⊕ Unit` be `fromBlocks A 0 0 1` with `A` invertible and symmetric, and let its first and
second derivatives vanish on every coefficient involving the time index `Sum.inr ()`, as for the
metric `g_t + dt²` in a product chart. Write `A'` and `A''` for the first and second time
derivatives of the spatial coefficients, assumed symmetric. Then the scalar curvature of the jet is
`Scal(A) - tr (A⁻¹ A'') + (3 / 4) tr ((A⁻¹ A')²) - (1 / 4) (tr (A⁻¹ A'))²`, where `Scal(A)` is the
scalar curvature of the spatial jet. -/
theorem scalarCurvatureOfJet_fromBlocks_one (hAs : A.IsSymm)
    (hdds : ∀ i j, ddg (.inr ()) (.inr ()) (.inl i) (.inl j) =
      ddg (.inr ()) (.inr ()) (.inl j) (.inl i)) :
    scalarCurvatureOfJet (fromBlocks A 0 0 1) dg ddg =
      scalarCurvatureOfJet A (fun k i j ↦ dg (.inl k) (.inl i) (.inl j))
          (fun m k i j ↦ ddg (.inl m) (.inl k) (.inl i) (.inl j)) -
        (A⁻¹ * of fun i j ↦ ddg (.inr ()) (.inr ()) (.inl i) (.inl j)).trace +
        3 / 4 * ((A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)) *
          (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j))).trace -
        1 / 4 * (A⁻¹ * of fun i j ↦ dg (.inr ()) (.inl i) (.inl j)).trace ^ 2 := by
  simp only [scalarCurvatureOfJet_def, inv_fromBlocks_one hA, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    riemann_inl_inl_inl_inl hA hd₁ hd₂ hds,
    riemann_inr_inl_inl_inr hA hd₁ hd₂ hd₃ hdd₁ hdd₂ hdd₃ hds,
    riemann_inl_inr_inr_inl hA hd₁ hd₂ hd₃ hdd₁ hdd₂ hdd₃ hds, riemannOfJet_self, Matrix.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero, one_apply_eq, one_mul, Finset.univ_unique,
    Finset.sum_singleton]
  exact sum_cylinder_eq _ hAs.inv (IsSymm.ext fun i j ↦ hds j i)
    (IsSymm.ext fun i j ↦ hdds j i)

end TauCeti.Manifold
