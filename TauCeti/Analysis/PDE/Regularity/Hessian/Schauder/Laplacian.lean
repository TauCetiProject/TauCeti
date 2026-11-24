/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.WholeSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# The scale-invariant Schauder estimate for the Laplacian on the whole space

Let `0 < α < 1`. For the Laplacian on `ℝ^{n+1}`, the global Schauder estimate
`[D²u]_α ≤ C ([Δu]_α + ‖u‖_∞)`
(`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv` with the
identity coefficient matrix) improves to the scale-invariant estimate

`[D²u]_α ≤ C [Δu]_α`

for every bounded `C²` function `u` with globally `α`-Hölder Hessian, with `C` depending only on
`n` and `α` (`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_holderWith_laplacian`). The
dilation `u_t(z) = u(t z)` multiplies `[D²u]_α` and `[Δu]_α` by the same factor `t^(2+α)` and
leaves `‖u‖_∞` unchanged, so the global estimate for `u_t` reads
`[D²u]_α ≤ C ([Δu]_α + t^(-2-α) ‖u‖_∞)`, and letting `t → ∞` removes the supremum. The
boundedness of `u` is used only so that the global estimate applies to the dilations; it does not
enter the final constant.

## Main declarations

* `TauCeti.PDE.sum_one_smul_fderiv_fderiv_eq_laplacian`: the non-divergence-form operator with
  the identity coefficient matrix is the Laplacian.
* `TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_holderWith_laplacian`: the
  scale-invariant estimate.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 4.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Graduate Studies
  in Mathematics 12, AMS, 1996, Chapter 3.
-/

public section

noncomputable section

open Filter InnerProductSpace Laplacian Metric Set Topology
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The non-divergence-form operator `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` with the identity coefficient matrix is the
Laplacian. -/
theorem sum_one_smul_fderiv_fderiv_eq_laplacian (u : E → ℝ) :
    (fun x ↦ ∑ i, ∑ j, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = Δ u := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  funext x
  simp [Matrix.one_apply, iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]

/-- The global Schauder estimate for the Laplacian, applied to the dilation `z ↦ u (t • z)` and
rescaled back: the Hölder quotients of `D²u` are at most `C ([Δu]_α + ‖u‖_∞ t^(-2-α))` for every
`t > 0`. -/
private theorem exists_dist_iteratedFDeriv_two_le_of_laplacian {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ} {N H Cu : ℝ≥0}, ContDiff ℝ 2 u → (∀ x, |u x| ≤ N) →
      HolderWith Cu α (iteratedFDeriv ℝ 2 u) → HolderWith H α (Δ u) → ∀ t : ℝ, 0 < t →
      ∀ x y, dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
        C * (H + N * (t ^ 2 * t ^ (α : ℝ))⁻¹) * dist x y ^ (α : ℝ) := by
  obtain ⟨C, hC⟩ :=
    exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv (n := n) hα hα1 1 1 0
  refine ⟨C, fun {u N H Cu} hu hN hCu hH t ht x y ↦ ?_⟩
  set v : E → ℝ := fun z ↦ u (t • z) with hv
  have hD2v : ∀ z, iteratedFDeriv ℝ 2 v z = t ^ 2 • iteratedFDeriv ℝ 2 u (t • z) :=
    fun z ↦ iteratedFDeriv_comp_const_smul_apply u t z 2
  -- A Hölder bound `K` for `g` gives the bound `s ^ 2 K s ^ α` for `z ↦ s ^ 2 • g (s • z)`.
  have hdil : ∀ {s : ℝ}, 0 < s → ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {g : E → F} {K : ℝ≥0}, HolderWith K α g → HolderWith (s ^ 2 * K * s ^ (α : ℝ)).toNNReal α
        (fun z ↦ s ^ 2 • g (s • z)) := fun {s} hs {F _ _ g K} hg ↦ by
    convert (holderOnWith_univ.1 ((hg.holderOnWith univ).comp_const_smul s
      (mapsTo_univ _ _))).smul (s ^ 2) using 1
    rw [← NNReal.coe_inj]
    push_cast [Real.coe_toNNReal _ (by positivity : 0 ≤ s ^ 2 * K * s ^ (α : ℝ)),
      norm_pow, Real.norm_of_nonneg hs.le]
    ring
  have hvH : MemHolder α (iteratedFDeriv ℝ 2 v) := ⟨_, by rw [funext hD2v]; exact hdil ht hCu⟩
  have hLv : HolderWith (t ^ 2 * H * t ^ (α : ℝ)).toNNReal α (fun z ↦ ∑ i, ∑ j,
      (fun _ ↦ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) z i j •
        fderiv ℝ (fderiv ℝ v) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    simp only [sum_one_smul_fderiv_fderiv_eq_laplacian]
    rw [hv, laplacian_comp_smul_right]
    exact hdil ht hH
  -- Dilating the estimate for `v` back by `t⁻¹` gives one for `u`.
  have hres := hdil (inv_pos.2 ht) (hC (uniformlyEllipticOn_const_one_one univ)
    (fun _ _ ↦ HolderWith.const) (show ContDiff ℝ 2 v from hu.comp (contDiff_const_smul t))
    (fun z ↦ hN (t • z)) hvH hLv).1
  have hu2 : (fun z ↦ t⁻¹ ^ 2 • iteratedFDeriv ℝ 2 v (t⁻¹ • z)) = iteratedFDeriv ℝ 2 u := by
    funext z
    rw [hD2v, smul_inv_smul₀ ht.ne', inv_pow, inv_smul_smul₀ (pow_ne_zero 2 ht.ne')]
  rw [hu2] at hres
  refine (hres.dist_le x y).trans_eq ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  push_cast [Real.coe_toNNReal _ (by positivity : 0 ≤ t ^ 2 * H * t ^ (α : ℝ)),
    Real.inv_rpow ht.le]
  field_simp

/-- **The scale-invariant Schauder estimate for the Laplacian.** For `0 < α < 1` there is a
constant `C`, depending only on `n` and `α`, such that every bounded `C²` function `u` on
`ℝ^{n+1}` with globally `α`-Hölder Hessian whose Laplacian is `α`-Hölder with constant `H`
satisfies `[D²u]_α ≤ C H`. The bound on `u` and the Hölder continuity of `D²u` enter only
qualitatively. -/
theorem exists_holderWith_iteratedFDeriv_two_of_holderWith_laplacian {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ} {N H : ℝ≥0}, ContDiff ℝ 2 u → (∀ x, |u x| ≤ N) →
      MemHolder α (iteratedFDeriv ℝ 2 u) → HolderWith H α (Δ u) →
      HolderWith (C * H) α (iteratedFDeriv ℝ 2 u) := by
  obtain ⟨C, hC⟩ := exists_dist_iteratedFDeriv_two_le_of_laplacian (n := n) hα hα1
  refine ⟨C, fun {u N H} hu hN ⟨Cu, hCu⟩ hH ↦
    holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)⟩
  -- Let the dilation factor tend to infinity.
  have h0 : Tendsto (fun t : ℝ ↦ (t ^ 2 * t ^ (α : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).atTop_mul_atTop₀
      (tendsto_rpow_atTop (NNReal.coe_pos.2 hα)))
  have hlim : Tendsto (fun t : ℝ ↦ C * (H + N * (t ^ 2 * t ^ (α : ℝ))⁻¹) * dist x y ^ (α : ℝ))
      atTop (𝓝 ((C * H : ℝ≥0) * dist x y ^ (α : ℝ))) := by
    simpa [NNReal.coe_mul, mul_assoc] using
      (((h0.const_mul (N : ℝ)).const_add (H : ℝ)).const_mul (C : ℝ)).mul_const
        (dist x y ^ (α : ℝ))
  exact ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht ↦ hC hu hN hCu hH t ht x y)

end TauCeti.PDE
