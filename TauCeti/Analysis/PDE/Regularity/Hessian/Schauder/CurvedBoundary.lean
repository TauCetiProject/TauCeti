/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.HalfBall
import TauCeti.Analysis.Calculus.FDeriv.ConstantDirection
import TauCeti.Analysis.Calculus.GraphFlattening.Direction
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.Transvection
import TauCeti.Analysis.Matrix.Holder
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.Topology.MetricSpace.Holder

/-!
# Schauder estimates near a curved boundary

Let `ν` be a unit vector of `ℝ^{n+1}` and let `γ : ℝ^{n+1} → ℝ` be `C²`, invariant under translation
along `ν`, with `Dγ` and `D²γ` bounded by `G` and `D²γ` `α`-Hölder with constant `G`, `0 < α < 1`.
Then `D = {x | γ x < ⟪x, ν⟫}` is the region above the graph of a `C^{2,α}` function over the
hyperplane `ν^⊥`, and its boundary `∂D = {x | ⟪x, ν⟫ = γ x}` is that graph. This file proves the
`C^{2,α}` estimate up to `∂D` for the non-divergence-form operator `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` with
Hölder coefficients (in the `TauCeti.PDE` namespace,
`exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph`):
for `R` small and `2 (1 + G)² ρ < R`, every `u` which is `C²` near `ball x₀ R ∩ closure D`, vanishes
on `∂D` and has `|u|`, `‖Du‖`, `‖D²u‖` bounded by `N` there satisfies

`[D²u]_{α; closedBall x₀ ρ ∩ closure D} ≤ C ([L u]_{α; ball x₀ R ∩ D} + N)`,

with `C` depending on the dimension, `α`, `G`, the ellipticity constants of `a` at `x₀`, the
Hölder constant and bound of `a`, `R` and `ρ`, but not on `u`, `x₀` or `a` otherwise. This is the
curved counterpart of the estimate on half-balls at a flat boundary
(`exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace`),
and, together with the interior estimate, the local estimate from which the global Schauder
estimate on a domain with `C^{2,α}` boundary is assembled by covering the boundary with such
graph patches.

## The argument

* **Flattening.** The shear `φ = TauCeti.shearAlong γ ν`, `φ y = y + γ y ν`, maps the half-space
  `{0 < ⟪y, ν⟫}` onto `D` and the hyperplane `{⟪y, ν⟫ = 0}` onto `∂D`, since
  `⟪φ y, ν⟫ - γ (φ y) = ⟪y, ν⟫`; its inverse is the shear `ψ = TauCeti.shearAlong (-γ) ν`,
  `ψ x = x - γ x ν`. Both are `(1 + G)`-Lipschitz.
* **The transformed equation.** For `v = u ∘ φ` the second-order chain rule reads
  `D²v(y)(h, k) = D²u(φ y)(S h, S k) + D²γ(y)(h, k) Du(φ y) ν` with `S = Dφ(y)`. Let `W` be the
  matrix whose rows `eᵢ - ∂ᵢγ ν` are the images of the basis vectors under `Dψ`, so that `S` maps
  them back to `eᵢ`. The coefficients `ã = Wᵀ (a ∘ φ) W` then satisfy
  `∑ₖₗ ãₖₗ ∂ₖ∂ₗv = (L u) ∘ φ + c Du(φ ·) ν` with `c = ∑ₖₗ ãₖₗ ∂ₖ∂ₗγ`. The quadratic form of `ã` at
  `ξ` is that of `a ∘ φ` at `W ξ = ξ - ⟪ν, ξ⟫ ∇γ`, and since `∂_ν γ = 0` the two vectors have norms
  within a factor `1 + G` of each other, so `ã` has ellipticity bounds `λ / (1 + G)²` and
  `Λ (1 + G)²`.
* **Hölder bounds.** The entries of `ã` and `c` are Hölder and bounded with constants depending
  only on `n`, `α`, `G`, `L` and `M`, and `Du ∘ φ` is Lipschitz on the convex half-ball, so the
  first-order term is Hölder. The second derivative of a composition with a shear is Hölder by
  `TauCeti.holderOnWith_fderiv_fderiv_comp_shearAlong`.
* **The flat estimate.** Since the Hölder constant of `ã` does not depend on the radius, the
  smallness condition of the half-ball estimate holds for `v` on the half-ball of radius
  `R / (2 (1 + G))` about `ψ x₀` once `R` is small.
* **Back to `u`.** Since `u = v ∘ ψ` and `ψ` is the shear by `-γ`, the same chain rule bounds the
  Hölder constant of `D²u` on `closedBall x₀ ρ ∩ closure D`, which `ψ` maps into the smaller
  half-ball.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2: the boundary estimate after flattening the boundary (Lemma 6.5) and its use in the
  global estimate (Theorem 6.6).
-/

public section

open Metric Set Filter Topology
open scoped NNReal Matrix InnerProductSpace

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### The shear flattening a graph -/

section Graph

variable {γ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν : EuclideanSpace ℝ (Fin (n + 1))}

/-- The matrix whose `i`-th row is the vector `eᵢ - Dγ(y) eᵢ ν`, the image of `eᵢ` under the
derivative of the inverse shear `x ↦ x - γ x ν`. -/
private noncomputable def shearRows (γ : E → ℝ) (ν y : E) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i k =>
    (EuclideanSpace.single i (1 : ℝ) - fderiv ℝ γ y (EuclideanSpace.single i 1) • ν : E) k

private theorem shearRows_apply (y : E) (i k : Fin (n + 1)) :
    shearRows γ ν y i k =
      (if k = i then 1 else 0) - fderiv ℝ γ y (EuclideanSpace.single i 1) * ν k := by
  simp [shearRows, PiLp.single_apply]

/-- The rows of `shearRows γ ν y`, as vectors. -/
private theorem sum_shearRows_smul_single (y : E) (i : Fin (n + 1)) :
    ∑ k, shearRows γ ν y i k • EuclideanSpace.single k (1 : ℝ) =
      EuclideanSpace.single i (1 : ℝ) - fderiv ℝ γ y (EuclideanSpace.single i 1) • ν := by
  simpa [shearRows, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr
      (EuclideanSpace.single i (1 : ℝ) - fderiv ℝ γ y (EuclideanSpace.single i 1) • ν)

/-- **The non-divergence operator under the shear.** If `γ` is invariant along `ν` and
`v = u ∘ φ` for the shear `φ y = y + γ y ν`, then the operator with the coefficients
`Wᵀ A W`, `W = shearRows γ ν y`, applied to `v` at `y` is the operator with the coefficients `A`
applied to `u` at `φ y`, plus the first-order term `c(y) Du(φ y) ν` with
`c = ∑ₖₗ (Wᵀ A W)ₖₗ ∂ₖ∂ₗγ`. -/
private theorem sum_sum_smul_fderiv_fderiv_comp_shearAlong (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    {u : E → ℝ} {y : E} (hu : ContDiffAt ℝ 2 u (shearAlong γ ν y)) (hγ : ContDiffAt ℝ 2 γ y)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∑ k, ∑ l, ((shearRows γ ν y)ᵀ * A * shearRows γ ν y) k l •
        fderiv ℝ (fderiv ℝ (u ∘ shearAlong γ ν)) y (EuclideanSpace.single k 1)
          (EuclideanSpace.single l 1) =
      ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) (shearAlong γ ν y) (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) +
        (∑ k, ∑ l, ((shearRows γ ν y)ᵀ * A * shearRows γ ν y) k l *
          fderiv ℝ (fderiv ℝ γ) y (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)) *
          fderiv ℝ u (shearAlong γ ν y) ν := by
  set S : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν
  have hS (h : E) : h + fderiv ℝ γ y h • ν = S h := by simp [S]
  have hrow (i : Fin (n + 1)) : S (∑ k, shearRows γ ν y i k • EuclideanSpace.single k (1 : ℝ)) =
      EuclideanSpace.single i 1 := by
    rw [sum_shearRows_smul_single]
    simp [S, fderiv_apply_eq_zero_of_apply_add_smul_neg (f := γ) (x := y) ν fun t => by
      rw [hγν, hγν]]
  simp only [fderiv_fderiv_comp_shearAlong_apply hu hγ, hS, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  congr 1
  have h := Matrix.sum_sum_transpose_mul_mul_apply_mul A (shearRows γ ν y)
    ((fderiv ℝ (fderiv ℝ u) (shearAlong γ ν y)).bilinearComp S S).toLinearMap₁₂
    fun k => EuclideanSpace.single k 1
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    ContinuousLinearMap.bilinearComp_apply, hrow, Matrix.mul_assoc] at h
  exact h

/-- The vector `W ξ`, for the matrix `W = shearRows γ ν y` with rows `eᵢ - Dγ(y) eᵢ ν`, is
`ξ - ⟪ν, ξ⟫ ∇γ(y)`. -/
private theorem shearRows_mulVec (y ξ : E) :
    shearRows γ ν y *ᵥ ⇑ξ =
      ⇑(ξ - ⟪ν, ξ⟫_ℝ • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y)) := by
  ext i
  have hg : ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y) : E) i =
      fderiv ℝ γ y (EuclideanSpace.single i 1) := by
    rw [← InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single i 1),
      EuclideanSpace.inner_single_right]
    simp
  simp only [Matrix.mulVec, dotProduct, shearRows_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, hg, EuclideanSpace.inner_eq_star_dotProduct, mul_assoc,
    ← Finset.mul_sum]
  simp [mul_comm]

/-- The vectors `ξ` and `η = ξ - ⟪ν, ξ⟫ ∇γ(y)` have comparable norms when `‖ν‖ = 1`,
`Dγ(y) ν = 0` and `‖Dγ(y)‖ ≤ G`. -/
private theorem norm_le_mul_norm_sub_inner_smul (hν : ‖ν‖ = 1) {y : E} {G : ℝ≥0}
    (hγν : fderiv ℝ γ y ν = 0) (hG : ‖fderiv ℝ γ y‖ ≤ G) (ξ : E) :
    ‖ξ - ⟪ν, ξ⟫_ℝ • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y)‖ ≤ (1 + G) * ‖ξ‖ ∧
      ‖ξ‖ ≤ (1 + G) * ‖ξ - ⟪ν, ξ⟫_ℝ • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y)‖ := by
  set g : E := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y)
  have hg : ‖g‖ ≤ G := by rw [LinearIsometryEquiv.norm_map]; exact hG
  have hνg : ⟪ν, g⟫_ℝ = 0 := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, hγν]
  -- `ξ ↦ ξ - ⟪ν, ξ⟫ g` is the transvection along `-g`, inverted by the one along `g`.
  have hT (s : E) (hs : ‖s‖ ≤ G) : ‖transvectionL ν s‖ ≤ 1 + G :=
    (norm_transvectionL_le ν s).trans (by rw [hν, one_mul]; gcongr)
  have hξ : ξ - ⟪ν, ξ⟫_ℝ • g = transvectionL ν (-g) ξ := by
    rw [transvectionL_apply, smul_neg, sub_eq_add_neg]
  rw [hξ]
  refine ⟨((transvectionL ν (-g)).le_opNorm ξ).trans (by gcongr; exact hT _ (by rwa [norm_neg])),
    ?_⟩
  conv_lhs => rw [← transvectionL_transvectionL_neg hνg ξ]
  exact ((transvectionL ν g).le_opNorm _).trans (by gcongr; exact hT g hg)

/-- **Ellipticity of the sheared coefficients.** If `A` has ellipticity bounds `λ, Λ`, then
`Wᵀ A W`, `W = shearRows γ ν y`, has ellipticity bounds `λ / (1 + G)²` and `Λ (1 + G)²`. -/
private theorem toQuadraticForm'_transpose_shearRows_mul_mul (hν : ‖ν‖ = 1) {y : E} {G : ℝ≥0}
    (hγν : fderiv ℝ γ y ν = 0) (hG : ‖fderiv ℝ γ y‖ ≤ G)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : E, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) (ξ : E) :
    lam / (1 + G) ^ 2 * ‖ξ‖ ^ 2 ≤ ((shearRows γ ν y)ᵀ * A * shearRows γ ν y).toQuadraticForm' ξ ∧
      ((shearRows γ ν y)ᵀ * A * shearRows γ ν y).toQuadraticForm' ξ ≤
        Lam * (1 + G) ^ 2 * ‖ξ‖ ^ 2 := by
  have hq : ((shearRows γ ν y)ᵀ * A * shearRows γ ν y).toQuadraticForm' ξ =
      A.toQuadraticForm' ⇑(ξ - ⟪ν, ξ⟫_ℝ • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y)) := by
    rw [Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, shearRows_mulVec]
  -- Comparing the bounds at a unit vector gives `λ ≤ Λ`, so `0 ≤ Λ`.
  have hLam : 0 ≤ Lam := by
    have h := (hA (EuclideanSpace.single 0 1)).trans (hA' (EuclideanSpace.single 0 1))
    have hn : ‖(EuclideanSpace.single 0 (1 : ℝ) : E)‖ = 1 := by simp
    rw [hn, one_pow, mul_one, mul_one] at h
    linarith
  obtain ⟨h1, h2⟩ := norm_le_mul_norm_sub_inner_smul hν hγν hG ξ
  set η : E := ξ - ⟪ν, ξ⟫_ℝ • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ γ y)
  rw [hq]
  constructor
  · refine le_trans ?_ (hA η)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : ‖ξ‖ ^ 2 ≤ ((1 + G) * ‖η‖) ^ 2 := by gcongr
    nlinarith
  · refine (hA' η).trans ?_
    have : ‖η‖ ^ 2 ≤ ((1 + G) * ‖ξ‖) ^ 2 := by gcongr
    nlinarith

end Graph

/-! ### Hölder bounds for the sheared coefficients -/

section Coefficients

/-- The entries of `shearRows γ ν` are Hölder with the Hölder constant of `Dγ` and bounded by
`1 + G`. -/
private theorem holderOnWith_shearRows_apply {γ : E → ℝ} {ν : E} (hν : ‖ν‖ ≤ 1) {s : Set E}
    {α G G₁ : ℝ≥0} (hG : ∀ y ∈ s, ‖fderiv ℝ γ y‖ ≤ G) (hH : HolderOnWith G₁ α (fderiv ℝ γ) s)
    (i k : Fin (n + 1)) :
    HolderOnWith G₁ α (fun y => shearRows γ ν y i k) s ∧
      ∀ y ∈ s, |shearRows γ ν y i k| ≤ ((1 + G : ℝ≥0) : ℝ) := by
  have he : ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ ≤ 1 := by simp
  have hνk : |ν k| ≤ 1 := (PiLp.norm_apply_le ν k).trans hν
  have hd (y : E) : |fderiv ℝ γ y (EuclideanSpace.single i 1)| ≤ ‖fderiv ℝ γ y‖ :=
    (fderiv ℝ γ y).unit_le_opNorm _ he
  refine ⟨HolderOnWith.of_dist_le fun y hy y' hy' => ?_, fun y hy => ?_⟩
  · have h := (hH.clm_apply_of_norm_le_one he).dist_le hy hy'
    rw [Real.dist_eq] at h ⊢
    simp only [shearRows_apply, sub_sub_sub_cancel_left, ← sub_mul, abs_mul]
    rw [abs_sub_comm]
    calc _ ≤ |fderiv ℝ γ y (EuclideanSpace.single i 1) -
          fderiv ℝ γ y' (EuclideanSpace.single i 1)| * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact h
  · rw [shearRows_apply]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have h0 : |(if k = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have := mul_le_mul ((hd y).trans (hG y hy)) hνk (abs_nonneg _) G.coe_nonneg
    push_cast
    linarith

end Coefficients

/-! ### The estimate near a graph -/

/-- A product of `N` with `(1 + G)²` or with `1 + G` is at most `N (1 + G)² + N G`. -/
private theorem le_mul_one_add_mul_one_add_add_mul (N G : ℝ≥0) :
    N ≤ N * (1 + G) * (1 + G) + N * G ∧ N * (1 + G) ≤ N * (1 + G) * (1 + G) + N * G := by
  have h1 : N * (1 + G) ≤ N * (1 + G) * (1 + G) :=
    calc N * (1 + G) = N * (1 + G) * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr; exact le_self_add
  have h0 : N ≤ N * (1 + G) :=
    calc N = N * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr; exact le_self_add
  exact ⟨h0.trans (h1.trans le_self_add), h1.trans le_self_add⟩

/-- The facts about `γ` used by the estimate: `γ` and `-γ` are `G`-Lipschitz, and `Dγ` and `D(-γ)`
are `α`-Hölder with constant `3 G`. -/
private theorem graph_facts {α : ℝ≥0} (hα1 : α ≤ 1) {γ : E → ℝ} {G : ℝ≥0}
    (hγ : ContDiff ℝ 2 γ) (hG1 : ∀ x, ‖fderiv ℝ γ x‖ ≤ G)
    (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) :
    LipschitzWith G γ ∧ LipschitzWith G (fun x => -γ x) ∧
      HolderWith (G + 2 * G) α (fderiv ℝ γ) ∧
      HolderWith (G + 2 * G) α (fderiv ℝ fun x => -γ x) := by
  have hd1 : Differentiable ℝ γ := hγ.differentiable two_ne_zero
  have hd2 : Differentiable ℝ (fderiv ℝ γ) :=
    (hγ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
  have hL : LipschitzWith G γ := lipschitzWith_of_nnNorm_fderiv_le hd1 fun x => by
    rw [← NNReal.coe_le_coe, coe_nnNorm]; exact hG1 x
  have hL1 : LipschitzWith G (fderiv ℝ γ) := lipschitzWith_of_nnNorm_fderiv_le hd2 fun x => by
    rw [← NNReal.coe_le_coe, coe_nnNorm]; exact hG2 x
  have hH : HolderWith (G + 2 * G) α (fderiv ℝ γ) := holderOnWith_univ.1
    ((hL1.lipschitzOnWith (s := univ)).holderOnWith_of_norm_le (fun x _ => hG1 x) hα1)
  have hneg : (fderiv ℝ fun x => -γ x) = -fderiv ℝ γ := funext fun x => fderiv_neg
  refine ⟨hL, ?_, hH, ?_⟩
  · exact hL.neg
  · rw [hneg]
    exact HolderWith.neg hH

/-- The shear `φ y = y + γ y ν` maps the part of the ball `closedBall y₀ r` above the hyperplane
`⟪·, ν⟫ = 0` into the part of `ball x₀ R` above the graph of `γ`, where `x₀ = φ y₀` and
`(1 + G) r < R`, and the part strictly above the hyperplane strictly above the graph. -/
private theorem shearAlong_mem_ball_inter {ν : E} (hν : ‖ν‖ = 1) {γ : E → ℝ}
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {G : ℝ≥0} (hγ : LipschitzWith G γ) {x₀ y₀ : E}
    (hy₀ : shearAlong γ ν y₀ = x₀) {r R : ℝ} (hr : (1 + G) * r < R) {y : E}
    (hy : dist y y₀ ≤ r) :
    (0 ≤ ⟪y, ν⟫_ℝ → shearAlong γ ν y ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}) ∧
      (0 < ⟪y, ν⟫_ℝ → shearAlong γ ν y ∈ ball x₀ R ∩ {x | γ x < ⟪x, ν⟫_ℝ}) := by
  have hd : shearAlong γ ν y ∈ ball x₀ R := by
    rw [mem_ball, ← hy₀]
    exact (dist_shearAlong_le hν.le hγ hy).trans_lt hr
  have hi := real_inner_shearAlong_sub hν hγν y
  exact ⟨fun h => ⟨hd, by simp only [mem_ofPred_eq]; linarith⟩,
    fun h => ⟨hd, by simp only [mem_ofPred_eq]; linarith⟩⟩

/-- **The sheared coefficients are Hölder.** With `x₀ = φ y₀` for the shear `φ y = y + γ y ν` and
`(1 + G) r < R`, if the coefficients `a` are Hölder with constant `L` and bounded by `M` above the
graph of `γ` near `x₀`, then the entries of `Wᵀ (a ∘ φ) W`, `W = shearRows γ ν`, are Hölder and
bounded on the part of `closedBall y₀ r` above the hyperplane, with constants depending only on
`n`, `α`, `G`, `L` and `M`. -/
private theorem holderOnWith_transpose_shearRows_mul_mul_apply {α : ℝ≥0} (hα1 : α ≤ 1) {ν : E}
    (hν : ‖ν‖ = 1) {γ : E → ℝ} {G : ℝ≥0} (hγ : ContDiff ℝ 2 γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hG1 : ∀ x, ‖fderiv ℝ γ x‖ ≤ G)
    (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) {L M : ℝ≥0}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ y₀ : E} (hy₀ : shearAlong γ ν y₀ = x₀)
    {r R : ℝ} (hr : (1 + G) * r < R)
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}))
    (hM : ∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M) (k l : Fin (n + 1)) :
    HolderOnWith ((n + 1) * ((n + 1) * ((1 + G) * M) * (G + 2 * G) +
        (1 + G) * ((n + 1) * ((1 + G) * (L * (1 + G) ^ (α : ℝ)) + M * (G + 2 * G))))) α
        (fun y => ((shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y) k l)
        (closedBall y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) ∧
      ∀ y ∈ closedBall y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ},
        |((shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y) k l| ≤
          (((n + 1) * ((n + 1) * ((1 + G) * M) * (1 + G)) : ℝ≥0) : ℝ) := by
  obtain ⟨hLγ, -, hH, -⟩ := graph_facts hα1 hγ hG1 hG2
  have hmaps (y : E) (hy : y ∈ closedBall y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) :
      shearAlong γ ν y ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ} :=
    (shearAlong_mem_ball_inter hν hγν hLγ hy₀ hr (mem_closedBall.1 hy.1)).1 hy.2
  have hW (i j : Fin (n + 1)) :=
    holderOnWith_shearRows_apply (ν := ν) (s := closedBall y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) hν.le
      (fun y _ => hG1 y) (hH.holderOnWith _) i j
  have h := holderOnWith_transpose_mul_mul_apply (A := fun y => a (shearAlong γ ν y))
    (W := shearRows γ ν)
    (fun i j => holderOnWith_comp_shearAlong hν.le hLγ (hL i j) fun y hy =>
      ⟨ball_subset_closedBall (hmaps y hy).1, (hmaps y hy).2⟩)
    (fun i j => (hW i j).1) (fun y hy i j => hM _ (hmaps y hy) i j)
    (fun y hy i j => (hW i j).2 y hy) k l
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h
  exact h

/-- **Bounds for `u ∘ φ`.** With `x₀ = φ y₀` for the shear `φ y = y + γ y ν` and
`(1 + G) r < R`, if `u` is `C²` near the part of `ball x₀ R` above the graph of `γ`, with `‖Du‖`
and `‖D²u‖` bounded by `N` and `D²u` Hölder there, then on the part of `ball y₀ r` above the
hyperplane `⟪·, ν⟫ = 0` the derivatives of `u ∘ φ` are bounded, `Du ∘ φ` is Hölder, and
`D²(u ∘ φ)` is Hölder. -/
private theorem comp_shearAlong_bounds {α : ℝ≥0} (hα1 : α ≤ 1) {ν : E} (hν : ‖ν‖ = 1) {γ : E → ℝ}
    {G : ℝ≥0} (hγ : ContDiff ℝ 2 γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hG1 : ∀ x, ‖fderiv ℝ γ x‖ ≤ G) (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G)
    (hG3 : HolderWith G α (fderiv ℝ (fderiv ℝ γ))) {x₀ y₀ : E} (hy₀ : shearAlong γ ν y₀ = x₀)
    {r R : ℝ} (hr : (1 + G) * r < R) {U : Set E} {u : E → ℝ} {N V : ℝ≥0} (hU : IsOpen U)
    (hBU : ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hN1 : ∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N)
    (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ})) :
    (∀ y ∈ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ},
        ‖fderiv ℝ (u ∘ shearAlong γ ν) y‖ ≤ ((N * (1 + G) : ℝ≥0) : ℝ)) ∧
      (∀ y ∈ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ},
        ‖fderiv ℝ (fderiv ℝ (u ∘ shearAlong γ ν)) y‖ ≤
          ((N * (1 + G) * (1 + G) + N * G : ℝ≥0) : ℝ)) ∧
      HolderOnWith (N * (1 + G) * (2 * r).toNNReal ^ ((1 : ℝ) - α)) α
        (fun y => fderiv ℝ u (shearAlong γ ν y)) (ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) ∧
      ∃ V', HolderOnWith V' α (fderiv ℝ (fderiv ℝ (u ∘ shearAlong γ ν)))
        (ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) := by
  obtain ⟨hLγ, -, hH, -⟩ := graph_facts hα1 hγ hG1 hG2
  set s := ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}
  have hmaps (y : E) (hy : y ∈ s) : shearAlong γ ν y ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ} :=
    (shearAlong_mem_ball_inter hν hγν hLγ hy₀ hr (mem_ball.1 hy.1).le).1 hy.2
  have hcd (y : E) (hy : y ∈ s) : ContDiffAt ℝ 2 u (shearAlong γ ν y) :=
    hu.contDiffAt (hU.mem_nhds (hBU (hmaps y hy)))
  have hφ (y : E) := hasFDerivAt_shearAlong (ν := ν) (hγ.differentiable two_ne_zero y)
  have hS (y : E) := norm_id_add_smulRight_le hν.le (hG1 y)
  have hN2' (y : E) (hy : y ∈ s) : ‖fderiv ℝ (fderiv ℝ u) (shearAlong γ ν y)‖ ≤ N := by
    rw [norm_fderiv_fderiv]
    exact hN2 _ (hmaps y hy)
  have hcomp (A : E →L[ℝ] ℝ) (y : E) (hA : ‖A‖ ≤ N) :
      ‖A.comp (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν)‖ ≤
        ((N * (1 + G) : ℝ≥0) : ℝ) :=
    (A.opNorm_comp_le _).trans (by push_cast at hS ⊢; gcongr; exact hS y)
  have hDD (y : E) (hy : y ∈ s) : HasFDerivAt (fun z => fderiv ℝ u (shearAlong γ ν z))
      ((fderiv ℝ (fderiv ℝ u) (shearAlong γ ν y)).comp
        (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν)) y :=
    ((hcd y hy).hasFDerivAt_fderiv le_rfl).comp y (hφ y)
  have hDu (y : E) (hy : y ∈ s) : ‖fderiv ℝ (fun z => fderiv ℝ u (shearAlong γ ν z)) y‖ ≤
      ((N * (1 + G) : ℝ≥0) : ℝ) := by
    rw [(hDD y hy).fderiv]
    refine ((fderiv ℝ (fderiv ℝ u) _).opNorm_comp_le _).trans ?_
    push_cast at hS ⊢
    gcongr
    exacts [hN2' y hy, hS y]
  have hHu := ((convex_ball y₀ r).inter
    (TauCeti.convex_setOf_le_inner ν 0)).holderOnWith_of_norm_fderiv_le hα1 inter_subset_left
    (fun y hy => (hDD y hy).differentiableAt) hDu
  have hVu : HolderOnWith (V * (1 + G) ^ (α : ℝ)) α
      (fun y => fderiv ℝ (fderiv ℝ u) (shearAlong γ ν y)) s :=
    holderOnWith_comp_shearAlong hν.le hLγ
      ((holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two u).2 hV) hmaps
  refine ⟨fun y hy => ?_, fun y hy => ?_, hHu, ⟨_, holderOnWith_fderiv_fderiv_comp_shearAlong hν.le
    (fun y _ => hγ.contDiffAt) hcd (fun y _ => hG1 y) (fun y _ => hG2 y) (hH.holderOnWith s)
    (hG3.holderOnWith s) (fun y hy => hN1 _ (hmaps y hy)) hN2' hVu hHu⟩⟩
  · rw [(((hcd y hy).differentiableAt two_ne_zero).hasFDerivAt.comp y (hφ y)).fderiv]
    exact hcomp _ y (hN1 _ (hmaps y hy))
  · have h := norm_fderiv_fderiv_comp_shearAlong_le hν.le hγ.contDiffAt (hcd y hy) (hG1 y) (hG2 y)
      (hN1 _ (hmaps y hy)) (hN2' y hy)
    push_cast
    exact h

/-- **The sheared operator is Hölder.** Let `φ y = y + γ y ν` and `v = u ∘ φ`. On a set `t` that
`φ` maps into the region where `u` is `C²` with `‖Du‖ ≤ N` and the operator
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` is Hölder with constant `K`, the operator `∑ₖₗ ãₖₗ ∂ₖ∂ₗv` with the sheared
coefficients `ã = Wᵀ (a ∘ φ) W` is Hölder, given Hölder bounds for `ã` and for `Du ∘ φ` on `t`. -/
private theorem holderOnWith_sum_sum_smul_fderiv_fderiv_comp_shearAlong {α : ℝ≥0} {ν : E}
    {γ : E → ℝ} {G : ℝ≥0} (hν : ‖ν‖ ≤ 1) (hγ : ContDiff ℝ 2 γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hLγ : LipschitzWith G γ)
    (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) (hG3 : HolderWith G α (fderiv ℝ (fderiv ℝ γ)))
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u : E → ℝ} {t T : Set E} {N K Kã Mã H : ℝ≥0}
    (hmaps : MapsTo (shearAlong γ ν) t T)
    (hcd : ∀ y ∈ t, ContDiffAt ℝ 2 u (shearAlong γ ν y))
    (hN1 : ∀ y ∈ t, ‖fderiv ℝ u (shearAlong γ ν y)‖ ≤ N)
    (hã : ∀ k l, HolderOnWith Kã α
      (fun y => ((shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y) k l) t)
    (hMã : ∀ k l, ∀ y ∈ t,
      |((shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y) k l| ≤ Mã)
    (hH : HolderOnWith H α (fun y => fderiv ℝ u (shearAlong γ ν y)) t)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) T) :
    HolderOnWith (K * (1 + G) ^ (α : ℝ) + ((n + 1) * ((n + 1) * (Mã * G)) * H +
        N * ((n + 1) * ((n + 1) * (Mã * G + G * Kã))))) α
      (fun y => ∑ k, ∑ l, ((shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y) k l •
        fderiv ℝ (fderiv ℝ (u ∘ shearAlong γ ν)) y (EuclideanSpace.single k 1)
          (EuclideanSpace.single l 1)) t := by
  have he (k : Fin (n + 1)) : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ ≤ 1 := by simp
  -- The entries `∂ₖ∂ₗγ` are Hölder with constant `G` and bounded by `G`.
  have hD2 (k l : Fin (n + 1)) :=
    ((hG3.holderOnWith t).clm_apply_of_norm_le_one (he k)).clm_apply_of_norm_le_one (he l)
  have hD2b (k l : Fin (n + 1)) (y : E) :
      |fderiv ℝ (fderiv ℝ γ) y (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)| ≤ G :=
    ((fderiv ℝ (fderiv ℝ γ) y (EuclideanSpace.single k 1)).unit_le_opNorm _ (he l)).trans
      (((fderiv ℝ (fderiv ℝ γ) y).unit_le_opNorm _ (he k)).trans (hG2 y))
  -- The first-order coefficient `c = ∑ₖₗ ãₖₗ ∂ₖ∂ₗγ` is Hölder and bounded.
  have hc := HolderOnWith.fintype_sum fun k => HolderOnWith.fintype_sum fun l =>
    (hã k l).smul_of_norm_le (hD2 k l) (hMã k l) fun y _ => hD2b k l y
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, smul_eq_mul] at hc
  have hcb (y : E) (hy : y ∈ t) :
      ‖∑ k, ∑ l, ((shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y) k l *
        fderiv ℝ (fderiv ℝ γ) y (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)‖ ≤
        (((n + 1) * ((n + 1) * (Mã * G)) : ℝ≥0) : ℝ) :=
    calc _ ≤ ∑ _ : Fin (n + 1), ∑ _ : Fin (n + 1), (Mã * G : ℝ) :=
          norm_sum_le_of_le Finset.univ fun k _ => norm_sum_le_of_le Finset.univ fun l _ => by
            rw [norm_mul]
            exact mul_le_mul (hMã k l y hy) (hD2b k l y) (norm_nonneg _) Mã.coe_nonneg
      _ = _ := by simp
  have hDν : HolderOnWith H α (fun y => fderiv ℝ u (shearAlong γ ν y) ν) t :=
    hH.clm_apply_of_norm_le_one hν
  have hDνb (y : E) (hy : y ∈ t) : |fderiv ℝ u (shearAlong γ ν y) ν| ≤ N :=
    ((fderiv ℝ u _).unit_le_opNorm ν hν).trans (hN1 y hy)
  have hprod := hc.smul_of_norm_le hDν hcb hDνb
  refine ((holderOnWith_comp_shearAlong hν hLγ hK hmaps).add hprod).congr fun y hy => ?_
  exact (sum_sum_smul_fderiv_fderiv_comp_shearAlong hγν (hcd y hy) hγ.contDiffAt _).symm

/-- **Back through the inverse shear.** If `v` is `C²` near the part of `ball y₀ r` above the
hyperplane `⟪·, ν⟫ = 0`, with `‖Dv‖` and `‖D²v‖` bounded by `N` there and `D²v` Hölder with
constant `W` on the smaller closed half-ball of radius `ρ < r`, then for the inverse shear
`ψ x = x - γ x ν` the second derivative of `v ∘ ψ` is Hölder on every set that `ψ` maps into that
closed half-ball. -/
private theorem holderOnWith_iteratedFDeriv_two_comp_shearAlong_neg {α : ℝ≥0} (hα1 : α ≤ 1) {ν : E}
    (hν : ‖ν‖ ≤ 1) {γ : E → ℝ} {G : ℝ≥0} (hγ : ContDiff ℝ 2 γ) (hG1 : ∀ x, ‖fderiv ℝ γ x‖ ≤ G)
    (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) (hG3 : HolderWith G α (fderiv ℝ (fderiv ℝ γ)))
    {y₀ : E} {ρ r : ℝ} (hρr : ρ < r) {U : Set E} {v : E → ℝ} {N W : ℝ≥0} (hU : IsOpen U)
    (hBU : ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ} ⊆ U) (hv : ContDiffOn ℝ 2 v U)
    (hN1 : ∀ y ∈ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}, ‖fderiv ℝ v y‖ ≤ N)
    (hN2 : ∀ y ∈ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 v y‖ ≤ N)
    (hW : HolderOnWith W α (iteratedFDeriv ℝ 2 v) (closedBall y₀ ρ ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}))
    {s : Set E} (hs : MapsTo (shearAlong (-γ) ν) s (closedBall y₀ ρ ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ})) :
    HolderOnWith (W * (1 + G) ^ (α : ℝ) * (1 + G) * (1 + G) + N * (G + 2 * G) * (1 + G) +
        N * (1 + G) * (G + 2 * G) +
        (N * G + G * (N * (2 * r).toNNReal ^ ((1 : ℝ) - α) * (1 + G) ^ (α : ℝ)))) α
      (iteratedFDeriv ℝ 2 (v ∘ shearAlong (-γ) ν)) s := by
  obtain ⟨-, hLγ', -, hH'⟩ := graph_facts hα1 hγ hG1 hG2
  set t := closedBall y₀ ρ ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}
  have htB : t ⊆ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ} :=
    inter_subset_inter_left _ (closedBall_subset_ball hρr)
  have hcd (y : E) (hy : y ∈ t) : ContDiffAt ℝ 2 v y := hv.contDiffAt (hU.mem_nhds (hBU (htB hy)))
  have hneg1 : (fderiv ℝ fun x => -γ x) = -fderiv ℝ γ := funext fun _ => fderiv_neg
  have hneg2 (x : E) : fderiv ℝ (fderiv ℝ fun x => -γ x) x = -fderiv ℝ (fderiv ℝ γ) x :=
    fderiv_fderiv_neg (f := γ)
  have hDv := ((convex_closedBall y₀ ρ).inter
    (TauCeti.convex_setOf_le_inner ν 0)).holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le hα1
    ((inter_subset_left).trans (closedBall_subset_ball hρr)) hcd fun y hy => hN2 y (htB hy)
  have h := holderOnWith_fderiv_fderiv_comp_shearAlong (γ := fun x => -γ x) (w := v) (s := s) hν
    (fun y _ => hγ.neg.contDiffAt) (fun y hy => hcd _ (hs hy))
    (fun y _ => by rw [hneg1, Pi.neg_apply, norm_neg]; exact hG1 y)
    (fun y _ => by rw [hneg2]; exact (norm_neg (fderiv ℝ (fderiv ℝ γ) y)).trans_le (hG2 y))
    (hH'.holderOnWith s)
    ((hG3.neg.holderOnWith s).congr fun x _ => (hneg2 x).symm)
    (fun y hy => hN1 _ (htB (hs hy)))
    (fun y hy => by
      rw [norm_fderiv_fderiv]
      exact hN2 _ (htB (hs hy)))
    (holderOnWith_comp_shearAlong hν hLγ'
      ((holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two v).2 hW) hs)
    (holderOnWith_comp_shearAlong hν hLγ' hDv hs)
  exact (holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two _).1 h

/-- **The choice of the radius.** For the shear by a function with `‖Dγ‖ ≤ G`, there is `R₀ > 0`
such that for `0 < R ≤ R₀` and `2 (1 + G)² ρ < R`, the radius `r = R / (2 (1 + G))` satisfies
`(1 + G) r < R` and `(1 + G) ρ < r`, and the smallness condition of the half-ball estimate holds
at `r` for coefficients with Hölder constant `K` and ellipticity bounds `λ / (1 + G)²`,
`Λ (1 + G)²`. -/
private theorem exists_radius_of_graph (C₀ : ℝ) {α : ℝ≥0} (hα : 0 < α) (G K : ℝ≥0) {lam : ℝ}
    (Lam : ℝ) (hlam : 0 < lam) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ {R ρ : ℝ}, 0 < R → R ≤ R₀ → 2 * (1 + G) ^ 2 * ρ < R →
      (1 + G) * (R / (2 * (1 + G))) < R ∧
      (1 + G) * ρ < R / (2 * (1 + G)) ∧
      2 * (C₀ * (Lam * (1 + G) ^ 2 / (lam / (1 + G) ^ 2)) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) *
        ((n : ℝ) + 1) ^ 2 * ((1 + 2 ^ (α : ℝ)) * K * (R / (2 * (1 + G))) ^ (α : ℝ)) ≤
          lam / (1 + G) ^ 2 := by
  obtain ⟨r₀, hr₀, -, hsmall₀⟩ := Real.exists_pos_le_one_mul_rpow_le
    (max (2 * (C₀ * (Lam * (1 + G) ^ 2 / (lam / (1 + G) ^ 2)) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) *
      ((n : ℝ) + 1) ^ 2 * (1 + 2 ^ (α : ℝ)) * K) 0) (by exact_mod_cast hα : (0 : ℝ) < α)
    (by positivity : 0 < lam / (1 + G) ^ 2)
  refine ⟨2 * (1 + G) * r₀, by positivity, fun {R ρ} hR0 hR hρR => ⟨?_, ?_, ?_⟩⟩
  · have h2 : (1 + (G : ℝ)) * (R / (2 * (1 + G))) = R / 2 := by field_simp
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · have hrr₀ : R / (2 * (1 + G)) ≤ r₀ := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc _ = 2 * (C₀ * (Lam * (1 + G) ^ 2 / (lam / (1 + G) ^ 2)) ^
            (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 * (1 + 2 ^ (α : ℝ)) * K *
            (R / (2 * (1 + G))) ^ (α : ℝ) := by ring
      _ ≤ _ := (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow (by positivity) hrr₀ α.coe_nonneg)
          (by positivity) (le_max_right _ _)).trans hsmall₀

/-- **The Schauder estimate near a curved boundary.** Let `0 < α < 1`, let `ν` be a unit vector
and let `γ : ℝ^{n+1} → ℝ` be `C²`, invariant under translation along `ν`, with `‖Dγ‖ ≤ G`,
`‖D²γ‖ ≤ G` and `D²γ` `α`-Hölder with constant `G`, so that `D = {x | γ x < ⟪x, ν⟫}` is the region
above the graph of a `C^{2,α}` function over the hyperplane `ν^⊥`. Let `0 < λ`, `Λ`, `L` and `M` be
given. Then there is `R₀ > 0` such that for all `R ≤ R₀` and `ρ` with `2 (1 + G)² ρ < R` there is
`C`, independent of the solution, with the following property. Let `x₀ ∈ closure D`, let `a` be
`α`-Hölder entrywise with constant `L` on `closedBall x₀ R ∩ closure D` and bounded entrywise by
`M` on `ball x₀ R ∩ closure D`, and suppose `a x₀` has ellipticity bounds `λ, Λ`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set containing `ball x₀ R ∩ closure D`, vanishing
on `ball x₀ R ∩ ∂D`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `ball x₀ R ∩ closure D` and
with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `ball x₀ R ∩ D` with
constant `K`, then `D²u` is `α`-Hölder on `closedBall x₀ ρ ∩ closure D` with constant `C (K + N)`.

The constants depend only on the dimension, `α`, `G`, `λ`, `Λ`, `L`, `M`, `R` and `ρ`: not on the
centre `x₀`, the coefficients `a` beyond the stated bounds, or `u`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν : E} (hν : ‖ν‖ = 1) {γ : E → ℝ} {G : ℝ≥0}
    (hγ : ContDiff ℝ 2 γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hG1 : ∀ x, ‖fderiv ℝ γ x‖ ≤ G) (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G)
    (hG3 : HolderWith G α (fderiv ℝ (fderiv ℝ γ))) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0)
    (hlam : 0 < lam) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ {R ρ : ℝ}, R ≤ R₀ → 2 * (1 + G) ^ 2 * ρ < R → ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E}, γ x₀ ≤ ⟪x₀, ν⟫_ℝ →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ})) →
      (∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U →
        ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
        (∀ x ∈ ball x₀ R, ⟪x, ν⟫_ℝ = γ x → u x = 0) →
        (∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, |u x| ≤ N) →
        (∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
          (ball x₀ R ∩ {x | γ x < ⟪x, ν⟫_ℝ}) →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u)
          (closedBall x₀ ρ ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}) := by
  obtain ⟨C₀, -, hflat⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace
      hα hα1 (n := n)
  -- The bounds for the sheared coefficients, and the ellipticity constants after the shear.
  set KA : ℝ≥0 := (n + 1) * ((n + 1) * ((1 + G) * M) * (G + 2 * G) +
    (1 + G) * ((n + 1) * ((1 + G) * (L * (1 + G) ^ (α : ℝ)) + M * (G + 2 * G))))
  set MA : ℝ≥0 := (n + 1) * ((n + 1) * ((1 + G) * M) * (1 + G))
  obtain ⟨R₀, hR₀, hrad⟩ := exists_radius_of_graph (n := n) C₀ hα G KA Lam hlam
  refine ⟨R₀, hR₀, fun {R ρ} hR hρR => ?_⟩
  rcases le_or_gt R 0 with hR0 | hR0
  · refine ⟨0, fun {a x₀} _ _ _ _ _ {U u N K V} _ _ _ _ _ _ _ _ _ => ?_⟩
    have hρ : ρ < 0 := by
      by_contra h
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 + G) ^ 2) (not_lt.1 h)
      linarith
    rw [closedBall_eq_empty.2 hρ, empty_inter]
    exact holderOnWith_empty _ _ _
  -- The flat estimate at the radius `r = R / (2 (1 + G))`.
  set r : ℝ := R / (2 * (1 + G))
  obtain ⟨hrR, hρr, hsmall⟩ := hrad hR0 hR hρR
  obtain ⟨C₁, hC₁⟩ := hflat (L := KA) (M := MA) (by positivity) hsmall hρr
  -- The final constant: the estimate obtained below is `F K N`, which is linear in `(K, N)`.
  set Kc : ℝ≥0 := (n + 1) * ((n + 1) * (MA * G + G * KA))
  set Mc : ℝ≥0 := (n + 1) * ((n + 1) * (MA * G))
  set δ : ℝ≥0 := (2 * r).toNNReal ^ ((1 : ℝ) - α)
  set F : ℝ≥0 → ℝ≥0 → ℝ≥0 := fun K N =>
    C₁ * ((K * (1 + G) ^ (α : ℝ) + (Mc * (N * (1 + G) * δ) + N * Kc)) +
        (N * (1 + G) * (1 + G) + N * G)) * (1 + G) ^ (α : ℝ) * (1 + G) * (1 + G) +
      (N * (1 + G) * (1 + G) + N * G) * (G + 2 * G) * (1 + G) +
      (N * (1 + G) * (1 + G) + N * G) * (1 + G) * (G + 2 * G) +
      ((N * (1 + G) * (1 + G) + N * G) * G +
        G * ((N * (1 + G) * (1 + G) + N * G) * δ * (1 + G) ^ (α : ℝ)))
  have hF (K N : ℝ≥0) : F K N ≤ F 1 1 * (K + N) :=
    calc F K N ≤ F (K + N) (K + N) := by
          simp only [F]
          gcongr <;> first | exact le_self_add | exact le_add_self
      _ = F 1 1 * (K + N) := by simp only [F]; ring
  refine ⟨F 1 1, fun {a x₀} hx₀ hEll hEll' hL hM {U u N K V} hU hBU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  -- Shear the boundary flat: `v = u ∘ φ` near `y₀ = ψ x₀`.
  set y₀ : E := shearAlong (-γ) ν x₀ with hy₀def
  have hy₀ : shearAlong γ ν y₀ = x₀ := shearAlong_shearAlong_neg hγν x₀
  obtain ⟨hLγ, hLγ', -, -⟩ := graph_facts hα1.le hγ hG1 hG2
  have hφ : ContDiff ℝ 2 (shearAlong γ ν) := contDiff_shearAlong hγ
  have hmem (y : E) (hy : dist y y₀ ≤ r) := shearAlong_mem_ball_inter hν hγν hLγ hy₀ hrR hy
  have hU' : IsOpen ((shearAlong γ ν) ⁻¹' U) := hU.preimage hφ.continuous
  have hBU' : ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ} ⊆ (shearAlong γ ν) ⁻¹' U :=
    fun y hy => hBU ((hmem y (mem_ball.1 hy.1).le).1 hy.2)
  have hv : ContDiffOn ℝ 2 (u ∘ shearAlong γ ν) ((shearAlong γ ν) ⁻¹' U) :=
    hu.comp hφ.contDiffOn (mapsTo_preimage _ _)
  obtain ⟨hDv, hD2v, hHu, V', hV'⟩ :=
    comp_shearAlong_bounds hα1.le hν hγ hγν hG1 hG2 hG3 hy₀ hrR hU hBU hu hN1 hN2 hV
  have hcoef (k l : Fin (n + 1)) :=
    holderOnWith_transpose_shearRows_mul_mul_apply hα1.le hν hγ hγν hG1 hG2 hy₀ hrR hL hM k l
  have hHo : ball y₀ r ∩ {y | 0 < ⟪y, ν⟫_ℝ} ⊆ closedBall y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ} :=
    inter_subset_inter ball_subset_closedBall fun _ hy => mem_ofPred_eq ▸ le_of_lt hy
  have hHo' : ball y₀ r ∩ {y | 0 < ⟪y, ν⟫_ℝ} ⊆ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ} :=
    inter_subset_inter_right _ fun _ hy => mem_ofPred_eq ▸ le_of_lt hy
  have hop := holderOnWith_sum_sum_smul_fderiv_fderiv_comp_shearAlong (a := a) (u := u)
    (t := ball y₀ r ∩ {y | 0 < ⟪y, ν⟫_ℝ}) hν.le hγ hγν hLγ hG2 hG3
    (fun y hy => (hmem y (mem_ball.1 hy.1).le).2 hy.2)
    (fun y hy => hu.contDiffAt (hU.mem_nhds (hBU' (hHo' hy))))
    (fun y hy => hN1 _ ((hmem y (mem_ball.1 hy.1).le).1 (hHo' hy).2))
    (fun k l => (hcoef k l).1.mono hHo) (fun k l y hy => (hcoef k l).2 y (hHo hy))
    (hHu.mono hHo') hK
  -- The ellipticity of the sheared coefficients at `y₀`.
  have hEllv (ξ : E) := toQuadraticForm'_transpose_shearRows_mul_mul (A := a (shearAlong γ ν y₀)) hν
    (fderiv_apply_eq_zero_of_apply_add_smul_neg (f := γ) (x := y₀) ν fun t => by simp only [hγν])
    (hG1 y₀) hlam.le (by rwa [hy₀]) (by rwa [hy₀]) ξ
  -- Bounds for `v` by `N' = N (1 + G)² + N G`.
  obtain ⟨hNN', hNN''⟩ := le_mul_one_add_mul_one_add_add_mul N G
  have hD2v' (y : E) (hy : y ∈ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) :
      ‖iteratedFDeriv ℝ 2 (u ∘ shearAlong γ ν) y‖ ≤
        ((N * (1 + G) * (1 + G) + N * G : ℝ≥0) : ℝ) := by
    have h := hD2v y hy
    rwa [norm_fderiv_fderiv] at h
  have hDv' (y : E) (hy : y ∈ ball y₀ r ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) :
      ‖fderiv ℝ (u ∘ shearAlong γ ν) y‖ ≤ ((N * (1 + G) * (1 + G) + N * G : ℝ≥0) : ℝ) :=
    (hDv y hy).trans (by exact_mod_cast hNN'')
  -- The flat estimate for `v`.
  have hflatv := hC₁ (a := fun y => (shearRows γ ν y)ᵀ * a (shearAlong γ ν y) * shearRows γ ν y)
    (x₀ := y₀) (c₀ := 0) (ne_zero_of_norm_ne_zero (by rw [hν]; exact one_ne_zero))
    (by
      rw [hy₀def, real_inner_shearAlong hν, Pi.neg_apply]
      linarith)
    (fun ξ => (hEllv ξ).1) (fun ξ => (hEllv ξ).2) (fun k l => (hcoef k l).1)
    (fun y hy k l => (hcoef k l).2 y (hHo hy)) hU' hBU' hv
    (fun y hy hy0 => by
      have h := (hmem y (mem_ball.1 hy).le).1 hy0.ge
      have hi := real_inner_shearAlong_sub hν hγν y
      exact hu0 _ h.1 (by linarith))
    (fun y hy => (hN0 _ ((hmem y (mem_ball.1 hy.1).le).1 hy.2)).trans (by exact_mod_cast hNN'))
    hDv' hD2v' ((holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two _).1 hV') hop
  -- Back to `u = v ∘ ψ` through the inverse shear `ψ x = x - γ x ν`.
  have hmaps : MapsTo (shearAlong (-γ) ν) (closedBall x₀ ρ ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ})
      (closedBall y₀ ((1 + G) * ρ) ∩ {y | 0 ≤ ⟪y, ν⟫_ℝ}) := fun x hx =>
    ⟨mem_closedBall.2 (dist_shearAlong_le hν.le hLγ' (mem_closedBall.1 hx.1)), by
      have h2 : γ x ≤ ⟪x, ν⟫_ℝ := hx.2
      simp only [mem_ofPred_eq, real_inner_shearAlong hν, Pi.neg_apply]
      linarith⟩
  have hback := holderOnWith_iteratedFDeriv_two_comp_shearAlong_neg hα1.le hν.le hγ hG1 hG2 hG3 hρr
    hU' hBU' hv hDv' hD2v' hflatv hmaps
  have hvu : ((u ∘ shearAlong γ ν) ∘ shearAlong (-γ) ν) = u :=
    funext fun x => by simp only [Function.comp_apply, shearAlong_shearAlong_neg hγν x]
  rw [hvu] at hback
  exact hback.mono_const (hF K N)

end TauCeti.PDE
