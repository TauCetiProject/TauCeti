/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.LeviForm.Laplacian
public import TauCeti.Analysis.Complex.QuadraticLeviForm

/-!
# Examples: the complex Laplacian of the standard metric

The Hermitian form of `i∂∂bar u` is `2 L_u`, and the complex Laplacian of the standard metric `ω` on
`ℂⁿ` is the sum `Δ_ω u = ∑ⱼ λⱼ[2 L_u]` of its relative eigenvalues. For `|z|²` the Levi form is the
inner product, so `λ[i∂∂bar |z|²] = 2e` and `Δ_ω |z|² = 2n`. For `x₁² = (Re z₁)²` the complex
Laplacian is `1`, half the Euclidean Laplacian `2`. The pluriharmonic `Re z₁²` has vanishing Levi
form, so `i∂∂bar (Re z₁²) = 0`.
-/

public section

open Complex Module TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {n : ℕ}

-- `λ[i∂∂bar |z|²] = 2e`.
example (hn : finrank ℂ E = n) (x : E)
    (h : ((2 : ℂ) • leviForm (fun z : E ↦ ‖z‖ ^ 2) x).IsSymm) :
    h.relEigenvalues hn = fun _ ↦ 2 := by
  refine h.relEigenvalues_eq_of_orthonormalBasis hn
    ((stdOrthonormalBasis ℂ E).reindex (finCongr hn)) antitone_const fun i j ↦ ?_
  simp only [leviForm_norm_sq, LinearMap.smul_apply, innerₛₗ_apply_apply,
    OrthonormalBasis.inner_eq_ite, smul_eq_mul]
  split_ifs <;> simp

-- `Δ_ω |z|² = 2n`.
example (hn : finrank ℂ E = n) (x : E)
    (h : ((2 : ℂ) • leviForm (fun z : E ↦ ‖z‖ ^ 2) x).IsSymm) :
    ∑ i, h.relEigenvalues hn i = 2 * n := by
  rw [h.sum_relEigenvalues_eq_sum_re_apply hn ((stdOrthonormalBasis ℂ E).reindex (finCongr hn))]
  simp [mul_comm]

-- `Δ_ω (x₁²) = 1` on `ℂⁿ⁺¹`, with `x₁ = Re z₁` the real part of the first coordinate.
example (x : EuclideanSpace ℂ (Fin (n + 1)))
    (h : ((2 : ℂ) • leviForm (fun z : EuclideanSpace ℂ (Fin (n + 1)) ↦ (z 0).re ^ 2) x).IsSymm) :
    ∑ i, h.relEigenvalues (finrank_euclideanSpace_fin) i = 1 := by
  have hg : ContDiffAt ℝ 2 (fun w : ℂ ↦ w.re ^ 2) (x 0) :=
    (reCLM.contDiff.pow 2).contDiffAt
  have hp : ContDiffAt ℂ 2 (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))) x :=
    by fun_prop
  -- `(Re w)² = (1/2) |w|² + Re ((1/2) w²)`, a Hermitian plus holomorphic quadratic function.
  have hre : (fun w : ℂ ↦ w.re ^ 2) = fun w ↦
      (1 / 2 : ℝ) * ‖w‖ ^ 2 + (∑ _ : Unit, (1 / 2 : ℂ) * ContinuousLinearMap.id ℂ ℂ w ^ 2).re := by
    funext w
    rw [Complex.sq_norm, normSq_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, ContinuousLinearMap.id_apply, sq, mul_re]
    norm_num
    ring
  have h2 : leviForm (fun w : ℂ ↦ w.re ^ 2) (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1)) x) =
      ((1 / 2 : ℝ) : ℂ) • innerₛₗ ℂ := by
    rw [hre]
    exact leviForm_mul_norm_sq_add_re_sum_mul_sq _ _ _ _
  have hL (v w : EuclideanSpace ℂ (Fin (n + 1))) :
      leviForm (fun z : EuclideanSpace ℂ (Fin (n + 1)) ↦ (z 0).re ^ 2) x v w =
        (1 / 2 : ℂ) * (starRingEnd ℂ (v 0) * w 0) := by
    have := leviForm_comp_apply (g := EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))) hg hp v w
    rw [h2] at this
    refine this.trans ?_
    rw [ContinuousLinearMap.fderiv]
    simp [mul_comm]
  rw [h.sum_relEigenvalues_eq_sum_re_apply _ (EuclideanSpace.basisFun _ ℂ)]
  rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by simp [hL, Ne.symm hj]) (by simp)]
  simp [hL]

-- The pluriharmonic `Re z₁²` has vanishing Levi form: `i∂∂bar (Re z₁²) = 0`.
example (x : EuclideanSpace ℂ (Fin (n + 1))) :
    leviForm (fun z : EuclideanSpace ℂ (Fin (n + 1)) ↦ (z 0 ^ 2).re) x = 0 :=
  leviForm_re_eq_zero
    ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).contDiff.pow 2).contDiffAt
