/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SchurHorn

/-!
# Davis's lower bound on the change of eigenvalues

Let `T` and `S` be symmetric endomorphisms of an `n`-dimensional inner product space over `ℝ` or
`ℂ`, with eigenvalues `λ₀ ≥ ⋯ ≥ λₙ₋₁` and `μ₀ ≥ ⋯ ≥ μₙ₋₁` listed in decreasing order, and let
`(vᵢ)` be the orthonormal eigenbasis of `T` with `T vᵢ = λᵢ vᵢ`. Read in this basis, the
perturbation `H = S - T` has diagonal entries `hᵢ = Re⟪vᵢ, H vᵢ⟫`, and `S` has diagonal entries
`dᵢ = Re⟪vᵢ, S vᵢ⟫ = λᵢ + hᵢ`.

The Hoffman–Wielandt inequality bounds `∑ᵢ (μᵢ - λᵢ)²` from above by the squared Frobenius norm of
`H`. Davis's theorem is a matching lower bound: if the eigenvalues of `S` are pairwise at distance
at least `γ ≥ 0` and the diagonal part of `H` is small, `∑ᵢ hᵢ² ≤ (γ / √2)²`, then

`∑ᵢ hᵢ² - (∑ᵢ μᵢ² - ∑ᵢ dᵢ²) ≤ ∑ᵢ (μᵢ - λᵢ)²`.

The first sum on the left is the squared Frobenius norm of the diagonal part of `H` in the basis
`(vᵢ)`, and `∑ᵢ μᵢ² - ∑ᵢ dᵢ²` is the squared Frobenius norm of the off-diagonal part of `S`, which
is also the off-diagonal part of `H` since `T` is diagonal in this basis. So the spectrum moves by
at least the excess of the diagonal energy of the perturbation over its off-diagonal energy.

The proof combines two facts about the permutohedron of `μ`, the convex hull of the rearrangements
of `μ`. The diagonal `d` of `S` lies in it, by Birkhoff's theorem applied to the doubly stochastic
Schur weight matrix. And since `μ` has `γ`-separated coordinates, every point `c` of it satisfies
`(γ / √2) ‖μ - c‖ ≤ ⟪μ - c, μ⟫`. With `c = d` and the Cauchy–Schwarz inequality
`|⟪μ - d, h⟫| ≤ ‖μ - d‖ ‖h‖ ≤ (γ / √2) ‖μ - d‖`, this gives `⟪μ - d, μ + h⟫ ≥ 0`, which is the
bound after expanding `μ - λ = (μ - d) + h`.

## Main results

* `LinearMap.IsSymmetric.le_sum_sq_eigenvalues_sub`: Davis's eigenvalue-change lower bound.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl. **6** (1963),
  159–173, Theorem 4.1.
-/

public section

open Finset Module
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E} {n : ℕ}

/-- **Davis's eigenvalue-change lower bound.** Let `T` and `S` be symmetric, let `(vᵢ)` be the
eigenbasis of `T`, and suppose the eigenvalues `μᵢ` of `S` are pairwise at distance at least
`γ ≥ 0`. If the diagonal entries `hᵢ = Re⟪vᵢ, (S - T) vᵢ⟫` of the perturbation satisfy
`∑ᵢ hᵢ² ≤ (γ / √2)²`, then the sorted spectra satisfy

`∑ᵢ hᵢ² - (∑ᵢ μᵢ² - ∑ᵢ Re⟪vᵢ, S vᵢ⟫²) ≤ ∑ᵢ (μᵢ - λᵢ)²`,

where `λᵢ` are the eigenvalues of `T`. Here `∑ᵢ μᵢ² - ∑ᵢ Re⟪vᵢ, S vᵢ⟫²` is the squared Frobenius
norm of the off-diagonal part of `S - T` in the basis `(vᵢ)`. -/
theorem le_sum_sq_eigenvalues_sub (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {γ : ℝ} (hγ : 0 ≤ γ)
    (hsep : Pairwise fun i j ↦ γ ≤ |hS.eigenvalues hn i - hS.eigenvalues hn j|)
    (hH : ∑ i, RCLike.re ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2
      ≤ (γ / √2) ^ 2) :
    ∑ i, RCLike.re ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2 -
        (∑ i, hS.eigenvalues hn i ^ 2 -
          ∑ i, RCLike.re ⟪hT.eigenvectorBasis hn i, S (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2)
      ≤ ∑ i, (hS.eigenvalues hn i - hT.eigenvalues hn i) ^ 2 := by
  set v := hT.eigenvectorBasis hn
  set μ := hS.eigenvalues hn
  set ν := hT.eigenvalues hn
  set d : Fin n → ℝ := fun i ↦ RCLike.re ⟪v i, S (v i)⟫_𝕜 with hd
  set h : Fin n → ℝ := fun i ↦ RCLike.re ⟪v i, (S - T) (v i)⟫_𝕜 with hh
  -- The diagonal of the perturbation is the diagonal of `S` minus the spectrum of `T`.
  have hdh (i : Fin n) : ν i = d i - h i := by
    simp [hd, hh, v, ν, inner_sub_right, inner_smul_right]
  -- The diagonal of `S` lies in the permutohedron of its spectrum.
  have hmem : d ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ μ ∘ σ) := by
    convert hS.re_inner_apply_self_mem_convexHull_eigenvalues_comp_perm hn v using 1
    ext i
    rw [hd, hS (v i)]
  have hdisp := TauCeti.mul_sqrt_sum_sq_sub_le_sum_sub_mul_of_mem_convexHull hγ hsep hmem
  -- Cauchy–Schwarz, with `‖h‖ ≤ γ / √2`.
  have hCS : -∑ i, (μ i - d i) * h i ≤ √(∑ i, (μ i - d i) ^ 2) * √(∑ i, h i ^ 2) := by
    simpa [neg_sq] using Real.sum_mul_le_sqrt_mul_sqrt univ (fun i ↦ μ i - d i) (fun i ↦ -h i)
  have hhγ : √(∑ i, h i ^ 2) ≤ γ / √2 := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ γ / √2)]
    exact Real.sqrt_le_sqrt hH
  have hkey : 0 ≤ ∑ i, (μ i - d i) * μ i + ∑ i, (μ i - d i) * h i := by
    nlinarith [mul_le_mul_of_nonneg_left hhγ (Real.sqrt_nonneg (∑ i, (μ i - d i) ^ 2))]
  -- Expanding `μ - λ = (μ - d) + h` reduces the bound to `hkey`.
  have hexpand : ∑ i, (μ i - ν i) ^ 2 - (∑ i, h i ^ 2 - (∑ i, μ i ^ 2 - ∑ i, d i ^ 2)) =
      2 * (∑ i, (μ i - d i) * μ i + ∑ i, (μ i - d i) * h i) := by
    simp only [mul_add, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hdh]
    ring
  linarith

end LinearMap.IsSymmetric
