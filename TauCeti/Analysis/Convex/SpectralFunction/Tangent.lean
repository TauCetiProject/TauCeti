/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Convex.Strong
import TauCeti.Analysis.InnerProductSpace.SchurHorn
import TauCeti.Analysis.Matrix.Eigenvalues.Basic

/-!
# The tangent inequality for concave spectral functions

Let `Γ ⊆ ℝⁿ` be invariant under permutations of the coordinates and let `f : ℝⁿ → ℝ` be symmetric
and concave on `Γ`. The spectral function `F_f(A) = f(λ(A))` on Hermitian matrices, with `λ(A)`
the decreasingly sorted eigenvalue vector, is concave on the matrices with `λ(A) ∈ Γ`
(`Matrix.concaveOn_spectralFunction`). This file proves the first-order form of that concavity:
where `f` is differentiable at `λ(S)`, the spectral function lies below its tangent at `S`,

`F_f(T) - F_f(S) ≤ DF_f(S)(T - S)`

(`Matrix.sub_le_fderiv_spectralFunction`).

The proof follows Spruck. Comparing `f(μ)` with `f` at the transposition of two coordinates shows
that `∂ᵢ f(μ) ≤ ∂ⱼ f(μ)` whenever `μⱼ < μᵢ` (`ConcaveOn.fderiv_apply_single_le_of_lt`), so the
partial derivatives `wⱼ = ∂ⱼ f(λ(S))` are nondecreasing in `j`
(`ConcaveOn.monotone_fderiv_apply_single`). By Lewis's theorem,
`DF_f(S)(T - S) = ∑ⱼ wⱼ Re ⟪uⱼ, (T - S) uⱼ⟫` for an orthonormal eigenbasis `(uⱼ)` of `S`, which is
`∑ⱼ wⱼ Re ⟪uⱼ, T uⱼ⟫ - ∑ⱼ wⱼ λⱼ(S)`. Since `w` is nondecreasing, the diagonal bound of the
Schur–Horn theorem (`LinearMap.IsSymmetric.sum_mul_re_inner_apply_self_le_sum_mul_eigenvalues`,
applied to `-w`) gives `∑ⱼ wⱼ λⱼ(T) ≤ ∑ⱼ wⱼ Re ⟪uⱼ, T uⱼ⟫`, so
`DF_f(S)(T - S) ≥ Df(λ(S))(λ(T) - λ(S)) ≥ f(λ(T)) - f(λ(S))`, the last step by the concavity of
`f`.

## Main results

* `ConcaveOn.fderiv_apply_single_le_of_lt`: the partial derivatives of a symmetric concave
  function are ordered opposite to the coordinates.
* `ConcaveOn.monotone_fderiv_apply_single`: at an antitone point they are nondecreasing.
* `Matrix.sub_le_fderiv_spectralFunction`: the tangent inequality for a concave spectral function.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in *Global
  theory of minimal surfaces*, Clay Math. Proc. **2** (2005), 283–309, Theorem 1.4.
-/

public section

open Finset TauCeti
open scoped InnerProductSpace

section Coordinates

variable {ι : Type*} [Finite ι] [DecidableEq ι] {Γ : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}

/-- **Partial derivatives of a symmetric concave function are ordered opposite to the
coordinates.** Let `Γ` be invariant under permutations of the coordinates and `f` concave and
symmetric on `Γ`. If `f` is differentiable at `μ ∈ Γ` and `μⱼ < μᵢ`, then
`∂ᵢ f(μ) ≤ ∂ⱼ f(μ)`. -/
theorem ConcaveOn.fderiv_apply_single_le_of_lt (hf : ConcaveOn ℝ Γ f)
    (hΓσ : ∀ σ : Equiv.Perm ι, ∀ μ ∈ Γ, μ ∘ σ ∈ Γ)
    (hfσ : ∀ σ : Equiv.Perm ι, ∀ μ ∈ Γ, f (μ ∘ σ) = f μ) {μ : ι → ℝ} (hμ : μ ∈ Γ)
    (hd : DifferentiableAt ℝ f μ) {i j : ι} (hij : μ j < μ i) :
    fderiv ℝ f μ (Pi.single i 1) ≤ fderiv ℝ f μ (Pi.single j 1) := by
  let := Fintype.ofFinite ι
  have hne : i ≠ j := fun h ↦ (h ▸ hij).false
  -- The tangent of `f` at `μ` lies above `f` at the transposed point, where `f` takes the same
  -- value.
  have ht := hf.neg.add_le_of_hasFDerivWithinAt hμ (hΓσ (Equiv.swap i j) μ hμ)
    hd.hasFDerivAt.neg.hasFDerivWithinAt
  rw [Pi.neg_apply, Pi.neg_apply, hfσ _ μ hμ] at ht
  have hsub : μ ∘ Equiv.swap i j - μ = (μ j - μ i) • (Pi.single i 1 - Pi.single j 1) := by
    ext k
    rcases eq_or_ne k i with rfl | hki
    · simp [hne]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hki]
    · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne]
  rw [hsub, neg_apply, map_smul, map_sub, smul_eq_mul] at ht
  nlinarith

/-- **The partial derivatives of a symmetric concave function at an antitone point are
nondecreasing.** Let `Γ ⊆ ℝⁿ` be invariant under permutations of the coordinates and `f` symmetric
and concave on `Γ`. If `μ ∈ Γ` is antitone and `f` is differentiable at `μ`, then
`k ↦ ∂ₖ f(μ)` is monotone. -/
theorem ConcaveOn.monotone_fderiv_apply_single {n : ℕ} {Γ : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ConcaveOn ℝ Γ f)
    (hΓσ : ∀ σ : Equiv.Perm (Fin n), ∀ μ ∈ Γ, μ ∘ σ ∈ Γ)
    (hfσ : ∀ σ : Equiv.Perm (Fin n), ∀ μ, f (μ ∘ σ) = f μ) {μ : Fin n → ℝ} (hμ : μ ∈ Γ)
    (hanti : Antitone μ) (hd : DifferentiableAt ℝ f μ) :
    Monotone fun k ↦ fderiv ℝ f μ (Pi.single k 1) := by
  intro i j hij
  rcases (hanti hij).lt_or_eq with hlt | heq
  · exact hf.fderiv_apply_single_le_of_lt hΓσ (fun σ ν _ ↦ hfσ σ ν) hμ hd hlt
  · exact (fderiv_apply_single_eq_of_comp_swap (fun ν ↦ hfσ _ ν) heq.symm 1).le

end Coordinates

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- **The tangent inequality for concave spectral functions** (Spruck 2005, proof of
Theorem 1.4). Let `Γ ⊆ ℝⁿ`, for `n` the size of the matrices, be invariant under permutations of
the coordinates, and let `f` be symmetric and concave on `Γ`. If `S` and `T` are Hermitian matrices
with `λ(S), λ(T) ∈ Γ` and `f` is differentiable at `λ(S)`, then the spectral function
`F_f(A) = f(λ(A))` satisfies `F_f(T) - F_f(S) ≤ DF_f(S)(T - S)`. -/
theorem sub_le_fderiv_spectralFunction {Γ : Set (Fin (Fintype.card ι) → ℝ)}
    (hΓσ : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ ∈ Γ, μ ∘ σ ∈ Γ)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hfσ : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    (hf : ConcaveOn ℝ Γ f) {S T : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)}
    (hSΓ : S.property.isHermitian.eigenvalues₀ ∈ Γ) (hTΓ : T.property.isHermitian.eigenvalues₀ ∈ Γ)
    (hd : DifferentiableAt ℝ f S.property.isHermitian.eigenvalues₀) :
    f T.property.isHermitian.eigenvalues₀ - f S.property.isHermitian.eigenvalues₀ ≤
      fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        f B.property.isHermitian.eigenvalues₀) S (T - S) := by
  set hS : (S : Matrix ι ι 𝕜).IsHermitian := S.property.isHermitian
  set hT : (T : Matrix ι ι 𝕜).IsHermitian := T.property.isHermitian
  set w : Fin (Fintype.card ι) → ℝ := fun k ↦ fderiv ℝ f hS.eigenvalues₀ (Pi.single k 1)
  obtain ⟨u, hu⟩ := hS.exists_orthonormalBasis_mulVec_eq_eigenvalues₀_smul
  rw [fderiv_spectralFunction_selfAdjoint_apply hfσ S hd u hu]
  -- The diagonal entries of `T - S` in the eigenbasis of `S`.
  have hdiag (k : Fin (Fintype.card ι)) :
      RCLike.re (star ⇑(u k) ⬝ᵥ (((T - S : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
        Matrix ι ι 𝕜) *ᵥ ⇑(u k))) =
        RCLike.re ⟪Matrix.toEuclideanLin (T : Matrix ι ι 𝕜) (u k), u k⟫_𝕜 -
          hS.eigenvalues₀ k := by
    have h1 : star ⇑(u k) ⬝ᵥ ⇑(u k) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        u.norm_eq_one]
      simp
    rw [(isSymmetric_toEuclideanLin_iff.mpr hT) (u k) (u k),
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Submodule.coe_sub, sub_mulVec,
      dotProduct_sub, hu k, dotProduct_smul, h1, smul_eq_mul, mul_one, map_sub, RCLike.ofReal_re]
    rw [dotProduct_comm]
  -- The Schur–Horn diagonal bound, applied to the nonincreasing weights `-w`.
  have hSH :=
    (isSymmetric_toEuclideanLin_iff.mpr hT).sum_mul_re_inner_apply_self_le_sum_mul_eigenvalues
      finrank_euclideanSpace u (c := -w)
      (hf.monotone_fderiv_apply_single hΓσ hfσ hSΓ hS.eigenvalues₀_antitone hd).neg
  -- The tangent inequality for `f` at `λ(S)`, with the derivative written in coordinates.
  have htan := hf.neg.add_le_of_hasFDerivWithinAt hSΓ hTΓ hd.hasFDerivAt.neg.hasFDerivWithinAt
  have hlin (ν : Fin (Fintype.card ι) → ℝ) : fderiv ℝ f hS.eigenvalues₀ ν = ∑ k, w k * ν k := by
    conv_lhs => rw [← univ_sum_single ν]
    refine (map_sum _ _ _).trans (sum_congr rfl fun k _ ↦ ?_)
    rw [show (Pi.single k (ν k) : Fin (Fintype.card ι) → ℝ) = ν k • Pi.single k 1 by
      ext j; simp [Pi.single_apply], map_smul, smul_eq_mul, mul_comm]
  simp only [Pi.neg_apply, neg_apply, hlin, neg_mul, sum_neg_distrib, neg_le_neg_iff,
    Pi.sub_apply, mul_sub, sum_sub_distrib] at hSH htan
  simp only [hdiag, mul_sub, sum_sub_distrib]
  have hSH' : ∑ k, w k * hT.eigenvalues₀ k ≤
      ∑ k, w k * RCLike.re ⟪Matrix.toEuclideanLin (T : Matrix ι ι 𝕜) (u k), u k⟫_𝕜 := hSH
  change _ ≤ ∑ k, w k * RCLike.re ⟪Matrix.toEuclideanLin (T : Matrix ι ι 𝕜) (u k), u k⟫_𝕜 -
    ∑ k, w k * hS.eigenvalues₀ k
  linarith

end Matrix
