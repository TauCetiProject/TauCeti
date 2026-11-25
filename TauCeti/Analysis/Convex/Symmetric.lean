/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Convex.Strong

/-!
# Partial derivatives of symmetric concave functions

Let `Γ ⊆ ℝⁿ` be invariant under permutations of the coordinates and let `f : ℝⁿ → ℝ` be concave
and symmetric on `Γ`. Comparing `f(μ)` with `f` at the transposition of two coordinates of
`μ ∈ Γ` through the tangent inequality shows that the partial derivatives of `f` are ordered
opposite to the coordinates: `∂ᵢ f(μ) ≤ ∂ⱼ f(μ)` whenever `μⱼ < μᵢ`. If `f` is symmetric on all of
`ℝⁿ`, partial derivatives in tied coordinates agree as well, so at an antitone point `μ` the
partial derivatives `k ↦ ∂ₖ f(μ)` are nondecreasing.

This is the step of Spruck's proof of the concavity of spectral functions that orders the
gradient of `f` at a sorted eigenvalue vector.

## Main results

* `ConcaveOn.fderiv_apply_single_le_of_lt`: the partial derivatives of a symmetric concave
  function are ordered opposite to the coordinates.
* `ConcaveOn.monotone_fderiv_apply_single`: at an antitone point they are nondecreasing.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in *Global
  theory of minimal surfaces*, Clay Math. Proc. **2** (2005), 283–309, Theorem 1.4.
-/

public section

open TauCeti

variable {ι : Type*} [Finite ι] [DecidableEq ι] {Γ : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}

/-- **Partial derivatives of a symmetric concave function are ordered opposite to the
coordinates.** Let `Γ` be invariant under permutations of the coordinates and `f` concave and
symmetric on `Γ`. If `μ ∈ Γ` and `μⱼ < μᵢ`, then `∂ᵢ f(μ) ≤ ∂ⱼ f(μ)`. Where `f` is not
differentiable at `μ` both sides are `0`. -/
theorem ConcaveOn.fderiv_apply_single_le_of_lt (hf : ConcaveOn ℝ Γ f)
    (hΓσ : ∀ σ : Equiv.Perm ι, ∀ μ ∈ Γ, μ ∘ σ ∈ Γ)
    (hfσ : ∀ σ : Equiv.Perm ι, ∀ μ ∈ Γ, f (μ ∘ σ) = f μ) {μ : ι → ℝ} (hμ : μ ∈ Γ)
    {i j : ι} (hij : μ j < μ i) :
    fderiv ℝ f μ (Pi.single i 1) ≤ fderiv ℝ f μ (Pi.single j 1) := by
  let := Fintype.ofFinite ι
  by_cases hd : DifferentiableAt ℝ f μ
  swap
  · simp [fderiv_zero_of_not_differentiableAt hd]
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
nondecreasing.** Let `Γ ⊆ ℝⁿ` be invariant under permutations of the coordinates, and let `f` be
symmetric on all of `ℝⁿ` and concave on `Γ`. If `μ ∈ Γ` is antitone, then `k ↦ ∂ₖ f(μ)` is
monotone. Symmetry off `Γ` is needed for the coordinates where `μ` is tied. -/
theorem ConcaveOn.monotone_fderiv_apply_single [Preorder ι] (hf : ConcaveOn ℝ Γ f)
    (hΓσ : ∀ σ : Equiv.Perm ι, ∀ μ ∈ Γ, μ ∘ σ ∈ Γ)
    (hfσ : ∀ σ : Equiv.Perm ι, ∀ μ, f (μ ∘ σ) = f μ) {μ : ι → ℝ} (hμ : μ ∈ Γ)
    (hanti : Antitone μ) :
    Monotone fun k ↦ fderiv ℝ f μ (Pi.single k 1) := by
  intro i j hij
  rcases (hanti hij).lt_or_eq with hlt | heq
  · exact hf.fderiv_apply_single_le_of_lt hΓσ (fun σ ν _ ↦ hfσ σ ν) hμ hlt
  · exact (fderiv_apply_single_eq_of_comp_swap (fun ν ↦ hfσ _ ν) heq.symm 1).le
