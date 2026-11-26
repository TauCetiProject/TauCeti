/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart

/-!
# Weak eigenvalues of `-Δ` with a Dirichlet condition on part of the boundary

For an open set `Ω` and a set `Γ`, write `H¹_Γ(Ω)` for the space `TauCeti.W1pVanishingOn mu Ω 2 Γ`
of Sobolev functions vanishing on `Γ`. This file treats the weak eigenvalue problem of `-Δ` on
`H¹_Γ(Ω)`: `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)`, with a Dirichlet condition on `Γ` and
the natural (Neumann) condition on the rest of the boundary.

## Main declarations

* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_of_complete`: a family of
  eigenfunctions complete in `L²(Ω)` has all the eigenvalues. This is how the explicit spectra of
  intervals and rectangles are identified.
* `TauCeti.PDE.inner_gradient_eq_mul_inner_value_of_mem_w1pVanishingOnSubmodule`: a weak
  eigen-identity extends from the generators of `H¹_Γ(Ω)` to all of it.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.5 (eigenvalues and eigenfunctions);
H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 9.8.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped Distributions InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {Γ : Set E}

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup

/-- **A weak eigen-identity extends from the generators of `H¹_Γ(Ω)` to all of it.** If
`∫ ∇u · ∇v = κ ∫ u v` holds whenever `v` is the restriction to `Ω` of a test function on `E` whose
support avoids the closure of `Γ`, then it holds for every `v ∈ H¹_Γ(Ω)`: both sides are continuous
in `v`, and `H¹_Γ(Ω)` is the closure of those restrictions. -/
theorem inner_gradient_eq_mul_inner_value_of_mem_w1pVanishingOnSubmodule {u : W1p mu Omega 2}
    {kappa : ℝ} (h : ∀ φ : 𝓓((⊤ : Opens E), ℝ), Disjoint (tsupport φ) (closure Γ) →
      ⟪W1p.gradient u, W1p.gradient (W1p.restrictL (le_top : Omega ≤ ⊤)
          (W1p.ofTestFunctionₗ mu ⊤ 2 φ))⟫_ℝ =
        kappa * ⟪W1p.value u, W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤)
          (W1p.ofTestFunctionₗ mu ⊤ 2 φ))⟫_ℝ)
    {v : W1p mu Omega 2} (hv : v ∈ w1pVanishingOnSubmodule mu Omega 2 Γ) :
    ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ :=
  w1pVanishingOnSubmodule_subset_of_isClosed (s := {v | ⟪W1p.gradient u,
      W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ})
    (isClosed_eq (continuous_const.inner (W1p.gradientL.continuous.congr W1p.gradientL_apply))
      (continuous_const.mul (continuous_const.inner
        (W1p.valueL.continuous.congr W1p.valueL_apply)))) h hv

/-- **The weak eigenvalues of `-Δ` on `H¹_Γ(Ω)` are those of a complete family of
eigenfunctions.** Let `w k ∈ H¹_Γ(Ω)`, `k ∈ ι`, be nonzero weak eigenfunctions,
`∫ ∇(w k) · ∇v = κₖ ∫ (w k) v` for every `v ∈ H¹_Γ(Ω)`, with values `F k`, and let the `F k` be
complete in `L²(Ω)`. Then the problem `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)` has a nonzero
solution `u ∈ H¹_Γ(Ω)` exactly when `κ` is one of the `κₖ`: the form `∫ ∇u · ∇v` is symmetric, so
an eigenfunction for any other `κ` is orthogonal in `L²(Ω)` to every `F k`, hence zero. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_of_complete {ι : Type*} {kappas : ι → ℝ}
    (F : ι → E → ℝ) (w : ι → W1pVanishingOn mu Omega 2 Γ)
    (hwv : ∀ k, W1p.value (w k : W1p mu Omega 2) =ᵐ[mu.restrict Omega] F k)
    (hw0 : ∀ k, W1p.value (w k : W1p mu Omega 2) ≠ 0)
    (hw : ∀ k, ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (w k : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappas k * ⟪W1p.value (w k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (hc : ∀ f : Lp ℝ 2 (mu.restrict Omega), (∀ k, ∫ x in Omega, f x * F k x ∂mu = 0) → f = 0)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ↔
      ∃ k, kappa = kappas k := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    by_contra hne
    push Not at hne
    refine hu0 (W1pVanishingOn.valueL_injective ?_)
    rw [map_zero, W1pVanishingOn.valueL_apply]
    refine hc _ fun k => ?_
    -- `κ ⟪u, w k⟫ = ∫ ∇u · ∇(w k) = κₖ ⟪u, w k⟫`, and `κ ≠ κₖ`.
    have h1 := hu (w k)
    rw [real_inner_comm, hw k u, real_inner_comm (W1p.value _)] at h1
    have h2 : (kappa - kappas k) * ⟪W1p.value (u : W1p mu Omega 2),
        W1p.value (w k : W1p mu Omega 2)⟫_ℝ = 0 := by
      linarith
    rw [← (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hne k)), L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hwv k] with x hx
    simp [hx, mul_comm]
  · rintro ⟨k, rfl⟩
    refine ⟨w k, fun h => hw0 k ?_, hw k⟩
    rw [← W1pVanishingOn.valueL_apply, h, map_zero]

end PDE

end TauCeti
