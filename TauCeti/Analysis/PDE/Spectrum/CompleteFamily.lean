/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart

/-!
# Weak mixed eigenvalues from a complete family of eigenfunctions

Let `Ω` be an open set and `Γ` a set, typically a part of the frontier of `Ω`. A real number `κ`
is a weak mixed eigenvalue of `-Δ` on `H¹_Γ(Ω)` (`TauCeti.W1pVanishingOn mu Ω 2 Γ`) when some
nonzero `u ∈ H¹_Γ(Ω)` satisfies `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)`. Since the form
`∫ ∇u · ∇v` is symmetric, eigenfunctions for distinct eigenvalues are orthogonal in `L²(Ω)`. So
when a family of weak eigenfunctions, with eigenvalues `κₖ`, is complete in `L²(Ω)`, an
eigenfunction for any other `κ` is orthogonal to the whole family, hence zero, and the weak mixed
eigenvalues are exactly the `κₖ`. This is how separation of variables computes a spectrum: exhibit
explicit eigenfunctions and prove their completeness. To show that an explicit function is a weak
eigenfunction, it suffices to test it against the generators of `H¹_Γ(Ω)`.

## Main declarations

* `TauCeti.PDE.inner_gradient_eq_mul_inner_value_of_mem_w1pVanishingOnSubmodule`: a weak
  eigen-identity of `-Δ_Γ` extends from the generators of `H¹_Γ(Ω)` to all of it.
* `TauCeti.PDE.inner_value_eq_zero_of_forall_inner_gradient_eq`: weak mixed eigenfunctions for
  distinct eigenvalues are orthogonal in `L²(Ω)`.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_of_complete`: the weak mixed
  eigenvalues are the eigenvalues of a family of weak eigenfunctions that is complete in `L²(Ω)`.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {Γ : Set E}

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

/-- **Weak mixed eigenfunctions for distinct eigenvalues are orthogonal.** If `u` and `w` in
`H¹_Γ(Ω)` satisfy `∫ ∇u · ∇v = κ ∫ u v` and `∫ ∇w · ∇v = κ' ∫ w v` for every `v ∈ H¹_Γ(Ω)`, with
`κ ≠ κ'`, then `∫ u w = 0`, since the form `∫ ∇u · ∇v` is symmetric. -/
theorem inner_value_eq_zero_of_forall_inner_gradient_eq {u w : W1pVanishingOn mu Omega 2 Γ}
    {kappa kappa' : ℝ} (hne : kappa ≠ kappa')
    (hu : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (hw : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (w : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappa' * ⟪W1p.value (w : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    ⟪W1p.value (u : W1p mu Omega 2), W1p.value (w : W1p mu Omega 2)⟫_ℝ = 0 := by
  have h := (hu w).symm.trans ((real_inner_comm _ _).trans (hw u))
  rw [real_inner_comm (W1p.value (u : W1p mu Omega 2)), ← sub_eq_zero, ← sub_mul,
    mul_eq_zero] at h
  exact h.resolve_left (sub_ne_zero.2 hne)

/-- **The weak mixed eigenvalues of a complete family of eigenfunctions.** Let `w k ∈ H¹_Γ(Ω)`,
`k ∈ ι`, be weak mixed eigenfunctions of `-Δ` with eigenvalues `κₖ`, nonzero, with values the
functions `F k`, and let the family `F` be complete in `L²(Ω)`: only `0` is orthogonal to every
`F k`. Then `κ` is a weak mixed eigenvalue, that is `∫ ∇u · ∇v = κ ∫ u v` for every
`v ∈ H¹_Γ(Ω)` has a nonzero solution `u ∈ H¹_Γ(Ω)`, exactly when `κ = κₖ` for some `k`: an
eigenfunction for any other `κ` is orthogonal to the whole family
(`TauCeti.PDE.inner_value_eq_zero_of_forall_inner_gradient_eq`), hence zero. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_of_complete {ι : Type*} {kappas : ι → ℝ}
    (F : ι → E → ℝ) (w : ι → W1pVanishingOn mu Omega 2 Γ)
    (hwv : ∀ k, W1p.value (w k : W1p mu Omega 2) =ᵐ[mu.restrict (Omega : Set E)] F k)
    (hw0 : ∀ k, W1p.value (w k : W1p mu Omega 2) ≠ 0)
    (hw : ∀ k, ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (w k : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappas k * ⟪W1p.value (w k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (hc : ∀ f : Lp ℝ 2 (mu.restrict (Omega : Set E)),
      (∀ k, ∫ x in Omega, f x * F k x ∂mu = 0) → f = 0)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ,
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
    rw [← inner_value_eq_zero_of_forall_inner_gradient_eq (hne k) hu (hw k), L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hwv k] with x hx
    simp [hx, mul_comm]
  · rintro ⟨k, rfl⟩
    refine ⟨w k, fun h => hw0 k ?_, hw k⟩
    rw [← W1pVanishingOn.valueL_apply, h, map_zero]

end PDE

end TauCeti
