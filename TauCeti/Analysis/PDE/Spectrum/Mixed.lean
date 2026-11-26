/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart

/-!
# Weak mixed eigenfunctions of `-Δ`

For an open set `Ω ⊆ ℝⁿ` and a Dirichlet part `Γ`, the weak mixed eigenvalue problem for `-Δ`
asks for a nonzero `u ∈ H¹_Γ(Ω)`, the space `TauCeti.W1pVanishingOn` of Sobolev functions vanishing
on `Γ`, with

`∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)`.

The form `∫ ∇u · ∇v` is symmetric, so eigenfunctions of distinct eigenvalues are orthogonal in
`L²(Ω)`. Hence a family of eigenfunctions complete in `L²(Ω)` carries every eigenvalue: an
eigenfunction for any other `κ` is orthogonal to the whole family, hence zero. No regularity of
`Ω` or `Γ` is used.

## Main declarations

* `TauCeti.PDE.inner_value_eq_zero_of_inner_gradient_eq_of_ne`: weak mixed eigenfunctions of
  distinct eigenvalues are orthogonal in `L²(Ω)`.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_of_complete`: the weak mixed
  eigenvalues are those of a family of eigenfunctions complete in `L²(Ω)`.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ : Set (EuclideanSpace ℝ ι)}

/-- **Weak mixed eigenfunctions of distinct eigenvalues are orthogonal.** Two solutions in
`H¹_Γ(Ω)` of the weak eigenvalue identity `∫ ∇u · ∇v = κ ∫ u v`, for every `v ∈ H¹_Γ(Ω)`, with
different `κ` are orthogonal in `L²(Ω)`, since the form `∫ ∇u · ∇v` is symmetric. -/
theorem inner_value_eq_zero_of_inner_gradient_eq_of_ne {u w : W1pVanishingOn mu Omega 2 Γ}
    {kappa kappa' : ℝ} (hne : kappa ≠ kappa')
    (hu : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (hw : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (w : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappa' * ⟪W1p.value (w : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    ⟪W1p.value (u : W1p mu Omega 2), W1p.value (w : W1p mu Omega 2)⟫_ℝ = 0 := by
  have key := (hu w).symm.trans ((real_inner_comm _ _).trans (hw u))
  rw [real_inner_comm (W1p.value (u : W1p mu Omega 2)), ← sub_eq_zero, ← sub_mul,
    mul_eq_zero] at key
  exact key.resolve_left (sub_ne_zero.2 hne)

/-- **The weak mixed eigenvalues from a complete family of eigenfunctions.** Let `w k ∈ H¹_Γ(Ω)`
be nonzero solutions of `∫ ∇(w k) · ∇v = κₖ ∫ (w k) v` for every `v ∈ H¹_Γ(Ω)`, with values
`F k`, complete in `L²(Ω)`. Then the problem `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)` has a
nonzero solution `u ∈ H¹_Γ(Ω)` exactly when `κ` is one of the `κₖ`: an eigenfunction for any other
`κ` is orthogonal to the whole family, hence zero. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_of_complete {α : Type*} {kappas : α → ℝ}
    (F : α → EuclideanSpace ℝ ι → ℝ) (w : α → W1pVanishingOn mu Omega 2 Γ)
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
    rw [W1p.setIntegral_mul_eq_inner_value_of_ae_eq (hwv k)]
    exact inner_value_eq_zero_of_inner_gradient_eq_of_ne (hne k) hu (hw k)
  · rintro ⟨k, rfl⟩
    refine ⟨w k, fun h => hw0 k ?_, hw k⟩
    rw [← W1pVanishingOn.valueL_apply, h, map_zero]

end PDE

end TauCeti
