/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm

/-!
# Exactness of restricted coefficient families

Uniformly bounded lifts on the range of a coefficient map characterize its range on restricted
families coefficientwise. Consequently, restricted families preserve an exact pair of bounded
linear maps when the first map has uniformly bounded lifts on its range. Algebraic exactness
alone would not ensure decay of the lifted coefficients.

The results allow seminormed coefficient modules, arbitrary variable sets and arbitrary radii.
The convolution compatibility in `Module.Norm` makes coefficient maps linear over scalar
restricted series for ultrametric modules. The criterion then applies to presentations of
modules over restricted-series algebras.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §§3.7.2–3.7.3, 5.1.1.
-/

public section

noncomputable section

open TauCeti.MvPowerSeries.IsRestrictedFamily (Gauss mem_addSubgroup)
open TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss

namespace LinearMap

variable {σ R E F G : Type*} [SeminormedRing R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]
  [SeminormedAddCommGroup G] [Module R G] [IsBoundedSMul R G]
  {c : σ → ℝ}

/-- Uniformly bounded lifts on the coefficient range give restricted lifts of every family
whose coefficients belong to that range. -/
theorem mem_range_gaussFamilyMap_iff (φ : E →ₗ[R] F) {C L : ℝ}
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (hlift : ∀ y ∈ LinearMap.range φ, ∃ x, φ x = y ∧ ‖x‖ ≤ L * ‖y‖)
    (b : Gauss c F) :
    b ∈ LinearMap.range (mapLinearMap φ hφ) ↔ ∀ t, b t ∈ LinearMap.range φ := by
  constructor
  · rintro ⟨a, rfl⟩ t
    exact ⟨a t, mapLinearMap_apply φ hφ a t |>.symm⟩
  · intro hb
    choose a ha hn using fun t ↦ hlift (b t) (hb t)
    refine ⟨ofAddSubgroup ⟨a, mem_addSubgroup.mpr
      ((mem_addSubgroup.mp b.toAddSubgroup.2).of_norm_le hn)⟩, ?_⟩
    ext t
    simpa using ha t

/-- Restricted families preserve exactness of a bounded pair if the first map has uniformly
bounded lifts on its range. No closed-range or completeness assumption is needed. -/
theorem range_gaussFamilyMap_eq_ker (φ : E →ₗ[R] F) (ψ : F →ₗ[R] G) {C D L : ℝ}
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (hψ : ∀ e, ‖ψ e‖ ≤ D * ‖e‖)
    (hexact : LinearMap.range φ = LinearMap.ker ψ)
    (hlift : ∀ y ∈ LinearMap.range φ, ∃ x, φ x = y ∧ ‖x‖ ≤ L * ‖y‖) :
    LinearMap.range (mapLinearMap (c := c) φ hφ) =
      LinearMap.ker (mapLinearMap ψ hψ) := by
  ext b
  rw [mem_range_gaussFamilyMap_iff φ hφ hlift]
  simp only [hexact, LinearMap.mem_ker]
  constructor
  · intro hb
    exact Gauss.ext fun t ↦ by simp [hb t]
  · intro hb t
    simpa using congrArg (fun a : Gauss c G ↦ a t) hb

end LinearMap
